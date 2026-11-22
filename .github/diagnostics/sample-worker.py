"""Record memory and compiler targets outside the unchanged Palomar verifier."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


UNIT = re.compile(r"palomar-[a-f0-9]{24}(?:\.service)?\Z")
MODULE = re.compile(r"(?:StacksFrontier|StacksCore|M9StacksIntegration|M9|Mathlib|Batteries|Lean|Init|Lake)(?:/[A-Za-z0-9_]+)+\.lean\Z")
WORKERS = {"lake", "lean", "leanexport", "leanchecker", "nanoda", "nanoda_bin", "con-ron"}
STATS = {"memory.stat": ("anon", "file", "shmem", "kernel", "slab", "pagetables"),
         "memory.events": ("high", "max", "oom", "oom_kill", "oom_group_kill"),
         "cpu.stat": ("usage_usec",)}
MEMORY = ("memory.current", "memory.peak", "memory.high", "memory.max", "memory.swap.current")
CONSTRAINTS = {"CONSTRAINT_NONE", "CONSTRAINT_CPUSET", "CONSTRAINT_MEMORY_POLICY", "CONSTRAINT_MEMCG"}


def read(path):
    try:
        return path.read_text(errors="replace")
    except OSError:
        return ""


def kernel_values(path, keys):
    result = {}
    for line in read(path).splitlines():
        key, separator, value = line.partition(" ")
        if separator and key in keys and value.isdecimal():
            result[key] = int(value)
    return result


def unit_of(data):
    for line in data.splitlines():
        if not line.startswith("0::/"):
            continue
        parts = line[4:].split("/")
        for i, part in enumerate(parts):
            if UNIT.fullmatch(part) and all(p not in (".", "..") and
                                            re.fullmatch(r"[\w.@:-]+", p, re.ASCII) for p in parts[:i]):
                return Path(*parts[:i + 1])
    return None


def lean_target(process):
    for arg in read(process / "cmdline").split("\0"):
        if not arg.endswith(".lean"):
            continue
        parts = arg.split("/")
        if parts[-1] in ("Solution.lean", "Challenge.lean"):
            return parts[-1]
        for i in range(len(parts)):
            name = "/".join(parts[i:])
            if MODULE.fullmatch(name):
                return name[:320]
    return None


def memory_stats(directory):
    values = {key: kernel_values(directory / key, fields) for key, fields in STATS.items()}
    for key in MEMORY:
        value = read(directory / key).strip()
        if value.isdecimal():
            values[key] = int(value)
        elif value == "max":
            values[key] = value
    return values


def process_start_time(process):
    # /proc/PID/stat field 2 is parenthesized and may itself contain spaces and ')'.
    _, separator, rest = read(process / "stat").rpartition(")")
    fields = rest.split()
    start_time = fields[19] if separator and len(fields) > 19 else ""
    return int(start_time) if re.fullmatch(r"[0-9]{1,20}", start_time) else None


def memory_pressure(raw):
    result = {}
    for line in raw.splitlines():
        match = re.fullmatch(r"(some|full) avg10=([0-9]{1,3})\.([0-9]{2}) "
                             r"avg60=[0-9]{1,3}\.[0-9]{2} avg300=[0-9]{1,3}\.[0-9]{2} "
                             r"total=([0-9]{1,20})", line)
        if match:
            basis_points = 100 * int(match[2]) + int(match[3])
            total = int(match[4])
            if basis_points <= 10000 and total < 1 << 63:
                result[match[1]] = {"avg10_basis_points": basis_points, "total_microseconds": total}
    return result


def sample_workers(proc, cgroups):
    groups = {}
    for process in proc.iterdir():
        if not process.name.isdecimal():
            continue
        name = read(process / "comm").strip()
        if name not in WORKERS:
            continue
        start_time = process_start_time(process)
        if start_time is None:
            continue
        unit = unit_of(read(process / "cgroup"))
        if unit is None:
            continue
        values = {}
        for line in read(process / "status").splitlines():
            key, _, value = line.partition(":")
            if key in ("VmRSS", "VmHWM", "RssAnon", "RssFile", "RssShmem"):
                match = re.fullmatch(r"\s*(\d+) kB", value)
                if match:
                    values[key] = 1024 * int(match[1])
        row = {"pid": int(process.name), "executable": name, "start_time_ticks": start_time,
               "memory_bytes": values}
        if name == "lean":
            row["target"] = lean_target(process)
        if read(process / "comm").strip() == name and process_start_time(process) == start_time:
            groups.setdefault(unit, []).append(row)

    result = []
    for unit, workers in sorted(groups.items()):
        directory = cgroups / unit
        ancestors = [memory_stats(cgroups / p) for p in unit.parents]
        result.append({"unit": unit.name, "cgroup": memory_stats(directory), "ancestors": ancestors,
                       "workers": sorted(workers, key=lambda item: item["pid"])})
    return result


def stage_of(report_path):
    try:
        stage = json.loads(read(report_path)).get("stage")
    except (AttributeError, ValueError):
        return None
    return stage if isinstance(stage, str) and re.fullmatch(r"[a-z-]{1,60}", stage) else None


def oom_scope(line, task_path):
    field = re.search(r"(?:^|[:, ])constraint=(CONSTRAINT_[A-Z_]+)(?=[, ]|$)", line)
    constraint = field[1] if field and field[1] in CONSTRAINTS else None
    field = re.search(r"(?:^|[, ])oom_memcg=([^, ]+)(?=[, ]|$)", line)
    if field is None:
        relationship = "not_reported"
    elif field[1] in {"(null)", "null"}:
        relationship = "none"
    elif field[1].startswith("/"):
        oom_group = Path(field[1])
        task_group = Path(task_path)
        if oom_group == task_group:
            relationship = "task_cgroup"
        elif oom_group in task_group.parents:
            relationship = "ancestor_cgroup"
        else:
            relationship = "other_cgroup"
    else:
        relationship = "not_reported"
    return {"constraint": constraint, "oom_memcg_relation": relationship}


def oom_victims(kernel_messages, observed):
    matches = {}
    pending = {}
    for line in kernel_messages.splitlines():
        event = re.search(r"task_memcg=(/[^,]+),task=([a-zA-Z0-9_-]+),pid=(\d+)", line)
        if event and "oom-kill:" in line and event[2] in WORKERS:
            group = unit_of("0::" + event[1])
            if group is not None:
                key = (int(event[3]), event[2], group.name)
                pending[key[:2]] = key
                matches[key] = {**oom_scope(line, event[1])}
        killed = re.search(r"Killed process (\d+) \(([a-zA-Z0-9_-]+)\)", line)
        if not killed:
            continue
        process = (int(killed[1]), killed[2])
        key = pending.pop(process, None)
        if key is None:
            candidates = [item for item in observed if item[:2] == process]
            if len(candidates) == 1:
                key = candidates[0]
        if key is None:
            continue
        match = re.search(r"\banon-rss:(\d+)kB\b", line)
        matches[key] = {**matches.get(key, oom_scope("", "")), "kill_confirmed": True,
                        "anon_rss_bytes": 1024 * int(match[1]) if match else None}
    result = []
    for key, row in sorted(matches.items()):
        instances = observed.get(key, {})
        start_time, targets = next(iter(instances.items())) if len(instances) == 1 else (None, set())
        target = next(iter(targets)) if len(targets) == 1 else None
        result.append({**row, "pid": key[0], "executable": key[1], "unit": key[2],
                       "start_time_ticks": start_time, "target": target})
    return result


def read_kernel_journal(start, observed):
    try:
        result = subprocess.run(["journalctl", "--dmesg", "--since", f"@{start}", "--no-pager",
                                 "--output=cat", "--grep=oom-kill:|Killed process"],
                                capture_output=True, text=True, errors="replace", timeout=8)
    except (OSError, subprocess.TimeoutExpired):
        return {"available": False, "victims": []}
    return {"available": result.returncode == 0, "victims": oom_victims(result.stdout, observed)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pid-file", type=Path, required=True)
    args = parser.parse_args()
    stopped = False
    started = int(time.time())
    observed = {}

    def stop(_number, _frame):
        nonlocal stopped
        stopped = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    with args.output.open("x", buffering=1) as output:
        args.output.chmod(0o644)
        with args.pid_file.open("x") as handle:
            handle.write(f"{os.getpid()}\n")
        args.pid_file.chmod(0o644)
        while not stopped:
            groups = sample_workers(Path("/proc"), Path("/sys/fs/cgroup"))
            for group in groups:
                for worker in group["workers"]:
                    key = (worker["pid"], worker["executable"], group["unit"])
                    targets = observed.setdefault(key, {}).setdefault(worker["start_time_ticks"], set())
                    if worker.get("target") is not None:
                        targets.add(worker["target"])
            meminfo = read(Path("/proc/meminfo"))
            available = re.search(r"^MemAvailable:\s+(\d+) kB$", meminfo, re.M)
            row = {"time": datetime.now(timezone.utc).isoformat(), "stage": stage_of(args.report), "units": groups,
                   "host_memory_available_bytes": int(available[1]) * 1024 if available else None,
                   "host_memory_psi": memory_pressure(read(Path("/proc/pressure/memory")))}
            output.write(json.dumps(row, separators=(",", ":")) + "\n")
            deadline = time.monotonic() + 3
            while not stopped and time.monotonic() < deadline:
                time.sleep(0.25)
        row = {"time": datetime.now(timezone.utc).isoformat(), "kernel_oom": read_kernel_journal(started, observed)}
        output.write(json.dumps(row, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
