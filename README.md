# Rationality of M₉

Lean formalization of Vlado Vojdanovski’s *Rationality of the Moduli Space of Curves of Genus Nine*, Theorem 1.1.

The coarse moduli space of smooth, connected, unpointed complex curves of genus nine is rational over ℂ. The development proves the coarse-moduli universal property for all algebraic-space targets, classifies curves over every algebraically closed complex extension, and constructs a common dense open with affine 24-space. It also proves the structural function-field identity ℂ(M₉) ≃ₐ[ℂ] ℂ(t₁,…,t₂₄) for that same moduli space.

## Paper and proof

- [Original paper](paper/Rationality_of_M9.pdf), unchanged, eight pages.
- [Lean errata and formalization differences](LEAN_ERRATA.md): scope omissions and replacement arguments, listed by paper location.
- [Solution.lean](Solution.lean): proved entry point `M9Rationality.main_result`.
- [Challenge.lean](Challenge.lean): self-contained comparison statement. Its intentional placeholder specifies the theorem that the independent Solution proves.
- [M9PaperResult.lean](M9StacksIntegration/M9PaperResult.lean): closed paper theorem and same-space function-field package.
- [GenusNineRationality.lean](M9StacksIntegration/GenusNineRationality.lean): density, quotient geometry, rational open and structural complex field equivalence.
- [formalization.yaml](formalization.yaml): authorship, provenance, source alignment and automation credits.

The statement includes arbitrary scheme bases and families with algebraic-space total spaces. It uses the literal complex field and asserts rationality of the coarse algebraic space; it does not add a universe-polymorphic or global scheme-representability assertion.

## Build

Use Lean `v4.35.0` and the committed Lake manifest. The pinned dependencies are Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and [Vlado-V/Stacks](https://github.com/Vlado-V/Stacks/tree/1800a10cc910b02ae3b9034ce298b702363cf5e5) `1800a10cc910b02ae3b9034ce298b702363cf5e5`, based on AxiomMath/Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`.

```sh
lake exe cache get
lake build Solution
```

The repository contains the complete 1,927-module project proof closure. Third-party dependencies are fetched at their pinned Git revisions.

On a supported Linux environment with the required sandbox tooling, the paired statement and proof can be checked using:

```sh
lake comparator comparator.json
```

Only `propext`, `Classical.choice` and `Quot.sound` are permitted axioms. Official Palomar full preflight additionally checks the complete source contract, provenance, statement comparison and independent kernel reports against an exact repository commit.

## Attribution

Vlado Vojdanovski (`Vlado-V`) is the author and responsible maintainer. Codex agent contributions are recorded in `formalization.yaml`. Proof source is released under [Apache-2.0](LICENSE); retained upstream notices and exact adaptations are documented in [NOTICE.md](NOTICE.md). The accompanying paper retains its authorship and separate copyright/provenance.
