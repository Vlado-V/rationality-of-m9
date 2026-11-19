# Provenance and attribution

This repository proves the rational coarse-algebraic-space and structural function-field formulation of the accompanying genus-nine paper. Scope omissions and replacement arguments are documented in [LEAN_ERRATA.md](LEAN_ERRATA.md). Proof source is licensed under Apache-2.0, with upstream per-file notices retained.

## Mathematical source

- Author: Vlado Vojdanovski.
- Paper: *Rationality of the Moduli Space of Curves of Genus Nine*, Theorem 1.1, page 1.
- Exact PDF: 8 pages, 111,508 bytes.
- SHA256: `024b7b64a33ccccd578888d0b433357414fbe9c6e0510ef48151852ffae53199`.
- Source relationship: `formalizes`; stable content identifier: `sha256:024b7b64a33ccccd578888d0b433357414fbe9c6e0510ef48151852ffae53199`.

The paper retains its stated authorship and separate copyright/provenance. No external paper licence is assigned by this proof-source notice.

## Pinned proof infrastructure

| Source | Exact revision | Role | Licence and licence-file SHA256 |
| --- | --- | --- | --- |
| [Lean](https://github.com/leanprover/lean4/tree/eb6cafb7290e8bd5f2937522d8d804f58f02bafc) | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | Compiler, kernel, exporter and Comparator tooling | Apache-2.0; `8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e` |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Canonical statement definitions and proof library; `builds-on` | Apache-2.0; `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |
| [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b) | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Native curve, stack and coarse-moduli proof infrastructure; `builds-on` | Apache-2.0; `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| [Vlado-V/Stacks](https://github.com/Vlado-V/Stacks/tree/da1a653b74c2193fc74d3d1cd4dce42fc06653e6) | `da1a653b74c2193fc74d3d1cd4dce42fc06653e6` | Exact proof dependency derived from the upstream revision above, with narrowed imports and the rank-zero lemma split | Apache-2.0; `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| [OpenAI math](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a) | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` | Selected projective-chart/function-field and Proj naturality source ports; `adapts` | Apache-2.0; `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |

The exact Mathlib manifest closure is committed with its dependency revisions and their own licence files. Stacks is a proof dependency; the independent Challenge imports canonical Mathlib definitions.

## Source adaptations

`M9.Private.ProjectiveCharts`, `M9.ProjectiveFunctionField` and `M9.FrameProjectiveGeometry` occur in the actual terminal import closure. Their existing headers and provenance records identify the selected source bodies and modifications.

- OpenAI `lean/OAI/AlgebraicGeometry/Foundations/Scheme/ProjectiveSpace.lean` at the pinned revision has SHA256 `5fd0b5b76d922e4ceb6f47b06ea687d28acc51a50a8871634f0a2d3f0982b1ad`, matching the selected original source in the projective-function-field provenance record.
- The native Proj naturality proof retains the original Chris Birkbeck copyright/author notice for `OAI.AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero`, its Apache-2.0 notice, and the statement that the adapted file was modified.
- The owner-compatible `ToSpecZero.lean` port used for adaptation has source SHA256 `4a71e0e85743709ec97770b6b7735f0b9a0685c8469d7120d8e126627eda42bc`; the public original at the pinned OpenAI revision has SHA256 `3b1560d542f4918802ce7c4672aa4be80bc51465c10b33bc414a8f1c1891d496`.
- The projective and frame adaptations retain their original author, source and modification notices. Local source collections without Git history are identified by their file hashes rather than an invented repository revision.

