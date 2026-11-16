module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ProjectiveIntersection

/-!
# The projective dimension squeeze for the actual hyperplane-prefix route

Intersecting a prospective prefix component with the remaining linear space
inside projective thirteen-space cannot leave dimension above one when the
intersection lies in the actual final curve. The lower bound comes from the
genuine native projective intersection theorem, with no proper-intersection
or desired prefix-dimension premise.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace

universe u
namespace M9Native.ProjectivePrefixDimensionBounds

variable (K : Type u) [Field K]

/-- If a prefix component has the principal-height lower bound, and the
remaining projective linear space has the linear-equation lower bound, their
intersection inside the actual final one-dimensional locus forces exactly
the expected prefix dimension and exactly a one-dimensional intersection.
The inclusions/dimension lower bounds are geometric producer obligations. -/
theorem dimension_squeeze
    (i r s : ℕ) (hi : i ≤ 5)
    (Z T C : Set (projectiveSpaceOverRing 13 (.of K)))
    (hZ : IsClosed Z) (hT : IsClosed T) (hZn : Z.Nonempty) (hTn : T.Nonempty)
    (hZd : topologicalKrullDim Z = (r : WithBot ℕ∞))
    (hTd : topologicalKrullDim T = (s : WithBot ℕ∞))
    (hr : 6 - i ≤ r) (hs : 8 + i ≤ s)
    (hCd : topologicalKrullDim C = (1 : WithBot ℕ∞)) (hsub : Z ∩ T ⊆ C) :
    (Z ∩ T).Nonempty ∧ r = 6 - i ∧ s = 8 + i ∧
      topologicalKrullDim ↥(Z ∩ T) = (1 : WithBot ℕ∞) := by
  have hsum : 13 ≤ r + s := by omega
  have hn := inter_nonempty_projectiveSpaceOverRing K 13 r s
    Z T hZ hT hZn hTn hZd hTd hsum
  have hl := le_topologicalKrullDim_inter_projectiveSpaceOverRing K 13 r s
    Z T hZ hT hZn hTn hZd hTd hsum
  have hu : topologicalKrullDim ↥(Z ∩ T) ≤ (1 : WithBot ℕ∞) := by
    rw [← hCd]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  have hnum : r + s - 13 ≤ 1 := by exact_mod_cast hl.trans hu
  have hre : r = 6 - i := by omega
  have hse : s = 8 + i := by omega
  have he : r + s - 13 = 1 := by omega
  rw [he] at hl
  exact ⟨hn, hre, hse, le_antisymm hu hl⟩

end M9Native.ProjectivePrefixDimensionBounds
