module

public import M9StacksIntegration.MukaiOrderedMinors
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates

/-!
# Native projective linear equations on the twenty ordered minors

The projective ambient module is the actual dual of the twenty ordered
coordinate vectors. Equations are the actual range of a dual linear map.
Their native projective zero locus is tested at the actual double-dual
evaluation point, and its dimension is proved from the quotient dimension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

universe u

namespace M9Native.MukaiProjectiveKernelCoordinates

open Module AlgebraicGeometry AlgebraicGeometry.ProjectiveSpaceOfModule TopologicalSpace

variable (K : Type u) [Field K]

abbrev Coordinates := MukaiOrderedMinors.OrderedPair → K
abbrev Forms := Module.Dual K (Coordinates K)
abbrev ambient := projectiveSpaceOfModule K (Forms K)

variable {Z : Type u} [AddCommGroup Z] [Module K Z]

/-- The genuine degree-one equations, with no supplied kernel point. -/
def constraints (L : Coordinates K →ₗ[K] Z) : Submodule K (Forms K) := LinearMap.range L.dualMap

/-- The actual native projective linear zero locus of those equations. -/
def kernelLinearSubspace (L : Coordinates K →ₗ[K] Z) : Set (ambient K) :=
  linearSubspace K (Forms K) (constraints K L)

theorem evaluation_ne_zero (w : Coordinates K) (hw : w ≠ 0) :
    Module.Dual.eval K (Coordinates K) w ≠ 0 := by
  intro hz
  apply hw
  apply Module.eval_apply_injective K
  simpa only [map_zero] using hz

/-- The actual native projective point whose coordinate vector is w. -/
def coordinatePoint (w : Coordinates K) (hw : w ≠ 0) : ambient K :=
  linearFunctionalPoint K (Forms K) (Module.Dual.eval K (Coordinates K) w)
    (evaluation_ne_zero K w hw)

@[simp] theorem coordinatePoint_pointSubmodule (w : Coordinates K) (hw : w ≠ 0) :
    pointSubmodule K (Forms K) (coordinatePoint K w hw) =
      LinearMap.ker (Module.Dual.eval K (Coordinates K) w) :=
  pointSubmodule_linearFunctionalPoint K (Forms K) _ _

/-- Actual native projective membership is precisely the original linear kernel equation. -/
theorem coordinatePoint_mem_iff (L : Coordinates K →ₗ[K] Z) (w : Coordinates K) (hw : w ≠ 0) :
    coordinatePoint K w hw ∈ kernelLinearSubspace K L ↔ L w = 0 := by
  rw [kernelLinearSubspace,mem_linearSubspace_iff,coordinatePoint_pointSubmodule]
  constructor
  · intro h
    apply Module.eval_apply_injective K
    ext f
    change f (L w) = f 0
    rw [map_zero]
    exact h ⟨f,rfl⟩
  · intro h
    rintro f ⟨g,rfl⟩
    change g (L w) = 0
    rw [h,map_zero]

theorem finrank_coordinates : finrank K (Coordinates K) = 20 := by
  simp [Coordinates,MukaiOrderedMinors.OrderedPair,Fintype.card_embedding_eq]

theorem finrank_forms : finrank K (Forms K) = 20 := by
  rw [Subspace.dual_finrank_eq,finrank_coordinates]

variable [FiniteDimensional K Z]

/-- At most five genuine linear constraints leave at least fifteen quotient dimensions. -/
theorem finrank_quotient_constraints_ge_fifteen (L : Coordinates K →ₗ[K] Z)
    (hZ : finrank K Z ≤ 5) : 15 ≤ finrank K (Forms K ⧸ constraints K L) := by
  have hr : finrank K (constraints K L) ≤ 5 := by
    rw [constraints,LinearMap.finrank_range_dualMap_eq_finrank_range]
    exact (Submodule.finrank_le L.range).trans hZ
  have hs := (constraints K L).finrank_quotient_add_finrank
  rw [finrank_forms K] at hs
  omega

/-- The native linear zero locus has actual projective Krull dimension at least fourteen. -/
theorem kernelLinearSubspace_dimension_ge_fourteen (L : Coordinates K →ₗ[K] Z)
    (hZ : finrank K Z ≤ 5) :
    (14 : WithBot ℕ∞) ≤ topologicalKrullDim (kernelLinearSubspace K L) := by
  have hq := finrank_quotient_constraints_ge_fifteen K L hZ
  let n := finrank K (Forms K ⧸ constraints K L) - 1
  have hn : finrank K (Forms K ⧸ constraints K L) = n + 1 := by omega
  have hdim := topologicalKrullDim_linearSubspace_of_finrank_quotient_eq
    (k := K) (V := Forms K) (W := constraints K L) hn
  change (14 : WithBot ℕ∞) ≤ topologicalKrullDim (linearSubspace K (Forms K) (constraints K L))
  rw [hdim]
  exact_mod_cast (show 14 ≤ n by omega)

end M9Native.MukaiProjectiveKernelCoordinates
