module

public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.LagrangianPluckerClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The actual Lagrangian Grassmannian meets every projective eight-plane

The image is the original fourteen-coordinate closed Plücker embedding.
The linear equations are the actual dual range of a surjection from the
fixed fourteen coordinates to five coordinates. Their quotient has
dimension nine, so their native projective zero locus is an eight-plane.
The native projective intersection theorem gives a nonempty intersection
of dimension at least one. No nonemptiness or intersection dimension is
an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace M9Native.LagrangianProjectiveIntersection

variable (K : Type u) [Field K]

abbrev Coordinates := Fin 14 → K
abbrev Forms := Module.Dual K (Coordinates K)
abbrev ambient := projectiveSpaceOverRing 13 (.of K)

/-- This is the literal ordered dual basis of the fourteen coordinates. -/
def coordinateIso : ambient K ≅ projectiveSpaceOfModule K (Forms K) :=
  basisProjectiveSpaceIso (Pi.basisFun K (Fin 14)).dualBasis

def constraints (L : Coordinates K →ₗ[K] (Fin 5 → K)) : Submodule K (Forms K) :=
  LinearMap.range L.dualMap

/-- The actual closed projective locus of the five coordinate equations. -/
def linearSection (L : Coordinates K →ₗ[K] (Fin 5 → K)) : Set (ambient K) :=
  (coordinateIso K).hom ⁻¹' linearSubspace K (Forms K) (constraints K L)

theorem linearSection_isClosed (L : Coordinates K →ₗ[K] (Fin 5 → K)) :
    IsClosed (linearSection K L) :=
  (isClosed_linearSubspace K (Forms K) (constraints K L)).preimage
    (coordinateIso K).hom.continuous

theorem finrank_forms : finrank K (Forms K) = 14 := by
  simp [Forms, Coordinates, Subspace.dual_finrank_eq]

theorem finrank_quotient_constraints
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    finrank K (Forms K ⧸ constraints K L) = 9 := by
  have hr : finrank K (constraints K L) = 5 := by
    rw [constraints, LinearMap.finrank_range_dualMap_eq_finrank_range,
      LinearMap.range_eq_top.mpr hL, finrank_top]
    simp
  have hs := (constraints K L).finrank_quotient_add_finrank
  rw [finrank_forms K, hr] at hs
  omega

/-- The actual projective locus is an eight-plane, including its dimension. -/
theorem linearSection_dimension_eight
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    topologicalKrullDim (linearSection K L) = (8 : WithBot ℕ∞) := by
  have hd := topologicalKrullDim_linearSubspace_of_finrank_quotient_eq
    (k := K) (V := Forms K) (W := constraints K L) (n := 8)
    (finrank_quotient_constraints K L hL)
  exact (topologicalKrullDim_preimage_of_homeomorph (coordinateIso K).hom.homeomorph
    (linearSubspace K (Forms K) (constraints K L))).trans hd

theorem linearSection_nonempty
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    (linearSection K L).Nonempty := by
  by_contra hn
  have : IsEmpty (linearSection K L) := ⟨fun x => hn ⟨x.val, x.property⟩⟩
  have hb := (topologicalKrullDim_eq_bot_iff_isEmpty (linearSection K L)).mpr
    inferInstance
  rw [linearSection_dimension_eight K L hL] at hb
  simp at hb

theorem evaluation_ne_zero (w : Coordinates K) (hw : w ≠ 0) :
    Module.Dual.eval K (Coordinates K) w ≠ 0 := by
  intro hz
  apply hw
  apply Module.eval_apply_injective K
  simpa only [map_zero] using hz

/-- The genuine native projective point associated to a nonzero coordinate vector. -/
def coordinatePoint (w : Coordinates K) (hw : w ≠ 0) : ambient K :=
  (coordinateIso K).inv
    (linearFunctionalPoint K (Forms K) (Module.Dual.eval K (Coordinates K) w)
      (evaluation_ne_zero K w hw))

/-- Projective membership is precisely the original five linear equations. -/
theorem coordinatePoint_mem_iff (L : Coordinates K →ₗ[K] (Fin 5 → K))
    (w : Coordinates K) (hw : w ≠ 0) :
    coordinatePoint K w hw ∈ linearSection K L ↔ L w = 0 := by
  change (coordinateIso K).hom ((coordinateIso K).inv _) ∈
    linearSubspace K (Forms K) (constraints K L) ↔ _
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  change linearFunctionalPoint K (Forms K) (Module.Dual.eval K (Coordinates K) w)
    (evaluation_ne_zero K w hw) ∈ linearSubspace K (Forms K) (constraints K L) ↔ _
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint]
  constructor
  · intro h
    apply Module.eval_apply_injective K
    ext f
    change f (L w) = f 0
    rw [map_zero]
    exact h ⟨f, rfl⟩
  · intro h
    rintro f ⟨g, rfl⟩
    change g (L w) = 0
    rw [h, map_zero]

variable [CharZero K]

def image : Set (ambient K) := Set.range (LagrangianPlucker.primitivePlucker K)

theorem image_isClosed : IsClosed (image K) :=
  (LagrangianPlucker.primitivePlucker K).isClosedEmbedding.isClosed_range

theorem image_nonempty : (image K).Nonempty :=
  ⟨LagrangianPlucker.primitivePlucker K (Classical.arbitrary
    (LagrangianGrassmannian.space K)), Set.mem_range_self _⟩

theorem image_dimension_six : topologicalKrullDim (image K) = (6 : WithBot ℕ∞) := by
  have he := (LagrangianPlucker.primitivePlucker K).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _
  exact he.symm.trans (LagrangianIntegral.space_dimension K)

/-- Genuine projective intersection, on the original Plücker image. -/
theorem image_inter_linearSection_nonempty
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    (image K ∩ linearSection K L).Nonempty := by
  exact inter_nonempty_projectiveSpaceOverRing K 13 6 8
    (image K) (linearSection K L) (image_isClosed K) (linearSection_isClosed K L)
    (image_nonempty K) (linearSection_nonempty K L hL)
    (image_dimension_six K) (linearSection_dimension_eight K L hL) (by decide)

/-- The nonempty intersection has dimension at least one. -/
theorem image_inter_linearSection_dimension_ge_one
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(image K ∩ linearSection K L) := by
  exact le_topologicalKrullDim_inter_projectiveSpaceOverRing K 13 6 8
    (image K) (linearSection K L) (image_isClosed K) (linearSection_isClosed K L)
    (image_nonempty K) (linearSection_nonempty K L hL)
    (image_dimension_six K) (linearSection_dimension_eight K L hL) (by decide)

theorem exists_lagrangian_point_in_linearSection
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    ∃ x : LagrangianGrassmannian.space K,
      LagrangianPlucker.primitivePlucker K x ∈ linearSection K L := by
  obtain ⟨_, ⟨⟨x, rfl⟩, hx⟩⟩ := image_inter_linearSection_nonempty K L hL
  exact ⟨x, hx⟩

/-- Properness supplies an actual closed LG point satisfying the equations. -/
theorem exists_closed_lagrangian_point_in_linearSection
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (hL : Function.Surjective L) :
    ∃ x : LagrangianGrassmannian.space K,
      IsClosed ({x} : Set (LagrangianGrassmannian.space K)) ∧
      LagrangianPlucker.primitivePlucker K x ∈ linearSection K L := by
  obtain ⟨x, hx⟩ := exists_lagrangian_point_in_linearSection K L hL
  have hc : IsClosed ((LagrangianPlucker.primitivePlucker K) ⁻¹' linearSection K L) :=
    (linearSection_isClosed K L).preimage (LagrangianPlucker.primitivePlucker K).continuous
  let : IsProper (LagrangianGrassmannian.projection K) :=
    isProper_of_isProjectiveMorphism _
      (LagrangianPluckerClosed.isProjectiveMorphism_projection K)
  let : CompactSpace (LagrangianGrassmannian.space K) :=
    QuasiCompact.compactSpace_of_compactSpace (LagrangianGrassmannian.projection K)
  obtain ⟨z, hz, hzc⟩ := hc.exists_closed_singleton ⟨x, hx⟩
  exact ⟨z, hzc, hz⟩

theorem matrix_image_inter_nonempty (A : Matrix (Fin 5) (Fin 14) K)
    (hA : Function.Surjective A.mulVec) :
    (image K ∩ linearSection K A.mulVecLin).Nonempty :=
  image_inter_linearSection_nonempty K A.mulVecLin hA

end M9Native.LagrangianProjectiveIntersection
