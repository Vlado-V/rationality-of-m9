module

public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.GrassmannianCharts
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The genuine Grassmannian meets nine exterior-evaluation equations

The native Pluecker closed immersion uses all120 ordered minors. An actual
rank9 map from the actual third exterior power of the original six-space
gives nine independent linear equations on those coordinates: a proved
linear section lifts its dual equations through the native coordinate map.
Their zero locus is an actual projective110-plane inside native P119.
The original Grassmannian has dimension9, so genuine projective intersection
produces an actual point, and projectivity gives an actual closed point.
No decomposable vector, independent triple or intersection premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open AlgebraicGeometry.ProjectiveSpaceOfModule
open scoped BigOperators

namespace M9Native.GrassmannianExteriorIntersection
open LagrangianPluckerLinear LagrangianPluckerClosed
universe u
variable (K : Type u) [Field K]

abbrev Exterior := LagrangianField.Third K
abbrev Forms := FullCoordinates K
abbrev ambient := projectiveSpaceOverRing (Grassmannian.pluckerDim 3 6) (.of K)
abbrev grass := LagrangianGrassmannian.grassmannian K

/-- The actual ordered20 exterior dual basis has explicit lifts among
the actual120 native coordinate forms. -/
def dualLift : Module.Dual K (Exterior K) →ₗ[K] Forms K :=
  (LagrangianField.thirdBasis20 K).dualBasis.constr K
    (fun j => Pi.basisFun K MinorIndex (LagrangianRing.triple j))

@[simp] theorem coordinateLinearMap_dualLift (ell : Module.Dual K (Exterior K)) :
    coordinateLinearMap K (dualLift K ell) = ell := by
  have h : (coordinateLinearMap K).comp (dualLift K) = LinearMap.id := by
    apply (LagrangianField.thirdBasis20 K).dualBasis.ext
    intro j
    change coordinateLinearMap K (dualLift K ((LagrangianField.thirdBasis20 K).dualBasis j)) = _
    rw [dualLift, Basis.constr_basis, coordinateLinearMap, Basis.constr_basis]
    apply LinearMap.ext
    intro w
    simpa only [LinearMap.id_apply, Basis.coord_apply, Basis.dualBasis_apply] using
      LinearMap.congr_fun (coordinate3_triple K j) w
  exact LinearMap.congr_fun h ell

theorem dualLift_injective : Function.Injective (dualLift K) := by
  intro x y h
  have he := congrArg (coordinateLinearMap K) h
  simpa only [coordinateLinearMap_dualLift] using he

variable {H : Type u} [AddCommGroup H] [Module K H]

/-- Actual dual equations of the actual exterior evaluation, lifted to
the native full Pluecker coordinate forms. -/
def liftedDual (D : Exterior K →ₗ[K] H) :
    Module.Dual K (LinearMap.range D) →ₗ[K] Forms K :=
  (dualLift K).comp D.rangeRestrict.dualMap

def constraints (D : Exterior K →ₗ[K] H) : Submodule K (Forms K) :=
  LinearMap.range (liftedDual K D)

theorem liftedDual_injective (D : Exterior K →ₗ[K] H) :
    Function.Injective (liftedDual K D) := by
  apply (dualLift_injective K).comp
  apply LinearMap.dualMap_injective_of_surjective
  intro y
  obtain ⟨x, hx⟩ := y.property
  exact ⟨x, Subtype.ext hx⟩

theorem constraints_finrank (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    finrank K (constraints K D) = 9 := by
  rw [constraints, LinearMap.finrank_range_of_inj (liftedDual_injective K D),
    Subspace.dual_finrank_eq, hD]

theorem forms_finrank : finrank K (Forms K) = 120 := by
  norm_num [Forms, FullCoordinates, MinorIndex, Fintype.card_embedding_eq, Nat.descFactorial]

theorem pluckerDim_eq : Grassmannian.pluckerDim 3 6 = 119 := by
  norm_num [Grassmannian.pluckerDim, Fintype.card_embedding_eq, Nat.descFactorial]

theorem quotient_constraints_finrank (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    finrank K (Forms K ⧸ constraints K D) = 111 := by
  have h := (constraints K D).finrank_quotient_add_finrank
  rw [forms_finrank K, constraints_finrank K D hD] at h
  omega

/-- The actual closed locus of the lifted determinant equations. -/
def linearSection (D : Exterior K →ₗ[K] H) : Set (ambient K) :=
  (fullProjectiveIso K).hom ⁻¹' linearSubspace K (Forms K) (constraints K D)

theorem linearSection_isClosed (D : Exterior K →ₗ[K] H) :
    IsClosed (linearSection K D) :=
  (isClosed_linearSubspace K (Forms K) (constraints K D)).preimage
    (fullProjectiveIso K).hom.continuous

theorem linearSection_dimension (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    topologicalKrullDim (linearSection K D) = (110 : WithBot ℕ∞) := by
  have hd := topologicalKrullDim_linearSubspace_of_finrank_quotient_eq
    (k := K) (V := Forms K) (W := constraints K D) (n := 110)
    (quotient_constraints_finrank K D hD)
  exact (topologicalKrullDim_preimage_of_homeomorph (fullProjectiveIso K).hom.homeomorph
    (linearSubspace K (Forms K) (constraints K D))).trans hd

theorem linearSection_nonempty (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) : (linearSection K D).Nonempty := by
  by_contra hn
  have : IsEmpty (linearSection K D) := ⟨fun x => hn ⟨x.val, x.property⟩⟩
  have hb := (topologicalKrullDim_eq_bot_iff_isEmpty (linearSection K D)).mpr inferInstance
  rw [linearSection_dimension K D hD] at hb
  simp at hb

def image : Set (ambient K) := Set.range (nativeGrassPlucker K)

theorem image_isClosed : IsClosed (image K) :=
  (nativeGrassPlucker K).isClosedEmbedding.isClosed_range

theorem image_nonempty : (image K).Nonempty := by
  let : Nonempty (grass K) := (GrassmannianCharts.space_irreducible K 3 6).toNonempty
  exact ⟨nativeGrassPlucker K (Classical.arbitrary (grass K)), Set.mem_range_self _⟩

theorem grass_dimension : topologicalKrullDim (grass K) = (9 : WithBot ℕ∞) := by
  let : IrreducibleSpace (grass K) := GrassmannianCharts.space_irreducible K 3 6
  let : SmoothOfRelativeDimension 9 (LagrangianGrassmannian.grassmannianProjection K) :=
    Grassmannian.smoothOfRelativeDimension_schemeOver 3 6 (Spec (.of K))
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (LagrangianGrassmannian.grassmannianProjection K) 9

theorem image_dimension : topologicalKrullDim (image K) = (9 : WithBot ℕ∞) := by
  have he := (nativeGrassPlucker K).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _
  exact he.symm.trans (grass_dimension K)

/-- Actual projective intersection, with no nonemptiness premise. -/
theorem image_inter_linearSection_nonempty (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    (image K ∩ linearSection K D).Nonempty := by
  apply inter_nonempty_projectiveSpaceOverRing K (Grassmannian.pluckerDim 3 6) 9 110
    (image K) (linearSection K D) (image_isClosed K) (linearSection_isClosed K D)
    (image_nonempty K) (linearSection_nonempty K D hD)
    (image_dimension K) (linearSection_dimension K D hD)
  rw [pluckerDim_eq]

/-- Projectivity supplies an ACTUAL closed point of the original
Grassmannian on all nine actual exterior-evaluation equations. -/
theorem exists_closed_point (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    ∃ x : grass K, IsClosed ({x} : Set (grass K)) ∧
      nativeGrassPlucker K x ∈ linearSection K D := by
  obtain ⟨_, ⟨⟨x, rfl⟩, hx⟩⟩ := image_inter_linearSection_nonempty K D hD
  have hc : IsClosed ((nativeGrassPlucker K) ⁻¹' linearSection K D) :=
    (linearSection_isClosed K D).preimage (nativeGrassPlucker K).continuous
  let : IsProper (LagrangianGrassmannian.grassmannianProjection K) :=
    isProper_of_isProjectiveMorphism _
      (Grassmannian.isProjectiveMorphism_schemeOver 3 6 (Spec (.of K)))
  let : CompactSpace (grass K) := QuasiCompact.compactSpace_of_compactSpace
    (LagrangianGrassmannian.grassmannianProjection K)
  obtain ⟨z, hz, hzc⟩ := hc.exists_closed_singleton ⟨x, hx⟩
  exact ⟨z, hzc, hz⟩

end M9Native.GrassmannianExteriorIntersection
