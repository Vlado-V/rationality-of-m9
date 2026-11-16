module

public import M9StacksIntegration.LagrangianProjectiveIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The actual native projective-eight-plane and its scheme intersection
with the original LG. The plane is the genuine Proj of the quotient of
the fourteen coordinate forms by the five actual equations. Its closed
embedding, projective-space isomorphism, intersection range, nonemptiness,
and dimension lower bound are derived. This leaf does not identify the
original universal incidence fibre's ideal with this intersection ideal. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open AlgebraicGeometry.ProjectiveSpaceOfModule
open M9Native.LagrangianProjectiveIntersection

universe u

namespace M9Native.LagrangianProjectiveSectionScheme

variable (K : Type u) [Field K] (L : Coordinates K →ₗ[K] (Fin 5 → K))

abbrev plane : Scheme.{u} := projectiveSpaceOfModule K (Forms K ⧸ constraints K L)

def planeInclusion : plane K L ⟶ ambient K :=
  quotientMap K (Forms K) (constraints K L) ≫ (coordinateIso K).inv

instance planeInclusion_isClosedImmersion : IsClosedImmersion (planeInclusion K L) := by
  dsimp [planeInclusion]
  infer_instance

theorem planeInclusion_range : Set.range (planeInclusion K L) = linearSection K L := by
  change Set.range ((coordinateIso K).inv ∘ quotientMap K (Forms K) (constraints K L)) = _
  rw [Set.range_comp, range_quotientMap]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (coordinateIso K).hom ((coordinateIso K).inv y) ∈
      linearSubspace K (Forms K) (constraints K L)
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    exact hy
  · intro hx
    refine ⟨(coordinateIso K).hom x, hx, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- The plane is genuinely isomorphic to native projective eight-space. -/
def planeIsoProjectiveEight (hL : Function.Surjective L) :
    projectiveSpaceOverRing 8 (.of K) ≅ plane K L :=
  basisProjectiveSpaceIso (Module.finBasisOfFinrankEq K _
    (show finrank K (Forms K ⧸ constraints K L) = 8 + 1 from
      finrank_quotient_constraints K L hL))

theorem plane_dimension_eight (hL : Function.Surjective L) :
    topologicalKrullDim (plane K L) = (8 : WithBot ℕ∞) :=
  topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq
    (finrank_quotient_constraints K L hL)

variable [CharZero K]

abbrev sectionScheme : Scheme.{u} :=
  pullback (LagrangianPlucker.primitivePlucker K) (planeInclusion K L)

abbrev sectionToLG : sectionScheme K L ⟶ LagrangianGrassmannian.space K :=
  pullback.fst _ _

def sectionToProjective : sectionScheme K L ⟶ ambient K :=
  sectionToLG K L ≫ LagrangianPlucker.primitivePlucker K

instance sectionToProjective_isClosedImmersion :
    IsClosedImmersion (sectionToProjective K L) := by
  dsimp [sectionToProjective, sectionToLG]
  infer_instance

theorem sectionToProjective_range : Set.range (sectionToProjective K L) =
    image K ∩ linearSection K L := by
  rw [sectionToProjective, sectionToLG, Scheme.Pullback.range_fst_comp,
    planeInclusion_range]
  rfl

theorem sectionScheme_nonempty (hL : Function.Surjective L) :
    Nonempty ↥(sectionScheme K L) := by
  obtain ⟨y, hy⟩ := image_inter_linearSection_nonempty K L hL
  rw [← sectionToProjective_range K L] at hy
  obtain ⟨z, -⟩ := hy
  exact ⟨z⟩

theorem sectionScheme_dimension_ge_one (hL : Function.Surjective L) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim (sectionScheme K L) := by
  have he := (sectionToProjective K L).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _
  rw [sectionToProjective_range] at he
  exact (image_inter_linearSection_dimension_ge_one K L hL).trans_eq he.symm

end M9Native.LagrangianProjectiveSectionScheme
