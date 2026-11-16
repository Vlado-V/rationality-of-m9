module

public import M9StacksIntegration.LagrangianCanonicalPointRows
public import M9StacksIntegration.RationalPointDivisorRestriction
public import M9StacksIntegration.IteratedLineSectionCuts

/-! Native canonical restriction ranks are the ranks of the actual
original point rows and full kernel-plane volumes. Reduced selected
point divisors are used only for the lower triple ranks; the upper
bound factors through an arbitrary FULL original member divisor. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
universe u

namespace M9Native.LagrangianCanonicalPointRanks
open LagrangianGrassmannian LagrangianPrimitiveRestriction
open LagrangianPointKernelCoordinates LagrangianPointVolumeRanks LagrangianCanonicalPointRows

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
  [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]
  (l : X ⟶ space K)

local instance canonicalInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) :=
  CurveCanonicalInvertibility.dualizing_isInvertible f

def closedTuple {n : ℕ} (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) : Fin n → closedPoints X :=
  fun i => pointEquivClosedPoint f ⟨p i,hp i⟩

theorem point_of_closedTuple {n : ℕ} (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) (i : Fin n) :
    ((pointEquivClosedPoint f).symm (closedTuple K f p hp i)).val = p i :=
  congrArg Subtype.val ((pointEquivClosedPoint f).symm_apply_apply ⟨p i,hp i⟩)

theorem rows_ker_eq_restriction_comp {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) :
    LinearMap.ker (rows K l p).mulVecLin = LinearMap.ker
      ((CanonicalDivisorSpan.canonicalRestriction f
        (RationalPointDivisor.divisor (closedTuple K f p hp))).comp
          (LagrangianPrimitiveRestriction.canonicalRestriction K f l c)) := by
  ext a
  change (rows K l p).mulVec a = 0 ↔
    CanonicalDivisorSpan.canonicalRestriction f
      (RationalPointDivisor.divisor (closedTuple K f p hp))
        (LagrangianPrimitiveRestriction.canonicalRestriction K f l c a) = 0
  rw [rows_zero_iff_canonical_points K f l c hl p hp a,
    RationalPointDivisorRestriction.restriction_eq_zero_iff_points f
      (closedTuple K f p hp) (Stacks.Duality.dualizingSheafOverField f)]
  exact forall_congr' fun i => by rw [point_of_closedTuple K f p hp i]

theorem rows_rank_eq_canonicalRestriction {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hC : Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K f l c))
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) :
    finrank K (LinearMap.range (rows K l p).mulVecLin) =
      finrank K (LinearMap.range (CanonicalDivisorSpan.canonicalRestriction f
        (RationalPointDivisor.divisor (closedTuple K f p hp)))) := by
  let R := CanonicalDivisorSpan.canonicalRestriction f
    (RationalPointDivisor.divisor (closedTuple K f p hp))
  let C := LagrangianPrimitiveRestriction.canonicalRestriction K f l c
  have hker : LinearMap.ker (rows K l p).mulVecLin = LinearMap.ker (R.comp C) :=
    rows_ker_eq_restriction_comp K f l c hl p hp
  have hA := (rows K l p).mulVecLin.finrank_range_add_finrank_ker
  have hB := (R.comp C).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (R.comp C) = LinearMap.range R :=
    LinearMap.range_comp_of_range_eq_top R (LinearMap.range_eq_top.mpr hC)
  rw [hker] at hA
  rw [hrange] at hB
  change finrank K (LinearMap.range (rows K l p).mulVecLin) = finrank K (LinearMap.range R)
  omega

theorem rows_rank_le_full_divisor {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hC : Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K f l c))
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) (D : X.IdealSheafData)
    (hfac : ∀ i, ∃ a : Spec (.of K) ⟶ D.subscheme, a ≫ D.subschemeι = p i) :
    finrank K (LinearMap.range (rows K l p).mulVecLin) ≤
      finrank K (LinearMap.range (CanonicalDivisorSpan.canonicalRestriction f D)) := by
  let R := CanonicalDivisorSpan.canonicalRestriction f D
  let C := LagrangianPrimitiveRestriction.canonicalRestriction K f l c
  have hker : LinearMap.ker (R.comp C) ≤ LinearMap.ker (rows K l p).mulVecLin := by
    intro a ha
    change (rows K l p).mulVec a = 0
    apply (rows_zero_iff_canonical_points K f l c hl p hp a).mpr
    have hD : pullbackGlobalSections D.subschemeι
        (Stacks.Duality.dualizingSheafOverField f)
        ((cohomologyOverFieldZeroLinearIso K f
          (Stacks.Duality.dualizingSheafOverField f)).hom (C a)) = 0 :=
      (RationalPointDivisorRestriction.restriction_eq_zero_iff_pullback f D
        (Stacks.Duality.dualizingSheafOverField f) (C a)).mp ha
    intro i
    obtain ⟨g,hg⟩ := hfac i
    rw [← hg]
    apply (IteratedLineSectionCuts.pullback_comp_zero_iff
      (Stacks.Duality.dualizingSheafOverField f) g D.subschemeι _).mpr
    rw [hD,map_zero]
  have hdim := Submodule.finrank_mono hker
  have hA := (rows K l p).mulVecLin.finrank_range_add_finrank_ker
  have hB := (R.comp C).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (R.comp C) = LinearMap.range R :=
    LinearMap.range_comp_of_range_eq_top R (LinearMap.range_eq_top.mpr hC)
  rw [hrange] at hB
  change finrank K (LinearMap.range (rows K l p).mulVecLin) ≤ finrank K (LinearMap.range R)
  omega

theorem kernelVolume_span_rank_eq_rows {n : ℕ} (p : Fin n → (Spec (.of K) ⟶ X)) :
    finrank K (Submodule.span K (Set.range (fun i => kernelVolume K (p i ≫ l)))) =
      finrank K (LinearMap.range (rows K l p).mulVecLin) := by
  let s : Fin n → (Fin 14 → K) := fun i => fourteen K (p i ≫ l)
  have h := (Submodule.equivMapOfInjective (kernelVolumeEmbedding K)
    (kernelVolumeEmbedding_injective K) (Submodule.span K (Set.range s))).finrank_eq.symm
  rw [Submodule.map_span, ← Set.range_comp'] at h
  have he : (fun i => kernelVolumeEmbedding K (s i)) =
      fun i => kernelVolume K (p i ≫ l) := funext fun i => kernelVolumeEmbedding_fourteen K (p i ≫ l)
  rw [he] at h
  refine h.trans ?_
  change finrank K (Submodule.span K (Set.range (rows K l p).row)) = _
  exact (Matrix.rank_eq_finrank_span_row (rows K l p)).symm

theorem kernelVolume_span_rank_eq_canonicalRestriction {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hC : Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K f l c))
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) :
    finrank K (Submodule.span K (Set.range (fun i => kernelVolume K (p i ≫ l)))) =
      finrank K (LinearMap.range (CanonicalDivisorSpan.canonicalRestriction f
        (RationalPointDivisor.divisor (closedTuple K f p hp)))) :=
  (kernelVolume_span_rank_eq_rows K l p).trans
    (rows_rank_eq_canonicalRestriction K f l c hC hl p hp)

theorem kernelVolume_span_rank_le_full_divisor {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hC : Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K f l c))
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) (D : X.IdealSheafData)
    (hfac : ∀ i, ∃ a : Spec (.of K) ⟶ D.subscheme, a ≫ D.subschemeι = p i) :
    finrank K (Submodule.span K (Set.range (fun i => kernelVolume K (p i ≫ l)))) ≤
      finrank K (LinearMap.range (CanonicalDivisorSpan.canonicalRestriction f D)) := by
  rw [kernelVolume_span_rank_eq_rows K l p]
  exact rows_rank_le_full_divisor K f l c hC hl p hp D hfac

end M9Native.LagrangianCanonicalPointRanks
