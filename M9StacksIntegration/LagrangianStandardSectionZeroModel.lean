module

public import M9StacksIntegration.LagrangianKernelRowRestriction
public import M9StacksIntegration.LagrangianKernelLinearCuts
public import M9StacksIntegration.NativeVectorSectionZeroPullback
public import M9StacksIntegration.LagrangianOrderedFibre

/-!
# The full original standard-section zero scheme is a quadric linear section

The original incidence fibre and its literal quotient section are fixed.
Its full native zero ideal is the pullback of the original universal zero
ideal. Actual original row equations and the genuine all-test-scheme
factorization laws identify it with the native quotient-projective linear
section of the literal split quadric. The original base field is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianStandardSectionZeroModel

open LagrangianPluckerQuotient LagrangianMatrixChart LagrangianCommonKernelZero
open IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev curve : Scheme.{u} := LagrangianGeometricFibre.geometricFibre K M hM
abbrev toLG : curve K M hM ⟶ LagrangianGrassmannian.space K :=
  LagrangianGeometricFibre.geometricFibreToLG K M hM
abbrev curveProjection : curve K M hM ⟶ Spec (.of K) :=
  pullback.snd (LagrangianLinearSections.familyProjection K)
    (LagrangianMatrixPointRows.matrixPoint K M hM)

instance toLG_closed : IsClosedImmersion (toLG K M hM) := by
  change IsClosedImmersion (LagrangianGeometricFibre.geometricFibreToLG K M hM)
  rw [← LagrangianGeometricFibre.geometricFibreIsoSection_hom_toLG K M hM]
  infer_instance

def curveSection : Γ(LagrangianUniversalSections.bundle K (toLG K M hM), ⊤) :=
  (LagrangianUniversalSections.quotientMap K (toLG K M hM)).app ⊤
    (freeBasisSection (curve K M hM) 6 0)

abbrev curveZeroIdeal : (curve K M hM).IdealSheafData :=
  Stacks.Chow.zeroSchemeOfSection (curve K M hM)
    (LagrangianUniversalSections.bundle K (toLG K M hM)) (curveSection K M hM)

abbrev zeroCurve : Scheme.{u} := (curveZeroIdeal K M hM).subscheme
abbrev zeroCurveProjection : zeroCurve K M hM ⟶ Spec (.of K) :=
  (curveZeroIdeal K M hM).subschemeι ≫ curveProjection K M hM

/-- The original quotient section is literally the pulled universal section. -/
theorem curveSection_eq_pullback : curveSection K M hM =
    pullbackGlobalSections (toLG K M hM) (quotientOnLG K).target
      (LagrangianCommonKernelZero.standardSection K) := by
  change (LagrangianIsotropicRestriction.pulledQuotient (toLG K M hM)
    (quotientOnLG K).map).app ⊤ (LagrangianGrassmannian.freeVector (curve K M hM) 0) = _
  rw [LagrangianIsotropicRestriction.pulledQuotient_basis]
  rfl

/-- Equality of the full native ideals, without taking supports or radicals. -/
theorem curveZeroIdeal_eq_comap : curveZeroIdeal K M hM =
    (LagrangianCommonKernelZero.zeroIdeal K).comap (toLG K M hM) := by
  change Stacks.Chow.zeroSchemeOfSection (curve K M hM)
    ((Scheme.Modules.pullback (toLG K M hM)).obj (quotientOnLG K).target)
      (curveSection K M hM) = _
  rw [curveSection_eq_pullback]
  exact NativeVectorSectionZeroPullback.zeroSchemeOfSection_pullback
    (toLG K M hM) (quotientOnLG K).target 3 (LagrangianCommonKernelZero.standardSection K)

private theorem subschemeι_transport {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The actual vector-section zero scheme is the actual scheme pullback. -/
def zeroPullbackIso : zeroCurve K M hM ≅ pullback (toLG K M hM) (zeroInclusion K) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (curveZeroIdeal_eq_comap K M hM)) ≪≫
    (LagrangianCommonKernelZero.zeroIdeal K).comapIso (toLG K M hM)

@[reassoc] theorem zeroPullbackIso_hom_fst : (zeroPullbackIso K M hM).hom ≫
    pullback.fst (toLG K M hM) (zeroInclusion K) = (curveZeroIdeal K M hM).subschemeι := by
  rw [zeroPullbackIso, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact subschemeι_transport (curveZeroIdeal_eq_comap K M hM)

def toZero : zeroCurve K M hM ⟶ zeroSpace K :=
  (zeroPullbackIso K M hM).hom ≫ pullback.snd (toLG K M hM) (zeroInclusion K)

instance toZero_closed : IsClosedImmersion (toZero K M hM) := by
  dsimp only [toZero]
  infer_instance

instance toZeroOver_mono : Mono (Over.mk (toZero K M hM)).hom := by
  change Mono (toZero K M hM)
  infer_instance

@[reassoc] theorem toZero_inclusion : toZero K M hM ≫ zeroInclusion K =
    (curveZeroIdeal K M hM).subschemeι ≫ toLG K M hM := by
  have h := congrArg (fun r => (zeroPullbackIso K M hM).hom ≫ r)
    (pullback.condition (f := toLG K M hM) (g := zeroInclusion K)).symm
  calc
    _ = ((zeroPullbackIso K M hM).hom ≫
        pullback.fst (toLG K M hM) (zeroInclusion K)) ≫ toLG K M hM := by
      simpa only [toZero, Category.assoc] using h
    _ = _ := by rw [zeroPullbackIso_hom_fst]

/-- The original incidence equations are recovered on every native test scheme. -/
theorem toZero_factors_iff_sections {T : Scheme.{u}} (t : T ⟶ zeroSpace K) :
    (∃ g : T ⟶ zeroCurve K M hM, g ≫ toZero K M hM = t) ↔
    ∀ j : Fin 5, pullbackGlobalSections t (LagrangianKernelSymmetricSections.line K)
      (LagrangianKernelSymmetricSections.sectionLinear K
        (LagrangianKernelRowRestriction.rows K M j)) = 0 := by
  have hpb : (∃ g : T ⟶ zeroCurve K M hM, g ≫ toZero K M hM = t) ↔
      ∃ a : T ⟶ curve K M hM, a ≫ toLG K M hM = t ≫ zeroInclusion K := by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g ≫ (curveZeroIdeal K M hM).subschemeι, ?_⟩
      have h := congrArg (fun r => r ≫ zeroInclusion K) hg
      simpa only [Category.assoc, toZero_inclusion] using h
    · rintro ⟨a, ha⟩
      refine ⟨pullback.lift a t ha ≫ (zeroPullbackIso K M hM).inv, ?_⟩
      simp only [toZero, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]
  calc
    _ ↔ ∃ a : T ⟶ curve K M hM, a ≫ toLG K M hM = t ≫ zeroInclusion K := hpb
    _ ↔ ∀ j : Fin 5, pullbackGlobalSections (t ≫ zeroInclusion K) (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (M j)) = 0 := by
      rw [LagrangianGeometricFibre.geometricFibre_factorsThrough_iff_rows]
      simp_rw [← LagrangianHyperplaneRows.determinantSection_row]
    _ ↔ _ := by
      apply forall_congr'
      intro j
      exact LagrangianKernelRowRestriction.pullback_row_zero_iff K t (M j)

abbrev equations : Submodule K (Fin 5 → K) :=
  LagrangianKernelLinearCuts.equations K (LagrangianKernelRowRestriction.rows K M)

/-- The full native curve-section zero scheme is the actual quadric linear section. -/
def zeroIsoLinearSection : zeroCurve K M hM ≅
    SplitQuadricLinearSection.linearSection K (equations K M) :=
  comparisonIso (Over.mk (toZero K M hM))
    (Over.mk (LagrangianKernelLinearCuts.toZero K (LagrangianKernelRowRestriction.rows K M)))
    (fun _ t => (toZero_factors_iff_sections K M hM t).trans
      (LagrangianKernelLinearCuts.toZero_factors_iff_sections K
        (LagrangianKernelRowRestriction.rows K M) t).symm)

@[reassoc] theorem zeroIsoLinearSection_hom_toZero : (zeroIsoLinearSection K M hM).hom ≫
    LagrangianKernelLinearCuts.toZero K (LagrangianKernelRowRestriction.rows K M) = toZero K M hM :=
  comparisonIso_hom_comp (Over.mk (toZero K M hM))
    (Over.mk (LagrangianKernelLinearCuts.toZero K (LagrangianKernelRowRestriction.rows K M)))
    (fun _ t => (toZero_factors_iff_sections K M hM t).trans
      (LagrangianKernelLinearCuts.toZero_factors_iff_sections K
        (LagrangianKernelRowRestriction.rows K M) t).symm)

theorem linearSection_toZero_projection :
    LagrangianKernelLinearCuts.toZero K (LagrangianKernelRowRestriction.rows K M) ≫ zeroProjection K =
      SplitQuadricLinearSection.sectionProjection K (equations K M) := by
  have hi : (LagrangianCommonKernelQuadricIso.modelIso K).inv ≫ zeroProjection K =
      SplitQuadricLinearSection.quadricProjection K := by
    apply (cancel_epi (LagrangianCommonKernelQuadricIso.modelIso K).hom).mp
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
      (LagrangianCommonKernelQuadricIso.modelIso_hom_projection K).symm
  let e := SplitQuadricLinearSection.sectionIsoPullback K (equations K M)
  let lin := SplitQuadricLinearSection.linearInclusion K (equations K M)
  let qi := SplitQuadricLinearSection.quadricInclusion K
  let base := Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 4
  calc
    _ = e.hom ≫ pullback.snd lin qi ≫ qi ≫ base := by
      simp only [LagrangianKernelLinearCuts.toZero, Category.assoc, hi,
        SplitQuadricLinearSection.quadricProjection]
      rfl
    _ = e.hom ≫ pullback.fst lin qi ≫ lin ≫ base := by
      simpa only [Category.assoc] using congrArg (fun r => e.hom ≫ r ≫ base)
        (pullback.condition (f := lin) (g := qi)).symm
    _ = _ := by
      change ((e.hom ≫ pullback.fst lin qi) ≫ lin) ≫ base = _
      rw [SplitQuadricLinearSection.sectionIsoPullback_hom_fst]
      rfl

private theorem compose_over {A B C D S : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (p : D ⟶ S) (q : C ⟶ S) (h : a ≫ b = c ≫ d) (hd : d ≫ p = q) :
    a ≫ (b ≫ p) = c ≫ q := by
  rw [← Category.assoc, h, Category.assoc, hd]

theorem toZero_projection : toZero K M hM ≫ zeroProjection K = zeroCurveProjection K M hM :=
  compose_over (toZero K M hM) (zeroInclusion K) (curveZeroIdeal K M hM).subschemeι
    (toLG K M hM) (LagrangianGrassmannian.projection K) (curveProjection K M hM)
    (toZero_inclusion K M hM) (LagrangianOrderedFibre.geometricFibre_over K M hM)

/-- The actual original structural field map is preserved by the scheme isomorphism. -/
theorem zeroIsoLinearSection_over : (zeroIsoLinearSection K M hM).hom ≫
    SplitQuadricLinearSection.sectionProjection K (equations K M) = zeroCurveProjection K M hM :=
  (congrArg (fun r => (zeroIsoLinearSection K M hM).hom ≫ r)
    (linearSection_toZero_projection K M)).symm.trans
      ((Category.assoc (zeroIsoLinearSection K M hM).hom
        (LagrangianKernelLinearCuts.toZero K (LagrangianKernelRowRestriction.rows K M))
        (zeroProjection K)).symm.trans
          ((congrArg (fun r => r ≫ zeroProjection K)
            (zeroIsoLinearSection_hom_toZero K M hM)).trans (toZero_projection K M hM)))

end M9Native.LagrangianStandardSectionZeroModel
