module

public import M9StacksIntegration.LagrangianCrossFieldRows
public import M9StacksIntegration.LagrangianGeometricFibre

/-! Every actual extension-field fibre of the original incidence is a
genuine native L-Lagrangian/projective-eight-plane scheme intersection.
The original LG_K map and the actual Spec L map are retained. The field
base change, matrix classifier, and original section comparisons are all
proved, rather than supplied as compatibility assumptions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.LagrangianLinearSections M9Native.IteratedLineSectionCuts
open M9Native.LagrangianCrossFieldParameter M9Native.LagrangianCrossFieldRows

universe u

namespace M9Native.LagrangianCrossFieldFibre

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)
variable (p : Spec (.of L) ⟶ parameter K)
variable (hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

abbrev nativeReversedFibre : Scheme.{u} := pullback (parameterPoint p) (familyProjection L)
abbrev nativeReversedToLG : nativeReversedFibre p ⟶ LagrangianGrassmannian.space L :=
  LagrangianFibreFactorization.fibreToLG L (parameterPoint p)

variable [CharZero K]

theorem zero_native_factorizations {T : Scheme.{u}} (f : T ⟶ LagrangianGrassmannian.space L) :
    (∃ z : T ⟶ zeroScheme φ p hp, z ≫ zeroInclusion φ p hp = f) ↔
      (∃ z : T ⟶ nativeReversedFibre p, z ≫ nativeReversedToLG p = f) := by
  rw [zero_factorsThrough_iff φ p hp f, factorizations_iff φ p hp f, comp_nativeAmbient]
  exact (LagrangianFibreFactorization.fibre_factorsThrough_iff L (parameterPoint p)
    (parameterPoint_projection p) f).symm

def zeroIsoNative : zeroScheme φ p hp ≅ nativeReversedFibre p := by
  let A : Over (LagrangianGrassmannian.space L) := Over.mk (zeroInclusion φ p hp)
  let B : Over (LagrangianGrassmannian.space L) := Over.mk (nativeReversedToLG p)
  let : Mono A.hom := by change Mono (zeroInclusion φ p hp); infer_instance
  let : Mono B.hom := LagrangianFibreFactorization.fibreToLG_mono L (parameterPoint p)
    (parameterPoint_projection p)
  exact comparisonIso A B (fun T f => zero_native_factorizations φ p hp f)

@[reassoc (attr := simp)] theorem zeroIsoNative_hom_toLG :
    (zeroIsoNative φ p hp).hom ≫ nativeReversedToLG p = zeroInclusion φ p hp :=
  comparisonHom_comp (Over.mk (zeroInclusion φ p hp)) (Over.mk (nativeReversedToLG p))
    (fun _ f => zero_native_factorizations φ p hp f)

def zeroIsoNativeConventional : zeroScheme φ p hp ≅ pullback (familyProjection L) (parameterPoint p) :=
  zeroIsoNative φ p hp ≪≫ pullbackSymmetry (parameterPoint p) (familyProjection L)

@[reassoc (attr := simp)] theorem zeroIsoNativeConventional_hom_toLG :
    (zeroIsoNativeConventional φ p hp).hom ≫
      pullback.fst (familyProjection L) (parameterPoint p) ≫ familyToLG L = zeroInclusion φ p hp := by
  simp only [zeroIsoNativeConventional, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  exact zeroIsoNative_hom_toLG φ p hp

def fibreIsoNative : pullback (familyProjection K) p ≅ pullback (familyProjection L) (parameterPoint p) :=
  (zeroSchemeIsoFibre φ p hp).symm ≪≫ zeroIsoNativeConventional φ p hp

@[reassoc]
theorem fibreIsoNative_hom_toLG :
    (fibreIsoNative φ p hp).hom ≫ pullback.fst (familyProjection L) (parameterPoint p) ≫
      familyToLG L ≫ LagrangianFieldBaseChange.map φ =
      pullback.fst (familyProjection K) p ≫ familyToLG K := by
  simp only [fibreIsoNative, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    zeroIsoNativeConventional_hom_toLG_assoc]
  have h := congrArg (fun a => (zeroSchemeIsoFibre φ p hp).inv ≫ a)
    (zeroSchemeIsoFibre_hom_toLG φ p hp)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

omit [CharZero K] in
theorem native_fibre_base :
    pullback.fst (familyProjection L) (parameterPoint p) ≫ familyToLG L ≫
      LagrangianGrassmannian.projection L = pullback.snd (familyProjection L) (parameterPoint p) := by
  have h := congrArg (fun a => a ≫ parameterProjection L)
    (pullback.condition (f := familyProjection L) (g := parameterPoint p))
  simpa only [Category.assoc, parameterPoint_projection, Category.comp_id, ← family_over L] using h

@[reassoc]
theorem fibreIsoNative_hom_base :
    (fibreIsoNative φ p hp).hom ≫ pullback.snd (familyProjection L) (parameterPoint p) =
      pullback.snd (familyProjection K) p := by
  rw [← native_fibre_base p]
  simp only [fibreIsoNative, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    zeroIsoNativeConventional_hom_toLG_assoc]
  have h := congrArg (fun a => (zeroSchemeIsoFibre φ p hp).inv ≫ a)
    (zeroSchemeIsoFibre_hom_base φ p hp)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

include hp in
/-- The actual original fibre over every extension-field parameter point
is the actual native L-LG/P8 scheme intersection, retaining both maps. -/
theorem exists_sectionIso :
    letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
    ∃ (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec)
      (e : pullback (familyProjection K) p ≅
        LagrangianProjectiveSectionScheme.sectionScheme L M.mulVecLin),
      e.hom ≫ LagrangianProjectiveSectionScheme.sectionToLG L M.mulVecLin ≫
          LagrangianFieldBaseChange.map φ = pullback.fst (familyProjection K) p ≫ familyToLG K ∧
      e.hom ≫ LagrangianProjectiveSectionScheme.sectionToLG L M.mulVecLin ≫
          LagrangianGrassmannian.projection L = pullback.snd (familyProjection K) p := by
  let _ : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  obtain ⟨M, hM, e, he⟩ := LagrangianGeometricFibre.every_parameter_fibre L (parameterPoint p)
    (parameterPoint_projection p)
  refine ⟨M, hM, fibreIsoNative φ p hp ≪≫ e, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, reassoc_of% he]
    exact fibreIsoNative_hom_toLG φ p hp
  · simp only [Iso.trans_hom, Category.assoc, reassoc_of% he]
    change (fibreIsoNative φ p hp).hom ≫
      (pullback.fst (familyProjection L) (parameterPoint p) ≫ familyToLG L ≫
        LagrangianGrassmannian.projection L) = _
    rw [native_fibre_base p, fibreIsoNative_hom_base φ p hp]

end M9Native.LagrangianCrossFieldFibre
