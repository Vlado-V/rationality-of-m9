module

public import M9StacksIntegration.LagrangianGoodOpenFieldBaseChange
public import M9StacksIntegration.LagrangianCrossFieldFibre
public import M9StacksIntegration.LagrangianGoodOpenRestriction
public import M9StacksIntegration.LagrangianTransverseGenusNine

/-! Every actual original good parameter over an arbitrary extension
field has an actual ordered five-row cut model. The full original fibre,
its original field map and the literal field-base parameter are retained.
Integrality, relative smoothness and genus nine are conclusions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LagrangianGoodOpenOrderedModel
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianTransverseRestriction LagrangianMatrixPointRows

section Pullbacks
variable {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x : T ⟶ U.toScheme)

theorem restrictedFibre_isPullback :
    IsPullback (pullback.fst (f ∣_ U) x ≫ (f ⁻¹ᵁ U).ι)
      (pullback.snd (f ∣_ U) x) f (x ≫ U.ι) :=
  (IsPullback.of_hasPullback (f ∣_ U) x).paste_horiz (isPullback_morphismRestrict f U).flip

def restrictedFibreIso : pullback (f ∣_ U) x ≅ pullback f (x ≫ U.ι) :=
  (restrictedFibre_isPullback f U x).isoPullback

@[reassoc (attr := simp)] theorem restrictedFibreIso_hom_base :
    (restrictedFibreIso f U x).hom ≫ pullback.snd f (x ≫ U.ι) = pullback.snd (f ∣_ U) x :=
  (restrictedFibre_isPullback f U x).isoPullback_hom_snd

variable (p q : T ⟶ Y) (h : p = q)
def pointFibreIso : pullback f p ≅ pullback f q :=
  eqToIso (congrArg (fun r : T ⟶ Y => pullback f r) h)

@[reassoc (attr := simp)] theorem pointFibreIso_hom_base :
    (pointFibreIso f p q h).hom ≫ pullback.snd f q = pullback.snd f p := by
  subst q
  simp [pointFibreIso]

end Pullbacks

theorem iso_inv_base {A B T : Scheme.{u}} (e : A ≅ B) (a : A ⟶ T) (b : B ⟶ T)
    (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h, Iso.inv_hom_id_assoc]

section Original
variable (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
  [CharZero K] [CharZero L] (φ : K →+* L)
  (x : Spec (.of L) ⟶ (goodOpen K).toScheme)
  (hx : x ≫ (goodOpen K).ι ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

include hx

/-- A matrix, the exact original parameter equality and an actual entire
ordered-cut/fibre isomorphism are constructed. No model, transversality,
genus or parameter-isomorphism premise is supplied. -/
theorem exists_ordered_model :
    ∃ (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec)
      (e : curve L M ≅ pullback (restrictedProjection K) x),
      matrixPoint L M hM ≫ GrassmannianFieldBaseChange.map φ 9 14 = x ≫ (goodOpen K).ι ∧
      e.hom ≫ pullback.snd (restrictedProjection K) x = curveProjection L M ∧
      IsIntegral (curve L M) ∧ SmoothOfRelativeDimension 1 (curveProjection L M) ∧
      genus (curveProjection L M) = 9 := by
  let p := x ≫ (goodOpen K).ι
  let q := LagrangianCrossFieldParameter.parameterPoint p
  have hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ := by
    simpa only [p, Category.assoc] using hx
  obtain ⟨M,hM,hq⟩ := LagrangianParameterMatrix.exists_matrix L q
    (LagrangianCrossFieldParameter.parameterPoint_projection p)
  change q = matrixPoint L M hM at hq
  have hmap : matrixPoint L M hM ≫ GrassmannianFieldBaseChange.map φ 9 14 = p := by
    rw [← hq]
    exact LagrangianCrossFieldParameter.parameterPoint_map φ p hp
  have hgood : matrixPoint L M hM (IsLocalRing.closedPoint L) ∈ goodOpen L := by
    rw [LagrangianGoodOpenFieldBaseChange.goodOpen_eq_preimage φ]
    change (GrassmannianFieldBaseChange.map φ 9 14)
      (matrixPoint L M hM (IsLocalRing.closedPoint L)) ∈ goodOpen K
    rw [← Scheme.Hom.comp_apply, hmap]
    exact (x (IsLocalRing.closedPoint L)).2
  let eR := restrictedFibreIso (familyProjection K) (goodOpen K) x
  let eN := LagrangianCrossFieldFibre.fibreIsoNative φ p hp
  let eQ := pointFibreIso (familyProjection L) q (matrixPoint L M hM) hq
  let eM := LagrangianOrderedFibre.cutIsoFibre L M hM
  let e := eM ≪≫ eQ.symm ≪≫ eN.symm ≪≫ eR.symm
  have hR : eR.inv ≫ pullback.snd (restrictedProjection K) x =
      pullback.snd (familyProjection K) p :=
    iso_inv_base eR _ _ (restrictedFibreIso_hom_base (familyProjection K) (goodOpen K) x)
  have hN : eN.inv ≫ pullback.snd (familyProjection K) p =
      pullback.snd (familyProjection L) q :=
    iso_inv_base eN _ _ (LagrangianCrossFieldFibre.fibreIsoNative_hom_base φ p hp)
  have hQ : eQ.inv ≫ pullback.snd (familyProjection L) q =
      pullback.snd (familyProjection L) (matrixPoint L M hM) :=
    iso_inv_base eQ _ _ (pointFibreIso_hom_base (familyProjection L) q (matrixPoint L M hM) hq)
  have he : e.hom ≫ pullback.snd (restrictedProjection K) x = curveProjection L M := by
    calc
      _ = eM.hom ≫ eQ.inv ≫ eN.inv ≫ eR.inv ≫ pullback.snd (restrictedProjection K) x := by
        simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      _ = eM.hom ≫ pullback.snd (familyProjection L) (matrixPoint L M hM) := by rw [hR,hN,hQ]
      _ = _ := LagrangianOrderedFibre.cutIsoFibre_hom_base L M hM
  letI : IsIntegral (LagrangianGeometricFibre.geometricFibre L M hM) :=
    LagrangianGoodOpenRestriction.fibre_integral L M hM hgood
  have hI : IsIntegral (curve L M) := IsIntegral.of_isIso eM.inv
  letI : IsIntegral (curve L M) := hI
  letI : SmoothOfRelativeDimension 1
      (pullback.snd (familyProjection L) (matrixPoint L M hM)) :=
    LagrangianGoodOpenRestriction.fibre_smooth L M hM hgood
  have hS : SmoothOfRelativeDimension 1 (curveProjection L M) := by
    have h : SmoothOfRelativeDimension (0 + 1)
        (eM.hom ≫ pullback.snd (familyProjection L) (matrixPoint L M hM)) := inferInstance
    rw [LagrangianOrderedFibre.cutIsoFibre_hom_base] at h
    exact h
  letI : SmoothOfRelativeDimension 1 (curveProjection L M) := hS
  exact ⟨M,hM,e,hmap,he,hI,hS,LagrangianTransverseGenusNine.genus_eq_nine L M hM⟩

end Original
end M9Native.LagrangianGoodOpenOrderedModel
