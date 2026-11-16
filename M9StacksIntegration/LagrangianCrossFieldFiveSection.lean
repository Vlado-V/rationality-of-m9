module

public import M9StacksIntegration.LagrangianFibreFiveSection
public import M9StacksIntegration.LagrangianCrossFieldFibre

/-! Literal five-section models for actual extension-field fibres of the
original incidence family, retaining both the original LG map and the base map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianCrossFieldFiveSection

open LagrangianLinearSections LagrangianFibreFactorization LagrangianFibreFiveSection
open LagrangianCrossFieldParameter LagrangianCrossFieldFibre

variable {K L : Type u} [Field K] [Field L] [CharZero K]
  (φ : K →+* L) (p : Spec (.of L) ⟶ parameter K)
  (hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

/-- The actual native L-LG immersion is induced by the genuine field-fibre
comparison, rather than chosen from a model. -/
def nativeInclusion : pullback (familyProjection K) p ⟶ LagrangianGrassmannian.space L :=
  (fibreIsoNative φ p hp).hom ≫ pullback.fst (familyProjection L) (parameterPoint p) ≫
    familyToLG L

@[reassoc] theorem nativeInclusion_toOriginal :
    nativeInclusion φ p hp ≫ LagrangianFieldBaseChange.map φ =
      pullback.fst (familyProjection K) p ≫ familyToLG K :=
  fibreIsoNative_hom_toLG φ p hp

@[reassoc] theorem nativeInclusion_over :
    nativeInclusion φ p hp ≫ LagrangianGrassmannian.projection L =
      pullback.snd (familyProjection K) p := by
  calc
    _ = (fibreIsoNative φ p hp).hom ≫
        (pullback.fst (familyProjection L) (parameterPoint p) ≫ familyToLG L ≫
          LagrangianGrassmannian.projection L) := by
      simp only [nativeInclusion,Category.assoc]
    _ = (fibreIsoNative φ p hp).hom ≫
        pullback.snd (familyProjection L) (parameterPoint p) :=
      congrArg (fun a => (fibreIsoNative φ p hp).hom ≫ a) (native_fibre_base p)
    _ = _ := fibreIsoNative_hom_base φ p hp

/-- No section-model, matrix-class, field-isomorphism or immersion
compatibility is supplied: the literal five equations and the genuine
scheme isomorphism are constructed from the original parameter. -/
theorem exists_fiveSectionIso :
    letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
    ∃ (s : Γ(LagrangianFiveSectionModel.equationBundle L,⊤))
      (e : LagrangianFiveSectionModel.curve L s ≅ pullback (familyProjection K) p),
      e.hom ≫ nativeInclusion φ p hp = LagrangianFiveSectionModel.inclusion L s ∧
      e.hom ≫ pullback.fst (familyProjection K) p ≫ familyToLG K =
        LagrangianFiveSectionModel.inclusion L s ≫ LagrangianFieldBaseChange.map φ ∧
      e.hom ≫ pullback.snd (familyProjection K) p =
        LagrangianFiveSectionModel.structureMap L s := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  obtain ⟨s,e₀,he₀⟩ := every_parameter_fiveSection L (parameterPoint p)
    (parameterPoint_projection p)
  let eN := fibreIsoNative φ p hp
  let e := e₀ ≪≫ pullbackSymmetry (parameterPoint p) (familyProjection L) ≪≫ eN.symm
  have he : e.hom ≫ nativeInclusion φ p hp = LagrangianFiveSectionModel.inclusion L s := by
    dsimp only [e,Iso.trans_hom,Iso.symm_hom,nativeInclusion]
    simp only [Category.assoc]
    change e₀.hom ≫ (pullbackSymmetry (parameterPoint p) (familyProjection L)).hom ≫
      eN.inv ≫ eN.hom ≫ pullback.fst (familyProjection L) (parameterPoint p) ≫
        familyToLG L = _
    simp only [Iso.inv_hom_id_assoc,pullbackSymmetry_hom_comp_fst_assoc]
    exact he₀
  refine ⟨s,e,he,?_,?_⟩
  · rw [← nativeInclusion_toOriginal φ p hp,← Category.assoc,he]
  · rw [← nativeInclusion_over φ p hp,← Category.assoc,he]

end M9Native.LagrangianCrossFieldFiveSection
