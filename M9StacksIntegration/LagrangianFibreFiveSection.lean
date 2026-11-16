module

public import M9StacksIntegration.LagrangianFiveSectionModel
public import M9StacksIntegration.LagrangianMatrixPointRows
public import M9StacksIntegration.LagrangianFibreFactorization
public import M9StacksIntegration.LagrangianParameterMatrix

/-! The original incidence fibre is the genuine zero scheme of a section
of the literal determinant-line-first, free-five-second equation bundle.
The bundle comparison is constructed from the original universal quotient
class, and the actual LG immersion is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianFibreFiveSection

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianLinearSections LagrangianMatrixPointRows LagrangianFibreFactorization
open LagrangianParameterRowComparison

variable (K : Type u) [Field K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- The actual product map determined by the original matrix parameter. -/
def fixedMap : space K ⟶ LagrangianLinearSections.ambient K :=
  fixedAmbient K (matrixPoint K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM) (𝟙 _)

@[reassoc (attr := simp)] theorem fixedMap_toLG : fixedMap K M hM ≫ toLG K = 𝟙 _ :=
  fixedAmbient_toLG K _ _ _

@[reassoc (attr := simp)] theorem fixedMap_toParameter :
    fixedMap K M hM ≫ toParameter K = projection K ≫ matrixPoint K M hM := by
  simpa only [fixedMap,Category.id_comp] using
    fixedAmbient_toParameter K (matrixPoint K M hM)
      (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM) (𝟙 _)

/-- The literal square is a genuine pullback, since the parameter is
an actual point over the original field. -/
theorem fixedMap_isPullback : IsPullback (fixedMap K M hM) (projection K)
    (toParameter K) (matrixPoint K M hM) := by
  apply IsPullback.of_right (h₁₂ := toLG K) (h₂₂ := parameterProjection K)
  · have h : IsPullback (𝟙 (space K)) (projection K) (projection K)
        (𝟙 (Spec (.of K))) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa only [fixedMap_toLG,SplitMatrixGrassmannian.fieldPoint_projection] using h
  · exact fixedMap_toParameter K M hM
  · exact IsPullback.of_hasPullback _ _

/-- The actual pulled determinant line has the original line as its target. -/
def fixedLineIso : (Scheme.Modules.pullback (fixedMap K M hM)).obj (lineBundle K) ≅
    determinantLine K :=
  lineComparison K (fixedMap K M hM) ≪≫
    (Scheme.Modules.pullbackCongr (fixedMap_toLG K M hM)).app (determinantLine K) ≪≫
      (Scheme.Modules.pullbackId (space K)).app (determinantLine K)

theorem fixedMap_parameter_condition :
    fixedMap K M hM ≫ toParameter K =
      ((fixedMap K M hM ≫ toLG K) ≫ projection K) ≫ matrixPoint K M hM := by
  rw [fixedMap_toParameter,fixedMap_toLG,Category.id_comp]

/-- The free-five frame is derived from the actual representing quotient class. -/
def fixedQuotientIso :
    (Scheme.Modules.pullback (fixedMap K M hM)).obj (quotientFive K) ≅ freeOn (space K) 5 :=
  (quotientFrame K (fixedMap K M hM) M hM (fixedMap_parameter_condition K M hM)).choose

/-- Actual pullback and tensor comparisons identify the original equation
bundle with the literal five-equation bundle; no comparison is supplied. -/
def fixedEquationIso :
    (Scheme.Modules.pullback (fixedMap K M hM)).obj (LagrangianLinearSections.equationBundle K) ≅
      LagrangianFiveSectionModel.equationBundle K :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (fixedMap K M hM)
      (lineBundle K) (quotientFive K) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso (space K).sheaf.obj
      (space K).ringCatSheaf.2 (fixedLineIso K M hM) (fixedQuotientIso K M hM)

/-- The five-section is the actual original incidence section transported
by the derived equation-bundle isomorphism. -/
def fiveSection : Γ(LagrangianFiveSectionModel.equationBundle K,⊤) :=
  (fixedEquationIso K M hM).hom.app ⊤
    (pullbackGlobalSections (fixedMap K M hM)
      (LagrangianLinearSections.equationBundle K) (equationSection K))

/-- Equality of genuine ideal sheaves, including on nonreduced schemes. -/
theorem fixedIdeal_eq : (LagrangianLinearSections.ideal K).comap (fixedMap K M hM) =
    SectionZeroConormal.zeroIdeal (LagrangianFiveSectionModel.equationBundle K)
      (fiveSection K M hM) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (fixedMap K M hM)).obj
        (LagrangianLinearSections.equationBundle K)) 5 :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      (fixedMap K M hM).base (fixedMap K M hM).toRingCatSheafHom
      (LagrangianLinearSections.equationBundle K) 5 inferInstance
  exact (ideal_baseChange K (fixedMap K M hM)).trans
    (sectionZeroIdeal_eq_of_iso 5 (fixedEquationIso K M hM)
      (pullbackGlobalSections (fixedMap K M hM)
        (LagrangianLinearSections.equationBundle K) (equationSection K)))

def fixedZeroIsoFibre : ((LagrangianLinearSections.ideal K).comap (fixedMap K M hM)).subscheme ≅
    fibre K (matrixPoint K M hM) :=
  (LagrangianLinearSections.ideal K).comapIso (fixedMap K M hM) ≪≫
    ((IsPullback.of_hasPullback (fixedMap K M hM) (LagrangianLinearSections.inclusion K)).flip.paste_vert
      (fixedMap_isPullback K M hM)).isoPullback ≪≫
        pullbackSymmetry (familyProjection K) (matrixPoint K M hM)

theorem fixedZeroIsoFibre_hom_toLG :
    (fixedZeroIsoFibre K M hM).hom ≫ fibreToLG K (matrixPoint K M hM) =
      ((LagrangianLinearSections.ideal K).comap (fixedMap K M hM)).subschemeι := by
  dsimp only [fixedZeroIsoFibre,fibreToLG,familyToLG]
  simp only [Iso.trans_hom,Category.assoc,pullbackSymmetry_hom_comp_snd_assoc,
    IsPullback.isoPullback_hom_fst_assoc]
  change ((LagrangianLinearSections.ideal K).comapIso (fixedMap K M hM)).hom ≫
      pullback.snd (fixedMap K M hM) (LagrangianLinearSections.inclusion K) ≫ inclusion K ≫ toLG K = _
  rw [← pullback.condition_assoc]
  calc
    _ = ((LagrangianLinearSections.ideal K).comap (fixedMap K M hM)).subschemeι ≫
        fixedMap K M hM ≫ toLG K := by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ fixedMap K M hM ≫ toLG K)
        (Scheme.IdealSheafData.comapIso_hom_fst (LagrangianLinearSections.ideal K) (fixedMap K M hM))
    _ = _ := by rw [fixedMap_toLG,Category.comp_id]

/-- The literal five-section zero scheme is the original incidence fibre. -/
def fiveSectionIsoFibre : LagrangianFiveSectionModel.curve K (fiveSection K M hM) ≅
    fibre K (matrixPoint K M hM) :=
  eqToIso (congrArg (fun I : (space K).IdealSheafData => I.subscheme)
    (fixedIdeal_eq K M hM).symm) ≪≫ fixedZeroIsoFibre K M hM

/-- The comparison retains the literal original LG immersion. -/
@[reassoc] theorem fiveSectionIsoFibre_hom_toLG :
    (fiveSectionIsoFibre K M hM).hom ≫ fibreToLG K (matrixPoint K M hM) =
      LagrangianFiveSectionModel.inclusion K (fiveSection K M hM) := by
  rw [fiveSectionIsoFibre,Iso.trans_hom,Category.assoc,fixedZeroIsoFibre_hom_toLG]
  exact eqToIso_subscheme_ι _ _ (fixedIdeal_eq K M hM).symm

/-- Every original field-valued parameter has a literal five-section
model, with its actual immersion retained and no model premise. -/
theorem every_parameter_fiveSection (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _) :
    ∃ (s : Γ(LagrangianFiveSectionModel.equationBundle K,⊤))
      (e : LagrangianFiveSectionModel.curve K s ≅ fibre K p),
      e.hom ≫ fibreToLG K p = LagrangianFiveSectionModel.inclusion K s := by
  obtain ⟨M,hM,rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact ⟨fiveSection K M hM,fiveSectionIsoFibre K M hM,
    fiveSectionIsoFibre_hom_toLG K M hM⟩

end M9Native.LagrangianFibreFiveSection
