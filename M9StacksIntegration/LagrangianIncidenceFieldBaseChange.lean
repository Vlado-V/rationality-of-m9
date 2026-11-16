module

public import M9StacksIntegration.LagrangianIncidenceParameterBaseChange
public import M9StacksIntegration.LagrangianDeterminantFieldRows
public import M9StacksIntegration.LagrangianLinearSectionEquations
public import M9StacksIntegration.LagrangianParameterRowComparison

/-! The full original universal incidence family commutes with field
base change. The proof transports its actual determinant line, actual
rank-five quotient and actual fourteen tensor summands. It identifies
full zero ideals, retaining nilpotents and both original projections. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.LagrangianIncidenceFieldBaseChange
open LagrangianLinearSections LagrangianMatrixChart
open AlgebraicGeometry.Grassmannian
open LagrangianIncidenceParameterBaseChange
open LagrangianPluckerTrivialization
open LinearIncidenceTensorCoordinates
open SectionZeroIdealFactorization

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

/-- The exact parameter map is the native Grassmannian field-base map. -/
theorem parameterMap_eq {T : Scheme.{u}} (q : T ⟶ parameter L) :
    parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q =
      q ≫ GrassmannianFieldBaseChange.map φ 9 14 := by
  apply pullback.hom_ext <;>
    simp only [parameterMap_projection, parameterMap_toIntegral, Category.assoc,
      GrassmannianFieldBaseChange.map_projection, GrassmannianFieldBaseChange.map_toIntegral]

def ambientMap : ambient L ⟶ ambient K :=
  pullback.lift (toLG L ≫ LagrangianFieldBaseChange.map φ)
    (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) (toParameter L))
    (by
      rw [Category.assoc, LagrangianFieldBaseChange.map_projection, parameterMap_projection]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ GrassmannianFieldBaseChange.specMap φ) (ambient_over L)))

@[reassoc (attr := simp)] theorem ambientMap_toLG :
    ambientMap φ ≫ toLG K = toLG L ≫ LagrangianFieldBaseChange.map φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem ambientMap_toParameter :
    ambientMap φ ≫ toParameter K = toParameter L ≫ GrassmannianFieldBaseChange.map φ 9 14 := by
  rw [ambientMap, pullback.lift_snd, parameterMap_eq]

theorem ambientMap_isPullback : IsPullback (ambientMap φ) (toParameter L)
    (toParameter K) (GrassmannianFieldBaseChange.map φ 9 14) := by
  apply IsPullback.of_right (h₁₂ := toLG K) (h₂₂ := parameterProjection K)
  · have h := (IsPullback.of_hasPullback (LagrangianGrassmannian.projection L)
        (parameterProjection L)).paste_horiz (LagrangianFieldBaseChange.map_isPullback φ)
    simpa only [ambientMap_toLG, GrassmannianFieldBaseChange.map_projection] using h
  · exact ambientMap_toParameter φ
  · exact IsPullback.of_hasPullback _ _

def lineIso : (Scheme.Modules.pullback (ambientMap φ)).obj (lineBundle K) ≅ lineBundle L :=
  LagrangianParameterRowComparison.lineComparison K (ambientMap φ) ≪≫
    (Scheme.Modules.pullbackCongr (ambientMap_toLG φ)).app
      (LagrangianPluckerQuotient.determinantLine K) ≪≫
    LagrangianDeterminantFieldRows.pullbackIso φ (toLG L)

theorem lineIso_section (i : Fin 14) :
    (lineIso φ).hom.app ⊤
      (pullbackGlobalSections (ambientMap φ) (lineBundle K) (lineSection K i)) =
      lineSection L i := by
  let D := LagrangianPluckerQuotient.determinantLine K
  let s := LagrangianPluckerQuotient.primitiveSections K i
  have hc := SectionsEqualizer.pullbackGlobalSections_comp (ambientMap φ) (toLG K) D s
  have hn := SectionsEqualizer.pullbackGlobalSections_congr (ambientMap_toLG φ) D s
  have ht := LagrangianDeterminantFieldRows.pullbackIso_primitive φ (toLG L) i
  exact (congrArg (fun z => (LagrangianDeterminantFieldRows.pullbackIso φ (toLG L)).hom.app ⊤
    (((Scheme.Modules.pullbackCongr (ambientMap_toLG φ)).app D).hom.app ⊤ z)) hc).trans
      ((congrArg ((LagrangianDeterminantFieldRows.pullbackIso φ (toLG L)).hom.app ⊤) hn).trans ht)

theorem quotient_isomorphic :
    (pullbackPresentation (ambientMap φ) (ambientQuotient K)).Isomorphic (ambientQuotient L) := by
  apply LagrangianGrassmannian.presentation_isomorphic_of_class_eq
  calc
    _ = (⟦pullbackPresentation (ambientMap φ ≫ toParameter K) (parameterQuotient K)⟧ :
      Points (ambient L) 9 14) :=
      Quotient.sound (.rel _ _ (pullbackPresentation_comp_isomorphic
        (toParameter K) (ambientMap φ) (parameterQuotient K)))
    _ = ⟦pullbackPresentation
      (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) (toParameter L))
        (parameterQuotient K)⟧ := by rw [ambientMap_toParameter, parameterMap_eq]
    _ = ⟦ambientQuotient L⟧ := parameterMap_class K L
      (GrassmannianFieldBaseChange.specMap φ) (toParameter L)

def quotientIso : (Scheme.Modules.pullback (ambientMap φ)).obj (quotientFive K) ≅ quotientFive L :=
  Classical.choose (quotient_isomorphic φ)

theorem quotientIso_triangle :
    (pullbackPresentation (ambientMap φ) (ambientQuotient K)).map ≫ (quotientIso φ).hom =
      (ambientQuotient L).map := Classical.choose_spec (quotient_isomorphic φ)

theorem quotientIso_section (i : Fin 14) :
    (quotientIso φ).hom.app ⊤
      (pullbackGlobalSections (ambientMap φ) (quotientFive K) (quotientSection K i)) =
      quotientSection L i := by
  have hb := FiniteFreeBasisPullback.pullbackPresentation_basis
    (ambientMap φ) (ambientQuotient K) i
  change Scheme.Modules.Hom.app (X := ambient L)
    (pullbackPresentation (ambientMap φ) (ambientQuotient K)).map ⊤
      (freeBasisSection (ambient L) 14 i) =
    pullbackGlobalSections (ambientMap φ) (quotientFive K) (quotientSection K i) at hb
  rw [← hb]
  exact congrArg (fun q => Scheme.Modules.Hom.app (X := ambient L) q ⊤
    (freeBasisSection (ambient L) 14 i)) (quotientIso_triangle φ)

def equationIso : (Scheme.Modules.pullback (ambientMap φ)).obj (equationBundle K) ≅
    equationBundle L :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (ambientMap φ)
    (lineBundle K) (quotientFive K) ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductIso (ambient L).sheaf.obj
        (ambient L).ringCatSheaf.property (lineIso φ) (quotientIso φ)

theorem equationIso_tensor (s : Γ(lineBundle K, ⊤)) (t : Γ(quotientFive K, ⊤)) :
    (equationIso φ).hom.app ⊤
      (pullbackGlobalSections (ambientMap φ) (equationBundle K)
        (tensorTop (ambient K) (lineBundle K) (quotientFive K) s t)) =
      tensorTop (ambient L) (lineBundle L) (quotientFive L)
        ((lineIso φ).hom.app ⊤ (pullbackGlobalSections (ambientMap φ) (lineBundle K) s))
        ((quotientIso φ).hom.app ⊤ (pullbackGlobalSections (ambientMap φ) (quotientFive K) t)) := by
  refine (congrArg (fun z =>
    ((Stacks.SheafOfModules.Invertible.tensorProductIso (ambient L).sheaf.obj
      (ambient L).ringCatSheaf.property (lineIso φ) (quotientIso φ)).hom.val.app (op ⊤) z))
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt (ambientMap φ)
      (lineBundle K) (quotientFive K) s t)).trans ?_
  exact Stacks.SheafOfModules.tensorSections_tensorProductIsoAt (ambient L).sheaf.obj
    (ambient L).ringCatSheaf.property (op ⊤) _ _ _ _ (lineIso φ) (quotientIso φ) _ _

theorem equationIso_section :
    (equationIso φ).hom.app ⊤
      (pullbackGlobalSections (ambientMap φ) (equationBundle K) (equationSection K)) =
      equationSection L := by
  simp only [equationSection, LagrangianLinearSectionEquations.tensorSection_eq_tensorTop,
    map_sum, equationIso_tensor, lineIso_section, quotientIso_section]

/-- Equality of the full actual incidence ideals under the actual field-base map. -/
theorem ideal_eq_comap : ideal L = (ideal K).comap (ambientMap φ) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (ambientMap φ)).obj (equationBundle K)) 5 :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      (ambientMap φ).base (ambientMap φ).toRingCatSheafHom (equationBundle K) 5 inferInstance
  rw [ideal_baseChange K (ambientMap φ), sectionZeroIdeal_eq_of_iso 5 (equationIso φ),
    equationIso_section]
  rfl

private theorem subschemeι_transport {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

def preimageIso : family L ≅ pullback (ambientMap φ) (inclusion K) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (ideal_eq_comap φ)) ≪≫
    (ideal K).comapIso (ambientMap φ)

@[reassoc (attr := simp)] theorem preimageIso_hom_fst :
    (preimageIso φ).hom ≫ pullback.fst (ambientMap φ) (inclusion K) = inclusion L := by
  simp only [preimageIso, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact subschemeι_transport (ideal_eq_comap φ)

def familyMap : family L ⟶ family K := (preimageIso φ).hom ≫ pullback.snd _ _

@[reassoc (attr := simp)] theorem familyMap_inclusion :
    familyMap φ ≫ inclusion K = inclusion L ≫ ambientMap φ := by
  rw [familyMap, Category.assoc, ← pullback.condition, ← Category.assoc, preimageIso_hom_fst]

theorem inclusion_isPullback : IsPullback (inclusion L) (familyMap φ) (ambientMap φ) (inclusion K) :=
  IsPullback.of_iso_pullback ⟨(familyMap_inclusion φ).symm⟩ (preimageIso φ)
    (preimageIso_hom_fst φ) rfl

/-- The literal original universal-family field-base-change square. -/
theorem familyMap_isPullback : IsPullback (familyMap φ) (familyProjection L)
    (familyProjection K) (GrassmannianFieldBaseChange.map φ 9 14) :=
  (inclusion_isPullback φ).flip.paste_vert (ambientMap_isPullback φ)

@[reassoc (attr := simp)] theorem familyMap_projection :
    familyMap φ ≫ familyProjection K = familyProjection L ≫ GrassmannianFieldBaseChange.map φ 9 14 :=
  (familyMap_isPullback φ).w

end M9Native.LagrangianIncidenceFieldBaseChange
