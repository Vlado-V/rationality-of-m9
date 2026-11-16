module

public import M9StacksIntegration.SplitLineProjectiveZero
public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates
public import M9StacksIntegration.LagrangianSectionGeneration
public import M9StacksIntegration.QuotientSectionMorphism

/-! The full split-hyperplane zero-scheme comparison retains the
ORIGINAL sheaf-graded projective bundle and its original tautological
quotient. The presentation comparison is proved on actual sections,
not supplied as a line or equation identification. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf
  AlgebraicGeometry.Scheme.unitModule SheafOfModules.unit PresheafOfModules.unit
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
universe u
namespace M9Native.ChowSplitLineProjectiveZero

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (q : F ⟶ G) [Epi q] (S : UnitSplitting q)

abbrev ambient (F : X.Modules) [F.IsQuasicoherent] := (symGradedBundle F).scheme
abbrev projection (F : X.Modules) [F.IsQuasicoherent] : ambient F ⟶ X :=
  (symGradedBundle F).toBase
abbrev twist (F : X.Modules) [F.IsQuasicoherent] : (ambient F).Modules :=
  Stacks.ProjectiveBundleSplitting.tautologicalTwist F
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)
abbrev tautological (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback (projection F)).obj F ⟶ twist F :=
  Stacks.ProjectiveBundleSplitting.tautologicalMap F
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)

instance twist_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twist F) 1 := by
  let : SheafOfModules.IsInvertible (ambient F).presheaf (ambient F).ringCatSheaf.2
      (twist F) := Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist F _
  exact Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme _ _

/-- The actual original tautological quotient applied to the actual
original global section of the actual split subline. -/
def originalSection : Γ(twist F,⊤) :=
  (tautological F).app ⊤
    (pullbackGlobalSections (projection F) F (S.σ.app ⊤ (1 : Γ(X,⊤))))

def zeroIdeal : (ambient F).IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal (ambient F) (twist F) (originalSection q S)

theorem unitHom_pullback {P T : Scheme.{u}} (f : T ⟶ P) (L : P.Modules) (s : Γ(L,⊤)) :
    Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
        (pullbackGlobalSections f L s) =
      (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L s) := by
  apply (cancel_epi (Scheme.Modules.pullbackUnitIso f).hom).mp
  simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  exact (Scheme.Modules.pullback_map_unitHomEquivTop f L s).symm

omit [G.IsQuasicoherent] [Epi q] in
theorem originalSection_unitHom :
    Scheme.Modules.unitHomEquivTop (twist F) (originalSection q S) =
      (Scheme.Modules.pullbackUnitIso (projection F)).inv ≫
        (Scheme.Modules.pullback (projection F)).map S.σ ≫ tautological F := by
  unfold originalSection
  rw [QuotientSectionMorphism.unitHom_quotient]
  have hσ : Scheme.Modules.unitHomEquivTop F (S.σ.app ⊤ (1 : Γ(X,⊤)))=S.σ := by
    apply LagrangianSectionGeneration.unitHom_ext_top_one
    exact LagrangianAffineDeterminant.unitHom_top_one F _
  rw [hσ]

omit [G.IsQuasicoherent] [Epi q] in
theorem native_section_eq_pullback : hyperplaneSection S.σ =
    pullbackGlobalSections (bundlePresentationIso F).inv (twist F) (originalSection q S) := by
  apply (Scheme.Modules.unitHomEquivTop (tautologicalDatumTwist F)).injective
  rw [unitHomEquivTop_hyperplaneSection]
  change hyperplaneSectionHom S.σ =
    Scheme.Modules.unitHomEquivTop
      ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj (twist F))
      (pullbackGlobalSections (bundlePresentationIso F).inv (twist F) (originalSection q S))
  rw [unitHom_pullback,originalSection_unitHom]
  change (Scheme.Modules.pullbackUnitIso (projectiveBundleToBase X F)).inv ≫
      (Scheme.Modules.pullback (projectiveBundleToBase X F)).map S.σ ≫
      (Scheme.Modules.pullbackCongr (bundlePresentationIso_inv_comp_toBase F)).inv.app F ≫
      (Scheme.Modules.pullbackComp (bundlePresentationIso F).inv (projection F)).inv.app F ≫
      (Scheme.Modules.pullback (bundlePresentationIso F).inv).map (tautological F) = _
  have h := @QuotientSectionMorphism.quotient_unit_morphism_transport
    X (ambient F) (projectiveBundle X F) (projection F) F (twist F)
    (tautological F) S.σ (bundlePresentationIso F).inv (projectiveBundleToBase X F)
    (bundlePresentationIso_inv_comp_toBase F)
  -- Retain the opaque categorical lemma application. The kernel checks
  -- the two definitionally equal projective-bundle presentations;
  -- elaborator normalization of their module dictionaries is expensive.
  run_tac Lean.Elab.Tactic.withMainContext do
    let hdecl ← Lean.Meta.getLocalDeclFromUserName `h
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar hdecl.fvarId)
    Lean.Elab.Tactic.replaceMainGoal []

/-- The genuine presentation comparison identifies FULL zero ideals. -/
theorem native_zeroIdeal_eq_comap : SplitLineProjectiveZero.zeroIdeal q S =
    (zeroIdeal q S).comap (bundlePresentationIso F).inv := by
  change SectionZeroIdealFactorization.sectionZeroIdeal (projectiveBundle X F)
    (tautologicalDatumTwist F) (hyperplaneSection S.σ) = _
  rw [native_section_eq_pullback]
  exact SectionZeroIdealFactorization.sectionZeroIdeal_pullback
    (bundlePresentationIso F).inv (twist F) 1 (originalSection q S)

def nativeToOriginalIso : (SplitLineProjectiveZero.zeroIdeal q S).subscheme ≅
    (zeroIdeal q S).subscheme :=
  eqToIso (congrArg (fun I : (projectiveBundle X F).IdealSheafData => I.subscheme)
    (native_zeroIdeal_eq_comap q S)) ≪≫
    (zeroIdeal q S).comapIso (bundlePresentationIso F).inv ≪≫
    asIso (pullback.snd (bundlePresentationIso F).inv (zeroIdeal q S).subschemeι)

@[reassoc]
theorem nativeToOriginalIso_ambient :
    (nativeToOriginalIso q S).hom ≫ (zeroIdeal q S).subschemeι =
      (SplitLineProjectiveZero.zeroIdeal q S).subschemeι ≫ (bundlePresentationIso F).inv := by
  rw [nativeToOriginalIso, Iso.trans_hom, Iso.trans_hom, Category.assoc,
    Category.assoc, show (asIso (pullback.snd (bundlePresentationIso F).inv
      (zeroIdeal q S).subschemeι)).hom = pullback.snd _ _ from rfl,
    ← pullback.condition]
  simp only [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc]
  exact congrArg (· ≫ (bundlePresentationIso F).inv)
    (LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (native_zeroIdeal_eq_comap q S))

variable (hG : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 G)

def zeroIsoBase : (zeroIdeal q S).subscheme ≅ X :=
  (nativeToOriginalIso q S).symm ≪≫ SplitLineProjectiveZero.zeroIsoBase q S hG

/-- The SAME original structural projection is the actual isomorphism. -/
theorem zeroIsoBase_hom : (zeroIsoBase q S hG).hom =
    (zeroIdeal q S).subschemeι ≫ projection F := by
  apply (cancel_epi (nativeToOriginalIso q S).hom).mp
  rw [zeroIsoBase, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    ← Category.assoc, nativeToOriginalIso_ambient, Category.assoc,
    bundlePresentationIso_inv_comp_toBase, SplitLineProjectiveZero.zeroIsoBase_hom]

include hG in
theorem zeroProjection_isIso : IsIso ((zeroIdeal q S).subschemeι ≫ projection F) := by
  rw [← zeroIsoBase_hom q S hG]
  infer_instance

end M9Native.ChowSplitLineProjectiveZero
