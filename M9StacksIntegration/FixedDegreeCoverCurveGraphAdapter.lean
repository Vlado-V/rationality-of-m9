module

public import M9StacksIntegration.GraphHilbertMembershipComparison
public import M9StacksIntegration.RelativeCoverSchemeEvaluation
public import M9StacksIntegration.PolarizedCoverGraphDegree
public import M9StacksIntegration.PolarizedCurveDegreeOpen
public import M9StacksIntegration.ConstantProjectiveLinePolarization
public import M9StacksIntegration.ConstantP1CoverDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleRelativeAmpleTransfer
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Actual polarized scheme covers in the native graph Hilbert locus

Both native polarizations are the associated modules of the specified
original scheme lines. Their literal readings, graph tensor restrictions,
and integer powers are derived. The actual proper-flat family Euler
base-change theorem retains every original field, with its original
structure-map action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RelativeVeryAmple
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace M9Native.FixedDegreeCoverCurveGraphAdapter
open AlgebraicGeometry.Space
open GraphHilbertEulerComparison GraphHilbertMembershipComparison

section SchemePowers

variable {V W : Scheme.{u}}

/-- An original line isomorphism gives its actual integer-power isomorphism. -/
def originalPowerCongr {F G : V.Modules}
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.property F]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.property G]
    (e : F ≅ G) (n : ℤ) :
    Stacks.SheafOfModules.Invertible.tensorPower V.presheaf V.ringCatSheaf.property F n ≅
      Stacks.SheafOfModules.Invertible.tensorPower V.presheaf V.ringCatSheaf.property G n := by
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    V.presheaf V.ringCatSheaf.property F
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    V.presheaf V.ringCatSheaf.property G
  exact Stacks.SheafOfModules.TensorPower.tensorPowerCongr V.presheaf V.ringCatSheaf.property e n

/-- Pullback commutes with every integer power of an actual original line. -/
def originalPullbackPowerIso (r : W ⟶ V) (F : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.property F] (n : ℤ) :
    letI := Stacks.InvertiblePullback.isInvertibleModule_pullback r F
    (Scheme.Modules.pullback r).obj
      (Stacks.SheafOfModules.Invertible.tensorPower V.presheaf V.ringCatSheaf.property F n) ≅
    Stacks.SheafOfModules.Invertible.tensorPower W.presheaf W.ringCatSheaf.property
      ((Scheme.Modules.pullback r).obj F) n := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback r F
  letI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.property
      ((RingedSpaceModuleAdjunction.modulePullback r.toLRSHom.toShHom).obj F) :=
    Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf r F
  let e := Stacks.ProjectiveBundleQuotients.pullbackIso r
  exact e.app _ ≪≫ Stacks.TensorPowerPullback.pullbackIntPowIso r.toLRSHom.toShHom F n ≪≫
    originalPowerCongr (e.app F).symm n

end SchemePowers

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q Y : BigFppfOver B S hS} (z : Z ⟶ Q) (x : X ⟶ Q)
  (p : RelativeMorphism B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
    (yoneda.map z) (yoneda.map x) (yoneda.obj Y))
  (hz : yoneda.relativelyRepresentable (yoneda.map z))

variable (N0 : ((BigFppfOver.toScheme B S hS).obj Z).Modules)
  [hN0 : SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj Z).presheaf
    ((BigFppfOver.toScheme B S hS).obj Z).ringCatSheaf.property N0]
  (M0 : ((BigFppfOver.toScheme B S hS).obj X).Modules)
  [hM0 : SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj X).presheaf
    ((BigFppfOver.toScheme B S hS).obj X).ringCatSheaf.property M0]

/-- The canonical native source polarization, from the specified original line. -/
abbrev nativeSourceLine : Space.Modules.{u,u} B S hS (schemeSpace Z).1 (schemeSpace Z).2 :=
  associatedModule B S hS Z N0

/-- The canonical native target polarization, from the specified original line. -/
abbrev nativeTargetLine : Space.Modules.{u,u} B S hS (schemeSpace X).1 (schemeSpace X).2 :=
  associatedModule B S hS X M0

instance nativeSourceLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (schemeSpace Z).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace Z).1 (schemeSpace Z).2).O).property
      (nativeSourceLine N0) :=
  isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule B S hS Z N0
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN0)

instance nativeTargetLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (schemeSpace X).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace X).1 (schemeSpace X).2).O).property
      (nativeTargetLine M0) :=
  isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule B S hS X M0
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM0)

/-- Native relative ampleness is derived from the actual original source line. -/
theorem nativeSourceLine_isRelativelyAmple
    (h : Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B S hS).map z) N0) :
    Space.IsRelativelyAmple B S hS (schemeSpaceMap z) (nativeSourceLine N0) :=
  isRelativelyAmple_schemeSpaceMap_associatedModule z N0 h

/-- Native relative ampleness is derived from the actual original target line. -/
theorem nativeTargetLine_isRelativelyAmple
    (h : Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B S hS).map x) M0) :
    Space.IsRelativelyAmple B S hS (schemeSpaceMap x) (nativeTargetLine M0) :=
  isRelativelyAmple_schemeSpaceMap_associatedModule x M0 h

/-- Every native source-line reading is the actual original pullback. -/
def sourceLineReadingIso {U : BigFppfOver B S hS} (r : U ⟶ Z)
    (q : yoneda.obj U ⟶ yoneda.obj Z) (hq : yoneda.map r = q) :
    baseChangeModule B S hS (nativeSourceLine N0) U q ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj N0 :=
  baseChangeModuleAssociatedModuleIso Z N0
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N0) r q hq

/-- Every native target-line reading is the actual original pullback. -/
def targetLineReadingIso {U : BigFppfOver B S hS} (r : U ⟶ X)
    (q : yoneda.obj U ⟶ yoneda.obj X) (hq : yoneda.map r = q) :
    baseChangeModule B S hS (nativeTargetLine M0) U q ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj M0 :=
  baseChangeModuleAssociatedModuleIso X M0
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule M0) r q hq

/-- The literal original line on the actual chosen universal source. -/
def totalGraphLine :
    ((BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz)).Modules :=
  tensorModules _
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
      (RelativeCoverSchemeEvaluation.toOriginal z x p hz))).obj N0)
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
      (RelativeCoverSchemeEvaluation.evaluation z x p hz))).obj M0)

instance totalGraphLine_isInvertible :
    SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz)).presheaf
      ((BigFppfOver.toScheme B S hS).obj
        (RelativeCoverSchemeEvaluation.source z x p hz)).ringCatSheaf.property
      (totalGraphLine z x p hz N0 M0) := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    ((BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.toOriginal z x p hz)) N0
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    ((BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.evaluation z x p hz)) M0
  dsimp only [totalGraphLine]
  infer_instance

/-- Every actual integer power of the original total graph line. -/
def totalGraphPower (n : ℤ) :=
  Stacks.SheafOfModules.Invertible.tensorPower
    ((BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz)).presheaf
    ((BigFppfOver.toScheme B S hS).obj
      (RelativeCoverSchemeEvaluation.source z x p hz)).ringCatSheaf.property
    (totalGraphLine z x p hz N0 M0) n

instance totalGraphPower_isInvertible (n : ℤ) :
    SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz)).presheaf
      ((BigFppfOver.toScheme B S hS).obj
        (RelativeCoverSchemeEvaluation.source z x p hz)).ringCatSheaf.property
      (totalGraphPower z x p hz N0 M0 n) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ _ n

variable (hsep : Space.IsSeparated B S hS (yoneda.map x))
  (hxfp : Space.IsFinitePresentation B S hS (yoneda.map x))
  (hfp : Space.IsFinitePresentation B S hS (yoneda.map z))
  (hflat : Space.IsFlat B S hS (yoneda.map z))
  (hproper : Space.IsProper B S hS (yoneda.map z))

/-- The actual native graph polarization reads as the literal total
original graph line. Its source and target reading isomorphisms are
proved from the canonical transfers, never supplied as premises. -/
def totalGraphLineReadingIso :
    baseChangeModule B S hS
      (graphAmbientTensor (yoneda.map z) (yoneda.map x)
        (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        (nativeSourceLine N0) (nativeTargetLine M0))
      (RelativeCoverSchemeEvaluation.source z x p hz)
      (graphAmbientFromSource (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hfp hflat hproper hz p) ≅ totalGraphLine z x p hz N0 M0 :=
  graphPolarizationTensorIso (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    hsep hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) ≪≫
  tensorModulesMapIso _
    (sourceLineReadingIso N0 (RelativeCoverSchemeEvaluation.toOriginal z x p hz)
      (hz.fst p.base) (by simp only [RelativeCoverSchemeEvaluation.toOriginal,
        Functor.map_preimage]))
    (targetLineReadingIso M0 (RelativeCoverSchemeEvaluation.evaluation z x p hz)
      ((hz.isPullback p.base).flip.isoPullback.hom ≫ p.morphism)
      (by simp only [RelativeCoverSchemeEvaluation.evaluation,
        RelativeCoverSchemeEvaluation.nativeEvaluation, Functor.map_preimage]))

/-- The actual original projection of the chosen native graph source. -/
abbrev totalProjection :=
  (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.projection z x p hz)

/-- The native residue fibre of the actual source, with no chosen curve iso. -/
abbrev residueScheme (t : (BigFppfOver.toScheme B S hS).obj Y) :=
  graphFibre (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    hsep hxfp hfp hflat hproper hz p t

abbrev residueSiteToSource (t : (BigFppfOver.toScheme B S hS).obj Y) :
    residueScheme z x p hz hsep hxfp hfp hflat hproper t ⟶
      RelativeCoverSchemeEvaluation.source z x p hz :=
  pullback.snd
    ((graphCohObject (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper p).pointSchemeHom t)
    (RelativeCoverSchemeEvaluation.projection z x p hz)

abbrev residueToSource (t : (BigFppfOver.toScheme B S hS).obj Y) :=
  (BigFppfOver.toScheme B S hS).map
    (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t)

abbrev residueProjection (t : (BigFppfOver.toScheme B S hS).obj Y) :=
  (BigFppfOver.toScheme B S hS).map
    (graphFibreProjection (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p t)

theorem residueAmbientMap_hom (t : (BigFppfOver.toScheme B S hS).obj Y) :
    (graphFibreAmbientMap (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p t).hom =
    yoneda.map (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t) ≫
      graphAmbientFromSource (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hfp hflat hproper hz p :=
  congrArg (fun q => q.hom)
    (GraphHilbertResidueFibreComparison.originalFibreAmbientMap_eq
      (graphCohObject (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hxfp hfp hflat hproper p)
      (graphClosedSupport (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hfp hflat hproper p)
      (RelativeCoverSchemeEvaluation.source z x p hz)
      (RelativeCoverSchemeEvaluation.projection z x p hz)
      (graphSupportIso (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hfp hflat hproper hz p)
      (graphSupportIso_projection (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hfp hflat hproper hz p) t)

theorem residueAmbientMap_fst (t : (BigFppfOver.toScheme B S hS).obj Y) :
    yoneda.map (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t ≫
      RelativeCoverSchemeEvaluation.toOriginal z x p hz) =
    (graphFibreAmbientMap (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p t).hom ≫ pullback.fst (yoneda.map z) (yoneda.map x) := by
  rw [residueAmbientMap_hom, Category.assoc, graphAmbientFromSource_fst]
  simp only [Functor.map_comp, RelativeCoverSchemeEvaluation.toOriginal, Functor.map_preimage]

theorem residueAmbientMap_snd (t : (BigFppfOver.toScheme B S hS).obj Y) :
    yoneda.map (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t ≫
      RelativeCoverSchemeEvaluation.evaluation z x p hz) =
    (graphFibreAmbientMap (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p t).hom ≫ pullback.snd (yoneda.map z) (yoneda.map x) := by
  rw [residueAmbientMap_hom, Category.assoc, graphAmbientFromSource_snd]
  simp only [Functor.map_comp, RelativeCoverSchemeEvaluation.evaluation,
    RelativeCoverSchemeEvaluation.nativeEvaluation, Functor.map_preimage]

/-- The original scheme functor's composition law, at the actual module pullback. -/
def sitePullbackCompIso {T₁ T₂ T₃ : BigFppfOver B S hS} (r : T₁ ⟶ T₂) (s : T₂ ⟶ T₃)
    (F : ((BigFppfOver.toScheme B S hS).obj T₃).Modules) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (r ≫ s))).obj F ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map s)).obj F) :=
  eqToIso (congrArg (fun f => (Scheme.Modules.pullback f).obj F)
    ((BigFppfOver.toScheme B S hS).map_comp r s)) ≪≫
  ((Scheme.Modules.pullbackComp _ _).app F).symm

/-- The exact frozen graph-fibre tensor comparison, followed by the
derived scheme transfer readings, is the original pullback of the
literal total graph line. -/
def fibreGraphLineIso (t : (BigFppfOver.toScheme B S hS).obj Y) :
    graphFibreLine (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) t ≅
    (Scheme.Modules.pullback (residueToSource z x p hz hsep hxfp hfp hflat hproper t)).obj
      (totalGraphLine z x p hz N0 M0) :=
  graphFibrePolarizationTensorIso (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) t ≪≫
  tensorModulesMapIso _
    (sourceLineReadingIso N0
      (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t ≫
        RelativeCoverSchemeEvaluation.toOriginal z x p hz) _
      (residueAmbientMap_fst z x p hz hsep hxfp hfp hflat hproper t) ≪≫
      sitePullbackCompIso _ _ N0)
    (targetLineReadingIso M0
      (residueSiteToSource z x p hz hsep hxfp hfp hflat hproper t ≫
        RelativeCoverSchemeEvaluation.evaluation z x p hz) _
      (residueAmbientMap_snd z x p hz hsep hxfp hfp hflat hproper t) ≪≫
      sitePullbackCompIso _ _ M0) ≪≫
  (pullbackTensorModulesIso _ _ _).symm

instance fibreGraphLine_isInvertible (t : (BigFppfOver.toScheme B S hS).obj Y) :
    SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj
        (residueScheme z x p hz hsep hxfp hfp hflat hproper t)).presheaf
      ((BigFppfOver.toScheme B S hS).obj
        (residueScheme z x p hz hsep hxfp hfp hflat hproper t)).ringCatSheaf.property
      (graphFibreLine (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) t) := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (residueToSource z x p hz hsep hxfp hfp hflat hproper t) (totalGraphLine z x p hz N0 M0)
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
    (fibreGraphLineIso z x p hz N0 M0 hsep hxfp hfp hflat hproper t).symm

/-- Actual original line powers match the actual pulled total graph
powers at every integer, including negative twists. -/
def fibreGraphPowerIso (t : (BigFppfOver.toScheme B S hS).obj Y) (n : ℤ) :
    graphFibreLinePower (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) t n ≅
    (Scheme.Modules.pullback (residueToSource z x p hz hsep hxfp hfp hflat hproper t)).obj
      (totalGraphPower z x p hz N0 M0 n) := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (residueToSource z x p hz hsep hxfp hfp hflat hproper t) (totalGraphLine z x p hz N0 M0)
  exact originalPowerCongr (fibreGraphLineIso z x p hz N0 M0 hsep hxfp hfp hflat hproper t) n ≪≫
    (originalPullbackPowerIso _ (totalGraphLine z x p hz N0 M0) n).symm

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

theorem residueOriginalSquare (t : (BigFppfOver.toScheme B S hS).obj Y) :
    IsPullback (residueToSource z x p hz hsep hxfp hfp hflat hproper t)
      (residueProjection z x p hz hsep hxfp hfp hflat hproper t)
      (totalProjection z x p hz)
      (((BigFppfOver.toScheme B S hS).obj Y).fromSpecResidueField t) :=
  (IsPullback.of_hasPullback
    ((graphCohObject (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper p).pointSchemeHom t)
    (RelativeCoverSchemeEvaluation.projection z x p hz)).flip.map (BigFppfOver.toScheme B S hS)

variable [IsProper ((BigFppfOver.toScheme B S hS).map z)]
  [SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B S hS).map z)]

instance totalProjection_isProper : IsProper (totalProjection z x p hz) :=
  RelativeCoverSchemeEvaluation.originalProjection_isProper z x p hz

instance totalProjection_isSmoothRelativeCurve :
    SmoothOfRelativeDimension 1 (totalProjection z x p hz) :=
  RelativeCoverSchemeEvaluation.originalProjection_isSmoothRelativeCurve z x p hz

local instance totalProjectionSmooth : Smooth (totalProjection z x p hz) :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The native graph fibre Euler is the original total family's actual
fibre Euler characteristic. No residue-field identification is an input. -/
theorem graphFibreEuler_eq (t : (BigFppfOver.toScheme B S hS).obj Y) (n : ℤ) :
    ProperFlatFibreEulerCharacteristic.eulerSum
      (((BigFppfOver.toScheme B S hS).obj Y).residueField t)
      (residueProjection z x p hz hsep hxfp hfp hflat hproper t)
      (graphFibreLinePower (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) t n) =
    ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic (totalProjection z x p hz)
      (totalGraphPower z x p hz N0 M0 n) t := by
  have hbc := PolarizedCurveDegreeOpen.fieldEuler_eq (totalProjection z x p hz)
    (totalGraphPower z x p hz N0 M0 n)
    (residueOriginalSquare z x p hz hsep hxfp hfp hflat hproper t)
  change ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic
    (totalProjection z x p hz) (totalGraphPower z x p hz N0 M0 n)
    ((((BigFppfOver.toScheme B S hS).obj Y).fromSpecResidueField t)
      (IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj Y).residueField t))) = _ at hbc
  rw [Scheme.fromSpecResidueField_apply] at hbc
  exact (ProperFlatFibreEulerCharacteristic.eulerSum_congr _ _
    (fibreGraphPowerIso z x p hz N0 M0 hsep hxfp hfp hflat hproper t n)).trans hbc.symm

/-- A literal abbreviation of the native coherent graph HP condition. -/
abbrev graphHP (P : ℤ → ℤ) : Prop :=
  @CoherentObject.HasHilbertPolynomial B S hS
    (structureSheafQuotSituation
      (graphAmbientMap B S hS (yoneda.map z) (yoneda.map x)
        (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2)
      (isFinitePresentation_graphAmbientMap (yoneda.map z) (yoneda.map x)
        (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 hfp hxfp)).toCoherentSituation
    (graphAmbientTensor (yoneda.map z) (yoneda.map x)
      (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      (nativeSourceLine N0) (nativeTargetLine M0))
    (graphCohAmbientTensor_isInvertible (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hxfp hfp (nativeSourceLine N0) (nativeTargetLine M0)) P
    (graphCohObject (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      hsep hxfp hfp hflat hproper p)

/-- The actual native HP condition is exactly the literal original
total graph-line family's fibre Euler condition at every point/integer. -/
theorem graphHP_iff_familyEuler (P : ℤ → ℤ) :
    graphHP z x p N0 M0 hsep hxfp hfp hflat hproper P ↔
    ∀ (t : (BigFppfOver.toScheme B S hS).obj Y) (n : ℤ), P n =
      ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic (totalProjection z x p hz)
        (totalGraphPower z x p hz N0 M0 n) t := by
  have hc := graph_hasHilbertPolynomial_iff_originalEuler
    (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    hsep hxfp hfp hflat hproper hz p (nativeSourceLine N0) (nativeTargetLine M0) P
  constructor
  · intro h t n
    exact (hc.mp h t n).trans (graphFibreEuler_eq z x p hz N0 M0 hsep hxfp hfp hflat hproper t n)
  · intro h
    apply hc.mpr
    intro t n
    exact (h t n).trans (graphFibreEuler_eq z x p hz N0 M0 hsep hxfp hfp hflat hproper t n).symm

/-- Native graph HP membership controls the actual line Euler on every
ORIGINAL field fibre. The proper-flat base-change theorem supplies the
field scalar comparison; no ContainsSpecField or residue-field iso is assumed. -/
theorem fieldEuler_of_graphHP (P : ℤ → ℤ)
    (hP : graphHP z x p N0 M0 hsep hxfp hfp hflat hproper P)
    {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj Y}
    {q : V ⟶ (BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz)}
    {f : V ⟶ Spec (.of K)} [IsProper f]
    (sq : IsPullback q f (totalProjection z x p hz) y) (n : ℤ) :
    ProperFlatFibreEulerCharacteristic.eulerSum K f
      ((Scheme.Modules.pullback q).obj (totalGraphPower z x p hz N0 M0 n)) = P n := by
  have h := (graphHP_iff_familyEuler z x p hz N0 M0 hsep hxfp hfp hflat hproper P).mp hP
  exact (PolarizedCurveDegreeOpen.fieldEuler_eq (totalProjection z x p hz)
    (totalGraphPower z x p hz N0 M0 n) sq).symm.trans (h (y (IsLocalRing.closedPoint K)) n).symm


/-- Membership of the actual native section is the native graph HP
condition of its actual relative morphism. -/
theorem graphHP_of_section_mem (P : ℤ → ℤ)
    (s : (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2
      (schemeSpace Q).2).obj (op Y))
    (hs : s ∈ (relativeHomHilbertPolynomial (schemeSpace Z).2 (schemeSpace X).2
      (schemeSpace Q).2 hsep hxfp hfp hflat hproper
      (graphAmbientTensor (yoneda.map z) (yoneda.map x)
        (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        (nativeSourceLine N0) (nativeTargetLine M0)) P).obj (op Y)) :
    graphHP z x (relativeHomSections B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 Y s)
      N0 M0 hsep hxfp hfp hflat hproper P := by
  rw [Space.mem_relativeHomHilbertPolynomial_iff] at hs
  exact hs

/-- Any actual morphism into the native graph-Hilbert locus, including
the literal representing isomorphism, produces its actual native graph
HP condition. Neither HP nor a line-reading comparison is a premise. -/
theorem graphHP_of_mapToLocus (P : ℤ → ℤ)
    (a : yoneda.obj Y ⟶ (relativeHomHilbertPolynomial
      (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 hsep hxfp hfp hflat hproper
      (graphAmbientTensor (yoneda.map z) (yoneda.map x)
        (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        (nativeSourceLine N0) (nativeTargetLine M0)) P).toFunctor) :
    graphHP z x
      (relativeHomEquiv B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
        (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
        (yoneda.obj Y) (schemeSpace Y).2
        (a ≫ (relativeHomHilbertPolynomial
          (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 hsep hxfp hfp hflat hproper
          (graphAmbientTensor (yoneda.map z) (yoneda.map x)
            (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
            (nativeSourceLine N0) (nativeTargetLine M0)) P).ι))
      N0 M0 hsep hxfp hfp hflat hproper P := by
  let F := relativeHomHilbertPolynomial (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    hsep hxfp hfp hflat hproper
    (graphAmbientTensor (yoneda.map z) (yoneda.map x)
      (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      (nativeSourceLine N0) (nativeTargetLine M0)) P
  let s := yonedaEquiv (a ≫ F.ι)
  have hs : s ∈ F.obj (op Y) := (a.app (op Y) (𝟙 Y)).property
  have heq := relativeHomEquiv_yoneda Y (schemeSpace Y).2 s
  simp only [s, Equiv.symm_apply_apply] at heq
  exact Eq.mpr
    (congrArg (fun r => graphHP z x r N0 M0 hsep hxfp hfp hflat hproper P) heq)
    (graphHP_of_section_mem z x N0 M0 hsep hxfp hfp hflat hproper P s hs)


/-- The literal canonical native graph-polynomial locus. -/
abbrev canonicalGraphLocus (P : ℤ → ℤ) :=
  relativeHomHilbertPolynomial (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    hsep hxfp hfp hflat hproper
    (graphAmbientTensor (yoneda.map z) (yoneda.map x)
      (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
      (nativeSourceLine N0) (nativeTargetLine M0)) P

/-- The actual native relative morphism supplied by a map to the genuine
graph Hilbert locus. For a representing isomorphism this is precisely
the fixed-degree cover scheme's universal relative morphism. -/
def familyOfMapToLocus (P : ℤ → ℤ)
    (a : yoneda.obj Y ⟶
      (canonicalGraphLocus z x N0 M0 hsep hxfp hfp hflat hproper P).toFunctor) :
    RelativeMorphism B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (yoneda.obj Y) :=
  relativeHomEquiv B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
    (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2
    (yoneda.obj Y) (schemeSpace Y).2
    (a ≫ (canonicalGraphLocus z x N0 M0 hsep hxfp hfp hflat hproper P).ι)

theorem section_mem_of_graphHP (P : ℤ → ℤ)
    (s : (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2
      (schemeSpace Q).2).obj (op Y))
    (h : graphHP z x (relativeHomSections B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 Y s)
      N0 M0 hsep hxfp hfp hflat hproper P) :
    s ∈ (canonicalGraphLocus z x N0 M0 hsep hxfp hfp hflat hproper P).obj (op Y) := by
  rw [canonicalGraphLocus, Space.mem_relativeHomHilbertPolynomial_iff]
  exact h



section ConstantTarget

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K : Type u) [Field K]
  (sQ : (BigFppfOver.toScheme B S hS).obj Q ⟶ Spec (.of K))
  (qX : (BigFppfOver.toScheme B S hS).obj X ⟶ Line K)
  (htarget : qX ≫ toBase K = (BigFppfOver.toScheme B S hS).map x ≫ sQ)

/-- The target polarization is the actual pulled original ground O(1). -/
abbrev targetOriginalLine :=
  (Scheme.Modules.pullback qX).obj (ConstantProjectiveLinePolarization.groundLine K)

instance targetOriginalLine_isInvertible :
    SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj X).presheaf
      ((BigFppfOver.toScheme B S hS).obj X).ringCatSheaf.property
      (targetOriginalLine K qX) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback qX _

/-- The original parameter structural map of the actual cover. -/
def originalGroundMap : (BigFppfOver.toScheme B S hS).obj Y ⟶ Spec (.of K) :=
  (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.base z x p) ≫ sQ

/-- Actual native evaluation read on the original source and ground line. -/
def originalLineMap :
    (BigFppfOver.toScheme B S hS).obj (RelativeCoverSchemeEvaluation.source z x p hz) ⟶
      Line K :=
  (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.evaluation z x p hz) ≫ qX

include htarget in
theorem originalLineMap_over :
    originalLineMap z x p hz K qX ≫ toBase K =
      totalProjection z x p hz ≫ originalGroundMap z x p K sQ := by
  rw [originalLineMap, Category.assoc, htarget, ← Category.assoc,
    RelativeCoverSchemeEvaluation.originalEvaluation_over, Category.assoc]
  rfl

/-- The actual source embedding line on an original field fibre. -/
def fieldSourceLine (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :=
  (Scheme.Modules.pullback (pullback.fst (totalProjection z x p hz) a ≫
    (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.toOriginal z x p hz))).obj N0

instance fieldSourceLine_isInvertible (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :
    SheafOfModules.IsInvertible (pullback (totalProjection z x p hz) a).presheaf
      (pullback (totalProjection z x p hz) a).ringCatSheaf.property
      (fieldSourceLine z x p hz N0 L a) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback
    (pullback.fst (totalProjection z x p hz) a ≫
      (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.toOriginal z x p hz)) N0

/-- The genuine field graph tensor is obtained by original module
pullback composition and the actual field-map triangle. -/
def fieldGraphLineIso (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :
    (Scheme.Modules.pullback (pullback.fst (totalProjection z x p hz) a)).obj
      (totalGraphLine z x p hz N0 (targetOriginalLine K qX)) ≅
    PolarizedCoverGraphDegree.graphLine
      (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
        (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a)
      (fieldSourceLine z x p hz N0 L a)
      ((Scheme.Modules.pullback (projectiveSpaceOverMap 1
        (a ≫ originalGroundMap z x p K sQ))).obj
          (ConstantProjectiveLinePolarization.groundLine K)) := by
  let q := pullback.fst (totalProjection z x p hz) a
  let e := (BigFppfOver.toScheme B S hS).map
    (RelativeCoverSchemeEvaluation.evaluation z x p hz)
  let g := fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
    (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a
  let r := projectiveSpaceOverMap 1 (a ≫ originalGroundMap z x p K sQ)
  have hcomp : (q ≫ e) ≫ qX = g ≫ r := by
    simpa only [q, e, g, r, originalLineMap, Category.assoc] using
      (fieldMap_toOriginal K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
        (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a).symm
  exact pullbackTensorModulesIso _ _ _ ≪≫
    tensorModulesMapIso _
      ((Scheme.Modules.pullbackComp q _).app N0)
      ((Scheme.Modules.pullbackComp q e).app (targetOriginalLine K qX) ≪≫
        (Scheme.Modules.pullbackComp (q ≫ e) qX).app _ ≪≫
        (Scheme.Modules.pullbackCongr hcomp).app _ ≪≫
        ((Scheme.Modules.pullbackComp g r).app _).symm)

/-- Every integer field twist is the genuine field graph power. -/
def fieldGraphPowerIso (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) (n : ℤ) :
    (Scheme.Modules.pullback (pullback.fst (totalProjection z x p hz) a)).obj
      (totalGraphPower z x p hz N0 (targetOriginalLine K qX) n) ≅
    PolarizedCoverGraphDegree.graphPower
      (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
        (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a)
      (fieldSourceLine z x p hz N0 L a)
      ((Scheme.Modules.pullback (projectiveSpaceOverMap 1
        (a ≫ originalGroundMap z x p K sQ))).obj
          (ConstantProjectiveLinePolarization.groundLine K)) n := by
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (pullback.fst (totalProjection z x p hz) a)
    (totalGraphLine z x p hz N0 (targetOriginalLine K qX))
  exact originalPullbackPowerIso _ _ n ≪≫
    originalPowerCongr (fieldGraphLineIso z x p hz N0 K sQ qX htarget L a) n

/-- The first original twist is the actual field graph line. -/
def fieldGraphFirstTwistIso (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :
    (Scheme.Modules.pullback (pullback.fst (totalProjection z x p hz) a)).obj
      (totalGraphPower z x p hz N0 (targetOriginalLine K qX) 1) ≅
    PolarizedCoverGraphDegree.graphLine
      (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
        (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a)
      (fieldSourceLine z x p hz N0 L a)
      ((Scheme.Modules.pullback (projectiveSpaceOverMap 1
        (a ≫ originalGroundMap z x p K sQ))).obj
          (ConstantProjectiveLinePolarization.groundLine K)) :=
  (Scheme.Modules.pullback (pullback.fst (totalProjection z x p hz) a)).mapIso
    (Stacks.SheafOfModules.Invertible.tensorPowerOneIso _ _
      (totalGraphLine z x p hz N0 (targetOriginalLine K qX))) ≪≫
    fieldGraphLineIso z x p hz N0 K sQ qX htarget L a

end ConstantTarget


/-- The actual all-original-field geometry supplied by the polarized
source open. In particular the line is the literal pulled embedding
line, retaining its degree forty-eight. -/
def sourceGeometry : Prop :=
  ∀ (L : Type u) [Field L] (V : Scheme.{u})
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Q)
    (q : V ⟶ (BigFppfOver.toScheme B S hS).obj Z) (f : V ⟶ Spec (.of L))
    [IsProper f], IsPullback q f ((BigFppfOver.toScheme B S hS).map z) a →
      IsCurve L f ∧ IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ f.appTop) ∧ genus f = 9 ∧
        ∀ hdim : topologicalKrullDim V ≤ 1,
          invertibleCurveDegree L f hdim ((Scheme.Modules.pullback q).obj N0) = 48

section CoverDegree

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K : Type u) [Field K]
  (sQ : (BigFppfOver.toScheme B S hS).obj Q ⟶ Spec (.of K))
  (qX : (BigFppfOver.toScheme B S hS).obj X ⟶ Line K)
  (htarget : qX ≫ toBase K = (BigFppfOver.toScheme B S hS).map x ≫ sQ)

/-- The genuine original field fibre of the universal source is a
field fibre of the SAME polarized original source family. -/
theorem fieldSourceSquare (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :
    IsPullback
      (pullback.fst (totalProjection z x p hz) a ≫
        (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.toOriginal z x p hz))
      (pullback.snd (totalProjection z x p hz) a)
      ((BigFppfOver.toScheme B S hS).map z)
      (a ≫ (BigFppfOver.toScheme B S hS).map (RelativeCoverSchemeEvaluation.base z x p)) :=
  (IsPullback.of_hasPullback (totalProjection z x p hz) a).paste_horiz
    (RelativeCoverSchemeEvaluation.originalSourceSquare z x p hz)

/-- The true first-twist converse turns native graph HP into a genuine
nonconstant field cover of exactly the specified native degree. -/
theorem fieldCover_of_graphHP (hsource : sourceGeometry z N0) (d : ℕ) (hd : 0 < d)
    (hP : graphHP z x p N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial d))
    (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) :
    ∃ hc : IsCurve L (pullback.snd (totalProjection z x p hz) a),
      letI := hc
      ∃ hnc : ¬ ∃ y : Line L, ∀ c : (pullback (totalProjection z x p hz) a : Scheme.{u}),
        (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
          (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a).base c = y,
        genus (pullback.snd (totalProjection z x p hz) a) = 9 ∧
          ConstantP1CoverDegreeBaseChange.fieldDegree K L (totalProjection z x p hz)
            (originalGroundMap z x p K sQ) (originalLineMap z x p hz K qX)
            (originalLineMap_over z x p hz K sQ qX htarget) a hnc = d := by
  have hgeom := hsource L _ _ _ _ (fieldSourceSquare z x p hz L a)
  refine ⟨hgeom.1, ?_⟩
  letI := hgeom.1
  letI := hgeom.2.1
  letI := totalProjectionSmooth z x p hz
  let f := pullback.snd (totalProjection z x p hz) a
  let g := fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
    (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a
  let M := (Scheme.Modules.pullback
    (projectiveSpaceOverMap 1 (a ≫ originalGroundMap z x p K sQ))).obj
      (ConstantProjectiveLinePolarization.groundLine K)
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (projectiveSpaceOverMap 1 (a ≫ originalGroundMap z x p K sQ))
    (ConstantProjectiveLinePolarization.groundLine K)
  have hdim : topologicalKrullDim (pullback (totalProjection z x p hz) a : Scheme.{u}) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hN : invertibleCurveDegree L f hdim (fieldSourceLine z x p hz N0 L a) = 48 :=
    hgeom.2.2.2 hdim
  have hM : invertibleCurveDegree L (toBase L) (lineDimension L) M = 1 :=
    ConstantProjectiveLinePolarization.groundLinePullback_degree K L
      (a ≫ originalGroundMap z x p K sQ)
  have hχ := fieldEuler_of_graphHP z x p hz N0 (targetOriginalLine K qX)
    hsep hxfp hfp hflat hproper (BoundedPencilGraphPolynomial.graphPolynomial d) hP
    (IsPullback.of_hasPullback (totalProjection z x p hz) a) 1
  have hχ' : ProperFlatFibreEulerCharacteristic.eulerSum L f
      (PolarizedCoverGraphDegree.graphLine g (fieldSourceLine z x p hz N0 L a) M) =
      BoundedPencilGraphPolynomial.graphPolynomial d 1 :=
    (ProperFlatFibreEulerCharacteristic.eulerSum_congr L f
      (fieldGraphFirstTwistIso z x p hz N0 K sQ qX htarget L a)).symm.trans hχ
  obtain ⟨hnc, hdeg⟩ := PolarizedCoverGraphDegree.exists_nativeDegree_eq_of_graphEuler f g
    (fieldMap_over K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
      (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a)
    (fieldSourceLine z x p hz N0 L a) M hdim hgeom.2.2.1 hN hM d hd hχ'
  exact ⟨hnc, hgeom.2.2.1, hdeg⟩

/-- The exact bounded-field cover condition needed by component
avoidance, obtained from the actual native HP condition. -/
theorem hcover_of_graphHP (hsource : sourceGeometry z N0) (d : ℕ)
    (hd : 0 < d) (hfive : d ≤ 5)
    (hP : graphHP z x p N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial d)) :
    ∀ (L : Type u) [Field L] (_ : B.Contains (Spec (.of L)))
      (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y),
      ∃ hc : IsCurve L (pullback.snd (totalProjection z x p hz) a),
        letI := hc
        ∃ hnc : ¬ ∃ y : Line L, ∀ c : (pullback (totalProjection z x p hz) a : Scheme.{u}),
          (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
            (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a).base c = y,
          genus (pullback.snd (totalProjection z x p hz) a) = 9 ∧
            ConstantP1CoverDegreeBaseChange.fieldDegree K L (totalProjection z x p hz)
              (originalGroundMap z x p K sQ) (originalLineMap z x p hz K qX)
              (originalLineMap_over z x p hz K sQ qX htarget) a hnc ≤ 5 := by
  intro L _ _ a
  obtain ⟨hc, hnc, hg, hdeg⟩ := fieldCover_of_graphHP z x p hz N0 hsep hxfp hfp hflat hproper
    K sQ qX htarget hsource d hd hP L a
  refine ⟨hc, hnc, hg, ?_⟩
  exact hdeg.le.trans hfive

/-- Forward native HP membership is derived from the actual native
degree of the original nonconstant field cover, using every-integer
Riemann--Roch and the actual field-square comparison. -/
theorem graphHP_of_nonconstant_fieldCover (hsource : sourceGeometry z N0)
    (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) [IsIso a]
    (hc : IsCurve L (pullback.snd (totalProjection z x p hz) a))
    (hnc : ¬ ∃ y : Line L, ∀ c : (pullback (totalProjection z x p hz) a : Scheme.{u}),
      (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
        (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a).base c = y) :
    letI := hc
    graphHP z x p N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial
        (ConstantP1CoverDegreeBaseChange.fieldDegree K L (totalProjection z x p hz)
          (originalGroundMap z x p K sQ) (originalLineMap z x p hz K qX)
          (originalLineMap_over z x p hz K sQ qX htarget) a hnc)) := by
  letI := hc
  have hgeom := hsource L _ _ _ _ (fieldSourceSquare z x p hz L a)
  letI := hgeom.2.1
  letI := totalProjectionSmooth z x p hz
  let f := pullback.snd (totalProjection z x p hz) a
  let g := fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
    (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a
  let M := (Scheme.Modules.pullback
    (projectiveSpaceOverMap 1 (a ≫ originalGroundMap z x p K sQ))).obj
      (ConstantProjectiveLinePolarization.groundLine K)
  letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (projectiveSpaceOverMap 1 (a ≫ originalGroundMap z x p K sQ))
    (ConstantProjectiveLinePolarization.groundLine K)
  have hdim : topologicalKrullDim (pullback (totalProjection z x p hz) a : Scheme.{u}) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hN : invertibleCurveDegree L f hdim (fieldSourceLine z x p hz N0 L a) = 48 :=
    hgeom.2.2.2 hdim
  have hM : invertibleCurveDegree L (toBase L) (lineDimension L) M = 1 :=
    ConstantProjectiveLinePolarization.groundLinePullback_degree K L
      (a ≫ originalGroundMap z x p K sQ)
  apply (graphHP_iff_familyEuler z x p hz N0 (targetOriginalLine K qX)
    hsep hxfp hfp hflat hproper _).mpr
  intro t n
  obtain ⟨w, rfl⟩ := (asIso a).hom.homeomorph.surjective t
  have hw : w = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  rw [hw]
  have hχ := PolarizedCoverGraphDegree.graphPower_euler f g
    (fieldMap_over K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
      (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a)
    (fieldSourceLine z x p hz N0 L a) M hdim hgeom.2.2.1 hN hM hnc n
  have hbc := PolarizedCurveDegreeOpen.fieldEuler_eq (totalProjection z x p hz)
    (totalGraphPower z x p hz N0 (targetOriginalLine K qX) n)
    (IsPullback.of_hasPullback (totalProjection z x p hz) a)
  exact hχ.symm.trans ((ProperFlatFibreEulerCharacteristic.eulerSum_congr L f
    (fieldGraphPowerIso z x p hz N0 K sQ qX htarget L a n)).symm.trans hbc.symm)

end CoverDegree

section UniversalCover

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K : Type u) [Field K]
  (sQ : (BigFppfOver.toScheme B S hS).obj Q ⟶ Spec (.of K))
  (qX : (BigFppfOver.toScheme B S hS).obj X ⟶ Line K)
  (htarget : qX ≫ toBase K = (BigFppfOver.toScheme B S hS).map x ≫ sQ)

/-- Every original bounded-field point of the actual native cover locus
is a genuine genus-nine nonconstant cover of degree at most five. Its
native HP is proved from the actual map to that locus inside the proof. -/
theorem universal_hcover (hsource : sourceGeometry z N0) (d : ℕ)
    (hd : 0 < d) (hfive : d ≤ 5)
    (A : yoneda.obj Y ⟶
      (canonicalGraphLocus z x N0 (targetOriginalLine K qX)
        hsep hxfp hfp hflat hproper (BoundedPencilGraphPolynomial.graphPolynomial d)).toFunctor) :
    let p := familyOfMapToLocus z x N0 (targetOriginalLine K qX)
      hsep hxfp hfp hflat hproper (BoundedPencilGraphPolynomial.graphPolynomial d) A
    ∀ (L : Type u) [Field L] (_ : B.Contains (Spec (.of L)))
      (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y),
      ∃ hc : IsCurve L (pullback.snd (totalProjection z x p hz) a),
        letI := hc
        ∃ hnc : ¬ ∃ y : Line L, ∀ c : (pullback (totalProjection z x p hz) a : Scheme.{u}),
          (fieldMap K (totalProjection z x p hz) (originalGroundMap z x p K sQ)
            (originalLineMap z x p hz K qX) (originalLineMap_over z x p hz K sQ qX htarget) L a).base c = y,
          genus (pullback.snd (totalProjection z x p hz) a) = 9 ∧
            ConstantP1CoverDegreeBaseChange.fieldDegree K L (totalProjection z x p hz)
              (originalGroundMap z x p K sQ) (originalLineMap z x p hz K qX)
              (originalLineMap_over z x p hz K sQ qX htarget) a hnc ≤ 5 := by
  let p := familyOfMapToLocus z x N0 (targetOriginalLine K qX)
    hsep hxfp hfp hflat hproper (BoundedPencilGraphPolynomial.graphPolynomial d) A
  have hP : graphHP z x p N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial d) :=
    graphHP_of_mapToLocus z x N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial d) A
  exact hcover_of_graphHP z x p hz N0 hsep hxfp hfp hflat hproper K sQ qX htarget
    hsource d hd hfive hP

end UniversalCover


/-- The actual native relative morphism of a native relative-Hom section. -/
abbrev familyOfSection
    (s : (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2
      (schemeSpace Q).2).obj (op Y)) :=
  relativeHomSections B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
    (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2 (schemeSpace Q).2 Y s

section FieldSectionMembership

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K : Type u) [Field K]
  (sQ : (BigFppfOver.toScheme B S hS).obj Q ⟶ Spec (.of K))
  (qX : (BigFppfOver.toScheme B S hS).obj X ⟶ Line K)
  (htarget : qX ≫ toBase K = (BigFppfOver.toScheme B S hS).map x ≫ sQ)

/-- Genuine nonconstant original field covers lie in the actual native
Hilbert-polynomial subfunctor for their genuine native degree. -/
theorem section_mem_of_nonconstant_fieldCover (hsource : sourceGeometry z N0)
    (s : (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (schemeSpace Z).2 (schemeSpace X).2
      (schemeSpace Q).2).obj (op Y))
    (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj Y) [IsIso a]
    (hc : IsCurve L (pullback.snd (totalProjection z x (familyOfSection z x s) hz) a))
    (hnc : ¬ ∃ y : Line L, ∀ c : (pullback (totalProjection z x (familyOfSection z x s) hz) a : Scheme.{u}),
      (fieldMap K (totalProjection z x (familyOfSection z x s) hz)
        (originalGroundMap z x (familyOfSection z x s) K sQ)
        (originalLineMap z x (familyOfSection z x s) hz K qX)
        (originalLineMap_over z x (familyOfSection z x s) hz K sQ qX htarget) L a).base c = y) :
    let p := familyOfSection z x s
    letI := hc
    s ∈ (canonicalGraphLocus z x N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper
      (BoundedPencilGraphPolynomial.graphPolynomial
        (ConstantP1CoverDegreeBaseChange.fieldDegree K L (totalProjection z x p hz)
          (originalGroundMap z x p K sQ) (originalLineMap z x p hz K qX)
          (originalLineMap_over z x p hz K sQ qX htarget) a hnc))).obj (op Y) := by
  letI := hc
  exact section_mem_of_graphHP z x N0 (targetOriginalLine K qX) hsep hxfp hfp hflat hproper _ s
    (graphHP_of_nonconstant_fieldCover z x (familyOfSection z x s) hz N0
      hsep hxfp hfp hflat hproper K sQ qX htarget hsource L a hc hnc)

end FieldSectionMembership

end M9Native.FixedDegreeCoverCurveGraphAdapter
