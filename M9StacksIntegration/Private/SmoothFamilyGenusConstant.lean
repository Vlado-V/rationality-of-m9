module

public import M9StacksIntegration.SmoothConnectedCurve
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# Genus constancy of the original smooth geometric curve family

Selected proof from pinned Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
`Curves/GenusCurve/FamilyGenusConstant.lean`, isolated privately. The audit
preserves the original source hash. The actual derived-fibre Euler theorem
is used directly; actual proper smooth geometrically connected fibres
supply constants over arbitrary fields, replacing algebraic-closedness.

No genus, cohomology rank or native family-class premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.SmoothFamilyGenusConstant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- All original field fibres of a proper smooth geometric relative curve
over a preconnected base have the same native cohomological genus. The
fields need not be algebraically closed; both Cartesian presentations,
structural maps and scalar actions are the original ones. -/
theorem genus_eq_of_isPullback
    {S Y : Scheme.{u}} [PreconnectedSpace S] (p : Y ⟶ S) [IsProper p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    (x₁ : Spec (.of K₁) ⟶ S) (x₂ : Spec (.of K₂) ⟶ S)
    {Z₁ Z₂ : Scheme.{u}} (q₁ : Z₁ ⟶ Y) (g₁ : Z₁ ⟶ Spec (.of K₁))
    (sq₁ : IsPullback q₁ g₁ p x₁)
    (q₂ : Z₂ ⟶ Y) (g₂ : Z₂ ⟶ Spec (.of K₂))
    (sq₂ : IsPullback q₂ g₂ p x₂) : genus g₁ = genus g₂ := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : IsProper g₁ := MorphismProperty.of_isPullback (P := @IsProper) sq₁ inferInstance
  let : IsProper g₂ := MorphismProperty.of_isPullback (P := @IsProper) sq₂ inferInstance
  let : SmoothOfRelativeDimension 1 g₁ :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) sq₁ inferInstance
  let : SmoothOfRelativeDimension 1 g₂ :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) sq₂ inferInstance
  let : Smooth g₁ := SmoothOfRelativeDimension.smooth 1 g₁
  let : Smooth g₂ := SmoothOfRelativeDimension.smooth 1 g₂
  let : GeometricallyConnected g₁ :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq₁ inferInstance
  let : GeometricallyConnected g₂ :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq₂ inferInstance
  let : ConnectedSpace Z₁ := GeometricallyConnected.connectedSpace_of_subsingleton g₁
  let : ConnectedSpace Z₂ := GeometricallyConnected.connectedSpace_of_subsingleton g₂
  let : IsIntegral Z₁ := SmoothConnectedCurve.isIntegral_of_smooth_connected g₁
  let : IsIntegral Z₂ := SmoothConnectedCurve.isIntegral_of_smooth_connected g₂
  have hd₁ := topologicalKrullDim_eq_of_smoothOfRelativeDimension g₁ 1
  have hd₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension g₂ 1
  let : GeometricallyReduced g₁ := geometricallyReduced_of_smooth g₁
  let : GeometricallyReduced g₂ := geometricallyReduced_of_smooth g₂
  let : IsIso ((Scheme.ΓSpecIso (.of K₁)).inv ≫ g₁.appTop) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper K₁ g₁
  let : IsIso ((Scheme.ΓSpecIso (.of K₂)).inv ≫ g₂.appTop) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper K₂ g₂
  have hfp : FinitePresentation p := FinitePresentation.mk inferInstance inferInstance inferInstance
  let F := SheafOfModules.unit Y.ringCatSheaf
  have hF : F.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit Y
  have hflat : IsFlatOver p.toLRSHom.toShHom F := isFlatOver_unit_of_flat p
  have h₁ := chiDerivedFibre_eq_eulerSum p hfp F hF hflat K₁ x₁ q₁ g₁ sq₁
    (IsLocalRing.closedPoint K₁)
  have h₂ := chiDerivedFibre_eq_eulerSum p hfp F hF hflat K₂ x₂ q₂ g₂ sq₂
    (IsLocalRing.closedPoint K₂)
  have hc := DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward p hfp inferInstance F hF
      hflat)
  have heq : eulerSum K₁ g₁ ((Scheme.Modules.pullback q₁).obj F) =
      eulerSum K₂ g₂ ((Scheme.Modules.pullback q₂).obj F) := by
    rw [← h₁, ← h₂]
    exact hc.apply_eq_of_preconnectedSpace _ _
  have i₁ : (Scheme.Modules.pullback q₁).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z₁.ringCatSheaf :=
    Stacks.PullbackAlgebra.pullbackUnitIso q₁.toLRSHom.toShHom
  have i₂ : (Scheme.Modules.pullback q₂).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z₂.ringCatSheaf :=
    Stacks.PullbackAlgebra.pullbackUnitIso q₂.toLRSHom.toShHom
  rw [eulerSum_congr K₁ g₁ i₁, eulerSum_congr K₂ g₂ i₂] at heq
  have eu₁ : eulerSum K₁ g₁ (SheafOfModules.unit Z₁.ringCatSheaf) = 1 - (genus g₁ : ℤ) :=
    eulerCharacteristic_unit_eq_one_sub_genus K₁ g₁ hd₁.le
  have eu₂ : eulerSum K₂ g₂ (SheafOfModules.unit Z₂.ringCatSheaf) = 1 - (genus g₂ : ℤ) :=
    eulerCharacteristic_unit_eq_one_sub_genus K₂ g₂ hd₂.le
  rw [eu₁, eu₂] at heq
  have hg : (genus g₁ : ℤ) = genus g₂ := by omega
  exact_mod_cast hg

end M9Native.SmoothFamilyGenusConstant
