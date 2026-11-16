module

public import M9StacksIntegration.SectionConormalEvaluation
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import M9StacksIntegration.ConormalDifferentialSections

/-!
# The conormal map induced by a genuinely vanishing section

For a closed immersion `i : Y ⟶ X`, a finite locally free sheaf `E` on
`X`, and an actual section whose pullback vanishes, dual evaluation lands
in the actual defining ideal of `i`. Pulling back that factorization
gives the genuine map to the native conormal sheaf. No regularity or
generation of the entire defining ideal is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open RingedSpaceModuleAdjunction

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.VanishingSectionConormalMap

variable {X Y : Scheme.{u}} (i : Y ⟶ X) (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
  (s : Γ(E, ⊤))

omit hE in
/-- The canonical image of every restriction of the original section
vanishes in the actual pullback sheaf. -/
theorem unit_section_eq_zero (hs : pullbackGlobalSections i E s = 0) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app E).val.app (op U)
      (E.presheaf.map (homOfLE le_top).op s) = 0 := by
  have h := pullbackSection_eq_zero_of_pullbackGlobalSections_eq_zero i E s hs
    (hV := (le_rfl : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ U))
  change ((Scheme.Modules.pullback i).obj E).presheaf.map
    (homOfLE (le_rfl : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ U)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app E).val.app (op U)
        (E.presheaf.map (homOfLE le_top).op s)) = 0 at h
  simpa using h

/-- Actual evaluation at the original section is zero after restricting
its scalar value to the closed subscheme. -/
theorem evaluation_restrict_eq_zero (hs : pullbackGlobalSections i E s = 0)
    (U : X.Opens) (τ : Γ(dualSheaf E, U)) :
    i.app U (evalAt E τ (E.presheaf.map (homOfLE le_top).op s)) = 0 := by
  have h := Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply i E hE U τ
    (E.presheaf.map (homOfLE le_top).op s)
  rw [unit_section_eq_zero i E s hs U, map_zero] at h
  exact h.symm

/-- The original structure-sheaf restriction, with its actual kernel. -/
abbrev structureMap : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)

/-- The actual defining ideal, as the categorical kernel of structure
sheaf restriction. -/
abbrev idealModule : X.Modules := Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom

abbrev idealInclusion : idealModule i ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom

/-- Dual evaluation is annihilated by the original restriction map. -/
theorem evaluation_comp_structureMap (hs : pullbackGlobalSections i E s = 0) :
    dualEvalHom E s ≫ structureMap i = 0 := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun τ => ?_))
  exact evaluation_restrict_eq_zero i E s hs U.unop τ

/-- The genuine factor of dual evaluation through the entire native
defining ideal; generation of that ideal is not asserted. -/
def idealEvaluation (hs : pullbackGlobalSections i E s = 0) :
    dualSheaf E ⟶ idealModule i :=
  kernel.lift (structureMap i) (dualEvalHom E s)
    (evaluation_comp_structureMap i E s hs)

@[reassoc]
theorem idealEvaluation_comp_inclusion (hs : pullbackGlobalSections i E s = 0) :
    idealEvaluation i E s hs ≫ idealInclusion i = dualEvalHom E s :=
  kernel.lift_ι (structureMap i) (dualEvalHom E s)
    (evaluation_comp_structureMap i E s hs)

/-- The factorization preserves every actual local functional value. -/
theorem idealEvaluation_eval (hs : pullbackGlobalSections i E s = 0)
    (U : X.Opens) (τ : Γ(dualSheaf E, U)) :
    (idealInclusion i).val.app (op U) ((idealEvaluation i E s hs).val.app (op U) τ) =
      evalAt E τ (E.presheaf.map (homOfLE le_top).op s) :=
  congrArg (fun a : dualModule E ⟶ _ => a.val.app (op U) τ)
    (kernel.lift_ι (structureMap i) (dualEvalHom E s)
      (evaluation_comp_structureMap i E s hs))

section Conormal

variable [IsClosedImmersion i]

/-- The native conormal comparison is the original pullback of the
original kernel ideal, with the canonical immersion normalization. -/
def idealPullbackIso : (Scheme.Modules.pullback i).obj (idealModule i) ≅
    Stacks.Conormal.conormalSheaf i :=
  Stacks.Immersion.conormalSheafSelfIso i

/-- The actual section-induced conormal map. -/
def conormalMap (hs : pullbackGlobalSections i E s = 0) :
    (Scheme.Modules.pullback i).obj (dualSheaf E) ⟶
    Stacks.Conormal.conormalSheaf i :=
  (Scheme.Modules.pullback i).map (idealEvaluation i E s hs) ≫ (idealPullbackIso i).hom

/-- The adjoint of the actual conormal map is dual evaluation into the
defining ideal followed by its genuine native I/I² quotient. -/
@[reassoc]
theorem conormalMap_adjoint (hs : pullbackGlobalSections i E s = 0) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _)
      (conormalMap i E s hs) = idealEvaluation i E s hs ≫
        Stacks.Immersion.canonicalConormalQuotientMap i := by
  change (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
    (Scheme.Modules.pushforward i).map
      ((Scheme.Modules.pullback i).map (idealEvaluation i E s hs) ≫
        (idealPullbackIso i).hom) = _
  rw [Functor.map_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ (Scheme.Modules.pushforward i).map (idealPullbackIso i).hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality
      (idealEvaluation i E s hs)).symm).trans (Category.assoc _ _ _)

/-- On the canonical image of each local dual section, the original
conormal map is the class of its original evaluation. -/
theorem conormalMap_unit_apply (hs : pullbackGlobalSections i E s = 0)
    (U : X.Opens) (τ : Γ(dualSheaf E, U)) :
    (conormalMap i E s hs).app (i ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf E)).app U τ) =
      (Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op U)
        ((idealEvaluation i E s hs).app U τ) :=
  congrArg (fun a : dualSheaf E ⟶
    (Scheme.Modules.pushforward i).obj (Stacks.Conormal.conormalSheaf i) => a.app U τ)
      (conormalMap_adjoint i E s hs)

/-- The same original section-induced map, with target the literal
first object of the native conormal differential sequence. -/
def sequenceMap (hs : pullbackGlobalSections i E s = 0) {S : Scheme.{u}} (p : X ⟶ S) :
    (Scheme.Modules.pullback i).obj (dualSheaf E) ⟶
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁ :=
  conormalMap i E s hs ≫ (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv

/-- The actual first conormal arrow sends the original equation
functional to `1 ⊗ d(eval(τ,s))`, with its genuine native normalization. -/
theorem sequenceMap_firstArrow_unit_apply (hs : pullbackGlobalSections i E s = 0)
    {S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) (τ : Γ(dualSheaf E, U)) :
    (sequenceMap i E s hs p ≫
        (Stacks.ConormalSequenceRight.conormalShortComplex i p).f).app (i ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf E)).app U τ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Hom.relativeDifferentials p)).app U
        ((Scheme.Hom.universalRelativeDerivation p).d
          (evalAt E τ (E.presheaf.map (homOfLE le_top).op s))) := by
  change ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
      Stacks.ConormalSequenceRight.conormalDifferential i p).val.app (op (i ⁻¹ᵁ U))
    ((conormalMap i E s hs).app (i ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf E)).app U τ)) = _
  rw [conormalMap_unit_apply]
  refine (ConormalDifferentialSections.conormalDifferential_canonicalConormalQuotientMap
    i p U ((idealEvaluation i E s hs).app U τ)).trans ?_
  exact congrArg (fun a => ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (Scheme.Hom.relativeDifferentials p)).app U
      ((Scheme.Hom.universalRelativeDerivation p).d a))
    (idealEvaluation_eval i E s hs U τ)

end Conormal

end M9Native.VanishingSectionConormalMap
