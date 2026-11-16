module

public import M9StacksIntegration.DualExtNaturalityCore
public import M9StacksIntegration.CurveExtLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# Canonical dual-evaluation Ext cancellation on the actual scheme modules

The duality data are the native evaluation and coevaluation of the
actual internal Hom sheaf. The first-variable map is proved to be the
actual sheaf dual map, using its literal evaluation formula. No
naturality or Ext/cohomology comparison is assumed as an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DualExtNaturality

variable {X : Scheme.{u}}

local instance nativeMonoidal : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.Strict.monoidalCategory X.presheaf X.ringCatSheaf.property

local instance nativeMonoidalPreadditive : MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.sheaf

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

local instance nativeInvertible (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL

local instance nativeDualPair (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ExactPairing L (dualSheaf L) :=
  Stacks.SheafOfModules.exactPairingDualSheafOfIsInvertible X.presheaf X.ringCatSheaf.property L

@[instance_reducible] local instance nativeRightDual (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    HasRightDual L where
  rightDual := dualSheaf L
  exact := nativeDualPair L

/-- The native exact pairing evaluates by the literal actual sheaf evaluation. -/
theorem pairing_evaluation (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ε_ L (dualSheaf L) =
      Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property L := rfl

/-- Evaluation is natural for the original sheaf dual morphism. -/
theorem evaluation_dualMap {L M : X.Modules} (φ : L ⟶ M) :
    dualMap φ ▷ L ≫ Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property L =
      dualSheaf M ◁ φ ≫
        Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property M := by
  apply PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := X.sheaf) (F := dualSheaf M) (G := L)
    (Q := SheafOfModules.unit X.ringCatSheaf)
  intro U lam x
  change (Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property L).val.app U
      ((dualMap φ ▷ L).val.app U
        (Stacks.SheafOfModules.tensorPt X.presheaf X.ringCatSheaf.property
          (dualSheaf M) L U lam x)) =
    (Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property M).val.app U
      ((dualSheaf M ◁ φ).val.app U
        (Stacks.SheafOfModules.tensorPt X.presheaf X.ringCatSheaf.property
          (dualSheaf M) L U lam x))
  have hL := (congrArg
    ((Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property L).val.app U)
    (Stacks.SheafOfModules.tensorPt_whiskerRight X.presheaf X.ringCatSheaf.property
      (dualMap φ) U lam x)).trans
    (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
      L U ((dualMap φ).val.app U lam) x)
  have hM := (congrArg
    ((Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property M).val.app U)
    (Stacks.SheafOfModules.tensorPt_whiskerLeft X.presheaf X.ringCatSheaf.property
      φ U lam x)).trans
    (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
      M U lam (φ.val.app U x))
  exact hL.trans hM.symm

/-- The mate supplied by genuine tensor duality is the actual internal-Hom dual map. -/
theorem rightAdjointMate_eq_dualMap {L M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] (φ : L ⟶ M) :
    rightAdjointMate φ = dualMap φ := by
  have he : dualMap φ ▷ L ≫ ε_ L (dualSheaf L) =
      dualSheaf M ◁ φ ≫ ε_ M (dualSheaf M) := evaluation_dualMap φ
  have hh := congrArg (tensorRightHomEquiv (dualSheaf M) L (dualSheaf L)
    (𝟙_ X.Modules)) he
  have hL := tensorRightHomEquiv_whiskerRight_comp_evaluation (X := L) (Y := dualSheaf M) (dualMap φ)
  have hM := tensorRightHomEquiv_whiskerLeft_comp_evaluation φ
  exact (cancel_mono (λ_ (dualSheaf L)).inv).mp
    (hM.symm.trans (hh.symm.trans hL))


local instance dualInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (dualSheaf L) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf
      X.presheaf X.ringCatSheaf.property L)

local instance strictTensorRightEquivalence (W : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W] :
    (MonoidalCategory.tensorRight W).IsEquivalence := by
  let e : MonoidalCategory.tensorRight W ≅
      M9StacksIntegration.InvertibleHomCancellation.tensorRight W :=
    Stacks.SheafOfModules.Strict.tensorRightIsoSheafTensor X.sheaf W
  let : (M9StacksIntegration.InvertibleHomCancellation.tensorRight W).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  exact Functor.isEquivalence_of_iso e.symm

local instance strictRightDualTensorEquivalence (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (MonoidalCategory.tensorRight (Lᘁ)).IsEquivalence :=
  strictTensorRightEquivalence (dualSheaf L)

/-- Genuine tensor-dual adjunction on the actual native small Ext groups. -/
def dualExtAddEquiv (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    Ext.{u} L (InvertibleExtCancellation.unit X) n ≃+
      Ext.{u} (InvertibleExtCancellation.unit X) (dualSheaf L) n :=
  DualExtNaturalityCore.dualExtAddEquiv L n

/-- Every first-variable precomposition is the actual sheaf dual on
actual unit Ext, in every degree. -/
theorem dualExtAddEquiv_naturality {L M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (φ : L ⟶ M) (n : ℕ) (ξ : Ext.{u} M (InvertibleExtCancellation.unit X) n) :
    dualExtAddEquiv L n ((Ext.mk₀ φ).comp ξ (zero_add n)) =
      (dualExtAddEquiv M n ξ).comp (Ext.mk₀ (dualMap φ)) (add_zero n) := by
  have hh : dualExtAddEquiv L n ((Ext.mk₀ φ).comp ξ (zero_add n)) =
      (dualExtAddEquiv M n ξ).comp (Ext.mk₀ (rightAdjointMate φ)) (add_zero n) :=
    DualExtNaturalityCore.dualExtAddEquiv_naturality.{u+1,u,u}
      (C := X.Modules) M φ n ξ
  exact hh.trans (congrArg
    (fun a => (dualExtAddEquiv M n ξ).comp (Ext.mk₀ a) (add_zero n))
    (rightAdjointMate_eq_dualMap φ))

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- The canonical evaluation-based cancellation preserves the original
native base-field scalar action. -/
def dualExtLinearEquiv (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    letI := modulesLinearOverField k f
    Ext.{u} L (InvertibleExtCancellation.unit X) n ≃ₗ[k]
      Ext.{u} (InvertibleExtCancellation.unit X) (dualSheaf L) n := by
  let := modulesLinearOverField k f
  let e : MonoidalCategory.tensorRight (dualSheaf L) ≅
      M9StacksIntegration.InvertibleHomCancellation.tensorRight (dualSheaf L) :=
    Stacks.SheafOfModules.Strict.tensorRightIsoSheafTensor X.sheaf (dualSheaf L)
  let : (M9StacksIntegration.InvertibleHomCancellation.tensorRight (dualSheaf L)).Linear k :=
    M9StacksIntegration.InvertibleHomCancellation.tensorRight_linear f (dualSheaf L)
  let : (MonoidalCategory.tensorRight (dualSheaf L)).Linear k :=
    Functor.linear_of_iso k e.symm
  refine { __ := dualExtAddEquiv L n, map_smul' := ?_ }
  intro a ξ
  change DualExtNaturalityCore.dualExtAddEquiv L n (a • ξ) =
    a • DualExtNaturalityCore.dualExtAddEquiv L n ξ
  rw [DualExtNaturalityCore.dualExtAddEquiv_apply,
    DualExtNaturalityCore.dualExtAddEquiv_apply,
    Functor.mapExactFunctor_smul, Ext.comp_smul, Ext.smul_comp]

/-- Actual scalar-compatible Ext¹(L,O) is original H¹ of the actual dual
sheaf, using the native unit-Ext/cohomology comparison. -/
def dualExtOneCohomologyLinearEquiv (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    letI := modulesLinearOverField k f
    Ext.{u} L (InvertibleExtCancellation.unit X) 1 ≃ₗ[k]
      cohomologyOverField k f (dualSheaf L) 1 := by
  let := modulesLinearOverField k f
  exact (dualExtLinearEquiv f L 1).trans
    (UnitExtCohomologyNaturality.unitExtCohomologyLinearEquiv k f (dualSheaf L))

/-- Literal first-line naturality for the original native H¹ map. -/
theorem dualExtOneCohomologyLinearEquiv_naturality {L M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (φ : L ⟶ M) (ξ : Ext.{u} M (InvertibleExtCancellation.unit X) 1) :
    letI := modulesLinearOverField k f
    dualExtOneCohomologyLinearEquiv f L ((Ext.mk₀ φ).comp ξ (zero_add 1)) =
      cohomologyOverFieldMap k f (dualMap φ) 1
        (dualExtOneCohomologyLinearEquiv f M ξ) := by
  let := modulesLinearOverField k f
  change InvertibleExtCancellation.unitExtCohomologyAddEquiv k f (dualSheaf L) 1
    (dualExtAddEquiv L 1 ((Ext.mk₀ φ).comp ξ (zero_add 1))) = _
  rw [dualExtAddEquiv_naturality]
  exact UnitExtCohomologyNaturality.unitExtCohomologyAddEquiv_naturality_one
    k f (dualMap φ) (dualExtAddEquiv M 1 ξ)

/-- Surjectivity of the actual H¹ dual map implies surjectivity of the
original Yoneda precomposition map, with no replacement class group. -/
theorem ext_precomp_surjective_of_dual_h1_surjective {L M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (φ : L ⟶ M)
    (hφ : Function.Surjective (cohomologyOverFieldMap k f (dualMap φ) 1).hom) :
    Function.Surjective (fun ξ : Ext.{u} M (InvertibleExtCancellation.unit X) 1 =>
      (Ext.mk₀ φ).comp ξ (zero_add 1)) := by
  let := modulesLinearOverField k f
  intro ξ
  obtain ⟨η, hη⟩ := hφ (dualExtOneCohomologyLinearEquiv f L ξ)
  refine ⟨(dualExtOneCohomologyLinearEquiv f M).symm η, ?_⟩
  apply (dualExtOneCohomologyLinearEquiv f L).injective
  rw [dualExtOneCohomologyLinearEquiv_naturality, LinearEquiv.apply_symm_apply]
  exact hη

end M9Native.DualExtNaturality
