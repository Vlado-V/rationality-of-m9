module

public import M9StacksIntegration.MukaiRecognitionHomBound

/-!
# The actual pentagonal Hom bound in Mukai (4.3)

The input is a genuine short exact sequence β∨ → O³ → F of actual
sheaves, an actual residual tensor isomorphism β⊗α ≅ ω, and the native
degree and section counts. Dualizing and tensoring this true sequence
gives the H0 inequality. Native line Riemann--Roch and actual Serre duality
then give Hom(F,ξ)+Hom(ξ,α) ≥ 1 over the original coefficient field.

The construction does not assume either Hom bound or the nonzero
alternative. Degree-eight geometry and the later geometric contradictions
remain separate producers. The algebraically closed field companion
derives the actual constant-function isomorphism internally.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u
namespace M9Native.MukaiPentagonalHomBound

variable {X : Scheme.{u}} (F β : X.Modules)
  [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
  (i : dualSheaf β ⟶ netFree X) (p : netFree X ⟶ F)
  (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)

include hS in
/-- The true original sequence is dualized using the actual finite
locally free sheaves. Neither exactness of its dual nor a dual-span
identification is a further input. -/
theorem dual_sequence_shortExact :
    ∃ z : dualMap p ≫ dualMap i = 0,
      (ShortComplex.mk (dualMap p) (dualMap i) z).ShortExact := by
  let hβ := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  let hβd := isFiniteLocallyFreeOfRank_dualSheaf β 1 hβ
  exact exists_dualSheaf_shortExact i p w hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      hβd.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      (netFree_rank X).isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hF.isFiniteLocallyFree)

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

include hS in
/-- Taking H0 of the actual dual sequence tensored by ξ gives the
paper's first inequality. The two end terms are identified by genuine
double-dual and tensor/Hom isomorphisms with the original k-scalars. -/
theorem tensor_H0_bound (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ] :
    let := modulesLinearOverField k f
    3 * Module.finrank k (cohomologyOverField k f ξ 0) ≤
      Module.finrank k (F ⟶ ξ) +
        Module.finrank k (cohomologyOverField k f (tensor β ξ) 0) := by
  let := modulesLinearOverField k f
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  let := netFree_rank X
  let := isFiniteLocallyFreeOfRank_dualSheaf F 2 hF
  let := isFiniteLocallyFreeOfRank_dualSheaf (netFree X) 3 (netFree_rank X)
  let := isFiniteLocallyFreeOfRank_dualSheaf β 1 inferInstance
  let := isFiniteLocallyFreeOfRank_dualSheaf (dualSheaf β) 1 inferInstance
  obtain ⟨z, hdual⟩ := dual_sequence_shortExact F β i p w hS
  let := MukaiCupAlternating.tensorRight_additive ξ
  let : PreservesFiniteLimits (MukaiCupAlternating.tensorRight ξ) :=
    (MukaiCupAlternating.tensorRight_exact ξ
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree ξ 1)).1
  let : PreservesFiniteColimits (MukaiCupAlternating.tensorRight ξ) :=
    (MukaiCupAlternating.tensorRight_exact ξ
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree ξ 1)).2
  let S := ShortComplex.mk (dualMap p) (dualMap i) z
  have ht := hdual.map_of_exact (MukaiCupAlternating.tensorRight ξ)
  let : Module.Finite k (cohomologyOverField k f
      (S.map (MukaiCupAlternating.tensorRight ξ)).X₁ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 k f (dualSheaf F) ξ 2 1
  let : Module.Finite k (cohomologyOverField k f
      (S.map (MukaiCupAlternating.tensorRight ξ)).X₂ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 k f (dualSheaf (netFree X)) ξ 3 1
  let : Module.Finite k (cohomologyOverField k f
      (S.map (MukaiCupAlternating.tensorRight ξ)).X₃ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 k f (dualSheaf (dualSheaf β)) ξ 1 1
  have hb := MukaiBundleUniqueness.finrank_H0_le_add k f ht
  change Module.finrank k (cohomologyOverField k f (tensor (dualSheaf (netFree X)) ξ) 0) ≤
    Module.finrank k (cohomologyOverField k f (tensor (dualSheaf F) ξ) 0) +
      Module.finrank k (cohomologyOverField k f (tensor (dualSheaf (dualSheaf β)) ξ) 0) at hb
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F := hF.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} β :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree β 1
  let : IsIso (toDoubleDual F) := isIso_toDoubleDual_of_isFiniteLocallyFree F
  let : IsIso (toDoubleDual β) := isIso_toDoubleDual_of_isFiniteLocallyFree β
  let eF : (F ⟶ ξ) ≃ₗ[k] cohomologyOverField k f (tensor (dualSheaf F) ξ) 0 :=
    (Linear.homCongr k (asIso (toDoubleDual F)) (Iso.refl ξ)).trans
      (MukaiRecognitionHomBound.homDualTensorH0Equiv k f (dualSheaf F) ξ 2)
  have hright : Module.finrank k
      (cohomologyOverField k f (tensor (dualSheaf (dualSheaf β)) ξ) 0) =
      Module.finrank k (cohomologyOverField k f (tensor β ξ) 0) :=
    (cohomologyOverFieldIso k f (tensorIso (asIso (toDoubleDual β)).symm (Iso.refl ξ)) 0).toLinearEquiv.finrank_eq
  have hmiddle : Module.finrank k
      (cohomologyOverField k f (tensor (dualSheaf (netFree X)) ξ) 0) =
      Module.finrank k (cohomologyOverField k f (tensor (netFree X) ξ) 0) :=
    (cohomologyOverFieldIso k f (tensorIso (dualNetFreeIso X) (Iso.refl ξ)) 0).toLinearEquiv.finrank_eq
  let eFree : (dualSheaf (netFree X) ⟶ ξ) ≃ₗ[k]
      (ULift.{u} (Fin 3) → cohomologyOverField k f ξ 0) :=
    (Linear.homCongr k (dualNetFreeIso X) (Iso.refl ξ)).trans
      ((MukaiBundleUniqueness.netFreeHomEquiv k f ξ).trans
        (LinearEquiv.piCongrRight fun _ => unitHomLinearEquivCohomologyZero k f ξ))
  let := MukaiRecognitionHomBound.finite_bundle_H0 k f ξ 1
  have hfree : Module.finrank k (cohomologyOverField k f (tensor (netFree X) ξ) 0) =
      3 * Module.finrank k (cohomologyOverField k f ξ 0) := by
    rw [← (MukaiRecognitionHomBound.homDualTensorH0Equiv k f (netFree X) ξ 3).finrank_eq,
      eFree.finrank_eq, Module.finrank_pi_fintype]
    simp
  rw [hmiddle, hfree, ← eF.finrank_eq, hright] at hb
  exact hb

section Curve
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- The original native line RR theorem computes χ(β⊗ξ)=5 from the
actual degrees eight and five on the actual genus-nine curve. -/
theorem tensor_euler_five (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (hξ : invertibleCurveDegree k f hdim ξ = 5) :
    (Module.finrank k (cohomologyOverField k f (tensor β ξ) 0) : ℤ) -
      Module.finrank k (cohomologyOverField k f (tensor β ξ) 1) = 5 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensor β ξ) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 β ξ
  have hd := invertibleCurveDegree_tensorSheaf_eq_add k f hdim β ξ
  change invertibleCurveDegree k f hdim (tensor β ξ) =
    invertibleCurveDegree k f hdim β + invertibleCurveDegree k f hdim ξ at hd
  have hr := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim (tensor β ξ)
  rw [hd, hβ, hξ, hg] at hr
  norm_num at hr
  exact hr

include hS in
/-- The genuine numerical inequality (4.3), with actual Hom scalars
from modulesLinearOverField k f. No Hom bound is an input. -/
theorem hom_bound (hdim : topologicalKrullDim X ≤ 1) (hg : genus f = 9)
    (α ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hres : tensor β α ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (hξ : invertibleCurveDegree k f hdim ξ = 5)
    (h2 : Module.finrank k (cohomologyOverField k f ξ 0) = 2) :
    let := modulesLinearOverField k f
    1 ≤ Module.finrank k (F ⟶ ξ) + Module.finrank k (ξ ⟶ α) := by
  let := modulesLinearOverField k f
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  have hb := tensor_H0_bound F β i p w hS k f ξ
  have hEuler := tensor_euler_five β k f hdim hg ξ hβ hξ
  let e : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2 α β ≪≫ hres
  have hSerre := MukaiRecognitionHomBound.finrank_residual_hom k f hdim ξ α β 1 e
  rw [h2] at hb
  rw [← hSerre] at hEuler
  omega

include hS in
/-- The bound produces an actual nonzero morphism in one of the two
original Hom spaces. No rank, epimorphism or image hypothesis is added. -/
theorem nonzero_hom_alternative (hdim : topologicalKrullDim X ≤ 1) (hg : genus f = 9)
    (α ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hres : tensor β α ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (hξ : invertibleCurveDegree k f hdim ξ = 5)
    (h2 : Module.finrank k (cohomologyOverField k f ξ 0) = 2) :
    (∃ φ : F ⟶ ξ, φ ≠ 0) ∨ (∃ ψ : ξ ⟶ α, ψ ≠ 0) := by
  let := modulesLinearOverField k f
  have hb := hom_bound F β i p w hS k f hdim hg α ξ hres hβ hξ h2
  by_contra h
  have hF0 : ∀ φ : F ⟶ ξ, φ = 0 := by
    intro φ
    by_contra hn
    exact h (Or.inl ⟨φ, hn⟩)
  have hα0 : ∀ ψ : ξ ⟶ α, ψ = 0 := by
    intro ψ
    by_contra hn
    exact h (Or.inr ⟨ψ, hn⟩)
  let : Subsingleton (F ⟶ ξ) := ⟨fun a b => (hF0 a).trans (hF0 b).symm⟩
  let : Subsingleton (ξ ⟶ α) := ⟨fun a b => (hα0 a).trans (hα0 b).symm⟩
  have hzF : Module.finrank k (F ⟶ ξ) = 0 := Module.finrank_zero_of_subsingleton
  have hzα : Module.finrank k (ξ ⟶ α) = 0 := Module.finrank_zero_of_subsingleton
  omega

end Curve

section AlgebraicallyClosed
variable [IsAlgClosed k] [IsCurve k f]

include hS in
/-- On the original proper integral curve over an algebraically closed
field, the native constants isomorphism and dimension bound are derived.
This is the actual-field version needed for the geometric contradiction. -/
theorem hom_bound_of_isAlgClosed (hg : genus f = 9) (α ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hres : tensor β α ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le β = 8)
    (hξ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le ξ = 5)
    (h2 : Module.finrank k (cohomologyOverField k f ξ 0) = 2) :
    let := modulesLinearOverField k f
    1 ≤ Module.finrank k (F ⟶ ξ) + Module.finrank k (ξ ⟶ α) := by
  let := isIso_globalSections_of_isAlgClosed k f
  exact hom_bound F β i p w hS k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    hg α ξ hres hβ hξ h2

include hS in
/-- The actual nonzero alternative over the original algebraically
closed field, without a separately assumed constants isomorphism. -/
theorem nonzero_hom_alternative_of_isAlgClosed (hg : genus f = 9) (α ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hres : tensor β α ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le β = 8)
    (hξ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le ξ = 5)
    (h2 : Module.finrank k (cohomologyOverField k f ξ 0) = 2) :
    (∃ φ : F ⟶ ξ, φ ≠ 0) ∨ (∃ ψ : ξ ⟶ α, ψ ≠ 0) := by
  let := isIso_globalSections_of_isAlgClosed k f
  exact nonzero_hom_alternative F β i p w hS k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    hg α ξ hres hβ hξ h2

end AlgebraicallyClosed
end M9Native.MukaiPentagonalHomBound
