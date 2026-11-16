module

public import M9StacksIntegration.MukaiBundleUniqueness
public import M9StacksIntegration.HomDualBundleTensor
public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.MukaiHomExact
public import M9StacksIntegration.MukaiDualSpanSections
public import M9StacksIntegration.InvertibleHomCancellation
public import M9StacksIntegration.MukaiCanonicalExteriorDegree
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant

/-!
# The actual numerical Hom bound in Mukai Lemma 5.5

All Hom spaces carry `modulesLinearOverField k f`, and all cohomology uses
the original structure map `f`. The dual span is the native dual of the
kernel of the actual generating net evaluation. Tensoring that sequence
with the actual finite locally free bundle supplies the section inequality;
the remaining numerical computation uses genuine RR and Serre duality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiRecognitionHomBound

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Actual morphisms out of the dual are the actual tensor's global
sections, with the original coefficient-field scalar action. -/
def homDualTensorH0Equiv (Q F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q r] :
    letI := modulesLinearOverField k f
    (dualSheaf Q ⟶ F) ≃ₗ[k] cohomologyOverField k f (tensor Q F) 0 := by
  letI := modulesLinearOverField k f
  let e : tensor Q F ≅ (Stacks.Algebraization.sheafHomFunctor X (dualSheaf Q)).obj F :=
    HomDualBundleTensor.tensorIsoHomDualBundle Q F r ≪≫
      HomBundleComparison.homBundleIsoSheafHom (dualSheaf Q) F
  exact (MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f (dualSheaf Q) F).trans
    (cohomologyOverFieldIso k f e.symm 0).toLinearEquiv

section Proper

variable [IsProper f]

theorem finite_tensor_H0 (Q F : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F s] :
    Module.Finite k (cohomologyOverField k f (tensor Q F) 0) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor Q F) (r * s) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X Q F r s
  letI : (tensor Q F).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
    k f (tensor Q F) (r * s)
  exact finiteDimensional_cohomologyOverField_of_isProper k f (tensor Q F) 0

theorem finite_bundle_H0 (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] :
    Module.Finite k (cohomologyOverField k f E 0) := by
  letI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E r
  exact finiteDimensional_cohomologyOverField_of_isProper k f E 0

/-- The actual evaluation sequence, tensored with `E`, proves the first
inequality of Mukai Lemma 1.1. No surjectivity of the final H0 map is used. -/
theorem evaluation_tensor_H0_bound (E β : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s)) :
    letI := modulesLinearOverField k f
    3 * Module.finrank k (cohomologyOverField k f E 0) ≤
      Module.finrank k (dualSpan β s ⟶ E) +
        Module.finrank k (cohomologyOverField k f (tensor β E) 0) := by
  letI := modulesLinearOverField k f
  letI := netFree_rank X
  letI := evaluationKernel_rank β s hs
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI := finite_bundle_H0 k f E r
  letI := finite_tensor_H0 k f (evaluationKernel β s) E 2 r
  letI := finite_tensor_H0 k f (netFree X) E 3 r
  letI := finite_tensor_H0 k f β E 1 r
  letI := MukaiCupAlternating.tensorRight_additive E
  letI : PreservesFiniteLimits (MukaiCupAlternating.tensorRight E) :=
    (MukaiCupAlternating.tensorRight_exact E
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r)).1
  letI : PreservesFiniteColimits (MukaiCupAlternating.tensorRight E) :=
    (MukaiCupAlternating.tensorRight_exact E
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r)).2
  have hS := (evaluationSequence_shortExact β s hs).map_of_exact
    (MukaiCupAlternating.tensorRight E)
  letI : Module.Finite k (cohomologyOverField k f
      ((evaluationSequence β s).map (MukaiCupAlternating.tensorRight E)).X₁ 0) :=
    finite_tensor_H0 k f (evaluationKernel β s) E 2 r
  letI : Module.Finite k (cohomologyOverField k f
      ((evaluationSequence β s).map (MukaiCupAlternating.tensorRight E)).X₂ 0) :=
    finite_tensor_H0 k f (netFree X) E 3 r
  letI : Module.Finite k (cohomologyOverField k f
      ((evaluationSequence β s).map (MukaiCupAlternating.tensorRight E)).X₃ 0) :=
    finite_tensor_H0 k f β E 1 r
  have hb := MukaiBundleUniqueness.finrank_H0_le_add k f hS
  change Module.finrank k (cohomologyOverField k f (tensor (netFree X) E) 0) ≤
    Module.finrank k (cohomologyOverField k f (tensor (evaluationKernel β s) E) 0) +
      Module.finrank k (cohomologyOverField k f (tensor β E) 0) at hb
  have hker : Module.finrank k (dualSpan β s ⟶ E) =
      Module.finrank k (cohomologyOverField k f (tensor (evaluationKernel β s) E) 0) :=
    (homDualTensorH0Equiv k f (evaluationKernel β s) E 2).finrank_eq
  let e : (dualSheaf (netFree X) ⟶ E) ≃ₗ[k]
      (ULift.{u} (Fin 3) → cohomologyOverField k f E 0) :=
    (Linear.homCongr k (dualNetFreeIso X) (Iso.refl E)).trans
      ((MukaiBundleUniqueness.netFreeHomEquiv k f E).trans
        (LinearEquiv.piCongrRight fun _ => unitHomLinearEquivCohomologyZero k f E))
  have hfree : Module.finrank k (cohomologyOverField k f (tensor (netFree X) E) 0) =
      3 * Module.finrank k (cohomologyOverField k f E 0) := by
    rw [← (homDualTensorH0Equiv k f (netFree X) E 3).finrank_eq, e.finrank_eq,
      Module.finrank_pi_fintype]
    simp
  rw [hfree, ← hker] at hb
  exact hb

/-- The actual residual line relation cancels the invertible β in Hom.
The result is linear for exactly `modulesLinearOverField k f`. -/
def residualHomLinearEquiv (E α β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    (E ⟶ α) ≃ₗ[k] (tensor β E ⟶ Stacks.Duality.dualizingSheafOverField f) := by
  letI := modulesLinearOverField k f
  let c : tensor β E ≅ tensor E β :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.property β E
  exact (M9StacksIntegration.InvertibleHomCancellation.tensorRightHomLinearEquiv f β E α).trans
    (Linear.homCongr k c.symm hres)

/-- Genuine Serre duality turns the residual Hom term into H1 of the
original tensor bundle. No numerical Serre-duality premise is supplied. -/
theorem finrank_residual_hom (hdim : topologicalKrullDim X ≤ 1)
    (E α β : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    Module.finrank k (E ⟶ α) =
      Module.finrank k (cohomologyOverField k f (tensor β E) 1) := by
  letI := modulesLinearOverField k f
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor β E) (1 * r) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X β E 1 r
  letI : (tensor β E).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
    k f (tensor β E) (1 * r)
  letI := isQuasicoherent_of_isCoherent (tensor β E)
  letI := finiteDimensional_cohomologyOverField_of_isProper k f (tensor β E) 1
  rw [(residualHomLinearEquiv k f E α β hres).finrank_eq,
    (Stacks.Duality.homDualizingSheafLinearEquiv f hdim (tensor β E)
      (isQuasicoherent_of_isCoherent _)).finrank_eq, Subspace.dual_finrank_eq]

section Curve

variable [IsCurve k f]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- The actual tensor-degree formula and RR compute the Euler
characteristic of the original rank-three tensor bundle as 16. -/
theorem tensor_euler_sixteen_of_degree (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) (E β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hE : curveDegree k f hdim E 3 = 16)
    (hβ : invertibleCurveDegree k f hdim β = 8) :
    (Module.finrank k (cohomologyOverField k f (tensor β E) 0) : ℤ) -
      Module.finrank k (cohomologyOverField k f (tensor β E) 1) = 16 := by
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor β E) 3 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X β E 1 3
  letI : (tensor β E).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      k f (tensor β E) 3
  have hβ' : curveDegree k f hdim β 1 = 8 :=
    (invertibleCurveDegree_eq_curveDegree k f hdim β).symm.trans hβ
  have hd := curveDegree_tensorSheaf_eq_add k f hdim β E 1 3
  change curveDegree k f hdim (tensor β E) 3 =
    (3 : ℤ) * curveDegree k f hdim β 1 + (1 : ℤ) * curveDegree k f hdim E 3 at hd
  rw [hβ', hE] at hd
  norm_num at hd
  have hd40 : curveDegree k f hdim (tensor β E) 3 = 40 := hd
  have hRR := eulerCharacteristic_eq_curveDegree_add_genus k f hdim (tensor β E) 3
  rw [hd40, hg] at hRR
  norm_num at hRR
  exact (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f (tensor β E)
    (isZero_cohomologyOverField_two_le k f hdim (tensor β E))).symm.trans hRR

/-- The numerical core, before deriving `deg(E)=16` from the actual
canonical determinant isomorphism. The degree here is actual native degree,
not a Hom-dimension hypothesis. -/
theorem hom_bound_of_curveDegree (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hE : curveDegree k f hdim E 3 = 16)
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    letI := modulesLinearOverField k f
    2 ≤ Module.finrank k (dualSpan β s ⟶ E) + Module.finrank k (E ⟶ α) := by
  letI := modulesLinearOverField k f
  have heval := evaluation_tensor_H0_bound k f E β 3 s hs
  have hSerre := finrank_residual_hom k f hdim E α β 3 hres
  have hEuler := tensor_euler_sixteen_of_degree k f hdim hg E β hE hβ
  rw [← hSerre] at hEuler
  omega

/-- The numerical inequality produces a genuinely nonzero actual
morphism in one of the two Hom spaces. -/
theorem nonzero_hom_alternative_of_curveDegree (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hE : curveDegree k f hdim E 3 = 16)
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    (∃ φ : dualSpan β s ⟶ E, φ ≠ 0) ∨ (∃ ψ : E ⟶ α, ψ ≠ 0) := by
  letI := modulesLinearOverField k f
  have hb := hom_bound_of_curveDegree k f hdim hg E α β s hs hres hE hβ h6
  by_contra h
  have hQ : ∀ φ : dualSpan β s ⟶ E, φ = 0 := by
    intro φ
    by_contra hφ
    exact h (Or.inl ⟨φ, hφ⟩)
  have hα : ∀ ψ : E ⟶ α, ψ = 0 := by
    intro ψ
    by_contra hψ
    exact h (Or.inr ⟨ψ, hψ⟩)
  letI : Subsingleton (dualSpan β s ⟶ E) := ⟨fun a b => (hQ a).trans (hQ b).symm⟩
  letI : Subsingleton (E ⟶ α) := ⟨fun a b => (hα a).trans (hα b).symm⟩
  have hzQ : Module.finrank k (dualSpan β s ⟶ E) = 0 := Module.finrank_zero_of_subsingleton
  have hzα : Module.finrank k (E ⟶ α) = 0 := Module.finrank_zero_of_subsingleton
  omega

omit [IsCurve k f] in
/-- The degree of the actual rank-three bundle follows from its genuine
top-exterior/determinant isomorphism and the checked canonical degree
calculation by native Serre duality and line Riemann--Roch. -/
theorem curveDegree_of_canonicalDeterminant (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hdet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f) :
    curveDegree k f hdim E 3 = 2 * (genus f : ℤ) - 2 :=
  MukaiCanonicalExteriorCohomology.canonical_curveDegree k f hdim E
    (Scheme.Modules.exteriorPowerIsoDeterminant E 3 ≪≫ hdet)

/-- Mukai Lemma 5.5's actual numerical bound. The canonical determinant,
the generating net, and the residual relation are actual sheaf maps; no
degree for E, Hom bound, or numerical Serre-duality premise is assumed. -/
theorem hom_bound (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    letI := modulesLinearOverField k f
    2 ≤ Module.finrank k (dualSpan β s ⟶ E) + Module.finrank k (E ⟶ α) := by
  let hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  have hE : curveDegree k f hdim E 3 = 16 := by
    rw [curveDegree_of_canonicalDeterminant k f hdim E hdet, hg]
    norm_num
  exact hom_bound_of_curveDegree k f hdim hg E α β s hs hres hE hβ h6

/-- The same bound for the literal complete free net: the three
sections come from a basis of actual native H0. -/
theorem hom_bound_complete_net (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hs : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β b)))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    letI := modulesLinearOverField k f
    2 ≤ Module.finrank k
      (dualSpan β (MukaiDualSpanSections.completeNetSections f β b) ⟶ E) +
      Module.finrank k (E ⟶ α) :=
  hom_bound k f hg E α β (MukaiDualSpanSections.completeNetSections f β b)
    hs hres hdet hβ h6

/-- The paper states the canonical determinant as `⋀³ E ≅ ω`;
the genuine determinant/top-exterior isomorphism supplies that interface. -/
theorem hom_bound_topExterior (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    letI := modulesLinearOverField k f
    2 ≤ Module.finrank k (dualSpan β s ⟶ E) + Module.finrank k (E ⟶ α) :=
  hom_bound k f hg E α β s hs hres
    ((Scheme.Modules.exteriorPowerIsoDeterminant E 3).symm ≪≫ hdet) hβ h6

/-- A genuinely nonzero actual morphism follows from the proved
canonical-determinant bound. This is the first reduction of Lemma 5.5. -/
theorem nonzero_hom_alternative (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    (∃ φ : dualSpan β s ⟶ E, φ ≠ 0) ∨ (∃ ψ : E ⟶ α, ψ ≠ 0) := by
  let hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  have hE : curveDegree k f hdim E 3 = 16 := by
    rw [curveDegree_of_canonicalDeterminant k f hdim E hdet, hg]
    norm_num
  exact nonzero_hom_alternative_of_curveDegree k f hdim hg E α β s hs hres hE hβ h6

/-- The nonzero alternative for the actual dual span of a complete
free net, with no separately supplied section-count or Hom bound. -/
theorem nonzero_hom_alternative_complete_net (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hs : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β b)))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    (∃ φ : dualSpan β (MukaiDualSpanSections.completeNetSections f β b) ⟶ E, φ ≠ 0) ∨
      (∃ ψ : E ⟶ α, ψ ≠ 0) :=
  nonzero_hom_alternative k f hg E α β (MukaiDualSpanSections.completeNetSections f β b)
    hs hres hdet hβ h6

/-- The nonzero alternative with the paper's literal top-exterior
canonical-determinant hypothesis. -/
theorem nonzero_hom_alternative_topExterior (hg : genus f = 9) (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hs : Epi (netEvaluation β s))
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdet : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hβ : invertibleCurveDegree k f
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) β = 8)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    (∃ φ : dualSpan β s ⟶ E, φ ≠ 0) ∨ (∃ ψ : E ⟶ α, ψ ≠ 0) :=
  nonzero_hom_alternative k f hg E α β s hs hres
    ((Scheme.Modules.exteriorPowerIsoDeterminant E 3).symm ≪≫ hdet) hβ h6

end Curve

end Proper

end M9Native.MukaiRecognitionHomBound
