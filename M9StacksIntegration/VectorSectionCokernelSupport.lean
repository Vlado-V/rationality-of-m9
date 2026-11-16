module

public import M9StacksIntegration.SymplecticQuotientEvaluation
public import M9StacksIntegration.LineMapCokernelCohomology

/-!
# Full evaluation cokernels and their actual quotient cohomology

Perfect finite locally free duality detects a nonzero original section on
the entire scheme. On a proper integral curve its actual evaluation
cokernel has support of dimension zero. An actual epimorphic coherent
quotient consequently has no larger original-field H0.

The final proof is the short zero-support quotient argument from the
pinned native `Curves/VanishingResults/SubcurveGlobalGeneration.lean`,
`finrank_zero_le_of_epi_of_supp_le_zero`, using its already-green exactness,
coherence and support parents rather than that file's unrelated closure.
The native package sources remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.ModuleStalk

universe u

namespace M9Native.VectorSectionCokernelSupport

variable {X : Scheme.{u}}

/-- Native dual evaluation detects actual global sections, including nilpotents. -/
theorem section_eq_zero_of_dualEvalHom_eq_zero (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E,⊤))
    (hs : AlgebraicGeometry.dualEvalHom E s = 0) : s = 0 := by
  let : IsIso (toDoubleDual E) := isIso_toDoubleDual_of_isFiniteLocallyFree E
  apply Scheme.Modules.injective_app_of_mono (toDoubleDual E) ⊤
  have h : LagrangianIsotropicDual.topFunctional (dualSheaf E)
      ((toDoubleDual E).app ⊤ s) = 0 :=
    (SymplecticQuotientEvaluation.sectionPairing_eq_dualEvalHom E s).trans hs
  have hz : LagrangianIsotropicDual.topFunctional (dualSheaf E) 0 = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext t
    rfl
  have ht := (LagrangianFreeDualSections.topFunctionalEquiv (dualSheaf E)).injective
    (h.trans hz.symm)
  exact ht.trans (map_zero _).symm

theorem dualEvalHom_ne_zero (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E,⊤)) (hs : s ≠ 0) :
    AlgebraicGeometry.dualEvalHom E s ≠ 0 :=
  fun h => hs (section_eq_zero_of_dualEvalHom_eq_zero E s h)

variable (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f]

include f in
/-- The actual evaluation cokernel is coherent, without a support premise. -/
theorem evaluationCokernel_isCoherent (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E,⊤)) :
    (cokernel (AlgebraicGeometry.dualEvalHom E s)).IsCoherent := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := isFiniteLocallyFreeOfRank_dualSheaf E r inferInstance
  let : (dualSheaf E).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      K f (dualSheaf E) r
  let : (dualSheaf E).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  let : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  let : (cokernel (AlgebraicGeometry.dualEvalHom E s)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent
    (inferInstance : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent)
    (cokernel.π (AlgebraicGeometry.dualEvalHom E s))

include f in
/-- Nonzero sections give actual zero-dimensional evaluation cokernels. -/
theorem evaluationCokernel_support_le_zero [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (s : Γ(E,⊤)) (hs : s ≠ 0) :
    topologicalKrullDim (SheafOfModules.supp
      (cokernel (AlgebraicGeometry.dualEvalHom E s))) ≤ 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let := evaluationCokernel_isCoherent K f E r s
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  have hn : ∃ a, mapFun (AlgebraicGeometry.dualEvalHom E s ≫ 𝟙 _)
      (genericPoint X) a ≠ 0 := by
    by_contra hall
    push Not at hall
    exact dualEvalHom_ne_zero E s hs
      (eq_zero_of_mapFun_genericPoint_eq_zero _ fun a => by simpa using hall a)
  exact topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim _
    (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ ‹_›)
    (genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp
      (AlgebraicGeometry.dualEvalHom E s) (𝟙 _) hn)

/-- An actual coherent epimorphic quotient of a zero-support sheaf has bounded H0. -/
theorem quotient_H0_le {Q Q' : X.Modules} (hQc : Q.IsCoherent)
    (hQ'c : Q'.IsCoherent) (p : Q ⟶ Q') [Epi p]
    (hQ : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0) :
    Module.finrank K (cohomologyOverField K f Q' 0) ≤
      Module.finrank K (cohomologyOverField K f Q 0) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := hQc
  let := hQ'c
  let := finiteDimensional_cohomologyOverField_of_isProper K f Q 0
  have hS := ShortComplex.shortExact_mk_kernel_ι p
  let : Q.IsQuasicoherent := isQuasicoherent_of_isCoherent Q
  let : Q'.IsQuasicoherent := isQuasicoherent_of_isCoherent Q'
  let : (kernel p).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel p
  let : (kernel p).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent
      hQc (kernel.ι p)
  have hKd : topologicalKrullDim (SheafOfModules.supp (kernel p)) ≤ 0 :=
    ((Topology.IsEmbedding.inclusion (supp_subset_of_mono (kernel.ι p))).isInducing
      |>.topologicalKrullDim_le).trans hQ
  have h1 := isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero K f
    (kernel p) hKd 1 Nat.one_pos
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence K f hS
  refine LinearMap.finrank_le_finrank_of_surjective
    (f := (cohomologyOverFieldMap K f p 0).hom) fun b => (hgd 0 b).mp ?_
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h1) _ _

end M9Native.VectorSectionCokernelSupport
