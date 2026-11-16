module

public import M9StacksIntegration.MukaiBundle
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction

/-!
# Sections of the actual dual-span construction

The complete-net kernel has no global sections: the evaluation map is
injective on global sections because its chosen three sections form the
original cohomology basis and the only global functions are constants.
All kernels, evaluation maps, and cohomology maps here are the actual
native ones from `MukaiBundle`.

This is an input to Mukai, *Curves and symmetric spaces, II*, Lemma 5.1.
The upper bound on the number of sections of the dual span still requires
constructing the length-two divisor in its plane-model argument; it is
not a premise of these lemmas.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiDualSpanSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open M9Native.MukaiBundle

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Sections of the actual line bundle determined by a complete basis of
its native zeroth cohomology. -/
def completeNetSections (f : X ⟶ Spec (.of k)) (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    ULift.{u} (Fin 3) → β.sections := fun i =>
  Stacks.PresheafOfModules.sectionOfTop β.val
    ((cohomologyOverFieldZeroLinearIso k f β).hom (b i))

@[simp]
theorem completeNetSections_eval_top (f : X ⟶ Spec (.of k)) (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (i : ULift.{u} (Fin 3)) :
    (completeNetSections f β b i).eval (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f β).hom (b i) :=
  Stacks.PresheafOfModules.sectionOfTop_val_top _ _

/-- Linear independence of the actual global sections makes evaluation
injective on global sections of the free source. -/
theorem netEvaluation_top_injective_of_linearIndependent (β : X.Modules)
    (s : ULift.{u} (Fin 3) → β.sections)
    (hs : LinearIndependent Γ(X, ⊤) (fun i => (s i).eval (op ⊤))) :
    Function.Injective ((netEvaluation β s).app ⊤) := by
  classical
  have hzero (z : (netFree X).val.obj (op ⊤))
      (hz : (netEvaluation β s).app ⊤ z = 0) : z = 0 := by
    have hsum : ∑ i, Stacks.SheafOfModules.freeCoord (S := X.ringCatSheaf)
        (op ⊤) z i • (s i).eval (op ⊤) = 0 := by
      simpa only [netEvaluation, Equiv.apply_symm_apply] using
        (Stacks.SheafOfModules.app_eq_sum_smul_freeCoord
          (netEvaluation β s) (op ⊤) z).symm.trans hz
    have hc := (Fintype.linearIndependent_iff.mp hs) _ hsum
    apply (Stacks.SheafOfModules.freeCoord_bijective
      (S := X.ringCatSheaf) (ι := ULift.{u} (Fin 3)) (op ⊤)).injective
    funext i
    simpa only [Stacks.SheafOfModules.freeCoord, map_zero] using hc i
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))

/-- Completeness and the actual constants isomorphism give independence
over the whole ring of global functions, rather than only over `k`. -/
theorem completeNetSections_linearIndependent (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    LinearIndependent Γ(X, ⊤)
      (fun i => (completeNetSections f β b i).eval (op ⊤)) := by
  classical
  let ρ : k →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop :=
    (Scheme.Hom.app_eq_appLE f).symm
  have hρ : Function.Surjective ρ := by
    simpa only [ρ, htop] using
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)).surjective
  let T := (restrictScalarsOverBase k f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj β)
  let e : cohomologyOverField k f β 0 ≃ₗ[k] T :=
    (cohomologyOverFieldZeroLinearIso k f β).toLinearEquiv
  have hlin : LinearIndependent k (fun i => e (b i)) := (b.map e).linearIndependent
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  choose a ha using fun i => hρ (c i)
  have hsum : ∑ i, a i • e (b i) = (0 : T) := by
    change ∑ i, ρ (a i) •
      (cohomologyOverFieldZeroLinearIso k f β).hom (b i) = 0
    simpa only [ha, completeNetSections_eval_top] using hc
  have hz := (Fintype.linearIndependent_iff.mp hlin) a hsum
  intro i
  rw [← ha i, hz i, map_zero]

/-- The evaluation attached to the original complete cohomology basis is
injective on actual top sections. -/
theorem completeNetEvaluation_top_injective (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Function.Injective ((netEvaluation β (completeNetSections f β b)).app ⊤) :=
  netEvaluation_top_injective_of_linearIndependent β _
    (completeNetSections_linearIndependent f β b)

/-- The same original evaluation is injective on native degree-zero
cohomology, using the proved natural comparison with top sections. -/
theorem completeNetEvaluation_cohomology_zero_injective (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Function.Injective
      (cohomologyOverFieldMap k f (netEvaluation β (completeNetSections f β b)) 0) := by
  intro a c hac
  apply (cohomologyOverFieldZeroLinearIso k f (netFree X)).toLinearEquiv.injective
  apply completeNetEvaluation_top_injective f β b
  change (netEvaluation β (completeNetSections f β b)).app ⊤
      ((cohomologyOverFieldZeroLinearIso k f (netFree X)).hom a) =
    (netEvaluation β (completeNetSections f β b)).app ⊤
      ((cohomologyOverFieldZeroLinearIso k f (netFree X)).hom c)
  rw [← cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap,
    ← cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap, hac]

/-- The original tautological free sections lift every member of the
complete basis through the original map on zeroth cohomology. -/
theorem completeNetEvaluation_cohomology_zero_surjective (f : X ⟶ Spec (.of k))
    (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Function.Surjective
      (cohomologyOverFieldMap k f (netEvaluation β (completeNetSections f β b)) 0) := by
  classical
  let e := (cohomologyOverFieldZeroLinearIso k f (netFree X)).toLinearEquiv
  let a : ULift.{u} (Fin 3) → cohomologyOverField k f (netFree X) 0 :=
    fun i => e.symm ((SheafOfModules.freeSection i).eval (op ⊤))
  let q := (cohomologyOverFieldMap k f
    (netEvaluation β (completeNetSections f β b)) 0).hom
  have hqa (i : ULift.{u} (Fin 3)) : q (a i) = b i := by
    apply (cohomologyOverFieldZeroLinearIso k f β).toLinearEquiv.injective
    change (cohomologyOverFieldZeroLinearIso k f β).hom
      ((cohomologyOverFieldMap k f
        (netEvaluation β (completeNetSections f β b)) 0).hom (a i)) =
      (cohomologyOverFieldZeroLinearIso k f β).hom (b i)
    rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
    change (netEvaluation β (completeNetSections f β b)).app ⊤
        (e (e.symm ((SheafOfModules.freeSection i).eval (op ⊤)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (fun z : β.sections => z.eval (op ⊤))
      (netEvaluation_freeSection β (completeNetSections f β b) i)).trans
        (completeNetSections_eval_top f β b i)
  intro v
  refine ⟨∑ i, b.repr v i • a i, ?_⟩
  change q (∑ i, b.repr v i • a i) = v
  rw [map_sum]
  simp_rw [q.map_smul, hqa]
  exact b.sum_repr v

/-- The complete net identifies the actual zeroth cohomology of its free
source with that of the line bundle. -/
def completeNetEvaluationCohomologyZeroEquiv (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    cohomologyOverField k f (netFree X) 0 ≃ₗ[k] cohomologyOverField k f β 0 :=
  LinearEquiv.ofBijective
    (cohomologyOverFieldMap k f (netEvaluation β (completeNetSections f β b)) 0).hom
    ⟨completeNetEvaluation_cohomology_zero_injective f β b,
      completeNetEvaluation_cohomology_zero_surjective f β b⟩

/-- In this actual complete-net situation the free source has three
global sections over the ground field. -/
theorem netFree_cohomology_zero_finrank (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Module.finrank k (cohomologyOverField k f (netFree X) 0) = 3 := by
  rw [(completeNetEvaluationCohomologyZeroEquiv f β b).finrank_eq]
  simpa only [Fintype.card_ulift, Fintype.card_fin] using Module.finrank_eq_card_basis b

/-- The actual kernel of a complete, generating evaluation has no native
zeroth cohomology. No vanishing or section-count premise is supplied. -/
theorem completeNetKernel_cohomology_zero_subsingleton (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (completeNetSections f β b))) :
    Subsingleton (cohomologyOverField k f
      (evaluationKernel β (completeNetSections f β b)) 0) :=
  evaluationKernel_H0_subsingleton k f β _ hgen
    (completeNetEvaluation_cohomology_zero_injective f β b)

/-- Equal-degree, nonisomorphic actual line bundles have no nonzero
morphism. This is the unequal-net branch of Mukai's vanishing argument. -/
theorem hom_eq_zero_of_equal_degree_not_isomorphic (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (α β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hdeg : invertibleCurveDegree k f hdim α = invertibleCurveDegree k f hdim β)
    (hαβ : ¬ Nonempty (α ≅ β)) (φ : α ⟶ β) : φ = 0 := by
  by_contra hφ
  let := isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero k f hdim α β φ hφ hdeg
  exact hαβ ⟨asIso φ⟩

/-- A positive-degree actual line bundle has no morphism to the structure
sheaf, by the native degree inequality for a nonzero morphism. -/
theorem hom_structure_eq_zero_of_positive_degree (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hdeg : 0 < invertibleCurveDegree k f hdim β)
    (φ : β ⟶ structureModule X) : φ = 0 := by
  by_contra hφ
  have hle := invertibleCurveDegree_le_of_hom_ne_zero k f hdim β
    (structureModule X) φ hφ
  have hunit := invertibleCurveDegree_unit_eq_zero k f hdim
  exact (not_le_of_gt hdeg) (by simpa only [structureModule, hunit] using hle)

/-- In particular the actual dual of a positive-degree line bundle has
zero zeroth cohomology; this does not assume a dual degree formula. -/
theorem dual_cohomology_zero_subsingleton_of_positive_degree
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (hdeg : 0 < invertibleCurveDegree k f hdim β) :
    Subsingleton (cohomologyOverField k f
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf β) 0) := by
  let := modulesLinearOverField k f
  let e := M9StacksIntegration.InvertibleHomCancellation.homDualLinearEquivCohomologyZero f β
  refine ⟨fun a c => e.symm.injective ?_⟩
  exact (hom_structure_eq_zero_of_positive_degree f hdim β hdeg (e.symm a)).trans
    (hom_structure_eq_zero_of_positive_degree f hdim β hdeg (e.symm c)).symm

end M9Native.MukaiDualSpanSections
