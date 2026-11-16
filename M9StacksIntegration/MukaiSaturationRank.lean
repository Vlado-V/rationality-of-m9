module

public import M9StacksIntegration.TupleEvaluationFiberRank
public import M9StacksIntegration.MukaiSaturationSections
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank of the prescribed saturation of a zero exterior-evaluation pair

The saturation is the original kernel constructed from the torsion-free
quotient of the original cokernel. Its generic image is identified with
the original evaluation image, rather than supplied as a rank premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.MukaiSaturationRank

section Linear

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Contraction with a linear functional, as an actual alternating map on pairs. -/
def pairContraction (ell : V →ₗ[K] K) : AlternatingMap K V V (Fin 2) where
  toFun v := ell (v 0) • v 1 - ell (v 1) • v 0
  map_update_add' := by
    intro _ v i a b
    fin_cases i <;> simp [Function.update, map_add, add_smul, smul_add] <;> abel
  map_update_smul' := by
    intro _ v i a b
    fin_cases i <;> simp [Function.update, map_smul, smul_sub, smul_smul, mul_comm]
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      rw [hij, sub_self]
    · change v 1 = v 0 at hij
      rw [hij, sub_self]
    · exact (hne rfl).elim

/-- Zero actual exterior product with a nonzero first vector forces scalar dependence. -/
theorem exists_smul_of_pair_wedge_zero {v w : V} (hv : v ≠ 0)
    (hw : exteriorPower.ιMulti K 2 ![v,w] = 0) : ∃ c : K, w = c • v := by
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one K hv
  have h := congrArg (exteriorPower.alternatingMapLinearEquiv (pairContraction ell)) hw
  rw [map_zero, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at h
  change ell v • w - ell w • v = 0 at h
  rw [hell, one_smul] at h
  exact ⟨ell w, sub_eq_zero.mp h⟩

end Linear

section Stalk

variable {X : Scheme.{u}}

/-- The canonical actual local-ring stalk module. -/
abbrev Stalk (E : X.Modules) (x : X) := ExteriorEvaluation.stalkSections E x

/-- The actual linear map of local-ring stalks induced by a sheaf morphism. -/
def stalkMap {E F : X.Modules} (phi : E ⟶ F) (x : X) :
    Stalk E x →ₗ[X.presheaf.stalk x] Stalk F x :=
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) E x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) F x
  Stacks.SheafOfModules.FlatShortExact.stalkLinearMap (X := X.toRingedSpace) phi x

/-- Its value on every genuine germ is the germ of the original image section. -/
theorem stalkMap_germ {E F : X.Modules} (phi : E ⟶ F) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(E, U)) :
    stalkMap phi x (TopCat.Presheaf.germ E.presheaf U x hx s) =
      TopCat.Presheaf.germ F.presheaf U x hx (phi.app U s) :=
  TupleEvaluationFiber.stalkMap_germ phi x U hx s

/-- The actual map agrees with the native exact stalk functor on underlying elements. -/
theorem stalkMap_native {E F : X.Modules} (phi : E ⟶ F) (x : X) (s : Stalk E x) :
    stalkMap phi x s =
      (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x phi).hom s := by
  obtain ⟨U, hx, t, rfl⟩ := E.presheaf.exists_germ_eq s
  exact (stalkMap_germ phi x U hx t).trans
    (AlgebraicGeometry.SheafOfModules.stalkMap_germ X.ringCatSheaf x phi U hx t).symm

/-- Exactness of the original sheaf maps is exactness of these actual stalk maps. -/
theorem stalkMap_exact (S : ShortComplex X.Modules) (hS : S.Exact) (x : X) :
    Function.Exact (stalkMap S.f x) (stalkMap S.g x) := by
  have h := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (O := X.ringCatSheaf) S).mp hS x
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  change Function.Exact
    (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x S.f).hom
    (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x S.g).hom at h
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := (h s).mp ((stalkMap_native S.g x s).symm.trans hs)
    exact ⟨t, (stalkMap_native S.f x t).trans ht⟩
  · rintro ⟨t, ht⟩
    exact (stalkMap_native S.g x s).trans
      ((h s).mpr ⟨t, (stalkMap_native S.f x t).symm.trans ht⟩)

/-- A genuine monomorphism of sheaves is injective on its actual local-ring stalks. -/
theorem stalkMap_injective {E F : X.Modules} (phi : E ⟶ F) [Mono phi] (x : X) :
    Function.Injective (stalkMap phi x) := by
  have h := (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (O := X.ringCatSheaf) phi).mp inferInstance x
  intro a b hab
  exact h (by simpa only [← stalkMap_native] using hab)

/-- Composition uses the original sheaf maps, also on arbitrary stalk elements. -/
theorem stalkMap_comp {E F G : X.Modules} (phi : E ⟶ F) (psi : F ⟶ G)
    (x : X) (s : Stalk E x) :
    stalkMap (phi ≫ psi) x s = stalkMap psi x (stalkMap phi x s) := by
  obtain ⟨U, hx, t, rfl⟩ := E.presheaf.exists_germ_eq s
  rw [stalkMap_germ, stalkMap_germ, stalkMap_germ]
  rfl

end Stalk

section GenericSaturation

open Stacks.AlgebraicGeometry.TorsionQuasicoherent
open MukaiEvaluationSaturation

variable {X : Scheme.{u}} [IsIntegral X]

/-- Torsion sections have zero image in the actual generic stalk, whose local ring is a field. -/
theorem torsionIncl_generic_stalk_zero (C : X.Modules) [C.IsQuasicoherent]
    (s : Stalk (torsionModule C) (genericPoint X)) :
    stalkMap (torsionIncl C) (genericPoint X) s = 0 := by
  obtain ⟨U, hx, t, rfl⟩ := (torsionModule C).presheaf.exists_germ_eq s
  rw [stalkMap_germ]
  obtain ⟨a, ha, has⟩ := isTorsionSection_val C t (genericPoint X) hx
  exact eq_zero_of_isUnit_smul_eq_zero (isUnit_of_ne_zero_stalk_genericPoint ha) has

/-- The original quotient by torsion is injective on the actual generic stalk. -/
theorem torsionQuotient_generic_stalk_injective (C : X.Modules) [C.IsQuasicoherent] :
    Function.Injective (stalkMap (cokernel.π (torsionIncl C)) (genericPoint X)) := by
  have he := stalkMap_exact (ShortComplex.cokernelSequence (torsionIncl C))
    (ShortComplex.cokernelSequence_exact _) (genericPoint X)
  intro a b hab
  have hz : stalkMap (cokernel.π (torsionIncl C)) (genericPoint X) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨s, hs⟩ := (he (a - b)).mp hz
  exact sub_eq_zero.mp (hs.symm.trans (torsionIncl_generic_stalk_zero C s))

variable {F E : X.Modules} (phi : F ⟶ E) [(cokernel phi).IsQuasicoherent]

/-- The prescribed saturation has exactly the original image at the actual generic stalk. -/
theorem range_saturation_generic_eq_range :
    LinearMap.range (stalkMap (inclusion phi) (genericPoint X)) =
      LinearMap.range (stalkMap phi (genericPoint X)) := by
  have hs := stalkMap_exact
    (ShortComplex.mk (inclusion phi) (projection phi) (kernel.condition (projection phi)))
    (sequence_shortExact phi).exact (genericPoint X)
  have hc := stalkMap_exact (ShortComplex.cokernelSequence phi)
    (ShortComplex.cokernelSequence_exact _) (genericPoint X)
  have ht := torsionQuotient_generic_stalk_injective (cokernel phi)
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    have hproj : stalkMap (projection phi) (genericPoint X)
        (stalkMap (inclusion phi) (genericPoint X) s) = 0 := (hs _).mpr ⟨s, rfl⟩
    apply (hc _).mp
    apply ht
    rw [map_zero]
    exact (stalkMap_comp (cokernel.π phi) (cokernel.π (torsionIncl (cokernel phi)))
      (genericPoint X) _).symm.trans hproj
  · rintro ⟨s, rfl⟩
    apply (hs _).mp
    have hraw : stalkMap (cokernel.π phi) (genericPoint X)
        (stalkMap phi (genericPoint X) s) = 0 := (hc _).mpr ⟨s, rfl⟩
    change stalkMap (cokernel.π phi ≫ cokernel.π (torsionIncl (cokernel phi)))
      (genericPoint X) (stalkMap phi (genericPoint X) s) = 0
    rw [stalkMap_comp, hraw, map_zero]

/-- Its generic dimension is therefore the rank of the original map, with no rank premise. -/
theorem finrank_saturation_generic_eq_finrank_range :
    Module.finrank (X.presheaf.stalk (genericPoint X))
        (Stalk (saturation phi) (genericPoint X)) =
      Module.finrank (X.presheaf.stalk (genericPoint X))
        (LinearMap.range (stalkMap phi (genericPoint X))) := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  rw [← range_saturation_generic_eq_range phi]
  exact (LinearMap.finrank_range_of_inj
    (stalkMap_injective (inclusion phi) (genericPoint X))).symm

end GenericSaturation

section Evaluation

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The actual local-ring coordinate map whose columns are the original section germs. -/
def stalkTupleMap {r : ℕ} (E : X.Modules) (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    (Fin r → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x] Stalk E x :=
  (Pi.basisFun (X.presheaf.stalk x) (Fin r)).constr (X.presheaf.stalk x)
    (fun i => ExteriorEvaluation.h0StalkEvaluation k f E x (s i))

theorem stalkTupleMap_single {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) (i : Fin r) :
    stalkTupleMap k f E s x (Pi.single i 1) =
      ExteriorEvaluation.h0StalkEvaluation k f E x (s i) := by
  change (Pi.basisFun (X.presheaf.stalk x) (Fin r)).constr (X.presheaf.stalk x)
    (fun j => ExteriorEvaluation.h0StalkEvaluation k f E x (s j)) (Pi.single i 1) = _
  rw [← Pi.basisFun_apply (X.presheaf.stalk x) (Fin r) i, Module.Basis.constr_basis]

/-- The genuine evaluation on each actual free-stalk basis vector is the original germ. -/
theorem evaluation_stalk_basis {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) (i : Fin r) :
    stalkMap (MukaiSemiIrreducible.evaluation k f E s) x
        (TupleEvaluationFiber.freeStalkBasis r x i) =
      ExteriorEvaluation.h0StalkEvaluation k f E x (s i) := by
  rw [TupleEvaluationFiber.freeStalkBasis_germ, stalkMap_germ]
  exact congrArg (fun z : Γ(E, ⊤) => TopCat.Presheaf.germ E.presheaf ⊤ x (by simp) z)
    (TupleEvaluationFiber.evaluation_freeSection_top k f E s i)

/-- In the original free-stalk coordinates, the sheaf evaluation is exactly `stalkTupleMap`. -/
theorem evaluation_stalk_coordinates {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    (stalkMap (MukaiSemiIrreducible.evaluation k f E s) x).comp
        (TupleEvaluationFiber.freeStalkBasis r x).equivFun.symm.toLinearMap =
      stalkTupleMap k f E s x := by
  apply (Pi.basisFun (X.presheaf.stalk x) (Fin r)).ext
  intro i
  change stalkMap (MukaiSemiIrreducible.evaluation k f E s) x
    ((TupleEvaluationFiber.freeStalkBasis r x).equivFun.symm
      ((Pi.basisFun (X.presheaf.stalk x) (Fin r)) i)) = _
  rw [Pi.basisFun_apply, stalkTupleMap_single]
  have h : (TupleEvaluationFiber.freeStalkBasis r x).equivFun.symm (Pi.single i 1) =
      TupleEvaluationFiber.freeStalkBasis r x i := by
    classical
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  rw [h]
  exact evaluation_stalk_basis k f E s x i

theorem range_stalkTupleMap_eq_range_evaluation {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    LinearMap.range (stalkTupleMap k f E s x) =
      LinearMap.range (stalkMap (MukaiSemiIrreducible.evaluation k f E s) x) := by
  rw [← evaluation_stalk_coordinates k f E s x]
  exact LinearMap.range_comp_of_range_eq_top _
    (TupleEvaluationFiber.freeStalkBasis r x).equivFun.symm.range

/-- This actual image is the span of precisely the original section germs. -/
theorem range_stalkTupleMap {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    LinearMap.range (stalkTupleMap k f E s x) =
      Submodule.span (X.presheaf.stalk x)
        (Set.range (fun i => ExteriorEvaluation.h0StalkEvaluation k f E x (s i))) :=
  (Pi.basisFun (X.presheaf.stalk x) (Fin r)).constr_range (X.presheaf.stalk x)

variable [IsIntegral X]

/-- Original nonzero H0 sections of a torsion-free sheaf have nonzero actual generic germs. -/
theorem h0_generic_germ_ne_zero (E : X.Modules) [E.IsQuasicoherent]
    (hE : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E)
    {s : cohomologyOverField k f E 0} (hs : s ≠ 0) :
    ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) s ≠ 0 := by
  intro h
  have hg : (cohomologyOverFieldZeroLinearIso k f E).hom s = 0 := by
    apply AlgebraicGeometry.injective_generic_germ_of_isTorsionFree E hE (U := ⊤) (by simp)
    rw [map_zero]
    exact h
  apply hs
  apply (cohomologyOverFieldZeroLinearIso k f E).toLinearEquiv.injective
  change (cohomologyOverFieldZeroLinearIso k f E).hom s =
    (cohomologyOverFieldZeroLinearIso k f E).hom 0
  rw [map_zero]
  exact hg

/-- Actual `λ₂`-vanishing and an original nonzero section give generic evaluation rank one. -/
theorem finrank_evaluation_generic_eq_one (E : X.Modules) [E.IsQuasicoherent]
    (hE : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E)
    (s : Fin 2 → cohomologyOverField k f E 0) (hs : s 0 ≠ 0)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.range (stalkMap (MukaiSemiIrreducible.evaluation k f E s) (genericPoint X))) = 1 := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let v := ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s 0)
  let w := ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s 1)
  have hv : v ≠ 0 := h0_generic_germ_ne_zero k f E hE hs
  have hf : (fun i : Fin 2 => ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s i)) =
      ![v,w] := by
    funext i
    fin_cases i <;> rfl
  have hz := ExteriorEvaluation.wedge_germs_eq_zero_of_lambda_eq_zero k f E 2
    (genericPoint X) s hw
  rw [hf] at hz
  obtain ⟨c, hc⟩ := exists_smul_of_pair_wedge_zero hv hz
  rw [← range_stalkTupleMap_eq_range_evaluation k f E s (genericPoint X), range_stalkTupleMap]
  have hspan : Submodule.span (X.presheaf.stalk (genericPoint X))
      (Set.range (fun i => ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s i))) =
      Submodule.span (X.presheaf.stalk (genericPoint X)) ({v} : Set (Stalk E (genericPoint X))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span (Set.mem_singleton v)
      · change w ∈ _
        rw [hc]
        exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
    · apply Submodule.span_le.mpr
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact Submodule.subset_span ⟨0, rfl⟩
  rw [hspan]
  exact finrank_span_singleton hv

end Evaluation

section RankOne

open MukaiEvaluationSaturation

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) (E : X.Modules) [E.IsQuasicoherent]
variable (s : Fin 2 → cohomologyOverField k f E 0)
variable [(cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent]

/-- The prescribed saturation of an actual zero-wedge pair is finite locally free of rank one.
The nonzero hypothesis is on the original global section, not on an assumed generic value. -/
theorem evaluation_saturation_rank_one
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E)
    (hs : s 0 ≠ 0)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (saturation (MukaiSemiIrreducible.evaluation k f E s)) 1 := by
  let phi := MukaiSemiIrreducible.evaluation k f E s
  let := hE
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  have hET : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr hE
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (saturation phi) :=
    saturation_isFiniteLocallyFree phi hreg hdim hE
  let : (saturation phi).IsCoherent := saturation_isCoherent phi
  let : (saturation phi).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hdimS : Module.finrank (X.presheaf.stalk (genericPoint X))
      (Stalk (saturation phi) (genericPoint X)) = 1 :=
    (finrank_saturation_generic_eq_finrank_range phi).trans
      (finrank_evaluation_generic_eq_one k f E hET s hs hw)
  have hfr : Scheme.Modules.fiberRank (saturation phi) (genericPoint X) = 1 :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (saturation phi)).trans hdimS
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (saturation phi) 1 (genericPoint X) hfr

/-- This very constructed saturation is an actual invertible subsheaf. -/
theorem evaluation_saturation_invertible
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E)
    (hs : s 0 ≠ 0)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (saturation (MukaiSemiIrreducible.evaluation k f E s)) := by
  let := evaluation_saturation_rank_one k f E s hreg hdim hE hs hw
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

end RankOne

section ActualPair

open MukaiEvaluationSaturation

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) (E : X.Modules)
variable [hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
variable (s : Fin 2 → cohomologyOverField k f E 0)

/-- An actual independent pair killed by `λ₂` has its prescribed saturation of rank one.
Both quasi-coherence instances needed by the construction are derived internally. -/
theorem actual_pair_saturation_rank_one
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (saturation (MukaiSemiIrreducible.evaluation k f E s)) 1 := by
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  exact evaluation_saturation_rank_one k f E s hreg hdim hE (hs.ne_zero 0) hw

/-- The same prescribed saturation is invertible, without an extra rank or generic premise. -/
theorem actual_pair_saturation_invertible
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (saturation (MukaiSemiIrreducible.evaluation k f E s)) := by
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  exact evaluation_saturation_invertible k f E s hreg hdim hE (hs.ne_zero 0) hw

/-- An actual independent zero-wedge pair gives its actual saturated line with two sections. -/
theorem actual_pair_saturation_line_with_two_sections
    [FiniteDimensional k (cohomologyOverField k f E 0)]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) = 0) :
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) ∧
      2 ≤ Module.finrank k (cohomologyOverField k f
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) 0) := by
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  exact ⟨evaluation_saturation_invertible k f E s hreg hdim hE (hs.ne_zero 0) hw,
    MukaiSaturationSections.evaluation_saturation_h0_lower_bound k f E s hs⟩

end ActualPair

end M9Native.MukaiSaturationRank
