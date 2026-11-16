module

public import M9StacksIntegration.MukaiPrimitiveCanonicalDiagram

/-!
# Actual evaluation and kernel generators under changes of bundle

The cohomology isomorphisms are induced by the original sheaf isomorphisms.
The exterior-evaluation squares and complete evaluation triangles are literal
native maps.  The canonical exterior dimension is used together with the
proved semi-irreducibility exclusions to recover the actual kernel line.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiEvaluationChoices

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The original sheaf isomorphism induces the actual complete-section isomorphism. -/
def cohomologyEquiv {E F : X.Modules} (e : E ≅ F) (n : ℕ) :
    cohomologyOverField k f E n ≃ₗ[k] cohomologyOverField k f F n where
  toFun := cohomologyOverFieldMap k f e.hom n
  invFun := cohomologyOverFieldMap k f e.inv n
  left_inv s := by
    have h := congrArg (fun m => (m : cohomologyOverField k f E n ⟶ cohomologyOverField k f E n) s)
      (cohomologyOverFieldMap_comp k f e.hom e.inv n)
    rw [e.hom_inv_id, cohomologyOverFieldMap_id] at h
    exact h.symm
  right_inv s := by
    have h := congrArg (fun m => (m : cohomologyOverField k f F n ⟶ cohomologyOverField k f F n) s)
      (cohomologyOverFieldMap_comp k f e.inv e.hom n)
    rw [e.inv_hom_id, cohomologyOverFieldMap_id] at h
    exact h.symm
  map_add' := (cohomologyOverFieldMap k f e.hom n).hom.map_add
  map_smul' := (cohomologyOverFieldMap k f e.hom n).hom.map_smul

def h0Equiv {E F : X.Modules} (e : E ≅ F) : H0 k f E ≃ₗ[k] H0 k f F :=
  cohomologyEquiv k f e 0

theorem h0Equiv_apply {E F : X.Modules} (e : E ≅ F) (s : H0 k f E) :
    h0Equiv k f e s = cohomologyOverFieldMap k f e.hom 0 s := rfl

def exteriorH0Equiv {E F : X.Modules} (e : E ≅ F) (n : ℕ) :
    cohomologyOverField k f (Scheme.Modules.exteriorPower E (n : ℤ)) 0 ≃ₗ[k]
      cohomologyOverField k f (Scheme.Modules.exteriorPower F (n : ℤ)) 0 :=
  cohomologyEquiv k f ((Scheme.Modules.exteriorPowerFunctor X (n : ℤ)).mapIso e) 0

/-- Actual exterior evaluation commutes with the original bundle isomorphism. -/
theorem lambda_h0Equiv {E F : X.Modules} (e : E ≅ F) (n : ℕ)
    (w : ⋀[k]^n (H0 k f E)) :
    exteriorH0Equiv k f e n (ExteriorEvaluation.lambda k f E n w) =
      ExteriorEvaluation.lambda k f F n
        (exteriorPower.map n (h0Equiv k f e).toLinearMap w) :=
  LinearMap.congr_fun (ExteriorEvaluation.lambda_iso_naturality k f e n) w

theorem lambda_kernel_transport {E F : X.Modules} (e : E ≅ F) (n : ℕ)
    (w : ⋀[k]^n (H0 k f E)) :
    ExteriorEvaluation.lambda k f F n
        (exteriorPower.map n (h0Equiv k f e).toLinearMap w) = 0 ↔
      ExteriorEvaluation.lambda k f E n w = 0 := by
  rw [← lambda_h0Equiv]
  exact map_eq_zero_iff _ (exteriorH0Equiv k f e n).injective

theorem sectionOfH0_naturality {E F : X.Modules} (φ : E ⟶ F) (s : H0 k f E) :
    SheafOfModules.sectionsMap φ (MukaiSemiIrreducible.sectionOfH0 k f E s) =
      MukaiSemiIrreducible.sectionOfH0 k f F (cohomologyOverFieldMap k f φ 0 s) := by
  apply Stacks.PresheafOfModules.sections_ext_top
  change φ.app ⊤ ((MukaiSemiIrreducible.sectionOfH0 k f E s).eval (op ⊤)) =
    (MukaiSemiIrreducible.sectionOfH0 k f F (cohomologyOverFieldMap k f φ 0 s)).eval (op ⊤)
  rw [MukaiSemiIrreducible.sectionOfH0_eval_top, MukaiSemiIrreducible.sectionOfH0_eval_top]
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f φ s).symm

/-- The original complete evaluation, not an existential generator map,
commutes with every actual morphism of target sheaves. -/
theorem evaluation_postcomp {E F : X.Modules} (φ : E ⟶ F) {r : ℕ}
    (s : Fin r → H0 k f E) :
    MukaiSemiIrreducible.evaluation k f E s ≫ φ =
      MukaiSemiIrreducible.evaluation k f F (fun i => cohomologyOverFieldMap k f φ 0 (s i)) := by
  rw [MukaiSemiIrreducible.evaluation, SheafOfModules.freeHomEquiv_symm_comp]
  apply congrArg F.freeHomEquiv.symm
  funext i
  exact sectionOfH0_naturality k f φ (s i.down)

theorem evaluation_mapped_basis {E F : X.Modules} (e : E ≅ F)
    (b : Basis (Fin 6) k (H0 k f E)) :
    MukaiSemiIrreducible.evaluation k f E b ≫ e.hom =
      MukaiSemiIrreducible.evaluation k f F (b.map (h0Equiv k f e)) :=
  evaluation_postcomp k f e.hom b

/-- The actual basis bivector is functorial, including its ordered signs. -/
theorem basisSigma_map {E F : X.Modules} (e : E ≅ F)
    (b : Basis (Fin 6) k (H0 k f E)) :
    exteriorPower.map 2 (h0Equiv k f e).toLinearMap (basisSigma k f E b) =
      basisSigma k f F (b.map (h0Equiv k f e)) := by
  simp only [basisSigma, map_sum, exteriorPower.map_apply_ιMulti, Basis.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem coordinateBivector_basisSigma {E : X.Modules} (b : Basis (Fin 6) k (H0 k f E)) :
    MukaiWedgeKernel.coordinateBivector k f E b (basisSigma k f E b) = standardSigma k := by
  simp only [MukaiWedgeKernel.coordinateBivector, basisSigma, standardSigma, map_sum,
    exteriorPower.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> funext r <;> simp [Pi.single_apply, eq_comm]

theorem standardSigma_ne_zero : standardSigma k ≠ 0 := by
  intro h
  have hv : MukaiWedgeKernel.bivectorMatrix k 6 (standardSigma k) 0 3 = 1 := by
    norm_num [standardSigma, map_sum, MukaiWedgeKernel.bivectorMatrix_ιMulti,
      Matrix.vecMulVec_apply, Fin.sum_univ_succ, Pi.single_apply]
  rw [h, map_zero] at hv
  exact zero_ne_one hv

theorem basisSigma_ne_zero {E : X.Modules} (b : Basis (Fin 6) k (H0 k f E)) :
    basisSigma k f E b ≠ 0 := by
  intro h
  have hc := coordinateBivector_basisSigma k f b
  rw [h, map_zero] at hc
  exact standardSigma_ne_zero k hc.symm

section CanonicalChoice

variable [CharZero k] {E : X.Modules}

/-- Postcomposition by an actual determinant-line isomorphism preserves
the kernel of the original primitive evaluation. -/
theorem ker_transportedEvaluation (b : Basis (Fin 6) k (H0 k f E))
    {L : X.Modules} (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ L) :
    LinearMap.ker (transportedEvaluation k f E b c) =
      LinearMap.ker (primitiveEvaluation k f E b) := by
  ext ell
  change cohomologyEquiv k f c 0 (primitiveEvaluation k f E b ell) = 0 ↔
    primitiveEvaluation k f E b ell = 0
  exact map_eq_zero_iff _ (cohomologyEquiv k f c 0).injective

/-- Canonical determinant trivializations give literally the same section
kernel; no scalar-automorphism or surjectivity premise is required. -/
theorem ker_canonicalEvaluation_choice [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    LinearMap.ker (canonicalEvaluation k f E b c) =
      LinearMap.ker (canonicalEvaluation k f E b d) :=
  (ker_transportedEvaluation k f b c).trans (ker_transportedEvaluation k f b d).symm

/-- For a fixed original complete basis, even the actual native canonical
projective morphism is independent of the determinant isomorphism. -/
theorem canonicalProjectiveMap_choice [IsProper f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) k (H0 k f E)) (q : EvaluationDiagram k f E b)
    (c d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    MukaiPrimitiveCanonicalDiagram.canonicalProjectiveMap k f E b c q =
      MukaiPrimitiveCanonicalDiagram.canonicalProjectiveMap k f E b d q :=
  (MukaiPrimitiveCanonicalDiagram.canonicalProjectiveMap_eq_determinant k f E b c q).trans
    (MukaiPrimitiveCanonicalDiagram.canonicalProjectiveMap_eq_determinant k f E b d q).symm

end CanonicalChoice

end M9Native.MukaiEvaluationChoices
