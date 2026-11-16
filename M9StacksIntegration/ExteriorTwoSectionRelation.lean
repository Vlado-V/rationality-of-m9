module

public import M9StacksIntegration.LagrangianSigmaInvariance

/-! A genuine two-section relation with a unit coefficient annihilates
the actual wedge over arbitrary rings and arbitrary schemes. No field
points, reducedness, or nonzero-locus premise is used. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory
universe u v

namespace M9Native.ExteriorTwoSectionRelation

theorem algebraic_left {R : Type u} [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] (a : R) (s t : V) (h : s + a • t = 0) :
    exteriorPower.ιMulti R 2 ![s,t] = 0 := by
  have hs : s = (-a) • t := by simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
  have hv : ![s,t] = Function.update (fun _ : Fin 2 => t) 0 ((-a) • t) := by
    funext i
    fin_cases i <;> simp [hs]
  rw [hv, (exteriorPower.ιMulti R 2).map_update_smul (fun _ : Fin 2 => t) 0 (-a) t,
    Function.update_eq_self,
    (exteriorPower.ιMulti R 2).map_eq_zero_of_eq (fun _ : Fin 2 => t)
      (i := 0) (j := 1) rfl (by decide), smul_zero]

theorem algebraic_right {R : Type u} [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] (a : R) (s t : V) (h : t + a • s = 0) :
    exteriorPower.ιMulti R 2 ![s,t] = 0 := by
  have ht : t = (-a) • s := by simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
  have hv : ![s,t] = Function.update (fun _ : Fin 2 => s) 1 ((-a) • s) := by
    funext i
    fin_cases i <;> simp [ht]
  rw [hv, (exteriorPower.ιMulti R 2).map_update_smul (fun _ : Fin 2 => s) 1 (-a) s,
    Function.update_eq_self,
    (exteriorPower.ιMulti R 2).map_eq_zero_of_eq (fun _ : Fin 2 => s)
      (i := 0) (j := 1) rfl (by decide), smul_zero]

theorem wedge_zero_of_left_relation {X : Scheme.{u}} (E : X.Modules)
    (a : Γ(X, ⊤)) (s t : Γ(E, ⊤)) (h : s + a • t = 0) :
    LagrangianGrassmannian.wedgeSection X E s t = 0 :=
  (LagrangianSigmaInvariance.wedgeSection_eq_comparison X E s t).trans
    ((congrArg (ExteriorEvaluation.sectionComparison E 2 ⊤) (algebraic_left a s t h)).trans
      (map_zero _))

theorem wedge_zero_of_right_relation {X : Scheme.{u}} (E : X.Modules)
    (a : Γ(X, ⊤)) (s t : Γ(E, ⊤)) (h : t + a • s = 0) :
    LagrangianGrassmannian.wedgeSection X E s t = 0 :=
  (LagrangianSigmaInvariance.wedgeSection_eq_comparison X E s t).trans
    ((congrArg (ExteriorEvaluation.sectionComparison E 2 ⊤) (algebraic_right a s t h)).trans
      (map_zero _))

end M9Native.ExteriorTwoSectionRelation
