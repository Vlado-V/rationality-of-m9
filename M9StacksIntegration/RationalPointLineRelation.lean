module

public import M9StacksIntegration.PencilPullbackSections
public import M9StacksIntegration.ExteriorEvaluation
public import M9StacksIntegration.CurveDivisorSections

/-!
# An actual linear relation on two line sections at a rational point

The pullback of an invertible module to an original-field rational point
has actual H0 dimension one. A genuine kernel of the map from two
coefficients constructs a nonzero relation, with the original structural
scalars. No evaluation rank or relation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace M9Native.RationalPointLineRelation

open PencilPullbackSections

/-- The original structural rational-point condition derives the actual
one-dimensional H0 of any original line at that point. -/
theorem pullback_h0_eq_one {K : Type u} [Field K] {Y : Scheme.{u}}
    (r : Y ⟶ Spec (.of K)) (q : Spec (.of K) ⟶ Y)
    (hq : q ≫ r = 𝟙 _) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L] :
    Module.finrank K (cohomologyOverField K (q ≫ r)
      ((Scheme.Modules.pullback q).obj L) 0) = 1 := by
  let C := (Scheme.Modules.pullback q).obj L
  let : SheafOfModules.IsInvertible (Spec (.of K)).presheaf
      (Spec (.of K)).ringCatSheaf.property C :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback q L
  let : Stacks.SheafOfModules.IsInvertible (Spec (.of K)).presheaf
      (Spec (.of K)).ringCatSheaf.property C :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ C inferInstance
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology (Spec (.of K)) C
  let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (q ≫ r).appTop) := by
    rw [hq,Scheme.Hom.id_appTop,Category.comp_id]
    infer_instance
  exact (finrank_cohomologyOverField_eq_of_iso K (q ≫ r) e 0).trans
    (finrank_cohomologyOverField_unit_zero_eq_one (q ≫ r))

/-- The nonzero pair of coefficients is constructed from the actual
one-dimensional pullback of the original line. -/
theorem exists_nonzero_relation {K : Type u} [Field K] {Y : Scheme.{u}}
    (r : Y ⟶ Spec (.of K)) (q : Spec (.of K) ⟶ Y)
    (hq : q ≫ r = 𝟙 _) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L]
    (t : Fin 2 → Γ(L, ⊤)) :
    ∃ a : Fin 2 → K, a ≠ 0 ∧
      pullbackGlobalSections q L
        (∑ i : Fin 2, ExteriorEvaluation.baseRingMap K r (a i) • t i) = 0 := by
  let C := (Scheme.Modules.pullback q).obj L
  let W := fieldGlobalSections K (q ≫ r) C
  have hW : Module.finrank K W = 1 :=
    (cohomologyOverFieldZeroLinearIso K (q ≫ r) C).toLinearEquiv.finrank_eq.symm.trans
      (pullback_h0_eq_one r q hq L)
  let : Module.Finite K W := Module.finite_of_finrank_pos (by rw [hW]; decide)
  let T : (Fin 2 → K) →ₗ[K] fieldGlobalSections K r L :=
    Fintype.linearCombination K (show Fin 2 → fieldGlobalSections K r L from t)
  let E : (Fin 2 → K) →ₗ[K] W := (globalSectionsPullback K r q L).comp T
  have hker : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [hW]
    simp)
  obtain ⟨a,ha,hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨a,hane,?_⟩
  have hzero : E a = 0 := ha
  change pullbackGlobalSections q L (T a) = 0 at hzero
  have hsmul (k : K) (s : fieldGlobalSections K r L) :
      (k • s : fieldGlobalSections K r L) =
        ExteriorEvaluation.baseRingMap K r k • (show Γ(L, ⊤) from s) := rfl
  simpa only [T,Fintype.linearCombination_apply,hsmul] using hzero

end M9Native.RationalPointLineRelation
