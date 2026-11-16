module

public import M9StacksIntegration.PencilCanonicalDivisor
public import M9StacksIntegration.RankTwoQuotientFactor
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic

/-! The actual original-field canonical evaluation on a full divisor,
read as literal pulled-back sections. The section expansion and its
rank bound are derived from the genuine restriction map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators

universe u

namespace M9Native.CanonicalDivisorEvaluation

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The ORIGINAL scalar restriction of the genuine divisor sections.
The carrier is literally the sections of the pulled-back line. -/
abbrev sectionsOnDivisor (D : X.IdealSheafData) (L : X.Modules) : ModuleCat K :=
  (restrictScalarsOverBase K f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L)))

/-- The original K-action is the actual structural action on the
divisor, not an arbitrary vector-space structure on its sections. -/
theorem sectionsOnDivisor_smul (D : X.IdealSheafData) (L : X.Modules)
    (a : K) (t : sectionsOnDivisor f D L) :
    (a • t : sectionsOnDivisor f D L) =
      (((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom a) •
        (show Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤) from t) := by
  change D.subschemeι.appTop.hom
      (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom a) •
        (show Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤) from t) = _
  rw [appLE_top_top_eq_appTop f]
  rfl

/-- Native cohomology restriction followed by the genuine H0/section
isomorphism, with no selected divisor basis or line trivialization. -/
def evaluation (D : X.IdealSheafData) (L : X.Modules) :
    cohomologyOverField K f L 0 →ₗ[K] sectionsOnDivisor f D L :=
  (cohomologyOverFieldZeroLinearIso K f
    ((Scheme.Modules.pushforward D.subschemeι).obj
      ((Scheme.Modules.pullback D.subschemeι).obj L))).hom.hom.comp
        (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom

/-- Evaluation is the actual pulled section, including nilpotents. -/
theorem evaluation_apply (D : X.IdealSheafData) (L : X.Modules)
    (x : cohomologyOverField K f L 0) :
    evaluation f D L x = pullbackGlobalSections D.subschemeι L
      ((cohomologyOverFieldZeroLinearIso K f L).hom x) := by
  change (cohomologyOverFieldZeroLinearIso K f _).hom
      (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0 x) = _
  rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap,
    pullbackGlobalSections_eq_unit]
  rfl

/-- Passing to actual sections and precomposing an original finite
coordinate system cannot enlarge the native restriction rank. -/
theorem evaluation_comp_rank_le {V : Type u} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (D : X.IdealSheafData) (L : X.Modules)
    [Module.Finite K (cohomologyOverField K f L 0)]
    (c : V →ₗ[K] cohomologyOverField K f L 0) :
    Module.finrank K (LinearMap.range ((evaluation f D L).comp c)) ≤
      Module.finrank K (LinearMap.range
        (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom) := by
  let r := (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom
  let e := (cohomologyOverFieldZeroLinearIso K f
    ((Scheme.Modules.pushforward D.subschemeι).obj
      ((Scheme.Modules.pullback D.subschemeι).obj L))).hom.hom
  change Module.finrank K (LinearMap.range ((e.comp r).comp c)) ≤ _
  rw [LinearMap.comp_assoc, LinearMap.range_comp]
  refine (Submodule.finrank_map_le e (LinearMap.range (r.comp c))).trans ?_
  exact Submodule.finrank_mono (by
    rw [LinearMap.range_comp]
    exact LinearMap.map_le_range)

/-- The literal smaller section system produced by any actual quotient
factorization. This statement is generic in the quotient dimension. -/
theorem sections_expansion {V : Type u} [AddCommGroup V] [Module K V]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (D : X.IdealSheafData)
    (L : X.Modules) (c : V →ₗ[K] cohomologyOverField K f L 0)
    (q : V →ₗ[K] (Fin m → K))
    (g : (Fin m → K) →ₗ[K] sectionsOnDivisor f D L)
    (h : g.comp q = (evaluation f D L).comp c) (j : Fin n) :
    pullbackGlobalSections D.subschemeι L
        ((cohomologyOverFieldZeroLinearIso K f L).hom (c (b j))) =
      ∑ i : Fin m, q (b j) i • g (Pi.single i 1) := by
  rw [← evaluation_apply f D L]
  have hj := LinearMap.congr_fun h (b j)
  change g (q (b j)) = evaluation f D L (c (b j)) at hj
  rw [← hj]
  have he := (Pi.basisFun K (Fin m)).sum_repr (q (b j))
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using
    congrArg g he.symm

/-- The same actual expansion in the sheaf's original structural-ring
scalar notation, ready for the native projective moduli theorem. -/
theorem sections_expansion_structural {V : Type u} [AddCommGroup V] [Module K V]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (D : X.IdealSheafData)
    (L : X.Modules) (c : V →ₗ[K] cohomologyOverField K f L 0)
    (q : V →ₗ[K] (Fin m → K))
    (g : (Fin m → K) →ₗ[K] sectionsOnDivisor f D L)
    (h : g.comp q = (evaluation f D L).comp c) (j : Fin n) :
    pullbackGlobalSections D.subschemeι L
        ((cohomologyOverFieldZeroLinearIso K f L).hom (c (b j))) =
      ∑ i : Fin m, (((Scheme.ΓSpecIso (.of K)).inv ≫
        (D.subschemeι ≫ f).appTop).hom (q (b j) i)) •
          (show Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤) from g (Pi.single i 1)) := by
  rw [sections_expansion f b D L c q g h j]
  exact Finset.sum_congr rfl fun i _ => sectionsOnDivisor_smul f D L _ _

section Canonical

variable [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

local instance canonicalInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) :=
  CurveCanonicalInvertibility.dualizing_isInvertible f

/-- The original canonical coordinate evaluation has rank at most d-1
on the FULL divisor of an original native g1_d. -/
theorem pencil_evaluation_rank_le {V : Type u} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (bA : Module.Basis (Fin 2) K A.V)
    (c : V →ₗ[K] cohomologyOverField K f (Stacks.Duality.dualizingSheafOverField f) 0) :
    Module.finrank K (LinearMap.range
      ((evaluation f (PencilCanonicalDivisor.divisor f hdim A bA)
        (Stacks.Duality.dualizingSheafOverField f)).comp c)) ≤ d-1 := by
  letI := CurveDivisorSections.invertible_cohomology_zero_finite f
    (Stacks.Duality.dualizingSheafOverField f)
  exact (evaluation_comp_rank_le f _ _ c).trans
    (PencilCanonicalDivisor.canonical_restriction_rank_le f hdim A bA)

end Canonical
end M9Native.CanonicalDivisorEvaluation
