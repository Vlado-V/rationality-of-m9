module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring

/-!
# The native rational-graph quotient is an actual localization

The coefficient variables are `Y_i`, and the outer variables are `T_i` and
`u`. The quotient has precisely the graph relations `A(T)Y_i=N_i(T)` and
`u B(T) A(T)=1`. No nonzero-denominator hypothesis is needed: the same
construction includes the possibly trivial localization.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace M9.GaussGraphQuotient

open MvPolynomial

variable (K I : Type*) [CommRing K]

abbrev Parameters := MvPolynomial I K
abbrev Coefficients := MvPolynomial I K
abbrev GraphPolynomial := MvPolynomial (I ⊕ Unit) (Coefficients K I)

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The actual parameter-polynomial map into the graph polynomial ring. -/
def parameterMap : Parameters K I →ₐ[K] GraphPolynomial K I :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (.inl i))

@[simp] theorem parameterMap_X (i : I) :
    parameterMap K I (X i) = X (.inl i) := by simp [parameterMap]

def denominator (A B : Parameters K I) : Parameters K I := B * A

def graphRelation (A : Parameters K I) (N : I → Parameters K I) (i : I) : GraphPolynomial K I :=
  parameterMap K I A * C (X i) - parameterMap K I (N i)

def inverseRelation (A B : Parameters K I) : GraphPolynomial K I :=
  X (.inr ()) * parameterMap K I (denominator K I A B) - 1

/-- Exactly the graph and inverse-denominator equations, with no Jacobian equation added. -/
def graphIdeal (A B : Parameters K I) (N : I → Parameters K I) : Ideal (GraphPolynomial K I) :=
  Ideal.span (Set.range (graphRelation K I A N) ∪ {inverseRelation K I A B})

abbrev GraphRing (A B : Parameters K I) (N : I → Parameters K I) :=
  GraphPolynomial K I ⧸ graphIdeal K I A B N

def graphMk (A B : Parameters K I) (N : I → Parameters K I) :
    GraphPolynomial K I →ₐ[K] GraphRing K I A B N :=
  Ideal.Quotient.mkₐ K (graphIdeal K I A B N)

def parameterToGraph (A B : Parameters K I) (N : I → Parameters K I) :
    Parameters K I →ₐ[K] GraphRing K I A B N :=
  (graphMk K I A B N).comp (parameterMap K I)

def graphY (A B : Parameters K I) (N : I → Parameters K I) (i : I) : GraphRing K I A B N :=
  graphMk K I A B N (C (X i))

def graphU (A B : Parameters K I) (N : I → Parameters K I) : GraphRing K I A B N :=
  graphMk K I A B N (X (.inr ()))

theorem graph_equation (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    parameterToGraph K I A B N A * graphY K I A B N i = parameterToGraph K I A B N (N i) := by
  have hm : graphRelation K I A N i ∈ graphIdeal K I A B N :=
    Ideal.subset_span (Or.inl (Set.mem_range_self i))
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  change graphMk K I A B N (graphRelation K I A N i) = 0 at hz
  simpa only [graphRelation, map_sub, map_mul, sub_eq_zero, parameterToGraph,
    AlgHom.comp_apply, graphY] using hz

theorem inverse_equation (A B : Parameters K I) (N : I → Parameters K I) :
    graphU K I A B N * parameterToGraph K I A B N (denominator K I A B) = 1 := by
  have hm : inverseRelation K I A B ∈ graphIdeal K I A B N :=
    Ideal.subset_span (Or.inr (Set.mem_singleton _))
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  change graphMk K I A B N (inverseRelation K I A B) = 0 at hz
  simpa only [inverseRelation, map_sub, map_mul, map_one, sub_eq_zero,
    parameterToGraph, AlgHom.comp_apply, graphU] using hz

theorem graph_denominator_isUnit (A B : Parameters K I) (N : I → Parameters K I) :
    IsUnit (parameterToGraph K I A B N (denominator K I A B)) := by
  refine ⟨⟨_, graphU K I A B N, ?_, inverse_equation K I A B N⟩, rfl⟩
  calc
    _ = graphU K I A B N * parameterToGraph K I A B N (denominator K I A B) :=
      mul_comm (parameterToGraph K I A B N (denominator K I A B)) (graphU K I A B N)
    _ = 1 := inverse_equation K I A B N

abbrev AwayRing (A B : Parameters K I) := Localization.Away (denominator K I A B)

def parameterToAway (A B : Parameters K I) : Parameters K I →ₐ[K] AwayRing K I A B :=
  IsScalarTower.toAlgHom K (Parameters K I) (AwayRing K I A B)

def inverseDenominator (A B : Parameters K I) : AwayRing K I A B :=
  IsLocalization.Away.invSelf (denominator K I A B)

theorem away_inverse_equation (A B : Parameters K I) :
    parameterToAway K I A B (denominator K I A B) * inverseDenominator K I A B = 1 :=
  IsLocalization.Away.mul_invSelf (denominator K I A B)

/-- This is the actual localized fraction `N_i/A`, written using only the inverted product. -/
def localizedY (A B : Parameters K I) (N : I → Parameters K I) (i : I) : AwayRing K I A B :=
  parameterToAway K I A B (N i) * parameterToAway K I A B B * inverseDenominator K I A B

theorem away_A_inverse (A B : Parameters K I) :
    parameterToAway K I A B A *
      (parameterToAway K I A B B * inverseDenominator K I A B) = 1 := by
  calc
    _ = parameterToAway K I A B (denominator K I A B) * inverseDenominator K I A B := by
      simp only [denominator, map_mul]
      ring
    _ = 1 := away_inverse_equation K I A B

theorem localizedY_equation (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    parameterToAway K I A B A * localizedY K I A B N i = parameterToAway K I A B (N i) := by
  calc
    _ = parameterToAway K I A B (N i) *
      (parameterToAway K I A B A *
        (parameterToAway K I A B B * inverseDenominator K I A B)) := by
      unfold localizedY
      ring
    _ = _ := by rw [away_A_inverse, mul_one]

/-- The actual map on the coefficient ring sends each `Y_i` to `N_i/A`. -/
def coefficientMap (A B : Parameters K I) (N : I → Parameters K I) :
    Coefficients K I →ₐ[K] AwayRing K I A B := MvPolynomial.aeval (localizedY K I A B N)

@[simp] theorem coefficientMap_X (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    coefficientMap K I A B N (X i) = localizedY K I A B N i := by simp [coefficientMap]

def graphPolynomialToAway (A B : Parameters K I) (N : I → Parameters K I) :
    GraphPolynomial K I →ₐ[K] AwayRing K I A B :=
  MvPolynomial.aevalTower (coefficientMap K I A B N)
    (Sum.elim (fun i => parameterToAway K I A B (X i)) (fun _ => inverseDenominator K I A B))

@[simp] theorem graphPolynomialToAway_C (A B : Parameters K I) (N : I → Parameters K I)
    (r : Coefficients K I) : graphPolynomialToAway K I A B N (C r) = coefficientMap K I A B N r := by
  simp [graphPolynomialToAway]

@[simp] theorem graphPolynomialToAway_T (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    graphPolynomialToAway K I A B N (X (.inl i)) = parameterToAway K I A B (X i) := by
  simp [graphPolynomialToAway]

@[simp] theorem graphPolynomialToAway_U (A B : Parameters K I) (N : I → Parameters K I) :
    graphPolynomialToAway K I A B N (X (.inr ())) = inverseDenominator K I A B := by
  simp [graphPolynomialToAway]

@[simp] theorem graphPolynomialToAway_parameterMap (A B : Parameters K I)
    (N : I → Parameters K I) (p : Parameters K I) :
    graphPolynomialToAway K I A B N (parameterMap K I p) = parameterToAway K I A B p := by
  have h : (graphPolynomialToAway K I A B N).comp (parameterMap K I) = parameterToAway K I A B := by
    ext i
    simp
  exact DFunLike.congr_fun h p

theorem graphIdeal_le_ker (A B : Parameters K I) (N : I → Parameters K I) :
    graphIdeal K I A B N ≤ RingHom.ker (graphPolynomialToAway K I A B N) := by
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | hp)
  · change graphPolynomialToAway K I A B N (graphRelation K I A N i) = 0
    simp only [graphRelation, map_sub, map_mul, graphPolynomialToAway_parameterMap,
      graphPolynomialToAway_C, coefficientMap_X, localizedY_equation, sub_self]
  · rcases Set.mem_singleton_iff.mp hp with rfl
    change graphPolynomialToAway K I A B N (inverseRelation K I A B) = 0
    simp only [inverseRelation, map_sub, map_mul, map_one, graphPolynomialToAway_U,
      graphPolynomialToAway_parameterMap]
    rw [mul_comm, away_inverse_equation, sub_self]

def graphToAway (A B : Parameters K I) (N : I → Parameters K I) :
    GraphRing K I A B N →ₐ[K] AwayRing K I A B :=
  Ideal.Quotient.liftₐ (graphIdeal K I A B N) (graphPolynomialToAway K I A B N)
    (fun _p hp => graphIdeal_le_ker K I A B N hp)

@[simp] theorem graphToAway_mk (A B : Parameters K I) (N : I → Parameters K I)
    (p : GraphPolynomial K I) :
    graphToAway K I A B N (graphMk K I A B N p) = graphPolynomialToAway K I A B N p := rfl

/-- The inverse-denominator equation gives the canonical map back from the actual localization. -/
def awayToGraph (A B : Parameters K I) (N : I → Parameters K I) :
    AwayRing K I A B →ₐ[K] GraphRing K I A B N :=
  IsLocalization.Away.liftAlgHom (A := K) (R := Parameters K I)
    (P := GraphRing K I A B N) (f := parameterToGraph K I A B N) (S := AwayRing K I A B)
    (denominator K I A B) (graph_denominator_isUnit K I A B N)

@[simp] theorem awayToGraph_parameter (A B : Parameters K I) (N : I → Parameters K I)
    (p : Parameters K I) :
    awayToGraph K I A B N (parameterToAway K I A B p) = parameterToGraph K I A B N p := by
  simp only [awayToGraph, IsLocalization.Away.coe_liftAlgHom,
    parameterToAway, IsScalarTower.toAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

@[simp] theorem awayToGraph_inverseDenominator (A B : Parameters K I) (N : I → Parameters K I) :
    awayToGraph K I A B N (inverseDenominator K I A B) = graphU K I A B N := by
  have hleft : parameterToGraph K I A B N (denominator K I A B) *
      awayToGraph K I A B N (inverseDenominator K I A B) = 1 := by
    simpa only [map_mul, map_one, awayToGraph_parameter] using
      congrArg (awayToGraph K I A B N) (away_inverse_equation K I A B)
  calc
    _ = 1 * awayToGraph K I A B N (inverseDenominator K I A B) := (one_mul _).symm
    _ = (graphU K I A B N * parameterToGraph K I A B N (denominator K I A B)) *
        awayToGraph K I A B N (inverseDenominator K I A B) := by rw [inverse_equation]
    _ = graphU K I A B N := by rw [mul_assoc, hleft, mul_one]

theorem graphY_reconstruction (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    parameterToGraph K I A B N (N i) * parameterToGraph K I A B N B * graphU K I A B N =
      graphY K I A B N i := by
  rw [← graph_equation K I A B N i]
  calc
    _ = graphY K I A B N i *
        (graphU K I A B N * parameterToGraph K I A B N (denominator K I A B)) := by
      simp only [denominator, map_mul]
      ring
    _ = _ := by rw [inverse_equation, mul_one]

@[simp] theorem awayToGraph_localizedY (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    awayToGraph K I A B N (localizedY K I A B N i) = graphY K I A B N i := by
  simp only [localizedY, map_mul, awayToGraph_parameter,
    awayToGraph_inverseDenominator, graphY_reconstruction]

def coefficientToGraph (A B : Parameters K I) (N : I → Parameters K I) :
    Coefficients K I →ₐ[K] GraphRing K I A B N :=
  (graphMk K I A B N).comp (IsScalarTower.toAlgHom K (Coefficients K I) (GraphPolynomial K I))

@[simp] theorem coefficientToGraph_apply (A B : Parameters K I) (N : I → Parameters K I)
    (r : Coefficients K I) : coefficientToGraph K I A B N r = graphMk K I A B N (C r) := rfl

@[simp] theorem awayToGraph_coefficientMap (A B : Parameters K I) (N : I → Parameters K I)
    (r : Coefficients K I) :
    awayToGraph K I A B N (coefficientMap K I A B N r) = coefficientToGraph K I A B N r := by
  have h : (awayToGraph K I A B N).comp (coefficientMap K I A B N) = coefficientToGraph K I A B N := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [graphY]
  exact DFunLike.congr_fun h r

theorem awayToGraph_graphToAway (A B : Parameters K I) (N : I → Parameters K I) :
    (awayToGraph K I A B N).comp (graphToAway K I A B N) =
      AlgHom.id K (GraphRing K I A B N) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext' (R := K) (σ := I ⊕ Unit)
    (A := Coefficients K I) (B := GraphRing K I A B N)
  · apply MvPolynomial.algHom_ext
    intro i
    change awayToGraph K I A B N
      (graphToAway K I A B N (graphMk K I A B N (C (X i)))) = graphMk K I A B N (C (X i))
    rw [graphToAway_mk, graphPolynomialToAway_C, coefficientMap_X, awayToGraph_localizedY]
    rfl
  · intro i
    rcases i with i | u
    · change awayToGraph K I A B N
        (graphToAway K I A B N (graphMk K I A B N (X (.inl i)))) = graphMk K I A B N (X (.inl i))
      simp only [graphToAway_mk, graphPolynomialToAway_T, awayToGraph_parameter,
        parameterToGraph, AlgHom.comp_apply, parameterMap_X]
    · cases u
      change awayToGraph K I A B N
        (graphToAway K I A B N (graphMk K I A B N (X (.inr ())))) = graphU K I A B N
      simp only [graphToAway_mk, graphPolynomialToAway_U, awayToGraph_inverseDenominator]

theorem graphToAway_awayToGraph (A B : Parameters K I) (N : I → Parameters K I) :
    (graphToAway K I A B N).comp (awayToGraph K I A B N) = AlgHom.id K (AwayRing K I A B) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denominator K I A B))
  apply MvPolynomial.algHom_ext
  intro i
  change graphToAway K I A B N
    (awayToGraph K I A B N (parameterToAway K I A B (X i))) = parameterToAway K I A B (X i)
  simp only [awayToGraph_parameter, parameterToGraph, AlgHom.comp_apply,
    graphToAway_mk, graphPolynomialToAway_parameterMap]

/-- The genuine graph quotient is the actual localization away from `B*A`. -/
def graphAwayEquiv (A B : Parameters K I) (N : I → Parameters K I) :
    GraphRing K I A B N ≃ₐ[K] AwayRing K I A B :=
  AlgEquiv.ofAlgHom (graphToAway K I A B N) (awayToGraph K I A B N)
    (graphToAway_awayToGraph K I A B N) (awayToGraph_graphToAway K I A B N)

@[simp] theorem graphAwayEquiv_apply (A B : Parameters K I) (N : I → Parameters K I)
    (x : GraphRing K I A B N) : graphAwayEquiv K I A B N x = graphToAway K I A B N x := rfl

@[simp] theorem graphAwayEquiv_symm_apply (A B : Parameters K I) (N : I → Parameters K I)
    (x : AwayRing K I A B) : (graphAwayEquiv K I A B N).symm x = awayToGraph K I A B N x := rfl

@[simp] theorem graphAwayEquiv_parameter (A B : Parameters K I) (N : I → Parameters K I)
    (p : Parameters K I) :
    graphAwayEquiv K I A B N (parameterToGraph K I A B N p) = parameterToAway K I A B p := by
  simp only [graphAwayEquiv_apply, parameterToGraph, AlgHom.comp_apply,
    graphToAway_mk, graphPolynomialToAway_parameterMap]

@[simp] theorem graphAwayEquiv_Y (A B : Parameters K I) (N : I → Parameters K I) (i : I) :
    graphAwayEquiv K I A B N (graphY K I A B N i) = localizedY K I A B N i := by
  simp only [graphAwayEquiv_apply, graphY, graphToAway_mk, graphPolynomialToAway_C, coefficientMap_X]

@[simp] theorem graphAwayEquiv_U (A B : Parameters K I) (N : I → Parameters K I) :
    graphAwayEquiv K I A B N (graphU K I A B N) = inverseDenominator K I A B := by
  simp only [graphAwayEquiv_apply, graphU, graphToAway_mk, graphPolynomialToAway_U]

/-- Exact compatibility with the original `Y` coefficient ring. -/
theorem graphAwayEquiv_coefficient (A B : Parameters K I) (N : I → Parameters K I)
    (r : Coefficients K I) :
    graphAwayEquiv K I A B N (algebraMap (Coefficients K I) (GraphRing K I A B N) r) =
      coefficientMap K I A B N r := by
  change graphAwayEquiv K I A B N (graphMk K I A B N (C r)) = _
  simp only [graphAwayEquiv_apply, graphToAway_mk, graphPolynomialToAway_C]

/-- The coefficient-ring algebra structure is given by `Y_i ↦ N_i/A`, rather than by `T_i`. -/
@[instance_reducible] def coefficientAlgebra (A B : Parameters K I) (N : I → Parameters K I) :
    Algebra (Coefficients K I) (AwayRing K I A B) := (coefficientMap K I A B N).toRingHom.toAlgebra

/-- The same actual equivalence as an equivalence over the graph's coefficient ring. -/
def graphAwayEquivOverCoefficients (A B : Parameters K I) (N : I → Parameters K I) :
    letI := coefficientAlgebra K I A B N
    GraphRing K I A B N ≃ₐ[Coefficients K I] AwayRing K I A B := by
  letI := coefficientAlgebra K I A B N
  exact
    { (graphAwayEquiv K I A B N).toRingEquiv with
      commutes' := fun r => graphAwayEquiv_coefficient K I A B N r }

/-- The parameter-polynomial algebra structure uses the `T` coordinates of the graph. -/
@[instance_reducible] def parameterAlgebra (A B : Parameters K I) (N : I → Parameters K I) :
    Algebra (Parameters K I) (GraphRing K I A B N) :=
  RingHom.toAlgebra (R := Parameters K I) (S := GraphRing K I A B N)
    (parameterToGraph K I A B N).toRingHom

def graphAwayEquivOverParameters (A B : Parameters K I) (N : I → Parameters K I) :
    letI := parameterAlgebra K I A B N
    GraphRing K I A B N ≃ₐ[Parameters K I] AwayRing K I A B := by
  letI := parameterAlgebra K I A B N
  exact
    { (graphAwayEquiv K I A B N).toRingEquiv with
      commutes' := fun p => by
        change graphAwayEquiv K I A B N (parameterToGraph K I A B N p) = parameterToAway K I A B p
        exact graphAwayEquiv_parameter K I A B N p }

/-- The quotient satisfies the genuine localization universal property over its parameters. -/
theorem graphRing_isLocalization (A B : Parameters K I) (N : I → Parameters K I) :
    letI := parameterAlgebra K I A B N
    IsLocalization (Submonoid.powers (denominator K I A B)) (GraphRing K I A B N) := by
  let := parameterAlgebra K I A B N
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (denominator K I A B)) (graphAwayEquivOverParameters K I A B N).symm

section Thirteen

/-- The actual denominator in the thirteen-parameter Gauss chart is `T₀*A`. -/
@[simp] theorem denominator_thirteen (A : Parameters K (Fin 13)) :
    denominator K (Fin 13) A (X 0) = X 0 * A := rfl

def gaussGraphEquiv (A : Parameters K (Fin 13)) (N : Fin 13 → Parameters K (Fin 13)) :
    GraphRing K (Fin 13) A (X 0) N ≃ₐ[K] Localization.Away (X 0 * A) :=
  graphAwayEquiv K (Fin 13) A (X 0) N

end Thirteen

end M9.GaussGraphQuotient
