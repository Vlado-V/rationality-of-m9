module

public import M9StacksIntegration.BoundedPencilTargetPolarization
public import M9StacksIntegration.GenusNineGraphPolarization
public import M9StacksIntegration.GenusNineTricanonicalEmbedding

/-! The five actual graph-polynomial possibilities for nonconstant maps
of degree at most five from an original smooth proper genus-nine curve.
The index is obtained from positivity of native function-field degree.
No finite-type or Hurwitz-space hypothesis enters this calculation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.BoundedPencilGraphPolynomial
open PencilProjectiveLineGeometry BoundedPencilTargetPolarization
attribute [local instance] isCurve_projectiveSpaceOver_one

def graphPolynomial (d : ℕ) (m : ℤ) : ℤ := (48 + (d : ℤ)) * m - 8

def graphNumericalPolynomial (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (48 + (d : ℚ)) * Polynomial.X - Polynomial.C 8

theorem graphNumericalPolynomial_eval (d : ℕ) (m : ℤ) :
    (graphNumericalPolynomial d).eval (m : ℚ) = (graphPolynomial d m : ℚ) := by
  simp only [graphNumericalPolynomial, graphPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring

def degreeIndex (i : Fin 5) : ℕ := i.val + 1

theorem degreeIndex_bounds (i : Fin 5) : 1 ≤ degreeIndex i ∧ degreeIndex i ≤ 5 := by
  have := i.isLt
  dsimp only [degreeIndex]
  omega

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
variable (g : X ⟶ Line k) (hg : g ≫ toBase k = f)
variable (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y)

theorem actual_degree_positive : 0 < PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc := by
  obtain ⟨s⟩ := PencilDegreePullback.nonempty_pencil_of_curveMap f (toBase k)
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le (lineDimension k)
    g hg hnc (fixedLine k) (fixedLine_degree k) (fixedLine_h0_atLeast_two k)
  exact lt_of_lt_of_le (by decide : 0 < 1) (linearSeries_dimension_le_degree f s)

theorem actual_graph_polynomial (hgen : genus f = 9) (m : ℤ) :
    (∑ᶠ i : ℕ, (-1 : ℤ)^i *
      (Module.finrank k (cohomologyOverField k f
        (GenusNineGraphPolarization.graphTensorPower f g (fixedLine k) m) i) : ℤ)) =
      graphPolynomial (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc) m :=
  GenusNineGraphPolarization.graphTensorPower_euler f (toBase k) g hg (fixedLine k)
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le (lineDimension k)
    hgen hnc (fixedLine_degree k) m

theorem exists_actual_degree_index
    (hdeg : PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc ≤ 5) :
    ∃ i : Fin 5, PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc = degreeIndex i := by
  have hp := actual_degree_positive f g hg hnc
  let i : Fin 5 := ⟨PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc - 1, by omega⟩
  refine ⟨i, ?_⟩
  dsimp only [degreeIndex, i]
  omega

theorem exists_actual_graph_polynomial (hgen : genus f = 9)
    (hdeg : PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc ≤ 5) :
    ∃ i : Fin 5, ∀ m : ℤ,
      (∑ᶠ j : ℕ, (-1 : ℤ)^j *
        (Module.finrank k (cohomologyOverField k f
          (GenusNineGraphPolarization.graphTensorPower f g (fixedLine k) m) j) : ℤ)) =
        graphPolynomial (degreeIndex i) m := by
  obtain ⟨i, hi⟩ := exists_actual_degree_index f g hg hnc hdeg
  exact ⟨i, fun m => (actual_graph_polynomial f g hg hnc hgen m).trans
    (congrArg (fun d => graphPolynomial d m) hi)⟩

end M9Native.BoundedPencilGraphPolynomial
end
