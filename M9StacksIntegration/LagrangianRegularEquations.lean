module

public import M9StacksIntegration.LagrangianSkewCoordinates
public import StacksFrontier.RingTheory.MvPolynomial.MonicSequenceRegular

/-!
# Regularity of the original three LG matrix-chart equations

The full polynomial-coordinate isomorphism sends the actual skew
equations to three distinct polynomial variables. The native monic
sequence theorem gives weak regularity, and the actual nontrivial
symmetric quotient gives regularity. No lci or codimension premise is
used to derive these properties of the original literal equations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace M9Native.LagrangianDegree

open M9Native.LagrangianMatrixChart RingTheory.Sequence

variable (R : Type u) [CommRing R]

/-- The literal three equations, not replacement defining equations,
form a weakly regular sequence in the original nine-variable ring. -/
theorem threeEquations_isWeaklyRegular :
    IsWeaklyRegular (MatrixRing R) (List.ofFn (threeEquations R)) := by
  have hx : IsWeaklyRegular (SkewPolynomialRing R)
      (List.ofFn (fun i : Fin 3 => (MvPolynomial.X i : SkewPolynomialRing R))) := by
    simpa using MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic 3
      (fun _ : Fin 3 => (Polynomial.X : Polynomial (SymmetricRing R)))
      (fun _ => Polynomial.monic_X)
  have hc : List.Forall₂
      (fun (r : MatrixRing R) (s : SkewPolynomialRing R) =>
        ∀ x, matrixSkewCoordinates R (r • x) = s • matrixSkewCoordinates R x)
      (List.ofFn (threeEquations R))
      ((List.ofFn (threeEquations R)).map (matrixSkewCoordinates R)) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x => (matrixSkewCoordinates R).map_mul r x))
  apply (AddEquiv.isWeaklyRegular_congr
    (R := MatrixRing R) (S := SkewPolynomialRing R)
    (e := (matrixSkewCoordinates R).toAddEquiv) hc).mpr
  simpa only [List.map_ofFn, Function.comp_def, matrixSkewCoordinates_threeEquations] using hx

theorem ofList_threeEquations :
    Ideal.ofList (List.ofFn (threeEquations R)) = symmetryIdeal R := by
  rw [symmetryIdeal_eq_three]
  exact congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn.trans Set.mem_range.symm)

/-- The original three equations form a regular sequence whenever the
original coefficient ring is nontrivial. -/
theorem threeEquations_isRegular [Nontrivial R] :
    IsRegular (MatrixRing R) (List.ofFn (threeEquations R)) := by
  refine ⟨threeEquations_isWeaklyRegular R, ?_⟩
  intro htop
  apply symmetryIdeal_ne_top R
  rw [← ofList_threeEquations R]
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using htop.symm

/-- Actual flat pullback preserves the original three equations as a
weakly regular sequence, including their images in local chart rings. -/
theorem threeEquations_flat_isWeaklyRegular
    (S : Type v) [CommRing S] [Algebra (MatrixRing R) S]
    [Module.Flat (MatrixRing R) S] :
    IsWeaklyRegular S
      (List.ofFn (fun i => algebraMap (MatrixRing R) S (threeEquations R i))) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    (threeEquations_isWeaklyRegular R).map_algebraMap_of_flat (T := S)

end M9Native.LagrangianDegree
