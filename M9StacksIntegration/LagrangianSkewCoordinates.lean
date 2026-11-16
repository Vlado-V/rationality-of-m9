module

public import M9StacksIntegration.LagrangianMatrixChart

/-!
# Independent polynomial coordinates for the actual LG chart equations

The original nine matrix entries are identified with the six original
upper entries and the three original skew equations. Thus the original
LG chart is cut out by three independent polynomial variables, not only
set-theoretically by three equations. This is the algebra input for the
actual regular-section/top-Chern comparison; no degree is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianMatrixChart

variable (R : Type u) [CommRing R]

abbrev SkewPolynomialRing := MvPolynomial (Fin 3) (SymmetricRing R)

/-- The lower entries occur in exactly the order of the original
threeEquations: (1,0), (2,0), (2,1). -/
def lowerIndex (p : Entry) : Fin 3 :=
  if p = (1,0) then 0 else if p = (2,0) then 1 else 2

/-- Upper entries remain original coefficient variables, while a lower
entry is its upper partner plus its original skew coefficient. -/
def splitEntry (p : ULift.{u} Entry) : SkewPolynomialRing R :=
  MvPolynomial.C (MvPolynomial.X (ULift.up (symmetricIndex p.down))) +
    if p.down.1 ≤ p.down.2 then 0 else MvPolynomial.X (lowerIndex p.down)

def toSkew : MatrixRing R →+* SkewPolynomialRing R :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (splitEntry R)

/-- Reconstruct all original entries from the original upper entries
and the literal original three skew equations. -/
def fromSkew : SkewPolynomialRing R →+* MatrixRing R :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.rename (fun p : ULift.{u} SymmetricEntry => ULift.up p.down.val)).toRingHom
    (threeEquations R)

theorem toSkew_threeEquations (i : Fin 3) :
    toSkew R (threeEquations R i) = MvPolynomial.X i := by
  fin_cases i <;>
    simp [toSkew, threeEquations, skewEntry, splitEntry, symmetricIndex, lowerIndex]

theorem fromSkew_comp_toSkew :
    (fromSkew R).comp (toSkew R) = RingHom.id (MatrixRing R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toSkew, fromSkew]
  · rintro ⟨⟨i,j⟩⟩
    fin_cases i <;> fin_cases j <;>
      simp [toSkew, fromSkew, splitEntry, symmetricIndex, lowerIndex, threeEquations, skewEntry]

theorem toSkew_comp_fromSkew :
    (toSkew R).comp (fromSkew R) = RingHom.id (SkewPolynomialRing R) := by
  have hcoeff : (toSkew R).comp
      (MvPolynomial.rename
        (fun p : ULift.{u} SymmetricEntry => ULift.up p.down.val)).toRingHom =
        (MvPolynomial.C : SymmetricRing R →+* SkewPolynomialRing R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [toSkew]
    · intro p
      simp [toSkew, splitEntry, p.down.property]
  apply MvPolynomial.ringHom_ext
  · intro p
    simpa [fromSkew] using RingHom.congr_fun hcoeff p
  · intro i
    simpa [fromSkew] using toSkew_threeEquations R i

/-- An actual polynomial-ring equivalence taking the actual three
equations to the actual three independent polynomial variables. -/
def matrixSkewCoordinates : MatrixRing R ≃+* SkewPolynomialRing R where
  toFun := toSkew R
  invFun := fromSkew R
  left_inv p := RingHom.congr_fun (fromSkew_comp_toSkew R) p
  right_inv p := RingHom.congr_fun (toSkew_comp_fromSkew R) p
  map_mul' := (toSkew R).map_mul
  map_add' := (toSkew R).map_add

@[simp] theorem matrixSkewCoordinates_threeEquations (i : Fin 3) :
    matrixSkewCoordinates R (threeEquations R i) = MvPolynomial.X i :=
  toSkew_threeEquations R i

/-- The actual symmetry ideal becomes exactly the independent-variable
ideal under the actual full matrix-coordinate isomorphism. -/
theorem map_symmetryIdeal :
    Ideal.map (matrixSkewCoordinates R).toRingHom (symmetryIdeal R) =
      Ideal.span (Set.range (fun i : Fin 3 =>
        (MvPolynomial.X i : SkewPolynomialRing R))) := by
  rw [symmetryIdeal_eq_three, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact matrixSkewCoordinates_threeEquations R i

theorem symmetryIdeal_ne_top [Nontrivial R] : symmetryIdeal R ≠ ⊤ := by
  intro h
  have h1 := symmetryIdeal_le_ker R (show (1 : MatrixRing R) ∈ symmetryIdeal R by
    simp [h])
  change symmetrize R 1 = 0 at h1
  simpa using h1

end M9Native.LagrangianDegree
