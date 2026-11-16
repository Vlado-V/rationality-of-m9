module

public import M9.FrameHomFieldDescent
public import M9StacksIntegration.ConicRawGammaMatrices

/-! Literal raw tensor-evaluation coordinates on the original raw Hom field.
These bases are the original tensor-evaluation bases on both fibres, rather
than the invariant bases of the descended fibres. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Module MvPolynomial
open scoped Classical

namespace M9Native.FrameHomRawMatrixCoordinates

open M9.FrameBundleDescent M9.FrameBundleDescent.Standard
open M9.FrameHomFieldDescent M9.DeterminantFrameScalarExtension

abbrev Index := Fin 4 × Fin 4
abbrev PolynomialRing := MvPolynomial Index Ambient
abbrev MatrixField := FractionRing PolynomialRing

/-- The actual tensor-evaluation basis on either original raw fibre. -/
def rawBasis (side : Bool) : Basis (Fin 4) Ambient (ActualRaw side) :=
  Basis.ofEquivFun (rawCoordinates Ambient)

@[simp] theorem rawBasis_repr (side : Bool) (x : ActualRaw side) (i : Fin 4) :
    (rawBasis side).repr x i = rawCoordinates Ambient x i :=
  Basis.ofEquivFun_repr_apply _ x i

theorem rawBasis_apply (side : Bool) (j : Fin 4) :
    rawBasis side j = (rawCoordinates Ambient).symm (Pi.single j 1) :=
  congrFun (Basis.coe_ofEquivFun (rawCoordinates Ambient)) j

/-- All sixteen matrix coordinate functionals, in the literal raw bases. -/
def coordinateBasis : Basis Index Ambient RawDual :=
  M9.SemilinearHomCoordinates.coordinateBasis Ambient (ActualRaw false) (ActualRaw true)
    (rawBasis false) (rawBasis true)

theorem coordinateBasis_apply (ij : Index) (h : RawHom) :
    coordinateBasis ij h =
      rawCoordinates Ambient (h ((rawCoordinates Ambient).symm (Pi.single ij.2 1))) ij.1 := by
  have hcoord := M9.SemilinearHomCoordinates.coordinateBasis_apply Ambient
    (ActualRaw false) (ActualRaw true) (rawBasis false) (rawBasis true) ij h
  change coordinateBasis ij h = LinearMap.toMatrix (rawBasis false) (rawBasis true) h ij.1 ij.2 at hcoord
  rw [LinearMap.toMatrix_apply] at hcoord
  calc
    coordinateBasis ij h = (rawBasis true).repr (h (rawBasis false ij.2)) ij.1 := hcoord
    _ = rawCoordinates Ambient (h (rawBasis false ij.2)) ij.1 := rawBasis_repr true _ _
    _ = _ := congrArg (fun v => rawCoordinates Ambient (h v) ij.1) (rawBasis_apply false ij.2)

def polynomialEquiv : PolynomialRing ≃ₐ[Ambient] RawRing :=
  (SymmetricAlgebra.equivMvPolynomial coordinateBasis).symm

@[simp] theorem polynomialEquiv_X (ij : Index) :
    polynomialEquiv (X ij) = SymmetricAlgebra.ι Ambient RawDual (coordinateBasis ij) :=
  SymmetricAlgebra.equivMvPolynomial_symm_X coordinateBasis ij

/-- Honest fraction-field coordinates on the original raw Hom field. -/
def fieldEquiv : MatrixField ≃ₐ[Ambient] RawField :=
  IsFractionRing.algEquivOfAlgEquiv polynomialEquiv

theorem fieldEquiv_polynomial (p : PolynomialRing) :
    fieldEquiv (algebraMap PolynomialRing MatrixField p) =
      algebraMap RawRing RawField (polynomialEquiv p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

/-- Every variable maps to its actual original degree-one matrix functional. -/
theorem fieldEquiv_X (ij : Index) :
    fieldEquiv (algebraMap PolynomialRing MatrixField (X ij)) =
      algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (coordinateBasis ij)) := by
  rw [fieldEquiv_polynomial,polynomialEquiv_X]

@[simp] theorem fieldEquiv_constant (a : Ambient) :
    fieldEquiv (algebraMap Ambient MatrixField a) = algebraMap Ambient RawField a :=
  fieldEquiv.commutes a

def rawMatrix : Matrix (Fin 4) (Fin 4) RawField := fun i j =>
  algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (coordinateBasis (i,j)))

theorem fieldEquiv_matrix (i j : Fin 4) :
    fieldEquiv (algebraMap PolynomialRing MatrixField (X (i,j))) = rawMatrix i j :=
  fieldEquiv_X (i,j)

end M9Native.FrameHomRawMatrixCoordinates
