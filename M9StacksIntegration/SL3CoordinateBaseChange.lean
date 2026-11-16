module

public import M9StacksIntegration.SL3CoordinateRing
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Actual scalar extension of the determinant-one coordinate ring

The two maps are constructed by evaluating the literal universal
special-linear matrices. They are inverse on the actual matrix-entry
generators and on the scalar tensor factor. Thus actual scalar extension
is the actual determinant-one quotient over the extended ring, with its
original coordinates preserved. For every field extension it is a domain.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped TensorProduct

universe u v

namespace M9Native.SL3CoordinateBaseChange

open SL3CoordinateRing

section Basic

variable (K : Type u) (L : Type v) [CommRing K] [CommRing L] [Algebra K L]

abbrev BaseChanged := L ⊗[K] CoordinateRing K

def scalarMap : CoordinateRing K →ₐ[K] CoordinateRing L := evaluation K (universal L)

@[simp] theorem scalarMap_coordinate (i j : Index) :
    scalarMap K L (coordinate K i j) = coordinate L i j :=
  evaluation_coordinate K (universal L) i j

def coordinateInclusion : CoordinateRing K →ₐ[K] BaseChanged K L :=
  Algebra.TensorProduct.includeRight

def tensorPoint : Matrix.SpecialLinearGroup Index (BaseChanged K L) :=
  ⟨(coordinateInclusion K L).mapMatrix (universalMatrix K),by
    have h := RingHom.map_det (R := CoordinateRing K) (S := BaseChanged K L)
      (coordinateInclusion K L).toRingHom (universalMatrix K)
    rw [universalMatrix_det] at h
    exact h.symm.trans (show coordinateInclusion K L (1 : CoordinateRing K) = 1 from rfl)⟩

def forward : BaseChanged K L →ₐ[L] CoordinateRing L :=
  AlgHom.liftEquiv K L (CoordinateRing K) (CoordinateRing L) (scalarMap K L)

def backward : CoordinateRing L →ₐ[L] BaseChanged K L := evaluation L (tensorPoint K L)

@[simp] theorem forward_coordinate (i j : Index) :
    forward K L ((1 : L) ⊗ₜ[K] coordinate K i j) = coordinate L i j := by
  simpa only [forward,AlgHom.liftEquiv_tmul,one_smul] using scalarMap_coordinate K L i j

@[simp] theorem backward_coordinate (i j : Index) :
    backward K L (coordinate L i j) = (1 : L) ⊗ₜ[K] coordinate K i j :=
  evaluation_coordinate L (tensorPoint K L) i j

theorem forward_comp_backward :
    (forward K L).comp (backward K L) = AlgHom.id L (CoordinateRing L) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  change forward K L (backward K L (coordinate L ij.1 ij.2)) = coordinate L ij.1 ij.2
  rw [backward_coordinate,forward_coordinate]

theorem backward_comp_forward :
    (backward K L).comp (forward K L) = AlgHom.id L (BaseChanged K L) := by
  apply Algebra.TensorProduct.ext_ring
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  change backward K L (forward K L ((1 : L) ⊗ₜ[K] coordinate K ij.1 ij.2)) =
    (1 : L) ⊗ₜ[K] coordinate K ij.1 ij.2
  rw [forward_coordinate,backward_coordinate]

/-- Genuine coordinate-preserving base change, constructed from the actual universal matrices. -/
def baseChangeEquiv : BaseChanged K L ≃ₐ[L] CoordinateRing L :=
  AlgEquiv.ofAlgHom (forward K L) (backward K L)
    (forward_comp_backward K L) (backward_comp_forward K L)

@[simp] theorem baseChangeEquiv_coordinate (i j : Index) :
    baseChangeEquiv K L ((1 : L) ⊗ₜ[K] coordinate K i j) = coordinate L i j :=
  forward_coordinate K L i j

end Basic

section Fields

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The actual determinant-one coordinate ring remains a domain after every field extension. -/
instance baseChanged_isDomain : IsDomain (BaseChanged K L) :=
  (baseChangeEquiv K L).toRingEquiv.isDomain_iff.mpr (coordinateRing_isDomain L)

end Fields

end M9Native.SL3CoordinateBaseChange
