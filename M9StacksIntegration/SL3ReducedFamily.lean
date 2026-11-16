module

public import M9StacksIntegration.SL3SymmetricCoordinates
public import M9StacksIntegration.ReducedGraphAction

@[expose] public section

/-! An actual twelve-coordinate family over every commutative ring.
Its field specialization is the original reduced primitive representation,
with the original symmetric-space dual and the frozen 4,2,4,2 coordinates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Matrix Module

namespace M9Native.SL3ReducedFamily

variable (R : Type) [CommRing R]

abbrev UpperSpace := M9.Upper3 → R
abbrev Mixed := UpperSpace R × Module.Dual R (UpperSpace R)

def split : UpperSpace R ≃ₗ[R] M9.GraphBundleDescent.Ambient R :=
  (LinearEquiv.funCongrLeft R R M9.GraphBundleDescent.upperSplitIndex.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R)

def splitBasis : Basis (Fin 4 ⊕ Fin 2) R (M9.GraphBundleDescent.Ambient R) :=
  (Pi.basisFun R _).map (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R)

def dualSplit : Module.Dual R (UpperSpace R) ≃ₗ[R] M9.GraphBundleDescent.Ambient R :=
  (split R).dualMap.symm.trans
    ((splitBasis R).dualBasis.equivFun.trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R))

def coordinates : Mixed R ≃ₗ[R] (Fin 12 → R) :=
  ((split R).prodCongr (dualSplit R)).trans GraphGrassmannianChart.ambientCoordinates

def mixedLinearEquiv (g : Matrix.SpecialLinearGroup (Fin 3) R) : Mixed R ≃ₗ[R] Mixed R :=
  (SL3SymmetricCoordinates.linearEquiv R g).prodCongr
    (SL3SymmetricCoordinates.linearEquiv R g⁻¹).dualMap

def coordinateLinearEquiv (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (Fin 12 → R) ≃ₗ[R] (Fin 12 → R) :=
  (coordinates R).symm.trans ((mixedLinearEquiv R g).trans (coordinates R))

def coordinateGL : ((Fin 12 → R) ≃ₗ[R] (Fin 12 → R)) ≃*
    Matrix.GeneralLinearGroup (Fin 12) R :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin 12 → R)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def matrixGL (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.GeneralLinearGroup (Fin 12) R := coordinateGL R (coordinateLinearEquiv R g)

theorem matrixGL_mulVec (g : Matrix.SpecialLinearGroup (Fin 3) R) (v : Fin 12 → R) :
    (matrixGL R g).val *ᵥ v = coordinateLinearEquiv R g v := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (coordinateLinearEquiv R g))
  exact congrArg (fun f : LinearMap.GeneralLinearGroup R (Fin 12 → R) =>
    (f : Module.End R (Fin 12 → R)) v) h

section FieldComparison

variable (K : Type) [Field K]

def originalMixedEquiv : M9.PrimitiveTwistedReduced.DualMixed K ≃ₗ[K] Mixed K :=
  (M9.symmetric3Coordinates K).prodCongr (M9.symmetric3Coordinates K).symm.dualMap

theorem coordinates_original (z : M9.PrimitiveTwistedReduced.DualMixed K) :
    coordinates K (originalMixedEquiv K z) = ReducedGraphAction.actualCoordinates K z := by
  rfl

theorem mixedLinearEquiv_original (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (z : M9.PrimitiveTwistedReduced.DualMixed K) :
    mixedLinearEquiv K g (originalMixedEquiv K z) =
      originalMixedEquiv K (M9.PrimitiveBlockCoordinates.dualMixedAction K g z) := by
  apply Prod.ext
  · exact SL3SymmetricCoordinates.linearEquiv_fieldCoordinates K g z.1
  · apply LinearMap.ext
    intro v
    have h := SL3SymmetricCoordinates.linearEquiv_fieldCoordinates K g⁻¹
      ((M9.symmetric3Coordinates K).symm v)
    rw [(M9.symmetric3Coordinates K).apply_symm_apply] at h
    have hs := congrArg (M9.symmetric3Coordinates K).symm h
    rw [(M9.symmetric3Coordinates K).symm_apply_apply] at hs
    exact congrArg z.2 hs

theorem coordinateLinearEquiv_original (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (z : M9.PrimitiveTwistedReduced.DualMixed K) :
    coordinateLinearEquiv K g (ReducedGraphAction.actualCoordinates K z) =
      ReducedGraphAction.actualCoordinates K (M9.PrimitiveBlockCoordinates.dualMixedAction K g z) := by
  rw [← coordinates_original K z]
  change coordinates K (mixedLinearEquiv K g
    ((coordinates K).symm (coordinates K (originalMixedEquiv K z)))) = _
  rw [LinearEquiv.symm_apply_apply, mixedLinearEquiv_original, coordinates_original]

variable [CharZero K]

/-- The uniform commutative-ring family specializes to the literal frozen
native reduced representation, retaining its original dual and center. -/
theorem matrixGL_eq_original (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    matrixGL K g = ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inl g) := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := (ReducedGraphAction.actualCoordinates K).surjective v
  change (matrixGL K g).val *ᵥ ReducedGraphAction.actualCoordinates K z =
    (ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inl g)).val *ᵥ
      ReducedGraphAction.actualCoordinates K z
  rw [matrixGL_mulVec, coordinateLinearEquiv_original, ReducedGraphAction.matrixRepresentation_connected]

end FieldComparison

end M9Native.SL3ReducedFamily
