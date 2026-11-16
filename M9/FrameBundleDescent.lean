module

public import M9.FrameQuadraticExtension
public import M9.ScalarExtendedRepresentation
public import M9.PairedSemilinearCoordinates
public import M9.FrameInversionRationality
public import M9.StandardFourPlaneRepresentation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Rank-four descent and paired exchange for the actual finite frame action

The two actions are the coefficient action on the native projective function
field together with the first and second frame representations.  The spaces
over the connected invariant field are their actual fixed vectors.  Native
transpose on the coefficient factor exchanges them and supplies paired bases.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace M9.FrameBundleDescent

open Module
open scoped TensorProduct BigOperators

abbrev Ambient := FrameQuadraticExtension.Ambient
abbrev Gamma := TetrahedralGroup.Gamma
abbrev Even := FrameQuadraticExtension.Even
abbrev ConnectedField := FrameQuadraticExtension.connectedField
abbrev Four := Fin 4 → ℂ

local instance ambientEvenAction : MulSemiringAction Even Ambient := FrameQuadraticExtension.evenAction
local instance ambientEvenCommutes : SMulCommClass Even ℂ Ambient where
  smul_comm g c x := map_smul (FrameQuadraticExtension.evenRepresentation g).toLinearEquiv c x

local instance ambientEvenFaithful : FaithfulSMul Even Ambient where
  eq_of_smul_eq_smul {g h} heq := by
    have hr : FrameQuadraticExtension.evenRepresentation g = FrameQuadraticExtension.evenRepresentation h := by
      ext x
      exact heq x
    have hg := FrameProjectiveGeometry.fieldRepresentation_injective hr
    exact Prod.ext (congrArg FrameAction.FrameGroup.first hg) (congrArg FrameAction.FrameGroup.second hg)

def swapEven : Even ≃* Even := MulEquiv.prodComm

def nativeTranspose : Ambient ≃ₐ[ℂ] Ambient :=
  FrameProjectiveGeometry.fieldRepresentation FrameAction.FrameGroup.tau

theorem nativeTranspose_squared (x : Ambient) : nativeTranspose (nativeTranspose x) = x := by
  change FrameProjectiveGeometry.fieldRepresentation FrameAction.FrameGroup.tau
    (FrameProjectiveGeometry.fieldRepresentation FrameAction.FrameGroup.tau x) = x
  rw [← AlgEquiv.mul_apply, ← map_mul, FrameAction.FrameGroup.tau_squared, map_one]
  rfl

theorem nativeTranspose_even (g : Even) (x : Ambient) :
    nativeTranspose (g • x) = swapEven g • nativeTranspose x := by
  have hg : (FrameAction.FrameGroup.tau : FrameProjectiveGeometry.W) * FrameAction.FrameGroup.pairHom g =
      FrameAction.FrameGroup.pairHom (swapEven g) * FrameAction.FrameGroup.tau := by
    rcases g with ⟨a,b⟩
    change (⟨1,1,true⟩ : FrameProjectiveGeometry.W) * ⟨a,b,false⟩ = ⟨b,a,false⟩ * ⟨1,1,true⟩
    rw [FrameAction.FrameGroup.mul_odd, FrameAction.FrameGroup.mul_even]
    simp
  change FrameProjectiveGeometry.fieldRepresentation FrameAction.FrameGroup.tau
    (FrameProjectiveGeometry.fieldRepresentation (FrameAction.FrameGroup.pairHom g) x) =
      FrameProjectiveGeometry.fieldRepresentation (FrameAction.FrameGroup.pairHom (swapEven g))
        (FrameProjectiveGeometry.fieldRepresentation FrameAction.FrameGroup.tau x)
  rw [← AlgEquiv.mul_apply, ← map_mul, hg, map_mul, AlgEquiv.mul_apply]

section RepresentationDescent

variable (ρ : Gamma →* (Four ≃ₗ[ℂ] Four))

def sideFactor (side : Bool) : Even →* Gamma where
  toFun g := if side then g.2 else g.1
  map_one' := by cases side <;> rfl
  map_mul' g h := by cases side <;> rfl

def sideRepresentation (side : Bool) : Even →* (Four ≃ₗ[ℂ] Four) := ρ.comp (sideFactor side)

theorem sideRepresentation_swap (side : Bool) (g : Even) :
    sideRepresentation ρ (!side) (swapEven g) = sideRepresentation ρ side g := by
  cases side <;> rfl

/-- A named carrier keeps the two genuine semilinear actions distinct. -/
def Raw (_representation : Gamma →* (Four ≃ₗ[ℂ] Four)) (_side : Bool) :=
  ScalarExtendedRepresentation.ScalarExtension ℂ Ambient Four

instance rawAddCommGroup (side : Bool) : AddCommGroup (Raw ρ side) := by unfold Raw; infer_instance
instance rawModule (side : Bool) : Module Ambient (Raw ρ side) := by unfold Raw; infer_instance
instance rawBaseModule (side : Bool) : Module ℂ (Raw ρ side) := by unfold Raw; infer_instance
instance rawFinite (side : Bool) : Module.Finite Ambient (Raw ρ side) := by unfold Raw; infer_instance

@[instance_reducible] instance rawAction (side : Bool) : DistribMulAction Even (Raw ρ side) :=
  ScalarExtendedRepresentation.tensorAction ℂ Ambient Even Four (sideRepresentation ρ side)

instance rawSemilinear (side : Bool) : SMulDistribClass Even Ambient (Raw ρ side) :=
  ScalarExtendedRepresentation.tensorSemilinear ℂ Ambient Even Four (sideRepresentation ρ side)

def rawTmul (side : Bool) (a : Ambient) (v : Four) : Raw ρ side := a ⊗ₜ[ℂ] v

theorem rawAction_tmul (side : Bool) (g : Even) (a : Ambient) (v : Four) :
    g • rawTmul ρ side a v =
      rawTmul ρ side (g • a) (sideRepresentation ρ side g v) := rfl

def rawBasis (side : Bool) : Basis (Fin 4) Ambient (Raw ρ side) :=
  ScalarExtendedRepresentation.scalarBasis ℂ Ambient Four (Pi.basisFun ℂ (Fin 4))

theorem finrank_raw (side : Bool) : finrank Ambient (Raw ρ side) = 4 := by
  rw [finrank_eq_card_basis (rawBasis ρ side), Fintype.card_fin]

/-- The descended rank-four space is the actual fixed-vector subspace. -/
def Descended (side : Bool) := ↥(FiniteGaloisDescent.fixedVectors Even Ambient (Raw ρ side))

instance descendedAddCommGroup (side : Bool) : AddCommGroup (Descended ρ side) := by
  unfold Descended
  infer_instance

instance descendedModule (side : Bool) : Module ConnectedField (Descended ρ side) :=
  inferInstanceAs (Module (FiniteGaloisDescent.FixedField Even Ambient)
    (FiniteGaloisDescent.fixedVectors Even Ambient (Raw ρ side)))

def descendedBasis (side : Bool) : Basis (Fin 4) ConnectedField (Descended ρ side) :=
  (FiniteGaloisDescent.descendedBasis Even Ambient (Raw ρ side)).reindex (finCongr (finrank_raw ρ side))

instance descendedFinite (side : Bool) : Module.Finite ConnectedField (Descended ρ side) :=
  (descendedBasis ρ side).finiteDimensional_of_finite

theorem finrank_descended (side : Bool) : finrank ConnectedField (Descended ρ side) = 4 := by
  rw [finrank_eq_card_basis (descendedBasis ρ side), Fintype.card_fin]

/-- The canonical multiplication map identifies scalar extension of the
actual descended space with the original semilinear module. -/
def descendedScalarExtension (side : Bool) :
    Ambient ⊗[ConnectedField] Descended ρ side ≃ₗ[Ambient] Raw ρ side :=
  FiniteGaloisDescent.scalarExtensionEquiv Even Ambient (Raw ρ side)

theorem descendedScalarExtension_tmul (side : Bool) (a : Ambient) (v : Descended ρ side) :
    descendedScalarExtension ρ side (a ⊗ₜ[ConnectedField] v) = a • v.val :=
  FiniteGaloisDescent.scalarExtensionEquiv_tmul Even Ambient (Raw ρ side) a v

/-- Native transpose acts on the actual coefficient tensor factor. -/
def rawTranspose (side : Bool) : Raw ρ side →ₗ[ℂ] Raw ρ (!side) :=
  TensorProduct.map nativeTranspose.toLinearMap (LinearMap.id : Four →ₗ[ℂ] Four)

theorem rawTranspose_tmul (side : Bool) (a : Ambient) (v : Four) :
    rawTranspose ρ side (rawTmul ρ side a v) = rawTmul ρ (!side) (nativeTranspose a) v := rfl

theorem rawTranspose_squared (side : Bool) (x : Raw ρ side) :
    rawTranspose ρ (!side) (rawTranspose ρ side x) = x := by
  change Ambient ⊗[ℂ] Four at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a v =>
    change rawTmul ρ side (nativeTranspose (nativeTranspose a)) v = rawTmul ρ side a v
    rw [nativeTranspose_squared]

theorem rawTranspose_smul (side : Bool) (a : Ambient) (x : Raw ρ side) :
    rawTranspose ρ side (a • x) = nativeTranspose a • rawTranspose ρ side x := by
  change Ambient ⊗[ℂ] Four at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul c v =>
    change rawTmul ρ (!side) (nativeTranspose (a*c)) v =
      rawTmul ρ (!side) (nativeTranspose a * nativeTranspose c) v
    rw [map_mul]

theorem rawTranspose_action (side : Bool) (g : Even) (x : Raw ρ side) :
    rawTranspose ρ side (g • x) = swapEven g • rawTranspose ρ side x := by
  change Ambient ⊗[ℂ] Four at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a v =>
    change rawTmul ρ (!side) (nativeTranspose (g • a)) (sideRepresentation ρ side g v) =
      rawTmul ρ (!side) (swapEven g • nativeTranspose a)
        (sideRepresentation ρ (!side) (swapEven g) v)
    rw [nativeTranspose_even, sideRepresentation_swap]

theorem rawTranspose_fixed (side : Bool) (x : Descended ρ side) :
    rawTranspose ρ side x.val ∈ FiniteGaloisDescent.fixedVectors Even Ambient (Raw ρ (!side)) := by
  intro g
  have h := rawTranspose_action ρ side (swapEven g) x.val
  change rawTranspose ρ side (swapEven g • x.val) = g • rawTranspose ρ side x.val at h
  rw [x.property (swapEven g)] at h
  exact h.symm

/-- Transpose supplies the exchange bijection of descended spaces. No
pairing or basis-exchange hypothesis is used to construct it. -/
def exchange : Descended ρ false ≃+ Descended ρ true where
  toFun x := ⟨rawTranspose ρ false x.val, rawTranspose_fixed ρ false x⟩
  invFun y := ⟨rawTranspose ρ true y.val, rawTranspose_fixed ρ true y⟩
  left_inv x := Subtype.ext (rawTranspose_squared ρ false x.val)
  right_inv y := Subtype.ext (rawTranspose_squared ρ true y.val)
  map_add' x y := Subtype.ext (map_add (rawTranspose ρ false) x.val y.val)

theorem exchange_semilinear :
    PairedSemilinearCoordinates.IsSemilinear FrameQuadraticExtension.exchange.toRingEquiv (exchange ρ) := by
  intro a x
  apply Subtype.ext
  change rawTranspose ρ false ((a : Ambient) • x.val) =
    (nativeTranspose (a : Ambient)) • rawTranspose ρ false x.val
  exact rawTranspose_smul ρ false a.val x.val

def pairedBasis : Basis (Fin 4) ConnectedField (Descended ρ true) :=
  PairedSemilinearCoordinates.pairedBasis FrameQuadraticExtension.exchange.toRingEquiv
    (exchange ρ) (exchange_semilinear ρ) (descendedBasis ρ false)

theorem pairedBasis_apply (i : Fin 4) : pairedBasis ρ i = exchange ρ (descendedBasis ρ false i) :=
  PairedSemilinearCoordinates.pairedBasis_apply FrameQuadraticExtension.exchange.toRingEquiv
    (exchange ρ) (exchange_semilinear ρ) (descendedBasis ρ false) i

theorem exchange_matrix_inverse (x : Descended ρ false ≃ₗ[ConnectedField] Descended ρ true) :
    LinearMap.toMatrix (descendedBasis ρ false) (pairedBasis ρ)
      (PairedSemilinearCoordinates.exchange FrameQuadraticExtension.exchange.toRingEquiv
        FrameQuadraticExtension.exchange_exchange (exchange ρ) (exchange_semilinear ρ) x).toLinearMap =
      ((LinearMap.toMatrix (descendedBasis ρ false) (pairedBasis ρ) x.toLinearMap)⁻¹).map
        FrameQuadraticExtension.exchange.toRingEquiv :=
  PairedSemilinearCoordinates.exchange_matrix_inverse FrameQuadraticExtension.exchange.toRingEquiv
    FrameQuadraticExtension.exchange_exchange (exchange ρ) (exchange_semilinear ρ) (descendedBasis ρ false) x

abbrev HomSpace := Descended ρ false →ₗ[ConnectedField] Descended ρ true
abbrev HomDual := Module.Dual ConnectedField (HomSpace ρ)
abbrev HomRing := SymmetricAlgebra ConnectedField (HomDual ρ)
abbrev HomField := FractionRing (HomRing ρ)

def homMatrixCoordinates : HomSpace ρ ≃ₗ[ConnectedField] Matrix (Fin 4) (Fin 4) ConnectedField :=
  LinearMap.toMatrix (descendedBasis ρ false) (pairedBasis ρ)

def homBasis : Basis (Fin 4 × Fin 4) ConnectedField (HomSpace ρ) :=
  (Matrix.stdBasis ConnectedField (Fin 4) (Fin 4)).map (homMatrixCoordinates ρ).symm

def homDualBasis : Basis (Fin 4 × Fin 4) ConnectedField (HomDual ρ) := (homBasis ρ).dualBasis

def homPolynomialCoordinates : HomRing ρ ≃ₐ[ConnectedField] CayleyField.Polynomial ConnectedField :=
  FiniteNoNameField.polynomialCoordinates ConnectedField (HomDual ρ) (homDualBasis ρ)

def homRationalCoordinates : HomField ρ ≃ₐ[ConnectedField] CayleyField.Rational ConnectedField :=
  FiniteNoNameField.rationalCoordinates ConnectedField (HomDual ρ) (homDualBasis ρ)

/-- The universal matrix entries are actual linear coordinate functions on
the space of maps between the two descended vector spaces. -/
def universalEntry (ij : Fin 4 × Fin 4) : HomRing ρ :=
  SymmetricAlgebra.ι ConnectedField (HomDual ρ) (homDualBasis ρ ij)

def universalMatrix : Matrix (Fin 4) (Fin 4) (HomRing ρ) := fun i j => universalEntry ρ (i,j)
def universalDeterminant : HomRing ρ := (universalMatrix ρ).det

theorem homDualBasis_apply (ij : Fin 4 × Fin 4) (f : HomSpace ρ) :
    homDualBasis ρ ij f = homMatrixCoordinates ρ f ij.1 ij.2 := by
  simp [homDualBasis, homBasis, Matrix.stdBasis]

def homEvaluation (f : HomSpace ρ) : HomRing ρ →ₐ[ConnectedField] ConnectedField :=
  SymmetricAlgebra.lift
    { toFun := fun l : HomDual ρ => l f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem homEvaluation_matrix (f : HomSpace ρ) :
    (universalMatrix ρ).map (homEvaluation ρ f).toRingHom = homMatrixCoordinates ρ f := by
  funext i j
  change homEvaluation ρ f (universalEntry ρ (i,j)) = _
  rw [homEvaluation, universalEntry, SymmetricAlgebra.lift_ι_apply]
  exact homDualBasis_apply ρ (i,j) f

theorem homPolynomialCoordinates_entry (ij : Fin 4 × Fin 4) :
    homPolynomialCoordinates ρ (universalEntry ρ ij) = MvPolynomial.X ij :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply (homDualBasis ρ) ij

theorem homPolynomialCoordinates_matrix :
    (universalMatrix ρ).map (homPolynomialCoordinates ρ).toRingHom =
      CayleyField.polynomialMatrix ConnectedField := by
  funext i j
  exact homPolynomialCoordinates_entry ρ (i,j)

theorem universalDeterminant_ne_zero : universalDeterminant ρ ≠ 0 := by
  intro h
  have hh := (homPolynomialCoordinates ρ).map_det (universalMatrix ρ)
  change homPolynomialCoordinates ρ (universalMatrix ρ).det =
    ((universalMatrix ρ).map (homPolynomialCoordinates ρ).toRingHom).det at hh
  rw [homPolynomialCoordinates_matrix] at hh
  change homPolynomialCoordinates ρ (universalDeterminant ρ) = _ at hh
  rw [h, map_zero] at hh
  exact CayleyField.polynomialMatrix_det_ne_zero ConnectedField hh.symm

/-- The actual isomorphism scheme coordinate ring is the principal open
in the symmetric coordinate ring of `Hom(E,F)` where its determinant is a unit. -/
abbrev IsomRing := Localization.Away (universalDeterminant ρ)

instance isomRingDomain : IsDomain (IsomRing ρ) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (IsomRing ρ)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (universalDeterminant_ne_zero ρ)))

abbrev IsomFunctionField := FractionRing (IsomRing ρ)

instance isomFunctionFieldConnectedAlgebra : Algebra ConnectedField (IsomFunctionField ρ) :=
  inferInstanceAs (Algebra ConnectedField (FractionRing (IsomRing ρ)))

instance isomFunctionFieldConnectedSMul : SMul ConnectedField (IsomFunctionField ρ) :=
  (isomFunctionFieldConnectedAlgebra ρ).toSMul

instance isomFunctionFieldRingTower : IsScalarTower ConnectedField (IsomRing ρ) (IsomFunctionField ρ) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def isomLocalizationToHomField : IsomRing ρ →ₐ[ConnectedField] HomField ρ :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom ConnectedField (HomRing ρ) (HomField ρ))
    (S := IsomRing ρ) (universalDeterminant ρ)
      (isUnit_iff_ne_zero.mpr (by
        change algebraMap (HomRing ρ) (HomField ρ) (universalDeterminant ρ) ≠ 0
        simpa only [map_zero] using (IsFractionRing.injective (HomRing ρ) (HomField ρ)).ne
          (universalDeterminant_ne_zero ρ)))

theorem isomLocalizationToHomField_polynomial (p : HomRing ρ) :
    isomLocalizationToHomField ρ (algebraMap (HomRing ρ) (IsomRing ρ) p) =
      algebraMap (HomRing ρ) (HomField ρ) p :=
  IsLocalization.Away.lift_eq (g := algebraMap (HomRing ρ) (HomField ρ))
    (S := IsomRing ρ) (universalDeterminant ρ)
      (isUnit_iff_ne_zero.mpr (by
        simpa only [map_zero] using (IsFractionRing.injective (HomRing ρ) (HomField ρ)).ne
          (universalDeterminant_ne_zero ρ))) p

instance isomLocalizationHomFieldAlgebra : Algebra (IsomRing ρ) (HomField ρ) :=
  (isomLocalizationToHomField ρ).toRingHom.toAlgebra

instance isomLocalizationHomFieldTower : IsScalarTower (HomRing ρ) (IsomRing ρ) (HomField ρ) :=
  IsScalarTower.of_algebraMap_eq fun p => (isomLocalizationToHomField_polynomial ρ p).symm

instance isomLocalizationBaseTower : IsScalarTower ConnectedField (IsomRing ρ) (HomField ρ) :=
  IsScalarTower.of_algebraMap_eq fun a => (isomLocalizationToHomField ρ).commutes a |>.symm

instance homFieldFractionIsomRing : IsFractionRing (IsomRing ρ) (HomField ρ) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (universalDeterminant ρ)) (IsomRing ρ) (HomField ρ)

def isomHomFieldEquiv : IsomFunctionField ρ ≃ₐ[ConnectedField] HomField ρ :=
  (IsLocalization.algEquiv (nonZeroDivisors (IsomRing ρ)) (IsomFunctionField ρ) (HomField ρ)).restrictScalars ConnectedField

/-- The native affine scheme of the determinant open in the actual Hom space. -/
abbrev isomScheme : AlgebraicGeometry.Scheme := AlgebraicGeometry.Spec (.of (IsomRing ρ))

instance isomSchemeIrreducible : IrreducibleSpace (isomScheme ρ) := by
  change IrreducibleSpace (AlgebraicGeometry.Spec (.of (IsomRing ρ)))
  infer_instance

abbrev NativeIsomFunctionField := (isomScheme ρ).functionField

instance nativeIsomRingAlgebra : Algebra (IsomRing ρ) (NativeIsomFunctionField ρ) :=
  ProjectiveFunctionField.affineFunctionField_ringAlgebra (IsomRing ρ)

instance nativeIsomFractionRing : IsFractionRing (IsomRing ρ) (NativeIsomFunctionField ρ) :=
  ProjectiveFunctionField.affineFunctionField_isFractionRing (IsomRing ρ)

instance nativeIsomConnectedAlgebra : Algebra ConnectedField (NativeIsomFunctionField ρ) :=
  ((algebraMap (IsomRing ρ) (NativeIsomFunctionField ρ)).comp (algebraMap ConnectedField (IsomRing ρ))).toAlgebra

instance nativeIsomScalarTower : IsScalarTower ConnectedField (IsomRing ρ) (NativeIsomFunctionField ρ) :=
  IsScalarTower.of_algebraMap_eq (R := ConnectedField) (S := IsomRing ρ) (A := NativeIsomFunctionField ρ) fun _ => rfl

/-- The actual native generic stalk of the isomorphism scheme is identified
with its fraction field by the affine fraction-ring theorem. -/
def nativeIsomFunctionFieldEquiv : NativeIsomFunctionField ρ ≃ₐ[ConnectedField] IsomFunctionField ρ :=
  (IsLocalization.algEquiv (nonZeroDivisors (IsomRing ρ))
    (NativeIsomFunctionField ρ) (IsomFunctionField ρ)).restrictScalars ConnectedField

/-- This equivalence is derived from symmetric-algebra coordinates on the
actual descended Hom space and localization at its determinant. -/
def isomAuxiliaryFieldEquiv :
    IsomFunctionField ρ ≃ₐ[ConnectedField] FrameInversionRationality.AuxiliaryField :=
  (isomHomFieldEquiv ρ).trans (homRationalCoordinates ρ)

def isomEntry (ij : Fin 4 × Fin 4) : IsomFunctionField ρ :=
  algebraMap (IsomRing ρ) (IsomFunctionField ρ)
    (algebraMap (HomRing ρ) (IsomRing ρ) (universalEntry ρ ij))

theorem isomAuxiliaryFieldEquiv_entry (ij : Fin 4 × Fin 4) :
    isomAuxiliaryFieldEquiv ρ (isomEntry ρ ij) = CayleyField.genericCoordinate ConnectedField ij := by
  change homRationalCoordinates ρ
    (isomHomFieldEquiv ρ (algebraMap (IsomRing ρ) (IsomFunctionField ρ)
      (algebraMap (HomRing ρ) (IsomRing ρ) (universalEntry ρ ij)))) = _
  have he (p : IsomRing ρ) :
      isomHomFieldEquiv ρ (algebraMap (IsomRing ρ) (IsomFunctionField ρ) p) =
        algebraMap (IsomRing ρ) (HomField ρ) p :=
    (IsLocalization.algEquiv (nonZeroDivisors (IsomRing ρ)) (IsomFunctionField ρ) (HomField ρ)).commutes p
  rw [he]
  change homRationalCoordinates ρ
    (isomLocalizationToHomField ρ (algebraMap (HomRing ρ) (IsomRing ρ) (universalEntry ρ ij))) = _
  rw [isomLocalizationToHomField_polynomial]
  change FiniteNoNameField.rationalCoordinates ConnectedField (HomDual ρ) (homDualBasis ρ)
    (algebraMap (HomRing ρ) (HomField ρ) (universalEntry ρ ij)) = _
  rw [FiniteNoNameField.rationalCoordinates_polynomial]
  exact congrArg (algebraMap (CayleyField.Polynomial ConnectedField) (CayleyField.Rational ConnectedField))
    (homPolynomialCoordinates_entry ρ ij)

def genericIsomMatrix : Matrix (Fin 4) (Fin 4) (IsomFunctionField ρ) := fun i j => isomEntry ρ (i,j)

theorem isomAuxiliaryFieldEquiv_matrix :
    (genericIsomMatrix ρ).map (isomAuxiliaryFieldEquiv ρ).toRingHom = CayleyField.genericMatrix ConnectedField := by
  funext i j
  exact isomAuxiliaryFieldEquiv_entry ρ (i,j)

theorem genericIsomMatrix_det_ne_zero : (genericIsomMatrix ρ).det ≠ 0 := by
  intro h
  have hh := (isomAuxiliaryFieldEquiv ρ).map_det (genericIsomMatrix ρ)
  change isomAuxiliaryFieldEquiv ρ (genericIsomMatrix ρ).det =
    ((genericIsomMatrix ρ).map (isomAuxiliaryFieldEquiv ρ).toRingHom).det at hh
  rw [isomAuxiliaryFieldEquiv_matrix, h, map_zero] at hh
  exact CayleyField.genericMatrix_det_ne_zero ConnectedField hh.symm

def matrixLinearEquiv (R : Type*) [CommRing R] :
    Matrix.GeneralLinearGroup (Fin 4) R ≃* ((Fin 4 → R) ≃ₗ[R] (Fin 4 → R)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin 4 → R))

/-- The generic point is an actual isomorphism of scalar extensions of the
two descended vector spaces. -/
def genericIsomorphism :
    (IsomFunctionField ρ ⊗[ConnectedField] Descended ρ false) ≃ₗ[IsomFunctionField ρ]
      (IsomFunctionField ρ ⊗[ConnectedField] Descended ρ true) :=
  ((descendedBasis ρ false).baseChange (IsomFunctionField ρ)).equivFun.trans
    ((matrixLinearEquiv (IsomFunctionField ρ)
      (Matrix.GeneralLinearGroup.mk'' (genericIsomMatrix ρ)
        (isUnit_iff_ne_zero.mpr (genericIsomMatrix_det_ne_zero ρ)))).trans
          ((pairedBasis ρ).baseChange (IsomFunctionField ρ)).equivFun.symm)

def isomInversion : IsomFunctionField ρ ≃+* IsomFunctionField ρ :=
  (isomAuxiliaryFieldEquiv ρ).toRingEquiv.trans
    (FrameInversionRationality.inversion.trans (isomAuxiliaryFieldEquiv ρ).symm.toRingEquiv)

theorem isomInversion_apply (x : IsomFunctionField ρ) :
    isomInversion ρ x = (isomAuxiliaryFieldEquiv ρ).symm
      (FrameInversionRationality.inversion (isomAuxiliaryFieldEquiv ρ x)) := rfl

theorem isomInversion_involutive : Function.Involutive (isomInversion ρ) := by
  intro x
  rw [isomInversion_apply, isomInversion_apply, AlgEquiv.apply_symm_apply,
    FrameInversionRationality.inversion_involutive, AlgEquiv.symm_apply_apply]

theorem isomInversion_coefficient (a : ConnectedField) :
    isomInversion ρ (algebraMap ConnectedField (IsomFunctionField ρ) a) =
      algebraMap ConnectedField (IsomFunctionField ρ) (FrameQuadraticExtension.exchange a) := by
  rw [isomInversion_apply, (isomAuxiliaryFieldEquiv ρ).commutes,
    FrameInversionRationality.inversion_constant, (isomAuxiliaryFieldEquiv ρ).symm.commutes]

theorem isomAuxiliaryFieldEquiv_inversion (x : IsomFunctionField ρ) :
    isomAuxiliaryFieldEquiv ρ (isomInversion ρ x) =
      FrameInversionRationality.inversion (isomAuxiliaryFieldEquiv ρ x) := by
  rw [isomInversion_apply, AlgEquiv.apply_symm_apply]

theorem isomFieldHom_ext {A : Type*} [Field A] (f g : IsomFunctionField ρ →+* A)
    (hc : ∀ a : ConnectedField, f (algebraMap ConnectedField (IsomFunctionField ρ) a) =
      g (algebraMap ConnectedField (IsomFunctionField ρ) a))
    (hX : ∀ ij : Fin 4 × Fin 4, f (isomEntry ρ ij) = g (isomEntry ρ ij)) : f = g := by
  let e := isomAuxiliaryFieldEquiv ρ
  have hh : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := by
    apply CayleyFixedField.rationalHom_ext ConnectedField
    · intro a
      change f (e.symm (algebraMap ConnectedField (CayleyField.Rational ConnectedField) a)) =
        g (e.symm (algebraMap ConnectedField (CayleyField.Rational ConnectedField) a))
      rw [e.symm.commutes]
      exact hc a
    · intro ij
      have he : e.symm (CayleyField.genericCoordinate ConnectedField ij) = isomEntry ρ ij := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply]
        exact (isomAuxiliaryFieldEquiv_entry ρ ij).symm
      change f (e.symm (CayleyField.genericCoordinate ConnectedField ij)) =
        g (e.symm (CayleyField.genericCoordinate ConnectedField ij))
      rw [he]
      exact hX ij
  apply RingHom.ext
  intro x
  have hx := RingHom.congr_fun hh (e x)
  change f (e.symm (e x)) = g (e.symm (e x)) at hx
  simpa only [e.symm_apply_apply] using hx

/-- In the paired bases constructed from native transpose, the coefficient
action and the generic isomorphism entries satisfy actual matrix inversion. -/
theorem isomInversion_matrix :
    (genericIsomMatrix ρ).map (isomInversion ρ).toRingHom = (genericIsomMatrix ρ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  apply Matrix.map_injective (isomAuxiliaryFieldEquiv ρ).injective
  change (isomAuxiliaryFieldEquiv ρ).toRingHom.mapMatrix
    (((genericIsomMatrix ρ).map (isomInversion ρ).toRingHom) * genericIsomMatrix ρ) =
      (isomAuxiliaryFieldEquiv ρ).toRingHom.mapMatrix 1
  rw [map_mul, map_one]
  have hh : ((genericIsomMatrix ρ).map (isomInversion ρ).toRingHom).map
      (isomAuxiliaryFieldEquiv ρ).toRingHom =
        (CayleyField.genericMatrix ConnectedField).map FrameInversionRationality.inversion.toRingHom := by
    funext i j
    change isomAuxiliaryFieldEquiv ρ (isomInversion ρ (isomEntry ρ (i,j))) = _
    rw [isomAuxiliaryFieldEquiv_inversion, isomAuxiliaryFieldEquiv_entry]
    rfl
  change (((genericIsomMatrix ρ).map (isomInversion ρ).toRingHom).map
    (isomAuxiliaryFieldEquiv ρ).toRingHom) *
      ((genericIsomMatrix ρ).map (isomAuxiliaryFieldEquiv ρ).toRingHom) = 1
  rw [hh, isomAuxiliaryFieldEquiv_matrix]
  change FrameInversionRationality.inversion.toRingHom.mapMatrix
    (CayleyField.genericMatrix ConnectedField) * CayleyField.genericMatrix ConnectedField = 1
  rw [FrameInversionRationality.inversion_genericMatrix]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (CayleyField.genericMatrix_det_ne_zero ConnectedField))

/-- Constants and the actual generic matrix characterize the descended
exchange action uniquely. -/
theorem isomInversion_unique (τ : IsomFunctionField ρ ≃+* IsomFunctionField ρ)
    (hc : ∀ a : ConnectedField, τ (algebraMap ConnectedField (IsomFunctionField ρ) a) =
      algebraMap ConnectedField (IsomFunctionField ρ) (FrameQuadraticExtension.exchange a))
    (hX : (genericIsomMatrix ρ).map τ.toRingHom = (genericIsomMatrix ρ)⁻¹) : τ = isomInversion ρ := by
  apply RingEquiv.toRingHom_injective
  apply isomFieldHom_ext ρ
  · intro a
    exact (hc a).trans (isomInversion_coefficient ρ a).symm
  · rintro ⟨i,j⟩
    exact congrFun (congrFun (hX.trans (isomInversion_matrix ρ).symm) i) j

instance isomFunctionFieldComplexAlgebra : Algebra ℂ (IsomFunctionField ρ) :=
  ((algebraMap ConnectedField (IsomFunctionField ρ)).comp (algebraMap ℂ ConnectedField)).toAlgebra

instance isomFunctionFieldComplexSMul : SMul ℂ (IsomFunctionField ρ) :=
  (isomFunctionFieldComplexAlgebra ρ).toSMul

instance isomFunctionFieldScalarTower : IsScalarTower ℂ ConnectedField (IsomFunctionField ρ) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := ConnectedField) (A := IsomFunctionField ρ) fun _ => rfl

theorem isomInversion_complex_constant (c : ℂ) :
    isomInversion ρ (algebraMap ℂ (IsomFunctionField ρ) c) = algebraMap ℂ (IsomFunctionField ρ) c := by
  rw [IsScalarTower.algebraMap_apply ℂ ConnectedField (IsomFunctionField ρ),
    isomInversion_coefficient, FrameQuadraticExtension.exchange.commutes]

def isomFixedField : IntermediateField ℂ (IsomFunctionField ρ) where
  __ := SemilinearInvolution.fixedField (isomInversion ρ)
  algebraMap_mem' := isomInversion_complex_constant ρ

/-- The actual isomorphism-field fixed subfield is identified with the
already constructed auxiliary inversion fixed field by the proved coordinate map. -/
def isomFixedAuxiliaryEquiv : isomFixedField ρ ≃ₐ[ℂ] FrameInversionRationality.auxiliaryFixedField where
  toFun x := ⟨isomAuxiliaryFieldEquiv ρ x.val, by
    have hx : isomInversion ρ x.val = x.val := x.property
    change FrameInversionRationality.inversion (isomAuxiliaryFieldEquiv ρ x.val) = _
    change FrameInversionRationality.inversion (isomAuxiliaryFieldEquiv ρ x.val) = isomAuxiliaryFieldEquiv ρ x.val
    rw [← isomAuxiliaryFieldEquiv_inversion, hx]⟩
  invFun y := ⟨(isomAuxiliaryFieldEquiv ρ).symm y.val, by
    have hy : FrameInversionRationality.inversion y.val = y.val := y.property
    change isomInversion ρ ((isomAuxiliaryFieldEquiv ρ).symm y.val) = _
    change isomInversion ρ ((isomAuxiliaryFieldEquiv ρ).symm y.val) = (isomAuxiliaryFieldEquiv ρ).symm y.val
    rw [isomInversion_apply, AlgEquiv.apply_symm_apply, hy]⟩
  left_inv x := Subtype.ext ((isomAuxiliaryFieldEquiv ρ).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((isomAuxiliaryFieldEquiv ρ).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((isomAuxiliaryFieldEquiv ρ).toRingHom.map_add x.val y.val)
  map_mul' x y := Subtype.ext ((isomAuxiliaryFieldEquiv ρ).toRingHom.map_mul x.val y.val)
  commutes' c := Subtype.ext (((isomAuxiliaryFieldEquiv ρ).restrictScalars ℂ).commutes c)

def isomFixedRationalEquiv : isomFixedField ρ ≃ₐ[ℂ] RationalField ℂ 24 :=
  (isomFixedAuxiliaryEquiv ρ).trans FrameInversionRationality.auxiliaryFixedRationalEquiv

end RepresentationDescent

namespace Standard

def representation : Gamma →* (Four ≃ₗ[ℂ] Four) :=
  StandardFourPlaneRepresentation.gammaSignedPermutationRepresentation

abbrev LeftFiber := Descended representation false
abbrev RightFiber := Descended representation true

theorem finrank_leftFiber : finrank ConnectedField LeftFiber = 4 := finrank_descended representation false
theorem finrank_rightFiber : finrank ConnectedField RightFiber = 4 := finrank_descended representation true

def transposeExchange : LeftFiber ≃+ RightFiber := exchange representation

theorem transposeExchange_semilinear :
    PairedSemilinearCoordinates.IsSemilinear FrameQuadraticExtension.exchange.toRingEquiv transposeExchange :=
  exchange_semilinear representation

def leftBasis : Basis (Fin 4) ConnectedField LeftFiber := descendedBasis representation false
def rightBasis : Basis (Fin 4) ConnectedField RightFiber := pairedBasis representation

theorem rightBasis_paired (i : Fin 4) : rightBasis i = transposeExchange (leftBasis i) :=
  pairedBasis_apply representation i

abbrev E0 := StandardFourPlaneRepresentation.E0

local instance standardPlaneAddCommGroup : AddCommGroup StandardFourPlaneRepresentation.S0 :=
  { StandardFourPlaneRepresentation.S0.addCommGroup with
    toAddCommMonoid := StandardFourPlaneRepresentation.S0.addCommMonoid }

local instance actualE0AddCommGroup : AddCommGroup E0 :=
  { (inferInstance : AddCommGroup E0) with toAddCommMonoid := (inferInstance : AddCommMonoid E0) }

local instance actualE0Finite : Module.Finite ℂ E0 :=
  StandardFourPlaneRepresentation.tensorBasis.finiteDimensional_of_finite

def actualSideRepresentation (side : Bool) : Even →* (E0 ≃ₗ[ℂ] E0) :=
  StandardFourPlaneRepresentation.tensorRepresentation.comp (sideFactor side)

/-- This is the literal scalar extension of `S0 ⊗ det(S0)∨`, with no
replacement of its exterior determinant line by an assumed character. -/
def ActualRaw (_side : Bool) := ScalarExtendedRepresentation.ScalarExtension ℂ Ambient E0

instance actualRawAddCommGroup (side : Bool) : AddCommGroup (ActualRaw side) := by unfold ActualRaw; infer_instance
instance actualRawModule (side : Bool) : Module Ambient (ActualRaw side) := by unfold ActualRaw; infer_instance
instance actualRawBaseModule (side : Bool) : Module ℂ (ActualRaw side) := by unfold ActualRaw; infer_instance
instance actualRawFinite (side : Bool) : Module.Finite Ambient (ActualRaw side) := by unfold ActualRaw; infer_instance

@[instance_reducible] instance actualRawAction (side : Bool) : DistribMulAction Even (ActualRaw side) :=
  ScalarExtendedRepresentation.tensorAction ℂ Ambient Even E0 (actualSideRepresentation side)

instance actualRawSemilinear (side : Bool) : SMulDistribClass Even Ambient (ActualRaw side) :=
  ScalarExtendedRepresentation.tensorSemilinear ℂ Ambient Even E0 (actualSideRepresentation side)

def actualRawCoordinates (side : Bool) : ActualRaw side ≃ₗ[Ambient] Raw representation side :=
  StandardFourPlaneRepresentation.tensorEvaluationEquiv.baseChange ℂ Ambient E0 Four

theorem actualRawCoordinates_tmul (side : Bool) (a : Ambient) (v : E0) :
    actualRawCoordinates side (a ⊗ₜ[ℂ] v) =
      rawTmul representation side a (StandardFourPlaneRepresentation.tensorEvaluationEquiv v) := rfl

/-- Evaluation coordinates intertwine the two actual tensor representations,
including the nontrivial coefficient action on the native ambient field. -/
theorem actualRawCoordinates_action (side : Bool) (g : Even) (x : ActualRaw side) :
    actualRawCoordinates side (g • x) = g • actualRawCoordinates side x := by
  change Ambient ⊗[ℂ] E0 at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a v =>
    change rawTmul representation side (g • a)
      (StandardFourPlaneRepresentation.tensorEvaluationEquiv
        (StandardFourPlaneRepresentation.tensorRepresentation (sideFactor side g) v)) =
      rawTmul representation side (g • a)
        (sideRepresentation representation side g
          (StandardFourPlaneRepresentation.tensorEvaluationEquiv v))
    congr 1
    exact StandardFourPlaneRepresentation.tensorEvaluationEquiv_equivariant (sideFactor side g) v

def ActualDescended (side : Bool) :=
  ↥(FiniteGaloisDescent.fixedVectors Even Ambient (ActualRaw side))

instance actualDescendedAddCommGroup (side : Bool) : AddCommGroup (ActualDescended side) := by
  unfold ActualDescended
  infer_instance

instance actualDescendedModule (side : Bool) : Module ConnectedField (ActualDescended side) :=
  inferInstanceAs (Module (FiniteGaloisDescent.FixedField Even Ambient)
    (FiniteGaloisDescent.fixedVectors Even Ambient (ActualRaw side)))

/-- The displayed coordinate fibers are canonically the actual fixed vectors
of the literal determinant-tensor module. This is derived from the proved
equivariance, rather than an identification supplied as descent data. -/
def actualFixedVectorsEquiv (side : Bool) : ActualDescended side ≃ₗ[ConnectedField] Descended representation side where
  toFun x := ⟨actualRawCoordinates side x.val, fun g => by
    rw [← actualRawCoordinates_action, x.property g]⟩
  invFun y := ⟨(actualRawCoordinates side).symm y.val, fun g => by
    apply (actualRawCoordinates side).injective
    rw [actualRawCoordinates_action, LinearEquiv.apply_symm_apply, y.property g]⟩
  left_inv x := Subtype.ext ((actualRawCoordinates side).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((actualRawCoordinates side).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (actualRawCoordinates side) x.val y.val)
  map_smul' a x := by
    apply Subtype.ext
    change actualRawCoordinates side ((a : Ambient) • x.val) = (a : Ambient) • actualRawCoordinates side x.val
    exact (actualRawCoordinates side).map_smul a.val x.val

def actualLeftBasis : Basis (Fin 4) ConnectedField (ActualDescended false) :=
  leftBasis.map (actualFixedVectorsEquiv false).symm

def actualRightBasis : Basis (Fin 4) ConnectedField (ActualDescended true) :=
  rightBasis.map (actualFixedVectorsEquiv true).symm

def actualTransposeExchange : ActualDescended false ≃+ ActualDescended true :=
  (actualFixedVectorsEquiv false).toAddEquiv.trans
    (transposeExchange.trans (actualFixedVectorsEquiv true).symm.toAddEquiv)

theorem actualTransposeExchange_coordinates (x : ActualDescended false) :
    actualFixedVectorsEquiv true (actualTransposeExchange x) =
      transposeExchange (actualFixedVectorsEquiv false x) :=
  (actualFixedVectorsEquiv true).apply_symm_apply _

theorem actualTransposeExchange_semilinear :
    PairedSemilinearCoordinates.IsSemilinear FrameQuadraticExtension.exchange.toRingEquiv
      actualTransposeExchange := by
  intro a x
  apply (actualFixedVectorsEquiv true).injective
  rw [actualTransposeExchange_coordinates, (actualFixedVectorsEquiv false).map_smul,
    transposeExchange_semilinear, (actualFixedVectorsEquiv true).map_smul,
      actualTransposeExchange_coordinates]

def actualRawTranspose : ActualRaw false →ₗ[ℂ] ActualRaw true :=
  TensorProduct.map nativeTranspose.toLinearMap (LinearMap.id : E0 →ₗ[ℂ] E0)

theorem actualRawTranspose_coordinates (x : ActualRaw false) :
    actualRawCoordinates true (actualRawTranspose x) =
      rawTranspose representation false (actualRawCoordinates false x) := by
  change Ambient ⊗[ℂ] E0 at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a v => rfl

/-- The exchange on the actual descended tensors is literally native
transpose on coefficients and the identity on the fixed determinant-tensor fiber. -/
theorem actualTransposeExchange_val (x : ActualDescended false) :
    (actualTransposeExchange x).val = actualRawTranspose x.val := by
  apply (actualRawCoordinates true).injective
  change (actualFixedVectorsEquiv true (actualTransposeExchange x)).val = _
  rw [actualTransposeExchange_coordinates, actualRawTranspose_coordinates]
  rfl

theorem actualRightBasis_paired (i : Fin 4) :
    actualRightBasis i = actualTransposeExchange (actualLeftBasis i) := by
  change (actualFixedVectorsEquiv true).symm (rightBasis i) =
    (actualFixedVectorsEquiv true).symm
      (transposeExchange ((actualFixedVectorsEquiv false) ((actualFixedVectorsEquiv false).symm (leftBasis i))))
  rw [LinearEquiv.apply_symm_apply, rightBasis_paired]

theorem actualRightBasis_eq_paired : actualRightBasis =
    PairedSemilinearCoordinates.pairedBasis FrameQuadraticExtension.exchange.toRingEquiv
      actualTransposeExchange actualTransposeExchange_semilinear actualLeftBasis := by
  apply Module.Basis.eq_of_apply_eq
  intro i
  rw [actualRightBasis_paired, PairedSemilinearCoordinates.pairedBasis_apply]

theorem actualExchange_matrix_inverse (x : ActualDescended false ≃ₗ[ConnectedField] ActualDescended true) :
    LinearMap.toMatrix actualLeftBasis actualRightBasis
      (PairedSemilinearCoordinates.exchange FrameQuadraticExtension.exchange.toRingEquiv
        FrameQuadraticExtension.exchange_exchange actualTransposeExchange actualTransposeExchange_semilinear x).toLinearMap =
      ((LinearMap.toMatrix actualLeftBasis actualRightBasis x.toLinearMap)⁻¹).map
        FrameQuadraticExtension.exchange.toRingEquiv := by
  rw [actualRightBasis_eq_paired]
  exact PairedSemilinearCoordinates.exchange_matrix_inverse FrameQuadraticExtension.exchange.toRingEquiv
    FrameQuadraticExtension.exchange_exchange actualTransposeExchange actualTransposeExchange_semilinear actualLeftBasis x

abbrev IsomField := IsomFunctionField representation
abbrev IsomFixedField := isomFixedField representation

/-- Scalar extension of the canonical actual-fiber coordinate identifications
turns the generic matrix into an actual isomorphism of the original descended tensors. -/
def actualGenericIsomorphism :
    (IsomField ⊗[ConnectedField] ActualDescended false) ≃ₗ[IsomField]
      (IsomField ⊗[ConnectedField] ActualDescended true) :=
  ((actualFixedVectorsEquiv false).baseChange ConnectedField IsomField _ _).trans
    ((genericIsomorphism representation).trans
      ((actualFixedVectorsEquiv true).symm.baseChange ConnectedField IsomField _ _))

def isomFieldAuxiliaryEquiv : IsomField ≃ₐ[ConnectedField] FrameInversionRationality.AuxiliaryField :=
  isomAuxiliaryFieldEquiv representation

def isomFixedFieldRationalEquiv : IsomFixedField ≃ₐ[ℂ] RationalField ℂ 24 :=
  isomFixedRationalEquiv representation

end Standard

end M9.FrameBundleDescent
