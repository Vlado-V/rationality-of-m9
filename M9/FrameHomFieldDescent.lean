module

public import M9.FrameBundleDescent
public import M9.SemilinearHomCoordinates

/-!
# The actual finite-frame Hom-field descent

The source is the rational function field of the literal raw Hom space
between the two scalar-extended determinant-tensor fibers.  Its group action
is the coefficient-semilinear contragredient action.  Scalar extension of the
actual descended bases gives fixed matrix-coordinate functionals.  Finite
denominator descent then identifies the actual invariant field with the
function field of the actual descended isomorphism scheme.

All coefficient embeddings and the sixteen universal matrix coordinates are
retained.  No identification of invariant fields is supplied as a premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace M9.FrameHomFieldDescent

open Module FrameBundleDescent FrameBundleDescent.Standard
open scoped TensorProduct

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

/-- The original Hom space, before taking the finite-frame quotient. -/
abbrev RawHom := ActualRaw false →ₗ[Ambient] ActualRaw true
abbrev RawDual := Dual Ambient RawHom
abbrev RawRing := SymmetricAlgebra Ambient RawDual
abbrev RawField := FractionRing RawRing

@[instance_reducible] instance rawHomAction : DistribMulAction Even RawHom :=
  SemilinearHomCoordinates.homAction Even Ambient (ActualRaw false) (ActualRaw true)

instance rawHomSemilinear : SMulDistribClass Even Ambient RawHom :=
  SemilinearHomCoordinates.homSemilinear Even Ambient (ActualRaw false) (ActualRaw true)

@[instance_reducible] instance rawDualAction : DistribMulAction Even RawDual :=
  SemilinearHomCoordinates.dualAction Even Ambient RawHom

instance rawDualSemilinear : SMulDistribClass Even Ambient RawDual :=
  SemilinearHomCoordinates.dualSemilinear Even Ambient RawHom

theorem rawHomAction_apply (g : Even) (h : RawHom) (x : ActualRaw false) :
    (g • h) x = g • h (g⁻¹ • x) := rfl

theorem rawDualAction_apply (g : Even) (l : RawDual) (h : RawHom) :
    (g • l) h = g • l (g⁻¹ • h) := rfl

theorem rawDualAction_pairing (g : Even) (l : RawDual) (h : RawHom) :
    (g • l) (g • h) = g • l h := by
  rw [rawDualAction_apply, inv_smul_smul]

/-- The canonical multiplication map for the literal determinant-tensor fibers. -/
def actualScalarExtension (side : Bool) :
    Ambient ⊗[ConnectedField] ActualDescended side ≃ₗ[Ambient] ActualRaw side :=
  FiniteGaloisDescent.scalarExtensionEquiv Even Ambient (ActualRaw side)

theorem actualScalarExtension_tmul (side : Bool) (a : Ambient) (x : ActualDescended side) :
    actualScalarExtension side (a ⊗ₜ[ConnectedField] x) = a • x.val :=
  FiniteGaloisDescent.scalarExtensionEquiv_tmul Even Ambient (ActualRaw side) a x

def scalarExtendedBasis (side : Bool) (b : Basis (Fin 4) ConnectedField (ActualDescended side)) :
    Basis (Fin 4) Ambient (ActualRaw side) :=
  (b.baseChange Ambient).map (actualScalarExtension side)

theorem scalarExtendedBasis_apply (side : Bool)
    (b : Basis (Fin 4) ConnectedField (ActualDescended side)) (i : Fin 4) :
    scalarExtendedBasis side b i = (b i).val := by
  rw [scalarExtendedBasis, Basis.map_apply, Basis.baseChange_apply, actualScalarExtension_tmul, one_smul]

theorem scalarExtendedBasis_fixed (side : Bool)
    (b : Basis (Fin 4) ConnectedField (ActualDescended side)) (g : Even) (i : Fin 4) :
    g • scalarExtendedBasis side b i = scalarExtendedBasis side b i := by
  rw [scalarExtendedBasis_apply]
  exact (b i).property g

theorem scalarExtendedBasis_repr_fixed (side : Bool)
    (b : Basis (Fin 4) ConnectedField (ActualDescended side))
    (x : ActualDescended side) (i : Fin 4) :
    (scalarExtendedBasis side b).repr x.val i = algebraMap ConnectedField Ambient (b.repr x i) := by
  have hx : (actualScalarExtension side).symm x.val = (1 : Ambient) ⊗ₜ[ConnectedField] x := by
    apply (actualScalarExtension side).injective
    rw [LinearEquiv.apply_symm_apply, actualScalarExtension_tmul, one_smul]
  change (b.baseChange Ambient).repr ((actualScalarExtension side).symm x.val) i = _
  rw [hx, Basis.baseChange_repr_tmul]
  change algebraMap ConnectedField Ambient (b.repr x i) * 1 = _
  exact mul_one _

def leftRawBasis : Basis (Fin 4) Ambient (ActualRaw false) := scalarExtendedBasis false actualLeftBasis
def rightRawBasis : Basis (Fin 4) Ambient (ActualRaw true) := scalarExtendedBasis true actualRightBasis

/-- The sixteen linear functionals are actual matrix entries in scalar-extended
bases of the actual descended fibers. -/
def rawCoordinateBasis : Basis (Fin 4 × Fin 4) Ambient RawDual :=
  SemilinearHomCoordinates.coordinateBasis Ambient (ActualRaw false) (ActualRaw true)
    leftRawBasis rightRawBasis

theorem rawCoordinateBasis_apply (ij : Fin 4 × Fin 4) (h : RawHom) :
    rawCoordinateBasis ij h = LinearMap.toMatrix leftRawBasis rightRawBasis h ij.1 ij.2 :=
  SemilinearHomCoordinates.coordinateBasis_apply Ambient (ActualRaw false) (ActualRaw true)
    leftRawBasis rightRawBasis ij h

theorem rawCoordinateBasis_fixed (g : Even) (ij : Fin 4 × Fin 4) :
    g • rawCoordinateBasis ij = rawCoordinateBasis ij :=
  SemilinearHomCoordinates.coordinateBasis_fixed Even Ambient (ActualRaw false) (ActualRaw true)
    leftRawBasis rightRawBasis (scalarExtendedBasis_fixed false actualLeftBasis)
      (scalarExtendedBasis_fixed true actualRightBasis) g ij

abbrev ActualHom := ActualDescended false →ₗ[ConnectedField] ActualDescended true

/-- Scalar extension of an actual descended linear map. -/
def extendHom (h : ActualHom) : RawHom :=
  (actualScalarExtension true).toLinearMap.comp
    ((h.baseChange Ambient).comp (actualScalarExtension false).symm.toLinearMap)

theorem extendHom_fixedVector (h : ActualHom) (x : ActualDescended false) :
    extendHom h x.val = (h x).val := by
  have hx : (actualScalarExtension false).symm x.val = (1 : Ambient) ⊗ₜ[ConnectedField] x := by
    apply (actualScalarExtension false).injective
    rw [LinearEquiv.apply_symm_apply, actualScalarExtension_tmul, one_smul]
  change actualScalarExtension true ((h.baseChange Ambient) ((actualScalarExtension false).symm x.val)) = _
  rw [hx, LinearMap.baseChange_tmul, actualScalarExtension_tmul, one_smul]

def descendedHomEquiv : ActualHom ≃ₗ[ConnectedField] HomSpace representation :=
  LinearEquiv.arrowCongr (actualFixedVectorsEquiv false) (actualFixedVectorsEquiv true)

/-- The raw fixed coordinate functions restrict to the literal descended Hom
matrix entries, with the original coefficient inclusion. -/
theorem rawCoordinateBasis_extendHom (ij : Fin 4 × Fin 4) (h : ActualHom) :
    rawCoordinateBasis ij (extendHom h) =
      algebraMap ConnectedField Ambient (homDualBasis representation ij (descendedHomEquiv h)) := by
  rw [rawCoordinateBasis_apply, LinearMap.toMatrix_apply]
  change rightRawBasis.repr (extendHom h (leftRawBasis ij.2)) ij.1 = _
  rw [show leftRawBasis ij.2 = (actualLeftBasis ij.2).val from scalarExtendedBasis_apply _ _ _,
    extendHom_fixedVector]
  rw [show rightRawBasis = scalarExtendedBasis true actualRightBasis from rfl,
    scalarExtendedBasis_repr_fixed]
  congr 1
  rw [homDualBasis_apply, homMatrixCoordinates, LinearMap.toMatrix_apply]
  rfl

@[instance_reducible] def rawPolynomialAction : MulSemiringAction Even RawRing :=
  FiniteNoNameField.symmetricPolynomialAction Even Ambient RawDual rawCoordinateBasis

@[instance_reducible] def rawFieldAction : MulSemiringAction Even RawField :=
  FiniteNoNameField.symmetricRationalAction Even Ambient RawDual rawCoordinateBasis

theorem rawPolynomialAction_coefficient (g : Even) (a : Ambient) :
    letI := rawPolynomialAction
    g • algebraMap Ambient RawRing a = algebraMap Ambient RawRing (g • a) :=
  FiniteNoNameField.symmetricPolynomialAction_constant Even Ambient RawDual rawCoordinateBasis g a

theorem rawPolynomialAction_degreeOne (g : Even) (l : RawDual) :
    letI := rawPolynomialAction
    g • SymmetricAlgebra.ι Ambient RawDual l = SymmetricAlgebra.ι Ambient RawDual (g • l) :=
  FiniteNoNameField.symmetricPolynomialAction_iota Even Ambient RawDual rawCoordinateBasis
    rawCoordinateBasis_fixed g l

theorem rawFieldAction_polynomial (g : Even) (p : RawRing) :
    letI := rawPolynomialAction
    letI := rawFieldAction
    g • algebraMap RawRing RawField p = algebraMap RawRing RawField (g • p) :=
  FiniteNoNameField.symmetricRationalAction_polynomial Even Ambient RawDual rawCoordinateBasis g p

theorem rawFieldAction_coefficient (g : Even) (a : Ambient) :
    letI := rawFieldAction
    g • algebraMap Ambient RawField a = algebraMap Ambient RawField (g • a) :=
  FiniteNoNameField.symmetricRationalAction_constant Even Ambient RawDual rawCoordinateBasis g a

/-- The field action on every degree-one function is the actual
coefficient-semilinear contragredient action, not a declared variable action. -/
theorem rawFieldAction_degreeOne (g : Even) (l : RawDual) :
    letI := rawFieldAction
    g • algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual l) =
      algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (g • l)) :=
  FiniteNoNameField.symmetricRationalAction_iota Even Ambient RawDual rawCoordinateBasis
    rawCoordinateBasis_fixed g l

/-- Coefficients and actual linear coordinate functions uniquely determine
the induced action on the rational function field. -/
theorem rawFieldAction_unique (α : MulSemiringAction Even RawField)
    (hc : ∀ (g : Even) (a : Ambient),
      α.smul g (algebraMap Ambient RawField a) = algebraMap Ambient RawField (g • a))
    (hl : ∀ (g : Even) (l : RawDual),
      α.smul g (algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual l)) =
        algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (g • l)))
    (g : Even) (z : RawField) : α.smul g z = rawFieldAction.smul g z := by
  let f : RawField →+* RawField := @MulSemiringAction.toRingHom Even _ RawField _ α g
  let h : RawField →+* RawField := @MulSemiringAction.toRingHom Even _ RawField _ rawFieldAction g
  have he : f = h := SemilinearHomCoordinates.coordinateFieldHom_ext f h
    (fun a => (hc g a).trans (rawFieldAction_coefficient g a).symm)
    (fun l => (hl g l).trans (rawFieldAction_degreeOne g l).symm)
  exact congrArg (fun r : RawField →+* RawField => r z) he

/-- The actual finite-frame invariant subfield of the raw Hom function field. -/
abbrev RawFixedField :=
  FiniteNoNameField.SymmetricFixedField Even Ambient RawDual rawCoordinateBasis

theorem mem_rawFixedField (z : RawField) :
    z ∈ RawFixedField ↔ ∀ g : Even, rawFieldAction.smul g z = z := Iff.rfl

def fixedSubfieldOfAction (α : MulSemiringAction Even RawField) : Subfield RawField :=
  letI := α
  FixedPoints.subfield Even RawField

/-- Any action with the original coefficient and contragredient formulas has
literally this fixed subfield; a fixed-field identification is not a hypothesis. -/
theorem fixedSubfieldOfAction_eq (α : MulSemiringAction Even RawField)
    (hc : ∀ (g : Even) (a : Ambient),
      α.smul g (algebraMap Ambient RawField a) = algebraMap Ambient RawField (g • a))
    (hl : ∀ (g : Even) (l : RawDual),
      α.smul g (algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual l)) =
        algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (g • l))) :
    fixedSubfieldOfAction α = RawFixedField := by
  ext z
  change (∀ g : Even, α.smul g z = z) ↔ ∀ g : Even, rawFieldAction.smul g z = z
  constructor
  · intro hz g
    exact (rawFieldAction_unique α hc hl g z).symm.trans (hz g)
  · intro hz g
    exact (rawFieldAction_unique α hc hl g z).trans (hz g)

def fixedCoordinate (ij : Fin 4 × Fin 4) : RawFixedField :=
  ⟨algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (rawCoordinateBasis ij)), by
    intro g
    exact (rawFieldAction_degreeOne g (rawCoordinateBasis ij)).trans
      (congrArg (fun l => algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual l))
        (rawCoordinateBasis_fixed g ij))⟩

instance rawFixedConnectedAlgebra : Algebra ConnectedField RawFixedField :=
  FiniteNoNameField.symmetricFixedAlgebra Even Ambient RawDual rawCoordinateBasis

def fixedRationalCoordinates : RawFixedField ≃ₐ[ConnectedField] CayleyField.Rational ConnectedField :=
  FiniteNoNameField.fixedSymmetricFieldAlgEquiv Even Ambient RawDual rawCoordinateBasis

theorem fixedRationalCoordinates_coordinate (ij : Fin 4 × Fin 4) :
    fixedRationalCoordinates (fixedCoordinate ij) = CayleyField.genericCoordinate ConnectedField ij := by
  apply (FiniteNoNameField.fixedRationalAlgEquiv Even Ambient (Fin 4 × Fin 4)).injective
  change (FiniteNoNameField.fixedRationalAlgEquiv Even Ambient (Fin 4 × Fin 4))
    ((FiniteNoNameField.fixedRationalAlgEquiv Even Ambient (Fin 4 × Fin 4)).symm
      (FiniteNoNameField.symmetricFixedCoordinates Even Ambient RawDual rawCoordinateBasis
        (fixedCoordinate ij))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  change FiniteNoNameField.rationalCoordinates Ambient RawDual rawCoordinateBasis
    (algebraMap RawRing RawField (SymmetricAlgebra.ι Ambient RawDual (rawCoordinateBasis ij))) =
      FiniteNoNameField.rationalInclude Even Ambient (Fin 4 × Fin 4)
        (algebraMap (MvPolynomial (Fin 4 × Fin 4) ConnectedField)
          (CayleyField.Rational ConnectedField) (MvPolynomial.X ij))
  rw [FiniteNoNameField.rationalCoordinates_polynomial,
    show FiniteNoNameField.polynomialCoordinates Ambient RawDual rawCoordinateBasis
      (SymmetricAlgebra.ι Ambient RawDual (rawCoordinateBasis ij)) = MvPolynomial.X ij from
        SymmetricAlgebra.equivMvPolynomial_ι_apply rawCoordinateBasis ij]
  have hinc := FiniteNoNameField.rationalInclude_polynomial Even Ambient (Fin 4 × Fin 4)
    (MvPolynomial.X ij)
  have hp : FiniteNoNameField.polynomialInclude Even Ambient (Fin 4 × Fin 4) (MvPolynomial.X ij) =
      MvPolynomial.X ij := MvPolynomial.map_X _ _
  exact (hinc.trans (congrArg (algebraMap (FiniteNoNameField.PolynomialRing Ambient (Fin 4 × Fin 4))
    (FiniteNoNameField.RationalField Ambient (Fin 4 × Fin 4))) hp)).symm

/-- Finite rational descent, followed by the actual determinant-open
localization comparison for the descended Hom scheme. -/
def fixedFieldEquiv : RawFixedField ≃ₐ[ConnectedField] Standard.IsomField :=
  fixedRationalCoordinates.trans
    (isomAuxiliaryFieldEquiv representation).symm

theorem fixedFieldEquiv_coefficient (a : ConnectedField) :
    fixedFieldEquiv (algebraMap ConnectedField RawFixedField a) =
      algebraMap ConnectedField Standard.IsomField a := fixedFieldEquiv.commutes a

/-- The equivalence retains each universal entry of the actual descended
isomorphism scheme, rather than only its transcendence degree. -/
theorem fixedFieldEquiv_coordinate (ij : Fin 4 × Fin 4) :
    fixedFieldEquiv (fixedCoordinate ij) = isomEntry representation ij := by
  apply (isomAuxiliaryFieldEquiv representation).injective
  change (isomAuxiliaryFieldEquiv representation)
    ((isomAuxiliaryFieldEquiv representation).symm
      (fixedRationalCoordinates (fixedCoordinate ij))) = _
  rw [AlgEquiv.apply_symm_apply, fixedRationalCoordinates_coordinate,
    isomAuxiliaryFieldEquiv_entry]

instance rawFixedComplexAlgebra : Algebra ℂ RawFixedField :=
  ((algebraMap ConnectedField RawFixedField).comp (algebraMap ℂ ConnectedField)).toAlgebra

instance rawFixedComplexTower : IsScalarTower ℂ ConnectedField RawFixedField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem rawFixedConnectedAlgebra_coe (a : ConnectedField) :
    ((algebraMap ConnectedField RawFixedField a : RawFixedField) : RawField) =
      algebraMap Ambient RawField (a : Ambient) := rfl

theorem rawFixedComplexAlgebra_coe (c : ℂ) :
    ((algebraMap ℂ RawFixedField c : RawFixedField) : RawField) =
      algebraMap Ambient RawField (algebraMap ℂ Ambient c) := rfl

/-- The same actual fixed-field comparison with its original complex
constant-field structure. -/
def fixedFieldComplexEquiv : RawFixedField ≃ₐ[ℂ] Standard.IsomField :=
  fixedFieldEquiv.restrictScalars ℂ

theorem fixedFieldComplexEquiv_coefficient (c : ℂ) :
    fixedFieldComplexEquiv (algebraMap ℂ RawFixedField c) =
      algebraMap ℂ Standard.IsomField c := fixedFieldComplexEquiv.commutes c

/-- The comparison also reaches the literal generic stalk of the native
determinant-open isomorphism scheme. -/
def fixedFieldNativeEquiv :
    RawFixedField ≃ₐ[ConnectedField] NativeIsomFunctionField representation :=
  fixedFieldEquiv.trans (nativeIsomFunctionFieldEquiv representation).symm

end M9.FrameHomFieldDescent
