module

public import M9.FrameQuadraticExtension
public import M9.CayleyFixedField
public import M9.ProjectiveNoName
public import M9.RationalExtensionAssembly

/-!
# Rationality of the actual auxiliary frame inversion field

The coefficient fields are the fixed fields of the actual native projective
frame action.  The nonzero anti-invariant is obtained from the proved
quadratic exchange.  The auxiliary sixteen-variable graph field carries the
actual coefficient exchange and generic matrix inversion.  Its fixed field
is rational of dimension twenty-four over the original complex constants.

This is an algebraic statement about that explicit auxiliary field.  It
does not identify the field with a Grassmannian or with a moduli space.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace M9.FrameInversionRationality

attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev ConnectedField := FrameQuadraticExtension.connectedField
abbrev BaseField := FrameQuadraticExtension.baseField
abbrev NativeFixedField := ProjectiveNoName.Concrete.nativeFixedField
abbrev ExchangeFixedField := FrameQuadraticExtension.exchangeFixedField
abbrev AuxiliaryField := CayleyField.Rational ConnectedField

/-- The anti-invariant is chosen from the actual connected invariant field,
using the nontrivial transpose action already proved on that field. -/
def antiInvariant : ConnectedField :=
  Classical.choose FrameQuadraticExtension.exists_anti_invariant

theorem antiInvariant_ne_zero : antiInvariant ≠ 0 :=
  (Classical.choose_spec FrameQuadraticExtension.exists_anti_invariant).1

theorem exchange_antiInvariant : FrameQuadraticExtension.exchange antiInvariant = -antiInvariant :=
  (Classical.choose_spec FrameQuadraticExtension.exists_anti_invariant).2

/-- The actual graph-field automorphism, obtained from the normalized Cayley
coordinates over the actual connected frame invariant field. -/
def inversion : AuxiliaryField ≃+* AuxiliaryField :=
  CayleyFixedField.graphInvolution ConnectedField FrameQuadraticExtension.exchange.toRingEquiv
    antiInvariant antiInvariant_ne_zero

theorem inversion_involutive : Function.Involutive inversion :=
  CayleyFixedField.graphInvolution_involutive ConnectedField
    FrameQuadraticExtension.exchange.toRingEquiv FrameQuadraticExtension.exchange_exchange
      antiInvariant antiInvariant_ne_zero

theorem inversion_constant (a : ConnectedField) :
    inversion (algebraMap ConnectedField AuxiliaryField a) =
      algebraMap ConnectedField AuxiliaryField (FrameQuadraticExtension.exchange a) :=
  CayleyFixedField.graphInvolution_constant ConnectedField FrameQuadraticExtension.exchange.toRingEquiv
    antiInvariant antiInvariant_ne_zero a

/-- On the original generic four-by-four matrix, the involution is literal
matrix inversion, rather than a replacement action specified only by name. -/
theorem inversion_genericMatrix :
    inversion.toRingHom.mapMatrix (CayleyField.genericMatrix ConnectedField) =
      (CayleyField.genericMatrix ConnectedField)⁻¹ :=
  CayleyFixedField.graphInvolution_matrix ConnectedField FrameQuadraticExtension.exchange.toRingEquiv
    antiInvariant antiInvariant_ne_zero exchange_antiInvariant

theorem inversion_complex_constant (c : ℂ) :
    inversion (algebraMap ℂ AuxiliaryField c) = algebraMap ℂ AuxiliaryField c := by
  rw [IsScalarTower.algebraMap_apply ℂ ConnectedField AuxiliaryField, inversion_constant,
    FrameQuadraticExtension.exchange.commutes]

/-- The graph-field automorphism fixes the original complex coefficient
inclusion. -/
def inversionAlgEquiv : AuxiliaryField ≃ₐ[ℂ] AuxiliaryField where
  __ := inversion
  commutes' := inversion_complex_constant

/-- The actual equalizer subfield of generic matrix inversion and coefficient
exchange, retaining the original complex coefficient inclusion. -/
def auxiliaryFixedField : IntermediateField ℂ AuxiliaryField where
  __ := SemilinearInvolution.fixedField inversion
  algebraMap_mem' := inversion_complex_constant

theorem mem_auxiliaryFixedField (x : AuxiliaryField) :
    x ∈ auxiliaryFixedField ↔ inversion x = x := Iff.rfl

instance exchangeFixedComplexAlgebra :
    Algebra ℂ (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv) :=
  inferInstanceAs (Algebra ℂ ExchangeFixedField)

/-- The two constructions use precisely the same native projective field
action; their fixed subfields agree element by element. -/
theorem baseField_eq_nativeFixedField : BaseField = NativeFixedField := by
  apply IntermediateField.ext
  intro x
  exact Iff.rfl

def nativeBaseEquiv : NativeFixedField ≃ₐ[ℂ] BaseField :=
  IntermediateField.equivOfEq baseField_eq_nativeFixedField.symm

def nativeExchangeFixedEquiv : NativeFixedField ≃ₐ[ℂ] ExchangeFixedField :=
  nativeBaseEquiv.trans FrameQuadraticExtension.baseFixedEquiv

/-- Cayley descent gives sixteen independent rational coordinates over the
actual exchange fixed coefficient field. -/
def auxiliaryCayleyPresentation :
    auxiliaryFixedField ≃ₐ[ℂ] CayleyField.Rational ExchangeFixedField where
  __ := (CayleyFixedField.fixedGraphRationalAlgEquiv ConnectedField
    FrameQuadraticExtension.exchange.toRingEquiv FrameQuadraticExtension.exchange_exchange
      antiInvariant antiInvariant_ne_zero).symm.toRingEquiv
  commutes' c := by
    let e := CayleyFixedField.fixedGraphRationalAlgEquiv ConnectedField
      FrameQuadraticExtension.exchange.toRingEquiv FrameQuadraticExtension.exchange_exchange
        antiInvariant antiInvariant_ne_zero
    let : Algebra (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv)
        (SemilinearInvolution.fixedField inversion) :=
      CayleyFixedField.graphFixedAlgebra ConnectedField FrameQuadraticExtension.exchange.toRingEquiv
        antiInvariant antiInvariant_ne_zero
    have hc : (algebraMap ℂ auxiliaryFixedField c : SemilinearInvolution.fixedField inversion) =
        algebraMap (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv)
          (SemilinearInvolution.fixedField inversion)
            (algebraMap ℂ (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv) c) := by
      apply Subtype.ext
      change algebraMap ℂ AuxiliaryField c =
        algebraMap ConnectedField AuxiliaryField (algebraMap ℂ ConnectedField c)
      exact IsScalarTower.algebraMap_apply ℂ ConnectedField AuxiliaryField c
    change e.symm (algebraMap ℂ auxiliaryFixedField c) = _
    rw [hc]
    exact (e.symm.commutes
      (algebraMap ℂ (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv) c)).trans
      (IsScalarTower.algebraMap_apply ℂ
        (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv)
        (CayleyField.Rational
          (SemilinearInvolution.fixedField FrameQuadraticExtension.exchange.toRingEquiv)) c).symm

/-- The explicit auxiliary inversion fixed field is a sixteen-variable
rational extension of the actual native full frame invariant field. -/
def auxiliaryNativePresentation : auxiliaryFixedField ≃ₐ[ℂ] RationalField NativeFixedField 16 :=
  (auxiliaryCayleyPresentation.trans
    ((rationalFieldReindex ExchangeFixedField
      (finProdFinEquiv : (Fin 4 × Fin 4) ≃ Fin 16)).restrictScalars ℂ)).trans
        (rationalFieldMap nativeExchangeFixedEquiv.symm 16)

/-- The closed algebraic quotient calculation for the explicit auxiliary
inversion graph field: sixteen Cayley variables over the actual native
frame quotient, with the proved eight-variable no-name stabilization,
yield twenty-four independent complex rational variables. -/
def auxiliaryFixedRationalEquiv : auxiliaryFixedField ≃ₐ[ℂ] RationalField ℂ 24 :=
  rationalExtensionSixteenEightEquiv auxiliaryNativePresentation
    ProjectiveNoName.Concrete.stableProjectiveInvariantEquiv

theorem auxiliaryFixedField_rational : RationalOfDimension ℂ auxiliaryFixedField 24 :=
  ⟨auxiliaryFixedRationalEquiv⟩

end M9.FrameInversionRationality
