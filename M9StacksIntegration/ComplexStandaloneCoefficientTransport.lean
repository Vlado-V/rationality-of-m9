module

public import M9StacksIntegration.ComplexULiftFunctionField
public import M9StacksIntegration.StandaloneCoefficientGeometryTransport
public import M9StacksIntegration.StandaloneCoefficientGeometricTransport

@[expose] public section

/-! Canonical Type-0 coefficient adapter for the original standalone
moduli structures. The input space and every original test/family are
retained by the derived inverse functors. This file produces no original
coarse classifier and does not enlarge the universe of test schemes. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace M9Native.ComplexStandaloneCoefficientTransport

open StandaloneCoefficientFamilyTransport StandaloneCoefficientClassifierTransport

abbrev Coeff : Type := ComplexULiftFunctionField.Coeff

def baseIso : Spec (.of ℂ) ≅ Spec (.of Coeff) :=
  ComplexULiftFunctionField.canonicalSpecIso.symm

theorem coefficientSpecIso_eq :
    StandaloneCoefficientGeometricTransport.coefficientSpecIso
      (ULift.ringEquiv.symm : ℂ ≃+* Coeff) = baseIso := rfl

/-- The actual original space is relabeled using the canonical base map. -/
abbrev space (M : M9StandaloneDraft.Space ℂ) : M9StandaloneDraft.Space Coeff :=
  spaceForward baseIso M

/-- The physical target values are those of the original space on the
canonically inverse-relabeled original tests. -/
theorem space_obj (M : M9StandaloneDraft.Space ℂ) :
    (space M).obj = (Over.map ComplexULiftFunctionField.canonicalSpecIso.hom).op ⋙ M.obj := rfl

abbrev classifier {g : ℕ} {M : M9StandaloneDraft.Presheaves ℂ}
    (c : M9StandaloneDraft.Classifier ℂ g M) :
    M9StandaloneDraft.Classifier Coeff g (presheafForward baseIso M) :=
  classifierForward baseIso c

/-- Full all-test coarse semantics are transported once actually proved
for the original independently chosen space and its original classifier. -/
theorem isCoarse {g : ℕ} {M : M9StandaloneDraft.Presheaves ℂ}
    (c : M9StandaloneDraft.Classifier ℂ g M) (h : M9StandaloneDraft.IsCoarse ℂ c) :
    M9StandaloneDraft.IsCoarse Coeff (classifier c) :=
  StandaloneCoefficientGeometricTransport.isCoarse_forward
    (ULift.ringEquiv.symm : ℂ ≃+* Coeff) c h

theorem varietySpace (M : M9StandaloneDraft.Space ℂ)
    (h : M9StandaloneDraft.VarietySpace ℂ M) :
    M9StandaloneDraft.VarietySpace Coeff (space M) :=
  StandaloneCoefficientGeometryTransport.varietySpace_forward baseIso M h

theorem rationalOpen (n : ℕ) (M : M9StandaloneDraft.Presheaves ℂ)
    (h : M9StandaloneDraft.RationalOpen ℂ n M) :
    M9StandaloneDraft.RationalOpen Coeff n (presheafForward baseIso M) :=
  StandaloneCoefficientGeometryTransport.rationalOpen_forward baseIso n M h

end M9Native.ComplexStandaloneCoefficientTransport
