module

public import M9StacksIntegration.PrimitiveRadicalFixedFieldComparison
public import M9StacksIntegration.ConicNativeFullFixedField

@[expose] public section

/-! Rationality of the actual native primitive Gr9(14) Sp6-invariant
function field. This is an algebraic Grassmannian quotient component,
without a moduli-space or coarse-space identification. -/

noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace M9Native.PrimitiveNativeInvariantRationality

abbrev NativeFixedField := PrimitiveRadicalInvariantDescent.nativeFixedField
abbrev Rational24 := M9.RationalField ℂ 24

/-- The original native primitive Grassmannian Sp6 fixed field is rational
in twenty-four variables over its original complex coefficient field. -/
def rationalEquiv : NativeFixedField ≃ₐ[ℂ] Rational24 :=
  PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv.trans
    ConicNativeFullFixedField.rationalEquiv

theorem rationalEquiv_apply (f : NativeFixedField) :
    rationalEquiv f = ConicNativeFullFixedField.rationalEquiv
      (PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv f) :=
  AlgEquiv.trans_apply PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv
    ConicNativeFullFixedField.rationalEquiv f

theorem rationalEquiv_symm_apply (t : Rational24) :
    rationalEquiv.symm t = PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv.symm
      (ConicNativeFullFixedField.rationalEquiv.symm t) :=
  AlgEquiv.symm_trans_apply PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv
    ConicNativeFullFixedField.rationalEquiv t

/-- The actual original complex coefficient inclusion is retained. -/
theorem rationalEquiv_coefficient (c : ℂ) :
    rationalEquiv (algebraMap ℂ NativeFixedField c) = algebraMap ℂ Rational24 c :=
  rationalEquiv.commutes c

theorem rationalEquiv_symm_coefficient (c : ℂ) :
    rationalEquiv.symm (algebraMap ℂ Rational24 c) = algebraMap ℂ NativeFixedField c :=
  rationalEquiv.symm.commutes c

/-- Forward coordinates still obey the original actual radical/fiber
pullback equality inside the native orbit-family source field. -/
theorem rationalEquiv_pullback (f : NativeFixedField) :
    PrimitiveRadicalSliceField.sliceEmbedding
      (ConicNativeFullFixedField.rationalEquiv.symm (rationalEquiv f)).val =
      PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val := by
  rw [rationalEquiv_apply, AlgEquiv.symm_apply_apply]
  exact PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv_spec f

/-- The inverse rational parametrization retains that same literal
native source-field pullback chain. -/
theorem rationalEquiv_inverse_pullback (t : Rational24) :
    PrimitiveRadicalSliceField.sliceEmbedding
      (ConicNativeFullFixedField.rationalEquiv.symm t).val =
      PrimitiveRadicalOrbitDominance.functionFieldEmbedding (rationalEquiv.symm t).val := by
  have h := PrimitiveRadicalFixedFieldComparison.nativeFixedEquiv_spec (rationalEquiv.symm t)
  rw [rationalEquiv_symm_apply, AlgEquiv.apply_symm_apply] at h
  exact h

end M9Native.PrimitiveNativeInvariantRationality
