module

public import M9StacksIntegration.ConicCompatibleGraphCoordinates

/-! The actual full stabilizer action on the determinant-twisted generic graph
field in the conic-compatible chart. The native original action is connected
by the proved actual native scheme change of basis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace M9Native.ConicCompatibleTwistedAction

open ReducedGraphAction ReducedGraphCenter
abbrev H := ReducedGraphAction.Stabilizer ℂ
abbrev FF := ReducedGraphCenter.FF
abbrev NativeField := ReducedGraphCenter.NativeField
abbrev Roots := ReducedGraphCenter.Roots

theorem nativeCentral_preserved (w : H) (z : NativeField) (hz : z ∈ nativeCentralFixedField) :
    ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w z ∈ nativeCentralFixedField := by
  rw [mem_nativeCentralFixedField_iff] at hz ⊢
  intro a
  obtain ⟨b, hb⟩ := ReducedGraphTwistedAction.center_mul a w
  rw [← ConicCompatibleGraphCoordinates.nativeField_center_eq a]
  change ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ (ReducedGraphTwistedAction.centerHom a) (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w z) = _
  rw [← AlgEquiv.mul_apply, ← map_mul, hb, map_mul, AlgEquiv.mul_apply]
  have hbfix : ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ (centralElement b) z = z := by
    rw [ConicCompatibleGraphCoordinates.nativeField_center_eq]
    exact hz b
  exact congrArg (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w) hbfix

/-- Literal restriction of the full actual native stabilizer representation. -/
def centralRestriction (w : H) : nativeCentralFixedField ≃ₐ[ℂ] nativeCentralFixedField where
  toFun z := ⟨ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w z.val, nativeCentral_preserved w z.val z.property⟩
  invFun z := ⟨ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w⁻¹ z.val, nativeCentral_preserved w⁻¹ z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    change ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w⁻¹ (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w z.val) = z.val
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv z := by
    apply Subtype.ext
    change ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w⁻¹ z.val) = z.val
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' z v := Subtype.ext (map_mul (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w) z.val v.val)
  map_add' z v := Subtype.ext (map_add (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w) z.val v.val)
  commutes' c := Subtype.ext ((ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w).commutes c)

def centralRepresentation : H →* (nativeCentralFixedField ≃ₐ[ℂ] nativeCentralFixedField) where
  toFun := centralRestriction
  map_one' := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ 1 z.val = z.val
    rw [map_one]
    rfl
  map_mul' w v := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ (w * v) z.val =
      ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ v z.val)
    rw [map_mul]
    rfl

/-- Actual action on determinant-twisted generic coordinates, obtained from
its genuine native central fixed-field quotient. The group remains SL3 semidirect C2. -/
def twistedFieldRepresentation : H →* (FF ≃ₐ[ℂ] FF) :=
  (AlgEquiv.autCongr nativeDeterminantQuotient.symm).toMonoidHom.comp centralRepresentation

theorem twistedFieldRepresentation_quotient (w : H) (z : FF) :
    (nativeDeterminantQuotient (twistedFieldRepresentation w z)).val =
      ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w (nativeDeterminantQuotient z).val := by
  change (nativeDeterminantQuotient
    (nativeDeterminantQuotient.symm (centralRestriction w (nativeDeterminantQuotient z)))).val = _
  exact congrArg Subtype.val
    (nativeDeterminantQuotient.apply_symm_apply (centralRestriction w (nativeDeterminantQuotient z)))

theorem mem_fixedField_range_iff {k L G : Type*} [Field k] [Field L] [Algebra k L]
    [Group G] (ρ : G →* (L ≃ₐ[k] L)) (z : L) :
    z ∈ IntermediateField.fixedField ρ.range ↔ ∀ w : G, ρ w z = z := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h w
    exact h (ρ w) ⟨w, rfl⟩
  · rintro h σ ⟨w, rfl⟩
    exact h w

/-- Full actual stabilizer invariants of the original native Gr4(12) field. -/
def nativeHFixedField : IntermediateField ℂ NativeField :=
  IntermediateField.fixedField (ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ).range

/-- Full actual stabilizer invariants after the genuine determinant quotient. -/
def twistedHFixedField : IntermediateField ℂ FF :=
  IntermediateField.fixedField twistedFieldRepresentation.range

theorem mem_nativeHFixedField_iff (z : NativeField) : z ∈ nativeHFixedField ↔
    ∀ w : H, ConicCompatibleGraphCoordinates.nativeFieldRepresentation ℂ w z = z := mem_fixedField_range_iff _ _

theorem mem_twistedHFixedField_iff (z : FF) : z ∈ twistedHFixedField ↔
    ∀ w : H, twistedFieldRepresentation w z = z := mem_fixedField_range_iff _ _

def fullToCentral : nativeHFixedField →ₐ[ℂ] nativeCentralFixedField where
  toFun z := ⟨z.val, (mem_nativeCentralFixedField_iff z.val).mpr (fun a =>
    by
      rw [← ConicCompatibleGraphCoordinates.nativeField_center_eq a]
      exact (mem_nativeHFixedField_iff z.val).mp z.property (centralElement a))⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

def toTwistedAux : nativeHFixedField →ₐ[ℂ] FF :=
  nativeDeterminantQuotient.symm.toAlgHom.comp fullToCentral

theorem toTwistedAux_fixed (z : nativeHFixedField) : toTwistedAux z ∈ twistedHFixedField := by
  apply (mem_twistedHFixedField_iff _).mpr
  intro w
  apply nativeDeterminantQuotient.injective
  apply Subtype.ext
  have hq : nativeDeterminantQuotient (toTwistedAux z) = fullToCentral z :=
    nativeDeterminantQuotient.apply_symm_apply (fullToCentral z)
  rw [twistedFieldRepresentation_quotient, hq]
  exact (mem_nativeHFixedField_iff z.val).mp z.property w

def toTwistedFixed : nativeHFixedField →ₐ[ℂ] twistedHFixedField where
  toFun z := ⟨toTwistedAux z, toTwistedAux_fixed z⟩
  map_zero' := Subtype.ext (map_zero toTwistedAux)
  map_one' := Subtype.ext (map_one toTwistedAux)
  map_add' z v := Subtype.ext (map_add toTwistedAux z v)
  map_mul' z v := Subtype.ext (map_mul toTwistedAux z v)
  commutes' c := Subtype.ext (toTwistedAux.commutes c)

theorem toTwistedFixed_surjective : Function.Surjective toTwistedFixed := by
  intro y
  have hy : (nativeDeterminantQuotient y.val).val ∈ nativeHFixedField := by
    apply (mem_nativeHFixedField_iff _).mpr
    intro w
    rw [← twistedFieldRepresentation_quotient]
    exact congrArg (fun z : FF => (nativeDeterminantQuotient z).val)
      ((mem_twistedHFixedField_iff y.val).mp y.property w)
  let x : nativeHFixedField := ⟨(nativeDeterminantQuotient y.val).val, hy⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change nativeDeterminantQuotient.symm (fullToCentral x) = y.val
  have hx : fullToCentral x = nativeDeterminantQuotient y.val := Subtype.ext rfl
  rw [hx, AlgEquiv.symm_apply_apply]

/-- The original full native stabilizer fixed field is exactly the full fixed
field of the actual determinant-twisted graph action. -/
def nativeFullFixedEquiv : nativeHFixedField ≃ₐ[ℂ] twistedHFixedField :=
  AlgEquiv.ofBijective toTwistedFixed ⟨toTwistedFixed.injective, toTwistedFixed_surjective⟩

theorem nativeFullFixedEquiv_quotient (z : nativeHFixedField) :
    (nativeDeterminantQuotient (nativeFullFixedEquiv z).val).val = z.val :=
  congrArg Subtype.val (nativeDeterminantQuotient.apply_symm_apply (fullToCentral z))

/-- The exact original native reduced-Grassmannian invariant field, through
the genuine basis change and the proved actual determinant quotient. -/
def originalNativeFullFixedEquiv :
    ReducedGraphTwistedAction.nativeHFixedField ≃ₐ[ℂ] twistedHFixedField :=
  ConicCompatibleGraphCoordinates.basisFixedEquiv.symm.trans nativeFullFixedEquiv

end M9Native.ConicCompatibleTwistedAction
