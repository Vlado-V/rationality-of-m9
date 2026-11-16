module

public import M9.ProjectiveFrameAction
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The actual SL3 and PGL3 invariants of the original projective pair field

Every literal complex invertible matrix is a scalar multiple of an
actual determinant-one matrix.  The frozen original projective pair
action is trivial on scalar matrices.  Consequently restriction of
that same action to the native special linear group has exactly the
existing PGL3 fixed field.  The existing native quotient equivalence
is retained and transported along the proved equality of subfields.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

open scoped Classical Matrix

namespace M9Native.ProjectivePairSLFixedField

open M9.FrameFieldElimination M9.ProjectiveFrameQuotient M9.ProjectiveFrameAction

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℂ

/-- A genuine scalar normalization of each actual constant GL3
matrix to an actual determinant-one matrix. -/
theorem exists_scalar_normalization (g : GL3) :
    ∃ (a : ℂˣ) (s : SL3),
      Matrix.SpecialLinearGroup.toGL s = Matrix.GeneralLinearGroup.scalar (Fin 3) a * g := by
  let d := Matrix.GeneralLinearGroup.det g
  have hd : (d : ℂ) ≠ 0 := d.ne_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((d : ℂ)⁻¹) (n := 3) (by decide)
  have hc0 : c ≠ 0 := by
    intro hz
    exact (inv_ne_zero hd)
      (by simpa only [hz, zero_pow (n := 3) (by decide)] using hc.symm)
  let a : ℂˣ := Units.mk0 c hc0
  have hdet : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 3) a * g) = 1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    apply Units.ext
    change c ^ 3 * (d : ℂ) = 1
    rw [hc]
    exact inv_mul_cancel₀ hd
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) a * g ∈
      (Matrix.SpecialLinearGroup.toGL : SL3 →* GL3).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact MonoidHom.mem_ker.mpr hdet
  obtain ⟨s, hs⟩ := hmem
  exact ⟨a, s, hs⟩

/-- Scalar normalization preserves the literal frozen action on
the actual original projective pair field. -/
theorem projectiveAction_scalar_mul (a : ℂˣ) (g : GL3) (z : projectivePairField) :
    projectiveActionHom (Matrix.GeneralLinearGroup.scalar (Fin 3) a * g) z =
      projectiveActionHom g z := by
  rw [map_mul, RingAut.mul_apply]
  apply Subtype.ext
  rw [projectiveActionHom_val]
  exact scalar_projectivePair_fixed a (projectiveActionHom g z).val
    (projectiveActionHom g z).property

/-- Every actual constant GL3 field automorphism is the field
automorphism of an actual native SL3 element. -/
theorem exists_sl_same_projectiveAction (g : GL3) :
    ∃ s : SL3, projectiveActionHom (Matrix.SpecialLinearGroup.toGL s) =
      projectiveActionHom g := by
  obtain ⟨a, s, hs⟩ := exists_scalar_normalization g
  refine ⟨s, ?_⟩
  rw [hs]
  exact RingEquiv.ext (projectiveAction_scalar_mul a g)

/-- The restricted action uses the canonical native SL3-to-GL3
homomorphism and the exact frozen original action. -/
def slActionHom : SL3 →* (projectivePairField ≃+* projectivePairField) :=
  projectiveActionHom.comp Matrix.SpecialLinearGroup.toGL

@[simp] theorem slActionHom_apply (g : SL3) (z : projectivePairField) :
    slActionHom g z = projectiveActionHom (Matrix.SpecialLinearGroup.toGL g) z := rfl

@[instance_reducible] def slAction : MulSemiringAction SL3 projectivePairField :=
  MulSemiringAction.compHom projectivePairField slActionHom

attribute [local instance] slAction

/-- The actual SL3-fixed intermediate field inside the actual
original projective pair-frame field. -/
def slFixedField : IntermediateField ℂ projectivePairField where
  __ := FixedPoints.subfield SL3 projectivePairField
  algebraMap_mem' c g := by
    change slActionHom g (algebraMap ℂ projectivePairField c) = _
    apply Subtype.ext
    rw [slActionHom_apply, projectiveActionHom_val]
    exact pairAction_constant ℂ (Matrix.SpecialLinearGroup.toGL g) c

theorem mem_slFixedField_iff (z : projectivePairField) :
    z ∈ slFixedField ↔
      ∀ g : SL3, projectiveActionHom (Matrix.SpecialLinearGroup.toGL g) z = z := Iff.rfl

/-- Equality of the genuine two fixed intermediate fields; there
is no quotient-field equality premise. -/
theorem slFixedField_eq_pglFixedField : slFixedField = pglFixedField := by
  ext z
  rw [mem_slFixedField_iff, mem_pglFixedField_iff]
  constructor
  · intro hs g
    obtain ⟨s, he⟩ := exists_sl_same_projectiveAction g
    have hz : projectiveActionHom g z = z := by rw [← he]; exact hs s
    simpa only [projectiveActionHom_val] using congrArg Subtype.val hz
  · intro hg s
    apply Subtype.ext
    rw [projectiveActionHom_val]
    exact hg (Matrix.SpecialLinearGroup.toGL s)

/-- The original native PGL quotient equivalence, transported only
along the proved equality of the actual fixed intermediate fields. -/
def nativeSLQuotientEquiv : NativeMatrixField ≃ₐ[ℂ] slFixedField :=
  nativePGLQuotientEquiv.trans (IntermediateField.equivOfEq slFixedField_eq_pglFixedField.symm)

theorem nativeSLQuotientEquiv_val (x : NativeMatrixField) :
    (nativeSLQuotientEquiv x).val = (nativePGLQuotientEquiv x).val := rfl

theorem nativeSLQuotientEquiv_coordinateRatio (i : Fin 8) :
    ((nativeSLQuotientEquiv
      (M9.ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)).val : PF) =
        invariantMatrix ℂ (affineIndex i).1 (affineIndex i).2 /
          invariantMatrix ℂ pivotIndex.1 pivotIndex.2 :=
  nativePGLQuotientEquiv_coordinateRatio i

end M9Native.ProjectivePairSLFixedField
