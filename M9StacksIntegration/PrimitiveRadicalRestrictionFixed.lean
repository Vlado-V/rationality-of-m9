module

public import M9StacksIntegration.PrimitiveReducedFamilyComparison
public import M9StacksIntegration.PrimitiveRadicalEquivariantKernelPairs
public import M9StacksIntegration.PrimitiveRadicalSourceActionValues
public import M9StacksIntegration.PrimitiveRadicalSliceExtension
public import M9StacksIntegration.ReducedGraphTwistedAction

@[expose] public section

/-! The genuine invariant restriction has image in the actual native
stabilizer fixed field. The coefficient-field automorphism is extended
through the actual tensor localization, and the actual reduced relation
lifts to the actual symplectic action. No field comparison is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace M9Native.PrimitiveRadicalRestrictionFixed
open PrimitiveRadicalInvariantDescent PrimitiveRadicalSliceField
open PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitGenericPoints
open PrimitiveReducedFieldMatrixAction PrimitiveReducedFieldMatrixComposition
open NativeGenericPullbackEvaluation

local instance sourceCharZero : CharZero sourceField := PrimitiveExtensionFieldBridge.charZero_extension sourceField

theorem restriction_fixed (f : nativeFixedField) :
    restriction f ∈ ReducedGraphTwistedAction.nativeHFixedField := by
  apply (ReducedGraphTwistedAction.mem_nativeHFixedField_iff _).mpr
  intro w
  let σ := ReducedGraphAction.nativeFieldRepresentation ℂ w
  let e := PrimitiveRadicalSliceExtension.sourceExtension σ
  let s : sourceField →ₐ[ℂ] sourceField := AlgHom.id ℂ sourceField
  let t : sourceField →ₐ[ℂ] sourceField := e.toAlgHom
  let y := sourcePoint sourceField s
  let z := sourcePoint sourceField t
  let v := PrimitiveReducedFamilyComparison.extendConstant sourceField w
  have he : t.comp sliceEmbedding = sliceEmbedding.comp σ.toAlgHom := by
    apply AlgHom.ext
    intro x
    exact PrimitiveRadicalSliceExtension.sourceExtension_slice σ x
  have ha : fieldAction sourceField (ReducedGraphAction.matrixRepresentation sourceField v)
      (PrimitiveRhoGraphNativePoints.point sourceField (rightPoint sourceField y)) =
    PrimitiveRhoGraphNativePoints.point sourceField (rightPoint sourceField z) := by
    rw [← PrimitiveReducedFamilyComparison.extendConstant_matrix,slicePoint_sourcePoint,slicePoint_sourcePoint]
    change fieldAction sourceField (Matrix.GeneralLinearGroup.map (algebraMap ℂ sourceField)
      (ReducedGraphAction.matrixRepresentation ℂ w)) (point sliceEmbedding.toRingHom) =
        point (t.comp sliceEmbedding).toRingHom
    rw [he]
    exact fieldAction_constant_genericPoint sourceField (ReducedGraphAction.matrixRepresentation ℂ w) sliceEmbedding
  have hr := PrimitiveReducedFamilyComparison.graph_ranges_of_fieldAction sourceField
    (ReducedGraphAction.matrixRepresentation sourceField v) (rightPoint sourceField y) (rightPoint sourceField z) ha
  have hr' : (Matrix.toLin' (graphAt sourceField z)).range =
      ((Matrix.toLin' (graphAt sourceField y)).range).map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation sourceField v⁻¹).val) := by
    simpa only [map_inv,graphAt] using hr
  obtain ⟨g,hg⟩ := PrimitiveRadicalEquivariantKernelPairs.exists_native_action_of_graph_relation
    sourceField v⁻¹ y z hr'
  have hv := PrimitiveRadicalSourceActionValues.eq_of_native_action f.val
    ((mem_nativeFixedField_iff f.val).mp f.property) g s t hg
  change σ (restriction f) = restriction f
  apply sliceEmbedding.injective
  change sliceEmbedding (σ (restriction f)) = sliceEmbedding (restriction f)
  calc
    sliceEmbedding (σ (restriction f)) = e (sliceEmbedding (restriction f)) :=
      (PrimitiveRadicalSliceExtension.sourceExtension_slice σ (restriction f)).symm
    _ = e (PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val) := by rw [restriction_spec]
    _ = PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val := hv.symm
    _ = sliceEmbedding (restriction f) := (restriction_spec f).symm

/-- The actual native symplectic invariant field embeds in the actual native
stabilizer invariant field, preserving the original restriction map. -/
def toStabilizerFixed : nativeFixedField →ₐ[ℂ] ReducedGraphTwistedAction.nativeHFixedField where
  toFun f := ⟨restriction f,restriction_fixed f⟩
  map_zero' := Subtype.ext (map_zero restriction)
  map_one' := Subtype.ext (map_one restriction)
  map_add' f g := Subtype.ext (map_add restriction f g)
  map_mul' f g := Subtype.ext (map_mul restriction f g)
  commutes' c := Subtype.ext (restriction.commutes c)

theorem toStabilizerFixed_val (f : nativeFixedField) : (toStabilizerFixed f).val = restriction f := rfl

theorem toStabilizerFixed_spec (f : nativeFixedField) :
    sliceEmbedding (toStabilizerFixed f).val =
      PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val := restriction_spec f

end M9Native.PrimitiveRadicalRestrictionFixed
