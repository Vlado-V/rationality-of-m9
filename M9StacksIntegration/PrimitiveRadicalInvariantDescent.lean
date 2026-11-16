module

public import M9StacksIntegration.PrimitiveRadicalSliceField
public import M9StacksIntegration.PrimitiveFieldMatrixAction
public import M9StacksIntegration.PrimitiveGeometricExtensionInvariance
public import M9StacksIntegration.FieldPointDescentGeometric

@[expose] public section

/-! Effective descent of actual native symplectic invariant functions through
the actual reduced-Grassmannian field embedding. The genuine native group
coordinate geometry and all geometric kernel-pair tests are proved; no field
comparison, orbit section, or universal invariance statement is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open MonoidalCategory CartesianMonoidalCategory
open scoped Classical Matrix CategoryTheory.MonObj

namespace M9Native.PrimitiveRadicalInvariantDescent
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitKernelPoints
open PrimitiveRadicalOrbitGenericPoints PrimitiveRadicalSliceField
open PrimitiveGrassmannianAction PrimitiveUniversalExtensionPoints
open NativeGenericPullbackEvaluation

abbrev targetField := (GrassmannianCharts.space ℂ 9 14).functionField
abbrev sourceField := PrimitiveRadicalOrbitFamily.source.functionField
abbrev sliceField := (GrassmannianCharts.space ℂ 4 12).functionField

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

/-- The group element is the literal relative transformation of the two
actual evaluated Gauss families. -/
def relativeGroup (s t : sourceField →ₐ[ℂ] K) : Sp6 K :=
  originalGroupAt K (sourcePoint K t) * (originalGroupAt K (sourcePoint K s))⁻¹

/-- Agreement on the actual reduced native field gives the genuine native
group-action equality between the actual target generic points. -/
theorem native_action_of_slice_embeddings_eq (s t : sourceField →ₐ[ℂ] K)
    (h : s.comp sliceEmbedding = t.comp sliceEmbedding) :
    (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint (relativeGroup K s t))
      (NativeGenericFieldPoints.overPoint ℂ PrimitiveGrassmannianAction.projection rfl
        (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding)) ≫ nativeAction.act).left =
      point (t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding).toRingHom := by
  let ys := sourcePoint K s
  let yt := sourcePoint K t
  have hk : kernelAt K yt = (kernelAt K ys).map (primitiveLinear K (relativeGroup K s t)).toLinearMap := by
    rw [kernelAt_eq_planeAt,kernelAt_eq_planeAt]
    exact congrArg (fun U : RankEightNinePlanes K => U.val)
      (planeAt_relation_of_slice_embeddings_eq K s t h)
  have ha := PrimitiveFieldMatrixAction.actPoint_eq_of_original_kernel_transport K
    (relativeGroup K s t) (nativePoint K ys) (nativePoint K yt)
    (nativePoint_projection K ys) (nativePoint_projection K yt)
    (quotientAt K ys) (quotientAt K yt) (quotientAt_surjective K ys) (quotientAt_surjective K yt)
    (nativePoint_class K ys) (nativePoint_class K yt) hk
  have hp : PrimitiveFieldMatrixAction.overPoint K (nativePoint K ys) (nativePoint_projection K ys) =
      NativeGenericFieldPoints.overPoint ℂ PrimitiveGrassmannianAction.projection rfl
        (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) := by
    apply Over.OverMorphism.ext
    exact nativePoint_sourcePoint K s
  change (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint (relativeGroup K s t))
    (PrimitiveFieldMatrixAction.overPoint K (nativePoint K ys) (nativePoint_projection K ys)) ≫
      nativeAction.act).left = nativePoint K yt at ha
  rw [hp] at ha
  exact ha.trans (nativePoint_sourcePoint K t)

section EffectiveDescent

/-- Constant native Sp6 invariance gives equality on the actual field-theoretic
slice kernel pair, through the proved genuine group action. -/
theorem invariant_equal_on_slice_kernel_pair (f : targetField)
    (hf : ∀ g : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback g f = f)
    (s t : sourceField →ₐ[ℂ] K) (h : s.comp sliceEmbedding = t.comp sliceEmbedding) :
    s (PrimitiveRadicalOrbitDominance.functionFieldEmbedding f) =
      t (PrimitiveRadicalOrbitDominance.functionFieldEmbedding f) := by
  exact PrimitiveGeometricExtensionInvariance.eq_of_original_action f hf
    (relativeGroup K s t)
    (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding)
    (t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding)
    (native_action_of_slice_embeddings_eq K s t h)

/-- The actual invariant pullback belongs to the actual native reduced field
image. All geometric field-point tests are discharged by the actual family
and its intrinsic radical/fiber comparison. -/
theorem invariant_mem_slice_image (f : targetField)
    (hf : ∀ g : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback g f = f) :
    PrimitiveRadicalOrbitDominance.functionFieldEmbedding f ∈ Set.range sliceEmbedding := by
  let : Algebra sliceField sourceField := sliceEmbedding.toRingHom.toAlgebra
  have : IsScalarTower ℂ sliceField sourceField :=
    IsScalarTower.of_algebraMap_eq' sliceEmbedding.comp_algebraMap.symm
  have : CharZero sliceField := PrimitiveExtensionFieldBridge.charZero_extension sliceField
  change PrimitiveRadicalOrbitDominance.functionFieldEmbedding f ∈
    Set.range (algebraMap sliceField sourceField)
  apply (FieldPointDescent.mem_range_iff_forall_algClosed_embeddings_charZero sliceField _).mpr
  intro L _ _ _ s t
  let : Algebra ℂ L :=
    ((algebraMap sliceField L).comp (algebraMap ℂ sliceField)).toAlgebra
  have : IsScalarTower ℂ sliceField L := IsScalarTower.of_algebraMap_eq' rfl
  let sC : sourceField →ₐ[ℂ] L := s.restrictScalars ℂ
  let tC : sourceField →ₐ[ℂ] L := t.restrictScalars ℂ
  have he : sC.comp sliceEmbedding = tC.comp sliceEmbedding := by
    apply AlgHom.ext
    intro x
    exact (s.commutes x).trans (t.commutes x).symm
  exact invariant_equal_on_slice_kernel_pair L f hf sC tC he

end EffectiveDescent

/-- The fixed field is that of the actual original constant symplectic action
on the actual native Grassmannian generic stalk. -/
def nativeFixedField : IntermediateField ℂ targetField :=
  IntermediateField.fixedField PrimitiveConstantFieldAction.fieldAction.range

theorem mem_nativeFixedField_iff (f : targetField) : f ∈ nativeFixedField ↔
    ∀ g : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback g f = f := by
  rw [nativeFixedField,IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    apply (PrimitiveConstantFieldAction.fixed_iff_pullback_fixed f).mp
    intro g
    exact h (PrimitiveConstantFieldAction.fieldAction g) ⟨g,rfl⟩
  · intro h σ hσ
    obtain ⟨g,rfl⟩ := hσ
    exact (PrimitiveConstantFieldAction.fixed_iff_pullback_fixed f).mpr h g

/-- The value is uniquely determined by the two genuine scheme-induced
field embeddings, without evaluating a rational function on a non-generic fiber. -/
def descendedValue (f : nativeFixedField) : sliceField :=
  Classical.choose (invariant_mem_slice_image f.val ((mem_nativeFixedField_iff f.val).mp f.property))

theorem descendedValue_spec (f : nativeFixedField) :
    sliceEmbedding (descendedValue f) = PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val :=
  Classical.choose_spec (invariant_mem_slice_image f.val ((mem_nativeFixedField_iff f.val).mp f.property))

/-- Genuine restriction of the native symplectic invariant field to the native
reduced Grassmannian field. Its inclusion in the true stabilizer fixed field
and surjectivity are separate remaining assertions. -/
def restriction : nativeFixedField →ₐ[ℂ] sliceField where
  toFun := descendedValue
  map_zero' := by
    apply sliceEmbedding.injective
    change sliceEmbedding (descendedValue 0) = sliceEmbedding 0
    rw [descendedValue_spec,IntermediateField.coe_zero,map_zero,map_zero]
  map_one' := by
    apply sliceEmbedding.injective
    change sliceEmbedding (descendedValue 1) = sliceEmbedding 1
    rw [descendedValue_spec,IntermediateField.coe_one,map_one,map_one]
  map_add' f g := by
    apply sliceEmbedding.injective
    calc
      sliceEmbedding (descendedValue (f+g)) =
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding (f+g).val := descendedValue_spec _
      _ = PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val +
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding g.val :=
        map_add PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val g.val
      _ = sliceEmbedding (descendedValue f + descendedValue g) := by
        rw [map_add,descendedValue_spec,descendedValue_spec]
  map_mul' f g := by
    apply sliceEmbedding.injective
    calc
      sliceEmbedding (descendedValue (f*g)) =
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding (f*g).val := descendedValue_spec _
      _ = PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val *
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding g.val :=
        map_mul PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val g.val
      _ = sliceEmbedding (descendedValue f * descendedValue g) := by
        rw [map_mul,descendedValue_spec,descendedValue_spec]
  commutes' c := by
    apply sliceEmbedding.injective
    change sliceEmbedding (descendedValue (algebraMap ℂ nativeFixedField c)) =
      sliceEmbedding (algebraMap ℂ sliceField c)
    rw [descendedValue_spec,sliceEmbedding.commutes]
    exact PrimitiveRadicalOrbitDominance.functionFieldEmbedding.commutes c

theorem restriction_spec (f : nativeFixedField) :
    sliceEmbedding (restriction f) = PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val :=
  descendedValue_spec f

theorem restriction_injective : Function.Injective restriction := restriction.injective

end M9Native.PrimitiveRadicalInvariantDescent
