module

public import M9StacksIntegration.Sp6AffinePoints
public import M9StacksIntegration.PrimitiveConstantFieldAction
public import M9StacksIntegration.NativeGenericFieldPoints
public import M9StacksIntegration.TensorEvaluationSeparation

@[expose] public section

/-! The actual universal Sp6 action over the original Grassmannian function field.
The parameter ring is the actual affine group algebra tensor the actual native
function field. All points and maps are obtained from the frozen scheme action.
No integrality or invariance is assumed in these constructions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace M9Native.PrimitiveUniversalFieldAction

open PrimitiveGrassmannianAction

abbrev A := Sp6AffinePoints.CoordinateRing ℂ
abbrev E := space.functionField
abbrev TensorRing := A ⊗[ℂ] E
abbrev parameter : Scheme := Spec (.of TensorRing)
abbrev fieldOver : Over PrimitiveFamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ E)
abbrev parameterOver : Over PrimitiveFamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ TensorRing)

/-- The actual affine morphism over the coefficient field of an algebra map. -/
def algebraSpecOver {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) :
    Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ S) ⟶
      Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ S))
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact φ.commutes c)

theorem algebraSpecOver_comp {R S T : Type}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ T]
    (φ : R →ₐ[ℂ] S) (ψ : S →ₐ[ℂ] T) :
    algebraSpecOver ψ ≫ algebraSpecOver φ = algebraSpecOver (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

theorem algebraSpecOver_id (R : Type) [CommRing R] [Algebra ℂ R] :
    algebraSpecOver (AlgHom.id ℂ R) = 𝟙 (Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ R)) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

/-- The actual generic point over the original complex base. -/
def genericOverPoint : fieldOver ⟶ overSpace :=
  NativeGenericFieldPoints.overPoint ℂ projection rfl (AlgHom.id ℂ E)

@[simp]
theorem genericOverPoint_left : genericOverPoint.left = NativeFunctionFieldFunctor.genericSpec space := by
  change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫
    NativeFunctionFieldFunctor.genericSpec space = _
  change Spec.map (𝟙 space.functionField) ≫ NativeFunctionFieldFunctor.genericSpec space = _
  exact (congrArg (fun q : Spec space.functionField ⟶ Spec space.functionField =>
    q ≫ NativeFunctionFieldFunctor.genericSpec space) (Spec.map_id space.functionField)).trans
      (Category.id_comp _)

/-- The actual universal group point over the tensor parameter. -/
def universalGroup : parameterOver ⟶ group :=
  Sp6AffinePoints.point ℂ (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing)

/-- The actual original generic Grassmannian point pulled to the tensor parameter. -/
def universalX : parameterOver ⟶ overSpace :=
  algebraSpecOver (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) ≫ genericOverPoint

/-- The actual universal action, from the frozen native action morphism. -/
def actionOver : parameterOver ⟶ overSpace :=
  lift universalGroup universalX ≫ nativeAction.act

def actionMap : parameter ⟶ space := actionOver.left
def projectionMap : parameter ⟶ space := universalX.left

/-- Actual scalar evaluation at a constant group-algebra point. -/
def slice (χ : A →ₐ[ℂ] ℂ) : fieldOver ⟶ parameterOver :=
  algebraSpecOver (TensorEvaluationSeparation.algebraEvaluate (E := E) χ)

/-- Constant evaluation leaves the original generic Grassmannian point fixed. -/
theorem slice_projection (χ : A →ₐ[ℂ] ℂ) : slice χ ≫ universalX = genericOverPoint := by
  rw [slice, universalX, ← Category.assoc, algebraSpecOver_comp]
  have he : (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).comp
      (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) = AlgHom.id ℂ E := by
    ext e
    simp
  rw [he, algebraSpecOver_id, Category.id_comp]

theorem slice_projection_left (χ : A →ₐ[ℂ] ℂ) :
    (slice χ).left ≫ projectionMap = NativeFunctionFieldFunctor.genericSpec space := by
  have he := congrArg (fun p : fieldOver ⟶ overSpace => p.left) (slice_projection χ)
  exact he.trans genericOverPoint_left

end M9Native.PrimitiveUniversalFieldAction
