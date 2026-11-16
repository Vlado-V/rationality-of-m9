module

public import M9StacksIntegration.PrimitiveUniversalFieldAction
public import M9StacksIntegration.Sp6AffineExtensionPoints

@[expose] public section

/-! Actual arbitrary extension-field action points of the universal tensor source.
The parameter point is constructed from the original native group point and
the original coefficient-preserving generic field embedding. The action and
projection squares are proved from the original native morphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace M9Native.PrimitiveUniversalExtensionPoints

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction

abbrev overField (L : Type) [Field L] [Algebra ℂ L] : Over PrimitiveFamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ L)

/-- Algebra-point formation is naturally the original native group-point formation. -/
theorem groupPoint_natural {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (φ : A →ₐ[ℂ] R) (ψ : R →ₐ[ℂ] S) :
    algebraSpecOver ψ ≫ Sp6AffinePoints.point ℂ φ = Sp6AffinePoints.point ℂ (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (Sp6AffineBaseChange.affineIso ℂ).hom) =
    Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom) ≫ (Sp6AffineBaseChange.affineIso ℂ).hom
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable {L : Type} [Field L] [Algebra ℂ L]

/-- The actual tensor algebra point attached to the native group point and
the original generic field embedding. -/
def parameterAlgebra (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) : TensorRing →ₐ[ℂ] L :=
  Algebra.TensorProduct.lift (Sp6AffineExtensionPoints.algebraOfPoint ℂ L g) s
    (fun _ _ => Commute.all _ _)

theorem parameterAlgebra_left (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    (parameterAlgebra g s).comp (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing) =
      Sp6AffineExtensionPoints.algebraOfPoint ℂ L g := by
  ext a
  simp [parameterAlgebra]

theorem parameterAlgebra_right (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    (parameterAlgebra g s).comp (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) = s := by
  ext e
  simp [parameterAlgebra]

def parameterPoint (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) : overField L ⟶ parameterOver :=
  algebraSpecOver (parameterAlgebra g s)

/-- The genuine universal group coordinate recovers the original native group point. -/
theorem parameterPoint_group (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    parameterPoint g s ≫ universalGroup = g := by
  change algebraSpecOver (parameterAlgebra g s) ≫
    Sp6AffinePoints.point ℂ (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing) = _
  rw [groupPoint_natural, parameterAlgebra_left]
  exact Sp6AffineExtensionPoints.point_algebraOfPoint ℂ L g

/-- The genuine universal variety coordinate recovers the original generic point. -/
theorem parameterPoint_projection (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    parameterPoint g s ≫ universalX =
      NativeGenericFieldPoints.overPoint ℂ projection rfl s := by
  rw [parameterPoint, universalX, ← Category.assoc, algebraSpecOver_comp, parameterAlgebra_right]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ genericOverPoint.left =
    Spec.map (CommRingCat.ofHom s.toRingHom) ≫ NativeFunctionFieldFunctor.genericSpec space
  exact congrArg (fun q : fieldOver.left ⟶ space => Spec.map (CommRingCat.ofHom s.toRingHom) ≫ q)
    genericOverPoint_left

theorem parameterPoint_projection_left (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    (parameterPoint g s).left ≫ projectionMap = NativeGenericPullbackEvaluation.point s.toRingHom := by
  have he := congrArg (fun q : overField L ⟶ overSpace => q.left) (parameterPoint_projection g s)
  exact he

/-- The original action relation is the literal universal action square. -/
theorem parameterPoint_action (g : overField L ⟶ group) (s : E →ₐ[ℂ] L) :
    parameterPoint g s ≫ actionOver =
      lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act := by
  change parameterPoint g s ≫ (lift universalGroup universalX ≫ nativeAction.act) = _
  rw [nativeAction.comp_smul, parameterPoint_group, parameterPoint_projection]

/-- The actual extension-field action relation binds the second original
generic field point, with no coordinate or denominator replacement. -/
theorem parameterPoint_action_of_relation (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    (parameterPoint g s).left ≫ actionMap = NativeGenericPullbackEvaluation.point t.toRingHom := by
  have he := congrArg (fun q : overField L ⟶ overSpace => q.left) (parameterPoint_action g s)
  exact he.trans ht

end M9Native.PrimitiveUniversalExtensionPoints
