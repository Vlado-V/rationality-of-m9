module

public import M9StacksIntegration.NativeStackSpacePointTopology
public import M9StacksIntegration.ASClassifierGeometricLift
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.GeometricPoints

/-! Density through the genuine coarse universal homeomorphism.
The stack point set and the algebraic-space point set retain their actual
native topologies. Coverage hypotheses below are named intermediate
statements, to be discharged by the original curve construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeStackCoverageDenseImage

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Stack.AlgebraicStacks.{u, w} B S hS} {M : AlgebraicSpaces B S hS}

/-- The actual stack map on points followed by the actual inverse
algebraic-space/stack point homeomorphism. -/
def coarsePointMap
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property) :
    Stack.AlgebraicStacks.points B S hS X → Space.points B S hS M.obj := by
  letI := Space.pointTopology B S hS M.obj
  letI := Stack.pointTopology B S hS
    (Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property).val
  exact (NativeStackSpacePointTopology.pointsHomeomorphSpace.{u, w}
    B S hS M.obj M.property).symm ∘ Stack.AlgebraicStacks.pointsMap B S hS f

/-- Continuity uses the two native point topologies, without identifying
the two point sets. -/
theorem coarsePointMap_continuous
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property) :
    @Continuous _ _ (Stack.pointTopology B S hS X.val)
      (Space.pointTopology B S hS M.obj) (coarsePointMap B S hS f) := by
  let := Stack.pointTopology B S hS X.val
  let := Stack.pointTopology B S hS
    (Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property).val
  let := Space.pointTopology B S hS M.obj
  exact (NativeStackSpacePointTopology.pointsHomeomorphSpace.{u, w}
    B S hS M.obj M.property).symm.continuous.comp
      (Stack.continuous_pointsMap B S hS X.val
        (Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property).val f.hom.hom)

/-- Surjectivity is derived from the actual coarse universal
homeomorphism, through its genuine native point theorem. -/
theorem coarsePointMap_surjective
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Stack.UniversalHomeomorphism B S hS f) :
    Function.Surjective (coarsePointMap B S hS f) := by
  let := Space.pointTopology B S hS M.obj
  let := Stack.pointTopology B S hS
    (Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property).val
  exact (NativeStackSpacePointTopology.pointsHomeomorphSpace.{u, w}
    B S hS M.obj M.property).symm.surjective.comp
      (Stack.surjective_pointsMap_of_universalHomeomorphism B S hS hf)

/-- A dense source subset has dense image in the actual algebraic
space when the given coarse map is an actual universal homeomorphism. -/
theorem dense_coarse_image
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Stack.UniversalHomeomorphism B S hS f)
    (D : Set (Stack.AlgebraicStacks.points B S hS X))
    (hd : @Dense _ (Stack.pointTopology B S hS X.val) D) :
    @Dense _ (Space.pointTopology B S hS M.obj) (coarsePointMap B S hS f '' D) := by
  let := Stack.pointTopology B S hS X.val
  let := Space.pointTopology B S hS M.obj
  exact (coarsePointMap_surjective B S hS f hf).denseRange.dense_image
    (coarsePointMap_continuous B S hS f) hd

/-- Honest point coverage of a dense source locus suffices for density
of the actual algebraic-space morphism. -/
theorem denseRange_of_point_coverage
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Stack.UniversalHomeomorphism B S hS f)
    {N : AlgebraicSpaces B S hS} (g : N ⟶ M)
    (D : Set (Stack.AlgebraicStacks.points B S hS X))
    (hd : @Dense _ (Stack.pointTopology B S hS X.val) D)
    (hcover : ∀ z ∈ D, coarsePointMap B S hS f z ∈
      Set.range (Space.pointsMap B S hS N.obj g.hom)) :
    @DenseRange _ (Space.pointTopology B S hS M.obj) _
      (Space.pointsMap B S hS N.obj g.hom) := by
  let := Space.pointTopology B S hS N.obj
  let := Space.pointTopology B S hS M.obj
  exact (dense_coarse_image B S hS f hf D hd).mono (by
    rintro _ ⟨z, hz, rfl⟩
    exact hcover z hz)

/-- The genuine source-stack point attached to an actual classifier
and an actual field-valued point of its represented parameter scheme. -/
def classifierFieldPoint {U : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.val.val)
    (p : Space.FieldValuedPoint B S hS (schemeSpace U).obj) :
    Stack.FieldValuedPoint B S hS X.val.val where
  carrier := p.carrier
  field := p.field
  base := p.siteObject
  isSpec := Iso.refl _
  obj := A.toFunctor.obj (Over.mk p.value)
  «over» := Functor.congr_obj A.w (Over.mk p.value)

/-- An actual arrow between field objects gives equality of the
corresponding native stack points, by their actual common refinement. -/
theorem pointClass_eq_of_arrow
    (p q : Stack.FieldValuedPoint B S hS X.val.val) (a : p.obj ⟶ q.obj) :
    Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids p =
      Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids q :=
  (Stack.class_eq_class_iff_hasCommonExtension B S hS X.val.val
    X.val.isFiberedInGroupoids p q).2 ⟨p, ⟨𝟙 _⟩, ⟨a⟩⟩

end M9Native.NativeStackCoverageDenseImage
