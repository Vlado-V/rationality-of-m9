module

public import M9StacksIntegration.CurveFieldTargetComparison
public import M9StacksIntegration.FiberedClassifierCartesianValue
public import StacksFrontier.Deformation.Artin.Predeformation.FormallyEtale

/-!
# The actual ground-field Curves classifier of an original family

An original family may have an algebraic-space total space. Its specified
map to the ground field gives a genuine object in the native base change
of Curves. The native two-Yoneda classifier evaluates to that same object,
and its projection evaluates to the original family. No family comparison
or scheme-total hypothesis is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation.Artin
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u
namespace M9Native.CurveFieldClassifyingFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)

/-- The exact ground-field Curves stack of the original native base change. -/
abbrev fieldStack := CurveFieldTargetComparison.fieldStack B hZ hK hAlg

/-- The actual projection back to the original small Curves model. -/
abbrev smallProjection :=
  Stack.algebraicStackBaseChangeProjection B (Spec (.of K)) integerBase hK hZ
    (CurveFieldTargetComparison.baseArrow B hZ hK)
    (CurveFieldTargetComparison.integerStack B hZ hAlg)

/-- The projection to the original category of curve families. -/
abbrev originalProjection := smallProjection B hZ hK hAlg ⋙
  (curvesSmallEquivalenceOver B hZ).inv.functor

variable (Q : CurveFamily B hZ)
  (s : B.inclusion.obj Q.base.left ⟶ Spec (.of K))

/-- The original base, now with its specified ground-field structure. -/
abbrev fieldBase : BigFppfOver B (Spec (.of K)) hK :=
  Over.mk (ObjectProperty.homMk s)

/-- The same original family in the native small model. -/
abbrev smallFamily := (curvesSmallEquivalenceOver B hZ).hom.functor.obj Q

/-- Its integer structure map is exactly the one induced by the actual
map to the ground field, by the true terminality of the integer spectrum. -/
theorem smallFamily_lies_over :
    ((CurveFieldTargetComparison.integerStack B hZ hAlg).val.val.p ⋙
        Over.post B.inclusion).obj (smallFamily B hZ Q) =
      (Over.map (B.inclusion.map (CurveFieldTargetComparison.baseArrow B hZ hK))).obj
        ((Over.post B.inclusion).obj (fieldBase B hZ hK Q s)) := by
  have h := congrArg (Over.post B.inclusion).obj
    (Functor.congr_obj (curvesSmallEquivalenceOver B hZ).hom.w Q)
  change _ = (Over.post B.inclusion).obj Q.base at h
  refine h.trans ?_
  change Over.mk (B.inclusion.map Q.base.hom) =
    Over.mk (s ≫ B.inclusion.map (CurveFieldTargetComparison.baseArrow B hZ hK))
  congr 1
  exact specULiftZIsTerminal.hom_ext _ _

/-- The native factor of the original family through the true ground base. -/
def fieldFactor :=
  Stack.algebraicStackBaseChangeFactor B (Spec (.of K)) integerBase hK hZ
    (CurveFieldTargetComparison.baseArrow B hZ hK)
    (CurveFieldTargetComparison.integerStack B hZ hAlg) (smallFamily B hZ Q)
    ((Over.post B.inclusion).obj (fieldBase B hZ hK Q s))
    (smallFamily_lies_over B hZ hK hAlg Q s)

/-- The original (possibly nonschematic) family as an object over the
actual ground field. -/
def fieldFamily : (fieldStack B hZ hK hAlg).val.val.obj :=
  Stack.algebraicStackBaseChangeLift B (Spec (.of K)) integerBase hK hZ
    (CurveFieldTargetComparison.baseArrow B hZ hK)
    (CurveFieldTargetComparison.integerStack B hZ hAlg) (smallFamily B hZ Q)
    (fieldFactor B hZ hK hAlg Q s)

/-- Its exact original small-family projection. -/
theorem fieldFamily_smallProjection :
    (smallProjection B hZ hK hAlg).obj (fieldFamily B hZ hK hAlg Q s) =
      smallFamily B hZ Q := rfl

/-- The genuine posted base of the constructed field object. -/
theorem fieldFamily_post :
    ((fieldStack B hZ hK hAlg).val.val.p ⋙ Over.post B.inclusion).obj
        (fieldFamily B hZ hK hAlg Q s) =
      (Over.post B.inclusion).obj (fieldBase B hZ hK Q s) :=
  Stack.algebraicStackBaseChangeLift_factor_post B (Spec (.of K)) integerBase hK hZ
    (CurveFieldTargetComparison.baseArrow B hZ hK)
    (CurveFieldTargetComparison.integerStack B hZ hAlg) (smallFamily B hZ Q)
    ((Over.post B.inclusion).obj (fieldBase B hZ hK Q s))
    (smallFamily_lies_over B hZ hK hAlg Q s)

/-- It lies over the literal original base object of the field site. -/
theorem fieldFamily_base :
    (fieldStack B hZ hK hAlg).val.val.p.obj (fieldFamily B hZ hK hAlg Q s) =
      fieldBase B hZ hK Q s :=
  post_obj_injective (fieldFamily_post B hZ hK hAlg Q s)

local instance fieldFibered : (fieldStack B hZ hK hAlg).val.val.p.IsFibered :=
  (fieldStack B hZ hK hAlg).val.property.isFibered

/-- The literal native two-Yoneda classifier of that actual field family. -/
def classifyingMor : Functor.FiberedMor (fieldStack B hZ hK hAlg).val.val.p
    (fieldBase B hZ hK Q s) :=
  Functor.FiberedMor.OfFiberObj.fiberedMor (fieldStack B hZ hK hAlg).val.val.p
    (fieldBase B hZ hK Q s) (fieldFamily_base B hZ hK hAlg Q s)

/-- Its identity evaluation is isomorphic to the very same field family. -/
def classifiesFieldFamily :
    (classifyingMor B hZ hK hAlg Q s).toFunctor.obj
        (Functor.FiberedMor.unit (fieldBase B hZ hK Q s)) ≅
      fieldFamily B hZ hK hAlg Q s :=
  Functor.Fiber.fiberInclusion.mapIso
    (Functor.FiberedMor.OfFiberObj.fiberIso (fieldStack B hZ hK hAlg).val.val.p
      (fieldBase B hZ hK Q s) (fieldFamily_base B hZ hK hAlg Q s)
      (classifyingMor B hZ hK hAlg Q s).obj_over_unit)

/-- The projected object is canonically the ORIGINAL family, even when
its total space is an algebraic space. -/
def fieldFamily_originalIso :
    (originalProjection B hZ hK hAlg).obj (fieldFamily B hZ hK hAlg Q s) ≅ Q :=
  ((curvesSmallEquivalenceOver B hZ).unitIso.app Q).symm

/-- Actual identity evaluation of the field classifier, projected to the
original family category. -/
def classifiesOriginalFamily :
    (originalProjection B hZ hK hAlg).obj
        ((classifyingMor B hZ hK hAlg Q s).toFunctor.obj
          (Functor.FiberedMor.unit (fieldBase B hZ hK Q s))) ≅ Q :=
  (originalProjection B hZ hK hAlg).mapIso
      (classifiesFieldFamily B hZ hK hAlg Q s) ≪≫
    fieldFamily_originalIso B hZ hK hAlg Q s

/-- The very same classifier as a genuine morphism of native algebraic
stacks, so geometric smoothness applies to this actual family map. -/
def stackMorphism : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK
    (fieldBase B hZ hK Q s) ⟶ fieldStack B hZ hK hAlg :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (classifyingMor B hZ hK hAlg Q s).toBasedFunctor)

/-- Its underlying original functor is the literal family classifier. -/
theorem stackMorphism_functor :
    CatFiberedInGroupoids.homFunctor (stackMorphism B hZ hK hAlg Q s).hom =
      (classifyingMor B hZ hK hAlg Q s).toFunctor := rfl

end M9Native.CurveFieldClassifyingFamily
