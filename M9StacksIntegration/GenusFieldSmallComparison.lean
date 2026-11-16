module

public import M9StacksIntegration.StrictPullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverFullSubcategory
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStack

/-! The actual original genus category and its native hom-shrunk model,
over the integer base and every specified coefficient field. The comparison
uses the proved native Curves equivalence and its actual unit/counit.
Algebraicity, a coarse space, or an equivalence are not inputs. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory StacksRepresentableCFG
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.GenusFieldSmallComparison

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining TRUE original genus condition, for every genus. -/
abbrev genusProperty (g : ℕ) : ObjectProperty (CurveFamily B hZ) :=
  IsSmoothH0FamilyOfFibreGenus B hZ g

instance genusProperty_closed (g : ℕ) :
    (genusProperty B hZ g).IsClosedUnderIsomorphisms :=
  ⟨fun e hx => CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom e.inv hx⟩

/-- The SAME genus condition on the actual native Curves small model,
read through its genuine original-family recovery functor. -/
abbrev smallGenusProperty (g : ℕ) : ObjectProperty (curvesSmallBased B hZ).obj :=
  (genusProperty B hZ g).inverseImage (curvesSmallEquivalenceOver B hZ).inv.functor

abbrev smallGenusProjection (g : ℕ) :=
  (smallGenusProperty B hZ g).ι ⋙ (curvesSmallBased B hZ).p

/-- Actual restriction of the native proved Curves equivalence. -/
def genusEquivalence (g : ℕ) :
    EquivalenceOver (moduliSmoothCurvesOfGenus B hZ g).val.p
      (smallGenusProjection B hZ g) := by
  letI : (genusProperty B hZ g).IsClosedUnderIsomorphisms :=
    genusProperty_closed B hZ g
  exact ((curvesSmallEquivalenceOver B hZ).fullSubcategory (genusProperty B hZ g)).symm

/-- The actual small genus category is fibred in groupoids, derived through
the equivalence with the original TRUE genus category. -/
def smallGenusStack (g : ℕ) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (smallGenusProjection B hZ g))
    (isFiberedInGroupoids_of_equivalenceOver (genusEquivalence B hZ g).symm
      (moduliSmoothCurvesOfGenus B hZ g).property)

/-- No object of the actual Curves small model is replaced. -/
theorem genusEquivalence_obj (g : ℕ) (X : (moduliSmoothCurvesOfGenus B hZ g).val.obj) :
    ((genusEquivalence B hZ g).hom.functor.obj X).obj =
      (curvesSmallEquivalenceOver B hZ).hom.functor.obj X.obj := rfl

/-- Every original native curve-family arrow is the actual hom-shrink map. -/
theorem genusEquivalence_map (g : ℕ)
    {X Y : (moduliSmoothCurvesOfGenus B hZ g).val.obj} (a : X ⟶ Y) :
    ((genusEquivalence B hZ g).hom.functor.map a).hom =
      (curvesSmallEquivalenceOver B hZ).hom.functor.map a.hom := rfl

/-- Every small-family object recovers its actual original native family. -/
theorem genusEquivalence_inverse_obj (g : ℕ)
    (X : (smallGenusProperty B hZ g).FullSubcategory) :
    ((genusEquivalence B hZ g).inv.functor.obj X).obj =
      (curvesSmallEquivalenceOver B hZ).inv.functor.obj X.obj := rfl

/-- Every small-family arrow recovers its actual original native arrow. -/
theorem genusEquivalence_inverse_map (g : ℕ)
    {X Y : (smallGenusProperty B hZ g).FullSubcategory} (a : X ⟶ Y) :
    ((genusEquivalence B hZ g).inv.functor.map a).hom =
      (curvesSmallEquivalenceOver B hZ).inv.functor.map a.hom := rfl

/-- Recovery is the genuine original-family unit, not an assumed comparison. -/
def originalRecoveryIso (g : ℕ) (X : (moduliSmoothCurvesOfGenus B hZ g).val.obj) :
    X.obj ≅ (curvesSmallEquivalenceOver B hZ).inv.functor.obj
      (((genusEquivalence B hZ g).hom.functor.obj X).obj) :=
  (genusProperty B hZ g).ι.mapIso ((genusEquivalence B hZ g).unitIso.app X)

/-- The actual original-family recovery is natural on ALL arrows. -/
theorem originalRecovery_naturality (g : ℕ)
    {X Y : (moduliSmoothCurvesOfGenus B hZ g).val.obj} (a : X ⟶ Y) :
    a.hom ≫ (originalRecoveryIso B hZ g Y).hom =
      (originalRecoveryIso B hZ g X).hom ≫
        (curvesSmallEquivalenceOver B hZ).inv.functor.map
          (((genusEquivalence B hZ g).hom.functor.map a).hom) :=
  congrArg (fun b => b.hom) ((genusEquivalence B hZ g).unitIso.hom.naturality a)

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual specified coefficient-field arrow to the integer spectrum. -/
def coefficientArrow : B.obj hK ⟶ B.obj hZ :=
  ObjectProperty.homMk (specULiftZIsTerminal.from (Spec (.of K)))

abbrev relocalize := Over.map (coefficientArrow B hZ K hK)

abbrev originalFieldProjection (g : ℕ) :=
  StrictPullback.structureFunctor (relocalize B hZ K hK)
    (moduliSmoothCurvesOfGenus B hZ g).val.p

abbrev smallFieldProjection (g : ℕ) :=
  StrictPullback.structureFunctor (relocalize B hZ K hK) (smallGenusProjection B hZ g)

/-- The genuine field comparison, for ALL coefficient-base objects and
arrows and every genus, with no algebraicity or equivalence premise. -/
def fieldEquivalence (g : ℕ) :
    EquivalenceOver (originalFieldProjection B hZ K hK g)
      (smallFieldProjection B hZ K hK g) :=
  StrictPullbackEquivalence.transportEquivalence (relocalize B hZ K hK)
    (genusEquivalence B hZ g)

def originalFieldStack (g : ℕ) :
    CatFiberedInGroupoids (BigFppfOver B (Spec (.of K)) hK) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (originalFieldProjection B hZ K hK g))
    (StrictPullback.isFiberedInGroupoids_structureFunctor (relocalize B hZ K hK)
      (moduliSmoothCurvesOfGenus B hZ g).val.p (moduliSmoothCurvesOfGenus B hZ g).property)

def smallFieldStack (g : ℕ) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B (Spec (.of K)) hK) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (smallFieldProjection B hZ K hK g))
    (StrictPullback.isFiberedInGroupoids_structureFunctor (relocalize B hZ K hK)
      (smallGenusProjection B hZ g) (smallGenusStack B hZ g).property)

/-- The literal specified field base is unchanged on every object. -/
theorem fieldEquivalence_obj_base (g : ℕ)
    (X : (originalFieldStack B hZ K hK g).val.obj) :
    ((fieldEquivalence B hZ K hK g).hom.functor.obj X).base = X.base := rfl

/-- The actual original family is sent through the genuine native hom shrink. -/
theorem fieldEquivalence_obj_family (g : ℕ)
    (X : (originalFieldStack B hZ K hK g).val.obj) :
    (((fieldEquivalence B hZ K hK g).hom.functor.obj X).fib).obj =
      (curvesSmallEquivalenceOver B hZ).hom.functor.obj X.fib.obj := rfl

/-- The specified field-base arrow is unchanged on EVERY family arrow. -/
theorem fieldEquivalence_map_base (g : ℕ)
    {X Y : (originalFieldStack B hZ K hK g).val.obj} (a : X ⟶ Y) :
    ((fieldEquivalence B hZ K hK g).hom.functor.map a).base = a.base := rfl

/-- The complete original-family arrow is retained, including its total
algebraic-space map; no scheme-total assumption occurs. -/
theorem fieldEquivalence_map_family (g : ℕ)
    {X Y : (originalFieldStack B hZ K hK g).val.obj} (a : X ⟶ Y) :
    (((fieldEquivalence B hZ K hK g).hom.functor.map a).fib).hom =
      (curvesSmallEquivalenceOver B hZ).hom.functor.map a.fib.hom := rfl

def fieldOriginalRecoveryIso (g : ℕ)
    (X : (originalFieldStack B hZ K hK g).val.obj) :
    X.fib.obj ≅ (curvesSmallEquivalenceOver B hZ).inv.functor.obj
      ((((fieldEquivalence B hZ K hK g).hom.functor.obj X).fib).obj) :=
  originalRecoveryIso B hZ g X.fib

theorem fieldOriginalRecovery_naturality (g : ℕ)
    {X Y : (originalFieldStack B hZ K hK g).val.obj} (a : X ⟶ Y) :
    a.fib.hom ≫ (fieldOriginalRecoveryIso B hZ K hK g Y).hom =
      (fieldOriginalRecoveryIso B hZ K hK g X).hom ≫
        (curvesSmallEquivalenceOver B hZ).inv.functor.map
          ((((fieldEquivalence B hZ K hK g).hom.functor.map a).fib).hom) :=
  originalRecovery_naturality B hZ g a.fib

/-- The field unit's original family component is exactly this recovery. -/
theorem fieldEquivalence_unit_family (g : ℕ)
    (X : (originalFieldStack B hZ K hK g).val.obj) :
    (((fieldEquivalence B hZ K hK g).unitIso.hom.app X).fib).hom =
      (fieldOriginalRecoveryIso B hZ K hK g X).hom := rfl

/-- The field unit covers the identity of the SAME coefficient base. -/
theorem fieldEquivalence_unit_base (g : ℕ)
    (X : (originalFieldStack B hZ K hK g).val.obj) :
    ((fieldEquivalence B hZ K hK g).unitIso.hom.app X).base = 𝟙 X.base := rfl

/-- The field counit covers the identity of the SAME coefficient base. -/
theorem fieldEquivalence_counit_base (g : ℕ)
    (X : (smallFieldStack B hZ K hK g).val.obj) :
    ((fieldEquivalence B hZ K hK g).counitIso.hom.app X).base = 𝟙 X.base := rfl

/-- Genuine cartesian naturality is derived from the actual field categories. -/
theorem fieldEquivalence_cartesian (g : ℕ)
    {X Y : (originalFieldStack B hZ K hK g).val.obj} (a : X ⟶ Y) :
    (smallFieldProjection B hZ K hK g).IsStronglyCartesian a.base
      ((fieldEquivalence B hZ K hK g).hom.functor.map a) := by
  haveI : (smallFieldProjection B hZ K hK g).IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).hom.functor.map a) := by
    apply IsHomLift.of_fac' (smallFieldProjection B hZ K hK g) a.base
      ((fieldEquivalence B hZ K hK g).hom.functor.map a) rfl rfl
    change a.base = eqToHom (rfl : X.base = X.base) ≫ a.base ≫
      eqToHom (rfl : Y.base = Y.base).symm
    simp
  haveI : (smallFieldStack B hZ K hK g).val.p.IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).hom.functor.map a) :=
    inferInstanceAs ((smallFieldProjection B hZ K hK g).IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).hom.functor.map a))
  exact (smallFieldStack B hZ K hK g).property.isStronglyCartesian_homLift _ _

/-- Original recovery is also genuinely cartesian over the specified field. -/
theorem fieldEquivalence_inverse_cartesian (g : ℕ)
    {X Y : (smallFieldStack B hZ K hK g).val.obj} (a : X ⟶ Y) :
    (originalFieldProjection B hZ K hK g).IsStronglyCartesian a.base
      ((fieldEquivalence B hZ K hK g).inv.functor.map a) := by
  haveI : (originalFieldProjection B hZ K hK g).IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).inv.functor.map a) := by
    apply IsHomLift.of_fac' (originalFieldProjection B hZ K hK g) a.base
      ((fieldEquivalence B hZ K hK g).inv.functor.map a) rfl rfl
    change a.base = eqToHom (rfl : X.base = X.base) ≫ a.base ≫
      eqToHom (rfl : Y.base = Y.base).symm
    simp
  haveI : (originalFieldStack B hZ K hK g).val.p.IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).inv.functor.map a) :=
    inferInstanceAs ((originalFieldProjection B hZ K hK g).IsHomLift a.base
      ((fieldEquivalence B hZ K hK g).inv.functor.map a))
  exact (originalFieldStack B hZ K hK g).property.isStronglyCartesian_homLift _ _

end M9Native.GenusFieldSmallComparison
