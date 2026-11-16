module

public import M9StacksIntegration.CurveFieldClassifierDeformation
public import M9StacksIntegration.PointedBasePointTransport
public import M9StacksIntegration.CurveFieldTargetTangent
public import M9StacksIntegration.PointedParameterDeformation
public import StacksFrontier.Deformation.Artin.AlgebraicStackTangentSpace

/-!
# Actual smooth family classifiers give the original pointed derivative onto

Geometric smoothness is imposed on the actual native stack morphism
constructed from the original family. The native Artinian lifting theorem
and the proved canonical change of marking derive surjectivity. No
Kodaira--Spencer comparison or tangent-surjectivity premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u
namespace M9Native.CurveFieldClassifierSmooth

private theorem based_ext {C : Type*} [Category C] {D E : BasedCategory C}
    {F G : D ⥤ᵇ E} (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K))

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

local instance fieldFibered :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsFibered :=
  (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.property.isFibered


variable {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (i : Spec (.of k) ⟶ T)
  [IsCurve k (ParameterFamilyDeformation.fibre p i).hom]

local instance fibreProper : IsProper (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (IsProper (pullback.snd p i))
local instance fibreSmooth : Smooth (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (Smooth (pullback.snd p i))

open CurveFieldClassifierPullback CurveFieldClassifierDeformation

/-- The literal family classifier commutes with the original scheme projections. -/
theorem posted_projection :
    (classifier B hZ hK hAlg hX hT p s).toFunctor ⋙
        ((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙
          Over.post B.inclusion) =
      Over.forget (base B hZ hK hX hT p s) ⋙ Over.post B.inclusion := by
  simpa only [BasedCategory.ofFunctor, Functor.assoc] using
    congrArg (fun F => F ⋙ Over.post B.inclusion)
      (classifier B hZ hK hAlg hX hT p s).w

abbrev imagePoint := (classifier B hZ hK hAlg hX hT p s).toFunctor.obj
  (parameterPoint B hZ hK hX hT p s hk i)

theorem imagePoint_base :
    ((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙
        Over.post B.inclusion).obj (imagePoint B hZ hK hAlg hX hT p s hk i) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ (i ≫ s)) :=
  imageBasePoint
    (qY := (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙
      Over.post B.inclusion) (i ≫ s)
    (Over.forget (base B hZ hK hX hT p s) ⋙ Over.post B.inclusion)
    (classifier B hZ hK hAlg hX hT p s).toFunctor
    (posted_projection B hZ hK hAlg hX hT p s)
    (parameterPoint B hZ hK hX hT p s hk i)
    (parameterPoint_base B hZ hK hX hT p s hk i)

abbrev imageDeformations := predeformationCategory (i ≫ s)
  ((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙ Over.post B.inclusion)
  (imagePoint B hZ hK hAlg hX hT p s hk i)
  (imagePoint_base B hZ hK hAlg hX hT p s hk i)

instance imageCategory : Category (imageDeformations B hZ hK hAlg hX hT p s hk i).carrier :=
  (imageDeformations B hZ hK hAlg hX hT p s hk i).category

/-- The actual pointed map of the original native chart. -/
def nativeMap :
    BasedCategory.ofFunctor (parameterDeformations B hZ hK hX hT p s hk i).projection ⥤ᵇ
      BasedCategory.ofFunctor (imageDeformations B hZ hK hAlg hX hT p s hk i).projection :=
  (mapPredeformationCategory (i ≫ s)
    (Over.forget (base B hZ hK hX hT p s) ⋙ Over.post B.inclusion)
    ((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙ Over.post B.inclusion)
    (classifier B hZ hK hAlg hX hT p s).toFunctor
    (posted_projection B hZ hK hAlg hX hT p s)
    (parameterPoint B hZ hK hX hT p s hk i)
    (parameterPoint_base B hZ hK hX hT p s hk i)).toBasedFunctor

/-- The canonical actual point-value isomorphism gives a genuine equivalence
from the image-point problem to the ORIGINAL fixed-curve problem. -/
def markingEquivalence := PointedBasePointTransport.equivalence B hK (i ≫ s)
  (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
  (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.property
  (CurveFieldTargetComparison.fieldPoint B hZ hK hAlg hk (i ≫ s)
    (ParameterFamilyDeformation.fibre p i).hom)
  (imagePoint B hZ hK hAlg hX hT p s hk i)
  (CurveFieldTargetComparison.fieldPoint_lies_over B hZ hK hAlg hk (i ≫ s)
    (ParameterFamilyDeformation.fibre p i).hom)
  (imagePoint_base B hZ hK hAlg hX hT p s hk i)
  (pointValueIso B hZ hK hAlg hX hT p s hk i).symm
  (pointValueIso_inv_base B hZ hK hAlg hX hT p s hk i)

def markingBased :
    BasedCategory.ofFunctor (imageDeformations B hZ hK hAlg hX hT p s hk i).projection ⥤ᵇ
      BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection :=
  ⟨(markingEquivalence B hZ hK hAlg hX hT p s hk i).hom.functor,
    (markingEquivalence B hZ hK hAlg hX hT p s hk i).hom.w⟩

/-- The actual transported family functor is this chart map followed by
the proved change of marking. -/
theorem classifyingBased_eq_comp :
    classifyingBased B hZ hK hAlg hX hT p s hk i =
      BasedFunctor.comp (nativeMap B hZ hK hAlg hX hT p s hk i)
        (markingBased B hZ hK hAlg hX hT p s hk i) := by
  apply based_ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b m
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply DeformationMorphism.ext_of_components
  · change m.ringHom = 𝟙 _ ≫ m.ringHom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · change (classifier B hZ hK hAlg hX hT p s).toFunctor.map m.arrow =
      𝟙 _ ≫ (classifier B hZ hK hAlg hX hT p s).toFunctor.map m.arrow ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

variable (hfinite : LocallyOfFiniteType (i ≫ s)) (hqc : QuasiCompact (i ≫ s))

include hfinite in
theorem point_finite : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ (i ≫ s)) := by
  rw [spec_identity, Category.id_comp]
  exact hfinite

include hqc in
theorem point_quasiCompact : QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ (i ≫ s)) := by
  rw [spec_identity, Category.id_comp]
  exact hqc

include hfinite hqc in
theorem sourceStructure :
    IsDeformationCategory (parameterDeformations B hZ hK hX hT p s hk i).projection :=
  PointedParameterDeformation.representedDeformation
    (hv₀ := parameterPoint_base B hZ hK hX hT p s hk i)
    (point_finite s i hfinite) (point_quasiCompact s i hqc)

omit [SmoothOfRelativeDimension 1 p] in
include hfinite hqc in
theorem targetStructure : IsDeformationCategory (targetDeformations B hZ hK hAlg p s hk i).projection :=
  CurveFieldTargetTangent.deformationStructure B hZ hK hAlg hk (i ≫ s)
    (ParameterFamilyDeformation.fibre p i).hom hfinite hqc

variable [IsOpenImmersion (i ≫ s)]

include hfinite hqc in
/-- Actual geometric smoothness supplies native Artinian lifting for
this SAME original classifying morphism. -/
theorem nativeMap_isSmooth
    (hsm : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (originalFamily B hZ hX hT p) s)) :
    Deformation.IsSmooth (nativeMap B hZ hK hAlg hX hT p s hk i) := by
  exact isSmoothOnPredeformationCategories_of_isSmooth B (Spec (.of K)) hK
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg)
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
      (originalFamily B hZ hX hT p) s) hsm
    (i ≫ s) (parameterPoint B hZ hK hX hT p s hk i)
    (parameterPoint_base B hZ hK hX hT p s hk i)
    (point_finite s i hfinite) (point_quasiCompact s i hqc) inferInstance

include hfinite hqc in
/-- The genuine change of marking preserves the actual smooth lifting property. -/
theorem classifyingBased_isSmooth
    (hsm : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (originalFamily B hZ hX hT p) s)) :
    Deformation.IsSmooth (classifyingBased B hZ hK hAlg hX hT p s hk i) := by
  rw [classifyingBased_eq_comp]
  exact isSmooth_comp _ _ (nativeMap_isSmooth B hZ hK hAlg hX hT p s hk i hfinite hqc hsm)
    (isSmooth_of_equivalenceOver (markingEquivalence B hZ hK hAlg hX hT p s hk i)
      (markingBased B hZ hK hAlg hX hT p s hk i) rfl)

/-- The original linear differential, with its actual finite coefficients. -/
def derivative (W : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (parameterDeformations B hZ hK hX hT p s hk i).projection)
      (sourceStructure B hZ hK hX hT p s hk i hfinite hqc) W) →ₗ[k]
    ↥(tangentModuleAt.{u,u,u}
      (BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection)
      (targetStructure B hZ hK hAlg p s hk i hfinite hqc) W) :=
  tangentMapAt.{u,u,u} (sourceStructure B hZ hK hX hT p s hk i hfinite hqc)
    (targetStructure B hZ hK hAlg p s hk i hfinite hqc)
    (classifyingBased B hZ hK hAlg hX hT p s hk i) W

omit [IsOpenImmersion (i ≫ s)] in
/-- The differential is evaluated on the actual marked image, with the
same original finite coefficients and Artinian algebra. -/
theorem derivative_class (W : FGModuleCat.{u} k)
    (z : (parameterDeformations B hZ hK hX hT p s hk i).projection.Fiber
      (coordBase (Λ := k) W)) :
    derivative B hZ hK hAlg hX hT p s hk i hfinite hqc W
      (tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (parameterDeformations B hZ hK hX hT p s hk i).projection)
        (sourceStructure B hZ hK hX hT p s hk i hfinite hqc) W z) =
    tangentClassAt.{u,u,u}
      (BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection)
      (targetStructure B hZ hK hAlg p s hk i hfinite hqc) W
      ((fiberFunctor (classifyingBased B hZ hK hAlg hX hT p s hk i)
        (coordBase (Λ := k) W)).obj z) :=
  tangentMapAt_tangentClassAt.{u,u,u}
    (sourceStructure B hZ hK hX hT p s hk i hfinite hqc)
    (targetStructure B hZ hK hAlg p s hk i hfinite hqc)
    (classifyingBased B hZ hK hAlg hX hT p s hk i) W z

/-- Surjectivity follows from the actual chart lifting property, for every
finite coefficient module. It is not a supplied KS hypothesis. -/
theorem derivative_surjective
    (hsm : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (originalFamily B hZ hX hT p) s)) (W : FGModuleCat.{u} k) :
    Function.Surjective (derivative B hZ hK hAlg hX hT p s hk i hfinite hqc W) := by
  have := essSurj_of_isSmooth_of_isPredeformationCategory
    (classifyingBased B hZ hK hAlg hX hT p s hk i)
    (sourceStructure B hZ hK hX hT p s hk i hfinite hqc).predeformation
    (targetStructure B hZ hK hAlg p s hk i hfinite hqc).predeformation
    (classifyingBased_isSmooth B hZ hK hAlg hX hT p s hk i hfinite hqc hsm)
  exact tangentMapAt_surjective_of_essSurj.{u,u,u}
    (sourceStructure B hZ hK hX hT p s hk i hfinite hqc)
    (targetStructure B hZ hK hAlg p s hk i hfinite hqc)
    (classifyingBased B hZ hK hAlg hX hT p s hk i) W

end M9Native.CurveFieldClassifierSmooth
