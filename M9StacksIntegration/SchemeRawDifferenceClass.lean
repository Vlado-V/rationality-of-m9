module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChange
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquivExt
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPull
public import M9StacksIntegration.SolutionSplitBaseSection

/-! The actual raw extension class and the difference against a split base
point. Base restriction and coefficient transport are retained explicitly. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap)

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.SchemeRawDifferenceClass

section BaseRestriction

variable {X S S' : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- Canonical transport along an equality of the original structure morphisms. -/
def rebaseClass {g : X ⟶ S} (h : f = g)
    (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    PresentedSquareZeroExtension.relativeObj g ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G :=
  h ▸ ξ

theorem rebaseClass_sub {g : X ⟶ S} (h : f = g)
    (ξ η : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    rebaseClass h (ξ - η) = rebaseClass h ξ - rebaseClass h η := by
  subst g
  rfl

theorem rebaseClass_zero {g : X ⟶ S} (h : f = g) :
    rebaseClass (G := G) h 0 = 0 := by
  subst g
  rfl

/-- The same actual extension, with only its structure morphism rewritten. -/
def rebaseExtension {g : X ⟶ S} (h : f = g) (P : AlgebraSquareZeroExtension f G) :
    AlgebraSquareZeroExtension g G := h ▸ P

theorem rebaseExtension_sheaf {g : X ⟶ S} (h : f = g)
    (P : AlgebraSquareZeroExtension f G) : (rebaseExtension h P).sheaf = P.sheaf := by
  subst g
  rfl

theorem rebaseExtension_extClass {g : X ⟶ S} (h : f = g)
    (P : AlgebraSquareZeroExtension f G) :
    (rebaseExtension h P).toPresented.extClass = rebaseClass h P.toPresented.extClass := by
  subst g
  rfl

theorem retraction_comp (t : S ⟶ S') (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S) :
    (f ≫ t) ≫ p = f := by rw [Category.assoc, hp, Category.comp_id]

theorem baseInverseImageRingMap_id (f : X ⟶ S) :
    baseInverseImageRingMap f (𝟙 S) = 𝟙 (inverseImageBaseRing f) := by
  unfold baseInverseImageRingMap
  change ((sheafAdjunction f).homEquiv _ _).symm
    ((sheafAdjunction f).unit.app S.sheaf) = 𝟙 _
  exact Adjunction.homEquiv_symm_unit _ _

theorem restrictBaseExtClass_id
    (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    restrictBaseExtClass (𝟙 S) ξ = ξ := by
  obtain ⟨P, rfl⟩ := exists_extension_extClass_eq (f := f) (G := G) ξ
  rw [restrictBaseExtClass_extClass]
  refine AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom
    (P.restrictBase (𝟙 S)) P (𝟙 _) ?_ (Category.id_comp _) (fun _ _ => rfl)
  exact (Category.comp_id _).trans
    ((congrArg (fun q => q ≫ P.base) (baseInverseImageRingMap_id f)).trans
      (Category.id_comp _))

theorem restrictBaseExtClass_eq_of_eq_id (q : S ⟶ S) (hq : q = 𝟙 S)
    (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    rebaseClass (show f ≫ q = f by rw [hq, Category.comp_id])
      (restrictBaseExtClass q ξ) = ξ := by
  subst q
  exact restrictBaseExtClass_id ξ

theorem restrictBaseExtClass_retraction (t : S ⟶ S') (p : S' ⟶ S)
    (hp : t ≫ p = 𝟙 S)
    (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    rebaseClass (retraction_comp t p hp)
      (restrictBaseExtClass p (restrictBaseExtClass t ξ)) = ξ := by
  have h := congrArg (rebaseClass (retraction_comp (f := f) t p hp))
    (restrictBaseExtClass_comp t p ξ).symm
  exact h.trans (restrictBaseExtClass_eq_of_eq_id (t ≫ p) hp ξ)

/-- The actual extension class after forgetting the thickened-base structure. -/
def rawClass (t : S ⟶ S') (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S)
    (P : AlgebraSquareZeroExtension (f ≫ t) G) :
    PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G :=
  rebaseClass (retraction_comp t p hp) (restrictBaseExtClass p P.toPresented.extClass)

def rawExtension (t : S ⟶ S') (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S)
    (P : AlgebraSquareZeroExtension (f ≫ t) G) : AlgebraSquareZeroExtension f G :=
  rebaseExtension (retraction_comp t p hp) (P.restrictBase p)

theorem rawExtension_sheaf (t : S ⟶ S') (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S)
    (P : AlgebraSquareZeroExtension (f ≫ t) G) : (rawExtension t p hp P).sheaf = P.sheaf :=
  rebaseExtension_sheaf (retraction_comp t p hp) (P.restrictBase p)

theorem rawClass_eq_extension (t : S ⟶ S') (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S)
    (P : AlgebraSquareZeroExtension (f ≫ t) G) :
    rawClass t p hp P = (rawExtension t p hp P).toPresented.extClass := by
  rw [rawExtension, rebaseExtension_extClass]
  unfold rawClass
  rw [restrictBaseExtClass_extClass]

theorem raw_differenceClass (t : S ⟶ S') (ht : IsFirstOrderThickening t)
    (p : S' ⟶ S) (hp : t ≫ p = 𝟙 S)
    {c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    (Q Q₀ : DeformationSolution t ht f G c) :
    differenceClass Q Q₀ =
      rawClass t p hp Q.toAlgebraExtension - rawClass t p hp Q₀.toAlgebraExtension := by
  have h := congrArg
    (fun ξ => rebaseClass (retraction_comp t p hp) (restrictBaseExtClass p ξ))
    (restrictBaseExtClass_differenceClass Q Q₀)
  change rebaseClass (retraction_comp t p hp)
      (restrictBaseExtClass p (restrictBaseExtClass t (differenceClass Q Q₀))) =
    rebaseClass (retraction_comp t p hp)
      (restrictBaseExtClass p (Q.extClass - Q₀.extClass)) at h
  rw [restrictBaseExtClass_retraction t p hp, restrictBaseExtClass_sub, rebaseClass_sub] at h
  exact h

end BaseRestriction

section SchemeFiber

open Deformation Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (X : Over (Spec (.of k))) (V : FGModuleCat.{u} k)

abbrev closedMap : (Spec (.of k)).toRingedSpace ⟶
    (baseSpec (coordBase (Λ := Λ) V)).toRingedSpace :=
  (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom

abbrev baseProjection : (baseSpec (coordBase (Λ := Λ) V)).toRingedSpace ⟶
    (Spec (.of k)).toRingedSpace :=
  (squareZeroStructureSpecMap (Λ := Λ) V).toLRSHom.toShHom

theorem base_retraction : closedMap (Λ := Λ) V ≫ baseProjection (Λ := Λ) V = 𝟙 _ :=
  congrArg (fun q => q.toLRSHom.toShHom)
    (residueSpecMap_comp_squareZeroStructureSpecMap (Λ := Λ) V)

abbrev coordinateSolution
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :=
  fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two V) x

/-- The original structure-sheaf extension, genuinely restricted from
the dual-number base to k and then read over the original structure map. -/
def rawFiberExtension
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    AlgebraSquareZeroExtension X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X) :=
  rawExtension (closedMap V) (baseProjection V) (base_retraction V)
    (coordinateSolution X V x).toAlgebraExtension

def rawFiberClass
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    extOneNaiveCotangent X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X) :=
  (rawFiberExtension X V x).toPresented.extClass

theorem rawFiberExtension_sheaf
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    (rawFiberExtension X V x).sheaf = (coordinateSolution X V x).thickenedSheaf :=
  rawExtension_sheaf (closedMap V) (baseProjection V) (base_retraction V)
    (coordinateSolution X V x).toAlgebraExtension

/-- The actual first projection of the native trivial base change. -/
def trivialProjection : (trivialFiberAt (Λ := Λ) X V).1.scheme ⟶ X.left :=
  (baseChangeDeformationHom (residueTrivialDeformation (Λ := Λ) X)
    (squareZeroInclusion (Λ := Λ) V)).map

theorem trivialProjection_retraction :
    (trivialFiberAt (Λ := Λ) X V).1.specialMap ≫ trivialProjection X V = 𝟙 X.left :=
  (baseChangeDeformationHom (residueTrivialDeformation (Λ := Λ) X)
    (squareZeroInclusion (Λ := Λ) V)).special_compat

theorem squareZeroInclusion_baseSpecMap :
    baseSpecMap (squareZeroInclusion (Λ := Λ) V) =
      squareZeroStructureSpecMap (Λ := Λ) V ≫
        residueSpecMap (residueFieldObject.{u,u,u} Λ k) := by
  rw [baseSpecMap, squareZeroStructureSpecMap, residueSpecMap, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rfl

theorem trivialProjection_structure :
    trivialProjection (Λ := Λ) X V ≫ X.hom =
      schemeMorphismPushStructure X.hom (trivialFiberAt (Λ := Λ) X V) := by
  have := isIso_residueSpecMap_residueFieldObject (Λ := Λ) (k := k)
  apply (cancel_mono (residueSpecMap (residueFieldObject.{u,u,u} Λ k))).mp
  calc
    _ = trivialProjection X V ≫ (residueTrivialDeformation (Λ := Λ) X).toBase :=
      Category.assoc _ _ _
    _ = (trivialDeformationAt (Λ := Λ) X V).toBase ≫
        baseSpecMap (squareZeroInclusion (Λ := Λ) V) :=
      (baseChangeDeformationHom (residueTrivialDeformation (Λ := Λ) X)
        (squareZeroInclusion (Λ := Λ) V)).cartesian.w
    _ = _ := by
      rw [squareZeroInclusion_baseSpecMap]
      simp only [schemeMorphismPushStructure, SchemeDeformationCategory.rebase_toBase,
        eqToHom_refl, Category.comp_id, Category.assoc]

theorem trivial_restricted_extClass_zero :
    ((coordinateSolution X V (trivialFiberAt (Λ := Λ) X V)).toAlgebraExtension.restrictBase
      (baseProjection (Λ := Λ) V)).toPresented.extClass = 0 := by
  let Q := coordinateSolution X V (trivialFiberAt (Λ := Λ) X V)
  let q : Q.X' ⟶ X.left.toRingedSpace := (trivialProjection X V).toLRSHom.toShHom
  have hq : Q.i ≫ q = 𝟙 _ :=
    congrArg (fun a => a.toLRSHom.toShHom) (trivialProjection_retraction X V)
  apply SolutionSplitBaseSection.restrictBase_extClass_eq_zero Q (baseProjection V) q hq
  rw [retraction_comp (closedMap V) (baseProjection V) (base_retraction V)]
  exact congrArg (fun a => a.toLRSHom.toShHom) (trivialProjection_structure (Λ := Λ) X V)

theorem trivial_rawFiberClass_zero : rawFiberClass (Λ := Λ) X V (trivialFiberAt X V) = 0 := by
  let Q := coordinateSolution X V (trivialFiberAt (Λ := Λ) X V)
  change (rawExtension (closedMap V) (baseProjection V) (base_retraction V)
    Q.toAlgebraExtension).toPresented.extClass = 0
  refine (rawClass_eq_extension (closedMap V) (baseProjection V) (base_retraction V)
    Q.toAlgebraExtension).symm.trans ?_
  unfold rawClass
  have he := restrictBaseExtClass_extClass (baseProjection V) Q.toAlgebraExtension
  have hz := trivial_restricted_extClass_zero (Λ := Λ) X V
  exact (congrArg (rebaseClass (retraction_comp (closedMap V) (baseProjection V)
    (base_retraction V))) (he.trans hz)).trans (rebaseClass_zero _)

theorem rawFiberClass_eq_differenceClass
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    rawFiberClass X V x = differenceClass (coordinateSolution X V x)
      (coordinateSolution X V (trivialFiberAt X V)) := by
  have h := raw_differenceClass (closedMap V)
    (residueSpecMap_isFirstOrderThickening (coordBase V)
      (maximalIdeal_squareZeroExtensionArtinian_pow_two V))
    (baseProjection V) (base_retraction V)
    (coordinateSolution X V x) (coordinateSolution X V (trivialFiberAt X V))
  rw [rawClass_eq_extension, rawClass_eq_extension] at h
  change differenceClass _ _ = rawFiberClass X V x - rawFiberClass X V (trivialFiberAt X V) at h
  exact (h.trans (by rw [trivial_rawFiberClass_zero, sub_zero])).symm

/-- The actual coefficient-transported raw k-extension is the original
standard native class, based at the actual trivial deformation. -/
theorem coefficient_rawFiberClass
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    coordExtCoefficientsAddEquiv X V (rawFiberClass X V x) = fiberExtClassAt X V x := by
  rw [rawFiberClass_eq_differenceClass]
  rfl

/-- The same actual coefficient identification, spelled as postcomposition
by its native shifted single map. -/
theorem coefficient_rawFiberClass_hom
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V)) :
    rawFiberClass X V x ≫ ((DerivedCategory.singleFunctor _ 0).map
      (coordPulledIdealIso (Λ := Λ) V X).hom)⟦(1 : ℤ)⟧' = fiberExtClassAt X V x :=
  (coordExtCoefficientsAddEquiv_apply X V (rawFiberClass X V x)).symm.trans
    (coefficient_rawFiberClass X V x)

end SchemeFiber

end M9Native.SchemeRawDifferenceClass
