module

public import M9StacksIntegration.ConormalClassNaturality
public import M9StacksIntegration.DirectCotangentComparison
public import M9StacksIntegration.AdjointCochainProjection
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass

/-!
# Necessary class vanishing for an actual compatible morphism

Only the genuine presentation and conormal maps of an actual compatible
morphism are used. The target class will be allowed to vanish; no
sufficiency, gluing or flat-comparison injectivity theorem is imported.
The degree-minus-one calculation follows the necessity computation in
the pinned Apache-licensed native CompatibleMorphismExtClass source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction HomologicalComplex CochainComplex
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 5000] _root_.SheafOfModules.instAbelian
attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.CompatibleMorphismClassNecessity

variable {X Y S : RingedSpace.{u,u}} {f : X ⟶ S} {g : Y ⟶ X}
  {F : SheafOfModules.{u} (structureSheafRing X)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}

/-- The actual original presentation sequence in its literal module category. -/
abbrev presentationSequence (P : SquareZeroAlgebraExtension f F) :
    ShortComplex (SheafOfModules.{u} (structureSheafRing X)) :=
  Stacks.SheafOfModules.presentationConormalSequence.{u,u,u,u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    X.sheaf (structureRingMap f) P.generators P.generatorsMap

/-- The actual differential of the original extension presentation. -/
abbrev presentationDifferential (P : SquareZeroAlgebraExtension f F) :
    (presentationSequence P).X₁ ⟶ (presentationSequence P).X₂ := (presentationSequence P).f

/-- The actual original presentation complex in its literal module category. -/
abbrev presentationComplex (P : SquareZeroAlgebraExtension f F) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  PresentedSquareZeroExtension.presentationComplex f P.generators P.generatorsMap

/-- The literal original cochain representing its conormal class. -/
def classCochain (P : SquareZeroAlgebraExtension f F) :
    presentationComplex P ⟶
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)⟦(1 : ℤ)⟧ :=
  ConormalClassCochain.classMap (C := SheafOfModules.{u} (structureSheafRing X))
    (presentationDifferential P) P.conormalToIdeal

/-- Reading the actual extension class on its actual presentation gives
the original cochain representative and original shift comparison. -/
theorem comparison_class (P : SquareZeroAlgebraExtension f F) :
    DerivedCategory.Q.map (CompatibleMorphism.comparisonX P) ≫ P.toAlgebraSquareZeroExtension.toPresented.extClass =
      DerivedCategory.Q.map (classCochain P) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F) := by
  have h := (PresentedSquareZeroExtension.naiveCotangentIso f P.generators
    P.generatorsMap).hom_inv_id_assoc
      ((PresentedSquareZeroExtension.twoTerm f P.generators P.generatorsMap).conormalExtClass
        F P.conormalToIdeal)
  exact h.trans (ConormalClassCochain.conormalExtClass_eq
    (C := SheafOfModules.{u} (structureSheafRing X))
    (presentationDifferential P) P.conormalToIdeal)

/-- A zero actual extension class has a zero actual representative
after passage to the original derived category. -/
theorem classCochain_eq_zero (P : SquareZeroAlgebraExtension f F) (hP : P.toAlgebraSquareZeroExtension.toPresented.extClass = 0) :
    DerivedCategory.Q.map (classCochain P) = 0 := by
  apply Limits.zero_of_comp_mono ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
    ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F))
  calc
    _ = DerivedCategory.Q.map (CompatibleMorphism.comparisonX P) ≫
        P.toAlgebraSquareZeroExtension.toPresented.extClass := (comparison_class P).symm
    _ = DerivedCategory.Q.map (CompatibleMorphism.comparisonX P) ≫
        (0 : extOneNaiveCotangent f F) :=
      congrArg (fun a : extOneNaiveCotangent f F =>
        DerivedCategory.Q.map (CompatibleMorphism.comparisonX P) ≫ a) hP
    _ = 0 := Limits.comp_zero

/-- Naturality of the actual original direct comparison takes zero
target class to zero on the termwise-pulled representative. -/
theorem comparison_classCochain_zero (P : SquareZeroAlgebraExtension f F)
    (hP : P.toAlgebraSquareZeroExtension.toPresented.extClass = 0) :
    (DirectCotangentComparison.comparisonNat g).app (presentationComplex P) ≫
      DerivedCategory.Q.map
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (classCochain P)) = 0 := by
  have hn := DirectCotangentComparison.comparison_naturality g (classCochain P)
  have hmap : (derivedPullback g).map (DerivedCategory.Q.map (classCochain P)) = 0 := by
    rw [classCochain_eq_zero P hP]
    exact (derivedPullback g).map_zero _ _
  exact hn.symm.trans
    ((congrArg (fun a => a ≫ (DirectCotangentComparison.comparisonNat g).app
      (((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)⟦(1 : ℤ)⟧))
        hmap).trans Limits.zero_comp)

variable {P : SquareZeroAlgebraExtension f F}
  {Q : SquareZeroAlgebraExtension (g ≫ f) G}
  {c : F ⟶ (modulePushforward g).obj G}

/-- The actual transposed compatible presentation map in degree minus
one is the actual compatible conormal map. -/
theorem pullbackPresentationMap_f_negOne (h : CompatibleMorphism P Q c) :
    h.pullbackPresentationMap.f (-1) =
      (modulePullback g).map
        (doubleXIso₀ (presentationDifferential P) ComplexShape.upIntRelNegOneZero).hom ≫
      h.pullbackConormalMap ≫
        (doubleXIso₀ (presentationDifferential Q) ComplexShape.upIntRelNegOneZero).inv := by
  have e := Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne g.hom.base
    (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp
  refine (AdjointCochainProjection.transpose_f
    (modulePullbackPushforwardAdjunction g) h.presentationPushMap (-1)).trans ?_
  refine (congrArg ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm e).trans ?_
  refine ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_left_symm _ _).trans ?_
  exact congrArg (_ ≫ ·) ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_right_symm
    _ _)

/-- The genuine termwise coefficient transport, before passing to the
derived category. No coefficient coordinate identification is used. -/
def coefficientTransport (c : F ⟶ (modulePushforward g).obj G) :=
  (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
    (1 : ℤ)).hom.app
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F) ≫
  ((singleMapHomologicalComplex (modulePullback g) (ComplexShape.up ℤ) 0).hom.app F)⟦(1 : ℤ)⟧' ≫
  ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
    (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c))⟦(1 : ℤ)⟧'

/-- The actual compatible conormal relation implies the actual square
of original class representatives. -/
theorem compatible_classCochain (h : CompatibleMorphism P Q c) :
    h.pullbackPresentationMap ≫ classCochain Q =
      ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (classCochain P) ≫ coefficientTransport c := by
  let E := doubleMapFunctorIso (modulePullback g) (presentationDifferential P)
    ComplexShape.upIntRelNegOneZero (by decide)
  apply (cancel_epi E.hom).mp
  have hδ : (doubleXIso₀ ((modulePullback g).map (presentationDifferential P))
        ComplexShape.upIntRelNegOneZero).inv ≫
      (E.hom ≫ h.pullbackPresentationMap).f (-1) ≫
      (doubleXIso₀ (presentationDifferential Q) ComplexShape.upIntRelNegOneZero).hom ≫
      Q.conormalToIdeal =
    (modulePullback g).map P.conormalToIdeal ≫
      ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c := by
    simp only [E, HomologicalComplex.comp_f, pullbackPresentationMap_f_negOne,
      doubleMapFunctorIso, asIso_hom, doubleMapFunctorHom, mkHomFromDouble_f₀,
      Category.assoc, Iso.inv_hom_id_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id]
    exact (congrArg (fun a => a ≫ h.pullbackConormalMap ≫ Q.conormalToIdeal)
      ((modulePullback g).map_id (presentationSequence P).X₁)).trans
        ((Category.id_comp _).trans h.pullbackConormalMap_comp_conormalToIdeal)
  have hleft : E.hom ≫ h.pullbackPresentationMap ≫ classCochain Q =
      ConormalClassCochain.classMap ((modulePullback g).map (presentationDifferential P))
        ((modulePullback g).map P.conormalToIdeal ≫
          ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c) :=
    (Category.assoc _ _ _).symm.trans
      ((ConormalClassNaturality.classMap_naturality
        (C := SheafOfModules.{u} (structureSheafRing Y))
        ((modulePullback g).map (presentationDifferential P)) (presentationDifferential Q)
        (E.hom ≫ h.pullbackPresentationMap) Q.conormalToIdeal).trans
          (congrArg (ConormalClassCochain.classMap
            ((modulePullback g).map (presentationDifferential P))) hδ))
  have hm := ConormalClassNaturality.classMap_map
    (C := SheafOfModules.{u} (structureSheafRing X))
    (D := SheafOfModules.{u} (structureSheafRing Y)) (presentationDifferential P)
    (modulePullback g) P.conormalToIdeal
  have hr := congrArg (fun z => E.hom ≫ z ≫
    ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
      (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c))⟦(1 : ℤ)⟧') hm
  have hright : E.hom ≫
      ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (classCochain P) ≫ coefficientTransport c =
      ConormalClassCochain.classMap ((modulePullback g).map (presentationDifferential P))
        ((modulePullback g).map P.conormalToIdeal ≫
          ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c) := by
    simpa only [classCochain, coefficientTransport, E, Category.assoc,
      Iso.hom_inv_id_assoc, ConormalClassNaturality.classMap_coefficient] using hr
  exact hleft.trans hright.symm

/-- The original direct derived arrow, read on the genuine extension
presentations, is the genuine compatible presentation map. -/
theorem derived_presentation_square (h : CompatibleMorphism P Q c) :
    (derivedPullback g).map (DerivedCategory.Q.map (CompatibleMorphism.comparisonX P)) ≫
      derivedPullbackNaiveCotangentMap g f =
    (DirectCotangentComparison.comparisonNat g).app (presentationComplex P) ≫
      DerivedCategory.Q.map h.pullbackPresentationMap ≫
      DerivedCategory.Q.map (CompatibleMorphism.comparisonY Q) := by
  rw [DirectCotangentComparison.directMap_eq]
  have hn := DirectCotangentComparison.comparison_naturality g
    (CompatibleMorphism.comparisonX P)
  calc
    _ = (DirectCotangentComparison.comparisonNat g).app _ ≫
        DerivedCategory.Q.map
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (CompatibleMorphism.comparisonX P) ≫ pullbackNaiveCotangentMap g f) := by
      rw [Functor.map_comp, ← Category.assoc, hn, Category.assoc]
    _ = (DirectCotangentComparison.comparisonNat g).app _ ≫
        DerivedCategory.Q.map
          (h.pullbackPresentationMap ≫ CompatibleMorphism.comparisonY Q) :=
      congrArg (fun a => (DirectCotangentComparison.comparisonNat g).app _ ≫
        DerivedCategory.Q.map a) h.pullbackPresentationMap_comp_comparison.symm
    _ = _ := by simp only [Functor.map_comp]

/-- A genuine compatible morphism with zero target extension class
forces zero restriction of its actual source extension class along the
actual original direct cotangent arrow. -/
theorem restrict_extClass_eq_zero (h : CompatibleMorphism P Q c) (hP : P.toAlgebraSquareZeroExtension.toPresented.extClass = 0) :
    derivedPullbackNaiveCotangentMap g f ≫ Q.toAlgebraSquareZeroExtension.toPresented.extClass = 0 := by
  have : IsIso (DerivedCategory.Q.map (CompatibleMorphism.comparisonX P)) :=
    PresentedSquareZeroExtension.isIso_Q_map_comparison f P.generators P.generatorsMap
  apply (cancel_epi
    ((derivedPullback g).map (DerivedCategory.Q.map (CompatibleMorphism.comparisonX P)))).mp
  rw [← Category.assoc, derived_presentation_square h]
  simp only [Category.assoc]
  rw [comparison_class Q]
  rw [← Functor.map_comp_assoc, compatible_classCochain h, Functor.map_comp]
  simp only [Category.assoc]
  have hz := comparison_classCochain_zero (g := g) P hP
  have ht := congrArg
    (fun a : (derivedPullback g).obj (DerivedCategory.Q.obj (presentationComplex P)) ⟶
        DerivedCategory.Q.obj
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)⟦(1 : ℤ)⟧)) =>
      a ≫ DerivedCategory.Q.map (coefficientTransport c) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj G)) hz
  simpa only [Category.assoc, zero_comp, comp_zero] using ht

end M9Native.CompatibleMorphismClassNecessity
