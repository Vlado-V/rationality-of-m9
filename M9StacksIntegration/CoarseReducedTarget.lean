module

public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget

@[expose] public section

/-!
Reducedness of a categorical coarse target.  The target is retained with its original
scheme structure: its full reduction is proved isomorphic to it by the categorical
universal property.  No separation or finiteness hypothesis on the target is used.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.CoarseReducedTarget

universe u

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem closed_space_map
    {Z Y : AlgebraicSpaces B S hS} (i : Z ⟶ Y)
    (hi : Space.IsClosedImmersion B S hS i.hom) :
    Stack.AlgebraicStacks.IsClosedImmersion B S hS
      (Stack.algebraicSpaceStackMap.{u, u + 1} B S hS Z.property Y.property i.hom) := by
  let iS := Stack.algebraicSpaceStackMap.{u, u + 1} B S hS Z.property Y.property i.hom
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS iS.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.property).property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z.obj Z.property) _
  have : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
    Space.isClosedImmersion_isLocalAtTarget_fpqc B S hS
  have : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  refine ⟨hrep, (Stack.isClosedImmersion_iff_hasRelativeProperty B S hS iS.hom hrep).2 ?_⟩
  have h := Stack.hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.closedImmersionProperty B S hS) iS.hom hrep Z.obj Y.obj Z.property Y.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  rw [Stack.representingMap_associatedMap] at h
  exact h.2 hi

/-- A map out of a reduced stack factors through every surjective closed immersion
of algebraic spaces into its target.  The lift and its comparison are constructed
from the closed substack, rather than supplied as premises. -/
theorem exists_lift_surjective_closed
    (X : Stack.AlgebraicStacks.{u, u + 1} B S hS)
    (Y Z : AlgebraicSpaces B S hS)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.property)
    (i : Z ⟶ Y) (hi : Space.IsClosedImmersion B S hS i.hom)
    (hsurj : Space.IsSurjective B S hS i.hom)
    (hred : Stack.IsReducedStack B S hS X) :
    ∃ g : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B S hS Z.obj Z.property,
      Nonempty (g ≫ Stack.algebraicSpaceStackMap.{u, u + 1} B S hS
        Z.property Y.property i.hom ≅ f) := by
  classical
  let YS := Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.property
  let ZS := Stack.algebraicSpaceStack.{u, u + 1} B S hS Z.obj Z.property
  let iS : ZS ⟶ YS := Stack.algebraicSpaceStackMap.{u, u + 1} B S hS
    Z.property Y.property i.hom
  have hci : Stack.AlgebraicStacks.IsClosedImmersion B S hS iS :=
    closed_space_map B S hS i hi
  have himm : Stack.AlgebraicStacks.IsImmersion B S hS iS :=
    ⟨hci.1, fun U y hy F hF he =>
      Space.isImmersion_of_isClosedImmersion B S hS (hci.2 U y hy F hF he)⟩
  let P := (CatFiberedInGroupoids.homFunctor iS.hom).essImage
  have hP : Stack.IsClosedSubstack YS P :=
    Stack.AlgebraicStacks.isClosedSubstack_essImage iS hci
  have hA := hP.2.choose
  obtain ⟨e, he, ⟨θ⟩⟩ :=
    Stack.AlgebraicStacks.exists_isEquivalence_to_essImage iS himm hA
  have hiSurj : Stack.IsSurjective B S hS iS := by
    apply Stack.isSurjective_of_isSurjective_representingMap B S hS Z.obj Y.obj
      Z.property Y.property (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) iS
    simpa only [iS, ZS, YS, Stack.algebraicSpaceStackMap,
      Stack.representingMap_associatedMap] using hsurj
  have hInclSurj : Stack.IsSurjective B S hS
      (Stack.fullSubcategoryInclusion YS P hA) := by
    intro y
    obtain ⟨z, hz⟩ := hiSurj y
    refine ⟨Stack.AlgebraicStacks.pointsMap B S hS e z, ?_⟩
    exact (congrFun (Stack.AlgebraicStacks.pointsMap_comp B S hS e
      (Stack.fullSubcategoryInclusion YS P hA)) z).symm.trans
      ((congrFun (Stack.AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS θ.hom) z).trans hz)
  have hfac : Stack.FactorsThroughSubstack f P :=
    (Stack.factorsThroughSubstack_iff_range_pointsMap_subset B S hS f hP hA hred).2
      (by rw [hInclSurj.range_eq]; exact Set.subset_univ _)
  let a := Stack.factorsThroughSubstackHom f hA hfac
  let α := Stack.factorsThroughSubstackIso f hA hfac
  obtain ⟨G, hG, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over ZS.val.val.p
      (Stack.fullSubcategoryAlgebraicStack YS P hA).val.val.p
      ZS.val.property
      (Stack.fullSubcategoryAlgebraicStack YS P hA).val.property
      e.hom.hom.toFunctor e.hom.hom.w he
  let b : Stack.fullSubcategoryAlgebraicStack YS P hA ⟶ ZS :=
    Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (⟨G, hG⟩ : _ ⥤ᵇ _))
  have ε' : b ≫ e ≅ 𝟙 _ :=
    Bicategory.InducedBicategory.isoMk
      (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε))
  refine ⟨a ≫ b, ⟨?_⟩⟩
  exact Bicategory.whiskerLeftIso (a ≫ b) θ.symm ≪≫
    (Bicategory.associator (a ≫ b) e _).symm ≪≫
    Bicategory.whiskerRightIso (Bicategory.associator a b e) _ ≪≫
    Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso a ε') _ ≪≫
    Bicategory.whiskerRightIso (Bicategory.rightUnitor a) _ ≪≫ α

/-- Every categorical moduli space of a reduced algebraic stack is reduced.
The assertion concerns the actual target, including its original nilpotent structure. -/
theorem reduced_of_categorical
    (X : Stack.AlgebraicStacks.{u, u + 1} B S hS)
    (Y : AlgebraicSpaces B S hS)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.property)
    (hf : Stack.IsCategoricalModuliSpace B S hS Y f.hom)
    (hred : Stack.IsReducedStack B S hS X) :
    Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsReduced T) := by
  classical
  let Z := Space.reducedClosedSubspace B S hS Y.obj Y.property Set.univ isClosed_univ
  have hZ := Space.isClosedSubspace_reducedClosedSubspace B S hS Y.obj Y.property
    Set.univ isClosed_univ
  have hZred := Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS
    Y.obj Y.property Set.univ isClosed_univ
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.1⟩
  let i : Zsp ⟶ Y := ObjectProperty.homMk Z.ι
  have hi : Space.IsClosedImmersion B S hS i.hom := hZ.2
  have hsurj : Space.IsSurjective B S hS i.hom := by
    change Function.Surjective (Space.pointsMap B S hS Z.toFunctor Z.ι)
    exact Set.range_eq_univ.mp
      (Space.range_pointsMap_ι_reducedClosedSubspace B S hS Y.obj Y.property
        Set.univ isClosed_univ)
  obtain ⟨g, ⟨hfac⟩⟩ := exists_lift_surjective_closed B S hS X Y Zsp f i hi hsurj hred
  obtain ⟨χ, ⟨hχ⟩, -⟩ := hf Zsp g.hom
  have hfac' : g.hom ≫ (Stack.associatedMap B S hS i.hom).1 ≅ f.hom :=
    Bicategory.InducedBicategory.isoHom hfac
  have hχi : χ ≫ i = 𝟙 Y := by
    apply Stack.eq_of_isCategoricalModuliSpace B S hS hf f.hom
    · change Nonempty (f.hom ≫ (Stack.associatedMap B S hS (χ.hom ≫ i.hom)).1 ≅ f.hom)
      rw [Stack.associatedMap_comp]
      exact ⟨(Bicategory.associator _ _ _).symm ≪≫
        Bicategory.whiskerRightIso hχ _ ≪≫ hfac'⟩
    · change Nonempty (f.hom ≫ (Stack.associatedMap B S hS (𝟙 Y.obj)).1 ≅ f.hom)
      rw [Stack.associatedMap_id_eq]
      exact ⟨Bicategory.rightUnitor f.hom⟩
  have hMonoRaw : Mono ((ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).map i) := by
    change Mono Z.ι
    infer_instance
  have : Mono i := Functor.ReflectsMonomorphisms.reflects _ hMonoRaw
  let e : Zsp ≅ Y := ⟨i, χ, (cancel_mono i).1 (by simp [Category.assoc, hχi]), hχi⟩
  exact Space.hasEtaleLocalProperty_of_iso B S hS (fun T : Scheme.{u} => IsReduced T)
    ((ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F)).mapIso e) hZred

end M9Native.CoarseReducedTarget
