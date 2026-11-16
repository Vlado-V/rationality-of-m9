module

public import StacksFrontier.AlgebraicGeometry.Stacks.PredeformationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.InnerSquareOfOuterTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase

/-! A comparison from the actual strict change of base to the native chosen
two-fibre product. The original projection and the smaller-base structure
functor are retained. The two models are not identified by definitional equality. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.StrictNativeStackBaseChange

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- The original-stack projection of the strict change of base, viewed over
the larger base. -/
def originalProjection (X : Stack.AlgebraicStacks.{u,w} B S' hS') :
    Stack.changeBaseAlgebraicStack B S S' hS hS' g
      (Stack.changeOfBase B S S' hS hS' g X) ⟶ X :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := StrictPullback.pr (Over.map g) X.val.val.p
      w := StrictPullback.pr_comp_eq _ _ })

/-- The actual strict change-of-base cone, with the original structure maps. -/
def strictSquare (X : Stack.AlgebraicStacks.{u,w} B S' hS') :
    Bicategory.TwoCommSq
      (Stack.structureMorphism B S' hS' (Stack.schemeStack B S' hS' (Over.mk g)))
      (Stack.structureMorphism B S' hS' X) where
  pt := Stack.changeBaseAlgebraicStack B S S' hS hS' g
    (Stack.changeOfBase B S S' hS hS' g X)
  fst := Stack.changeBaseStructureMorphism B S S' hS hS' g
    (Stack.changeOfBase B S S' hS hS' g X)
  snd := originalProjection B S S' hS hS' g X
  iso := eqToIso ((Stack.comp_structureMorphism B S' hS' _).trans
    (Stack.comp_structureMorphism B S' hS' _).symm)

/-- The original morphism gives a cone over the larger target's base change. -/
def mapCone {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    Bicategory.TwoCommSq
      (Stack.structureMorphism B S' hS' (Stack.schemeStack B S' hS' (Over.mk g)))
      (Stack.structureMorphism B S' hS' Y) where
  pt := (strictSquare B S S' hS hS' g X).pt
  fst := (strictSquare B S S' hS hS' g X).fst
  snd := originalProjection B S S' hS hS' g X ≫ f
  iso := eqToIso ((Stack.comp_structureMorphism B S' hS' _).trans
    (Stack.comp_structureMorphism B S' hS' _).symm)

/-- The canonical native lift retains both cone legs on the nose. -/
def mapOverLargerBase {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :=
  (Stack.canonicalPreHomAlgebraicStacks B S' hS' _ _
    (mapCone B S S' hS hS' g f)).hom

/-- A genuine morphism over the smaller base from the strict source model
to the chosen native two-fibre-product target. -/
def map {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    Stack.changeOfBase B S S' hS hS' g X ⟶
      Stack.algebraicStackBaseChange B S S' hS hS' g Y :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (mapOverLargerBase B S S' hS hS' g f).hom.hom.toFunctor
      w := by
        change (mapOverLargerBase B S S' hS hS' g f).hom.hom.toFunctor ⋙
          ((Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y).fst.hom.hom.toFunctor ⋙
            Over.iteratedSliceForward (Over.mk g)) = _
        change ((mapOverLargerBase B S S' hS hS' g f).hom.hom.toFunctor ⋙
          (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y).fst.hom.hom.toFunctor) ⋙
            Over.iteratedSliceForward (Over.mk g) = _
        change (Stack.changeBaseStructureMorphism B S S' hS hS' g
          (Stack.changeOfBase B S S' hS hS' g X)).hom.hom.toFunctor ⋙
            Over.iteratedSliceForward (Over.mk g) = _
        rfl })

/-- Every original object and arrow survives the actual comparison. -/
theorem map_original {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    (map B S S' hS hS' g f).hom.hom.toFunctor ⋙
        Stack.algebraicStackBaseChangeProjection B S S' hS hS' g Y =
      StrictPullback.pr (Over.map g) X.val.val.p ⋙ f.hom.hom.toFunctor := rfl

/-- The specified smaller-base structure is retained by the comparison. -/
theorem map_base {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    (map B S S' hS hS' g f).hom.hom.toFunctor ⋙
        (Stack.algebraicStackBaseChange B S S' hS hS' g Y).val.val.p =
      (Stack.changeOfBase B S S' hS hS' g X).val.val.p :=
  (map B S S' hS hS' g f).hom.hom.w

/-- Two 2-cells into a represented scheme stack agree when their endpoints
are fixed: the forgetful functor of the slice is faithful. -/
theorem twoHom_ext_scheme (T : BigFppfOver B S' hS')
    {A : Stack.AlgebraicStacks.{u,w} B S' hS'}
    {F G : A ⟶ Stack.schemeStack B S' hS' T} (a b : F ⟶ G) : a = b := by
  apply Bicategory.InducedBicategory.hom₂_ext
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext _ _
  apply NatTrans.ext
  funext x
  apply (Over.forget T).map_injective
  have ha : (Over.forget T).IsHomLift (𝟙 (A.val.val.p.obj x))
      (a.hom.hom.toNatTrans.app x) := a.hom.hom.isHomLift' x
  have hb : (Over.forget T).IsHomLift (𝟙 (A.val.val.p.obj x))
      (b.hom.hom.toNatTrans.app x) := b.hom.hom.isHomLift' x
  rw [IsHomLift.fac' (Over.forget T) (𝟙 (A.val.val.p.obj x)) _,
    IsHomLift.fac' (Over.forget T) (𝟙 (A.val.val.p.obj x)) _]

theorem twoIso_ext_scheme (T : BigFppfOver B S' hS')
    {A : Stack.AlgebraicStacks.{u,w} B S' hS'}
    {F G : A ⟶ Stack.schemeStack B S' hS' T} (a b : F ≅ G) : a = b := by
  apply Iso.ext
  exact twoHom_ext_scheme B S' hS' T a.hom b.hom

/-- Equality of the source and of the actual underlying functor determines
the morphism, without identifying different stack models. -/
theorem hom_heq_of_functor
    {A A' Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (e : A = A')
    {f : A ⟶ Y} {f' : A' ⟶ Y}
    (h : HEq f.hom.hom.toFunctor f'.hom.hom.toFunctor) : HEq f f' := by
  cases e
  apply heq_of_eq
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  exact BasedCategory.BasedFunctor.ext' (eq_of_heq h)

/-- A two-cartesian square can be read on its specified apex and legs.
The filler is unique because the common target is a represented scheme. -/
def normalizedSquare_isTwoFibreProduct
    (T : BigFppfOver B S' hS')
    {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'}
    {f : X ⟶ Stack.schemeStack B S' hS' T}
    {k : Y ⟶ Stack.schemeStack B S' hS' T}
    (Q : Bicategory.TwoCommSq f k) (hQ : Bicategory.IsTwoFibreProduct Q)
    (A : Stack.AlgebraicStacks.{u,w} B S' hS') (a : A ⟶ X) (b : A ⟶ Y)
    (e : Q.pt = A) (ea : HEq Q.fst a) (eb : HEq Q.snd b) (i : a ≫ f ≅ b ≫ k) :
    Bicategory.IsTwoFibreProduct (⟨A, a, b, i⟩ : Bicategory.TwoCommSq f k) := by
  cases e
  have ea' : Q.fst = a := eq_of_heq ea
  have eb' : Q.snd = b := eq_of_heq eb
  subst a b
  have hi : i = Q.iso := twoIso_ext_scheme B S' hS' T i Q.iso
  subst i
  exact hQ

/-- The native strict change-of-base witness proves two-cartesianness of the
literal source square; its apex and legs are transported by their proved
equalities, rather than postulated to be another model. -/
def strictSquare_isTwoFibreProduct (X : Stack.AlgebraicStacks.{u,w} B S' hS') :
    Bicategory.IsTwoFibreProduct (strictSquare B S S' hS hS' g X) := by
  obtain ⟨f, k, hf, hk, Q, hpt, hsnd, hfst, hQ⟩ :=
    (Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g X).some
  have ef : f = Stack.structureMorphism B S' hS' X := by
    apply Bicategory.InducedBicategory.hom_ext
    apply Bicategory.InducedBicategory.hom_ext
    apply BasedCategory.BasedFunctor.ext'
    rw [hf]
    rfl
  have ek : k = Stack.structureMorphism B S' hS'
      (Stack.schemeStack B S' hS' (Over.mk g)) := by
    apply Bicategory.InducedBicategory.hom_ext
    apply Bicategory.InducedBicategory.hom_ext
    apply BasedCategory.BasedFunctor.ext'
    rw [hk]
    rfl
  subst f k
  exact normalizedSquare_isTwoFibreProduct B S' hS'
    (Over.mk (𝟙 (B.obj hS'))) Q.swap (Bicategory.isTwoFibreProduct_swap hQ)
    (strictSquare B S S' hS hS' g X).pt
    (strictSquare B S S' hS hS' g X).fst
    (strictSquare B S S' hS hS' g X).snd hpt
    (Stack.AlgebraicStacks.heq_mkHom B S' hS' hpt hsnd)
    (hom_heq_of_functor B S' hS' hpt hfst)
    (strictSquare B S S' hS hS' g X).iso


/-- The inner square of the two original base-change squares. Its first
leg is a genuine base change of the original morphism. -/
def innerSquare {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :=
  Stack.innerSquareOfOuter B S' hS'
    (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' _ _)
    (eqToIso (Stack.comp_structureMorphism B S' hS' f))
    (strictSquare B S S' hS hS' g X)

def innerSquare_isTwoFibreProduct {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'}
    (f : X ⟶ Y) : Bicategory.IsTwoFibreProduct (innerSquare B S S' hS hS' g f) :=
  Stack.isTwoFibreProduct_innerSquareOfOuter B S' hS'
    (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' _ _)
    (eqToIso (Stack.comp_structureMorphism B S' hS' f))
    (strictSquare B S S' hS hS' g X)
    (strictSquare_isTwoFibreProduct B S S' hS hS' g X)

/-- The inner square has the same literal coefficient and original-family
legs as the explicit comparison cone, up to its derived comparison 2-cells. -/
def innerPreHom {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    Bicategory.TwoCommSq.PreHom (mapCone B S S' hS hS' g f)
      (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y) where
  hom := (innerSquare B S S' hS hS' g f).fst
  isoFst := Stack.innerSquareOfOuter_fst_comp_iso B S' hS'
    (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' _ _)
    (eqToIso (Stack.comp_structureMorphism B S' hS' f))
    (strictSquare B S S' hS hS' g X)
  isoSnd := Bicategory.whiskerRightIso
      (Stack.innerSquareOfOuter_snd_iso B S' hS'
        (Stack.algebraicStackBaseChangeSquare B S S' hS hS' g Y)
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' _ _)
        (eqToIso (Stack.comp_structureMorphism B S' hS' f))
        (strictSquare B S S' hS hS' g X)) f ≪≫
    (innerSquare B S S' hS hS' g f).iso.symm
  compat := by
    exact twoHom_ext_scheme B S' hS' (Over.mk (𝟙 (B.obj hS'))) _ _

/-- Universal uniqueness supplies the genuine 2-isomorphism between the
literal comparison and the base-changed original morphism. -/
def mapComparisonIso {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y) :
    mapOverLargerBase B S S' hS hS' g f ≅ (innerSquare B S S' hS hS' g f).fst :=
  (Bicategory.twoFibreProductPreHom_rel
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' _ _)
    (Stack.canonicalPreHomAlgebraicStacks B S' hS' _ _ (mapCone B S S' hS hS' g f))
    (innerPreHom B S S' hS hS' g f)).choose

/-- Open immersions are unchanged by a 2-isomorphism of their actual map. -/
theorem open_of_iso {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'}
    {f f' : X ⟶ Y} (e : f ≅ f')
    (hf' : Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f') :
    Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f := by
  have : (BasedFunctor.id X.val.val).toFunctor.IsEquivalence :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 X.val.val.obj))
  have : (BasedFunctor.id Y.val.val).toFunctor.IsEquivalence :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 Y.val.val.obj))
  let ei := Stack.twoIsoHomIso B S' hS'
    (Stack.algebraicStacksTwoIsoHom B S' hS' e.symm)
  exact ⟨(Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences B S' hS'
      f.hom.hom f'.hom.hom (BasedFunctor.id X.val.val) (BasedFunctor.id Y.val.val) ei).1 hf'.1,
    Stack.relativeProperty_of_equivalences B S' hS' (Space.openImmersionProperty B S' hS')
      f.hom.hom f'.hom.hom (BasedFunctor.id X.val.val) (BasedFunctor.id Y.val.val) ei hf'.2⟩

/-- The explicit comparison over the larger base is an open immersion when
the original morphism is, by actual two-cartesian base change. -/
theorem mapOverLargerBase_isOpenImmersion
    {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y)
    (hf : Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f) :
    Stack.AlgebraicStacks.IsOpenImmersion B S' hS'
      (mapOverLargerBase B S S' hS hS' g f) := by
  apply open_of_iso B S' hS' (mapComparisonIso B S S' hS hS' g f)
  exact Stack.AlgebraicStacks.isOpenImmersion_baseChange_snd B S' hS'
    (innerSquare B S S' hS hS' g f).swap
    (Bicategory.isTwoFibreProduct_swap (innerSquare_isTwoFibreProduct B S S' hS hS' g f)) hf

/-- Actual endpoint equalities and equality of the underlying functor
transport the map without claiming two models are definitionally equal. -/
theorem hom_heq_of_functor₂
    {A A' Y Y' : Stack.AlgebraicStacks.{u,w} B S' hS'} (eA : A = A') (eY : Y = Y')
    {f : A ⟶ Y} {f' : A' ⟶ Y'}
    (h : HEq f.hom.hom.toFunctor f'.hom.hom.toFunctor) : HEq f f' := by
  cases eY
  exact hom_heq_of_functor B S' hS' eA h

theorem property_of_heq₂ {C : Type*} [CategoryStruct C]
    (P : ∀ {X Y : C}, (X ⟶ Y) → Prop)
    {X X' Y Y' : C} (eX : X = X') (eY : Y = Y')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : HEq f f') (hf : P f) : P f' := by
  cases eX
  cases eY
  cases eq_of_heq e
  exact hf

/-- The open-immersion conclusion holds over the original smaller base. -/
theorem map_isOpenImmersion
    {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y)
    (hf : Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f) :
    Stack.AlgebraicStacks.IsOpenImmersion B S hS (map B S S' hS hS' g f) := by
  let m := map B S S' hS hS' g f
  let mr : Stack.changeBaseAlgebraicStack B S S' hS hS' g
        (Stack.changeOfBase B S S' hS hS' g X) ⟶
      Stack.changeBaseAlgebraicStack B S S' hS hS' g
        (Stack.algebraicStackBaseChange B S S' hS hS' g Y) :=
    Bicategory.InducedBicategory.mkHom (Stack.changeBaseHom B S S' hS hS' g m.hom)
  have eY := Stack.changeBaseAlgebraicStacks_algebraicStackBaseChange B S S' hS hS' g Y
  have em : HEq mr (mapOverLargerBase B S S' hS hS' g f) :=
    hom_heq_of_functor₂ B S' hS' rfl eY HEq.rfl
  have hr : Stack.AlgebraicStacks.IsOpenImmersion B S' hS' mr :=
    property_of_heq₂
      (fun {A C : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : A ⟶ C) =>
        Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f)
      rfl eY.symm em.symm (mapOverLargerBase_isOpenImmersion B S S' hS hS' g f hf)
  exact ⟨(Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
      m.hom.hom).1 hr.1,
    (Stack.isOpenImmersion_changeBaseHom_iff B S S' hS hS' g m.hom).1 hr.2⟩

/-- Smoothness is derived from the proved open immersion of the comparison. -/
theorem map_isSmooth
    {X Y : Stack.AlgebraicStacks.{u,w} B S' hS'} (f : X ⟶ Y)
    (hf : Stack.AlgebraicStacks.IsOpenImmersion B S' hS' f) :
    Stack.AlgebraicStacks.IsSmooth B S hS (map B S S' hS hS' g f) :=
  Stack.AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS _
    (map_isOpenImmersion B S S' hS hS' g f hf)

end M9Native.StrictNativeStackBaseChange
