module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-! Equivalences genuinely over a base transport through the native strict
pullback, retaining both the original object and its specified base map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory StacksRepresentableCFG

namespace M9Native.StrictPullbackEquivalence

universe uC vC uD vD uE vE uF vF

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {F : Type uF} [Category.{vF} F]
  (f : C ⥤ D) {p : E ⥤ D} {q : F ⥤ D}

/-- The literal native pullback functor of a morphism over the base. -/
def transportMorphism (H : MorphismOver p q) :
    MorphismOver (StrictPullback.structureFunctor f p)
      (StrictPullback.structureFunctor f q) where
  functor := StrictPullback.liftFib (StrictPullback.structureFunctor f p)
    (StrictPullback.pr f p ⋙ H.functor) (by
      rw [Functor.assoc, H.w, StrictPullback.pr_comp_eq])
  w := rfl

@[simp] theorem transportMorphism_obj_base (H : MorphismOver p q)
    (X : StrictPullback f p) :
    ((transportMorphism f H).functor.obj X).base = X.base := rfl

@[simp] theorem transportMorphism_obj_fib (H : MorphismOver p q)
    (X : StrictPullback f p) :
    ((transportMorphism f H).functor.obj X).fib = H.functor.obj X.fib := rfl

@[simp] theorem transportMorphism_map_base (H : MorphismOver p q)
    {X Y : StrictPullback f p} (a : X ⟶ Y) :
    ((transportMorphism f H).functor.map a).base = a.base := rfl

@[simp] theorem transportMorphism_map_fib (H : MorphismOver p q)
    {X Y : StrictPullback f p} (a : X ⟶ Y) :
    ((transportMorphism f H).functor.map a).fib = H.functor.map a.fib := rfl

/-- An original isomorphism over the same specified base gives an actual
isomorphism in the strict pullback, with its original hom component. -/
def isoOfFiber {X Y : StrictPullback f p} (hb : X.base = Y.base)
    (e : X.fib ≅ Y.fib) (he : p.IsHomLift (𝟙 (f.obj X.base)) e.hom) : X ≅ Y := by
  have hover : p.map e.hom = eqToHom X.over ≫ f.map (eqToHom hb) ≫
      eqToHom Y.over.symm := by
    haveI := he
    have h := IsHomLift.fac' p (𝟙 (f.obj X.base)) e.hom
    simpa only [eqToHom_map, Category.id_comp, Category.comp_id, eqToHom_trans] using h
  let a : X ⟶ Y := ⟨eqToHom hb, e.hom, hover⟩
  haveI : IsIso a.base := by change IsIso (eqToHom hb); infer_instance
  haveI : IsIso a.fib := by change IsIso e.hom; infer_instance
  haveI : IsIso a := StrictPullback.isIso_of_isIso_base_fib a
  exact asIso a

@[simp] theorem isoOfFiber_hom_base {X Y : StrictPullback f p} (hb : X.base = Y.base)
    (e : X.fib ≅ Y.fib) (he : p.IsHomLift (𝟙 (f.obj X.base)) e.hom) :
    (isoOfFiber f hb e he).hom.base = eqToHom hb := rfl

@[simp] theorem isoOfFiber_hom_fib {X Y : StrictPullback f p} (hb : X.base = Y.base)
    (e : X.fib ≅ Y.fib) (he : p.IsHomLift (𝟙 (f.obj X.base)) e.hom) :
    (isoOfFiber f hb e he).hom.fib = e.hom := rfl

/-- Transport of the genuine original unit, with no replaced base object. -/
def transportedUnit (e : EquivalenceOver p q) :
    𝟭 (StrictPullback f p) ≅
      (transportMorphism f e.hom).functor ⋙ (transportMorphism f e.inv).functor :=
  NatIso.ofComponents
    (fun X => isoOfFiber f rfl (e.unitIso.app X.fib)
      ((congrArg (fun U => p.IsHomLift (𝟙 U) (e.unitIso.hom.app X.fib)) X.over).mp
        (e.isHomLift_unitIso_hom_app X.fib)))
    (by
      intro X Y a
      apply StrictPullback.Hom.ext
      · change a.base ≫ 𝟙 Y.base = 𝟙 X.base ≫ a.base
        simp
      · exact e.unitIso.hom.naturality a.fib)

/-- Transport of the genuine original counit, retaining the original family. -/
def transportedCounit (e : EquivalenceOver p q) :
    (transportMorphism f e.inv).functor ⋙ (transportMorphism f e.hom).functor ≅
      𝟭 (StrictPullback f q) :=
  NatIso.ofComponents
    (fun X => isoOfFiber f rfl (e.counitIso.app X.fib)
      ((congrArg (fun U => q.IsHomLift (𝟙 U) (e.counitIso.hom.app X.fib)) X.over).mp
        (e.isHomLift_counitIso_hom_app X.fib)))
    (by
      intro X Y a
      apply StrictPullback.Hom.ext
      · change a.base ≫ 𝟙 Y.base = 𝟙 X.base ≫ a.base
        simp
      · exact e.counitIso.hom.naturality a.fib)

/-- An actual equivalence over the original base gives an actual equivalence
over the coefficient base. Its unit and counit keep the base identities. -/
def transportEquivalence (e : EquivalenceOver p q) :
    EquivalenceOver (StrictPullback.structureFunctor f p)
      (StrictPullback.structureFunctor f q) where
  hom := transportMorphism f e.hom
  inv := transportMorphism f e.inv
  unitIso := transportedUnit f e
  counitIso := transportedCounit f e
  unit_over := by
    apply whiskerRight_eq_eqToHom
    intro X
    change (StrictPullback.structureFunctor f p).IsHomLift (𝟙 X.base) _
    apply IsHomLift.of_fac' (StrictPullback.structureFunctor f p)
      (𝟙 X.base) ((transportedUnit f e).hom.app X) rfl rfl
    change (𝟙 X.base) = eqToHom (rfl : X.base = X.base) ≫
      𝟙 X.base ≫ eqToHom (rfl : X.base = X.base).symm
    simp
  counit_over := by
    apply whiskerRight_eq_eqToHom
    intro X
    change (StrictPullback.structureFunctor f q).IsHomLift (𝟙 X.base) _
    apply IsHomLift.of_fac' (StrictPullback.structureFunctor f q)
      (𝟙 X.base) ((transportedCounit f e).hom.app X) rfl rfl
    change (𝟙 X.base) = eqToHom (rfl : X.base = X.base) ≫
      𝟙 X.base ≫ eqToHom (rfl : X.base = X.base).symm
    simp

/-- Both original-family and specified-base projections commute literally. -/
theorem transport_original (H : MorphismOver p q) :
    (transportMorphism f H).functor ⋙ StrictPullback.pr f q =
      StrictPullback.pr f p ⋙ H.functor := rfl

end M9Native.StrictPullbackEquivalence
