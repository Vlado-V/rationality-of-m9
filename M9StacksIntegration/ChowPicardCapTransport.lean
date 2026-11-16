module

public import M9StacksIntegration.ChowPicardCap

/-!
# Proper transport of the actual Picard first-Chern caps

The actual Picard pullback is compared with the actual module pullback
of the native representative. Native Stacks 02SU then supplies the cap
projection formula, including arbitrary finite words of these caps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ChowPicardCapTransport

open Stacks.Chow ChowCapWords CurvePowerChowFunctional ChowPicardCap

def pullbackLine {X Y : Scheme.{u}} (g : Y ⟶ X) (L : InvertibleLine X) :
    InvertibleLine Y :=
  ⟨(Scheme.Modules.pullback g).obj L.1,
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      g.toLRSHom.toShHom L.1 L.2⟩

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (fX : X ⟶ C.S)
  [LocallyOfFiniteType fX] (fY : Y ⟶ C.S) [LocallyOfFiniteType fY]
  (g : Y ⟶ X)

theorem capFun_pullback_repr (d : ℤ) (x : Stacks.Picard.ofScheme X) :
    capFun C fY d (Stacks.Picard.schemePullbackClass g x) =
      (lineCap C fY (pullbackLine g (chosenLine x))).capOnChow C fY d := by
  have h := Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom
    (chosenLine x).1 (chosenLine x).2
  have hx : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
      (chosenLine x).1 (chosenLine x).2 = x :=
    Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x
  rw [hx] at h
  have hp : Stacks.Picard.schemePullbackClass g x =
      Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf
        (pullbackLine g (chosenLine x)).1 (pullbackLine g (chosenLine x)).2 := h
  rw [hp]
  exact capFun_picardClass C fY d _ (pullbackLine g (chosenLine x)).2

theorem capFun_proper [IsProper g] (hg : g ≫ fX = fY) (d : ℤ)
    (x : Stacks.Picard.ofScheme X) (a : chowGroup C fY (d + 1)) :
    properChowPushforward C fY fX g hg d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY fX g hg d)
        (capFun C fY d (Stacks.Picard.schemePullbackClass g x) a) =
      capFun C fX d x (properChowPushforward C fY fX g hg (d + 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY fX g hg (d + 1))
        a) := by
  rw [capFun_pullback_repr (C := C) (fY := fY) (g := g)]
  let L := chosenLine x
  have hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.1 := L.2
  exact properChowPushforward_invCap_capOnChow C fY fX g hg d L.1 a

theorem iterated_capFun_proper [IsProper g] (hg : g ≫ fX = fY)
    (xs : List (Stacks.Picard.ofScheme X)) (d : ℤ)
    (a : chowGroup C fY
      (d + ((xs.map fun x => lineCap C fY
        (chosenLine (Stacks.Picard.schemePullbackClass g x))).length : ℤ)))
    (b : chowGroup C fX (d + ((xs.map fun x => lineCap C fX (chosenLine x)).length : ℤ)))
    (hab : b ≍ properChowPushforward C fY fX g hg _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY fX g hg _) a) :
    properChowPushforward C fY fX g hg d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY fX g hg d)
        (iteratedChernCapOnChow C fY
          (xs.map fun x => lineCap C fY (chosenLine (Stacks.Picard.schemePullbackClass g x)))
          d a) =
      iteratedChernCapOnChow C fX (xs.map fun x => lineCap C fX (chosenLine x)) d b := by
  apply properChowPushforward_iteratedChernCapOnChow_of_forall₂ C fY fX g hg _ d a b hab
  clear hab b a
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
      exact List.Forall₂.cons (fun e z => capFun_proper C fX fY g hg e x z) ih

end M9Native.ChowPicardCapTransport
