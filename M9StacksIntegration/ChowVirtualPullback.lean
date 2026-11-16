module

public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedIntertwining

/-!
# Genuine flat pullback of the virtual Chern and ordered Schur operators

The native cap-family naturality theorem applies to actual flat pullback
on Chow groups. The native formal-inverse theorem uses an equivalent
degree-lowering convention. The explicit transport below connects those
two native conventions, so that inverse, virtual and ordered Schur
families inherit genuine flat-pullback naturality.

No arbitrary-morphism Chow pullback, Chern comparison, Schur vanishing or
geometric pushforward is an input or conclusion of this leaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.ChowVirtualPullback

open GradedCapVirtualSchur

section Generic

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]
  {d : ℤ} (pull : ∀ k : ℤ, G k →+ H (k+d))

/-- The same actual degree-shifting map in the native lowering spelling. -/
def loweringPull (k : ℤ) : G k →+ H (k - (-d)) :=
  (gradedDegreeCast H (show k+d = k-(-d) by omega)).toAddMonoidHom.comp (pull k)

theorem loweringPull_heq (k : ℤ) (x : G k) :
    loweringPull pull k x ≍ pull k x :=
  gradedDegreeCast_heq (show k+d = k-(-d) by omega) (pull k x)

/-- The two native intertwining conventions differ only by the displayed
degree transport, with no compatibility hypothesis added. -/
theorem intertwines_iff_lowering (a : GradedCapFamily G) (b : GradedCapFamily H) :
    Stacks.Chow.Intertwines pull a b ↔
      a.Intertwines (-d) (loweringPull pull) b := by
  constructor
  · intro h
    apply GradedCapFamily.Intertwines.iff_heq.2
    intro k i x
    exact (loweringPull_heq pull (k-i) (a k i x)).trans
      (((heq_of_eq (h k i x)).trans (gradedDegreeCast_heq _ _)).trans
        (b.apply_heq (by omega) i (loweringPull_heq pull k x).symm))
  · intro h k i x
    apply eq_of_heq
    exact (loweringPull_heq pull (k-i) (a k i x)).symm.trans
      ((GradedCapFamily.Intertwines.iff_heq.1 h k i x).trans
        ((b.apply_heq (by omega) i (loweringPull_heq pull k x)).trans
          (gradedDegreeCast_heq _ _).symm))

/-- Native formal inversion preserves the original naturality relation. -/
theorem intertwines_gradedRightInv {a : GradedCapFamily G} {b : GradedCapFamily H}
    (h : Stacks.Chow.Intertwines pull a b) :
    Stacks.Chow.Intertwines pull (gradedRightInv a) (gradedRightInv b) :=
  (intertwines_iff_lowering pull _ _).2
    (((intertwines_iff_lowering pull a b).1 h).gradedRightInv)

/-- The literal ordered degree-nine Schur polynomial respects a native
intertwiner; no commutativity of the operator ring is used. -/
theorem intertwines_schur333 {a : GradedCapFamily G} {b : GradedCapFamily H}
    (h : Stacks.Chow.Intertwines pull a b) :
    Stacks.Chow.Intertwines pull (schur333 a) (schur333 b) := by
  apply (intertwines_iff_lowering pull _ _).2
  have h' := (intertwines_iff_lowering pull a b).1 h
  have h1 := h'.homComponent 1
  have h2 := h'.homComponent 2
  have h3 := h'.homComponent 3
  have h4 := h'.homComponent 4
  have h5 := h'.homComponent 5
  exact (((((h3.mul h3).mul h3).sub ((h3.mul h4).mul h2)).sub
      ((h4.mul h2).mul h3)).add ((h4.mul h4).mul h1)).add
      ((h5.mul h2).mul h2) |>.sub ((h5.mul h3).mul h1)

end Generic

section ActualChow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
  (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
  (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
  (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ qX = qY) (d : ℕ) (hd : RelativeDimension f d)

/-- This is the genuine native flat pullback on the original Chow groups. -/
abbrev actualPull (k : ℤ) : chowGroup C qX k →+ chowGroup C qY (k+(d:ℤ)) :=
  flatPullbackChow C qY qX f hf d hd k
    (flatPullbackFactorsThroughRationalEquivalence_general C qY qX f hf d hd k)

variable (E : X.Modules) (rE : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E rE]
  (E' : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E' rE]
  (eE : E' ≅ (Scheme.Modules.pullback f).obj E)

include eE

/-- The inverse of the genuine total Chern family is carried to the
inverse of the actual pulled-back bundle's family. -/
theorem inverseFamily_flatPullback :
    Stacks.Chow.Intertwines (actualPull C qX qY f hf d hd)
      (inverseFamily C qX E rE) (inverseFamily C qY E' rE) := by
  rw [inverseFamily_eq_gradedRightInv, inverseFamily_eq_gradedRightInv]
  exact intertwines_gradedRightInv _
    (intertwines_chernFamily C qX E rE qY f hf d hd E' eE)

variable (F : X.Modules) (rF : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
  (F' : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F' rF]
  (eF : F' ≅ (Scheme.Modules.pullback f).obj F)

include eF

/-- Genuine flat pullback transports the actual virtual family
c(F)c(E)^{-1}, with the original multiplication order. -/
theorem virtualFamily_flatPullback :
    Stacks.Chow.Intertwines (actualPull C qX qY f hf d hd)
      (virtualFamily C qX F E rF rE) (virtualFamily C qY F' E' rF rE) :=
  (intertwines_chernFamily C qX F rF qY f hf d hd F' eF).convolve
    (inverseFamily_flatPullback C qX qY f hf d hd E rE E' eE)

/-- The literal actual Schur operator has genuine flat-pullback
naturality, derived from native Chern naturality and inversion. -/
theorem schur333_flatPullback :
    Stacks.Chow.Intertwines (actualPull C qX qY f hf d hd)
      (schur333 (virtualFamily C qX F E rF rE))
      (schur333 (virtualFamily C qY F' E' rF rE)) :=
  intertwines_schur333 _
    (virtualFamily_flatPullback C qX qY f hf d hd E rE E' eE F rF F' eF)

end ActualChow

end M9Native.ChowVirtualPullback
