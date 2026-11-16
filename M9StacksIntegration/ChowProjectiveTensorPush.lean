module

public import M9StacksIntegration.ChowProjectiveMomentInverse
public import M9StacksIntegration.ChowLineProperPush
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTensor

/-! Actual projective pushforward of the top Chern cap of a tautological
line twist. The tensor formula, flat pullback and proper pushforward are
the original native operations on the integer-graded Chow groups. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowProjectiveTensorPush

section Tensor

variable (C : ChowSituation.{u}) {P : Scheme.{u}} (q : P ⟶ C.S)
  [LocallyOfFiniteType q] (F : P.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r] (L : P.Modules)
  [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]

def tensorTopCap (k : ℤ) : chowGroup C q k →+ chowGroup C q (k-r) :=
  @chernCap C r P q inferInstance
    (((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj F).obj L)
    (isFiniteLocallyFreeOfRank_sheafTensor F r L) k (Fin.last r)

def tensorTerm (k : ℤ) (j : Fin (r+1)) (α : chowGroup C q k) :
    chowGroup C q (k-r) :=
  chowGroupCast C q (by have hj := j.isLt; simp only [Fin.val_mk]; omega)
    (chernCap C r q F (k-(j:ℤ)) ⟨r-(j:ℕ), by omega⟩
      (capPow C q (invCap C q L) (j:ℕ) k (k-(j:ℤ)) (by ring) α))

theorem tensorTopCap_apply (k : ℤ) (α : chowGroup C q k) :
    tensorTopCap C q F r L k α = ∑ j : Fin (r+1), tensorTerm C q F r L k j α := by
  have h := chernCap_sheafTensor C q F r L k (Fin.last r) α
  simpa only [tensorTopCap, tensorTerm, Fin.val_last, Nat.sub_self,
    zero_add, Nat.choose_self, Nat.cast_one, one_smul] using h

end Tensor

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

def tensorProjection (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C q (k-b) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let qP := bundleProj E ≫ q
  let PF := (Scheme.Modules.pullback (bundleProj E)).obj F
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  let β := capPow C qP (invCap C qP (bundleTwist E)) a (k+n) (k+n-a) (by ring)
    (bundlePullback C q qP (bundleProj E) rfl n (Stacks.Chow.relativeDimension_bundleProj E n) k α)
  exact ChowLineProperPush.properPush C qP q (bundleProj E) rfl (k-b)
    (chowGroupCast C qP (by omega) (tensorTopCap C qP PF r (bundleTwist E) (k+n-a) β))

def projectionTerm (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (j : Fin (r+1))
    (α : chowGroup C q k) : chowGroup C q (k-b) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let qP := bundleProj E ≫ q
  let PF := (Scheme.Modules.pullback (bundleProj E)).obj F
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  let β := capPow C qP (invCap C qP (bundleTwist E)) a (k+n) (k+n-a) (by ring)
    (bundlePullback C q qP (bundleProj E) rfl n (Stacks.Chow.relativeDimension_bundleProj E n) k α)
  exact ChowLineProperPush.properPush C qP q (bundleProj E) rfl (k-b)
    (chowGroupCast C qP (by omega) (tensorTerm C qP PF r (bundleTwist E) (k+n-a) j β))

theorem tensorProjection_eq_sum (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (α : chowGroup C q k) :
    tensorProjection E n F r C q a b hab k α =
      ∑ j : Fin (r+1), projectionTerm E n F r C q a b hab k j α := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  dsimp only [tensorProjection, projectionTerm]
  rw [tensorTopCap_apply, map_sum, map_sum]

end M9Native.ChowProjectiveTensorPush
