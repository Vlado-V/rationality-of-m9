module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses

/-!
# Actual proper pushforward of the shifted projective Chern relation

The shift is the actual extra power of the original tautological cap
followed by literal proper Chow pushforward. Its term comparison is an
equality of actual Chow maps, not a Chern/Segre or trace identification
assumed as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.ChowProjectiveShiftedRelation

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (qX : X ⟶ C.S)
  [LocallyOfFiniteType qX] (qP : P ⟶ C.S) [LocallyOfFiniteType qP]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] [IsProper π]
  (hbase : π ≫ qX = qP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (ξ : ChernCapOperator C qP)

/-- The actual extra-cap then actual proper-push map in positive degree. -/
def shiftedPush (k : ℤ) (m : ℕ) (hm : 0 < m) :
    chowGroup C qP (k+(n:ℤ)-((n+1:ℕ):ℤ)) →+ chowGroup C qX (k-(m:ℤ)) :=
  (properChowPushforward C qP qX π hbase (k-(m:ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qP qX π hbase (k-(m:ℤ)))).comp
    (capPow C qP ξ (m-1) (k+(n:ℤ)-((n+1:ℕ):ℤ)) (k-(m:ℤ))
      (by have hm' : 1 ≤ m := hm; push_cast [Nat.cast_sub hm']; ring))

/-- Extra actual cap powers turn the original Chern-relation term
into the genuine projective moment of that original coefficient class. -/
theorem shiftedPush_chernTerm (k : ℤ) (m : ℕ) (hm : 0 < m)
    (i : ℕ) (hi : i ≤ n+1) (β : chowGroup C qX (k-((n+1-i:ℕ):ℤ))) :
    shiftedPush C qX qP π hbase n ξ k m hm
      (projectiveBundleChernTerm C qX qP π hbase (n+1) hπ
        (fun k => flatPullbackFactorsThroughRationalEquivalence_general C qP qX π hbase n hπ k)
        ξ k i hi β) =
      bundleProjection C qX qP π hbase n hπ ξ (i+(m-1))
        (k-((n+1-i:ℕ):ℤ)) (k-(m:ℤ))
        (by have hm' : 1 ≤ m := hm; push_cast [Nat.cast_sub hi, Nat.cast_sub hm']; ring) β := by
  simp only [shiftedPush, projectiveBundleChernTerm, bundleProjection,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← capPow_eq_iteratedChernCapOnChow, capPow_cast]
  apply congrArg (properChowPushforward C qP qX π hbase (k-(m:ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper
      C qP qX π hbase (k-(m:ℤ))))
  exact capPow_capPow C qP ξ i (m-1)
    (k-((n+1-i:ℕ):ℤ)+(n:ℤ)) (k+(n:ℤ)-((n+1:ℕ):ℤ)) (k-(m:ℤ))
    (by push_cast [Nat.cast_sub hi]; ring)
    (by have hm' : 1 ≤ m := hm; push_cast [Nat.cast_sub hm']; ring)
    (bundlePullback C qX qP π hbase n hπ (k-((n+1-i:ℕ):ℤ)) β)

end M9Native.ChowProjectiveShiftedRelation
