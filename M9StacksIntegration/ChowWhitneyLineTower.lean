module

public import M9StacksIntegration.ChowLineFamilyComparison
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum

/-!
# Actual finite Whitney rows give the actual ordered line-root product

Each row is a literal short exact sequence of actual sheaf modules, with
an actual invertible quotient. Unconditional native Whitney and the
proved rank-one cap comparison yield the ordered product of one plus
the very same native line-cap operators used by the C9 trace. No
elementary-Chern/root identity is assumed.

The auxiliary prefix is an explicit finite ordered product in a monoid;
neither commutativity nor membership of an infinite inverse family in
the uncompleted line subring is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern

universe u v w

namespace M9Native.ChowWhitneyLineTower

section Product

variable {R : Type v} [Monoid R] {S : Type w} [Monoid S]

/-- The explicit ordered product of the first m entries. -/
def orderedPrefix {n : ℕ} (a : Fin n → R) : (m : ℕ) → m ≤ n → R
  | 0, _ => 1
  | m+1, hm => orderedPrefix a m (by omega) * a ⟨m, by omega⟩

theorem orderedPrefix_const {n : ℕ} (a : R) (m : ℕ) (hm : m ≤ n) :
    orderedPrefix (fun _ : Fin n => a) m hm = a^m := by
  induction m with
  | zero => simp only [orderedPrefix, pow_zero]
  | succ m ih => rw [orderedPrefix, ih (by omega), pow_succ]

/-- Genuine finite products commute with genuine monoid maps. -/
theorem map_orderedPrefix {n : ℕ} (φ : R →* S) (a : Fin n → R)
    (m : ℕ) (hm : m ≤ n) :
    φ (orderedPrefix a m hm) = orderedPrefix (fun j => φ (a j)) m hm := by
  induction m with
  | zero => exact map_one φ
  | succ m ih => rw [orderedPrefix, orderedPrefix, map_mul, ih (by omega)]

end Product

open ChowCapWords GradedLineCapSubring

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

/-- Literal actual Whitney rows give the actual Chern family as the
ordered product of the original line caps, without a Chern/root premise. -/
theorem chernFamily_eq_ordered_line_product (n r : ℕ)
    (V : Fin (n+1) → X.Modules)
    (hV : ∀ a, SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (V a) (r+a.val))
    (L : Fin n → InvertibleLine X)
    (i : ∀ a : Fin n, V a.castSucc ⟶ V a.succ)
    (p : ∀ a : Fin n, V a.succ ⟶ (L a).1)
    (w : ∀ a, i a ≫ p a = 0)
    (h : ∀ a, (ShortComplex.mk (i a) (p a) (w a)).ShortExact) :
    @chernFamily C X q _ (V (Fin.last n)) (r+n) (by
      simpa only [Fin.val_last] using hV (Fin.last n)) =
    @chernFamily C X q _ (V 0) r (by simpa using hV 0) *
      orderedPrefix (fun a => 1 + lineFamily C q (L a)) n le_rfl := by
  have hpref : ∀ (m : ℕ) (hm : m ≤ n),
      @chernFamily C X q _ (V ⟨m, by omega⟩) (r+m) (hV ⟨m, by omega⟩) =
        @chernFamily C X q _ (V 0) r (by simpa using hV 0) *
          orderedPrefix (fun a => 1 + lineFamily C q (L a)) m hm := by
    intro m
    induction m with
    | zero => intro hm; exact (mul_one _).symm
    | succ m ih =>
      intro hm
      let a : Fin n := ⟨m, by omega⟩
      have hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
          (V a.castSucc) (r+m) := hV a.castSucc
      have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (L a).1 1 :=
        @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (L a).1 (L a).2
      have hB : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
          (V a.succ) ((r+m)+1) := by
        simpa only [Fin.val_succ, a, Nat.add_assoc] using hV a.succ
      have hW := @chernFamily_eq_mul_of_shortExact C X q _
        (ShortComplex.mk (i a) (p a) (w a)) (h a) (r+m) 1 hA hL
      have hrow :
          @chernFamily C X q _ (V a.succ) ((r+m)+1) hB =
          @chernFamily C X q _ (V a.castSucc) (r+m) hA *
            (1 + lineFamily C q (L a)) :=
        hW.trans (congrArg (fun b : GradedCapFamily (chowGroup C q) =>
          @chernFamily C X q _ (V a.castSucc) (r+m) hA * b)
            (ChowLineFamilyComparison.chernFamily_eq_one_add_lineFamily C q (L a)))
      have hih : @chernFamily C X q _ (V a.castSucc) (r+m) hA =
          @chernFamily C X q _ (V 0) r (by simpa using hV 0) *
            orderedPrefix (fun a => 1 + lineFamily C q (L a)) m (by omega) :=
        ih (by omega)
      have hstep := congrArg (fun b : GradedCapFamily (chowGroup C q) =>
        b * (1 + lineFamily C q (L a))) hih
      exact hrow.trans (hstep.trans (mul_assoc _ _ _))
  exact hpref n le_rfl

/-- The actual finite line-root product is the image of the same
finite product in the genuinely generated commutative line subring. -/
theorem ordered_line_product_eq_inclusion (n : ℕ) (L : Fin n → InvertibleLine X) :
    orderedPrefix (fun a => 1 + lineFamily C q (L a)) n le_rfl =
      inclusion C q (orderedPrefix (fun a => 1 + lineRoot C q (L a)) n le_rfl) := by
  have h := map_orderedPrefix (inclusion C q).toMonoidHom
    (fun a => 1 + lineRoot C q (L a)) n le_rfl
  change inclusion C q (orderedPrefix (fun a => 1 + lineRoot C q (L a)) n le_rfl) =
    orderedPrefix (fun a => inclusion C q (1 + lineRoot C q (L a))) n le_rfl at h
  have hmap : (fun a => inclusion C q (1 + lineRoot C q (L a))) =
      fun a => 1 + lineFamily C q (L a) := by
    funext a
    rfl
  rw [hmap] at h
  exact h.symm

end M9Native.ChowWhitneyLineTower
