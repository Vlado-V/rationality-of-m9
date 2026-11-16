module

public import M9StacksIntegration.GradedLineCapSubring
public import M9StacksIntegration.CurvePowerRootChern
public import M9StacksIntegration.ChowWhitneyLineTower
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.List.OfFn

/-!
# Finite actual inverse-Chern coefficients and Segre polynomials

This is ordered operator algebra. The geometric Whitney/jet identities
for the actual bundles must be supplied separately; they are not proved
or assumed globally by this module. No infinite inverse is asserted to
belong to the uncompleted line-generated subring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v
namespace M9Native.GradedCapSegreComparison
open AlgebraicGeometry CategoryTheory Stacks.Chow Finset
open M9Native.GradedCapVirtualSchur M9Native.GradedLineCapSubring
open M9Native.CurvePowerRootChern

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- Two homogeneous coefficients multiply as the actual ordered two
cap maps, with only the native degree transport. -/
theorem homComponent_mul_apply (a b : GradedCapFamily G) (i j n : ℕ)
    (h : i + j = n) (k : ℤ) (α : G k) :
    (homComponent i a * homComponent j b) k n α =
      capTo a i (by omega) (b k j α) := by
  subst n
  rw [mul_apply_of_homogeneous_right _ (isHomogeneous_homComponent j b),
    homComponent_apply_self, capTo_def, homComponent_apply_self]
  rfl

/-- A positive degree-one cap cannot contribute to the constant
coefficient of an ordered product. -/
theorem homComponent_zero_mul_of_degree_one
    (a b : GradedCapFamily G) (ha : a.IsHomogeneous 1) :
    homComponent 0 (a * b) = 0 := by
  have hcoeff (k : ℤ) : (a * b) k 0 = (0 : GradedCapFamily G) k 0 := by
    apply AddMonoidHom.ext
    intro α
    rw [gradedCap_mul_apply, Finset.sum_range_one,
      convolveTerm_of_le _ _ _ (Nat.zero_le 0)]
    exact capTo_of_eq_zero a _ (ha _ _ (by decide)) _
  exact (homComponent_congr hcoeff).trans (homComponent 0).map_zero

/-- The native recursive inverse has an actual homogeneous-family
recurrence; no commutativity is used. -/
theorem homComponent_gradedRightInv (a : GradedCapFamily G) (n : ℕ) :
    homComponent n (gradedRightInv a) = homComponent n 1 -
      ∑ j : Fin n, homComponent (n - j) a * homComponent j (gradedRightInv a) := by
  let b := homComponent n (1 : GradedCapFamily G) -
    ∑ j : Fin n, homComponent (n - j) a * homComponent j (gradedRightInv a)
  have hb : b.IsHomogeneous n := by
    have hs : (∑ j : Fin n,
        homComponent (n - j) a * homComponent j (gradedRightInv a)).IsHomogeneous n := by
      apply GradedCapFamily.IsHomogeneous.sum
      intro j _
      simpa only [Nat.sub_add_cancel j.isLt.le] using
        (isHomogeneous_homComponent (n - j) a).mul
          (isHomogeneous_homComponent j (gradedRightInv a))
    simpa only [b, sub_eq_add_neg, neg_one_zsmul] using
      (isHomogeneous_homComponent n (1 : GradedCapFamily G)).add (hs.zsmul (-1))
  have hcoeff (k : ℤ) : gradedRightInv a k n = b k n := by
    have hs : (∑ j : Fin n,
        homComponent (n - j) a * homComponent j (gradedRightInv a)) k n =
        ∑ j : Fin n, (gradedDegreeCast G
          (show k - ((j : ℕ) : ℤ) - ((n - (j : ℕ) : ℕ) : ℤ) = k - (n : ℤ) by
            have := j.isLt; omega)).toAddMonoidHom.comp
          ((a (k - ((j : ℕ) : ℤ)) (n - j)).comp (gradedRightInv a k j)) := by
      apply AddMonoidHom.ext
      intro α
      rw [gradedCap_sum_apply, AddMonoidHom.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [homComponent_mul_apply a (gradedRightInv a) (n - j) j n
        (by have := j.isLt; omega)]
      rfl
    rw [gradedRightInv_apply, ← hs]
    simp only [b, Pi.sub_apply, homComponent_apply_self]
  exact (homComponent_congr hcoeff).trans hb.homComponent_self

end Generic

section RootPolynomials
variable {R : Type*} [CommRing R]

/-- The existing finite Segre polynomials satisfy the same ordered
finite-index recurrence as the actual inverse cap coefficients. -/
theorem segreCoefficient_fin_recurrence (r : List R) (n : ℕ) :
    segreCoefficient r (n + 1) =
      -∑ j : Fin (n + 1), elementary r (n + 1 - j) * segreCoefficient r j := by
  rw [segreCoefficient_succ, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change -(∑ j ∈ range (n + 1 + 1),
    if j < n + 1 then elementary r (n + 1 - j) * segreCoefficient r j else 0) = _
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false, ite_false, add_zero]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => if j < n + 1 then elementary r (n + 1 - j) * segreCoefficient r j else 0)
    (n + 1)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact ite_eq_left j.isLt

end RootPolynomials

section OrderedProducts
variable {R : Type*} [Monoid R]

/-- The explicit left-ordered Whitney prefix is the literal product
of its finite list, preserving order without commutativity. -/
theorem orderedPrefix_eq_ofFn_prod {n : ℕ} (a : Fin n → R)
    (m : ℕ) (hm : m ≤ n) :
    ChowWhitneyLineTower.orderedPrefix a m hm =
      (List.ofFn (fun j : Fin m => a ⟨j.val, by omega⟩)).prod := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [ChowWhitneyLineTower.orderedPrefix, ih (by omega),
        List.ofFn_succ', List.prod_concat]
      simp only [Fin.val_castSucc, Fin.val_last]

end OrderedProducts

section ActualChow
variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q]

/-- The actual finite product of one plus each native line cap has
the genuine elementary coefficients in the actual line-generated
ring. This uses the proved degree-one property, not a Chern/root
coefficient premise. -/
theorem homComponent_line_list_product
    (L : List (ChowCapWords.InvertibleLine X)) (n : ℕ) :
    homComponent n ((L.map (fun M => 1 + lineFamily C q M)).prod) =
      inclusion C q (elementary (L.map (lineRoot C q)) n) := by
  induction L generalizing n with
  | nil =>
      cases n with
      | zero =>
          simpa only [List.map_nil, List.prod_nil, elementary,
            (inclusion C q).map_one] using
            (GradedCapFamily.IsHomogeneous.one (G := chowGroup C q)).homComponent_self
      | succ n =>
          simpa only [List.map_nil, List.prod_nil, elementary,
            (inclusion C q).map_zero] using
            (GradedCapFamily.IsHomogeneous.one (G := chowGroup C q)).homComponent_of_ne
              (Nat.succ_ne_zero n)
  | cons M L ih =>
      cases n with
      | zero =>
          rw [List.map_cons, List.prod_cons, add_mul, one_mul,
            (homComponent 0).map_add,
            homComponent_zero_mul_of_degree_one _ _ (lineFamily_homogeneous C q M),
            add_zero, ih]
          simp only [elementary_zero]
      | succ n =>
          rw [List.map_cons, List.prod_cons, add_mul, one_mul,
            (homComponent (n + 1)).map_add]
          have hshift := homComponent_mul_of_isHomogeneous_left
            (lineFamily_homogeneous C q M)
            ((L.map (fun M => 1 + lineFamily C q M)).prod) n
          rw [show homComponent (n + 1)
              (lineFamily C q M * (L.map (fun M => 1 + lineFamily C q M)).prod) =
              lineFamily C q M * homComponent n
                ((L.map (fun M => 1 + lineFamily C q M)).prod) by
            simpa only [Nat.add_comm] using hshift,
            ih (n + 1), ih n]
          rw [List.map_cons, elementary, (inclusion C q).map_add,
            (inclusion C q).map_mul]
          rfl

/-- The same coefficient equality for the literal left-ordered
finite Whitney product used by the actual filtration theorem. -/
theorem homComponent_ordered_line_product (n : ℕ)
    (L : Fin n → ChowCapWords.InvertibleLine X) (i : ℕ) :
    homComponent i (ChowWhitneyLineTower.orderedPrefix
      (fun j => 1 + lineFamily C q (L j)) n le_rfl) =
    inclusion C q (elementary (List.ofFn (fun j => lineRoot C q (L j))) i) := by
  rw [orderedPrefix_eq_ofFn_prod]
  have harg : (fun j : Fin n => 1 + lineFamily C q (L ⟨j.val, by omega⟩)) =
      (fun j => 1 + lineFamily C q (L j)) := by
    funext j
    have he : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
    rw [he]
  rw [harg]
  simpa only [List.map_ofFn, Function.comp_def] using
    homComponent_line_list_product C q (List.ofFn L) i

/-- Genuine actual Chern coefficient identities through N determine
the actual inverse coefficients through N as the finite Segre
polynomials in the actual line-generated ring. The coefficient
identities are explicit geometric inputs, not proved by this algebra. -/
theorem inverseComponent_eq_segre_of_coefficients (E : X.Modules) (rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    (r : List (lineSubring C q)) (N : ℕ)
    (hChern : ∀ i ≤ N, homComponent i (GenuineChern.chernFamily C q E rE) =
      inclusion C q (elementary r i)) (n : ℕ) (hn : n ≤ N) :
    homComponent n (inverseFamily C q E rE) = inclusion C q (segreCoefficient r n) := by
  have hrec (m : ℕ) : homComponent m (inverseFamily C q E rE) = homComponent m 1 -
      ∑ j : Fin m, homComponent (m - j) (GenuineChern.chernFamily C q E rE) *
        homComponent j (inverseFamily C q E rE) := by
    simpa only [inverseFamily_eq_gradedRightInv] using
      homComponent_gradedRightInv (GenuineChern.chernFamily C q E rE) m
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [segreCoefficient_zero, map_one]
          exact (homComponent_congr (inverseFamily_apply_zero C q E rE)).trans
            GradedCapFamily.IsHomogeneous.one.homComponent_self
      | succ n =>
          rw [hrec, GradedCapFamily.IsHomogeneous.one.homComponent_of_ne
            (Nat.succ_ne_zero n), zero_sub, segreCoefficient_fin_recurrence,
            (inclusion C q).map_neg]
          change -(∑ j : Fin (n + 1), _) =
            -((inclusion C q).toAddMonoidHom (∑ j : Fin (n + 1), _))
          rw [map_sum (inclusion C q).toAddMonoidHom]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [hChern _ (by have := j.isLt; omega),
            ih j (by have := j.isLt; omega) (by have := j.isLt; omega)]
          change inclusion C q _ * inclusion C q _ = inclusion C q (_ * _)
          exact ((inclusion C q).map_mul _ _).symm

/-- A separately proved actual virtual/trivial-row removal identity
transfers the coefficient comparison to the original actual virtual
family. Both geometric identities remain visible hypotheses. -/
theorem virtualComponent_eq_segre_of_coefficients
    (F E T : X.Modules) (rF rE rT : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    [SheafOfModules.IsFiniteLocallyFreeOfRank T rT]
    (r : List (lineSubring C q)) (N : ℕ)
    (hChern : ∀ i ≤ N, homComponent i (GenuineChern.chernFamily C q T rT) =
      inclusion C q (elementary r i))
    (hremove : virtualFamily C q F E rF rE = inverseFamily C q T rT)
    (n : ℕ) (hn : n ≤ N) :
    virtualComponent C q F E rF rE n = inclusion C q (segreCoefficient r n) := by
  dsimp only [virtualComponent]
  rw [hremove]
  exact inverseComponent_eq_segre_of_coefficients C q T rT r N hChern n hn

/-- Matching the five actual homogeneous cap coefficients identifies
the literal ordered Schur operator with the actual image of the finite
commutative Segre determinant. Commutativity is used only inside the
proved line-generated subring. -/
theorem schur333_eq_image_segreDet_of_components
    (c : GradedCapFamily (chowGroup C q)) (r : List (lineSubring C q))
    (hcoeff : ∀ i, 1 ≤ i → i ≤ 5 →
      homComponent i c = inclusion C q (segreCoefficient r i)) :
    schur333 c = inclusion C q (segreSchurMatrix r).det := by
  have hd : (segreSchurMatrix r).det =
      segreCoefficient r 3 * segreCoefficient r 3 * segreCoefficient r 3 -
      segreCoefficient r 3 * segreCoefficient r 4 * segreCoefficient r 2 -
      segreCoefficient r 4 * segreCoefficient r 2 * segreCoefficient r 3 +
      segreCoefficient r 4 * segreCoefficient r 4 * segreCoefficient r 1 +
      segreCoefficient r 5 * segreCoefficient r 2 * segreCoefficient r 2 -
      segreCoefficient r 5 * segreCoefficient r 3 * segreCoefficient r 1 := by
    simp [segreSchurMatrix, Matrix.det_fin_three]
  rw [hd]
  simp only [schur333, hcoeff 1 (by decide) (by decide),
    hcoeff 2 (by decide) (by decide), hcoeff 3 (by decide) (by decide),
    hcoeff 4 (by decide) (by decide), hcoeff 5 (by decide) (by decide),
    (inclusion C q).map_sub, (inclusion C q).map_add, (inclusion C q).map_mul]

/-- The actual virtual Schur operator matches the finite Segre
determinant when the genuine Chern identities through five and the
actual row-removal identity have been established. No geometric
Whitney/jet or Gysin statement is asserted by this conditional algebra. -/
theorem virtualSchur_eq_image_segreDet_of_coefficients
    (F E T : X.Modules) (rF rE rT : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    [SheafOfModules.IsFiniteLocallyFreeOfRank T rT]
    (r : List (lineSubring C q))
    (hChern : ∀ i ≤ 5, homComponent i (GenuineChern.chernFamily C q T rT) =
      inclusion C q (elementary r i))
    (hremove : virtualFamily C q F E rF rE = inverseFamily C q T rT) :
    schur333 (virtualFamily C q F E rF rE) = inclusion C q (segreSchurMatrix r).det := by
  apply schur333_eq_image_segreDet_of_components C q _ r
  intro i _ hi
  exact virtualComponent_eq_segre_of_coefficients C q F E T rF rE rT r 5 hChern hremove i hi

/-- An actual finite Whitney-product identity yields the actual inverse
coefficient as a finite Segre polynomial. No coefficient identity is an
additional premise, and no whole inverse membership is asserted. -/
theorem inverseComponent_eq_segre_of_ordered_line_product
    (E : X.Modules) (rE n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    (L : Fin n → ChowCapWords.InvertibleLine X)
    (hProduct : GenuineChern.chernFamily C q E rE =
      ChowWhitneyLineTower.orderedPrefix (fun j => 1 + lineFamily C q (L j)) n le_rfl)
    (i : ℕ) :
    homComponent i (inverseFamily C q E rE) =
      inclusion C q (segreCoefficient (List.ofFn (fun j => lineRoot C q (L j))) i) := by
  apply inverseComponent_eq_segre_of_coefficients C q E rE _ i _ i le_rfl
  intro j _
  rw [hProduct]
  exact homComponent_ordered_line_product C q n L j

/-- Actual finite Whitney/row-removal identities identify the original
ordered virtual Schur cap operator with the finite commutative Segre
determinant in the genuine line-generated subring. The actual geometric
row identities are still explicit producer obligations. -/
theorem virtualSchur_eq_image_segreDet_of_ordered_line_product
    (F E T : X.Modules) (rF rE rT n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    [SheafOfModules.IsFiniteLocallyFreeOfRank T rT]
    (L : Fin n → ChowCapWords.InvertibleLine X)
    (hProduct : GenuineChern.chernFamily C q T rT =
      ChowWhitneyLineTower.orderedPrefix (fun j => 1 + lineFamily C q (L j)) n le_rfl)
    (hremove : virtualFamily C q F E rF rE = inverseFamily C q T rT) :
    schur333 (virtualFamily C q F E rF rE) =
      inclusion C q (segreSchurMatrix (List.ofFn (fun j => lineRoot C q (L j)))).det := by
  apply virtualSchur_eq_image_segreDet_of_coefficients C q F E T rF rE rT _ _ hremove
  intro j _
  rw [hProduct]
  exact homComponent_ordered_line_product C q n L j

end ActualChow
end M9Native.GradedCapSegreComparison
