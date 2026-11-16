module

public import M9StacksIntegration.ChowProjectiveMoments
public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapSignScale

/-!
# Actual projective Chow moments and inverse Chern coefficients

All moment maps below are the literal proper-push/cap/flat-pull maps of
ChowProjectiveMoments. Their inverse-Chern recurrence is derived from the
actual projective characteristic relation and actual lower-power vanishing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Finset Stacks.Chow
open Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowProjectiveMomentInverse

/-- The two native transports are the same actual additive degree transport. -/
theorem chowCast_eq_graded (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] {a b : ℤ} (h : a = b)
    (α : chowGroup C q a) :
    chowGroupCast C q h α = gradedDegreeCast (chowGroup C q) h α := by
  cases h
  rfl

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The actual total-family coefficient up to the true rank is the
actual coefficient occurring in the native projective relation. -/
theorem chernFamily_apply_le (k : ℤ) (j : ℕ) (hj : j ≤ n+1)
    (α : chowGroup C q k) :
    chernFamily C q E (n+1) k j α =
      bundleChernCapFamily E n C q k α ⟨j, by omega⟩ := by
  change (chernCapFamilyOnChow C (chernCap C) q E (n+1) k j) α = _
  rw [chernCapFamilyOnChow_of_le C (chernCap C) q E (n+1) k hj,
    chernCap_succ, bundleChernCap_apply]

/-- The actual pushed jth Chern term, before truncation at the fiber dimension. -/
def projectedTerm (k : ℤ) (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ n+1)
    (α : chowGroup C q k) : chowGroup C q (k-(m:ℤ)) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  exact bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (Stacks.Chow.relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ q) (bundleTwist E))
    ((n+1-j)+(m-1)) (k-(j:ℤ)) (k-(m:ℤ))
    (by push_cast [Nat.cast_sub hj, Nat.cast_sub (by omega : 1 ≤ m)]; ring)
    (bundleChernCapFamily E n C q k α ⟨j, by omega⟩)

/-- Above m the literal power is below the actual projective fiber dimension,
so the genuine proper pushforward vanishes. -/
theorem projectedTerm_eq_zero_of_gt (k : ℤ) (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j ≤ n+1) (hjm : m < j) (α : chowGroup C q k) :
    projectedTerm E n C q k m hm j hj α = 0 := by
  exact projectiveBundle_projection_eq_zero_of_lt E n C q
    ((n+1-j)+(m-1)) (by omega) (k-(j:ℤ)) (k-(m:ℤ)) _ _

/-- Every remaining actual projective term is exactly the corresponding
actual moment applied after the actual Chern coefficient. -/
theorem projectedTerm_eq_moment (k : ℤ) (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j ≤ n+1) (hjm : j ≤ m) (α : chowGroup C q k) :
    projectedTerm E n C q k m hm j hj α =
      capTo (ChowProjectiveMoments.momentFamily E n C q) (m-j)
        (by omega) (chernFamily C q E (n+1) k j α) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  have he : (n+1-j)+(m-1) = n+(m-j) := by omega
  have hdeg : (k-(j:ℤ))-((m-j:ℕ):ℤ) = k-(m:ℤ) := by omega
  have hc := bundleProjection_congr_target C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (Stacks.Chow.relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ q) (bundleTwist E))
    (n+(m-j)) (k-(j:ℤ)) (by push_cast; ring) hdeg
    (bundleChernCapFamily E n C q k α ⟨j, by omega⟩)
  rw [chowCast_eq_graded] at hc
  simpa only [projectedTerm, he, capTo, ChowProjectiveMoments.momentFamily,
    ChowProjectiveMoments.moment, chernFamily_apply_le E n C q k j hj] using hc

/-- Literal convolution summands agree with signed actual projective terms.
The out-of-range case uses genuine projective pushforward vanishing. -/
theorem convolveTerm_eq_signed_projectedTerm (k : ℤ) (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j ≤ n+1) (α : chowGroup C q k) :
    convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
      (capFamilySignScale (chernFamily C q E (n+1))) k m j α =
      (-1:ℤ)^j • projectedTerm E n C q k m hm j hj α := by
  by_cases hjm : j ≤ m
  · rw [convolveTerm_of_le _ _ _ hjm, capFamilySignScale_apply,
      projectedTerm_eq_moment E n C q k m hm j hj hjm, capTo_def, capTo_def,
      map_zsmul, map_zsmul]
  · rw [convolveTerm_of_gt _ _ _ hjm,
      projectedTerm_eq_zero_of_gt E n C q k m hm j hj (by omega), smul_zero]


/-- A Chern index above the actual rank contributes zero to the literal
native convolution. This uses the true zero extension of Chern caps. -/
theorem convolveTerm_eq_zero_of_gt_rank (k : ℤ) (m j : ℕ)
    (hj : n+1 < j) (α : chowGroup C q k) :
    convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
      (capFamilySignScale (chernFamily C q E (n+1))) k m j α = 0 := by
  by_cases hjm : j ≤ m
  · rw [convolveTerm_of_le _ _ _ hjm, capFamilySignScale_apply]
    have hc : chernFamily C q E (n+1) k j = 0 :=
      chernCapFamilyOnChow_of_gt C (chernCap C) q E (n+1) k (by omega)
    rw [hc]
    simp only [AddMonoidHom.zero_apply, smul_zero, capTo_zero]
  · exact convolveTerm_of_gt _ _ _ hjm α

/-- Reversing the genuine characteristic relation and multiplying by
its sign unit gives the finite convolution through the actual rank.
No integer other than a sign is cancelled on a possibly torsion Chow group. -/
theorem rank_convolution_eq_zero (k : ℤ) (m : ℕ) (hm : 0 < m)
    (α : chowGroup C q k) :
    ∑ j : Fin (n+2), convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
      (capFamilySignScale (chernFamily C q E (n+1))) k m j α = 0 := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  have hp := ChowProjectiveMoments.projected_characteristic_relation E n C q k m hm α
  have hf : (∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
      projectedTerm E n C q k m hm (n+1-(i:ℕ)) (by omega) α) = 0 := by
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : (i:ℕ) ≤ n+1 := by omega
        simp only [projectedTerm, Nat.sub_sub_self hi]
      _ = 0 := hp
  have hscaled := congrArg (fun x : chowGroup C q (k-(m:ℤ)) =>
    (-1:ℤ)^(n+1) • x) hf
  rw [Finset.smul_sum, smul_zero] at hscaled
  have hterm : ∀ i : Fin (n+2),
      (-1:ℤ)^(n+1) • ((-1:ℤ)^(i:ℕ) •
        projectedTerm E n C q k m hm (n+1-(i:ℕ)) (by omega) α) =
      convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
        (capFamilySignScale (chernFamily C q E (n+1))) k m (i.rev:ℕ) α := by
    intro i
    have hi : (i:ℕ) ≤ n+1 := by omega
    have hrev : (i.rev:ℕ) = n+1-(i:ℕ) := by rw [Fin.val_rev]; omega
    have hsign : (-1:ℤ)^(n+1) * (-1:ℤ)^(i:ℕ) = (-1:ℤ)^(i.rev:ℕ) := by
      have hexp : n+1+(i:ℕ) = 2*(i:ℕ)+(i.rev:ℕ) := by omega
      rw [← pow_add, hexp, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [convolveTerm_eq_signed_projectedTerm E n C q k m hm (i.rev:ℕ) (by omega),
      smul_smul, hsign]
    simp only [hrev]
  have hrevsum : (∑ i : Fin (n+2),
      convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
        (capFamilySignScale (chernFamily C q E (n+1))) k m (i.rev:ℕ) α) = 0 := by
    simpa only [hterm] using hscaled
  exact (Equiv.sum_comp Fin.revPerm _).symm.trans hrevsum

/-- Above the actual rank or above the convolution degree, all extra
summands are zero; thus the genuinely projected relation is the full product. -/
theorem positive_product_eq_zero (k : ℤ) (m : ℕ) (hm : 0 < m)
    (α : chowGroup C q k) :
    (ChowProjectiveMoments.momentFamily E n C q *
      capFamilySignScale (chernFamily C q E (n+1))) k m α = 0 := by
  let f : ℕ → chowGroup C q (k-(m:ℤ)) := fun j =>
    convolveTerm (ChowProjectiveMoments.momentFamily E n C q)
      (capFamilySignScale (chernFamily C q E (n+1))) k m j α
  have hrank : ∑ j ∈ Finset.range (n+2), f j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range f (n+2)]
    exact rank_convolution_eq_zero E n C q k m hm α
  have hsum : (∑ j ∈ Finset.range (m+1), f j) =
      ∑ j ∈ Finset.range (n+2), f j := by
    by_cases hmr : m ≤ n+1
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      exact convolveTerm_of_gt _ _ _ (by simp only [Finset.mem_range] at hj; omega) α
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      exact convolveTerm_eq_zero_of_gt_rank E n C q k m j (by
        simp only [Finset.mem_range] at hj; omega) α
  rw [gradedCap_mul_apply]
  exact hsum.trans hrank

/-- Genuine projective pushforward moments form the inverse of the
signed actual total Chern family. -/
theorem momentFamily_mul_signed_chern :
    ChowProjectiveMoments.momentFamily E n C q *
      capFamilySignScale (chernFamily C q E (n+1)) = 1 := by
  funext k m
  apply AddMonoidHom.ext
  intro α
  rcases m with _ | m
  · rw [gradedCap_mul_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      convolveTerm_of_le _ _ _ (Nat.zero_le 0), capFamilySignScale_apply,
      pow_zero, one_smul, Nat.sub_self, Nat.cast_zero, sub_zero, chernFamily_apply_zero,
      capTo_def, ChowProjectiveMoments.momentFamily_apply_zero,
      gradedCap_one_apply_zero, gradedDegreeCast_gradedDegreeCast]
  · rw [positive_product_eq_zero E n C q k (m+1) (by omega) α,
      gradedCap_one_of_ne (by omega : m+1 ≠ 0)]
    rfl

/-- Actual proper push/cap/flat-pull moments equal the signed genuine
inverse Chern family, with no supplied trace or pushforward comparison. -/
theorem momentFamily_eq_signed_inverse :
    ChowProjectiveMoments.momentFamily E n C q =
      capFamilySignScale (GradedCapVirtualSchur.inverseFamily C q E (n+1)) := by
  have hinv : chernFamily C q E (n+1) *
      GradedCapVirtualSchur.inverseFamily C q E (n+1) = 1 := by
    simp only [GradedCapVirtualSchur.inverseFamily, IsUnit.mul_val_inv]
  have hsigned := congrArg capFamilySignScale hinv
  rw [capFamilySignScale_mul, capFamilySignScale_one] at hsigned
  calc
    ChowProjectiveMoments.momentFamily E n C q =
        ChowProjectiveMoments.momentFamily E n C q *
          (capFamilySignScale (chernFamily C q E (n+1)) *
            capFamilySignScale (GradedCapVirtualSchur.inverseFamily C q E (n+1))) := by
      rw [hsigned, mul_one]
    _ = _ := by rw [← mul_assoc, momentFamily_mul_signed_chern, one_mul]

end M9Native.ChowProjectiveMomentInverse
