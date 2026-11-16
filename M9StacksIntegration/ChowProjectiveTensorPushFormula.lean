module

public import M9StacksIntegration.ChowProjectiveTensorPushTerms
public import M9StacksIntegration.ChowProjectiveTensorPushIndex

/-! The genuine single projective Gysin formula for a tautological
line twist, expressed as convolution with actual projective moments. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowProjectiveTensorPushFormula

open ChowProjectiveTensorPush ChowProjectiveTensorPushTerms ChowProjectiveMomentInverse

theorem family_apply_heq {G : ℤ → Type*} [∀ k, AddCommGroup (G k)]
    (A : GradedCapFamily G) {k l : ℤ} {i j : ℕ} (hk : k=l) (hi : i=j)
    {α : G k} {β : G l} (hα : HEq α β) : HEq (A k i α) (A l j β) := by
  cases hk
  cases hi
  cases hα
  rfl

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

theorem projectedCoefficient_eq_zero (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (j : Fin (r+1)) (hj : a+(j:ℕ)<n) (α : chowGroup C q k) :
    projectedCoefficient E n F r C q a b hab k j α = 0 := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  dsimp only [projectedCoefficient]
  rw [projectiveBundle_projection_eq_zero_of_lt E n C q (a+(j:ℕ)) hj k
    (k+n-a-(j:ℤ)) (by push_cast; ring) α, map_zero, map_zero]

theorem projectedCoefficient_eq_convolveTerm (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (j : Fin (r+1)) (hj : n≤a+(j:ℕ)) (α : chowGroup C q k) :
    projectedCoefficient E n F r C q a b hab k j α =
      convolveTerm (chernFamily C q F r) (ChowProjectiveMoments.momentFamily E n C q)
        k b (a+(j:ℕ)-n) α := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  generalize hm : a+(j:ℕ)-n = m
  have hmb : m ≤ b := by have hlt := j.isLt; omega
  have he : a+(j:ℕ) = n+m := by omega
  have hi : r-(j:ℕ) = b-m := by have hlt := j.isLt; omega
  have hd : k+n-a-(j:ℤ) = k-(m:ℤ) := by omega
  rw [convolveTerm_of_le _ _ k hmb α, capTo_def]
  dsimp only [projectedCoefficient]
  have hp : ∀ (s t : ℕ) (l l' : ℤ) (hs : s=t)
      (h₁ : k+n=l+s) (h₂ : k+n=l'+t),
      HEq (bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
        (Stacks.Chow.relativeDimension_bundleProj E n)
        (invCap C (bundleProj E ≫ q) (bundleTwist E)) s k l h₁ α)
        (bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
          (Stacks.Chow.relativeDimension_bundleProj E n)
          (invCap C (bundleProj E ≫ q) (bundleTwist E)) t k l' h₂ α) := by
    intro s t l l' hs h₁ h₂
    have hh : l=l' := by omega
    cases hs
    cases hh
    rfl
  have hγ : HEq (bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
      (Stacks.Chow.relativeDimension_bundleProj E n)
      (invCap C (bundleProj E ≫ q) (bundleTwist E)) (a+(j:ℕ)) k
      (k+n-a-(j:ℤ)) (by push_cast; ring) α)
      (ChowProjectiveMoments.momentFamily E n C q k m α) :=
    hp (a+(j:ℕ)) (n+m) (k+n-a-(j:ℤ)) (k-(m:ℤ)) he
      (by push_cast; ring) (by push_cast; ring)
  have hOut : (k+n-a-(j:ℤ))-((r-(j:ℕ):ℕ):ℤ)=k-b := by
    rw [hd, hi]
    omega
  apply eq_of_heq
  refine (chowGroupCast_heq C q hOut _).trans ?_
  exact (family_apply_heq (chernFamily C q F r) hd hi hγ).trans
    (gradedDegreeCast_heq (show k-(m:ℤ)-((b-m:ℕ):ℤ)=k-b by omega) _).symm

theorem convolveTerm_eq_zero_lower_tail (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (m : ℕ) (hm : m≤b) (hlo : n+m<a) (α : chowGroup C q k) :
    convolveTerm (chernFamily C q F r) (ChowProjectiveMoments.momentFamily E n C q)
      k b m α = 0 := by
  rw [convolveTerm_of_le _ _ k hm α, capTo_def]
  have hi : ¬ b-m≤r := by omega
  rw [chernFamily_apply_of_gt C q F r (k-(m:ℤ)) hi]
  simp only [AddMonoidHom.zero_apply, map_zero]

theorem projectionTerm_eq_if (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (j : Fin (r+1)) (α : chowGroup C q k) :
    projectionTerm E n F r C q a b hab k j α =
      if n≤a+(j:ℕ) then
        convolveTerm (chernFamily C q F r) (ChowProjectiveMoments.momentFamily E n C q)
          k b (a+(j:ℕ)-n) α else 0 := by
  rw [projectionTerm_eq_projectedCoefficient]
  by_cases hj : n≤a+(j:ℕ)
  · rw [if_pos hj]
    exact projectedCoefficient_eq_convolveTerm E n F r C q a b hab k j hj α
  · rw [if_neg hj]
    exact projectedCoefficient_eq_zero E n F r C q a b hab k j (by omega) α

/-- The actual top-Chern cap, extra tautological cap, flat pullback and
proper pushforward equal the indicated genuine Chern/moment convolution.
No inverse-Chern formula or projection identity is assumed. -/
theorem tensorProjection_eq_chern_mul_moment (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (α : chowGroup C q k) :
    tensorProjection E n F r C q a b hab k α =
      (chernFamily C q F r * ChowProjectiveMoments.momentFamily E n C q) k b α := by
  let f : ℕ → chowGroup C q (k-(b:ℤ)) := fun m =>
    convolveTerm (chernFamily C q F r) (ChowProjectiveMoments.momentFamily E n C q) k b m α
  have hz : ∀ m, m≤b → n+m<a → f m=0 :=
    fun m hm hlo => convolveTerm_eq_zero_lower_tail E n F r C q a b hab k m hm hlo α
  calc
    _ = ∑ j : Fin (r+1), if n≤a+(j:ℕ) then f (a+(j:ℕ)-n) else 0 := by
      rw [tensorProjection_eq_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact projectionTerm_eq_if E n F r C q a b hab k j α
    _ = ∑ m ∈ Finset.range (b+1), f m :=
      ChowProjectiveTensorPushIndex.fin_reindex_range r a n b hab f hz
    _ = _ := by rw [gradedCap_mul_apply]

end M9Native.ChowProjectiveTensorPushFormula
