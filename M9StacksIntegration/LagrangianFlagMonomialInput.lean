module

public import M9StacksIntegration.LagrangianFlagPowerStages
public import M9StacksIntegration.LagrangianChowPolynomials
public import M9StacksIntegration.LagrangianLinePullback

/-!
# Actual monomial evaluation on the three-stage rank-six flag pullback

The actual positive quotient-line families commute by the native line-cap
commutation theorem.  Their polynomial evaluation is therefore reordered
into the order of the original three cap powers.  Genuine flat-pullback
naturality moves the first two powers through the actual projective
stages.  All remaining comparisons are the native changes of Chow grade.
No free trivialization, numerical push value or compatibility premise is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianFlagMonomialInput

open ChowCapWords GradedLineCapSubring GradedCapVirtualSchur LagrangianChowPolynomials

section LineMonomials

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (r : T ⟶ C.S)
  [LocallyOfFiniteType r] (L : Fin 3 → InvertibleLine T)

/-- Genuine polynomial evaluation is the three native cap powers, in any equal displayed grades. -/
theorem evaluate_monomial_heq_caps (a b c : ℕ) (k m₀ m₁ m₂ : ℤ)
    (h₀ : k = m₀ + (a : ℤ)) (h₁ : m₀ = m₁ + (b : ℤ))
    (h₂ : m₁ = m₂ + (c : ℤ)) (α : chowGroup C r k) :
    evaluate C r L (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c)
        k (a + b + c) α ≍
      capPow C r (lineCap C r (L 2)) c m₁ m₂ h₂
        (capPow C r (lineCap C r (L 1)) b m₀ m₁ h₁
          (capPow C r (lineCap C r (L 0)) a k m₀ h₀ α)) := by
  let F₀ := lineFamily C r (L 0) ^ a
  let F₁ := lineFamily C r (L 1) ^ b
  let F₂ := lineFamily C r (L 2) ^ c
  have hF₀ : F₀.IsHomogeneous a := (lineFamily_homogeneous C r (L 0)).pow a
  have hF₁ : F₁.IsHomogeneous b := (lineFamily_homogeneous C r (L 1)).pow b
  have hp :
      (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℤ) ^ a *
          MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c =
        MvPolynomial.X 2 ^ c * (MvPolynomial.X 1 ^ b * MvPolynomial.X 0 ^ a) :=
    (mul_comm _ _).trans
      (congrArg (fun y => MvPolynomial.X 2 ^ c * y) (mul_comm _ _))
  have hReverse :
      evaluate C r L
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c) =
      F₂ * (F₁ * F₀) := by
    calc
      _ = evaluate C r L
          (MvPolynomial.X 2 ^ c * (MvPolynomial.X 1 ^ b * MvPolynomial.X 0 ^ a)) :=
        congrArg (evaluate C r L) hp
      _ = _ := by simp only [map_mul, map_pow, evaluate_X, F₀, F₁, F₂]
  have hPow₀ := LineFamilyCapPower.lineFamily_pow_apply_heq C r (L 0) a k m₀ h₀ α
  have hMul₁ := mul_apply_of_homogeneous_right F₁ hF₀ b k α
  have hDrop₁ :
      capTo F₁ b (by omega : (k - (a : ℤ)) - (b : ℤ) = k - ((b + a : ℕ) : ℤ))
          (F₀ k a α) ≍ F₁ (k - (a : ℤ)) b (F₀ k a α) :=
    gradedDegreeCast_heq _ _
  have hInner :
      (F₁ * F₀) k (b + a) α ≍
        capPow C r (lineCap C r (L 1)) b m₀ m₁ h₁
          (capPow C r (lineCap C r (L 0)) a k m₀ h₀ α) :=
    (heq_of_eq hMul₁).trans (hDrop₁.trans
      ((F₁.apply_heq (by omega) b hPow₀).trans
        (LineFamilyCapPower.lineFamily_pow_apply_heq C r (L 1) b m₀ m₁ h₁ _)))
  have hMul₂ := mul_apply_of_homogeneous_right F₂ (hF₁.mul hF₀) c k α
  have hDrop₂ :
      capTo F₂ c
          (by omega : (k - ((b + a : ℕ) : ℤ)) - (c : ℤ) = k - ((c + (b + a) : ℕ) : ℤ))
          ((F₁ * F₀) k (b + a) α) ≍
        F₂ (k - ((b + a : ℕ) : ℤ)) c ((F₁ * F₀) k (b + a) α) :=
    gradedDegreeCast_heq _ _
  have hIndex := LineFamilyCapWords.family_apply_index_heq C r (F₂ * (F₁ * F₀)) k
    (show a + b + c = c + (b + a) by omega) α
  exact (heq_of_eq (congrArg (fun F : GradedCapFamily (chowGroup C r) =>
      F k (a + b + c) α) hReverse)).trans
    (hIndex.trans ((heq_of_eq hMul₂).trans (hDrop₂.trans
      ((F₂.apply_heq (by omega) c hInner).trans
        (LineFamilyCapPower.lineFamily_pow_apply_heq C r (L 2) c m₁ m₂ h₂ _)))))

end LineMonomials

attribute [local instance] LagrangianFlagPowerStages.actualHasKernels
  LagrangianFlagPowerStages.actualHasKernel LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1Flat LagrangianFlagPowerStages.projection2Flat
  LagrangianFlagPowerStages.projection3Flat LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

open LagrangianFlagPowerStages

section Flag

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- First-line powers move through the genuine second flat projective pullback. -/
theorem pull2_cap_first (s : ℕ) (i m : ℤ) (h : i = m + (s : ℤ))
    (β : chowGroup C (baseMap1 E C q) i) :
    pull2 E C q m
        (capPow C (baseMap1 E C q) (lineCap C (baseMap1 E C q) (firstLine E)) s i m h β) =
      capPow C (baseMap2 E C q) (lineCap C (baseMap2 E C q) (firstLineAt2 E))
        s (i + 4) (m + 4) (by omega) (pull2 E C q i β) :=
  LagrangianLinePullback.flatPull_capPow C (baseMap1 E C q) (baseMap2 E C q)
    (projection2 E) rfl 4
    (@relativeDimension_bundleProj (space1 E) (kernel1 E) 4 (kernel1Rank E))
    (firstLine E) (firstLineAt2 E) (Iso.refl _) s i m h β

/-- First-line powers move through the genuine third flat projective pullback. -/
theorem pull3_cap_first (s : ℕ) (i m : ℤ) (h : i = m + (s : ℤ))
    (β : chowGroup C (baseMap2 E C q) i) :
    pull3 E C q m
        (capPow C (baseMap2 E C q) (lineCap C (baseMap2 E C q) (firstLineAt2 E)) s i m h β) =
      capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (firstLineAt3 E))
        s (i + 3) (m + 3) (by omega) (pull3 E C q i β) :=
  LagrangianLinePullback.flatPull_capPow C (baseMap2 E C q) (baseMap3 E C q)
    (projection3 E) rfl 3
    (@relativeDimension_bundleProj (space2 E) (kernel2 E) 3 (kernel2Rank E))
    (firstLineAt2 E) (firstLineAt3 E) (Iso.refl _) s i m h β

/-- Second-line powers move through the genuine third flat projective pullback. -/
theorem pull3_cap_second (s : ℕ) (i m : ℤ) (h : i = m + (s : ℤ))
    (β : chowGroup C (baseMap2 E C q) i) :
    pull3 E C q m
        (capPow C (baseMap2 E C q) (lineCap C (baseMap2 E C q) (secondLine E)) s i m h β) =
      capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (secondLineAt3 E))
        s (i + 3) (m + 3) (by omega) (pull3 E C q i β) :=
  LagrangianLinePullback.flatPull_capPow C (baseMap2 E C q) (baseMap3 E C q)
    (projection3 E) rfl 3
    (@relativeDimension_bundleProj (space2 E) (kernel2 E) 3 (kernel2Rank E))
    (secondLine E) (secondLineAt3 E) (Iso.refl _) s i m h β

/-- The three native powers, all applied after the original full flat pullback. -/
def finalPowerClass (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 E C q) (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3 - (c : ℤ)) :=
  capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (thirdLine E)) c
    (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3)
    (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3 - (c : ℤ)) (by omega)
    (capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (secondLineAt3 E)) b
      (((k + 5 - (a : ℤ)) + 4) + 3)
      (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3) (by omega)
      (capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (firstLineAt3 E)) a
        (k + 12) (((k + 5 - (a : ℤ)) + 4) + 3) (by omega)
        (flatPullClass E C q k α)))

/-- Genuine pullback naturality gives the original interleaved cap class. -/
theorem powerClass3_eq_finalPowerClass (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    powerClass3 E C q a b c k α = finalPowerClass E C q a b c k α := by
  unfold powerClass3 powerClass2 powerClass1 finalPowerClass flatPullClass
  rw [pull3_cap_second, pull2_cap_first, pull3_cap_first]
  rw [capPow_cast]

/-- Monomial evaluation on the actual full flat pullback is the actual three-stage power class. -/
theorem evaluate_monomial_flatPullClass (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    evaluate C (baseMap3 E C q) (positiveLines E)
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c)
        (k + 12) (a + b + c) (flatPullClass E C q k α) ≍
      powerClass3 E C q a b c k α := by
  have h :
      evaluate C (baseMap3 E C q) (positiveLines E)
          (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c)
          (k + 12) (a + b + c) (flatPullClass E C q k α) ≍
        finalPowerClass E C q a b c k α :=
    evaluate_monomial_heq_caps C (baseMap3 E C q) (positiveLines E) a b c (k + 12)
      (((k + 5 - (a : ℤ)) + 4) + 3)
      (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3)
      (((k + 5 - (a : ℤ)) + 4 - (b : ℤ)) + 3 - (c : ℤ))
      (by omega) (by omega) (by omega) (flatPullClass E C q k α)
  exact h.trans (heq_of_eq (powerClass3_eq_finalPowerClass E C q a b c k α).symm)

end Flag

end M9Native.LagrangianFlagMonomialInput
