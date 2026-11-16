module

public import M9StacksIntegration.ChowFlagThreePullback
public import M9StacksIntegration.LagrangianFlagNormalizerFamily
public import M9StacksIntegration.LagrangianFlagPolynomialNumerator

/-!
# The original Grassmannian numerator on the actual normalized full flag

Genuine full flat pullback carries the original determinant/top-Chern
operator to its actual pulled counterpart. The actual x²y normalizer
and the proved actual polynomial identity then give its true triple
proper push. Every input class is an original native Chow class.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.LagrangianFlagNumeratorPullback

open ChowCapWords GradedLineCapSubring GradedCapVirtualSchur
open LagrangianFlagChernNumerator

attribute [local instance] ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT
  LagrangianFlagChernNumerator.sourceExteriorRank
  LagrangianFlagChernNumerator.pulledExteriorRank
  LagrangianFlagPolynomialNumerator.nativeExteriorRank
  LagrangianFlagPolynomialNumerator.nativePulledExteriorRank

/-- Ordered convolution in the normalization degrees, before any
actual geometric operator is substituted. -/
theorem degreeTwelve_product_three_nine {G : ℤ → Type v}
    [∀ k, AddCommGroup (G k)] (a b : GradedCapFamily G) (hb : b.IsHomogeneous 9)
    (α : G 12) : (a*b) 12 12 α = a 3 3 (b 12 9 α) := by
  rw [mul_apply_of_homogeneous_right _ hb 3]
  rfl

/-- The shifted convolution identity with all displayed output degrees
transported before a geometric Chow group is substituted. -/
theorem normalized_cap_identity {G H : ℤ → Type v}
    [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]
    (f : ∀ k, G k →+ H (k+3)) (a b : GradedCapFamily H) (c : GradedCapFamily G)
    (h : Stacks.Chow.Intertwines f c b) (hb : b.IsHomogeneous 9) (α : G 9) :
    capTo a (k:=0+3) 3 (by decide : ((0:ℤ)+3)-(3:ℕ)=0)
      (f 0 (capTo c 9 (by decide : (9:ℤ)-(9:ℕ)=0) α)) =
    capTo (a*b) (k:=9+3) 12 (by decide : ((9:ℤ)+3)-(12:ℕ)=0) (f 9 α) := by
  have hPull := ChowFlagThreePullback.intertwines_apply_heq h 9 9 α
  have hCast := ChowFlagThreePullback.shiftedMap_heq f
    (by decide : (0:ℤ)=9-(9:ℕ))
    (gradedDegreeCast_heq (G:=G) (by decide : (9:ℤ)-(9:ℕ)=0) (c 9 9 α))
  have hValue := a.apply_heq (by decide : (0+3:ℤ)=(9+3)-(9:ℕ)) 3
    (hCast.trans hPull)
  have hProduct := mul_apply_of_homogeneous_right a hb 3 (9+3) (f 9 α)
  have hProductRaw : (a*b) (9+3) 12 (f 9 α) ≍
      a ((9+3)-(9:ℕ)) 3 (b (9+3) 9 (f 9 α)) :=
    (heq_of_eq hProduct).trans (gradedDegreeCast_heq _ _)
  apply eq_of_heq
  exact (gradedDegreeCast_heq _ _).trans (hValue.trans
    (hProductRaw.symm.trans (gradedDegreeCast_heq _ _).symm))

/-- A polynomial identity is mapped in an arbitrary target ring; no
commutativity of the ambient cap ring is assumed. -/
theorem map_integrand {R : Type v} [Ring R]
    (φ : MvPolynomial (Fin 3) ℤ →+* R) :
    φ LagrangianFlagCoefficientFunctional.integrand =
      (φ (MvPolynomial.X 0)^2 * φ (MvPolynomial.X 1)) *
        ((φ (MvPolynomial.X 0)+φ (MvPolynomial.X 1)+φ (MvPolynomial.X 2))^6 *
          ((φ (MvPolynomial.X 0)+φ (MvPolynomial.X 1)) *
           (φ (MvPolynomial.X 0)+φ (MvPolynomial.X 2)) *
           (φ (MvPolynomial.X 1)+φ (MvPolynomial.X 2)))) := by
  have hp : LagrangianFlagCoefficientFunctional.integrand =
      (MvPolynomial.X 0^2 * MvPolynomial.X 1) *
        ((MvPolynomial.X 0+MvPolynomial.X 1+MvPolynomial.X 2)^6 *
          ((MvPolynomial.X 0+MvPolynomial.X 1)*(MvPolynomial.X 0+MvPolynomial.X 2)*
            (MvPolynomial.X 1+MvPolynomial.X 2))) := by
    unfold LagrangianFlagCoefficientFunctional.integrand
    ring
  rw [hp]
  simp only [φ.map_mul,φ.map_add,φ.map_pow]

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local notation "qF" => ChowFlagThreeNormalizer.baseMap3 D C q

/-- The original flag carrier has the finite-type structure of the same three
actual projective maps; no new finite-type hypothesis is introduced. -/
local instance nativeFlagBaseLFT : LocallyOfFiniteType
    (show FlagThreeQuotient.space D ⟶ C.S from ChowFlagThreeNormalizer.baseMap3 D C q) := by
  infer_instance

local instance actualNativeExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (Scheme.Modules.exteriorPower D 2) 3 :=
  LagrangianFlagPolynomialNumerator.nativeExteriorRank D

local instance actualNativePulledExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
        (Scheme.Modules.exteriorPower D 2)) 3 :=
  LagrangianFlagPolynomialNumerator.nativePulledExteriorRank D

/-- The original determinant-six and exterior-square top-Chern-three operator. -/
def sourceNumerator : GradedCapFamily (chowGroup C q) :=
  lineFamily C q (originalDeterminantLine D) ^ 6 *
    homComponent 3 (chernFamily C q (Scheme.Modules.exteriorPower D 2) 3)

/-- Its literal actual full-projection pullback operator. -/
def pulledNumerator : GradedCapFamily (chowGroup C qF) :=
  lineFamily C qF (pulledDeterminantLine D) ^ 6 *
    homComponent 3 (@chernFamily C (ChowFlagThreeNormalizer.space3 D) qF inferInstance
      ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
        (Scheme.Modules.exteriorPower D 2)) 3 (actualNativePulledExteriorRank D))

theorem pulledNumerator_homogeneous : (pulledNumerator D C q).IsHomogeneous 9 :=
  ((lineFamily_homogeneous C qF (pulledDeterminantLine D)).pow 6).mul
    (isHomogeneous_homComponent 3 _)

/-- Genuine native full-flat naturality, with no supplied cap compatibility. -/
theorem fullPull_sourceNumerator :
    Stacks.Chow.Intertwines (ChowFlagThreePullback.fullPull D C q)
      (sourceNumerator D C q) (pulledNumerator D C q) := by
  have hLine := ChowFlagThreePullback.fullPull_lineFamily_pow D C q
    (originalDeterminantLine D) 6
  have hLineIso : lineFamily C qF
      (ChowFlagThreePullback.pulledLine D (originalDeterminantLine D)) =
        lineFamily C qF (pulledDeterminantLine D) :=
    ChowLineFamilyComparison.lineFamily_congr C qF _ _ (Iso.refl _)
  rw [hLineIso] at hLine
  have hChern := ChowFlagThreePullback.fullPull_chernFamily D C q
    (Scheme.Modules.exteriorPower D 2) 3
  have hTop := (ChowVirtualPullback.intertwines_iff_lowering
    (ChowFlagThreePullback.fullPull D C q) _ _).2
      (((ChowVirtualPullback.intertwines_iff_lowering
        (ChowFlagThreePullback.fullPull D C q) _ _).1 hChern).homComponent 3)
  exact hLine.convolve hTop

/-- The same original flatPullClass formula in every actual displayed grade. -/
theorem fullPull_sourceNumerator_apply (k : ℤ) (α : chowGroup C q k) :
    ChowFlagThreeNormalizer.flatPullClass D C q (k-9) (sourceNumerator D C q k 9 α) ≍
      pulledNumerator D C q (k+3) 9 (ChowFlagThreeNormalizer.flatPullClass D C q k α) := by
  simpa only [ChowFlagThreePullback.fullPull_apply,Nat.cast_ofNat] using
    ChowFlagThreePullback.intertwines_apply_heq
      (fullPull_sourceNumerator D C q) k 9 α

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual normalized polynomial is the same operator product. -/
theorem evaluate_integrand :
    LagrangianChowPolynomials.evaluate C qF
      (LagrangianFlagPolynomialNumerator.originalLines D)
        LagrangianFlagCoefficientFunctional.integrand =
      LagrangianFlagNormalizerFamily.normalizingFamily D C q * pulledNumerator D C q := by
  have h1 : lineFamily C qF (ChowFlagThreeNormalizer.flagLine1 D) =
      lineFamily C qF (firstLine D) :=
    ChowLineFamilyComparison.lineFamily_congr C qF _ _ (Iso.refl _)
  have h2 : lineFamily C qF (ChowFlagThreeNormalizer.flagLine2 D) =
      lineFamily C qF (secondLine D) :=
    ChowLineFamilyComparison.lineFamily_congr C qF _ _ (Iso.refl _)
  have hNorm := congrArg₂
    (fun a b : GradedCapFamily (chowGroup C qF) => a ^ 2 * b) h1 h2
  let hCached := LagrangianFlagPolynomialNumerator.evaluate_integrand D C qF
  let hScale := congrArg (fun a : GradedCapFamily (chowGroup C qF) =>
    a * pulledNumerator D C q) hNorm.symm
  -- Retain both fully typed equality proofs; the kernel validates their composition.
  run_tac Lean.Elab.Tactic.withMainContext do
    let l ← Lean.Meta.getLocalDeclFromUserName `hCached
    let r ← Lean.Meta.getLocalDeclFromUserName `hScale
    let proof ← Lean.Meta.mkEqTrans l.toExpr r.toExpr
    Lean.Elab.Tactic.closeMainGoal `exact proof

/-- The actual original numerator cap, with its proved zero output grade. -/
def sourceNumeratorClass (α : chowGroup C q 9) : chowGroup C q 0 :=
  capTo (sourceNumerator D C q) 9 (by decide : (9:ℤ)-(9:ℕ)=0) α

/-- The actual normalized polynomial cap on the genuine full flat pullback. -/
def integrandClass (α : chowGroup C q 9) : chowGroup C qF 0 :=
  capTo (LagrangianChowPolynomials.evaluate C qF
    (LagrangianFlagPolynomialNumerator.originalLines D)
    LagrangianFlagCoefficientFunctional.integrand)
    (k:=9+3) 12 (by decide : ((9:ℤ)+3)-(12:ℕ)=0)
    (ChowFlagThreeNormalizer.flatPullClass D C q 9 α)

/-- The native normal class is the same actual normalized operator cap. -/
theorem normalClass_sourceNumerator (α : chowGroup C q 9) :
    ChowFlagThreeNormalizer.normalClass D C q 0 (sourceNumeratorClass D C q α) =
      capTo (LagrangianFlagNormalizerFamily.normalizingFamily D C q * pulledNumerator D C q)
        (k:=9+3) 12 (by decide : ((9:ℤ)+3)-(12:ℕ)=0)
        (ChowFlagThreeNormalizer.flatPullClass D C q 9 α) := by
  have hNative := LagrangianFlagNormalizerFamily.normalizingFamily_apply D C q 0
    (sourceNumeratorClass D C q α)
  have hLeft : ChowFlagThreeNormalizer.normalClass D C q 0 (sourceNumeratorClass D C q α) =
      capTo (LagrangianFlagNormalizerFamily.normalizingFamily D C q)
        (k:=0+3) 3 (by decide : ((0:ℤ)+3)-(3:ℕ)=0)
        (ChowFlagThreeNormalizer.flatPullClass D C q 0 (sourceNumeratorClass D C q α)) := by
    apply eq_of_heq
    exact (heq_of_eq hNative.symm).trans
      ((gradedDegreeCast_heq _ _).trans (gradedDegreeCast_heq _ _).symm)
  have hGeneric := normalized_cap_identity
    (ChowFlagThreePullback.fullPull D C q)
    (LagrangianFlagNormalizerFamily.normalizingFamily D C q) (pulledNumerator D C q)
    (sourceNumerator D C q) (fullPull_sourceNumerator D C q)
    (pulledNumerator_homogeneous D C q) α
  exact hLeft.trans (by
    simpa only [sourceNumeratorClass,ChowFlagThreePullback.fullPull_apply] using hGeneric)

/-- True triple proper push of the actual normalized polynomial cap
returns the original determinant/top-Chern numerator on every input. -/
theorem triplePush_integrand (α : chowGroup C q 9) :
    ChowFlagThreeNormalizer.triplePush D C q 0 (integrandClass D C q α) =
      sourceNumeratorClass D C q α := by
  have hEvaluation := congrArg (fun A : GradedCapFamily (chowGroup C qF) =>
    ChowFlagThreeNormalizer.triplePush D C q 0
      (capTo A (k:=9+3) 12 (by decide : ((9:ℤ)+3)-(12:ℕ)=0)
        (ChowFlagThreeNormalizer.flatPullClass D C q 9 α))) (evaluate_integrand D C q)
  have hNormal := congrArg (ChowFlagThreeNormalizer.triplePush D C q 0)
    (normalClass_sourceNumerator D C q α).symm
  exact hEvaluation.trans (hNormal.trans
    (ChowFlagThreeNormalizer.triplePush_normalClass D C q 0 (sourceNumeratorClass D C q α)))

end M9Native.LagrangianFlagNumeratorPullback
