module

public import M9StacksIntegration.IntegralLineSectionCartier
public import M9StacksIntegration.IteratedLineSectionCuts
public import M9StacksIntegration.SerreCommonPointIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension

/-!
# Actual Cartier cuts preserve the needed Serre and dimension data

The section's nonvanishing is used to derive the genuine Cartier predicate.
The native Cartier theorems then derive the Serre step and the dimensions of
every actual irreducible component. Ordered append compatibility identifies
the next actual recursive cut, with no alternate prefix model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
namespace M9Native.IntegralLineCutSerreDimension

theorem hasPropertySk_of_regular (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.IsRegular X) (k : ℕ) : HasPropertySk X k := by
  intro x
  have hx : IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hx
  have hCM :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (X.presheaf.stalk x)).2
  change (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x) : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) at hCM
  change min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤ _
  rw [hCM]
  exact min_le_right _ _

theorem zeroScheme_serre {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (k : ℕ) (hk : 1 ≤ k) (hS : HasPropertySk X k) :
    @HasPropertySk (Stacks.Divisors.zeroScheme X L s).subscheme
      (LocallyOfFiniteType.isLocallyNoetherian (Stacks.Divisors.zeroScheme X L s).subschemeι)
      (k - 1) :=
  isEffectiveCartierDivisor_hasPropertySk (Stacks.Divisors.zeroScheme X L s)
    (isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs) k hk hS

theorem zeroScheme_components_dimension (K : Type u) [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (n : ℕ)
    (hXdim : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hne : Nonempty (Stacks.Divisors.zeroScheme X L s).subscheme) :
    (∀ W : Set (Stacks.Divisors.zeroScheme X L s).subscheme,
      W ∈ irreducibleComponents (Stacks.Divisors.zeroScheme X L s).subscheme →
      topologicalKrullDim W = ((n - 1 : ℕ) : WithBot ℕ∞)) ∧
      topologicalKrullDim (Stacks.Divisors.zeroScheme X L s).subscheme =
        ((n - 1 : ℕ) : WithBot ℕ∞) :=
  Stacks.Chow.topologicalKrullDim_irreducibleComponents_of_isEffectiveCartierDivisor
    (Stacks.Chow.fieldChowSituation K) (fun _ _ => rfl) f n
    (Equidimensional.of_preirreducibleSpace X) hXdim
    (Stacks.Divisors.zeroScheme X L s) (isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs) hne

theorem iteratedCut_append {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ls rs : List Γ(L, ⊤)) (A : Over X) :
    IteratedLineSectionCuts.iteratedCut L (ls ++ rs) A =
      IteratedLineSectionCuts.iteratedCut L rs (IteratedLineSectionCuts.iteratedCut L ls A) := by
  induction ls generalizing A with
  | nil => rfl
  | cons a ls ih =>
    simpa only [List.cons_append, IteratedLineSectionCuts.iteratedCut] using
      ih (IteratedLineSectionCuts.cut L A a)

theorem iteratedCut_append_singleton {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ss : List Γ(L, ⊤)) (s : Γ(L, ⊤)) (A : Over X) :
    IteratedLineSectionCuts.iteratedCut L (ss ++ [s]) A =
      IteratedLineSectionCuts.cut L (IteratedLineSectionCuts.iteratedCut L ss A) s := by
  rw [iteratedCut_append]
  rfl

end M9Native.IntegralLineCutSerreDimension
