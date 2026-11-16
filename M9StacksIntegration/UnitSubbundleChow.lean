module

public import M9StacksIntegration.BaseFieldSectionCokernel
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible

/-!
# Integral Chow top-Chern vanishing from an actual nowhere-zero section

The native Whitney theorem for the actual unit subbundle shows that the
top Chern cap is zero on every actual integral Chow class. The actual
cokernel and its rank are derived from nonzero field fibres, or from
nonvanishing at base-field points through the checked closed-point
argument. No dimension bound, expected codimension, Chern equality,
de Rham realization, or pushforward formula is an input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.UnitSubbundleChow

open Stacks.Chow Stacks.Chow.GenuineChern

theorem topCap_eq_zero_of_cokernel_rank
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (H : X.Modules) (r : ℕ) (s : SectionKZero.unitModule X ⟶ H) [Mono s]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H (r+1)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) r]
    (k : ℤ) (α : chowGroup C q k) :
    chernCap C (r+1) q H k (Fin.last (r+1)) α = 0 := by
  let S : ShortComplex X.Modules := ShortComplex.mk s (cokernel.π s) (cokernel.condition s)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel s }
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ (r+1) := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H (r+1)
    infer_instance
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ r := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) r
    infer_instance
  exact (chernCap_eq_of_shortExact_of_iso_unit C q S hS (Iso.refl _) r).1 k α

theorem topCap_eq_zero_of_nonzeroFieldFibers
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (H : X.Modules) (r : ℕ) (s : SectionKZero.unitModule X ⟶ H)
    [hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H (r+1)]
    (hs : SectionCokernelLocallyFree.NonzeroFieldFibers s)
    (k : ℤ) (α : chowGroup C q k) :
    chernCap C (r+1) q H k (Fin.last (r+1)) α = 0 := by
  have : Mono s := SectionCokernelLocallyFree.mono_of_nonzeroFieldFibers s (r+1) hH hs
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) r := by
    simpa only [Nat.add_sub_cancel] using
      SectionCokernelLocallyFree.cokernel_rank s (r+1) hH hs
  exact topCap_eq_zero_of_cokernel_rank C q H r s k α

theorem topCap_eq_zero_of_base_field_nonvanishing
    {K : Type u} [Field K] [IsAlgClosed K] (C : ChowSituation.{u})
    {X : Scheme.{u}} (qK : X ⟶ Spec (.of K)) [LocallyOfFiniteType qK]
    (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (H : X.Modules) (r : ℕ) (s : SectionKZero.unitModule X ⟶ H)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H (r+1)]
    (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ qK = 𝟙 _ →
      pullbackGlobalSections p H (UnitSectionPullback.unitSection s) ≠ 0)
    (k : ℤ) (α : chowGroup C q k) :
    chernCap C (r+1) q H k (Fin.last (r+1)) α = 0 :=
  topCap_eq_zero_of_nonzeroFieldFibers C q H r s
    (BaseFieldSectionCokernel.nonzeroFieldFibers qK H (r+1) s hs) k α

end M9Native.UnitSubbundleChow
