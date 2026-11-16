module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSectionsAffineOpen
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import Mathlib.Tactic

/-!
# Actual relative differential rank with only its geometric providers

This is a thin replay of the pinned native smooth-differential argument,
using its actual Kähler-section comparison and actual local bases.
The unused different/Riemann-Hurwitz development is not imported.
See the source-bound provenance receipt under audits/lagrangian-degree.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry Matrix

universe u

namespace M9Native.SmoothDifferentialsRankThin

private def sectionsEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    Γ(Scheme.Hom.relativeDifferentials f, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)] :=
  let := Stacks.Smooth.algebraAppLE f hUV
  (sectionsLinearEquivOfIso (Scheme.Hom.cotangentSheafIso f) U).trans
    (Stacks.Smooth.cotangentSectionsEquiv f hU hV hUV).symm

private theorem natCard_compl_range_map {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation R B ι σ) :
    Nat.card ((Set.range P.map)ᶜ : Set ι) = Nat.card ι - Nat.card σ := by
  classical
  have h := Nat.card_congr (Equiv.Set.sumCompl (Set.range P.map))
  rw [Nat.card_sum, Nat.card_range_of_injective P.map_inj] at h
  omega

private theorem module_rank_of_basis {R : Type u} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    Module.IsFiniteLocallyFreeOfRank R M n := by
  classical
  refine ⟨PUnit.{u + 1}, fun _ => 1, by simp, fun _ => ?_⟩
  let : Algebra R (Localization.Away (1 : R)) :=
    @OreLocalization.instAlgebra R _ (Submonoid.powers (1 : R)) _ R _ (Algebra.id R)
  have : IsLocalization (Submonoid.powers (1 : R)) (Localization.Away (1 : R)) :=
    Localization.isLocalization (R := R) (M := Submonoid.powers 1)
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R)) (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

private theorem exists_affine_subset {Y : Scheme.{u}} (y : Y) (O : Y.Opens)
    (hy : y ∈ O) : ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy O.isOpen
  exact ⟨⟨V, hV⟩, hyV, hVO⟩

theorem exists_basis_on_affine {X S : Scheme.{u}} (p : X ⟶ S) {n : ℕ}
    [SmoothOfRelativeDimension n p] (x : X) {W : S.Opens} (hW : IsAffineOpen W)
    {T : X.Opens} (hxT : x ∈ T) (hTW : T ≤ p ⁻¹ᵁ W) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ ∃ (hUT : U ≤ T),
      letI := Stacks.Smooth.algebraAppLE p (hUT.trans hTW)
      Nonempty (Module.Basis (Fin n) Γ(X, U) Ω[Γ(X, U)⁄Γ(S, W)]) := by
  classical
  obtain ⟨W₀, hW₀, U₀, hU₀, hxU₀, e₀, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) x
  let := Stacks.Smooth.algebraAppLE p e₀
  have hstd' : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, W₀) Γ(X, U₀) := hstd
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ := hstd'.out
  have : Finite ι := hι
  have : Finite σ := hσ
  have hcard : Nat.card ((Set.range P.map)ᶜ : Set ι) = n :=
    (natCard_compl_range_map P).trans hP
  set F := Scheme.Hom.relativeDifferentials p with hF
  have : F.IsQuasicoherent := Scheme.Hom.isQuasicoherent_relativeDifferentials p
  -- the sections of `Ω_{X/S}` on the standard smooth chart are free of rank `n`
  let b₀ : Module.Basis (Fin n) Γ(X, U₀) Γ(F, U₀) :=
    (P.basisKaehler.reindex (Finite.equivFinOfCardEq hcard)).map
      (sectionsEquiv p hU₀ hW₀ e₀).symm
  -- shrink the chart to a basic open inside `T`
  obtain ⟨g, hgT, hxg⟩ := hU₀.exists_basicOpen_le (V := T) ⟨x, hxT⟩ hxU₀
  refine ⟨X.basicOpen g, hU₀.basicOpen g, hxg, hgT, ?_⟩
  have : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) :=
    hU₀.isLocalization_basicOpen g
  let : Module Γ(X, U₀) Γ(F, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g))
  have : IsScalarTower Γ(X, U₀) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : Γ(F, U₀) →ₗ[Γ(X, U₀)] Γ(F, X.basicOpen g) :=
    { toFun a := F.presheaf.map (homOfLE (X.basicOpen_le g)).op a
      map_add' a b := by exact map_add _ a b
      map_smul' r a := by exact Scheme.Modules.map_smul F (homOfLE (X.basicOpen_le g)) r a }
  have : IsLocalizedModule (Submonoid.powers g) ρ :=
    isLocalizedModule_restrict_basicOpen F hU₀ g ρ fun _ => rfl
  exact ⟨(b₀.ofIsLocalizedModule Γ(X, X.basicOpen g) (Submonoid.powers g) ρ).map
    (sectionsEquiv p (hU₀.basicOpen g) hW (hgT.trans hTW))⟩

/-! ### The relative differentials of a morphism smooth of relative dimension `n` -/

/-- **The sheaf of relative differentials of a morphism smooth of relative dimension `n` is
finite locally free of rank `n`.**  Finite local freeness of rank `n` is affine-local on
sections for a quasi-coherent module, and the charts of
`Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential` give a basis of `n` sections
around every point. -/
theorem relativeDifferentials_rank {S X : Scheme.{u}} (p : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n p] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials p) n := by
  have : (Scheme.Hom.relativeDifferentials p).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials p
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ n).mp
    (Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens _ n fun x => ?_)
  obtain ⟨W, hxW, -⟩ := exists_affine_subset (p.base x) ⊤ trivial
  obtain ⟨U, hU, hxU, hUW, hb⟩ :=
    exists_basis_on_affine (n := n) p x W.2 (T := p ⁻¹ᵁ W.1) hxW le_rfl
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  let := Stacks.Smooth.algebraAppLE p (hUW.trans (le_refl (p ⁻¹ᵁ W.1)))
  exact module_rank_of_basis
    (hb.some.map (sectionsEquiv p hU W.2 hUW).symm)


end M9Native.SmoothDifferentialsRankThin
