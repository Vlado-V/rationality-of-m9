module

public import M9StacksIntegration.FreeTwoPairIncidence
public import M9StacksIntegration.TensorSubbundleUniversalMono
public import M9StacksIntegration.TensorUnitSections

/-! The original free-pair incidence is unchanged by an actual
subbundle inclusion. Exactness and the locally free quotient derive
universal monicity after tensoring by the genuine O1. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.FreeTwoPairIncidenceSubbundle
open LagrangianMatrixChart FreeTwoProjectiveCharts LinearIncidenceTensorCoordinates

variable (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
  (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₃)

def tensorInjection : FreeTwoPairIncidence.equationBundle X S.X₁ ⟶
    FreeTwoPairIncidence.equationBundle X S.X₂ :=
  TensorUnitSections.tensorFirst ((Scheme.Modules.pullback (projectiveBundleProjection X)).map S.f)
    (tautologicalLine X)

include hS hQ in
theorem tensorInjection_universallyMono {T : Scheme.{u}} (f : T ⟶ projectiveBundleSpace X) :
    Mono ((Scheme.Modules.pullback f).map (tensorInjection X S)) := by
  letI : SheafOfModules.IsInvertible (projectiveBundleSpace X).presheaf
      (projectiveBundleSpace X).ringCatSheaf.2 (tautologicalLine X) :=
    Stacks.Chow.isInvertible_bundleTwist (freeOn X 2)
  exact TensorSubbundleUniversalMono.mono_pullback_tensor
    (S.map (Scheme.Modules.pullback (projectiveBundleProjection X)))
    (VectorBundleKZeroPullbackAdd.shortExact_pullback (projectiveBundleProjection X) S hS hQ)
    (Stacks.Chow.isFiniteLocallyFree_pullback (projectiveBundleProjection X) S.X₃ hQ)
    (tautologicalLine X) f

def imageSections (s : Fin 2 → Γ(S.X₁,⊤)) : Fin 2 → Γ(S.X₂,⊤) := fun k => S.f.app ⊤ (s k)

theorem equation_image (s : Fin 2 → Γ(S.X₁,⊤)) :
    (tensorInjection X S).app ⊤ (FreeTwoPairIncidence.equationSection X S.X₁ s) =
      FreeTwoPairIncidence.equationSection X S.X₂ (imageSections X S s) := by
  simp only [FreeTwoPairIncidence.equationSection,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := TensorUnitSections.tensorFirst_tensorTop
    ((Scheme.Modules.pullback (projectiveBundleProjection X)).map S.f) (tautologicalLine X)
    (pullbackGlobalSections (projectiveBundleProjection X) S.X₁ (s k)) (tautCoordinate X k)
  rw [SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections] at h
  exact h

variable (r q : ℕ) [hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ r]
  [hFq : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ q]

include hS hQ r q hEr hFq in
theorem ideal_eq (s : Fin 2 → Γ(S.X₁,⊤)) :
    FreeTwoPairIncidence.ideal X S.X₂ (imageSections X S s) =
      FreeTwoPairIncidence.ideal X S.X₁ s := by
  letI := FreeTwoPairIncidence.equationBundle_rank X S.X₁ r
  letI := FreeTwoPairIncidence.equationBundle_rank X S.X₂ q
  rw [FreeTwoPairIncidence.ideal,← equation_image X S s]
  exact SectionZeroSubbundle.sectionZeroIdeal_eq_of_universallyMono (tensorInjection X S) r q
    (fun f => tensorInjection_universallyMono X S hS hQ f)
      (FreeTwoPairIncidence.equationSection X S.X₁ s)

def zeroIso (s : Fin 2 → Γ(S.X₁,⊤)) :
    FreeTwoPairIncidence.space X S.X₂ (imageSections X S s) ≅ FreeTwoPairIncidence.space X S.X₁ s :=
  eqToIso (congrArg (fun I : (projectiveBundleSpace X).IdealSheafData => I.subscheme)
    (ideal_eq X S hS hQ r q s))

@[reassoc]
theorem zeroIso_hom_toBase (s : Fin 2 → Γ(S.X₁,⊤)) :
    (zeroIso X S hS hQ r q s).hom ≫ FreeTwoPairIncidence.toBase X S.X₁ s =
      FreeTwoPairIncidence.toBase X S.X₂ (imageSections X S s) := by
  simpa only [zeroIso,FreeTwoPairIncidence.toBase,Category.assoc] using
    congrArg (· ≫ projectiveBundleProjection X)
      (LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (ideal_eq X S hS hQ r q s))

end M9Native.FreeTwoPairIncidenceSubbundle
