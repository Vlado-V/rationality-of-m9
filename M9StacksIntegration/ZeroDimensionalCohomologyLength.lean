module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CokernelSupportDegree
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Actual local length and H0 of a zero-dimensional coherent sheaf

The original global germ map is promoted to a base-field-linear
isomorphism onto the actual stalks. Over an algebraically closed field,
every point in the original zero-dimensional support is closed and has
residue degree one. Actual change of rings for composition length thus
identifies the sum of actual local-ring lengths with original H0.

The local algebra length calculation follows the elementary opening
lemmas of pinned StacksFrontier `Curves.RiemannHurwitzFormula`, without
importing its global formula or its unrelated dependency closure.
Package sources remain unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.ModuleStalk

universe u

namespace M9Native.ZeroDimensionalCohomologyLength

/-- Dimension is the finite natural part of field-module length, also
for the infinite-dimensional case where both natural parts are zero. -/
theorem finrank_eq_length_toNat (k : Type u) [Field k] (M : Type u)
    [AddCommGroup M] [Module k M] :
    Module.finrank k M = (Module.length k M).toNat := by
  by_cases h : Module.Finite k M
  · rw [Module.length_eq_finrank k M, ENat.toNat_natCast]
  · rw [Module.finrank_of_not_finite h]
    have : Module.length k M = ⊤ := by
      by_contra hne
      have := (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (Module.length_ne_top_iff.mp hne)).1
      exact h (Module.IsNoetherian.finite k M)
    rw [this, ENat.toNat_top]

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (F : X.Modules) [F.IsCoherent]
variable (hs : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)

include f hs

/-- The original native H0 is linearly identified by the actual germ
maps with the actual stalks, with scalars from the original f. -/
def cohomologyStalkLinearEquiv :
    let : ∀ x : ↥(SheafOfModules.supp F),
        Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
      fun x => Module.compHom _ (baseToStalk f x.1)
    cohomologyOverField k f F 0 ≃ₗ[k]
      ∀ x : ↥(SheafOfModules.supp F),
        TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1 := by
  let : ∀ x : ↥(SheafOfModules.supp F),
      Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    fun x => Module.compHom _ (baseToStalk f x.1)
  let G := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)
  let L : G →ₗ[k] ∀ x : ↥(SheafOfModules.supp F),
      TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1 :=
    { toFun := fun s x => (F.presheaf.Γgerm x.1).hom s
      map_add' := fun s t => funext fun x => map_add _ s t
      map_smul' := fun c s => funext fun x =>
        (Γgerm_smul F x.1 (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c)
          (show Γ(F, ⊤) from s) :) }
  exact (cohomologyOverFieldZeroIsoSections k f F).toLinearEquiv.trans
    (LinearEquiv.ofBijective L (bijective_suppGermHom_of_supp_le_zero k f F hs))

/-- Every original stalk in the support is finite-dimensional over the base field. -/
theorem stalk_finiteDimensional (x : ↥(SheafOfModules.supp F)) :
    let : Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
      Module.compHom _ (baseToStalk f x.1)
    Module.Finite k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) := by
  classical
  let : ∀ x : ↥(SheafOfModules.supp F),
      Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    fun x => Module.compHom _ (baseToStalk f x.1)
  let e := cohomologyStalkLinearEquiv f F hs
  let : FiniteDimensional k (cohomologyOverField k f F 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 0
  exact Module.Finite.of_surjective ((LinearMap.proj x).comp e.toLinearMap) fun m => by
    obtain ⟨a, ha⟩ := e.surjective (Pi.single x m)
    exact ⟨a, by simp [ha]⟩

/-- The original local-ring composition lengths are finite, before any use of toNat. -/
theorem stalk_isFiniteLength (x : ↥(SheafOfModules.supp F)) :
    IsFiniteLength (X.presheaf.stalk x.1)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) := by
  let : Algebra k (X.presheaf.stalk x.1) := (baseToStalk f x.1).toAlgebra
  let : Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    Module.compHom _ (baseToStalk f x.1)
  let : IsScalarTower k (X.presheaf.stalk x.1)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let := stalk_finiteDimensional f F hs x
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- Every original support point is closed, derived from actual
zero-dimensional scheme-theoretic support. -/
theorem support_point_isClosed (x : X) (hx : x ∈ SheafOfModules.supp F) :
    IsClosed ({x} : Set X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : DiscreteTopology ((annihilatorIdeal F).subscheme : Type u) :=
    (discreteTopology_and_finite_subscheme_annihilatorIdeal_of_supp_le_zero k f F hs).1
  rw [supp_eq_range_subschemeι F] at hx
  obtain ⟨z, rfl⟩ := hx
  simpa only [Set.image_singleton] using
    (annihilatorIdeal F).subschemeι.isClosedMap _
      (isClosed_singleton : IsClosed ({z} : Set (annihilatorIdeal F).subscheme))

variable [IsAlgClosed k]

omit hs [F.IsCoherent] in
/-- At every actual closed point, residue degree one identifies base
field dimension with the original local-ring composition length. -/
theorem stalk_finrank_eq_local_length (x : X) (hx : IsClosed ({x} : Set X)) :
    let : Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) :=
      Module.compHom _ (baseToStalk f x)
    Module.finrank k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) =
      (Module.length (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)).toNat := by
  let : Algebra k (X.presheaf.stalk x) := (baseToStalk f x).toAlgebra
  let : Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) :=
    Module.compHom _ (baseToStalk f x)
  let : IsScalarTower k (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsLocalHom (algebraMap k (X.presheaf.stalk x)) :=
    ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha
        exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have hκ : Module.finrank k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = 1 :=
    finrank_residueField_of_isClosed f x hx
  let : Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Module.finite_of_finrank_pos (by rw [hκ]; omega)
  have key := IsLocalRing.length_restrictScalars k (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  rw [← Module.length_eq_of_surjective (S := k)
      (M := IsLocalRing.ResidueField (X.presheaf.stalk x))
      IsLocalRing.residue_surjective] at key
  rw [Module.length_eq_finrank k (IsLocalRing.ResidueField (X.presheaf.stalk x)),
    hκ, Nat.cast_one, mul_one] at key
  change Module.finrank k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) =
    (Module.length (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)).toNat
  rw [finrank_eq_length_toNat, key]

omit [IsAlgClosed k] in
/-- The literal finite sum of composition lengths over original local
stalk rings. This is not defined using any cohomology dimension. -/
def totalStalkLength : ℕ :=
  let : Fintype ↥(SheafOfModules.supp F) :=
    (finite_supp_of_supp_le_zero k f F hs).fintype
  ∑ x : ↥(SheafOfModules.supp F),
    (Module.length (X.presheaf.stalk x.1)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1)).toNat

/-- Original H0 equals the sum of the original actual local-ring lengths. -/
theorem totalStalkLength_eq_h0 :
    totalStalkLength f F hs = Module.finrank k (cohomologyOverField k f F 0) := by
  classical
  let : Fintype ↥(SheafOfModules.supp F) :=
    (finite_supp_of_supp_le_zero k f F hs).fintype
  let : ∀ x : ↥(SheafOfModules.supp F),
      Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    fun x => Module.compHom _ (baseToStalk f x.1)
  let e := cohomologyStalkLinearEquiv f F hs
  let : FiniteDimensional k (cohomologyOverField k f F 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 0
  let : ∀ x : ↥(SheafOfModules.supp F),
      Module.Finite k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    stalk_finiteDimensional f F hs
  have hd := e.finrank_eq
  rw [Module.finrank_pi_fintype k] at hd
  rw [hd]
  change (∑ x : ↥(SheafOfModules.supp F),
    (Module.length (X.presheaf.stalk x.1)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1)).toNat) = _
  exact Finset.sum_congr rfl fun x _ =>
    (stalk_finrank_eq_local_length f F x.1 (support_point_isClosed f F hs x.1 x.2)).symm

end M9Native.ZeroDimensionalCohomologyLength
