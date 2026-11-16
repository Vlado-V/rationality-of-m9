module

public import M9StacksIntegration.PowerSeriesLocalDimension
public import StacksFrontier.Deformation.TangentSpace.PowerSeries

/-!
# The actual represented tangent rank of a field power-series model

The field itself is an actual object of the completed Artin base. Its
represented tangent is zero because all coefficient-algebra maps out of
the field agree. The original relative power-series tangent theorem then
computes the actual transported represented tangent, with no supplied rank.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory Deformation IsLocalRing

universe u

namespace M9Native.RepresentedPowerSeriesDimension

/-- The coefficient field as an actual complete local k-algebra. -/
def fieldObject (k : Type u) [Field k] : CompleteLocalAlgCat.{u,u,u} k k where
  carrier := k
  completeLocal := ⟨inferInstance,inferInstance,by
    simpa only [IsLocalRing.maximalIdeal_eq_bot] using IsAdicComplete.bot k⟩
  residueEquiv :=
    (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField k))
      ⟨(algebraMap k _).injective,IsLocalRing.residue_surjective⟩).symm

variable {k : Type u} [Field k]

/-- The actual coefficient morphism from the completed coefficient-field object. -/
def coefficientMap (R : CompleteLocalAlgCat.{u,u,u} k k) : fieldObject k ⟶ R where
  hom := Algebra.ofId k R
  isLocal := by
    change IsLocalHom (algebraMap k R)
    constructor
    intro x hx
    apply (isUnit_iff_ne_zero (a := x)).mpr
    intro hx0
    have hz : IsUnit (0 : R) := by simpa only [hx0,map_zero] using hx
    exact not_isUnit_zero hz
  residue_comm := by
    intro x
    have hl := R.residueEquiv.commutes (x : k)
    have hr := (fieldObject k).residueEquiv.commutes (x : k)
    change R.residueEquiv (residue R (algebraMap k R x)) = x at hl
    change (fieldObject k).residueEquiv (residue (fieldObject k) x) = x at hr
    exact hl.trans hr.symm

/-- The actual coefficient map exhibits the actual ring model as a power-series extension. -/
theorem coefficientMap_isPowerSeriesOver
    (R : CompleteLocalAlgCat.{u,u,u} k k) {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) : IsPowerSeriesOver (coefficientMap R) := by
  let r := e.toRingEquiv
  have hr : ∀ c : k, r (algebraMap k R c) = algebraMap k (MvPowerSeries (Fin n) k) c :=
    e.commutes
  change (letI : Algebra k R := (algebraMap k R).toAlgebra
    ∃ m : ℕ, Nonempty (R ≃ₐ[k] MvPowerSeries (Fin m) k))
  letI : Algebra k R := (algebraMap k R).toAlgebra
  exact ⟨n,⟨{ __ := r, commutes' := hr }⟩⟩

/-- Coefficient-algebra maps from k into its dual numbers are unique. -/
theorem field_tangent_subsingleton :
    Subsingleton (tangentSpaceArtinian k k (restrictedCoyoneda (fieldObject k))) := by
  refine ⟨?_⟩
  intro a b
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro x
  have ha := a.hom.commutes (x : k)
  have hb := b.hom.commutes (x : k)
  exact ha.trans hb.symm

/-- The represented tangent rank is computed from the actual number of variables. -/
theorem tangent_finrank_of_model (R : CompleteLocalAlgCat.{u,u,u} k k) {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) :
    Module.finrank k (tangentSpaceArtinian k k (restrictedCoyoneda R)) = n := by
  obtain ⟨m,hm,ht⟩ :=
    finrank_tangentSpaceArtinian_of_isPowerSeriesOver (coefficientMap_isPowerSeriesOver R e)
  have hfield : ringKrullDim (fieldObject k) = 0 := by
    change ringKrullDim k = 0
    exact ringKrullDim_eq_zero_of_field k
  have hfieldT : Module.finrank k
      (tangentSpaceArtinian k k (restrictedCoyoneda (fieldObject k))) = 0 := by
    let := field_tangent_subsingleton (k := k)
    exact Module.finrank_zero_of_subsingleton
  rw [hfield,zero_add] at hm
  rw [hfieldT,zero_add] at ht
  have hmn : m = n := by
    exact_mod_cast hm.symm.trans (PowerSeriesLocalDimension.krullDimension_of_powerSeriesEquiv e)
  simpa only [hmn] using ht

/-- In the constructed field power-series model, the actual ring dimension
is the actual represented tangent rank. -/
theorem krullDimension_eq_tangent_finrank (R : CompleteLocalAlgCat.{u,u,u} k k) {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) :
    ringKrullDim R =
      (Module.finrank k (tangentSpaceArtinian k k (restrictedCoyoneda R)) : WithBot ℕ∞) := by
  rw [tangent_finrank_of_model R e]
  exact PowerSeriesLocalDimension.krullDimension_of_powerSeriesEquiv e

end M9Native.RepresentedPowerSeriesDimension
