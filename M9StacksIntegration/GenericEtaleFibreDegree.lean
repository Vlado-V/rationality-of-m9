module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.Perfect
public import StacksFrontier.RingTheory.Etale.GenericFiniteEtaleFinitePresentation

/-!
# Actual closed-fibre counts and fraction-field degree

The fibre cardinality is the number of actual algebra maps, rather than a
supplied rank. Finite étale algebras over a separably closed field split as
finite products. Finite flatness over an integral base identifies every
closed-fibre dimension with the generic module rank.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Algebra TensorProduct

universe u

namespace M9Native.GenericEtaleFibreDegree

/-- Equality of finite transcendence degrees forces the relative extension
to be algebraic; no finiteness of the relative field degree is assumed. -/
theorem isAlgebraic_of_equal_finite_trdeg (k K L : Type u)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (hfin : Algebra.trdeg k K < Cardinal.aleph0)
    (heq : Algebra.trdeg k K = Algebra.trdeg k L) : Algebra.IsAlgebraic K L := by
  apply trdeg_eq_zero_iff.mp
  apply (Cardinal.add_right_inj_of_lt_aleph0 hfin).mp
  calc
    Algebra.trdeg K L + Algebra.trdeg k K =
        Algebra.trdeg k K + Algebra.trdeg K L := add_comm _ _
    _ = Algebra.trdeg k L := trdeg_add_eq k K (A := L)
    _ = 0 + Algebra.trdeg k K := by rw [zero_add, heq]

/-- In characteristic zero the extension obtained above is genuinely
separable, as required by generic étaleness. -/
theorem isSeparable_of_equal_finite_trdeg (k K L : Type u)
    [Field k] [Field K] [Field L] [CharZero K]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (hfin : Algebra.trdeg k K < Cardinal.aleph0)
    (heq : Algebra.trdeg k K = Algebra.trdeg k L) : Algebra.IsSeparable K L := by
  have := isAlgebraic_of_equal_finite_trdeg k K L hfin heq
  infer_instance

/-- Actual rational points of a finite étale algebra over a separably closed
field are counted by its vector-space dimension, including the zero algebra. -/
theorem card_algHom_eq_finrank (k B : Type*) [Field k] [IsSepClosed k]
    [CommRing B] [Algebra k B] [Algebra.Etale k B] :
    Nat.card (B →ₐ[k] k) = Module.finrank k B := by
  have := Algebra.FormallyUnramified.finite_of_free k B
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let := Fintype.ofFinite (PrimeSpectrum B)
  calc
    Nat.card (B →ₐ[k] k) = Nat.card (PrimeSpectrum B) :=
      Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k B)
    _ = Module.finrank k (PrimeSpectrum B → k) := by simp
    _ = Module.finrank k B :=
      (Algebra.FormallyEtale.equivPiOfIsSepClosed k B).toLinearEquiv.finrank_eq.symm

/-- Finite-flat fibre dimension over an integral base, without a chosen rank
or a supplied basis on an open. -/
theorem fibre_finrank_eq (A B k : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    [Field k] [Algebra A k] :
    Module.finrank k (k ⊗[A] B) = Module.finrank A B := by
  let p : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  let q : PrimeSpectrum A := p.comap (algebraMap A k)
  calc
    Module.finrank k (k ⊗[A] B) = Module.rankAtStalk (k ⊗[A] B) p := by simp
    _ = Module.rankAtStalk B q := Module.rankAtStalk_baseChange p
    _ = Module.finrank A B := by
      rw [← q.asIdeal.finrank_fiber_eq_rankAtStalk, q.asIdeal.finrank_fiber_eq_finrank]

/-- The actual algebra lifts to an algebraically closed residue field of a
finite étale algebra over a domain are counted by its generic rank. -/
theorem card_algHom_eq_generic_finrank (A B k : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B]
    [Field k] [IsSepClosed k] [Algebra A k] :
    Nat.card (B →ₐ[A] k) = Module.finrank A B := by
  calc
    Nat.card (B →ₐ[A] k) = Nat.card ((k ⊗[A] B) →ₐ[k] k) :=
      Nat.card_congr (Algebra.TensorProduct.liftEquivRight A k B k)
    _ = Module.finrank k (k ⊗[A] B) := card_algHom_eq_finrank k _
    _ = Module.finrank A B := fibre_finrank_eq A B k

/-- The generic rank above is the actual degree of the fraction-field
extension. No desired finite degree is passed to the theorem. -/
theorem card_algHom_eq_fraction_finrank (A B k K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B]
    [Field k] [IsSepClosed k] [Algebra A k]
    [CommRing K] [CommRing L] [Algebra A K] [Algebra B L] [Algebra A L]
    [Module K L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] :
    Nat.card (B →ₐ[A] k) = Module.finrank K L := by
  rw [card_algHom_eq_generic_finrank A B k, IsFractionRing.finrank_eq A K B L]

/-- A genuine closed point exists for every nonzero finite-type algebra
over an algebraically closed field. -/
theorem exists_algHom_of_finiteType (k A : Type*) [Field k] [IsAlgClosed k]
    [CommRing A] [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] :
    Nonempty (A →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := hm
  let := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let e : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)⟩

/-- A nonempty principal open of a finite-type integral algebra over an
algebraically closed field contains an actual rational point. -/
theorem exists_point_ne_zero (k A : Type*) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (g : A) (hg : g ≠ 0) : ∃ x : A →ₐ[k] k, x g ≠ 0 := by
  let S := Localization.Away g
  have : IsDomain S := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨y⟩ := exists_algHom_of_finiteType k S
  refine ⟨y.comp (IsScalarTower.toAlgHom k A S), ?_⟩
  exact ((IsLocalization.Away.algebraMap_isUnit (S := S) g).map y.toRingHom).ne_zero

section PointLifts

variable (k A B : Type*) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- Actual `k`-algebra lifts of the specified `k`-point under the given
algebra map, rather than abstract geometric points or a cardinal premise. -/
def PointLifts (x : A →ₐ[k] k) : Type _ :=
  { y : B →ₐ[k] k // y.comp (IsScalarTower.toAlgHom k A B) = x }

/-- The lift subtype is the actual algebra-hom fibre after making the
coefficient field an `A`-algebra through the specified point. -/
def pointLiftsEquiv (x : A →ₐ[k] k) :
    letI : Algebra A k := x.toRingHom.toAlgebra
    PointLifts k A B x ≃ (B →ₐ[A] k) := by
  letI : Algebra A k := x.toRingHom.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' x.comp_algebraMap.symm
  refine
    { toFun := fun y => { __ := y.val.toRingHom, commutes' := fun a => ?_ }
      invFun := fun y => ⟨y.restrictScalars k, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun y => ?_ }
  · exact congrArg (fun f : A →ₐ[k] k => f a) y.property
  · ext a
    exact y.commutes a
  · apply Subtype.ext
    ext b
    rfl
  · ext b
    rfl

/-- Count actual `k`-algebra lifts at a specified rational point for a
finite étale map over an integral base. -/
theorem card_pointLifts_eq_finrank [IsSepClosed k] [IsDomain A]
    [Module.Finite A B] [Algebra.Etale A B] (x : A →ₐ[k] k) :
    Nat.card (PointLifts k A B x) = Module.finrank A B := by
  let : Algebra A k := x.toRingHom.toAlgebra
  exact (Nat.card_congr (pointLiftsEquiv k A B x)).trans
    (card_algHom_eq_generic_finrank A B k)

end PointLifts

/-- The actual simultaneous localization of the target at an element of
the base. This is definitionally the native generic-étaleness model. -/
abbrev AwayTarget {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (g : A) := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))

/-- The actual hom-fibre is unchanged by a base change through which the
specified residue-field map factors. -/
def localizedAlgHomEquiv (A B Ag Bg k : Type*) [CommRing A] [CommRing B]
    [CommRing Ag] [CommRing Bg] [CommRing k]
    [Algebra A B] [Algebra A Ag] [Algebra B Bg] [Algebra A Bg] [Algebra Ag Bg]
    [IsScalarTower A B Bg] [IsScalarTower A Ag Bg] [Algebra.IsPushout A Ag B Bg]
    [Algebra A k] [Algebra Ag k] [IsScalarTower A Ag k] :
    (B →ₐ[A] k) ≃ (Bg →ₐ[Ag] k) :=
  (Algebra.TensorProduct.liftEquivRight A Ag B k).trans
    { toFun := fun f => f.comp (Algebra.IsPushout.equiv A Ag B Bg).symm.toAlgHom
      invFun := fun f => f.comp (Algebra.IsPushout.equiv A Ag B Bg).toAlgHom
      left_inv := fun f => by ext z; simp
      right_inv := fun f => by ext z; simp }

/-- Simultaneous localization preserves the actual generic module rank;
neither finiteness nor a chosen basis is assumed. -/
theorem away_finrank_eq (A B : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] (g : A) (hg : g ≠ 0) :
    Module.finrank (Localization.Away g) (AwayTarget B g) = Module.finrank A B := by
  have hM : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hM
  have : FaithfulSMul A (Localization.Away g) :=
    (faithfulSMul_iff_algebraMap_injective A (Localization.Away g)).mpr
      (IsLocalization.injective (Localization.Away g) hM)
  let f := (IsScalarTower.toAlgHom A B (AwayTarget B g)).toLinearMap
  have : IsLocalizedModule (Submonoid.powers g) f :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization.Away g) f).finrank_eq

/-- At a point where `g` is nonzero, a finite étale simultaneous localization
counts the lifts of the original map, with their actual generic rank. -/
theorem card_pointLifts_eq_finrank_of_localization (k A B : Type*)
    [Field k] [IsSepClosed k] [CommRing A] [IsDomain A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (g : A) (hg : g ≠ 0)
    (hfin : Module.Finite (Localization.Away g) (AwayTarget B g))
    (het : Algebra.Etale (Localization.Away g) (AwayTarget B g))
    (x : A →ₐ[k] k) (hx : x g ≠ 0) :
    Nat.card (PointLifts k A B x) = Module.finrank A B := by
  let : Module.Finite (Localization.Away g) (AwayTarget B g) := hfin
  let : Algebra.Etale (Localization.Away g) (AwayTarget B g) := het
  let : Algebra A k := x.toRingHom.toAlgebra
  let : Algebra (Localization.Away g) k :=
    (IsLocalization.Away.lift g (show IsUnit (algebraMap A k g) from hx.isUnit)).toAlgebra
  let : IsScalarTower A (Localization.Away g) k :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.Away.lift_comp g (show IsUnit (algebraMap A k g) from hx.isUnit)).symm
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : Algebra.IsPushout A B (Localization.Away g) (AwayTarget B g) :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers g) (Localization.Away g) B _
  have : Algebra.IsPushout A (Localization.Away g) B (AwayTarget B g) :=
    Algebra.IsPushout.symm inferInstance
  calc
    Nat.card (PointLifts k A B x) = Nat.card (B →ₐ[A] k) :=
      Nat.card_congr (pointLiftsEquiv k A B x)
    _ = Nat.card (AwayTarget B g →ₐ[Localization.Away g] k) :=
      Nat.card_congr (localizedAlgHomEquiv A B (Localization.Away g) (AwayTarget B g) k)
    _ = Module.finrank (Localization.Away g) (AwayTarget B g) :=
      card_algHom_eq_generic_finrank _ _ k
    _ = Module.finrank A B := away_finrank_eq A B g hg

section GenericDegree

variable (k A B K L : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]

/-- A genuine generic finite étale localization makes the actual number of
original `k`-algebra lifts equal the fraction-field degree. Finiteness and
étaleness are conclusions obtained from the native generic-localization
theorem, not assumptions on the original map or on its desired degree. -/
theorem exists_generic_finiteEtale_pointLifts_card :
    ∃ g : A, g ≠ 0 ∧ Module.Finite (Localization.Away g) (AwayTarget B g) ∧
      Algebra.Etale (Localization.Away g) (AwayTarget B g) ∧
      ∀ x : A →ₐ[k] k, x g ≠ 0 →
        Nat.card (PointLifts k A B x) = Module.finrank K L := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨g, hg, hfin, het⟩ :=
    Stacks.GenericFiniteEtale.exists_finite_etale_localization_of_finitePresentation
      (R := A) (B := B) K L
  refine ⟨g, hg, hfin, het, fun x hx => ?_⟩
  exact (card_pointLifts_eq_finrank_of_localization k A B g hg hfin het x hx).trans
    (IsFractionRing.finrank_eq A K B L).symm

/-- The cardinality part of the genuine generic finite étale localization. -/
theorem exists_generic_pointLifts_card :
    ∃ g : A, g ≠ 0 ∧ ∀ x : A →ₐ[k] k, x g ≠ 0 →
      Nat.card (PointLifts k A B x) = Module.finrank K L := by
  obtain ⟨g, hg, _, _, hcard⟩ := exists_generic_finiteEtale_pointLifts_card k A B K L
  exact ⟨g, hg, hcard⟩

/-- There is an actual nonempty closed fibre on that generic open. The
point is obtained from finite type over the algebraically closed base,
rather than being supplied as a rational-point assumption. -/
theorem exists_pointLifts_card_eq_fraction_finrank
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ x : A →ₐ[k] k, Nonempty (PointLifts k A B x) ∧
      Nat.card (PointLifts k A B x) = Module.finrank K L := by
  obtain ⟨g, hg, hcard⟩ := exists_generic_pointLifts_card k A B K L
  have hBg : algebraMap A B g ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg
  obtain ⟨y, hy⟩ := exists_point_ne_zero k B (algebraMap A B g) hBg
  let x : A →ₐ[k] k := y.comp (IsScalarTower.toAlgHom k A B)
  exact ⟨x, ⟨⟨y, rfl⟩⟩, hcard x hy⟩

/-- A closed-fibre orbit count determines the exact fraction-field degree.
It suffices to count nonempty fibres of the original map; no surjectivity,
finite-map hypothesis, rank formula, or generic-degree value is assumed. -/
theorem fraction_finrank_eq_of_nonempty_pointLifts_card
    (hinj : Function.Injective (algebraMap A B)) (N : ℕ)
    (hcard : ∀ x : A →ₐ[k] k, Nonempty (PointLifts k A B x) →
      Nat.card (PointLifts k A B x) = N) : Module.finrank K L = N := by
  obtain ⟨x, hx, hdeg⟩ := exists_pointLifts_card_eq_fraction_finrank k A B K L hinj
  exact hdeg.symm.trans (hcard x hx)

/-- A positive closed-fibre count proves finiteness of the actual field
extension together with its exact degree, rather than relying on a finite
extension hypothesis. In particular this applies directly to count `24`. -/
theorem finite_and_fraction_finrank_eq_of_nonempty_pointLifts_card
    (hinj : Function.Injective (algebraMap A B)) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ x : A →ₐ[k] k, Nonempty (PointLifts k A B x) →
      Nat.card (PointLifts k A B x) = N) : Module.Finite K L ∧ Module.finrank K L = N := by
  have hdeg := fraction_finrank_eq_of_nonempty_pointLifts_card k A B K L hinj N hcard
  exact ⟨Module.finite_of_finrank_pos (by rw [hdeg]; exact hN), hdeg⟩

end GenericDegree

end M9Native.GenericEtaleFibreDegree
