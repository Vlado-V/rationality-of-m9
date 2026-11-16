module

public import M9.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Regrouping rational variables in the final rationality argument

The fields in this file are actual fraction fields of polynomial rings.  The
final result uses the given rationality of an eight-variable extension, retaining
the remaining eight variables of a sixteen-variable extension.
-/

@[expose] public section
noncomputable section

namespace M9

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A change of the set of independent variables extends to fraction fields. -/
def rationalFieldReindex (K : Type*) [Field K] {σ τ : Type*} (e : σ ≃ τ) :
    FractionRing (MvPolynomial σ K) ≃ₐ[K] FractionRing (MvPolynomial τ K) :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K e)

@[simp]
theorem rationalFieldReindex_algebraMap (K : Type*) [Field K] {σ τ : Type*}
    (e : σ ≃ τ) (p : MvPolynomial σ K) :
    rationalFieldReindex K e (algebraMap _ (FractionRing (MvPolynomial σ K)) p) =
      algebraMap _ (FractionRing (MvPolynomial τ K)) (MvPolynomial.rename e p) := by
  simp [rationalFieldReindex]

/-- A base-field algebra equivalence extends coefficientwise to rational fields. -/
def rationalFieldMap {C E F : Type*} [Field C] [Field E] [Field F]
    [Algebra C E] [Algebra C F] (e : E ≃ₐ[C] F) (n : ℕ) :
    RationalField E n ≃ₐ[C] RationalField F n :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv (Fin n) e)

@[simp]
theorem rationalFieldMap_algebraMap {C E F : Type*} [Field C] [Field E] [Field F]
    [Algebra C E] [Algebra C F] (e : E ≃ₐ[C] F) (n : ℕ) (p : MvPolynomial (Fin n) E) :
    rationalFieldMap e n (algebraMap _ (RationalField E n) p) =
      algebraMap _ (RationalField F n) (MvPolynomial.map e.toRingHom p) := by
  simp [rationalFieldMap]

/-- Localizing polynomial coefficients before taking fractions gives the fraction
field of the original polynomial ring. -/
theorem isFractionRing_iterated_polynomial (K : Type*) [Field K] (σ τ : Type*) :
    IsFractionRing (MvPolynomial τ (MvPolynomial σ K))
      (FractionRing (MvPolynomial τ (FractionRing (MvPolynomial σ K)))) := by
  let A := MvPolynomial σ K
  let B := MvPolynomial τ A
  let S := MvPolynomial τ (FractionRing A)
  let T := FractionRing S
  let N := (nonZeroDivisors A).map (MvPolynomial.C (σ := τ))
  have hinj : Function.Injective (algebraMap B S) := by
    exact MvPolynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
  have hcomap : (nonZeroDivisors S).comap (algebraMap B S) = nonZeroDivisors B :=
    le_antisymm (comap_nonZeroDivisors_le_of_injective hinj)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    N (nonZeroDivisors S) T (fun _ hx => hx.mem_nonZeroDivisors)
  rw [hcomap] at h
  exact h

/-- The original coefficient-field scalar action agrees with the iterated
polynomial localization maps. -/
theorem isScalarTower_iterated_polynomial (K : Type*) [Field K] (σ τ : Type*) :
    IsScalarTower K (MvPolynomial τ (MvPolynomial σ K))
      (FractionRing (MvPolynomial τ (FractionRing (MvPolynomial σ K)))) := by
  have : IsScalarTower K (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (FractionRing (MvPolynomial σ K))) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      change MvPolynomial.C (algebraMap K (FractionRing (MvPolynomial σ K)) k) =
        MvPolynomial.map (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))
          (MvPolynomial.C (MvPolynomial.C k))
      rw [MvPolynomial.map_C]
      exact congrArg MvPolynomial.C
        (IsScalarTower.algebraMap_apply K (MvPolynomial σ K)
          (FractionRing (MvPolynomial σ K)) k)
  exact IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply K
      (MvPolynomial τ (FractionRing (MvPolynomial σ K)))]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (FractionRing (MvPolynomial σ K)))]
    rfl

/-- Flatten an iterated rational function field, with outer variables in the left
summand and coefficient-field variables in the right summand. -/
def rationalFieldSumVariables (K : Type*) [Field K] (σ τ : Type*) :
    FractionRing (MvPolynomial τ (FractionRing (MvPolynomial σ K))) ≃ₐ[K]
      FractionRing (MvPolynomial (τ ⊕ σ) K) := by
  letI := isFractionRing_iterated_polynomial K σ τ
  letI := isScalarTower_iterated_polynomial K σ τ
  exact (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.sumAlgEquiv K τ σ)).symm

@[simp]
theorem rationalFieldSumVariables_algebraMap (K : Type*) [Field K] (σ τ : Type*)
    (p : MvPolynomial τ (MvPolynomial σ K)) :
    rationalFieldSumVariables K σ τ
        (algebraMap _ (FractionRing (MvPolynomial τ (FractionRing (MvPolynomial σ K)))) p) =
      algebraMap _ (FractionRing (MvPolynomial (τ ⊕ σ) K))
        ((MvPolynomial.sumAlgEquiv K τ σ).symm p) := by
  have := isFractionRing_iterated_polynomial K σ τ
  have := isScalarTower_iterated_polynomial K σ τ
  simp [rationalFieldSumVariables]

/-- Flatten iterated rational fields, numbering the coefficient-field variables
first and then the outer variables. -/
def rationalFieldIteratedEquiv (K : Type*) [Field K] (m n : ℕ) :
    RationalField (RationalField K m) n ≃ₐ[K] RationalField K (m + n) :=
  (rationalFieldSumVariables K (Fin m) (Fin n)).trans
    (rationalFieldReindex K ((Equiv.sumComm (Fin n) (Fin m)).trans finSumFinEquiv))

@[simp]
theorem rationalFieldIteratedEquiv_algebraMap (K : Type*) [Field K] (m n : ℕ)
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin m) K)) :
    rationalFieldIteratedEquiv K m n
        (algebraMap _ (RationalField (RationalField K m) n) p) =
      algebraMap _ (RationalField K (m + n))
        (MvPolynomial.rename ((Equiv.sumComm (Fin n) (Fin m)).trans finSumFinEquiv)
          ((MvPolynomial.sumAlgEquiv K (Fin n) (Fin m)).symm p)) := by
  simp [rationalFieldIteratedEquiv]

/-- The final algebraic assembly retains `b` independent variables after a
rational presentation of the extension by `a` variables.  All algebra structures
on rational fields are the canonical ones induced by their coefficient fields. -/
def rationalExtensionAssemblyEquiv {C E M : Type*} [Field C] [Field E] [Field M]
    [Algebra C E] [Algebra C M] (a b c : ℕ)
    (presentation : M ≃ₐ[C] RationalField E (a + b))
    (stablePresentation : RationalField E a ≃ₐ[C] RationalField C c) :
    M ≃ₐ[C] RationalField C (c + b) :=
  presentation.trans <|
    ((rationalFieldIteratedEquiv E a b).symm.restrictScalars C).trans <|
      (rationalFieldMap stablePresentation b).trans (rationalFieldIteratedEquiv C c b)

/-- The paper's final `16 = 8 + 8`, `16 + 8 = 24` rational-field equivalence. -/
def rationalExtensionSixteenEightEquiv {C E M : Type*} [Field C] [Field E] [Field M]
    [Algebra C E] [Algebra C M]
    (presentation : M ≃ₐ[C] RationalField E 16)
    (stablePresentation : RationalField E 8 ≃ₐ[C] RationalField C 16) :
    M ≃ₐ[C] RationalField C 24 :=
  rationalExtensionAssemblyEquiv 8 8 16 presentation stablePresentation

/-- A concrete pair of presentations proves rationality of dimension twenty-four. -/
theorem rationalOfDimension_twentyFour {C E M : Type*} [Field C] [Field E] [Field M]
    [Algebra C E] [Algebra C M]
    (presentation : M ≃ₐ[C] RationalField E 16)
    (stablePresentation : RationalField E 8 ≃ₐ[C] RationalField C 16) :
    RationalOfDimension C M 24 :=
  ⟨rationalExtensionSixteenEightEquiv presentation stablePresentation⟩

end M9
