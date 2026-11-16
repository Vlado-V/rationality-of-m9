module

public import M9.DeterminantTwistField
public import M9.CayleyFixedField

/-! The determinant scalar quotient after adjoining an arbitrary complex
coefficient field K. Only the three constant complex cube roots act. No
algebraic closedness or point-surjectivity over K is assumed. The cubic
field-degree argument is the frozen generic quotient proof over this base. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

namespace M9.DeterminantTwistBaseChange

open MvPolynomial Module

abbrev Index := Fin 4 × Fin 4
abbrev CoordinateRing (K : Type*) [Field K] := MvPolynomial Index K
abbrev FunctionField (K : Type*) [Field K] := FractionRing (CoordinateRing K)

variable (K : Type*) [Field K] [Algebra ℂ K]

local notation "CR" => CoordinateRing K
local notation "FF" => FunctionField K

/-- The actual constant complex roots, embedded in the coefficient field. -/
def rootUnit : rootsOfUnity 3 ℂ →* Kˣ :=
  (Units.map (algebraMap ℂ K).toMonoidHom).comp (rootsOfUnity 3 ℂ).subtype

def polynomialMatrix : Matrix (Fin 4) (Fin 4) CR := fun i j => X (i,j)

def genericMatrix : DeterminantTwist.Mat4 FF :=
  (polynomialMatrix K).map (algebraMap CR FF)

def determinant : FF := (genericMatrix K).det

def twistedMatrix : DeterminantTwist.Mat4 FF :=
  DeterminantTwist.twist (genericMatrix K)

def twistedEntryField : IntermediateField K FF :=
  IntermediateField.adjoin K (Set.range fun ij : Index => (twistedMatrix K) ij.1 ij.2)

omit [Algebra ℂ K] in
theorem polynomial_det_ne_zero : (polynomialMatrix K).det ≠ 0 := by
  let ev : CR →ₐ[K] K := aeval (fun ij : Index => if ij.1 = ij.2 then 1 else 0)
  have hm : (polynomialMatrix K).map ev.toRingHom = 1 := by
    ext i j
    simp [polynomialMatrix, ev, Matrix.one_apply]
  intro h
  have he := ev.map_det (polynomialMatrix K)
  change ev (polynomialMatrix K).det = ((polynomialMatrix K).map ev.toRingHom).det at he
  rw [h, map_zero, hm, Matrix.det_one] at he
  exact zero_ne_one he

omit [Algebra ℂ K] in
theorem determinant_ne_zero : (determinant K) ≠ 0 := by
  have hm := (algebraMap CR FF).map_det (polynomialMatrix K)
  change algebraMap CR FF (polynomialMatrix K).det = (determinant K) at hm
  rw [← hm]
  simpa only [map_zero] using
    (IsFractionRing.injective CR FF).ne (polynomial_det_ne_zero K)

omit [Algebra ℂ K] in
theorem generic_entry_ne_zero (ij : Index) : (genericMatrix K) ij.1 ij.2 ≠ 0 := by
  change algebraMap CR FF (X ij) ≠ 0
  simpa only [map_zero] using (IsFractionRing.injective CR FF).ne (X_ne_zero ij)

omit [Algebra ℂ K] in
theorem generic_reconstruction (i j : Fin 4) :
    (genericMatrix K) i j = (determinant K) * (twistedMatrix K) i j := by
  have h := congrArg (fun M : DeterminantTwist.Mat4 FF => M i j)
    (DeterminantTwist.recover (genericMatrix K) (determinant_ne_zero K))
  exact h.symm

omit [Algebra ℂ K] in
theorem twisted_det_ne_zero : (twistedMatrix K).det ≠ 0 :=
  DeterminantTwist.det_twist_ne_zero (genericMatrix K) (determinant_ne_zero K)

omit [Algebra ℂ K] in
theorem determinant_cubic_equation : (determinant K)^3 * (twistedMatrix K).det = 1 :=
  DeterminantTwist.determinant_cover_equation (genericMatrix K) (determinant_ne_zero K)

omit [Algebra ℂ K] in
theorem twisted_entry_mem (ij : Index) : (twistedMatrix K) ij.1 ij.2 ∈ (twistedEntryField K) :=
  IntermediateField.subset_adjoin K _ ⟨ij,rfl⟩

def scalePolynomialMap (a : K) : CR →ₐ[K] CR :=
  aeval (fun ij : Index => C a * X ij)

omit [Algebra ℂ K] in
@[simp] theorem scalePolynomialMap_X (a : K) (ij : Index) :
    (scalePolynomialMap K) a (X ij) = C a * X ij := by simp [scalePolynomialMap]

omit [Algebra ℂ K] in
@[simp] theorem scalePolynomialMap_C (a c : K) :
    (scalePolynomialMap K) a (C c) = C c := by simp [scalePolynomialMap]


def scalePolynomial (a : Kˣ) : CR ≃ₐ[K] CR :=
  AlgEquiv.ofAlgHom ((scalePolynomialMap K) a.val) ((scalePolynomialMap K) (a⁻¹).val)
    (by
      ext ij : 1
      simp only [AlgHom.comp_apply, (scalePolynomialMap_X K), map_mul, (scalePolynomialMap_C K),
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext ij : 1
      simp only [AlgHom.comp_apply, (scalePolynomialMap_X K), map_mul, (scalePolynomialMap_C K),
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp)

omit [Algebra ℂ K] in
@[simp] theorem scalePolynomial_X (a : Kˣ) (ij : Index) :
    (scalePolynomial K) a (X ij) = C a.val * X ij := by
  exact (scalePolynomialMap_X K) a.val ij

omit [Algebra ℂ K] in
@[simp] theorem scalePolynomial_C (a : Kˣ) (c : K) :
    (scalePolynomial K) a (C c) = C c := by
  exact (scalePolynomialMap_C K) a.val c


def scale (a : Kˣ) : FF ≃ₐ[K] FF :=
  IsFractionRing.algEquivOfAlgEquiv ((scalePolynomial K) a)

omit [Algebra ℂ K] in
@[simp] theorem scale_polynomial (a : Kˣ) (P : CR) :
    (scale K) a (algebraMap CR FF P) =
      algebraMap CR FF ((scalePolynomial K) a P) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

omit [Algebra ℂ K] in
theorem scale_generic_entry (a : Kˣ) (ij : Index) :
    (scale K) a ((genericMatrix K) ij.1 ij.2) = algebraMap K FF a.val * (genericMatrix K) ij.1 ij.2 := by
  change (scale K) a (algebraMap CR FF (X ij)) = _
  rw [(scale_polynomial K), (scalePolynomial_X K), map_mul]
  rfl

omit [Algebra ℂ K] in
theorem scale_generic_matrix (a : Kˣ) :
    (genericMatrix K).map ((scale K) a).toRingHom = (algebraMap K FF a.val) • (genericMatrix K) := by
  ext i j
  exact (scale_generic_entry K) a (i,j)

omit [Algebra ℂ K] in
theorem scale_determinant (a : Kˣ) :
    (scale K) a (determinant K) = (algebraMap K FF a.val)^4 * (determinant K) := by
  rw [determinant, AlgEquiv.map_det]
  change ((genericMatrix K).map ((scale K) a).toRingHom).det = _
  rw [(scale_generic_matrix K), DeterminantTwist.det_smul_four]

omit [Algebra ℂ K] in
theorem scale_twisted_matrix (a : Kˣ) :
    (twistedMatrix K).map ((scale K) a).toRingHom =
      DeterminantTwist.twist ((algebraMap K FF a.val) • (genericMatrix K)) := by
  ext i j
  change (scale K) a ((determinant K)⁻¹ * (genericMatrix K) i j) = _
  rw [map_mul, map_inv₀, (scale_determinant K), DeterminantTwist.twist,
    DeterminantTwist.det_smul_four]
  rw [(scale_generic_entry K) a (i,j)]
  rfl

theorem cubeRoot_fixes_twisted_entry (a : rootsOfUnity 3 ℂ) (ij : Index) :
    (scale K) (rootUnit K a) ((twistedMatrix K) ij.1 ij.2) = (twistedMatrix K) ij.1 ij.2 := by
  have haK : ((rootUnit K a : Kˣ) : K)^3 = 1 := by
    change (algebraMap ℂ K (a.val : ℂ))^3 = 1
    rw [← map_pow, (mem_rootsOfUnity' 3 a.val).mp a.property, map_one]
  have ha : (algebraMap K FF ((rootUnit K a : Kˣ) : K))^3 = 1 := by
    rw [← map_pow, haK, map_one]
  have h := congrArg (fun M : DeterminantTwist.Mat4 FF => M ij.1 ij.2)
    ((scale_twisted_matrix K) (rootUnit K a))
  rw [DeterminantTwist.twist_smul_cubeRoot (genericMatrix K) (determinant_ne_zero K) _ ha] at h
  exact h

omit [Algebra ℂ K] in
theorem scalePolynomial_mul_apply (a b : Kˣ) (P : CR) :
    (scalePolynomial K) (a*b) P = (scalePolynomial K) a ((scalePolynomial K) b P) := by
  have hm : ((scalePolynomial K) a).toAlgHom.comp ((scalePolynomial K) b).toAlgHom =
      ((scalePolynomial K) (a*b)).toAlgHom := by
    ext ij : 1
    change (scalePolynomial K) a ((scalePolynomial K) b (X ij)) = (scalePolynomial K) (a*b) (X ij)
    simp only [(scalePolynomial_X K), map_mul, (scalePolynomial_C K), Units.val_mul]
    ring
  exact (congrArg (fun f : CR →ₐ[K] CR => f P) hm).symm

omit [Algebra ℂ K] in
theorem scalePolynomial_one_apply (P : CR) : (scalePolynomial K) 1 P = P := by
  have h : ((scalePolynomial K) 1).toAlgHom = AlgHom.id K CR := by
    ext ij : 1
    change (scalePolynomial K) 1 (X ij) = X ij
    simp only [(scalePolynomial_X K), Units.val_one, C_1, one_mul]
  exact congrArg (fun f : CR →ₐ[K] CR => f P) h

omit [Algebra ℂ K] in
theorem scale_mul (a b : Kˣ) : (scale K) (a*b) = (scale K) a * (scale K) b := by
  apply AlgEquiv.ext
  intro f
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CR f
  simp only [map_div₀, (scale_polynomial K), (scalePolynomial_mul_apply K), AlgEquiv.mul_apply]

omit [Algebra ℂ K] in
theorem scale_one : (scale K) 1 = (1 : FF ≃ₐ[K] FF) := by
  apply AlgEquiv.ext
  intro f
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CR f
  simp only [map_div₀, (scale_polynomial K), (scalePolynomial_one_apply K), AlgEquiv.one_apply]


def scalarAction : rootsOfUnity 3 ℂ →* (FF ≃ₐ[K] FF) where
  toFun a := (scale K) (rootUnit K a)
  map_one' := by rw [map_one]; exact scale_one K
  map_mul' a b := by rw [map_mul]; exact scale_mul K (rootUnit K a) (rootUnit K b)

theorem scalarAction_injective : Function.Injective (scalarAction K) := by
  intro a b h
  apply rootsOfUnity.coe_injective
  apply (algebraMap ℂ K).injective
  apply (algebraMap K FF).injective
  have he := congrArg (fun σ : FF ≃ₐ[K] FF => σ ((genericMatrix K) 0 0)) h
  change scale K (rootUnit K a) ((genericMatrix K) 0 0) = scale K (rootUnit K b) ((genericMatrix K) 0 0) at he
  rw [scale_generic_entry K (rootUnit K a) (0,0), scale_generic_entry K (rootUnit K b) (0,0)] at he
  exact mul_right_cancel₀ (generic_entry_ne_zero K (0,0)) he

def scalarSubgroup : Subgroup (FF ≃ₐ[K] FF) := (scalarAction K).range

instance finite_scalarSubgroup : Finite (scalarSubgroup K) := Finite.of_surjective (scalarAction K).rangeRestrict
  (scalarAction K).rangeRestrict_surjective

instance fintype_scalarSubgroup : Fintype (scalarSubgroup K) := Fintype.ofFinite (scalarSubgroup K)

theorem card_scalarSubgroup : Fintype.card (scalarSubgroup K) = 3 := by
  let e : rootsOfUnity 3 ℂ ≃ (scalarSubgroup K) :=
    Equiv.ofBijective (scalarAction K).rangeRestrict
      ⟨fun a b h => (scalarAction_injective K) (congrArg Subtype.val h),
        (scalarAction K).rangeRestrict_surjective⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
  exact Complex.card_rootsOfUnity 3

def scalarFixedField : IntermediateField K FF :=
  IntermediateField.fixedField (scalarSubgroup K)

theorem mem_scalarFixedField_iff (f : FF) :
    f ∈ (scalarFixedField K) ↔ ∀ a : rootsOfUnity 3 ℂ, (scale K) (rootUnit K a) f = f := by
  constructor
  · intro h a
    exact (IntermediateField.mem_fixedField_iff (scalarSubgroup K) f).mp h
      ((scalarAction K) a) ⟨a,rfl⟩
  · intro h
    apply (IntermediateField.mem_fixedField_iff (scalarSubgroup K) f).mpr
    rintro σ ⟨a,rfl⟩
    exact h a

theorem twistedEntryField_le_fixed : (twistedEntryField K) ≤ (scalarFixedField K) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨ij,hij⟩
  have hfix : (twistedMatrix K) ij.1 ij.2 ∈ IntermediateField.fixedField (scalarSubgroup K) := by
    apply (IntermediateField.mem_fixedField_iff (scalarSubgroup K) _).mpr
    rintro σ ⟨a,rfl⟩
    exact (cubeRoot_fixes_twisted_entry K) a ij
  exact hij ▸ hfix

theorem finrank_fixedField : finrank (scalarFixedField K) FF = 3 := by
  rw [← (card_scalarSubgroup K)]
  exact FixedPoints.finrank_eq_card (scalarSubgroup K) FF


omit [Algebra ℂ K] in
theorem eq_top_of_generic_entries (E : IntermediateField K FF)
    (hE : ∀ ij : Index, (genericMatrix K) ij.1 ij.2 ∈ E) : E = ⊤ := by
  have hpoly (P : CR) : algebraMap CR FF P ∈ E := by
    induction P using MvPolynomial.induction_on with
    | C c => exact E.algebraMap_mem c
    | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
    | mul_X P ij hP =>
      exact (map_mul (algebraMap CR FF) P (X ij)) ▸ E.mul_mem hP (hE ij)
  apply top_unique
  intro f _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CR f
  exact E.div_mem (hpoly p) (hpoly q)


omit [Algebra ℂ K] in
theorem adjoin_determinant_eq_top :
    IntermediateField.adjoin (twistedEntryField K) ({(determinant K)} : Set FF) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top]
  apply (eq_top_of_generic_entries K)
  intro ij
  rw [(generic_reconstruction K)]
  exact mul_mem (IntermediateField.mem_adjoin_simple_self (twistedEntryField K) (determinant K))
    (IntermediateField.algebraMap_mem _
      (⟨(twistedMatrix K) ij.1 ij.2, (twisted_entry_mem K) ij⟩ : (twistedEntryField K)))

omit [Algebra ℂ K] in
theorem twisted_det_mem : (twistedMatrix K).det ∈ (twistedEntryField K) := by
  rw [Matrix.det_apply]
  apply (twistedEntryField K).sum_mem
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply (twistedEntryField K).mul_mem
  · exact (twistedEntryField K).intCast_mem _
  · exact (twistedEntryField K).prod_mem fun i _ => (twisted_entry_mem K) (σ i,i)

omit [Algebra ℂ K] in
theorem determinant_cube_mem : (determinant K)^3 ∈ (twistedEntryField K) := by
  have he : (determinant K)^3 = (twistedMatrix K).det⁻¹ := by
    apply (mul_right_cancel₀ (twisted_det_ne_zero K))
    rw [(determinant_cubic_equation K), inv_mul_cancel₀ (twisted_det_ne_zero K)]
  rw [he]
  exact (twistedEntryField K).inv_mem (twisted_det_mem K)

def determinantCube : (twistedEntryField K) := ⟨(determinant K)^3, (determinant_cube_mem K)⟩

def cubicPolynomial : Polynomial (twistedEntryField K) := Polynomial.X^3 - Polynomial.C (determinantCube K)

omit [Algebra ℂ K] in
theorem cubicPolynomial_monic : (cubicPolynomial K).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0)

omit [Algebra ℂ K] in
theorem cubicPolynomial_vanishes : Polynomial.aeval (determinant K) (cubicPolynomial K) = 0 := by
  simp [cubicPolynomial, determinantCube]

omit [Algebra ℂ K] in
theorem determinant_integral : IsIntegral (twistedEntryField K) (determinant K) :=
  ⟨(cubicPolynomial K), (cubicPolynomial_monic K), (cubicPolynomial_vanishes K)⟩


def determinantPowerBasis : PowerBasis (twistedEntryField K) FF :=
  PowerBasis.ofAdjoinSimpleEqTop (determinant_integral K) (adjoin_determinant_eq_top K)

instance finiteDimensional_twistedEntryField : FiniteDimensional (twistedEntryField K) FF :=
  (determinantPowerBasis K).finite

omit [Algebra ℂ K] in
theorem finrank_entryField_le_three : finrank (twistedEntryField K) FF ≤ 3 := by
  rw [(determinantPowerBasis K).finrank]
  change (minpoly (twistedEntryField K) (determinant K)).natDegree ≤ 3
  have h := Polynomial.natDegree_le_of_dvd
    (minpoly.dvd (twistedEntryField K) (determinant K) (cubicPolynomial_vanishes K)) (cubicPolynomial_monic K).ne_zero
  simpa only [cubicPolynomial, Polynomial.natDegree_X_pow_sub_C] using h


theorem fixedField_eq_twistedEntryField : (scalarFixedField K) = (twistedEntryField K) := by
  apply (IntermediateField.eq_of_le_of_finrank_le' (twistedEntryField_le_fixed K) _).symm
  rw [(finrank_fixedField K)]
  exact (finrank_entryField_le_three K)

theorem finrank_entryField : finrank (twistedEntryField K) FF = 3 := by
  rw [← (fixedField_eq_twistedEntryField K)]
  exact (finrank_fixedField K)

theorem determinantPowerBasis_dim : (determinantPowerBasis K).dim = 3 := by
  rw [← (determinantPowerBasis K).finrank]
  exact (finrank_entryField K)


def cubicBasis : Basis (Fin 3) (twistedEntryField K) FF :=
  (determinantPowerBasis K).basis.reindex (finCongr (determinantPowerBasis_dim K))

theorem cubicBasis_apply (i : Fin 3) : (cubicBasis K) i = (determinant K)^i.val := by
  rw [cubicBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp [determinantPowerBasis]

theorem scalar_invariant_iff_mem_twistedEntryField (f : FF) :
    (∀ a : rootsOfUnity 3 ℂ, (scale K) (rootUnit K a) f = f) ↔ f ∈ (twistedEntryField K) := by
  rw [← (fixedField_eq_twistedEntryField K)]
  exact ((mem_scalarFixedField_iff K) f).symm

omit [Algebra ℂ K] in
theorem generic_entries_independent :
    AlgebraicIndependent K (fun ij : Index => (genericMatrix K) ij.1 ij.2) := by
  exact (MvPolynomial.algebraicIndependent_X Index K).map'
    (f := IsScalarTower.toAlgHom K CR FF)
      (IsFractionRing.injective CR FF)

open scoped IntermediateField.algebraAdjoinAdjoin

omit [Algebra ℂ K] in
theorem twisted_entries_algebraically_spanning :
    Algebra.IsAlgebraic
      (Algebra.adjoin K (Set.range fun ij : Index => (twistedMatrix K) ij.1 ij.2)) FF := by
  let : Algebra.IsAlgebraic
      (IntermediateField.adjoin K (Set.range fun ij : Index => (twistedMatrix K) ij.1 ij.2)) FF := by
    change Algebra.IsAlgebraic (twistedEntryField K) FF
    exact Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.trans _
    (IntermediateField.adjoin K (Set.range fun ij : Index => (twistedMatrix K) ij.1 ij.2)) _


omit [Algebra ℂ K] in
theorem twisted_entries_transcendenceBasis :
    IsTranscendenceBasis K (fun ij : Index => (twistedMatrix K) ij.1 ij.2) := by
  let := (twisted_entries_algebraically_spanning K)
  exact Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K _
    (generic_entries_independent K).lift_cardinalMk_le_trdeg

omit [Algebra ℂ K] in
theorem twisted_entries_independent :
    AlgebraicIndependent K (fun ij : Index => (twistedMatrix K) ij.1 ij.2) :=
  (twisted_entries_transcendenceBasis K).1


def quotientCoordinateEquiv : FF ≃ₐ[K] (scalarFixedField K) :=
  (twisted_entries_independent K).aevalEquivField.trans
    (IntermediateField.equivOfEq (fixedField_eq_twistedEntryField K).symm)

theorem quotientCoordinateEquiv_coordinate (ij : Index) :
    ((quotientCoordinateEquiv K) (algebraMap CR FF (X ij)) : FF) =
      (twistedMatrix K) ij.1 ij.2 := by
  change ((twisted_entries_independent K).aevalEquivField
    (algebraMap CR FF (X ij)) : FF) = _
  rw [(twisted_entries_independent K).aevalEquivField_algebraMap_apply_coe]
  simp

def indexEquivFin : Index ≃ Fin 16 :=
  (Fintype.equivFin Index).trans (finCongr (by decide))

def fractionCoordinates16 : FF ≃ₐ[K] M9.RationalField K 16 :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K indexEquivFin)

def fixedFieldRationalEquiv : (scalarFixedField K) ≃ₐ[K] M9.RationalField K 16 :=
  (quotientCoordinateEquiv K).symm.trans (fractionCoordinates16 K)

theorem fixedField_rational : M9.RationalOfDimension K (scalarFixedField K) 16 :=
  ⟨(fixedFieldRationalEquiv K)⟩


section BaseChange

variable {K' : Type*} [Field K'] [Algebra ℂ K']

/-- Coefficient base change on the actual polynomial matrix coordinate ring. -/
def polynomialBaseChange (φ : K →ₐ[ℂ] K') :
    CoordinateRing K →ₐ[ℂ] CoordinateRing K' :=
  MvPolynomial.mapAlgHom φ

def polynomialIntoTarget (φ : K →ₐ[ℂ] K') :
    CoordinateRing K →ₐ[ℂ] FunctionField K' :=
  (IsScalarTower.toAlgHom ℂ (CoordinateRing K') (FunctionField K')).comp
    (polynomialBaseChange K φ)

theorem polynomialIntoTarget_injective (φ : K →ₐ[ℂ] K') :
    Function.Injective (polynomialIntoTarget K φ) := by
  change Function.Injective (fun p : CoordinateRing K =>
    algebraMap (CoordinateRing K') (FunctionField K') (MvPolynomial.map φ p))
  exact (IsFractionRing.injective (CoordinateRing K') (FunctionField K')).comp
    (MvPolynomial.map_injective φ.toRingHom φ.injective)

/-- The actual coefficient base-change embedding of generic matrix fields. -/
def baseChangeEmbedding (φ : K →ₐ[ℂ] K') :
    FunctionField K →ₐ[ℂ] FunctionField K' :=
  IsFractionRing.liftAlgHom (g := polynomialIntoTarget K φ)
    (polynomialIntoTarget_injective K φ)

@[simp] theorem baseChangeEmbedding_polynomial (φ : K →ₐ[ℂ] K') (p : CoordinateRing K) :
    baseChangeEmbedding K φ (algebraMap (CoordinateRing K) (FunctionField K) p) =
      algebraMap (CoordinateRing K') (FunctionField K') (MvPolynomial.map φ p) := by
  rw [baseChangeEmbedding, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem baseChangeEmbedding_constant (φ : K →ₐ[ℂ] K') (a : K) :
    baseChangeEmbedding K φ (algebraMap K (FunctionField K) a) =
      algebraMap K' (FunctionField K') (φ a) := by
  change baseChangeEmbedding K φ
    (algebraMap (CoordinateRing K) (FunctionField K) (MvPolynomial.C a)) = _
  rw [baseChangeEmbedding_polynomial, MvPolynomial.map_C]
  rfl

theorem baseChangeEmbedding_generic (φ : K →ₐ[ℂ] K') (ij : Index) :
    baseChangeEmbedding K φ (genericMatrix K ij.1 ij.2) = genericMatrix K' ij.1 ij.2 := by
  change baseChangeEmbedding K φ
    (algebraMap (CoordinateRing K) (FunctionField K) (MvPolynomial.X ij)) = _
  rw [baseChangeEmbedding_polynomial, MvPolynomial.map_X]
  rfl

theorem baseChangeEmbedding_generic_matrix (φ : K →ₐ[ℂ] K') :
    (genericMatrix K).map (baseChangeEmbedding K φ).toRingHom = genericMatrix K' := by
  ext i j
  exact baseChangeEmbedding_generic K φ (i,j)

theorem baseChangeEmbedding_determinant (φ : K →ₐ[ℂ] K') :
    baseChangeEmbedding K φ (determinant K) = determinant K' := by
  rw [determinant, AlgHom.map_det]
  exact congrArg Matrix.det (baseChangeEmbedding_generic_matrix K φ)

/-- The determinant twist commutes with coefficient base change. -/
theorem baseChangeEmbedding_twisted (φ : K →ₐ[ℂ] K') (ij : Index) :
    baseChangeEmbedding K φ (twistedMatrix K ij.1 ij.2) = twistedMatrix K' ij.1 ij.2 := by
  change baseChangeEmbedding K φ
    ((determinant K)⁻¹ * genericMatrix K ij.1 ij.2) =
      (determinant K')⁻¹ * genericMatrix K' ij.1 ij.2
  rw [map_mul, map_inv₀, baseChangeEmbedding_determinant, baseChangeEmbedding_generic]

/-- The constant complex scalar action commutes with base change on every
rational function, rather than only on polynomial coordinates. -/
theorem baseChangeEmbedding_scalar (φ : K →ₐ[ℂ] K') (a : rootsOfUnity 3 ℂ) (f : FunctionField K) :
    baseChangeEmbedding K φ (scalarAction K a f) =
      scalarAction K' a (baseChangeEmbedding K φ f) := by
  have heq :
      (baseChangeEmbedding K φ).toRingHom.comp (scalarAction K a).toRingHom =
        (scalarAction K' a).toRingHom.comp (baseChangeEmbedding K φ).toRingHom := by
    apply M9.CayleyFixedField.rationalHom_ext K
    · intro b
      change baseChangeEmbedding K φ (scalarAction K a (algebraMap K (FunctionField K) b)) =
        scalarAction K' a (baseChangeEmbedding K φ (algebraMap K (FunctionField K) b))
      rw [(scalarAction K a).commutes, baseChangeEmbedding_constant, (scalarAction K' a).commutes]
    · rintro ⟨i,j⟩
      change baseChangeEmbedding K φ
        (scale K (rootUnit K a) (genericMatrix K i j)) =
          scale K' (rootUnit K' a) (baseChangeEmbedding K φ (genericMatrix K i j))
      rw [scale_generic_entry K (rootUnit K a) (i,j), map_mul, baseChangeEmbedding_constant,
        baseChangeEmbedding_generic K φ (i,j), scale_generic_entry K' (rootUnit K' a) (i,j)]
      have hroot : φ ((rootUnit K a : Kˣ) : K) = ((rootUnit K' a : K'ˣ) : K') := by
        change φ (algebraMap ℂ K (a.val : ℂ)) = algebraMap ℂ K' (a.val : ℂ)
        exact φ.commutes _
      rw [hroot]
  exact congrArg (fun g : FunctionField K →+* FunctionField K' => g f) heq

/-- Base change sends actual scalar invariants to actual scalar invariants. -/
theorem baseChangeEmbedding_mem_fixed (φ : K →ₐ[ℂ] K') {f : FunctionField K}
    (hf : f ∈ scalarFixedField K) :
    baseChangeEmbedding K φ f ∈ scalarFixedField K' := by
  apply (mem_scalarFixedField_iff K' _).mpr
  intro a
  change scalarAction K' a (baseChangeEmbedding K φ f) = _
  rw [← baseChangeEmbedding_scalar K φ a f]
  exact congrArg (baseChangeEmbedding K φ) ((mem_scalarFixedField_iff K f).mp hf a)

/-- The actual scalar fixed field after base change is generated over the
new coefficient field by the image of the original scalar fixed field. -/
theorem scalarFixedField_baseChange (φ : K →ₐ[ℂ] K') :
    IntermediateField.adjoin K'
        (Set.range fun f : scalarFixedField K => baseChangeEmbedding K φ f.val) =
      scalarFixedField K' := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨f,rfl⟩
    exact baseChangeEmbedding_mem_fixed K φ f.property
  · rw [fixedField_eq_twistedEntryField]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ij,rfl⟩
    apply IntermediateField.subset_adjoin K'
    refine ⟨⟨twistedMatrix K ij.1 ij.2,
      twistedEntryField_le_fixed K (twisted_entry_mem K ij)⟩,?_⟩
    exact baseChangeEmbedding_twisted K φ ij

end BaseChange

/-- The general construction specializes to the frozen complex fixed field. -/
theorem complex_fixedField_eq :
    scalarFixedField ℂ = M9.DeterminantTwistField.scalarFixedField := by
  rw [fixedField_eq_twistedEntryField, M9.DeterminantTwistField.fixedField_eq_twistedEntryField]
  rfl

end M9.DeterminantTwistBaseChange
