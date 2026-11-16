module

public import M9.DeterminantTwist
public import M9.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The genuine cubic scalar fixed field of the generic determinant twist

The ambient field is the fraction field of the polynomial ring in the
sixteen actual matrix entries. All scalar actions below are extensions of
the coordinate substitutions `Xᵢⱼ ↦ a Xᵢⱼ` to this fraction field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

namespace M9.DeterminantTwistField

open MvPolynomial Module

abbrev Index := Fin 4 × Fin 4
abbrev CoordinateRing := MvPolynomial Index ℂ
abbrev FunctionField := FractionRing CoordinateRing

def polynomialMatrix : Matrix (Fin 4) (Fin 4) CoordinateRing := fun i j => X (i,j)

def genericMatrix : DeterminantTwist.Mat4 FunctionField :=
  polynomialMatrix.map (algebraMap CoordinateRing FunctionField)

def determinant : FunctionField := genericMatrix.det

def twistedMatrix : DeterminantTwist.Mat4 FunctionField :=
  DeterminantTwist.twist genericMatrix

def twistedEntryField : IntermediateField ℂ FunctionField :=
  IntermediateField.adjoin ℂ (Set.range fun ij : Index => twistedMatrix ij.1 ij.2)

theorem polynomial_det_ne_zero : polynomialMatrix.det ≠ 0 := by
  let ev : CoordinateRing →ₐ[ℂ] ℂ := aeval (fun ij : Index => if ij.1 = ij.2 then 1 else 0)
  have hm : polynomialMatrix.map ev.toRingHom = 1 := by
    ext i j
    simp [polynomialMatrix, ev, Matrix.one_apply]
  intro h
  have he := ev.map_det polynomialMatrix
  change ev polynomialMatrix.det = (polynomialMatrix.map ev.toRingHom).det at he
  rw [h, map_zero, hm, Matrix.det_one] at he
  exact zero_ne_one he

theorem determinant_ne_zero : determinant ≠ 0 := by
  have hm := (algebraMap CoordinateRing FunctionField).map_det polynomialMatrix
  change algebraMap CoordinateRing FunctionField polynomialMatrix.det = determinant at hm
  rw [← hm]
  simpa only [map_zero] using
    (IsFractionRing.injective CoordinateRing FunctionField).ne polynomial_det_ne_zero

theorem generic_entry_ne_zero (ij : Index) : genericMatrix ij.1 ij.2 ≠ 0 := by
  change algebraMap CoordinateRing FunctionField (X ij) ≠ 0
  simpa only [map_zero] using (IsFractionRing.injective CoordinateRing FunctionField).ne (X_ne_zero ij)

theorem generic_reconstruction (i j : Fin 4) :
    genericMatrix i j = determinant * twistedMatrix i j := by
  have h := congrArg (fun M : DeterminantTwist.Mat4 FunctionField => M i j)
    (DeterminantTwist.recover genericMatrix determinant_ne_zero)
  exact h.symm

theorem twisted_det_ne_zero : twistedMatrix.det ≠ 0 :=
  DeterminantTwist.det_twist_ne_zero genericMatrix determinant_ne_zero

theorem determinant_cubic_equation : determinant^3 * twistedMatrix.det = 1 :=
  DeterminantTwist.determinant_cover_equation genericMatrix determinant_ne_zero

theorem twisted_entry_mem (ij : Index) : twistedMatrix ij.1 ij.2 ∈ twistedEntryField :=
  IntermediateField.subset_adjoin ℂ _ ⟨ij,rfl⟩

def scalePolynomialMap (a : ℂ) : CoordinateRing →ₐ[ℂ] CoordinateRing :=
  aeval (fun ij : Index => C a * X ij)

@[simp] theorem scalePolynomialMap_X (a : ℂ) (ij : Index) :
    scalePolynomialMap a (X ij) = C a * X ij := by simp [scalePolynomialMap]

@[simp] theorem scalePolynomialMap_C (a c : ℂ) :
    scalePolynomialMap a (C c) = C c := by simp [scalePolynomialMap]

/-- Scalar multiplication is an actual automorphism of the coordinate ring. -/
def scalePolynomial (a : ℂˣ) : CoordinateRing ≃ₐ[ℂ] CoordinateRing :=
  AlgEquiv.ofAlgHom (scalePolynomialMap a.val) (scalePolynomialMap (a⁻¹).val)
    (by
      ext ij : 1
      simp only [AlgHom.comp_apply, scalePolynomialMap_X, map_mul, scalePolynomialMap_C,
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext ij : 1
      simp only [AlgHom.comp_apply, scalePolynomialMap_X, map_mul, scalePolynomialMap_C,
        AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp)

@[simp] theorem scalePolynomial_X (a : ℂˣ) (ij : Index) :
    scalePolynomial a (X ij) = C a.val * X ij := by
  exact scalePolynomialMap_X a.val ij

@[simp] theorem scalePolynomial_C (a : ℂˣ) (c : ℂ) :
    scalePolynomial a (C c) = C c := by
  exact scalePolynomialMap_C a.val c

/-- Extend the coordinate automorphism to the actual fraction field. -/
def scale (a : ℂˣ) : FunctionField ≃ₐ[ℂ] FunctionField :=
  IsFractionRing.algEquivOfAlgEquiv (scalePolynomial a)

@[simp] theorem scale_polynomial (a : ℂˣ) (P : CoordinateRing) :
    scale a (algebraMap CoordinateRing FunctionField P) =
      algebraMap CoordinateRing FunctionField (scalePolynomial a P) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

theorem scale_generic_entry (a : ℂˣ) (ij : Index) :
    scale a (genericMatrix ij.1 ij.2) = algebraMap ℂ FunctionField a.val * genericMatrix ij.1 ij.2 := by
  change scale a (algebraMap CoordinateRing FunctionField (X ij)) = _
  rw [scale_polynomial, scalePolynomial_X, map_mul]
  rfl

theorem scale_generic_matrix (a : ℂˣ) :
    genericMatrix.map (scale a).toRingHom = (algebraMap ℂ FunctionField a.val) • genericMatrix := by
  ext i j
  exact scale_generic_entry a (i,j)

theorem scale_determinant (a : ℂˣ) :
    scale a determinant = (algebraMap ℂ FunctionField a.val)^4 * determinant := by
  rw [determinant, AlgEquiv.map_det]
  change (genericMatrix.map (scale a).toRingHom).det = _
  rw [scale_generic_matrix, DeterminantTwist.det_smul_four]

theorem scale_twisted_matrix (a : ℂˣ) :
    twistedMatrix.map (scale a).toRingHom =
      DeterminantTwist.twist ((algebraMap ℂ FunctionField a.val) • genericMatrix) := by
  ext i j
  change scale a (determinant⁻¹ * genericMatrix i j) = _
  rw [map_mul, map_inv₀, scale_determinant, DeterminantTwist.twist,
    DeterminantTwist.det_smul_four]
  rw [scale_generic_entry a (i,j)]
  rfl

theorem cubeRoot_fixes_twisted_entry (a : rootsOfUnity 3 ℂ) (ij : Index) :
    scale a.val (twistedMatrix ij.1 ij.2) = twistedMatrix ij.1 ij.2 := by
  have ha : (algebraMap ℂ FunctionField (a.val : ℂ))^3 = 1 := by
    rw [← map_pow, (mem_rootsOfUnity' 3 a.val).mp a.property, map_one]
  have h := congrArg (fun M : DeterminantTwist.Mat4 FunctionField => M ij.1 ij.2)
    (scale_twisted_matrix a.val)
  rw [DeterminantTwist.twist_smul_cubeRoot genericMatrix determinant_ne_zero _ ha] at h
  exact h

theorem scalePolynomial_mul_apply (a b : ℂˣ) (P : CoordinateRing) :
    scalePolynomial (a*b) P = scalePolynomial a (scalePolynomial b P) := by
  have hm : (scalePolynomial a).toAlgHom.comp (scalePolynomial b).toAlgHom =
      (scalePolynomial (a*b)).toAlgHom := by
    ext ij : 1
    change scalePolynomial a (scalePolynomial b (X ij)) = scalePolynomial (a*b) (X ij)
    simp only [scalePolynomial_X, map_mul, scalePolynomial_C, Units.val_mul]
    ring
  exact (congrArg (fun f : CoordinateRing →ₐ[ℂ] CoordinateRing => f P) hm).symm

theorem scalePolynomial_one_apply (P : CoordinateRing) : scalePolynomial 1 P = P := by
  have h : (scalePolynomial 1).toAlgHom = AlgHom.id ℂ CoordinateRing := by
    ext ij : 1
    change scalePolynomial 1 (X ij) = X ij
    simp only [scalePolynomial_X, Units.val_one, C_1, one_mul]
  exact congrArg (fun f : CoordinateRing →ₐ[ℂ] CoordinateRing => f P) h

theorem scale_mul (a b : ℂˣ) : scale (a*b) = scale a * scale b := by
  apply AlgEquiv.ext
  intro f
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CoordinateRing f
  simp only [map_div₀, scale_polynomial, scalePolynomial_mul_apply, AlgEquiv.mul_apply]

theorem scale_one : scale 1 = (1 : FunctionField ≃ₐ[ℂ] FunctionField) := by
  apply AlgEquiv.ext
  intro f
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CoordinateRing f
  simp only [map_div₀, scale_polynomial, scalePolynomial_one_apply, AlgEquiv.one_apply]

/-- The genuine scalar `μ₃` action on the generic matrix fraction field. -/
def scalarAction : rootsOfUnity 3 ℂ →* (FunctionField ≃ₐ[ℂ] FunctionField) where
  toFun a := scale a.val
  map_one' := scale_one
  map_mul' a b := scale_mul a.val b.val

theorem scalarAction_injective : Function.Injective scalarAction := by
  intro a b h
  apply rootsOfUnity.coe_injective
  have he := congrArg (fun σ : FunctionField ≃ₐ[ℂ] FunctionField => σ (genericMatrix 0 0)) h
  change scale a.val (genericMatrix 0 0) = scale b.val (genericMatrix 0 0) at he
  rw [scale_generic_entry a.val (0,0), scale_generic_entry b.val (0,0)] at he
  exact (algebraMap ℂ FunctionField).injective
    (mul_right_cancel₀ (generic_entry_ne_zero (0,0)) he)

def scalarSubgroup : Subgroup (FunctionField ≃ₐ[ℂ] FunctionField) := scalarAction.range

instance finite_scalarSubgroup : Finite scalarSubgroup := Finite.of_surjective scalarAction.rangeRestrict
  scalarAction.rangeRestrict_surjective

instance fintype_scalarSubgroup : Fintype scalarSubgroup := Fintype.ofFinite scalarSubgroup

theorem card_scalarSubgroup : Fintype.card scalarSubgroup = 3 := by
  let e : rootsOfUnity 3 ℂ ≃ scalarSubgroup :=
    Equiv.ofBijective scalarAction.rangeRestrict
      ⟨fun a b h => scalarAction_injective (congrArg Subtype.val h),
        scalarAction.rangeRestrict_surjective⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
  exact Complex.card_rootsOfUnity 3

def scalarFixedField : IntermediateField ℂ FunctionField :=
  IntermediateField.fixedField scalarSubgroup

theorem mem_scalarFixedField_iff (f : FunctionField) :
    f ∈ scalarFixedField ↔ ∀ a : rootsOfUnity 3 ℂ, scale a.val f = f := by
  constructor
  · intro h a
    exact (IntermediateField.mem_fixedField_iff scalarSubgroup f).mp h
      (scalarAction a) ⟨a,rfl⟩
  · intro h
    apply (IntermediateField.mem_fixedField_iff scalarSubgroup f).mpr
    rintro σ ⟨a,rfl⟩
    exact h a

theorem twistedEntryField_le_fixed : twistedEntryField ≤ scalarFixedField := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨ij,hij⟩
  have hfix : twistedMatrix ij.1 ij.2 ∈ IntermediateField.fixedField scalarSubgroup := by
    apply (IntermediateField.mem_fixedField_iff scalarSubgroup _).mpr
    rintro σ ⟨a,rfl⟩
    exact cubeRoot_fixes_twisted_entry a ij
  exact hij ▸ hfix

theorem finrank_fixedField : finrank scalarFixedField FunctionField = 3 := by
  rw [← card_scalarSubgroup]
  exact FixedPoints.finrank_eq_card scalarSubgroup FunctionField

/-- Every intermediate field containing the sixteen actual coordinates
contains the whole rational function field. -/
theorem eq_top_of_generic_entries (E : IntermediateField ℂ FunctionField)
    (hE : ∀ ij : Index, genericMatrix ij.1 ij.2 ∈ E) : E = ⊤ := by
  have hpoly (P : CoordinateRing) : algebraMap CoordinateRing FunctionField P ∈ E := by
    induction P using MvPolynomial.induction_on with
    | C c => exact E.algebraMap_mem c
    | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
    | mul_X P ij hP =>
      exact (map_mul (algebraMap CoordinateRing FunctionField) P (X ij)) ▸ E.mul_mem hP (hE ij)
  apply top_unique
  intro f _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective CoordinateRing f
  exact E.div_mem (hpoly p) (hpoly q)

/-- Reconstruction proves that adjoining just the determinant to the actual
twisted-entry field recovers every original rational coordinate. -/
theorem adjoin_determinant_eq_top :
    IntermediateField.adjoin twistedEntryField ({determinant} : Set FunctionField) = ⊤ := by
  apply IntermediateField.restrictScalars_injective ℂ
  rw [IntermediateField.restrictScalars_top]
  apply eq_top_of_generic_entries
  intro ij
  rw [generic_reconstruction]
  exact mul_mem (IntermediateField.mem_adjoin_simple_self twistedEntryField determinant)
    (IntermediateField.algebraMap_mem _
      (⟨twistedMatrix ij.1 ij.2, twisted_entry_mem ij⟩ : twistedEntryField))

theorem twisted_det_mem : twistedMatrix.det ∈ twistedEntryField := by
  rw [Matrix.det_apply]
  apply twistedEntryField.sum_mem
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply twistedEntryField.mul_mem
  · exact twistedEntryField.intCast_mem _
  · exact twistedEntryField.prod_mem fun i _ => twisted_entry_mem (σ i,i)

theorem determinant_cube_mem : determinant^3 ∈ twistedEntryField := by
  have he : determinant^3 = twistedMatrix.det⁻¹ := by
    apply (mul_right_cancel₀ twisted_det_ne_zero)
    rw [determinant_cubic_equation, inv_mul_cancel₀ twisted_det_ne_zero]
  rw [he]
  exact twistedEntryField.inv_mem twisted_det_mem

def determinantCube : twistedEntryField := ⟨determinant^3, determinant_cube_mem⟩

def cubicPolynomial : Polynomial twistedEntryField := Polynomial.X^3 - Polynomial.C determinantCube

theorem cubicPolynomial_monic : cubicPolynomial.Monic :=
  Polynomial.monic_X_pow_sub_C _ (by decide : 3 ≠ 0)

theorem cubicPolynomial_vanishes : Polynomial.aeval determinant cubicPolynomial = 0 := by
  simp [cubicPolynomial, determinantCube]

theorem determinant_integral : IsIntegral twistedEntryField determinant :=
  ⟨cubicPolynomial, cubicPolynomial_monic, cubicPolynomial_vanishes⟩

/-- A power basis of the full rational function field over the twisted-entry
field, constructed from the actual determinant and its cubic equation. -/
def determinantPowerBasis : PowerBasis twistedEntryField FunctionField :=
  PowerBasis.ofAdjoinSimpleEqTop determinant_integral adjoin_determinant_eq_top

instance finiteDimensional_twistedEntryField : FiniteDimensional twistedEntryField FunctionField :=
  determinantPowerBasis.finite

theorem finrank_entryField_le_three : finrank twistedEntryField FunctionField ≤ 3 := by
  rw [determinantPowerBasis.finrank]
  change (minpoly twistedEntryField determinant).natDegree ≤ 3
  have h := Polynomial.natDegree_le_of_dvd
    (minpoly.dvd twistedEntryField determinant cubicPolynomial_vanishes) cubicPolynomial_monic.ne_zero
  simpa only [cubicPolynomial, Polynomial.natDegree_X_pow_sub_C] using h

/-- The fixed field of the genuine scalar `μ₃` action is exactly the field
generated by the sixteen actual entries `Xᵢⱼ / det X`. -/
theorem fixedField_eq_twistedEntryField : scalarFixedField = twistedEntryField := by
  apply (IntermediateField.eq_of_le_of_finrank_le' twistedEntryField_le_fixed _).symm
  rw [finrank_fixedField]
  exact finrank_entryField_le_three

theorem finrank_entryField : finrank twistedEntryField FunctionField = 3 := by
  rw [← fixedField_eq_twistedEntryField]
  exact finrank_fixedField

theorem determinantPowerBasis_dim : determinantPowerBasis.dim = 3 := by
  rw [← determinantPowerBasis.finrank]
  exact finrank_entryField

/-- The actual cubic basis is `1, det X, (det X)²`. -/
def cubicBasis : Basis (Fin 3) twistedEntryField FunctionField :=
  determinantPowerBasis.basis.reindex (finCongr determinantPowerBasis_dim)

theorem cubicBasis_apply (i : Fin 3) : cubicBasis i = determinant^i.val := by
  rw [cubicBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp [determinantPowerBasis]

theorem scalar_invariant_iff_mem_twistedEntryField (f : FunctionField) :
    (∀ a : rootsOfUnity 3 ℂ, scale a.val f = f) ↔ f ∈ twistedEntryField := by
  rw [← fixedField_eq_twistedEntryField]
  exact (mem_scalarFixedField_iff f).symm

theorem generic_entries_independent :
    AlgebraicIndependent ℂ (fun ij : Index => genericMatrix ij.1 ij.2) := by
  exact (MvPolynomial.algebraicIndependent_X Index ℂ).map'
    (f := IsScalarTower.toAlgHom ℂ CoordinateRing FunctionField)
      (IsFractionRing.injective CoordinateRing FunctionField)

open scoped IntermediateField.algebraAdjoinAdjoin

theorem twisted_entries_algebraically_spanning :
    Algebra.IsAlgebraic
      (Algebra.adjoin ℂ (Set.range fun ij : Index => twistedMatrix ij.1 ij.2)) FunctionField := by
  let : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ (Set.range fun ij : Index => twistedMatrix ij.1 ij.2)) FunctionField := by
    change Algebra.IsAlgebraic twistedEntryField FunctionField
    exact Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.trans _
    (IntermediateField.adjoin ℂ (Set.range fun ij : Index => twistedMatrix ij.1 ij.2)) _

/-- The sixteen literal twisted entries are a transcendence basis. Their
independence follows from the proved cubic algebraicity and the original
sixteen independent polynomial coordinates. -/
theorem twisted_entries_transcendenceBasis :
    IsTranscendenceBasis ℂ (fun ij : Index => twistedMatrix ij.1 ij.2) := by
  let := twisted_entries_algebraically_spanning
  exact Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ _
    generic_entries_independent.cardinalMk_le_trdeg

theorem twisted_entries_independent :
    AlgebraicIndependent ℂ (fun ij : Index => twistedMatrix ij.1 ij.2) :=
  twisted_entries_transcendenceBasis.1

/-- The actual coordinate-field quotient map is an isomorphism onto the
actual fixed field, sending every original variable to the corresponding
entry of `X / det X`. -/
def quotientCoordinateEquiv : FunctionField ≃ₐ[ℂ] scalarFixedField :=
  twisted_entries_independent.aevalEquivField.trans
    (IntermediateField.equivOfEq fixedField_eq_twistedEntryField.symm)

theorem quotientCoordinateEquiv_coordinate (ij : Index) :
    (quotientCoordinateEquiv (algebraMap CoordinateRing FunctionField (X ij)) : FunctionField) =
      twistedMatrix ij.1 ij.2 := by
  change (twisted_entries_independent.aevalEquivField
    (algebraMap CoordinateRing FunctionField (X ij)) : FunctionField) = _
  rw [twisted_entries_independent.aevalEquivField_algebraMap_apply_coe]
  simp

def indexEquivFin : Index ≃ Fin 16 :=
  (Fintype.equivFin Index).trans (finCongr (by decide))

def fractionCoordinates16 : FunctionField ≃ₐ[ℂ] M9.RationalField ℂ 16 :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv ℂ indexEquivFin)

def fixedFieldRationalEquiv : scalarFixedField ≃ₐ[ℂ] M9.RationalField ℂ 16 :=
  quotientCoordinateEquiv.symm.trans fractionCoordinates16

theorem fixedField_rational : M9.RationalOfDimension ℂ scalarFixedField 16 :=
  ⟨fixedFieldRationalEquiv⟩

end M9.DeterminantTwistField
