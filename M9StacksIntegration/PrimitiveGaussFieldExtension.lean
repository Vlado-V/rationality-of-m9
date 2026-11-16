module

public import M9StacksIntegration.PrimitiveGaussCoordinates
public import M9StacksIntegration.GenericEtaleFibreDegree
public import Mathlib.FieldTheory.IntermediateField.Basic

/-! The actual thirteen-parameter Gauss field is algebraic over its literal orbit-coordinate
field. This follows from the proved coordinate independence and the two actual trdeg13 facts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace M9Native.PrimitiveGaussFieldExtension

open PrimitiveGaussCoordinates

/-- Distinct variable names keep the orbit-coordinate algebra separate from the parameter algebra. -/
abbrev targetPolynomial : Type := MvPolynomial (ULift.{0} (Fin 13)) ℂ
abbrev targetField : Type := FractionRing targetPolynomial
abbrev parameterField : Type := rationalField ℂ

def coordinateMap : targetPolynomial →ₐ[ℂ] parameterField :=
  MvPolynomial.aeval (fun i => coordinate ℂ i.down)

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  (coordinate_algebraicIndependent ℂ).comp ULift.down ULift.down_injective

def targetEmbedding : targetField →ₐ[ℂ] parameterField :=
  IsFractionRing.liftAlgHom coordinateMap_injective

@[simp] theorem targetEmbedding_algebraMap (p : targetPolynomial) :
    targetEmbedding (algebraMap targetPolynomial targetField p) = coordinateMap p :=
  IsFractionRing.lift_algebraMap coordinateMap_injective p

instance targetAlgebra : Algebra targetField parameterField := targetEmbedding.toRingHom.toAlgebra

instance targetTower : IsScalarTower ℂ targetField parameterField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact targetEmbedding.comp_algebraMap.symm

theorem target_trdeg : Algebra.trdeg ℂ targetField = 13 := by
  have : Algebra.IsAlgebraic targetPolynomial targetField :=
    IsLocalization.isAlgebraic targetField (nonZeroDivisors targetPolynomial)
  have h := trdeg_add_eq ℂ targetPolynomial (A := targetField)
  rw [trdeg_eq_zero (R := targetPolynomial) (A := targetField), add_zero] at h
  rw [← h]
  simp [targetPolynomial, MvPolynomial.trdeg_of_isDomain]

theorem parameter_trdeg : Algebra.trdeg ℂ parameterField = 13 := by
  have : Algebra.IsAlgebraic (polynomial ℂ) parameterField :=
    IsLocalization.isAlgebraic parameterField (nonZeroDivisors (polynomial ℂ))
  have h := trdeg_add_eq ℂ (polynomial ℂ) (A := parameterField)
  rw [trdeg_eq_zero (R := polynomial ℂ) (A := parameterField), add_zero] at h
  rw [← h]
  simp [polynomial, MvPolynomial.trdeg_of_isDomain]

/-- Genuine algebraicity of the Gauss field over the orbit-coordinate field. -/
theorem parameter_isAlgebraic : Algebra.IsAlgebraic targetField parameterField :=
  GenericEtaleFibreDegree.isAlgebraic_of_equal_finite_trdeg ℂ targetField parameterField
    (by rw [target_trdeg]; exact Cardinal.ofNat_lt_aleph0)
    (by rw [target_trdeg, parameter_trdeg])

variable {L : Type} [Field L] [Algebra ℂ L]

theorem target_image_mem (σ : parameterField →ₐ[ℂ] L) (E : IntermediateField ℂ L)
    (hE : ∀ j, σ (coordinate ℂ j) ∈ E) (x : targetField) :
    σ (targetEmbedding x) ∈ E := by
  have hp (p : targetPolynomial) :
      σ (targetEmbedding (algebraMap targetPolynomial targetField p)) ∈ E := by
    rw [targetEmbedding_algebraMap]
    induction p using MvPolynomial.induction_on with
    | C c =>
      simpa [coordinateMap] using E.algebraMap_mem c
    | add p q hp hq =>
      simpa only [map_add] using E.add_mem hp hq
    | mul_X p j hp =>
      simpa [coordinateMap] using E.mul_mem hp (hE j.down)
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective targetPolynomial x
  rw [map_div₀, map_div₀]
  exact E.div_mem (hp p) (hp q)

/-- In any actual field embedding, containing the thirteen literal orbit ratios suffices
to make every Gauss parameter algebraic. No finite-fibre or dominance premise is supplied. -/
theorem mapped_parameter_isAlgebraic (σ : parameterField →ₐ[ℂ] L) (E : IntermediateField ℂ L)
    (hE : ∀ j, σ (coordinate ℂ j) ∈ E) (y : parameterField) : IsAlgebraic E (σ y) := by
  let φ : targetField →ₐ[ℂ] L := σ.comp targetEmbedding
  let τ : targetField →+* E :=
    { toFun := fun x => ⟨φ x, target_image_mem σ E hE x⟩
      map_one' := Subtype.ext φ.toRingHom.map_one
      map_mul' a b := Subtype.ext (φ.toRingHom.map_mul a b)
      map_zero' := Subtype.ext φ.toRingHom.map_zero
      map_add' a b := Subtype.ext (φ.toRingHom.map_add a b) }
  letI : Algebra targetField E := τ.toAlgebra
  letI : Algebra targetField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower targetField E L := IsScalarTower.of_algebraMap_eq' rfl
  let σ' : parameterField →ₐ[targetField] L :=
    { toRingHom := σ.toRingHom
      commutes' := fun _ => rfl }
  haveI := parameter_isAlgebraic
  exact (IsAlgebraic.algHom σ' (Algebra.IsAlgebraic.isAlgebraic y)).tower_top E

end M9Native.PrimitiveGaussFieldExtension
