module

public import M9.PrimitiveOpenOrbit
public import M9.GaussGraphQuotient
public import M9.Private.GenericFiniteEtaleAway
public import M9.Private.EtalePointNeighborhood
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A native principal open in the actual primitive symplectic orbit

The native square graph is used directly. Its rational points give literal
Gauss parameters through its equations; the open-image theorem supplies the
principal open neighborhood.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace M9.PrimitiveOpenOrbitGeometry

open Module MvPolynomial PrimitiveOpenOrbit
open scoped BigOperators

variable (K : Type*) [Field K]

attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Index := Fin 13 ⊕ Unit
abbrev GP := GaussGraphQuotient.GraphPolynomial K (Fin 13)
abbrev Q := GaussGraphQuotient.GraphRing K (Fin 13) (formalA K) (X 0) (formalTarget K)

/-- The same square system defining the actual graph quotient. -/
def equations : Index → GP K :=
  Sum.elim (GaussGraphQuotient.graphRelation K (Fin 13) (formalA K) (formalTarget K))
    (fun _ => GaussGraphQuotient.inverseRelation K (Fin 13) (formalA K) (X 0))

theorem graphIdeal_eq_span :
    GaussGraphQuotient.graphIdeal K (Fin 13) (formalA K) (X 0) (formalTarget K) =
      Ideal.span (Set.range (equations K)) := by
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro (⟨i,rfl⟩ | hf)
    · exact ⟨Sum.inl i,rfl⟩
    · rcases hf with rfl
      exact ⟨Sum.inr (),rfl⟩
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i,rfl⟩
    | inr i => exact Or.inr rfl

/-- Evaluation of the graph's coefficient and parameter variables at literal field elements. -/
def graphEval (y z : Fin 13 → K) (u : K) : GP K →ₐ[K] K :=
  MvPolynomial.aevalTower (MvPolynomial.aeval y) (Sum.elim z (fun _ => u))

@[simp] theorem graphEval_parameter (y z : Fin 13 → K) (u : K) (f : ParameterRing K) :
    graphEval K y z u (GaussGraphQuotient.parameterMap K (Fin 13) f) = MvPolynomial.eval z f := by
  have h : (graphEval K y z u).comp (GaussGraphQuotient.parameterMap K (Fin 13)) =
      MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [graphEval]
  exact DFunLike.congr_fun h f

@[simp] theorem graphEval_C (y z : Fin 13 → K) (u : K) (f : ParameterRing K) :
    graphEval K y z u (C f) = MvPolynomial.eval y f := by simp [graphEval]

@[simp] theorem graphEval_X_inl (y z : Fin 13 → K) (u : K) (i : Fin 13) :
    graphEval K y z u (X (.inl i)) = z i := by simp [graphEval]
@[simp] theorem graphEval_X_inr (y z : Fin 13 → K) (u : K) :
    graphEval K y z u (X (.inr ())) = u := by simp [graphEval]

def baseEval : GP K →ₐ[K] K := graphEval K (basePoint K) (basePoint K) 1

@[simp] theorem baseEval_parameter (f : ParameterRing K) :
    baseEval K (GaussGraphQuotient.parameterMap K (Fin 13) f) = evalBase K f :=
  graphEval_parameter K _ _ _ _

@[simp] theorem baseEval_C (f : ParameterRing K) : baseEval K (C f) = evalBase K f :=
  graphEval_C K _ _ _ _

@[simp] theorem evalBase_X (i : Fin 13) : evalBase K (X i) = basePoint K i := by
  simp [PrimitiveOpenOrbit.evalBase]

@[simp] theorem baseEval_X_inl (i : Fin 13) : baseEval K (X (.inl i)) = basePoint K i :=
  graphEval_X_inl K _ _ _ _
@[simp] theorem baseEval_X_inr : baseEval K (X (.inr ())) = 1 :=
  graphEval_X_inr K _ _ _

@[simp] theorem baseEval_equations (i : Index) : baseEval K (equations K i) = 0 := by
  cases i with
  | inl i =>
    simp [equations,GaussGraphQuotient.graphRelation,basePoint,Pi.single_apply]
  | inr i =>
    simp [equations,GaussGraphQuotient.inverseRelation,GaussGraphQuotient.denominator,
      basePoint]

/-- Exact contraction of the polynomial coordinate map with a parameter derivative. -/
theorem parameterMap_pderiv (f : ParameterRing K) (i : Fin 13) :
    MvPolynomial.pderiv (.inl i) (GaussGraphQuotient.parameterMap K (Fin 13) f) =
      GaussGraphQuotient.parameterMap K (Fin 13) (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [GaussGraphQuotient.parameterMap,
      IsScalarTower.algebraMap_eq K (ParameterRing K) (GP K)]
  | add f g hf hg => simp [hf,hg]
  | mul_X f j hf =>
    simp [hf,Pi.single_apply,apply_ite]

/-- The parameter map contains no inverse-variable occurrence. -/
theorem parameterMap_pderiv_inr (f : ParameterRing K) :
    MvPolynomial.pderiv (.inr ()) (GaussGraphQuotient.parameterMap K (Fin 13) f) = 0 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [GaussGraphQuotient.parameterMap,
      IsScalarTower.algebraMap_eq K (ParameterRing K) (GP K)]
  | add f g hf hg => simp [hf,hg]
  | mul_X f j hf => simp [hf]

/-- Actual Jacobian matrix evaluated at the graph point lying over the split vector. -/
def baseJacobian : Matrix Index Index K :=
  fun i j => baseEval K (MvPolynomial.pderiv j (equations K i))

@[simp] theorem baseJacobian_inl_inl (i j : Fin 13) :
    baseJacobian K (.inl i) (.inl j) = -evalBase K (chartJacobian K i j) := by
  simp only [baseJacobian,equations,Sum.elim_inl,GaussGraphQuotient.graphRelation,
    map_sub,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,parameterMap_pderiv,
    mul_zero,add_zero,map_mul,baseEval_parameter,baseEval_C]
  rw [show evalBase K (X i) = evalBase K (formalTarget K i) by
    simp [basePoint,Pi.single_apply]]
  simp only [chartJacobian,map_sub,map_mul,evalBase_formalA,one_mul]
  ring

@[simp] theorem baseJacobian_inl_inr (i : Fin 13) :
    baseJacobian K (.inl i) (.inr ()) = 0 := by
  simp [baseJacobian,equations,GaussGraphQuotient.graphRelation,
    parameterMap_pderiv_inr]

@[simp] theorem baseJacobian_inr_inr : baseJacobian K (.inr ()) (.inr ()) = 1 := by
  simp [baseJacobian,equations,GaussGraphQuotient.inverseRelation,
    GaussGraphQuotient.denominator,parameterMap_pderiv_inr,basePoint]


/-- The actual graph Jacobian has an invertible evaluated determinant. -/
theorem baseJacobian_det : Matrix.det (baseJacobian K) = 2 := by
  have hb : baseJacobian K = Matrix.fromBlocks
      (-((chartJacobian K).map (evalBase K))) 0
      (fun _ j => baseJacobian K (.inr ()) (.inl j)) (1 : Matrix Unit Unit K) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · exact baseJacobian_inl_inl K i j
    · exact baseJacobian_inl_inr K i
    · rfl
    · exact baseJacobian_inr_inr K
  have hd : Matrix.det ((chartJacobian K).map (evalBase K)) = -2 := by
    have h := evalBase_chartJacobian_det K
    rw [RingHom.map_det] at h
    exact h
  rw [hb,Matrix.det_fromBlocks_zero₁₂,Matrix.det_neg,hd]
  norm_num

@[simp] theorem baseEval_jacobianDet :
    baseEval K (FiniteEtaleJacobianReplay.jacobianDet (equations K)) = 2 := by
  simp only [FiniteEtaleJacobianReplay.jacobianDet,AlgHom.map_det]
  exact baseJacobian_det K

/-- The actual point of the graph quotient lying over the split form. -/
def quotientBasePoint : Q K →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (baseEval K) (by
    change GaussGraphQuotient.graphIdeal K (Fin 13) (formalA K) (X 0) (formalTarget K) ≤
      RingHom.ker (baseEval K).toRingHom
    rw [graphIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact baseEval_equations K i)

@[simp] theorem quotientBasePoint_graphMk (f : GP K) :
    quotientBasePoint K (GaussGraphQuotient.graphMk K (Fin 13)
      (formalA K) (X 0) (formalTarget K) f) = baseEval K f := rfl

abbrev jacobianElement : Q K :=
  GaussGraphQuotient.graphMk K (Fin 13) (formalA K) (X 0) (formalTarget K)
    (FiniteEtaleJacobianReplay.jacobianDet (equations K))

abbrev EtaleRing := Localization.Away (jacobianElement K)

def quotientToEtale : Q K →ₐ[K] EtaleRing K := IsScalarTower.toAlgHom K (Q K) (EtaleRing K)

def coefficientToGraph : ParameterRing K →ₐ[K] Q K :=
  (GaussGraphQuotient.graphMk K (Fin 13) (formalA K) (X 0) (formalTarget K)).comp
    (IsScalarTower.toAlgHom K (ParameterRing K) (GP K))

@[simp] theorem coefficientToGraph_X (i : Fin 13) :
    coefficientToGraph K (X i) =
      GaussGraphQuotient.graphY K (Fin 13) (formalA K) (X 0) (formalTarget K) i := rfl

def coefficientMap : ParameterRing K →ₐ[K] EtaleRing K :=
  (quotientToEtale K).comp (coefficientToGraph K)

@[simp] theorem coefficientMap_X (i : Fin 13) : coefficientMap K (X i) =
    quotientToEtale K (GaussGraphQuotient.graphY K (Fin 13) (formalA K) (X 0) (formalTarget K) i) := rfl

/-- The actual coefficient-ring map of the square graph is étale after inverting its actual Jacobian. -/
theorem coefficientMap_etale : RingHom.Etale (coefficientMap K).toRingHom := by
  let : IsLocalization.Away
      (Ideal.Quotient.mk (GaussGraphQuotient.graphIdeal K (Fin 13) (formalA K) (X 0) (formalTarget K))
        (FiniteEtaleJacobianReplay.jacobianDet (equations K))) (EtaleRing K) := by
    change IsLocalization.Away (jacobianElement K) (Localization.Away (jacobianElement K))
    infer_instance
  exact FiniteEtaleJacobianReplay.etale_away_jacobianDet
    (R := ParameterRing K) (equations K) (graphIdeal_eq_span K) (EtaleRing K)

instance finiteType_etaleRing : Algebra.FiniteType K (EtaleRing K) := by
  have hGP : Algebra.FiniteType K (GP K) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (ParameterRing K))
    (inferInstance : Algebra.FiniteType (ParameterRing K) (GP K))
  have hQ : Algebra.FiniteType K (Q K) := hGP.of_surjective
    (GaussGraphQuotient.graphMk K (Fin 13) (formalA K) (X 0) (formalTarget K))
    Ideal.Quotient.mk_surjective
  have hQS : Algebra.FiniteType (Q K) (EtaleRing K) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (jacobianElement K)) (EtaleRing K)
  exact Algebra.FiniteType.trans hQ hQS

/-- The normalized graph point survives the Jacobian localization. -/
def basePointOnEtale [CharZero K] : EtaleRing K →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (S := EtaleRing K) (f := quotientBasePoint K)
    (jacobianElement K) (by
      change IsUnit (baseEval K (FiniteEtaleJacobianReplay.jacobianDet (equations K)))
      rw [baseEval_jacobianDet]
      exact isUnit_iff_ne_zero.mpr two_ne_zero)

@[simp] theorem basePointOnEtale_map [CharZero K] (q : Q K) :
    basePointOnEtale K (quotientToEtale K q) = quotientBasePoint K q := by
  simp [basePointOnEtale,quotientToEtale]

theorem basePointOnEtale_coefficients [CharZero K] :
    (basePointOnEtale K).comp (coefficientMap K) = MvPolynomial.aeval (basePoint K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,coefficientMap_X,basePointOnEtale_map,
    GaussGraphQuotient.graphY,quotientBasePoint_graphMk,baseEval_C,evalBase_X,MvPolynomial.aeval_X]

/-- Actual parameter values read from a field-valued point of the localized graph. -/
def sourcePoint (ψ : EtaleRing K →ₐ[K] K) : ParameterRing K →ₐ[K] K :=
  (ψ.comp (quotientToEtale K)).comp
    (GaussGraphQuotient.parameterToGraph K (Fin 13) (formalA K) (X 0) (formalTarget K))

def parameters (ψ : EtaleRing K →ₐ[K] K) : Fin 13 → K := fun i => sourcePoint K ψ (X i)

theorem sourcePoint_eq_aeval (ψ : EtaleRing K →ₐ[K] K) :
    sourcePoint K ψ = MvPolynomial.aeval (parameters K ψ) := by
  apply MvPolynomial.algHom_ext
  intro i
  change parameters K ψ i = (MvPolynomial.aeval (parameters K ψ)) (X i)
  rw [MvPolynomial.aeval_X]

@[simp] theorem sourcePoint_apply (ψ : EtaleRing K →ₐ[K] K) (f : ParameterRing K) :
    ψ (quotientToEtale K (GaussGraphQuotient.parameterToGraph K (Fin 13)
      (formalA K) (X 0) (formalTarget K) f)) = MvPolynomial.eval (parameters K ψ) f := by
  change sourcePoint K ψ f = (MvPolynomial.aeval (parameters K ψ)) f
  rw [sourcePoint_eq_aeval]

/-- Every actual point of the native graph image belongs to the actual symplectic projective orbit. -/
theorem point_lift_in_orbit [CharZero K] (y : Fin 13 → K) (ψ : EtaleRing K →ₐ[K] K)
    (hψ : ψ.comp (coefficientMap K) = MvPolynomial.aeval y) :
    ∃ (h : PrimitiveStabilizer.Sp6 K) (c : K), c ≠ 0 ∧
      chartVector K y = c • PrimitiveStabilizer.primitiveAction K h (PrimitiveStabilizer.rho K) := by
  let z := parameters K ψ
  have hyi (i : Fin 13) :
      ψ (quotientToEtale K (GaussGraphQuotient.graphY K (Fin 13)
        (formalA K) (X 0) (formalTarget K) i)) = y i := by
    have h := DFunLike.congr_fun hψ (X i)
    simpa only [AlgHom.comp_apply,coefficientMap_X,MvPolynomial.aeval_X] using h
  have hrel (i : Fin 13) : MvPolynomial.eval z (formalA K) * y i =
      MvPolynomial.eval z (formalTarget K i) := by
    have h := congrArg (ψ.comp (quotientToEtale K))
      (GaussGraphQuotient.graph_equation K (Fin 13) (formalA K) (X 0) (formalTarget K) i)
    simpa only [AlgHom.comp_apply,map_mul,sourcePoint_apply,hyi] using h
  have hinv : ψ (quotientToEtale K (GaussGraphQuotient.graphU K (Fin 13)
      (formalA K) (X 0) (formalTarget K))) *
      (z 0 * MvPolynomial.eval z (formalA K)) = 1 := by
    have h := congrArg (ψ.comp (quotientToEtale K))
      (GaussGraphQuotient.inverse_equation K (Fin 13) (formalA K) (X 0) (formalTarget K))
    simpa only [AlgHom.comp_apply,map_mul,map_one,sourcePoint_apply,
      GaussGraphQuotient.denominator,map_mul,MvPolynomial.eval_X] using h
  have hd : z 0 * MvPolynomial.eval z (formalA K) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hinv
    exact zero_ne_one hinv
  obtain ⟨ht,hA⟩ := mul_ne_zero_iff.mp hd
  have hy : y = chartPoint K z := by
    funext i
    change y i = MvPolynomial.eval z (formalTarget K i) / MvPolynomial.eval z (formalA K)
    apply (eq_div_iff hA).mpr
    exact (mul_comm _ _).trans (hrel i)
  rw [hy]
  exact chartPoint_in_orbit K z ht hA

/-- A genuine principal open neighborhood of the split point is contained in its actual orbit. -/
theorem exists_principal_open_orbit [CharZero K] [IsAlgClosed K] :
    ∃ f : ParameterRing K, evalBase K f ≠ 0 ∧ ∀ y : Fin 13 → K,
      MvPolynomial.eval y f ≠ 0 → ∃ (h : PrimitiveStabilizer.Sp6 K) (c : K), c ≠ 0 ∧
        chartVector K y = c • PrimitiveStabilizer.primitiveAction K h (PrimitiveStabilizer.rho K) := by
  obtain ⟨f,hf,hpoints⟩ := EtalePointNeighborhood.exists_principal_open_point_lifts
    (coefficientMap K) (coefficientMap_etale K) (basePointOnEtale K)
  refine ⟨f,?_,?_⟩
  · change ((basePointOnEtale K).comp (coefficientMap K)) f ≠ 0 at hf
    rw [basePointOnEtale_coefficients] at hf
    exact hf
  · intro y hy
    obtain ⟨ψ,hψ⟩ := hpoints (MvPolynomial.aeval y) hy
    exact point_lift_in_orbit K y ψ hψ

/-- The principal open is dense in the native affine spectrum and has only actual orbit points. -/
theorem exists_dense_principal_open_orbit [CharZero K] [IsAlgClosed K] :
    ∃ f : ParameterRing K, Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ParameterRing K))) ∧
      evalBase K f ≠ 0 ∧ ∀ y : Fin 13 → K, MvPolynomial.eval y f ≠ 0 →
        ∃ (h : PrimitiveStabilizer.Sp6 K) (c : K), c ≠ 0 ∧
          chartVector K y = c • PrimitiveStabilizer.primitiveAction K h (PrimitiveStabilizer.rho K) := by
  obtain ⟨f,hf,horbit⟩ := exists_principal_open_orbit K
  refine ⟨f,?_,hf,horbit⟩
  apply (PrimeSpectrum.basicOpen f).isOpen.dense
  exact ⟨EtalePointNeighborhood.pointPrime (MvPolynomial.aeval (basePoint K)),hf⟩


@[simp] theorem chartVector_basePoint [CharZero K] :
    chartVector K (basePoint K) = PrimitiveStabilizer.rho K := by
  apply primitive_ext_tuple K
  · simp [PrimitiveStabilizer.rho]
  · rw [coordinateTuple_chartVector]
    funext i
    fin_cases i <;> simp [coordinateTuple,coordinateFunctionals,PrimitiveStabilizer.rho,basePoint]

theorem chartVector_ne_zero [CharZero K] (y : Fin 13 → K) : chartVector K y ≠ 0 := by
  intro hz
  have h := congrArg (fun r : ExteriorPrimitive.Primitive K =>
    ExteriorPrimitive.aCoordinate K r.val) hz
  simp at h

def chartProjective [CharZero K] (y : Fin 13 → K) :
    Projectivization K (ExteriorPrimitive.Primitive K) :=
  Projectivization.mk K (chartVector K y) (chartVector_ne_zero K y)

@[simp] theorem chartProjective_basePoint [CharZero K] :
    chartProjective K (basePoint K) = PrimitiveStabilizer.rhoProjective K := by
  simp [chartProjective,chartVector_basePoint,PrimitiveStabilizer.rhoProjective]

/-- The orbit witness is the actual projective action on the actual primitive exterior kernel. -/
theorem projective_transport_of_proportional [CharZero K] (y : Fin 13 → K)
    (h : PrimitiveStabilizer.Sp6 K) (c : K) (hc : c ≠ 0)
    (heq : chartVector K y = c • PrimitiveStabilizer.primitiveAction K h (PrimitiveStabilizer.rho K)) :
    PrimitiveStabilizer.projectiveAction K h (PrimitiveStabilizer.rhoProjective K) =
      chartProjective K y := by
  change PrimitiveStabilizer.primitiveRepresentation K h • PrimitiveStabilizer.rhoProjective K = _
  rw [PrimitiveStabilizer.rhoProjective,chartProjective,Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  refine ⟨(Units.mk0 c hc)⁻¹,?_⟩
  change c⁻¹ • chartVector K y =
    PrimitiveStabilizer.primitiveAction K h (PrimitiveStabilizer.rho K)
  rw [heq,smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- A dense actual principal open around `[a+b]` consists of points of its actual projective orbit. -/
theorem exists_dense_principal_open_projective_orbit [CharZero K] [IsAlgClosed K] :
    ∃ f : ParameterRing K, Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ParameterRing K))) ∧
      evalBase K f ≠ 0 ∧ ∀ y : Fin 13 → K, MvPolynomial.eval y f ≠ 0 →
        ∃ h : PrimitiveStabilizer.Sp6 K,
          PrimitiveStabilizer.projectiveAction K h (PrimitiveStabilizer.rhoProjective K) =
            chartProjective K y := by
  obtain ⟨f,hd,hf,horbit⟩ := exists_dense_principal_open_orbit K
  refine ⟨f,hd,hf,?_⟩
  intro y hy
  obtain ⟨h,c,hc,heq⟩ := horbit y hy
  exact ⟨h,projective_transport_of_proportional K y h c hc heq⟩


/-- Explicit inverse coordinates on the actual projective chart `a≠0`. -/
def primitiveChart (w : ExteriorPrimitive.Primitive K) : Fin 13 → K :=
  fun i => coordinateTuple K w.val i / ExteriorPrimitive.aCoordinate K w.val

theorem chartVector_primitiveChart [CharZero K] (w : ExteriorPrimitive.Primitive K)
    (hA : ExteriorPrimitive.aCoordinate K w.val ≠ 0) :
    chartVector K (primitiveChart K w) = (ExteriorPrimitive.aCoordinate K w.val)⁻¹ • w := by
  apply primitive_ext_tuple K
  · simp only [aCoordinate_chartVector,Submodule.coe_smul,map_smul,smul_eq_mul,inv_mul_cancel₀ hA]
  · rw [coordinateTuple_chartVector]
    simp only [Submodule.coe_smul,map_smul]
    funext i
    simp only [primitiveChart,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

theorem primitive_ne_zero_of_a (w : ExteriorPrimitive.Primitive K)
    (hA : ExteriorPrimitive.aCoordinate K w.val ≠ 0) : w ≠ 0 := by
  intro hz
  apply hA
  simp [hz]

theorem chartProjective_primitiveChart [CharZero K] (w : ExteriorPrimitive.Primitive K)
    (hA : ExteriorPrimitive.aCoordinate K w.val ≠ 0) :
    chartProjective K (primitiveChart K w) =
      Projectivization.mk K w (primitive_ne_zero_of_a K w hA) := by
  rw [chartProjective,Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 _ (inv_ne_zero hA),(chartVector_primitiveChart K w hA).symm⟩

theorem chartProjective_injective [CharZero K] : Function.Injective (chartProjective K) := by
  intro y z h
  have h' : Projectivization.mk K (chartVector K y) (chartVector_ne_zero K y) =
      Projectivization.mk K (chartVector K z) (chartVector_ne_zero K z) := h
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h'
  have ha := congrArg (fun r : ExteriorPrimitive.Primitive K =>
    ExteriorPrimitive.aCoordinate K r.val) hc
  have hc1 : (c : K) = 1 := by
    simpa only [Units.smul_def,Submodule.coe_smul,map_smul,aCoordinate_chartVector,
      smul_eq_mul,mul_one] using ha
  have hv : chartVector K z = chartVector K y := by
    simpa only [Units.smul_def,hc1,one_smul] using hc
  have ht := congrArg (fun r : ExteriorPrimitive.Primitive K => coordinateTuple K r.val) hv
  simpa only [coordinateTuple_chartVector] using ht.symm

/-- The complex specialization has no remaining algebraic-closedness or open-orbit premise. -/
theorem complex_dense_principal_open_projective_orbit :
    ∃ f : ParameterRing ℂ, Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ParameterRing ℂ))) ∧
      evalBase ℂ f ≠ 0 ∧ ∀ y : Fin 13 → ℂ, MvPolynomial.eval y f ≠ 0 →
        ∃ h : PrimitiveStabilizer.Sp6 ℂ,
          PrimitiveStabilizer.projectiveAction ℂ h (PrimitiveStabilizer.rhoProjective ℂ) =
            chartProjective ℂ y :=
  exists_dense_principal_open_projective_orbit ℂ

end M9.PrimitiveOpenOrbitGeometry
