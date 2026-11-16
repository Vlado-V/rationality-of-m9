module
public import M9StacksIntegration.LagrangianGrassmannian

/-! The primitive Plucker coordinate identities over arbitrary commutative
coordinate rings. The actual third exterior power and contraction are used
throughout. The fourteen-coordinate projection is the scalar extension of
the frozen field model along an explicit coefficient-ring homomorphism.
No reducedness or field-valued-points criterion is used.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open Module Matrix exteriorPower
open scoped BigOperators
namespace M9Native.LagrangianRing
variable (R : Type*) [CommRing R]
abbrev V := Fin 6 → R
abbrev Third := ⋀[R]^3 (V R)
def eIndex (i : Fin 3) : Fin 6 := i.castAdd 3
def fIndex (i : Fin 3) : Fin 6 := Fin.natAdd 3 i

def basisVector (i : Fin 6) : V R := Pi.single i 1
def e (i : Fin 3) : V R := basisVector R (eIndex i)
def f (i : Fin 3) : V R := basisVector R (fIndex i)

/-- The paper's sign convention, `ω(e_i,f_j)=δ_ij`. -/
def omegaValue (u v : V R) : R :=
  ∑ i : Fin 3, (u (eIndex i) * v (fIndex i) - u (fIndex i) * v (eIndex i))

def omega : LinearMap.BilinForm R (V R) :=
  LinearMap.mk₂ R (omegaValue R)
    (by intro u v w; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro c u v; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro u v w; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro c u v; simp [omegaValue, Fin.sum_univ_succ]; ring)

@[simp] theorem omega_apply (u v : V R) : omega R u v = omegaValue R u v := rfl

@[simp] theorem omegaValue_self (u : V R) : omegaValue R u u = 0 := by
  simp [omegaValue, mul_comm]

@[simp] theorem omega_self (u : V R) : omega R u u = 0 := by
  exact omegaValue_self R u

theorem omega_swap (u v : V R) : omega R u v = -omega R v u := by
  simp only [omega_apply, omegaValue, Fin.sum_univ_succ]
  ring

def tripleContract (u v w : V R) : V R :=
  omega R u v • w - omega R u w • v + omega R v w • u

/-- The actual contraction formula before descent to the exterior power. -/
def contractionFormula (v : Fin 3 → V R) : V R := tripleContract R (v 0) (v 1) (v 2)

theorem tripleContract_add_left (x y v w : V R) :
    tripleContract R (x+y) v w = tripleContract R x v w + tripleContract R y v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_add_middle (u x y w : V R) :
    tripleContract R u (x+y) w = tripleContract R u x w + tripleContract R u y w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_add_right (u v x y : V R) :
    tripleContract R u v (x+y) = tripleContract R u v x + tripleContract R u v y := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_left (c : R) (u v w : V R) :
    tripleContract R (c • u) v w = c • tripleContract R u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_middle (c : R) (u v w : V R) :
    tripleContract R u (c • v) w = c • tripleContract R u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_right (c : R) (u v w : V R) :
    tripleContract R u v (c • w) = c • tripleContract R u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

def contractionAlternating : (V R) [⋀^Fin 3]→ₗ[R] V R where
  toMultilinearMap := MultilinearMap.mk' (contractionFormula R)
    (by
      intro v i x y
      fin_cases i
      · change tripleContract R (x+y) (v 1) (v 2) = tripleContract R x (v 1) (v 2) + tripleContract R y (v 1) (v 2)
        exact tripleContract_add_left R x y _ _
      · change tripleContract R (v 0) (x+y) (v 2) = tripleContract R (v 0) x (v 2) + tripleContract R (v 0) y (v 2)
        exact tripleContract_add_middle R _ x y _
      · change tripleContract R (v 0) (v 1) (x+y) = tripleContract R (v 0) (v 1) x + tripleContract R (v 0) (v 1) y
        exact tripleContract_add_right R _ _ x y)
    (by
      intro v i c x
      fin_cases i
      · change tripleContract R (c • x) (v 1) (v 2) = c • tripleContract R x (v 1) (v 2)
        exact tripleContract_smul_left R c x _ _
      · change tripleContract R (v 0) (c • x) (v 2) = c • tripleContract R (v 0) x (v 2)
        exact tripleContract_smul_middle R c _ x _
      · change tripleContract R (v 0) (v 1) (c • x) = c • tripleContract R (v 0) (v 1) x
        exact tripleContract_smul_right R c _ _ x)
  map_eq_zero_of_eq' v i j hij hne := by
    change contractionFormula R v = 0
    have hv : v 0 = v 1 ∨ v 0 = v 2 ∨ v 1 = v 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hv with hv | hv | hv
    · simp [contractionFormula, tripleContract, hv]
    · funext k
      simp only [contractionFormula, tripleContract, hv, omega_self, Pi.add_apply, Pi.smul_apply,
        zero_smul, sub_zero, smul_eq_mul, Pi.zero_apply]
      rw [omega_swap R (v 2) (v 1)]
      ring
    · simp [contractionFormula, tripleContract, hv]

/-- Contraction on Mathlib's actual third exterior power. -/
def contraction : Third R →ₗ[R] V R :=
  exteriorPower.alternatingMapLinearEquiv (contractionAlternating R)

@[simp] theorem contraction_ιMulti (v : Fin 3 → V R) :
    contraction R (exteriorPower.ιMulti R 3 v) = contractionFormula R v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

def wedge3 (u v w : V R) : Third R := exteriorPower.ιMulti R 3 ![u,v,w]

@[simp] theorem contraction_wedge3 (u v w : V R) :
    contraction R (wedge3 R u v w) = omega R u v • w - omega R u w • v + omega R v w • u := by
  simp [wedge3, contractionFormula, tripleContract]



abbrev TripleIndex := Set.powersetCard (Fin 6) 3

def tripleEquiv : TripleIndex ≃ Fin 20 :=
  Fintype.equivFinOfCardEq
    ((finrank_eq_card_basis ((Pi.basisFun ℚ (Fin 6)).exteriorPower 3)).symm.trans
      (M9Native.LagrangianField.finrank_third ℚ))

def triple (j : Fin 20) : Fin 3 ↪ Fin 6 :=
  (Set.powersetCard.ofFinEmbEquiv.symm (tripleEquiv.symm j)).toEmbedding

def thirdBasis20 : Basis (Fin 20) R (Third R) :=
  ((Pi.basisFun R (Fin 6)).exteriorPower 3).reindex tripleEquiv

theorem thirdBasis20_apply (j : Fin 20) :
    thirdBasis20 R j=exteriorPower.ιMulti R 3 (fun i => basisVector R (triple j i)) := by
  rw [thirdBasis20,Basis.reindex_apply,exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family]
  exact congrArg (exteriorPower.ιMulti R 3)
    (funext (fun i => Pi.basisFun_apply R (Fin 6) (triple j i)))

def contractionMatrix : Matrix (Fin 6) (Fin 20) R :=
  LinearMap.toMatrix (thirdBasis20 R) (Pi.basisFun R (Fin 6)) (contraction R)

theorem contractionMatrix_apply (i : Fin 6) (j : Fin 20) :
    contractionMatrix R i j=contractionFormula R (fun k => basisVector R (triple j k)) i := by
  simp only [contractionMatrix,LinearMap.toMatrix_apply,Pi.basisFun_repr]
  rw [thirdBasis20_apply,contraction_ιMulti]

def rowPlucker (M : Matrix (Fin 3) (Fin 6) R) : Third R :=
  exteriorPower.ιMulti R 3 (fun i => M i)

def rowTwenty (M : Matrix (Fin 3) (Fin 6) R) : Fin 20 → R :=
  (thirdBasis20 R).equivFun (rowPlucker R M)

theorem rowTwenty_eq_minor (M : Matrix (Fin 3) (Fin 6) R) (j : Fin 20) :
    rowTwenty R M j=Matrix.det (M.submatrix id (triple j)) := by
  change ((Pi.basisFun R (Fin 6)).exteriorPower 3).repr
    (rowPlucker R M) (tripleEquiv.symm j)=_
  rw [exteriorPower.basis_repr_apply, rowPlucker,exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

theorem contraction_rowTwenty_eq_zero (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j, omega R (M i) (M j)=0) :
    contractionMatrix R *ᵥ rowTwenty R M=0 := by
  have h : contraction R (rowPlucker R M)=0 := by
    rw [rowPlucker,contraction_ιMulti]
    simp only [contractionFormula,tripleContract,hM,zero_smul,sub_zero,add_zero]
  change LinearMap.toMatrix (thirdBasis20 R) (Pi.basisFun R (Fin 6)) (contraction R) *ᵥ
    (thirdBasis20 R).repr (rowPlucker R M)=0
  rw [LinearMap.toMatrix_mulVec_repr,h]
  rfl

section FieldComparison
variable (K : Type*) [Field K]

theorem thirdBasis20_eq_field :
    thirdBasis20 K=M9Native.LagrangianField.thirdBasis20 K := rfl

theorem contraction_eq_field :
    contraction K=M9Native.LagrangianField.contraction K := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change contraction K (exteriorPower.ιMulti K 3 v)=
    M9Native.LagrangianField.contraction K (exteriorPower.ιMulti K 3 v)
  rw [contraction_ιMulti,M9Native.LagrangianField.contraction_ιMulti]
  rfl

theorem contractionMatrix_eq_field :
    contractionMatrix K=M9Native.LagrangianField.contractionMatrix K := by
  rw [contractionMatrix,thirdBasis20_eq_field,contraction_eq_field]
  rfl

end FieldComparison


/-- The actual contraction matrix has coefficients compatible with every
coefficient-ring homomorphism. -/
theorem contractionMatrix_map {K : Type*} [Field K] (f : K →+* R) :
    (M9Native.LagrangianField.contractionMatrix K).map f=contractionMatrix R := by
  ext i j
  rw [← contractionMatrix_eq_field K,Matrix.map_apply,contractionMatrix_apply,contractionMatrix_apply]
  have hf (p : Prop) [Decidable p] (x y : K) :
      f (if p then x else y)=(if p then f x else f y) := by split_ifs <;> rfl
  simp [contractionFormula,tripleContract,omegaValue,basisVector,Pi.single_apply,smul_eq_mul,hf]

/-- Primitive reconstruction over arbitrary coordinate rings, using the
actual minors of the actual three-row quotient matrix. -/
theorem primitive_reconstruction {K : Type*} [Field K] [CharZero K] (f : K →+* R)
    (M : Matrix (Fin 3) (Fin 6) R) (hM : ∀ i j,omega R (M i) (M j)=0) :
    (M9Native.LagrangianField.embeddingMatrix K).map f *ᵥ
      ((M9Native.LagrangianField.projectionMatrix K).map f *ᵥ rowTwenty R M)=rowTwenty R M :=
  M9Native.LagrangianField.primitive_vector_reconstruction K f (rowTwenty R M)
    (by rw [contractionMatrix_map];exact contraction_rowTwenty_eq_zero R M hM)



def coordinate3 (c : Fin 3 ↪ Fin 6) : Third R →ₗ[R] R :=
  exteriorPower.pairingDual R (V R) 3
    (exteriorPower.ιMulti R 3 (fun j => LinearMap.proj (c j)))

theorem coordinate3_rowPlucker (M : Matrix (Fin 3) (Fin 6) R) (c : Fin 3 ↪ Fin 6) :
    coordinate3 R c (rowPlucker R M)=Matrix.det (M.submatrix id c) := by
  simp only [coordinate3,rowPlucker,exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

theorem coordinate3_eq_sum (w : Third R) (c : Fin 3 ↪ Fin 6) :
    coordinate3 R c w=∑ j : Fin 20,(thirdBasis20 R).equivFun w j *
      coordinate3 R c (thirdBasis20 R j) := by
  have h := congrArg (coordinate3 R c) ((thirdBasis20 R).sum_repr w)
  simpa only [map_sum,map_smul,smul_eq_mul,Basis.equivFun_apply] using h.symm

/-- The twenty actual exterior coordinates span the unit ideal whenever
one actual quotient minor is a unit. -/
theorem span_rowTwenty_eq_top_of_isUnit_minor (M : Matrix (Fin 3) (Fin 6) R)
    (c : Fin 3 ↪ Fin 6) (hc : IsUnit (Matrix.det (M.submatrix id c))) :
    Ideal.span (Set.range (rowTwenty R M))=⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ ?_ hc
  rw [← coordinate3_rowPlucker R M c,coordinate3_eq_sum]
  exact Submodule.sum_mem _ (fun j _ => Ideal.mul_mem_right _ _
    (Ideal.subset_span ⟨j,rfl⟩))

section PrimitiveFourteen
variable {K : Type*} [Field K] [CharZero K] (f : K →+* R)

def rowFourteen (M : Matrix (Fin 3) (Fin 6) R) : Fin 14 → R :=
  (M9Native.LagrangianField.projectionMatrix K).map f *ᵥ rowTwenty R M

def minorFourteen (c : Fin 3 ↪ Fin 6) (v : Fin 14 → R) : R :=
  ∑ j : Fin 20,((M9Native.LagrangianField.embeddingMatrix K).map f *ᵥ v) j *
    coordinate3 R c (thirdBasis20 R j)

/-- Every one of the native 120 quotient minors is a genuine linear
functional of the fourteen coordinates, over arbitrary coordinate rings. -/
theorem nativeMinor_from_rowFourteen (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,omega R (M i) (M j)=0) (c : Fin 3 ↪ Fin 6) :
    minorFourteen R f c (rowFourteen R f M)=Matrix.det (M.submatrix id c) := by
  rw [minorFourteen,rowFourteen,primitive_reconstruction R f M hM]
  exact (coordinate3_eq_sum R (rowPlucker R M) c).symm.trans
    (coordinate3_rowPlucker R M c)

/-- The projected actual row coordinates define an honest projective point
on every normalized quotient chart. -/
theorem span_rowFourteen_eq_top (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,omega R (M i) (M j)=0) (c : Fin 3 ↪ Fin 6)
    (hc : IsUnit (Matrix.det (M.submatrix id c))) :
    Ideal.span (Set.range (rowFourteen R f M))=⊤ :=
  M9Native.LagrangianField.span_projection_eq_top K f (rowTwenty R M)
    (by rw [contractionMatrix_map];exact contraction_rowTwenty_eq_zero R M hM)
    (span_rowTwenty_eq_top_of_isUnit_minor R M c hc)

end PrimitiveFourteen



/-- The actual quotient bivector for an arbitrary three-by-six matrix. -/
def quotientSigma (M : Matrix (Fin 3) (Fin 6) R) : ⋀[R]^2 (Fin 3 → R) :=
  ∑ i : Fin 3,exteriorPower.ιMulti R 2
    ![(fun j => M j (i.castAdd 3)),(fun j => M j (Fin.natAdd 3 i))]

def coordinate2 (i j : Fin 3) : (⋀[R]^2 (Fin 3 → R)) →ₗ[R] R :=
  exteriorPower.pairingDual R (Fin 3 → R) 2
    (exteriorPower.ιMulti R 2 ![LinearMap.proj i,LinearMap.proj j])

@[simp] theorem coordinate2_wedge (i j : Fin 3) (v w : Fin 3 → R) :
    coordinate2 R i j (exteriorPower.ιMulti R 2 ![v,w])=v i*w j-v j*w i := by
  simp [coordinate2,Matrix.det_fin_two]

theorem coordinate2_quotientSigma (M : Matrix (Fin 3) (Fin 6) R) (i j : Fin 3) :
    coordinate2 R i j (quotientSigma R M)=omega R (M i) (M j) := by
  simp only [quotientSigma,map_sum,coordinate2_wedge,omega_apply,omegaValue,eIndex,fIndex]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rows_isotropic_of_quotientSigma_zero (M : Matrix (Fin 3) (Fin 6) R)
    (hM : quotientSigma R M=0) (i j : Fin 3) : omega R (M i) (M j)=0 := by
  rw [← coordinate2_quotientSigma R M i j,hM,map_zero]



/-- Changing the three quotient rows scales all actual exterior coordinates
by the actual determinant, over any commutative coordinate ring. -/
theorem rowTwenty_mul (E : Matrix (Fin 3) (Fin 3) R) (M : Matrix (Fin 3) (Fin 6) R) :
    rowTwenty R (E*M)=E.det • rowTwenty R M := by
  ext j
  simp only [Pi.smul_apply,smul_eq_mul,rowTwenty_eq_minor]
  rw [← Matrix.det_mul]
  congr 1

theorem rowFourteen_mul {K : Type*} [Field K] (f : K →+* R)
    (E : Matrix (Fin 3) (Fin 3) R) (M : Matrix (Fin 3) (Fin 6) R) :
    rowFourteen R f (E*M)=E.det • rowFourteen R f M := by
  simp only [rowFourteen,rowTwenty_mul,Matrix.mulVec_smul]

/-- The coordinate-ring construction specializes to the frozen manuscript
fourteen-coordinate model, with no silently chosen row/kernel identification. -/
theorem rowFourteen_id_eq_field (K : Type*) [Field K]
    (M : Matrix (Fin 3) (Fin 6) K) :
    rowFourteen K (RingHom.id K) M=M9Native.LagrangianField.rowFourteen K M := by
  have hrow : rowPlucker K M=M9Native.LagrangianField.rowPlucker K M := by
    unfold rowPlucker M9Native.LagrangianField.rowPlucker M9Native.LagrangianField.wedge3
    congr 1
    funext i
    fin_cases i <;> rfl
  change M9Native.LagrangianField.projectionMatrix K *ᵥ
      (thirdBasis20 K).repr (rowPlucker K M)=
    (M9Native.LagrangianField.coordinateBasis14 K).repr
      (M9Native.LagrangianField.coordinateProjection K (M9Native.LagrangianField.rowPlucker K M))
  rw [thirdBasis20_eq_field,hrow]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

end M9Native.LagrangianRing
