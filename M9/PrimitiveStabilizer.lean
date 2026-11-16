module

public import M9.ExteriorPrimitive
public import M9.RadicalFiber
public import M9.PrimitiveEndomorphism
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Determinant

/-!
# Actual symplectic actions at the split primitive vector

The group acts on the actual six-dimensional space and its actual third
exterior power. No stabilizer classification or open-orbit assertion is
included as a premise.
-/

@[expose] public section
noncomputable section
namespace M9.PrimitiveStabilizer
open Module Matrix
open ExteriorPrimitive
variable (K : Type*) [Field K]

/-- The actual symplectic group of the manuscript's six-dimensional form. -/
def symplecticGroup : Subgroup (V K ≃ₗ[K] V K) where
  carrier := {h | ∀ u v, omega K (h u) (h v) = omega K u v}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro h g hh hg u v
    change omega K (h (g u)) (h (g v)) = omega K u v
    rw [hh,hg]
  inv_mem' := by
    intro h hh u v
    have h' := hh (h.symm u) (h.symm v)
    simpa using h'.symm

abbrev Sp6 := symplecticGroup K

@[simp] theorem sp6_omega (h : Sp6 K) (u v : V K) :
    omega K (h.val u) (h.val v) = omega K u v := h.property u v

/-- The genuine exterior representation on Mathlib's third exterior power. -/
def exteriorAction (h : Sp6 K) : Third K →ₗ[K] Third K :=
  exteriorPower.map 3 h.val.toLinearMap

@[simp] theorem exteriorAction_wedge3 (h : Sp6 K) (u v w : V K) :
    exteriorAction K h (wedge3 K u v w) = wedge3 K (h.val u) (h.val v) (h.val w) := by
  simp only [exteriorAction,wedge3,exteriorPower.map_apply_ιMulti,Function.comp_def]
  apply congrArg (exteriorPower.ιMulti K 3)
  funext i
  fin_cases i <;> rfl

/-- Contraction commutes with the actual symplectic action. -/
theorem contraction_natural (h : Sp6 K) :
    (contraction K).comp (exteriorAction K h) = h.val.toLinearMap.comp (contraction K) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change contraction K (exteriorAction K h (exteriorPower.ιMulti K 3 v)) =
    h.val (contraction K (exteriorPower.ιMulti K 3 v))
  simp only [LinearMap.comp_apply,exteriorAction,exteriorPower.map_apply_ιMulti,
    contraction_ιMulti,contractionFormula,tripleContract,Function.comp_apply]
  simp only [LinearEquiv.coe_coe,sp6_omega,map_add,map_sub,map_smul]

@[simp] theorem contraction_exteriorAction (h : Sp6 K) (r : Third K) :
    contraction K (exteriorAction K h r) = h.val (contraction K r) :=
  LinearMap.congr_fun (contraction_natural K h) r

/-- The actual primitive kernel is preserved by the symplectic action. -/
def primitiveAction (h : Sp6 K) : Primitive K →ₗ[K] Primitive K :=
  ((exteriorAction K h).comp (Primitive K).subtype).codRestrict (Primitive K) (by
    intro r
    change contraction K (exteriorAction K h r.val) = 0
    rw [contraction_exteriorAction,show contraction K r.val=0 from r.property,map_zero])

@[simp] theorem primitiveAction_val (h : Sp6 K) (r : Primitive K) :
    (primitiveAction K h r).val = exteriorAction K h r.val := rfl

/-- Splitting into the two actual ordered three-dimensional coordinate summands. -/
def splitV : V K ≃ₗ[K] ((Fin 3 → K) × (Fin 3 → K)) where
  toFun v := (fun i => v (eIndex i),fun i => v (fIndex i))
  invFun v := Fin.append v.1 v.2
  left_inv v := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [eIndex,Fin.append_left]
    · simp only [fIndex,Fin.append_right]
  right_inv v := by
    apply Prod.ext <;> funext i
    · simp only [eIndex,Fin.append_left]
    · simp only [fIndex,Fin.append_right]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem splitV_fst (v : V K) (i : Fin 3) : (splitV K v).1 i = v (eIndex i) := rfl
@[simp] theorem splitV_snd (v : V K) (i : Fin 3) : (splitV K v).2 i = v (fIndex i) := rfl

/-- The actual alternating form in its split dot-product coordinates. -/
theorem omega_split (u v : V K) :
    omega K u v = (splitV K u).1 ⬝ᵥ (splitV K v).2 -
      (splitV K u).2 ⬝ᵥ (splitV K v).1 := by
  simp only [omega_apply,omegaValue,dotProduct,splitV_fst,splitV_snd,Finset.sum_sub_distrib]

/-- The actual block diagonal equivalence `diag(g,g⁻ᵀ)`. -/
def blockLinear (g : Matrix.SpecialLinearGroup (Fin 3) K) : V K ≃ₗ[K] V K :=
  (splitV K).trans ((g.toLin').prodCongr ((g⁻¹).transpose.toLin')) |>.trans (splitV K).symm

@[simp] theorem blockLinear_split (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : V K) :
    splitV K (blockLinear K g v) =
      (g.val *ᵥ (splitV K v).1,(g⁻¹).val.transpose *ᵥ (splitV K v).2) := by
  simp only [blockLinear,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    LinearEquiv.prodCongr_apply,Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply]
  rfl

theorem blockLinear_dot (g : Matrix.SpecialLinearGroup (Fin 3) K) (u v : Fin 3 → K) :
    (g.val *ᵥ u) ⬝ᵥ ((g⁻¹).val.transpose *ᵥ v) = u ⬝ᵥ v := by
  have h : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,h,Matrix.one_mulVec,dotProduct_comm]

/-- The actual connected block embedding takes values in the symplectic group. -/
def block (g : Matrix.SpecialLinearGroup (Fin 3) K) : Sp6 K :=
  ⟨blockLinear K g,by
    intro u v
    rw [omega_split,omega_split,blockLinear_split,blockLinear_split]
    change (g.val *ᵥ (splitV K u).1) ⬝ᵥ ((g⁻¹).val.transpose *ᵥ (splitV K v).2) -
      ((g⁻¹).val.transpose *ᵥ (splitV K u).2) ⬝ᵥ (g.val *ᵥ (splitV K v).1) = _
    rw [blockLinear_dot,dotProduct_comm ((g⁻¹).val.transpose *ᵥ (splitV K u).2),
      blockLinear_dot,dotProduct_comm ((splitV K v).1)]⟩

@[simp] theorem exteriorAction_one : exteriorAction K 1 = LinearMap.id :=
  exteriorPower.map_id

theorem exteriorAction_mul (h g : Sp6 K) :
    exteriorAction K (h*g) = (exteriorAction K h).comp (exteriorAction K g) := by
  change exteriorPower.map 3 (h.val.toLinearMap.comp g.val.toLinearMap) = _
  exact exteriorPower.map_comp _ _

/-- A genuine representation of the actual symplectic group on the third exterior power. -/
def exteriorRepresentation : Sp6 K →* Module.End K (Third K) where
  toFun := exteriorAction K
  map_one' := exteriorAction_one K
  map_mul' := exteriorAction_mul K

@[simp] theorem primitiveAction_one : primitiveAction K 1 = LinearMap.id := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  exact LinearMap.congr_fun (exteriorAction_one K) r.val

theorem primitiveAction_mul (h g : Sp6 K) :
    primitiveAction K (h*g) = (primitiveAction K h).comp (primitiveAction K g) := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  exact LinearMap.congr_fun (exteriorAction_mul K h g) r.val

/-- The actual primitive action is invertible, with inverse given by the group inverse. -/
def primitiveLinear (h : Sp6 K) : Primitive K ≃ₗ[K] Primitive K :=
  LinearEquiv.ofLinearMap (primitiveAction K h) (primitiveAction K h⁻¹)
    (by rw [← primitiveAction_mul,mul_inv_cancel,primitiveAction_one])
    (by rw [← primitiveAction_mul,inv_mul_cancel,primitiveAction_one])

/-- The genuine group representation on the primitive exterior kernel. -/
def primitiveRepresentation : Sp6 K →* (Primitive K ≃ₗ[K] Primitive K) where
  toFun := primitiveLinear K
  map_one' := LinearEquiv.toLinearMap_injective (primitiveAction_one K)
  map_mul' h g := LinearEquiv.toLinearMap_injective (primitiveAction_mul K h g)

@[simp] theorem splitV_e (i : Fin 3) : splitV K (e K i) = (Pi.single i 1,0) := by
  apply Prod.ext <;> funext j <;> fin_cases i <;> fin_cases j <;>
    norm_num [splitV,e,basisVector,eIndex,fIndex,Pi.single_apply]

@[simp] theorem splitV_f (i : Fin 3) : splitV K (f K i) = (0,Pi.single i 1) := by
  apply Prod.ext <;> funext j <;> fin_cases i <;> fin_cases j <;>
    norm_num [splitV,f,basisVector,eIndex,fIndex,Pi.single_apply]

@[simp] theorem block_e_e (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (block K g).val (e K i) (eIndex j) = g.val j i := by
  change (splitV K (blockLinear K g (e K i))).1 j = _
  rw [blockLinear_split,splitV_e]
  exact congrFun (Matrix.mulVec_single_one g.val i) j

@[simp] theorem block_e_f (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (block K g).val (e K i) (fIndex j) = 0 := by
  change (splitV K (blockLinear K g (e K i))).2 j = _
  rw [blockLinear_split,splitV_e]
  simp

@[simp] theorem block_f_e (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (block K g).val (f K i) (eIndex j) = 0 := by
  change (splitV K (blockLinear K g (f K i))).1 j = _
  rw [blockLinear_split,splitV_f]
  simp

@[simp] theorem block_f_f (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (block K g).val (f K i) (fIndex j) = (g⁻¹).val i j := by
  change (splitV K (blockLinear K g (f K i))).2 j = _
  rw [blockLinear_split,splitV_f]
  exact congrFun (Matrix.mulVec_single_one (g⁻¹).val.transpose i) j

theorem block_injective : Function.Injective (block K) := by
  intro g h hgh
  apply Subtype.ext
  funext j i
  have heq := congrArg (fun z : Sp6 K => z.val (e K i) (eIndex j)) hgh
  simpa only [block_e_e] using heq

/-- The actual exchange of the two three-dimensional summands. -/
def switchV : V K ≃ₗ[K] V K :=
  (splitV K).trans (LinearEquiv.prodComm K (Fin 3 → K) (Fin 3 → K)) |>.trans (splitV K).symm

@[simp] theorem switchV_split (v : V K) :
    splitV K (switchV K v) = ((splitV K v).2,(splitV K v).1) := by
  simp [switchV]
  rfl

@[simp] theorem switchV_switchV (v : V K) : switchV K (switchV K v) = v := by
  apply (splitV K).injective
  simp

theorem omega_switchV (u v : V K) : omega K (switchV K u) (switchV K v) = -omega K u v := by
  rw [omega_split,omega_split,switchV_split,switchV_split]
  change (splitV K u).2 ⬝ᵥ (splitV K v).1 - (splitV K u).1 ⬝ᵥ (splitV K v).2 = _
  ring

theorem square_neg_one_ne_zero (i : K) (hi : i^2 = -1) : i ≠ 0 := by
  intro hi0
  simpa [hi0] using hi

/-- The literal exchanging lift, `e_i ↦ i f_i`, `f_i ↦ i e_i`. -/
def exchanging (i : K) (hi : i^2 = -1) : Sp6 K :=
  ⟨(switchV K).trans (LinearEquiv.smulOfNeZero K (V K) i (square_neg_one_ne_zero K i hi)),by
    intro u v
    change omega K (i • switchV K u) (i • switchV K v) = omega K u v
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [omega_switchV]
    calc
      i * (i * -omega K u v) = -(i^2) * omega K u v := by ring
      _ = _ := by rw [hi]; ring⟩

@[simp] theorem exchanging_apply (i : K) (hi : i^2 = -1) (v : V K) :
    (exchanging K i hi).val v = i • switchV K v := rfl

@[simp] theorem switchV_e (i : Fin 3) : switchV K (e K i) = f K i := by
  apply (splitV K).injective
  simp

@[simp] theorem switchV_f (i : Fin 3) : switchV K (f K i) = e K i := by
  apply (splitV K).injective
  simp

@[simp] theorem exchanging_e (i : K) (hi : i^2 = -1) (j : Fin 3) :
    (exchanging K i hi).val (e K j) = i • f K j := by simp

@[simp] theorem exchanging_f (i : K) (hi : i^2 = -1) (j : Fin 3) :
    (exchanging K i hi).val (f K j) = i • e K j := by simp

/-- The actual central sign transformation. -/
def negativeIdentity : Sp6 K := ⟨LinearEquiv.neg K,by
  intro u v
  change omega K (-u) (-v) = omega K u v
  simp only [map_neg,LinearMap.neg_apply,neg_neg]⟩

@[simp] theorem negativeIdentity_apply (v : V K) : (negativeIdentity K).val v = -v := rfl

theorem exchanging_square (i : K) (hi : i^2 = -1) :
    exchanging K i hi * exchanging K i hi = negativeIdentity K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change i • switchV K (i • switchV K v) = -v
  rw [map_smul,switchV_switchV,smul_smul,← pow_two,hi,neg_one_smul]

/-- The actual symplectic basis, with the two summands kept visibly distinct. -/
def splitBasis : Basis (Fin 3 ⊕ Fin 3) K (V K) :=
  (Pi.basisFun K (Fin 3 ⊕ Fin 3)).map
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) K K).trans (splitV K).symm)

@[simp] theorem splitBasis_inl (i : Fin 3) : splitBasis K (Sum.inl i) = e K i := by
  apply (splitV K).injective
  simp only [splitBasis,Basis.map_apply,Pi.basisFun_apply,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply,splitV_e]
  apply Prod.ext <;> funext j <;>
    simp [LinearEquiv.sumArrowLequivProdArrow,Pi.single_apply]

@[simp] theorem splitBasis_inr (i : Fin 3) : splitBasis K (Sum.inr i) = f K i := by
  apply (splitV K).injective
  simp only [splitBasis,Basis.map_apply,Pi.basisFun_apply,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply,splitV_f]
  apply Prod.ext <;> funext j <;>
    simp [LinearEquiv.sumArrowLequivProdArrow,Pi.single_apply]

/-- Mathlib's canonical `J` has the opposite sign to the manuscript's form. -/
theorem omega_matrix : LinearMap.BilinForm.toMatrix (splitBasis K) (omega K) = -Matrix.J (Fin 3) K := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply,Matrix.J,Matrix.fromBlocks,Matrix.one_apply,
      neg_ite,neg_neg,-omega_apply,-omega_pair_e,-omega_pair_f]

/-- The actual matrix of a six-dimensional symplectic transformation is symplectic. -/
theorem symplectic_matrix (h : Sp6 K) :
    LinearMap.toMatrix (splitBasis K) (splitBasis K) h.val.toLinearMap ∈
      Matrix.symplecticGroup (Fin 3) K := by
  have hf : (omega K).comp h.val.toLinearMap h.val.toLinearMap = omega K := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact h.property u v
  have hm := congrArg (LinearMap.BilinForm.toMatrix (splitBasis K)) hf
  rw [LinearMap.BilinForm.toMatrix_comp (b := splitBasis K) (c := splitBasis K),omega_matrix] at hm
  apply SymplecticGroup.mem_iff'.mpr
  simpa only [Matrix.mul_neg,Matrix.neg_mul,neg_inj] using hm

/-- Every actual symplectic transformation has determinant one. -/
theorem symplectic_det_one (h : Sp6 K) : LinearMap.det h.val.toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix (splitBasis K)]
  exact SymplecticGroup.det_eq_one (symplectic_matrix K h)

@[simp] theorem blockLinear_one (v : V K) : blockLinear K 1 v = v := by
  apply (splitV K).injective
  simp [blockLinear_split]

theorem blockLinear_mul (g h : Matrix.SpecialLinearGroup (Fin 3) K) (v : V K) :
    blockLinear K (g*h) v = blockLinear K g (blockLinear K h v) := by
  apply (splitV K).injective
  have hmul : (g*h).val = g.val*h.val := rfl
  have hinv : ((g*h)⁻¹).val = (h⁻¹).val*(g⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  simp only [blockLinear_split,hmul,hinv,Matrix.transpose_mul,Matrix.mulVec_mulVec]

/-- The connected block inclusion is a genuine injective group homomorphism. -/
def blockHom : Matrix.SpecialLinearGroup (Fin 3) K →* Sp6 K where
  toFun := block K
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_one K
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_mul K g h

theorem blockHom_injective : Function.Injective (blockHom K) := block_injective K

/-- The actual exchanging lift conjugates the connected blocks by inverse transpose. -/
theorem exchanging_block (i : K) (hi : i^2 = -1) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    exchanging K i hi * block K g =
      block K (PrimitiveRepresentation.inverseTranspose K g) * exchanging K i hi := by
  have ht : ((PrimitiveRepresentation.inverseTranspose K g)⁻¹).val.transpose = g.val := by
    rw [PrimitiveRepresentation.inverseTranspose_inv]
    exact Matrix.transpose_transpose _
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply (splitV K).injective
  change splitV K (i • switchV K (blockLinear K g v)) =
    splitV K (blockLinear K (PrimitiveRepresentation.inverseTranspose K g) (i • switchV K v))
  rw [map_smul,switchV_split,blockLinear_split,blockLinear_split,map_smul,switchV_split]
  simp only [PrimitiveRepresentation.inverseTranspose_val,ht]
  change (i • ((g⁻¹).val.transpose *ᵥ (splitV K v).2), i • (g.val *ᵥ (splitV K v).1)) =
    ((g⁻¹).val.transpose *ᵥ (i • (splitV K v).2),g.val *ᵥ (i • (splitV K v).1))
  simp only [Matrix.mulVec_smul]

/-- The central sign acts by the odd exterior sign on the actual third exterior power. -/
theorem exteriorAction_negativeIdentity :
    exteriorAction K (negativeIdentity K) = -LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply,exteriorAction,exteriorPower.map_apply_ιMulti,
    Function.comp_apply,LinearEquiv.coe_coe,negativeIdentity_apply,LinearMap.neg_apply,LinearMap.id_apply]
  change exteriorPower.ιMulti K 3 (fun j => -v j) = -(exteriorPower.ιMulti K 3 v)
  have h := (exteriorPower.ιMulti K 3).map_smul_univ (fun _ => (-1 : K)) v
  simpa [show (-1 : K)^3 = -1 by ring] using h

/-- The split vector is an element of the actual primitive kernel. -/
def rho : Primitive K := ⟨a K+b K,by change contraction K (a K+b K)=0; simp⟩

@[simp] theorem rho_val : (rho K).val = a K+b K := rfl

theorem rho_ne_zero : rho K ≠ 0 := by
  intro h
  have hc := congrArg (fun r : Primitive K => aCoordinate K r.val) h
  simpa [rho] using hc

/-- The actual one-dimensional primitive submodule spanned by the split vector. -/
def rhoLine : Submodule K (Primitive K) := K ∙ rho K

/-- The actual line of the split primitive vector. -/
def rhoProjective : Projectivization K (Primitive K) :=
  Projectivization.mk K (rho K) (rho_ne_zero K)

/-- The actual projective action induced by the genuine primitive representation. -/
def projectiveAction : Sp6 K →* Equiv.Perm (Projectivization K (Primitive K)) :=
  (MulAction.toPermHom (Primitive K ≃ₗ[K] Primitive K)
    (Projectivization K (Primitive K))).comp (primitiveRepresentation K)

/-- The actual line stabilizer, before quotienting by the central sign. -/
def lineStabilizer : Subgroup (Sp6 K) :=
  (MulAction.stabilizer (Equiv.Perm (Projectivization K (Primitive K))) (rhoProjective K)).comap
    (projectiveAction K)

/-- Scaling all three actual wedge factors multiplies by the cube. -/
theorem wedge3_smul (c : K) (u v w : V K) :
    wedge3 K (c • u) (c • v) (c • w) = c^3 • wedge3 K u v w := by
  unfold wedge3
  have hv : (![c • u,c • v,c • w] : Fin 3 → V K) = (fun j => c • (![u,v,w] : Fin 3 → V K) j) := by
    funext j
    fin_cases j <;> rfl
  rw [hv,AlternatingMap.map_smul_univ]
  simp [Fin.prod_univ_succ,pow_succ,mul_assoc]

theorem cube_of_square_neg_one (i : K) (hi : i^2 = -1) : i^3 = -i := by
  calc
    i^3 = i^2 * i := by ring
    _ = -i := by rw [hi,neg_one_mul]

@[simp] theorem exchanging_a (i : K) (hi : i^2 = -1) :
    exteriorAction K (exchanging K i hi) (a K) = (-i) • b K := by
  rw [a,exteriorAction_wedge3,exchanging_e,exchanging_e,exchanging_e,wedge3_smul,
    cube_of_square_neg_one K i hi]
  rfl

@[simp] theorem exchanging_b (i : K) (hi : i^2 = -1) :
    exteriorAction K (exchanging K i hi) (b K) = (-i) • a K := by
  rw [b,exteriorAction_wedge3,exchanging_f,exchanging_f,exchanging_f,wedge3_smul,
    cube_of_square_neg_one K i hi]
  rfl

@[simp] theorem exchanging_q (i : K) (hi : i^2 = -1) (j k : Fin 3) :
    exteriorAction K (exchanging K i hi) (q K j k) = (-i) • p K j k := by
  rw [q,exteriorAction_wedge3,exchanging_e,exchanging_f,exchanging_f,wedge3_smul,
    cube_of_square_neg_one K i hi]
  rfl

@[simp] theorem exchanging_p (i : K) (hi : i^2 = -1) (j k : Fin 3) :
    exteriorAction K (exchanging K i hi) (p K j k) = (-i) • q K j k := by
  rw [p,exteriorAction_wedge3,exchanging_f,exchanging_e,exchanging_e,wedge3_smul,
    cube_of_square_neg_one K i hi]
  rfl

theorem exchanging_rho (i : K) (hi : i^2 = -1) :
    primitiveAction K (exchanging K i hi) (rho K) = (-i) • rho K := by
  apply Subtype.ext
  change exteriorAction K (exchanging K i hi) (a K+b K) = (-i) • (a K+b K)
  rw [map_add,exchanging_a,exchanging_b,smul_add,add_comm]

theorem exchanging_mixedQ (i : K) (hi : i^2 = -1) (X : Matrix (Fin 3) (Fin 3) K) :
    exteriorAction K (exchanging K i hi) (mixedQ K X) = (-i) • mixedP K X := by
  simp [mixedQ,mixedP,Finset.smul_sum,smul_smul,mul_comm]

theorem exchanging_mixedP (i : K) (hi : i^2 = -1) (Y : Matrix (Fin 3) (Fin 3) K) :
    exteriorAction K (exchanging K i hi) (mixedP K Y) = (-i) • mixedQ K Y := by
  simp [mixedQ,mixedP,Finset.smul_sum,smul_smul,mul_comm]

/-- The literal exterior action is minus-i times the coordinate swap. -/
theorem exchanging_coordinateEmbedding (i : K) (hi : i^2 = -1)
    (r : PrimitiveRepresentation.Coordinates K) :
    exteriorAction K (exchanging K i hi) (coordinateEmbedding K r) =
      (-i) • coordinateEmbedding K (PrimitiveRepresentation.swap K r) := by
  change exteriorAction K (exchanging K i hi)
    (r.1 • a K + mixedQ K r.2.1.val + mixedP K r.2.2.1.val + r.2.2.2 • b K) =
    (-i) • (r.2.2.2 • a K + mixedQ K r.2.2.1.val + mixedP K r.2.1.val + r.1 • b K)
  simp only [map_add,map_smul,exchanging_a,exchanging_b,exchanging_mixedQ,exchanging_mixedP]
  module

/-- The inverse line character i cancels the raw -i, giving the stated twisted swap. -/
theorem twisted_exchanging_coordinateEmbedding (i : K) (hi : i^2 = -1)
    (r : PrimitiveRepresentation.Coordinates K) :
    i • exteriorAction K (exchanging K i hi) (coordinateEmbedding K r) =
      coordinateEmbedding K (PrimitiveRepresentation.swap K r) := by
  rw [exchanging_coordinateEmbedding,smul_smul]
  have hc : i * -i = 1 := by rw [mul_neg,← pow_two,hi,neg_neg]
  rw [hc,one_smul]

@[simp] theorem aCoordinate_block_a (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    aCoordinate K (exteriorAction K (block K g) (a K)) = 1 := by
  rw [a,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K ((block K g).val (e K 0)) ((block K g).val (e K 1)) ((block K g).val (e K 2))) = 1
  rw [coordinate_wedge3]
  simp only [block_e_e]
  calc
    _ = g.val.det := by rw [Matrix.det_fin_three]; ring
    _ = 1 := g.property

@[simp] theorem bCoordinate_block_a (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    bCoordinate K (exteriorAction K (block K g) (a K)) = 0 := by
  rw [a,exteriorAction_wedge3]
  change coordinate K (fIndex 0) (fIndex 1) (fIndex 2)
    (wedge3 K ((block K g).val (e K 0)) ((block K g).val (e K 1)) ((block K g).val (e K 2))) = 0
  simp [coordinate_wedge3]

@[simp] theorem aCoordinate_block_b (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    aCoordinate K (exteriorAction K (block K g) (b K)) = 0 := by
  rw [b,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K ((block K g).val (f K 0)) ((block K g).val (f K 1)) ((block K g).val (f K 2))) = 0
  simp [coordinate_wedge3]

@[simp] theorem bCoordinate_block_b (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    bCoordinate K (exteriorAction K (block K g) (b K)) = 1 := by
  rw [b,exteriorAction_wedge3]
  change coordinate K (fIndex 0) (fIndex 1) (fIndex 2)
    (wedge3 K ((block K g).val (f K 0)) ((block K g).val (f K 1)) ((block K g).val (f K 2))) = 1
  rw [coordinate_wedge3]
  simp only [block_f_f]
  calc
    _ = (g⁻¹).val.det := by rw [Matrix.det_fin_three]; ring
    _ = 1 := (g⁻¹).property

@[simp] theorem qCoordinate_block_a (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    qCoordinate K i j (exteriorAction K (block K g) (a K)) = 0 := by
  simp [qCoordinate,a,exteriorAction_wedge3]

@[simp] theorem pCoordinate_block_a (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    pCoordinate K i j (exteriorAction K (block K g) (a K)) = 0 := by
  simp [pCoordinate,a,exteriorAction_wedge3]

@[simp] theorem qCoordinate_block_b (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    qCoordinate K i j (exteriorAction K (block K g) (b K)) = 0 := by
  simp [qCoordinate,b,exteriorAction_wedge3]

@[simp] theorem pCoordinate_block_b (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    pCoordinate K i j (exteriorAction K (block K g) (b K)) = 0 := by
  simp [pCoordinate,b,exteriorAction_wedge3]

/-- The preserving blocks really fix the split vector, not just its coordinate surrogate. -/
theorem block_rho [CharZero K] (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    primitiveAction K (block K g) (rho K) = rho K := by
  apply primitive_ext_upper
  · simp [rho,primitiveAction_val]
  · simp [rho,primitiveAction_val]
  · intro ij
    simp [rho,primitiveAction_val]
  · intro ij
    simp [rho,primitiveAction_val]

/-- The actual projective stabilizer criterion is ordinary nonzero proportionality. -/
theorem mem_lineStabilizer_iff (h : Sp6 K) : h ∈ lineStabilizer K ↔
    ∃ c : K, c ≠ 0 ∧ primitiveAction K h (rho K) = c • rho K := by
  change primitiveRepresentation K h • rhoProjective K = rhoProjective K ↔ _
  rw [rhoProjective,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c.val,c.ne_zero,hc.symm⟩
  · rintro ⟨c,hc,heq⟩
    exact ⟨Units.mk0 c hc,heq.symm⟩

theorem block_mem_lineStabilizer [CharZero K] (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    block K g ∈ lineStabilizer K := by
  apply (mem_lineStabilizer_iff K _).mpr
  exact ⟨1,one_ne_zero,by rw [block_rho,one_smul]⟩

theorem exchanging_mem_lineStabilizer (i : K) (hi : i^2 = -1) :
    exchanging K i hi ∈ lineStabilizer K := by
  apply (mem_lineStabilizer_iff K _).mpr
  exact ⟨-i,neg_ne_zero.mpr (square_neg_one_ne_zero K i hi),exchanging_rho K i hi⟩

end M9.PrimitiveStabilizer
