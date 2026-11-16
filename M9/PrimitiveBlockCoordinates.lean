module

public import M9.PrimitiveStabilizer
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic

/-!
# Actual block action in primitive exterior coordinates

The exterior action is computed on the genuine mixed wedges using their
cyclic cofactor coordinates. It agrees with the fixed symmetric-matrix
representation, and the actual symplectic line quotient is identified with
the two symmetric matrix blocks.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace M9.PrimitiveBlockCoordinates

open Module Matrix ExteriorPrimitive PrimitiveStabilizer
open scoped BigOperators

variable (K : Type*) [Field K]

/-- The actual cyclic two-by-two cofactor with the orientations of q and p. -/
def cyclicCofactor (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) : K :=
  M (nextOne i) (nextOne j) * M (nextTwo i) (nextTwo j) -
    M (nextOne i) (nextTwo j) * M (nextTwo i) (nextOne j)

theorem cyclicCofactor_eq_adjugate (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    cyclicCofactor K M i j = M.adjugate j i := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp [cyclicCofactor,nextOne,nextTwo] <;> ring

theorem sl3_cofactor (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    cyclicCofactor K g.val i j = (g⁻¹).val j i :=
  cyclicCofactor_eq_adjugate K g.val i j

theorem sl3_inverse_transpose_cofactor (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) :
    cyclicCofactor K (g⁻¹).val.transpose i j = g.val i j := by
  rw [cyclicCofactor_eq_adjugate, ← Matrix.adjugate_transpose]
  change ((g⁻¹)⁻¹).val i j = g.val i j
  rw [inv_inv]

@[simp] theorem qCoordinate_block_q (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j k l : Fin 3) :
    qCoordinate K i j (exteriorAction K (block K g) (q K k l)) =
      g.val i k * g.val j l := by
  rw [q,exteriorAction_wedge3,qCoordinate,coordinate_wedge3]
  simp only [block_e_e,block_f_f,block_e_f,block_f_e,mul_zero,zero_mul,
    add_zero,sub_zero]
  calc
    _ = g.val i k * cyclicCofactor K (g⁻¹).val.transpose j l := by
      simp only [cyclicCofactor,Matrix.transpose_apply]
      ring
    _ = _ := by rw [sl3_inverse_transpose_cofactor]

@[simp] theorem pCoordinate_block_p (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j k l : Fin 3) :
    pCoordinate K i j (exteriorAction K (block K g) (p K k l)) =
      (g⁻¹).val k i * (g⁻¹).val l j := by
  rw [p,exteriorAction_wedge3,pCoordinate,coordinate_wedge3]
  simp only [block_e_e,block_f_f,block_e_f,block_f_e,mul_zero,zero_mul,
    add_zero,sub_zero]
  calc
    _ = (g⁻¹).val k i * cyclicCofactor K g.val j l := by
      simp only [cyclicCofactor]
      ring
    _ = _ := by rw [sl3_cofactor]

@[simp] theorem qCoordinate_block_p (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j k l : Fin 3) :
    qCoordinate K i j (exteriorAction K (block K g) (p K k l)) = 0 := by
  simp [p,exteriorAction_wedge3,qCoordinate]

@[simp] theorem pCoordinate_block_q (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j k l : Fin 3) :
    pCoordinate K i j (exteriorAction K (block K g) (q K k l)) = 0 := by
  simp [q,exteriorAction_wedge3,pCoordinate]

@[simp] theorem aCoordinate_block_q (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) : aCoordinate K (exteriorAction K (block K g) (q K i j)) = 0 := by
  rw [q,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K ((block K g).val (e K i)) ((block K g).val (f K (nextOne j)))
      ((block K g).val (f K (nextTwo j)))) = 0
  simp [coordinate_wedge3]

@[simp] theorem aCoordinate_block_p (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) : aCoordinate K (exteriorAction K (block K g) (p K i j)) = 0 := by
  rw [p,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K ((block K g).val (f K i)) ((block K g).val (e K (nextOne j)))
      ((block K g).val (e K (nextTwo j)))) = 0
  simp [coordinate_wedge3]

@[simp] theorem bCoordinate_block_q (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) : bCoordinate K (exteriorAction K (block K g) (q K i j)) = 0 := by
  rw [q,exteriorAction_wedge3]
  change coordinate K (fIndex 0) (fIndex 1) (fIndex 2)
    (wedge3 K ((block K g).val (e K i)) ((block K g).val (f K (nextOne j)))
      ((block K g).val (f K (nextTwo j)))) = 0
  simp [coordinate_wedge3]

@[simp] theorem bCoordinate_block_p (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) : bCoordinate K (exteriorAction K (block K g) (p K i j)) = 0 := by
  rw [p,exteriorAction_wedge3]
  change coordinate K (fIndex 0) (fIndex 1) (fIndex 2)
    (wedge3 K ((block K g).val (f K i)) ((block K g).val (e K (nextOne j)))
      ((block K g).val (e K (nextTwo j)))) = 0
  simp [coordinate_wedge3]

@[simp] theorem aCoordinate_block_embedding (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (r : PrimitiveRepresentation.Coordinates K) :
    aCoordinate K (exteriorAction K (block K g) (coordinateEmbedding K r)) = r.1 := by
  simp [coordinateEmbedding,mixedQ,mixedP]

@[simp] theorem bCoordinate_block_embedding (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (r : PrimitiveRepresentation.Coordinates K) :
    bCoordinate K (exteriorAction K (block K g) (coordinateEmbedding K r)) = r.2.2.2 := by
  simp [coordinateEmbedding,mixedQ,mixedP]

@[simp] theorem qCoordinate_block_embedding (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (r : PrimitiveRepresentation.Coordinates K) (i j : Fin 3) :
    qCoordinate K i j (exteriorAction K (block K g) (coordinateEmbedding K r)) =
      (g.val * r.2.1.val * g.val.transpose) i j := by
  simp only [coordinateEmbedding,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,
    qCoordinate_block_a,qCoordinate_block_b,qCoordinate_block_p,add_zero,zero_add,
    mixedQ,mixedP,map_sum,qCoordinate_block_q,smul_eq_mul,mul_zero,Finset.sum_const_zero]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

@[simp] theorem pCoordinate_block_embedding (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (r : PrimitiveRepresentation.Coordinates K) (i j : Fin 3) :
    pCoordinate K i j (exteriorAction K (block K g) (coordinateEmbedding K r)) =
      ((g⁻¹).val.transpose * r.2.2.1.val * (g⁻¹).val) i j := by
  simp only [coordinateEmbedding,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,
    pCoordinate_block_a,pCoordinate_block_b,pCoordinate_block_q,add_zero,zero_add,
    mixedQ,mixedP,map_sum,pCoordinate_block_p,smul_eq_mul,mul_zero,Finset.sum_const_zero]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The actual block symplectic exterior action equals the fixed coordinate action. -/
theorem primitive_block_covariance [CharZero K]
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (r : PrimitiveRepresentation.Coordinates K) :
    primitiveAction K (block K g) (primitiveEquiv K r) =
      primitiveEquiv K (PrimitiveRepresentation.sl3Action K g r) := by
  apply primitive_ext_upper
  · simp [PrimitiveRepresentation.sl3Action]
  · simp [PrimitiveRepresentation.sl3Action]
  · intro ij
    simp [PrimitiveRepresentation.sl3Action,PrimitiveRepresentation.congruence_val]
  · intro ij
    simp [PrimitiveRepresentation.sl3Action,PrimitiveRepresentation.congruence_val]

theorem exterior_block_covariance [CharZero K]
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (r : PrimitiveRepresentation.Coordinates K) :
    exteriorAction K (block K g) (coordinateEmbedding K r) =
      coordinateEmbedding K (PrimitiveRepresentation.sl3Action K g r) :=
  congrArg Subtype.val (primitive_block_covariance K g r)

section Reduction

variable [CharZero K]

local instance primitiveAddCommGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

abbrev Mixed := Symmetric3 K × Symmetric3 K
abbrev Perp := RadicalFiber.Perp (primitivePairing K) (rhoLine K)

local instance perpAddCommGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

abbrev Inside := RadicalFiber.Inside (primitivePairing K) (rhoLine K)
abbrev Reduced := RadicalFiber.Reduced (primitivePairing K) (rhoLine K)

def rhoCoordinates : PrimitiveRepresentation.Coordinates K := (1,0,0,1)

@[simp] theorem primitiveEquiv_rhoCoordinates : primitiveEquiv K (rhoCoordinates K) = rho K := by
  apply Subtype.ext
  simp [rhoCoordinates,coordinateEmbedding,rho]

theorem mem_perp_coordinates (r : PrimitiveRepresentation.Coordinates K) :
    primitiveEquiv K r ∈ Perp K ↔ r.1 = r.2.2.2 := by
  constructor
  · intro hr
    have h := hr (rho K) (Submodule.mem_span_singleton_self _)
    rw [← primitiveEquiv_rhoCoordinates,primitivePairing_equiv] at h
    have hz : r.2.2.2 - r.1 = 0 := by
      simpa [rhoCoordinates,PrimitiveRepresentation.pairing_apply] using h
    exact (sub_eq_zero.mp hz).symm
  · intro hr y hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul,LinearMap.smul_apply,← primitiveEquiv_rhoCoordinates,primitivePairing_equiv]
    simp [rhoCoordinates,PrimitiveRepresentation.pairing_apply,hr]

/-- Projection of an actual primitive vector to its two symmetric matrix blocks. -/
def mixedProjection : Primitive K →ₗ[K] Mixed K :=
  ((qExtraction K).prod (pExtraction K)).comp (Primitive K).subtype

@[simp] theorem mixedProjection_primitiveEquiv (r : PrimitiveRepresentation.Coordinates K) :
    mixedProjection K (primitiveEquiv K r) = (r.2.1,r.2.2.1) := by
  change (qExtraction K (coordinateEmbedding K r),pExtraction K (coordinateEmbedding K r)) = _
  simp

def perpProjection : Perp K →ₗ[K] Mixed K :=
  (mixedProjection K).comp (Perp K).subtype

/-- The actual mixed exterior vectors provide a section inside the perpendicular. -/
def mixedSection : Mixed K →ₗ[K] Perp K where
  toFun z := ⟨primitiveEquiv K (0,z.1,z.2,0),
    (mem_perp_coordinates K _).mpr rfl⟩
  map_add' x y := by
    apply Subtype.ext
    change primitiveEquiv K (0,x.1+y.1,x.2+y.2,0) =
      primitiveEquiv K (0,x.1,x.2,0) + primitiveEquiv K (0,y.1,y.2,0)
    have h := map_add (primitiveEquiv K) (0,x.1,x.2,0) (0,y.1,y.2,0)
    simp only [Prod.mk_add_mk,zero_add] at h
    exact h
  map_smul' c z := by
    apply Subtype.ext
    change primitiveEquiv K (0,c • z.1,c • z.2,0) = c • primitiveEquiv K (0,z.1,z.2,0)
    have h := map_smul (primitiveEquiv K) c (0,z.1,z.2,0)
    simp only [Prod.smul_mk,smul_zero] at h
    exact h

@[simp] theorem perpProjection_mixedSection (z : Mixed K) :
    perpProjection K (mixedSection K z) = z := by
  change mixedProjection K (primitiveEquiv K (0,z.1,z.2,0)) = z
  rw [mixedProjection_primitiveEquiv]

theorem perpProjection_surjective : Function.Surjective (perpProjection K) :=
  fun z => ⟨mixedSection K z,perpProjection_mixedSection K z⟩

/-- The only perpendicular vectors with zero mixed coordinates are the
actual multiples of the split primitive vector. -/
theorem perpProjection_ker : LinearMap.ker (perpProjection K) = Inside K := by
  ext x
  change mixedProjection K x.val = 0 ↔ x.val ∈ rhoLine K
  obtain ⟨r,hr⟩ := (primitiveEquiv K).surjective x.val
  have hperp : r.1 = r.2.2.2 := (mem_perp_coordinates K r).mp (by rw [hr]; exact x.property)
  rw [← hr,mixedProjection_primitiveEquiv]
  constructor
  · intro hz
    have hX : r.2.1 = 0 := congrArg Prod.fst hz
    have hY : r.2.2.1 = 0 := congrArg Prod.snd hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r.1,?_⟩
    rw [← primitiveEquiv_rhoCoordinates,← map_smul]
    apply congrArg (primitiveEquiv K)
    rcases r with ⟨a,X,Y,b⟩
    simp_all [rhoCoordinates]
  · intro hmem
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h := congrArg (mixedProjection K) hc
    rw [map_smul,← primitiveEquiv_rhoCoordinates,mixedProjection_primitiveEquiv] at h
    simp only [mixedProjection_primitiveEquiv,rhoCoordinates,Prod.smul_mk,smul_zero] at h
    exact h.symm

/-- The actual reduced twelve-dimensional exterior space in its two mixed blocks. -/
def reducedEquiv : Reduced K ≃ₗ[K] Mixed K :=
  (Submodule.quotEquivOfEq (Inside K) (LinearMap.ker (perpProjection K))
    (perpProjection_ker K).symm).trans
    ((perpProjection K).quotKerEquivOfSurjective (perpProjection_surjective K))

@[simp] theorem reducedEquiv_mk (x : Perp K) :
    reducedEquiv K ((Inside K).mkQ x) = perpProjection K x := rfl

@[simp] theorem reducedEquiv_mixedSection (z : Mixed K) :
    reducedEquiv K ((Inside K).mkQ (mixedSection K z)) = z := perpProjection_mixedSection K z

theorem finrank_reduced : finrank K (Reduced K) = 12 := by
  rw [(reducedEquiv K).finrank_eq]
  simp [Mixed,Module.finrank_prod]

def mixedAction (g : Matrix.SpecialLinearGroup (Fin 3) K) : Mixed K →ₗ[K] Mixed K :=
  (PrimitiveRepresentation.congruence K g.val).prodMap
    (PrimitiveRepresentation.congruence K (g⁻¹).val.transpose)

theorem mixedProjection_block (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Primitive K) :
    mixedProjection K (primitiveAction K (block K g) x) = mixedAction K g (mixedProjection K x) := by
  obtain ⟨r,rfl⟩ := (primitiveEquiv K).surjective x
  rw [primitive_block_covariance,mixedProjection_primitiveEquiv,mixedProjection_primitiveEquiv]
  rfl

theorem block_preserves_perp (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Perp K) :
    primitiveAction K (block K g) x.val ∈ Perp K := by
  obtain ⟨r,hr⟩ := (primitiveEquiv K).surjective x.val
  have hp := (mem_perp_coordinates K r).mp (by rw [hr]; exact x.property)
  rw [← hr,primitive_block_covariance]
  exact (mem_perp_coordinates K _).mpr hp

def perpAction (g : Matrix.SpecialLinearGroup (Fin 3) K) : Perp K →ₗ[K] Perp K :=
  ((primitiveAction K (block K g)).comp (Perp K).subtype).codRestrict (Perp K)
    (block_preserves_perp K g)

theorem perpAction_preserves_inside (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Inside K ≤ (Inside K).comap (perpAction K g) := by
  intro x hx
  change x.val ∈ rhoLine K at hx
  change primitiveAction K (block K g) x.val ∈ rhoLine K
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [← hc,map_smul,block_rho]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

/-- The action descends from the actual primitive action on actual quotient classes. -/
def reducedAction (g : Matrix.SpecialLinearGroup (Fin 3) K) : Reduced K →ₗ[K] Reduced K :=
  (Inside K).mapQ (Inside K) (perpAction K g) (perpAction_preserves_inside K g)

theorem reducedEquiv_action (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Reduced K) :
    reducedEquiv K (reducedAction K g x) = mixedAction K g (reducedEquiv K x) := by
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  exact mixedProjection_block K g x.val

theorem reducedForm_mixed (z w : Mixed K) :
    RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)
      ((Inside K).mkQ (mixedSection K z)) ((Inside K).mkQ (mixedSection K w)) =
      PrimitiveRepresentation.tracePair K z.1 w.2 - PrimitiveRepresentation.tracePair K w.1 z.2 := by
  rw [RadicalFiber.reducedForm_mk]
  change primitivePairing K (primitiveEquiv K (0,z.1,z.2,0))
    (primitiveEquiv K (0,w.1,w.2,0)) = _
  rw [primitivePairing_equiv]
  simp [PrimitiveRepresentation.pairingValue,PrimitiveRepresentation.pairing,
    PrimitiveRepresentation.tracePair]

/-- The second symmetric block is the actual dual of the first via trace. -/
def traceDual : Symmetric3 K →ₗ[K] Module.Dual K (Symmetric3 K) where
  toFun Y :=
    { toFun X := PrimitiveRepresentation.tracePair K X Y
      map_add' X Z := by
        simp [PrimitiveRepresentation.tracePair,Matrix.add_mul,Matrix.trace_add]
      map_smul' c X := by
        simp [PrimitiveRepresentation.tracePair] }
  map_add' Y Z := by
    apply LinearMap.ext
    intro X
    simp [PrimitiveRepresentation.tracePair,Matrix.mul_add,Matrix.trace_add]
  map_smul' c Y := by
    apply LinearMap.ext
    intro X
    simp [PrimitiveRepresentation.tracePair]

omit [CharZero K] in
@[simp] theorem traceDual_apply (Y X : Symmetric3 K) :
    traceDual K Y X = PrimitiveRepresentation.tracePair K X Y := rfl

theorem traceDual_injective : Function.Injective (traceDual K) := by
  intro Y Z h
  apply sub_eq_zero.mp
  apply PrimitiveRepresentation.tracePair_separating K (Y-Z)
  intro X
  have hx := LinearMap.congr_fun h X
  rw [traceDual_apply,traceDual_apply] at hx
  rw [PrimitiveRepresentation.tracePair_comm K (Y-Z) X]
  simpa [PrimitiveRepresentation.tracePair,Matrix.mul_sub,Matrix.trace_sub] using sub_eq_zero.mpr hx

def symmetricDualEquiv : Symmetric3 K ≃ₗ[K] Module.Dual K (Symmetric3 K) :=
  (traceDual K).linearEquivOfInjective (traceDual_injective K) (Subspace.dual_finrank_eq).symm

/-- The actual reduced space identified with Q ⊕ Q*, including its duality. -/
def reducedDualEquiv : Reduced K ≃ₗ[K] (Symmetric3 K × Module.Dual K (Symmetric3 K)) :=
  (reducedEquiv K).trans ((LinearEquiv.refl K (Symmetric3 K)).prodCongr (symmetricDualEquiv K))

omit [CharZero K] in
/-- The inverse-transpose block is literally the contragredient action under trace duality. -/
theorem traceDual_action (g : Matrix.SpecialLinearGroup (Fin 3) K) (X Y : Symmetric3 K) :
    traceDual K (PrimitiveRepresentation.congruence K (g⁻¹).val.transpose Y)
      (PrimitiveRepresentation.congruence K g.val X) = traceDual K Y X :=
  PrimitiveRepresentation.tracePair_sl3 K g X Y

omit [CharZero K] in
theorem traceDual_contragredient (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (Y : Symmetric3 K) :
    traceDual K (PrimitiveRepresentation.congruence K (g⁻¹).val.transpose Y) =
      (PrimitiveRepresentation.congruence K (g⁻¹).val).dualMap (traceDual K Y) := by
  apply LinearMap.ext
  intro X
  have h := traceDual_action K g (PrimitiveRepresentation.congruence K (g⁻¹).val X) Y
  have hg : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [← PrimitiveRepresentation.congruence_mul,hg,PrimitiveRepresentation.congruence_one] at h
  exact h

def dualMixedAction (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (Symmetric3 K × Module.Dual K (Symmetric3 K)) →ₗ[K]
      (Symmetric3 K × Module.Dual K (Symmetric3 K)) :=
  (PrimitiveRepresentation.congruence K g.val).prodMap
    (PrimitiveRepresentation.congruence K (g⁻¹).val).dualMap

theorem reducedDualEquiv_action (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Reduced K) :
    reducedDualEquiv K (reducedAction K g x) = dualMixedAction K g (reducedDualEquiv K x) := by
  change ((reducedEquiv K (reducedAction K g x)).1,
      symmetricDualEquiv K (reducedEquiv K (reducedAction K g x)).2) = _
  rw [reducedEquiv_action]
  apply Prod.ext
  · rfl
  · exact traceDual_contragredient K g (reducedEquiv K x).2

/-- The symmetric off-diagonal coordinates retain their actual Gram weight two
in the reduced exterior quotient. -/
theorem reduced_offDiagonal_weight (i j : Fin 3) (hij : i ≠ j) :
    RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)
      ((Inside K).mkQ (mixedSection K (PrimitiveRepresentation.symmetricTest K i j,0)))
      ((Inside K).mkQ (mixedSection K (0,PrimitiveRepresentation.symmetricTest K i j))) = 2 := by
  rw [reducedForm_mixed]
  simp only [PrimitiveRepresentation.tracePair_zero_left,sub_zero]
  rw [PrimitiveRepresentation.tracePair_symmetricTest]
  simp [PrimitiveRepresentation.symmetricTest,hij,Ne.symm hij]

end Reduction

end M9.PrimitiveBlockCoordinates
