module

public import M9.PrimitiveBlockCoordinates
public import M9.PrimitiveProjectiveAction

/-!
# The actual line-character-twisted reduced stabilizer representation

The action on the actual quotient `rhoᗮ/rho` is induced from the exterior
representation. Multiplication by the inverse of the actual character on
`rho` is a representation and kills the global central sign. Under the
proved mixed-coordinate equivalence its connected action is the two matrix
congruences and its exchanging generator is the plain swap.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace M9.PrimitiveTwistedReduced

open Module Matrix ExteriorPrimitive PrimitiveStabilizer PrimitiveBlockCoordinates
open scoped Classical

variable (K : Type*) [Field K] [CharZero K]

local instance primitiveAddCommGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

local instance perpAddCommGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

/-- The exchanging covariance is for the actual primitive kernel. -/
theorem primitive_exchanging (i : K) (hi : i^2 = -1)
    (r : PrimitiveRepresentation.Coordinates K) :
    PrimitiveStabilizer.primitiveAction K (exchanging K i hi) (primitiveEquiv K r) =
      (-i) • primitiveEquiv K (PrimitiveRepresentation.swap K r) := by
  apply Subtype.ext
  exact exchanging_coordinateEmbedding K i hi r

omit [CharZero K] in
@[simp] theorem primitive_negativeIdentity (x : Primitive K) :
    PrimitiveStabilizer.primitiveAction K (negativeIdentity K) x = -x := by
  apply Subtype.ext
  change exteriorAction K (negativeIdentity K) x.val = -x.val
  rw [exteriorAction_negativeIdentity]
  rfl

theorem exchanging_preserves_perp (i : K) (hi : i^2 = -1) (x : Perp K) :
    PrimitiveStabilizer.primitiveAction K (exchanging K i hi) x.val ∈ Perp K := by
  obtain ⟨r, hr⟩ := (primitiveEquiv K).surjective x.val
  have hp := (mem_perp_coordinates K r).mp (by rw [hr]; exact x.property)
  rw [← hr, primitive_exchanging]
  apply Submodule.smul_mem
  exact (mem_perp_coordinates K _).mpr hp.symm

omit [CharZero K] in
theorem negativeIdentity_preserves_perp (x : Perp K) :
    PrimitiveStabilizer.primitiveAction K (negativeIdentity K) x.val ∈ Perp K := by
  rw [primitive_negativeIdentity]
  exact Submodule.neg_mem _ x.property

omit [CharZero K] in
theorem mul_preserves_perp (h g : Sp6 K)
    (hh : ∀ x : Perp K, PrimitiveStabilizer.primitiveAction K h x.val ∈ Perp K)
    (hg : ∀ x : Perp K, PrimitiveStabilizer.primitiveAction K g x.val ∈ Perp K)
    (x : Perp K) :
    PrimitiveStabilizer.primitiveAction K (h*g) x.val ∈ Perp K := by
  rw [PrimitiveStabilizer.primitiveAction_mul]
  exact hh ⟨_, hg x⟩

/-- Preservation is proved from the four actual normal forms, not assumed. -/
theorem stabilizer_preserves_perp (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Perp K) :
    PrimitiveStabilizer.primitiveAction K h.val x.val ∈ Perp K := by
  obtain ⟨g, hh | hh | hh | hh⟩ := stabilizer_normalForms K i hi h.val h.property
  · rw [hh]
    exact block_preserves_perp K g x
  · rw [hh]
    exact mul_preserves_perp K _ _ (negativeIdentity_preserves_perp K)
      (block_preserves_perp K g) x
  · rw [hh]
    exact mul_preserves_perp K _ _ (exchanging_preserves_perp K i hi)
      (block_preserves_perp K g) x
  · rw [hh]
    exact mul_preserves_perp K _ _
      (mul_preserves_perp K _ _ (negativeIdentity_preserves_perp K)
        (exchanging_preserves_perp K i hi)) (block_preserves_perp K g) x

/-- Restriction of the actual exterior action to the actual perpendicular. -/
def rawPerpAction (i : K) (hi : i^2 = -1) (h : lineStabilizer K) :
    Perp K →ₗ[K] Perp K :=
  ((PrimitiveStabilizer.primitiveAction K h.val).comp (Perp K).subtype).codRestrict
    (Perp K) (stabilizer_preserves_perp K i hi h)

theorem rawPerpAction_preserves_inside (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) : Inside K ≤ (Inside K).comap (rawPerpAction K i hi h) := by
  intro x hx
  change x.val ∈ rhoLine K at hx
  change PrimitiveStabilizer.primitiveAction K h.val x.val ∈ rhoLine K
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [← hc, map_smul, (lineScalar_spec K h).2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.mem_span_singleton_self _))

/-- The untwisted action is induced on genuine quotient classes. -/
def rawReducedAction (i : K) (hi : i^2 = -1) (h : lineStabilizer K) :
    Reduced K →ₗ[K] Reduced K :=
  (Inside K).mapQ (Inside K) (rawPerpAction K i hi h)
    (rawPerpAction_preserves_inside K i hi h)

@[simp] theorem rawReducedAction_mk (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Perp K) :
    rawReducedAction K i hi h ((Inside K).mkQ x) =
      (Inside K).mkQ (rawPerpAction K i hi h x) := rfl

@[simp] theorem rawReducedAction_one (i : K) (hi : i^2 = -1) :
    rawReducedAction K i hi 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  change (Inside K).mkQ (rawPerpAction K i hi 1 x) = (Inside K).mkQ x
  apply congrArg (Inside K).mkQ
  apply Subtype.ext
  exact LinearMap.congr_fun (PrimitiveStabilizer.primitiveAction_one K) x.val

theorem rawReducedAction_mul (i : K) (hi : i^2 = -1) (h g : lineStabilizer K) :
    rawReducedAction K i hi (h*g) =
      (rawReducedAction K i hi h).comp (rawReducedAction K i hi g) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  change (Inside K).mkQ (rawPerpAction K i hi (h*g) x) =
    (Inside K).mkQ (rawPerpAction K i hi h (rawPerpAction K i hi g x))
  apply congrArg (Inside K).mkQ
  apply Subtype.ext
  exact LinearMap.congr_fun (PrimitiveStabilizer.primitiveAction_mul K h.val g.val) x.val

/-- A genuine representation before the character twist. -/
def rawReducedRepresentation (i : K) (hi : i^2 = -1) :
    lineStabilizer K →* Module.End K (Reduced K) where
  toFun := rawReducedAction K i hi
  map_one' := rawReducedAction_one K i hi
  map_mul' := rawReducedAction_mul K i hi

/-- The inverse of the actual primitive-line character, as a scalar. -/
def twistScalar (h : lineStabilizer K) : K := ((lineCharacter K h)⁻¹ : Kˣ).val

@[simp] theorem twistScalar_one : twistScalar K 1 = 1 := by
  simp [twistScalar]

theorem twistScalar_mul (h g : lineStabilizer K) :
    twistScalar K (h*g) = twistScalar K h * twistScalar K g := by
  simp [twistScalar, mul_comm]

@[simp] theorem twistScalar_block (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    twistScalar K (blockStabilizerHom K g) = 1 := by
  simp [twistScalar, lineCharacter]

@[simp] theorem twistScalar_centralSign : twistScalar K (centralSign K) = -1 := by
  simp [twistScalar, lineCharacter]

@[simp] theorem twistScalar_swapping (i : K) (hi : i^2 = -1) :
    twistScalar K (swappingElement K i hi) = i := by
  apply Units.inv_eq_of_mul_eq_one_right
  change lineScalar K (swappingElement K i hi) * i = 1
  rw [lineScalar_swapping, neg_mul, ← pow_two, hi, neg_neg]

/-- The scalar twist models tensoring the reduced quotient with the dual line. -/
def twistedReducedAction (i : K) (hi : i^2 = -1) (h : lineStabilizer K) :
    Reduced K →ₗ[K] Reduced K := twistScalar K h • rawReducedAction K i hi h

@[simp] theorem twistedReducedAction_apply (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Reduced K) :
    twistedReducedAction K i hi h x = twistScalar K h • rawReducedAction K i hi h x := rfl

@[simp] theorem twistedReducedAction_one (i : K) (hi : i^2 = -1) :
    twistedReducedAction K i hi 1 = LinearMap.id := by
  simp [twistedReducedAction]

theorem twistedReducedAction_mul (i : K) (hi : i^2 = -1) (h g : lineStabilizer K) :
    twistedReducedAction K i hi (h*g) =
      (twistedReducedAction K i hi h).comp (twistedReducedAction K i hi g) := by
  ext x
  simp [twistedReducedAction, rawReducedAction_mul, twistScalar_mul, smul_smul]

/-- The actual inverse-character twist is a group representation by linear maps. -/
def twistedReducedRepresentation (i : K) (hi : i^2 = -1) :
    lineStabilizer K →* Module.End K (Reduced K) where
  toFun := twistedReducedAction K i hi
  map_one' := twistedReducedAction_one K i hi
  map_mul' := twistedReducedAction_mul K i hi

@[simp] theorem rawReducedAction_block (i : K) (hi : i^2 = -1)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    rawReducedAction K i hi (blockStabilizerHom K g) = reducedAction K g := rfl

theorem mixedProjection_exchanging (i : K) (hi : i^2 = -1) (x : Primitive K) :
    mixedProjection K (PrimitiveStabilizer.primitiveAction K (exchanging K i hi) x) =
      (-i) • (LinearEquiv.prodComm K (Symmetric3 K) (Symmetric3 K)) (mixedProjection K x) := by
  obtain ⟨r, rfl⟩ := (primitiveEquiv K).surjective x
  rw [primitive_exchanging, map_smul, mixedProjection_primitiveEquiv,
    mixedProjection_primitiveEquiv]
  rfl

theorem reducedEquiv_raw_swapping (i : K) (hi : i^2 = -1) (x : Reduced K) :
    reducedEquiv K (rawReducedAction K i hi (swappingElement K i hi) x) =
      (-i) • (LinearEquiv.prodComm K (Symmetric3 K) (Symmetric3 K)) (reducedEquiv K x) := by
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  exact mixedProjection_exchanging K i hi x.val

@[simp] theorem rawReducedAction_centralSign (i : K) (hi : i^2 = -1) (x : Reduced K) :
    rawReducedAction K i hi (centralSign K) x = -x := by
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  change (Inside K).mkQ (rawPerpAction K i hi (centralSign K) x) =
    -(Inside K).mkQ x
  rw [← map_neg]
  apply congrArg (Inside K).mkQ
  apply Subtype.ext
  exact primitive_negativeIdentity K x.val

/-- Connected equivariance for the genuine character-twisted quotient action. -/
theorem reducedEquiv_twisted_block (i : K) (hi : i^2 = -1)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Reduced K) :
    reducedEquiv K (twistedReducedAction K i hi (blockStabilizerHom K g) x) =
      mixedAction K g (reducedEquiv K x) := by
  simp only [twistedReducedAction_apply, twistScalar_block, one_smul,
    rawReducedAction_block, reducedEquiv_action]

/-- The inverse line character cancels the raw minus-i on the quotient. -/
theorem reducedEquiv_twisted_swapping (i : K) (hi : i^2 = -1) (x : Reduced K) :
    reducedEquiv K (twistedReducedAction K i hi (swappingElement K i hi) x) =
      (LinearEquiv.prodComm K (Symmetric3 K) (Symmetric3 K)) (reducedEquiv K x) := by
  rw [twistedReducedAction_apply, twistScalar_swapping, map_smul,
    reducedEquiv_raw_swapping, smul_smul]
  have hc : i * -i = 1 := by rw [mul_neg, ← pow_two, hi, neg_neg]
  rw [hc, one_smul]

/-- The global negative identity acts trivially after the actual character twist. -/
@[simp] theorem twistedReducedAction_centralSign (i : K) (hi : i^2 = -1) :
    twistedReducedAction K i hi (centralSign K) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [twistedReducedAction_apply, twistScalar_centralSign,
    rawReducedAction_centralSign, neg_one_smul, neg_neg, LinearMap.id_apply]

theorem centralSignSubgroup_le_kernel (i : K) (hi : i^2 = -1) :
    PrimitiveProjectiveStabilizer.centralSignSubgroup K ≤
      (twistedReducedRepresentation K i hi).ker := by
  apply Subgroup.zpowers_le.mpr
  exact twistedReducedAction_centralSign K i hi

/-- The twisted representation descends through the actual global central sign. -/
def quotientRepresentation (i : K) (hi : i^2 = -1) :
    PrimitiveProjectiveStabilizer.projectiveLineStabilizer K →*
      Module.End K (Reduced K) :=
  QuotientGroup.lift (PrimitiveProjectiveStabilizer.centralSignSubgroup K)
    (twistedReducedRepresentation K i hi) (centralSignSubgroup_le_kernel K i hi)

@[simp] theorem quotientRepresentation_mk (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) :
    quotientRepresentation K i hi
      (QuotientGroup.mk' (PrimitiveProjectiveStabilizer.centralSignSubgroup K) h) =
        twistedReducedAction K i hi h := rfl

/-! The target representation is built independently from matrix congruence
and the literal two-factor swap, using the semidirect-product universal property. -/

omit [CharZero K] in
@[simp] theorem mixedAction_one (z : Mixed K) : mixedAction K 1 z = z := by
  rcases z with ⟨X,Y⟩
  simp [mixedAction]

omit [CharZero K] in
theorem mixedAction_mul (g h : Matrix.SpecialLinearGroup (Fin 3) K) (z : Mixed K) :
    mixedAction K (g*h) z = mixedAction K g (mixedAction K h z) := by
  have hc := PrimitiveRepresentation.sl3Action_mul K g h (0,z.1,z.2,0)
  exact congrArg (fun r : PrimitiveRepresentation.Coordinates K => (r.2.1,r.2.2.1)) hc

/-- The connected two-block action as an actual linear automorphism. -/
def mixedLinear (g : Matrix.SpecialLinearGroup (Fin 3) K) : Mixed K ≃ₗ[K] Mixed K :=
  LinearEquiv.ofLinearMap (mixedAction K g) (mixedAction K g⁻¹)
    (by
      apply LinearMap.ext
      intro z
      change mixedAction K g (mixedAction K g⁻¹ z) = z
      rw [← mixedAction_mul, mul_inv_cancel, mixedAction_one])
    (by
      apply LinearMap.ext
      intro z
      change mixedAction K g⁻¹ (mixedAction K g z) = z
      rw [← mixedAction_mul, inv_mul_cancel, mixedAction_one])

def mixedBlockRepresentation : Matrix.SpecialLinearGroup (Fin 3) K →*
    (Mixed K ≃ₗ[K] Mixed K) where
  toFun := mixedLinear K
  map_one' := by
    apply LinearEquiv.ext
    exact mixedAction_one K
  map_mul' g h := by
    apply LinearEquiv.ext
    exact mixedAction_mul K g h

/-- The literal exchange of the two symmetric-matrix spaces. -/
def mixedSwap : Mixed K ≃ₗ[K] Mixed K :=
  LinearEquiv.prodComm K (Symmetric3 K) (Symmetric3 K)

omit [CharZero K] in
@[simp] theorem mixedSwap_apply (z : Mixed K) : mixedSwap K z = (z.2,z.1) := rfl

omit [CharZero K] in
@[simp] theorem mixedSwap_swap (z : Mixed K) : mixedSwap K (mixedSwap K z) = z := rfl

omit [CharZero K] in
@[simp] theorem mixedSwap_square : mixedSwap K * mixedSwap K = 1 := by
  apply LinearEquiv.ext
  exact mixedSwap_swap K

def mixedSwapRepresentation : CentralSignQuotient.C2 →* (Mixed K ≃ₗ[K] Mixed K) :=
  CentralSignQuotient.involutionHom (mixedSwap K) (mixedSwap_square K)

omit [CharZero K] in
theorem mixedSwap_covariance (g : Matrix.SpecialLinearGroup (Fin 3) K) (z : Mixed K) :
    mixedSwap K (mixedAction K g z) =
      mixedAction K (PrimitiveRepresentation.inverseTranspose K g) (mixedSwap K z) := by
  have hc := PrimitiveRepresentation.swap_sl3Action K g (0,z.1,z.2,0)
  exact congrArg (fun r : PrimitiveRepresentation.Coordinates K => (r.2.1,r.2.2.1)) hc

theorem mixed_semidirect_compatibility (c : CentralSignQuotient.C2) :
    (mixedBlockRepresentation K).comp
        (PrimitiveProjectiveStabilizer.inverseTransposeAction K c).toMonoidHom =
      (MulAut.conj (mixedSwapRepresentation K c)).toMonoidHom.comp
        (mixedBlockRepresentation K) := by
  rcases CentralSignQuotient.c2_cases c with rfl | rfl
  · apply MonoidHom.ext
    intro g
    change mixedBlockRepresentation K
        (PrimitiveProjectiveStabilizer.inverseTransposeAction K 1 g) =
      mixedSwapRepresentation K 1 * mixedBlockRepresentation K g *
        (mixedSwapRepresentation K 1)⁻¹
    rw [map_one, map_one]
    simp
  · apply MonoidHom.ext
    intro g
    apply LinearEquiv.ext
    intro z
    change mixedLinear K
        (PrimitiveProjectiveStabilizer.inverseTransposeAction K CentralSignQuotient.epsilon g) z =
      ((mixedSwapRepresentation K CentralSignQuotient.epsilon) * mixedLinear K g *
        (mixedSwapRepresentation K CentralSignQuotient.epsilon)⁻¹) z
    simp only [PrimitiveProjectiveStabilizer.inverseTransposeAction_epsilon,
      mixedSwapRepresentation, CentralSignQuotient.involutionHom_epsilon]
    change mixedAction K (PrimitiveRepresentation.inverseTranspose K g) z =
      mixedSwap K (mixedAction K g (mixedSwap K z))
    simpa only [mixedSwap_swap] using (mixedSwap_covariance K g (mixedSwap K z)).symm

/-- The independently constructed `SL₃ ⋊ C₂` linear representation. -/
def mixedSemidirectLinearRepresentation :
    PrimitiveProjectiveStabilizer.specialLinearSemidirect K →* (Mixed K ≃ₗ[K] Mixed K) :=
  SemidirectProduct.lift (mixedBlockRepresentation K) (mixedSwapRepresentation K)
    (mixed_semidirect_compatibility K)

def mixedSemidirectRepresentation :
    PrimitiveProjectiveStabilizer.specialLinearSemidirect K →* Module.End K (Mixed K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (mixedSemidirectLinearRepresentation K)

@[simp] theorem mixedSemidirectRepresentation_inl
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    mixedSemidirectRepresentation K (SemidirectProduct.inl g) = mixedAction K g := by
  change (mixedSemidirectLinearRepresentation K (SemidirectProduct.inl g)).toLinearMap = _
  rw [mixedSemidirectLinearRepresentation, SemidirectProduct.lift_inl]
  rfl

@[simp] theorem mixedSemidirectRepresentation_inr_epsilon :
    mixedSemidirectRepresentation K (SemidirectProduct.inr CentralSignQuotient.epsilon) =
      (mixedSwap K).toLinearMap := by
  change (mixedSemidirectLinearRepresentation K
    (SemidirectProduct.inr CentralSignQuotient.epsilon)).toLinearMap = _
  rw [mixedSemidirectLinearRepresentation, SemidirectProduct.lift_inr]
  simp only [mixedSwapRepresentation, CentralSignQuotient.involutionHom_epsilon]

/-- The full semidirect-product action, with the order of swap and congruence explicit. -/
theorem mixedSemidirectRepresentation_apply
    (s : PrimitiveProjectiveStabilizer.specialLinearSemidirect K) (z : Mixed K) :
    mixedSemidirectRepresentation K s z =
      if s.right = 1 then mixedAction K s.left z
      else mixedAction K s.left (z.2,z.1) := by
  change mixedAction K s.left ((mixedSwapRepresentation K s.right) z) = _
  by_cases hc : s.right = 1
  · rw [hc]
    rw [map_one]
    simp only [ite_true]
    rfl
  · rw [ite_eq_right hc]
    have hs : mixedSwapRepresentation K s.right = mixedSwap K := by
      change (if s.right = 1 then 1 else mixedSwap K) = mixedSwap K
      exact ite_eq_right hc
    rw [hs]
    rfl

/-- In particular the connected component has exactly the two manuscript matrix formulas. -/
theorem mixedSemidirectRepresentation_inl_matrices
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (X Y : Symmetric3 K) :
    (mixedSemidirectRepresentation K (SemidirectProduct.inl g) (X,Y)).1.val =
        g.val * X.val * g.val.transpose ∧
      (mixedSemidirectRepresentation K (SemidirectProduct.inl g) (X,Y)).2.val =
        (g⁻¹).val.transpose * Y.val * (g⁻¹).val := by
  rw [mixedSemidirectRepresentation_inl]
  constructor
  · rfl
  · change (g⁻¹).val.transpose * Y.val * ((g⁻¹).val.transpose).transpose = _
    rw [Matrix.transpose_transpose]

@[simp] theorem toProjectiveSemidirect_block (i : K) (hi : i^2 = -1)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi (blockStabilizerHom K g) =
      SemidirectProduct.inl g :=
  PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv_block K i hi g

@[simp] theorem toProjectiveSemidirect_swapping (i : K) (hi : i^2 = -1) :
    PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi (swappingElement K i hi) =
      SemidirectProduct.inr CentralSignQuotient.epsilon :=
  PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv_swapping K i hi

@[simp] theorem toProjectiveSemidirect_centralSign (i : K) (hi : i^2 = -1) :
    PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi (centralSign K) = 1 := by
  rw [PrimitiveProjectiveStabilizer.toProjectiveSemidirect_eq_data]
  exact (PrimitiveProjectiveStabilizer.quotientData K i hi).toSemidirect_z

/-- The component in the action formula is the actual square-character parity. -/
theorem toProjectiveSemidirect_right (i : K) (hi : i^2 = -1) (h : lineStabilizer K) :
    (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h).right =
      stabilizerParity K h :=
  DFunLike.congr_fun (PrimitiveProjectiveStabilizer.toProjectiveSemidirect_parity K i hi) h

theorem reducedEquiv_twisted_mul (i : K) (hi : i^2 = -1) (h g : lineStabilizer K)
    (hh : ∀ x, reducedEquiv K (twistedReducedAction K i hi h x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h) (reducedEquiv K x))
    (hg : ∀ x, reducedEquiv K (twistedReducedAction K i hi g x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi g) (reducedEquiv K x))
    (x : Reduced K) :
    reducedEquiv K (twistedReducedAction K i hi (h*g) x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi (h*g)) (reducedEquiv K x) := by
  rw [twistedReducedAction_mul, map_mul, map_mul]
  change reducedEquiv K (twistedReducedAction K i hi h (twistedReducedAction K i hi g x)) = _
  rw [hh, hg]
  rfl

/-- Every actual stabilizer element acts in the proved matrix/swap representation. -/
theorem reducedEquiv_twisted (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Reduced K) :
    reducedEquiv K (twistedReducedAction K i hi h x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h) (reducedEquiv K x) := by
  have hb (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Reduced K) :
      reducedEquiv K (twistedReducedAction K i hi (blockStabilizerHom K g) x) =
        mixedSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi
            (blockStabilizerHom K g)) (reducedEquiv K x) := by
    simpa only [toProjectiveSemidirect_block, mixedSemidirectRepresentation_inl] using
      reducedEquiv_twisted_block K i hi g x
  have hs (x : Reduced K) :
      reducedEquiv K (twistedReducedAction K i hi (swappingElement K i hi) x) =
        mixedSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi
            (swappingElement K i hi)) (reducedEquiv K x) := by
    rw [toProjectiveSemidirect_swapping, mixedSemidirectRepresentation_inr_epsilon]
    exact reducedEquiv_twisted_swapping K i hi x
  have hz (x : Reduced K) :
      reducedEquiv K (twistedReducedAction K i hi (centralSign K) x) =
        mixedSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi (centralSign K))
            (reducedEquiv K x) := by
    simp only [twistedReducedAction_centralSign, LinearMap.id_apply,
      toProjectiveSemidirect_centralSign, map_one, Module.End.one_apply]
  obtain ⟨g, hh | hh | hh | hh⟩ :=
    (PrimitiveProjectiveStabilizer.quotientData K i hi).normalForms h
  · rw [hh]
    exact hb g x
  · rw [hh]
    exact reducedEquiv_twisted_mul K i hi _ _ hz (hb g) x
  · rw [hh]
    exact reducedEquiv_twisted_mul K i hi _ _ hs (hb g) x
  · rw [hh]
    exact reducedEquiv_twisted_mul K i hi _ _
      (reducedEquiv_twisted_mul K i hi _ _ hz hs) (hb g) x

/-- A full action formula with parity coming from the actual line character. -/
theorem reducedEquiv_twisted_parity (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Reduced K) :
    reducedEquiv K (twistedReducedAction K i hi h x) =
      if stabilizerParity K h = 1 then
        mixedAction K (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h).left
          (reducedEquiv K x)
      else
        mixedAction K (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h).left
          ((reducedEquiv K x).2,(reducedEquiv K x).1) := by
  rw [reducedEquiv_twisted, mixedSemidirectRepresentation_apply, toProjectiveSemidirect_right]

/-- Equivariance of the actual descended quotient representation. -/
theorem reducedEquiv_quotient (i : K) (hi : i^2 = -1)
    (h : PrimitiveProjectiveStabilizer.projectiveLineStabilizer K) (x : Reduced K) :
    reducedEquiv K (quotientRepresentation K i hi h x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv K i hi h) (reducedEquiv K x) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    (PrimitiveProjectiveStabilizer.centralSignSubgroup K) h
  exact reducedEquiv_twisted K i hi h x

/-- Equality of representations under the actual quotient's linear-coordinate isomorphism. -/
theorem quotientRepresentation_conjugate (i : K) (hi : i^2 = -1) :
    ((reducedEquiv K).conjRingEquiv.toMonoidHom).comp (quotientRepresentation K i hi) =
      (mixedSemidirectRepresentation K).comp
        (PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv K i hi).toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro z
  change reducedEquiv K
    (quotientRepresentation K i hi h ((reducedEquiv K).symm z)) = _
  rw [reducedEquiv_quotient, LinearEquiv.apply_symm_apply]
  rfl

/-- The representation of the literal point stabilizer inside global `PSp₆`. -/
def actualStabilizerRepresentation (i : K) (hi : i^2 = -1) :
    PrimitiveProjectiveAction.pointStabilizer K →* Module.End K (Reduced K) :=
  (quotientRepresentation K i hi).comp
    (PrimitiveProjectiveAction.stabilizerQuotientEquiv K).symm.toMonoidHom

@[simp] theorem actualStabilizerRepresentation_projection (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) :
    actualStabilizerRepresentation K i hi (PrimitiveProjectiveAction.stabilizerProjection K h) =
      twistedReducedAction K i hi h := by
  change quotientRepresentation K i hi
    ((PrimitiveProjectiveAction.stabilizerQuotientEquiv K).symm
      (PrimitiveProjectiveAction.stabilizerProjection K h)) = _
  rw [PrimitiveProjectiveAction.stabilizerQuotientEquiv_symm_projection]
  rfl

/-- Literal `PSp₆` stabilizer equivariance, including every component. -/
theorem reducedEquiv_actualStabilizer (i : K) (hi : i^2 = -1)
    (h : PrimitiveProjectiveAction.pointStabilizer K) (x : Reduced K) :
    reducedEquiv K (actualStabilizerRepresentation K i hi h x) =
      mixedSemidirectRepresentation K
        (PrimitiveProjectiveAction.actualStabilizerEquiv K i hi h) (reducedEquiv K x) :=
  reducedEquiv_quotient K i hi ((PrimitiveProjectiveAction.stabilizerQuotientEquiv K).symm h) x

/-- The full representation identity for the literal stabilizer in global `PSp₆`. -/
theorem actualStabilizerRepresentation_conjugate (i : K) (hi : i^2 = -1) :
    ((reducedEquiv K).conjRingEquiv.toMonoidHom).comp
        (actualStabilizerRepresentation K i hi) =
      (mixedSemidirectRepresentation K).comp
        (PrimitiveProjectiveAction.actualStabilizerEquiv K i hi).toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro z
  change reducedEquiv K
    (actualStabilizerRepresentation K i hi h ((reducedEquiv K).symm z)) = _
  rw [reducedEquiv_actualStabilizer, LinearEquiv.apply_symm_apply]
  rfl

/-! The same representation in `Q ⊕ Q*`, using the actual trace-pairing duality. -/

abbrev DualMixed := Symmetric3 K × Module.Dual K (Symmetric3 K)

def mixedDualEquiv : Mixed K ≃ₗ[K] DualMixed K :=
  (LinearEquiv.refl K (Symmetric3 K)).prodCongr (symmetricDualEquiv K)

def dualSemidirectRepresentation :
    PrimitiveProjectiveStabilizer.specialLinearSemidirect K →* Module.End K (DualMixed K) :=
  ((mixedDualEquiv K).conjRingEquiv.toMonoidHom).comp (mixedSemidirectRepresentation K)

theorem dualSemidirectRepresentation_apply
    (s : PrimitiveProjectiveStabilizer.specialLinearSemidirect K) (z : DualMixed K) :
    dualSemidirectRepresentation K s z =
      mixedDualEquiv K (mixedSemidirectRepresentation K s ((mixedDualEquiv K).symm z)) := rfl

/-- The actual dual-coordinate action has the contragredient second component. -/
@[simp] theorem dualSemidirectRepresentation_inl
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    dualSemidirectRepresentation K (SemidirectProduct.inl g) = dualMixedAction K g := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (mixedDualEquiv K).surjective z
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply,
    mixedSemidirectRepresentation_inl]
  apply Prod.ext
  · rfl
  · exact traceDual_contragredient K g w.2

/-- The odd generator swaps a vector and covector using the proved trace duality. -/
theorem dualSemidirectRepresentation_inr_epsilon (z : DualMixed K) :
    dualSemidirectRepresentation K (SemidirectProduct.inr CentralSignQuotient.epsilon) z =
      ((symmetricDualEquiv K).symm z.2,symmetricDualEquiv K z.1) := by
  rw [dualSemidirectRepresentation_apply, mixedSemidirectRepresentation_inr_epsilon]
  rfl

theorem reducedDualEquiv_twisted (i : K) (hi : i^2 = -1)
    (h : lineStabilizer K) (x : Reduced K) :
    reducedDualEquiv K (twistedReducedAction K i hi h x) =
      dualSemidirectRepresentation K
        (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h) (reducedDualEquiv K x) := by
  change mixedDualEquiv K (reducedEquiv K (twistedReducedAction K i hi h x)) =
    dualSemidirectRepresentation K
      (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h)
        (mixedDualEquiv K (reducedEquiv K x))
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply, reducedEquiv_twisted]

theorem reducedDualEquiv_actualStabilizer (i : K) (hi : i^2 = -1)
    (h : PrimitiveProjectiveAction.pointStabilizer K) (x : Reduced K) :
    reducedDualEquiv K (actualStabilizerRepresentation K i hi h x) =
      dualSemidirectRepresentation K
        (PrimitiveProjectiveAction.actualStabilizerEquiv K i hi h) (reducedDualEquiv K x) := by
  change mixedDualEquiv K (reducedEquiv K (actualStabilizerRepresentation K i hi h x)) =
    dualSemidirectRepresentation K (PrimitiveProjectiveAction.actualStabilizerEquiv K i hi h)
      (mixedDualEquiv K (reducedEquiv K x))
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply,
    reducedEquiv_actualStabilizer]

/-- Over the complex numbers the actual representation needs no square-root premise. -/
def complexActualStabilizerRepresentation :
    PrimitiveProjectiveAction.pointStabilizer ℂ →* Module.End ℂ (Reduced ℂ) :=
  actualStabilizerRepresentation ℂ Complex.I (by simp)

end M9.PrimitiveTwistedReduced
