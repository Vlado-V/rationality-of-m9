module

public import M9.WreathProductInvariants

/-!
# The concrete tetrahedral frame group and the permutation wreath group

The coordinatewise lift of the proved action on the four projective diagonals
identifies the two actual frame groups. The eight-coordinate polynomial and
fraction actions are pulled back along this group isomorphism. Their fixed
field is then proved equal to the already computed wreath fixed field.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace M9.WreathFrameComparison

open FrameAction

/-- A group isomorphism induces an isomorphism of the checked factor-swapping frame groups. -/
def frameGroupCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    FrameGroup G ≃* FrameGroup H where
  toFun x := ⟨e x.first, e x.second, x.odd⟩
  invFun x := ⟨e.symm x.first, e.symm x.second, x.odd⟩
  left_inv x := by
    rcases x with ⟨a, b, o⟩
    simp
  right_inv x := by
    rcases x with ⟨a, b, o⟩
    simp
  map_mul' x y := by
    rcases x with ⟨a, b, o⟩
    rcases y with ⟨a', b', o'⟩
    cases o <;> cases o' <;>
      simp [FrameGroup.mul_even, FrameGroup.mul_odd]

@[simp] theorem frameGroupCongr_mk {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a b : G) (o : Bool) :
    frameGroupCongr e ⟨a, b, o⟩ = ⟨e a, e b, o⟩ := rfl

/-- The concrete signed-permutation frame group is exactly the permutation wreath group. -/
def frameWreathEquiv : TetrahedralFrameGroup ≃* WreathProductInvariants.WreathGroup :=
  frameGroupCongr TetrahedralGroup.framePermutation

@[simp] theorem frameWreathEquiv_mk (a b : TetrahedralGroup.Gamma) (o : Bool) :
    frameWreathEquiv ⟨a, b, o⟩ =
      ⟨TetrahedralGroup.framePermutation a, TetrahedralGroup.framePermutation b, o⟩ := rfl

@[simp] theorem frameWreathEquiv_pair (a b : TetrahedralGroup.Gamma) :
    frameWreathEquiv (FrameGroup.pairHom (a, b)) =
      FrameGroup.pairHom (TetrahedralGroup.framePermutation a,
        TetrahedralGroup.framePermutation b) := rfl

@[simp] theorem frameWreathEquiv_tau :
    frameWreathEquiv (FrameGroup.tau : TetrahedralFrameGroup) = FrameGroup.tau := by
  simp [frameWreathEquiv, frameGroupCongr, FrameGroup.tau]

@[simp] theorem frameWreathEquiv_symm_pair (a b : Equiv.Perm (Fin 4)) :
    frameWreathEquiv.symm (FrameGroup.pairHom (a, b)) =
      FrameGroup.pairHom (TetrahedralGroup.framePermutation.symm a,
        TetrahedralGroup.framePermutation.symm b) := rfl

@[simp] theorem frameWreathEquiv_symm_tau :
    frameWreathEquiv.symm (FrameGroup.tau : WreathProductInvariants.WreathGroup) =
      FrameGroup.tau := by
  simp [frameWreathEquiv, frameGroupCongr, FrameGroup.tau]

/-- The eight-coordinate permutation attached to the actual tetrahedral matrices. -/
def frameIndexRepresentation : TetrahedralFrameGroup →*
    Equiv.Perm SymmetricBlockInvariants.BlockIndex :=
  WreathProductInvariants.indexRepresentation.comp frameWreathEquiv.toMonoidHom

theorem frameIndexRepresentation_injective : Function.Injective frameIndexRepresentation :=
  WreathProductInvariants.indexRepresentation_injective.comp frameWreathEquiv.injective

@[simp] theorem frameIndexRepresentation_even_left
    (a b : TetrahedralGroup.Gamma) (i : Fin 4) :
    frameIndexRepresentation ⟨a, b, false⟩ (.inl i) =
      .inl (TetrahedralGroup.framePermutation a i) := by
  simp [frameIndexRepresentation, WreathProductInvariants.indexRepresentation]

@[simp] theorem frameIndexRepresentation_even_right
    (a b : TetrahedralGroup.Gamma) (i : Fin 4) :
    frameIndexRepresentation ⟨a, b, false⟩ (.inr i) =
      .inr (TetrahedralGroup.framePermutation b i) := by
  simp [frameIndexRepresentation, WreathProductInvariants.indexRepresentation]

@[simp] theorem frameIndexRepresentation_odd_left
    (a b : TetrahedralGroup.Gamma) (i : Fin 4) :
    frameIndexRepresentation ⟨a, b, true⟩ (.inl i) =
      .inr (TetrahedralGroup.framePermutation b i) := by
  simp [frameIndexRepresentation, WreathProductInvariants.indexRepresentation]

@[simp] theorem frameIndexRepresentation_odd_right
    (a b : TetrahedralGroup.Gamma) (i : Fin 4) :
    frameIndexRepresentation ⟨a, b, true⟩ (.inr i) =
      .inl (TetrahedralGroup.framePermutation a i) := by
  simp [frameIndexRepresentation, WreathProductInvariants.indexRepresentation]

@[simp] theorem frameIndexRepresentation_tau (i : SymmetricBlockInvariants.BlockIndex) :
    frameIndexRepresentation (FrameGroup.tau : TetrahedralFrameGroup) i = Sum.swap i := by
  rcases i with i | i <;>
    simp [frameIndexRepresentation, WreathProductInvariants.indexRepresentation, FrameGroup.tau]

abbrev FramePermutationPolynomial (K : Type*) [Field K] :=
  WreathProductInvariants.PermutationPolynomial K
abbrev FramePermutationField (K : Type*) [Field K] :=
  WreathProductInvariants.PermutationField K

variable (K : Type*) [Field K]

/-- Transport the actual eight-coordinate polynomial action along the actual group isomorphism. -/
instance framePolynomialMulSemiringAction :
    MulSemiringAction TetrahedralFrameGroup (FramePermutationPolynomial K) :=
  MulSemiringAction.compHom (FramePermutationPolynomial K) frameWreathEquiv.toMonoidHom

instance framePolynomialSmulCommClass :
    SMulCommClass TetrahedralFrameGroup K (FramePermutationPolynomial K) where
  smul_comm g a p := smul_comm (frameWreathEquiv g) a p

@[simp] theorem frame_smul_polynomial (g : TetrahedralFrameGroup)
    (p : FramePermutationPolynomial K) : g • p = frameWreathEquiv g • p := rfl

@[simp] theorem frame_smul_X (g : TetrahedralFrameGroup)
    (i : SymmetricBlockInvariants.BlockIndex) :
    g • (MvPolynomial.X i : FramePermutationPolynomial K) =
      MvPolynomial.X (frameIndexRepresentation g i) :=
  WreathProductInvariants.polynomial_smul_X K (frameWreathEquiv g) i

/-- Transport the actual fraction-field action, with no new fixed-field premise. -/
instance frameFieldMulSemiringAction :
    MulSemiringAction TetrahedralFrameGroup (FramePermutationField K) :=
  MulSemiringAction.compHom (FramePermutationField K) frameWreathEquiv.toMonoidHom

instance frameFieldSmulDistribClass :
    SMulDistribClass TetrahedralFrameGroup (FramePermutationPolynomial K) (FramePermutationField K) where
  smul_distrib_smul g p z := smul_distrib_smul (frameWreathEquiv g) p z

instance frameFieldSmulCommClass :
    SMulCommClass TetrahedralFrameGroup K (FramePermutationField K) where
  smul_comm g a z := smul_comm (frameWreathEquiv g) a z

@[simp] theorem frame_smul_field (g : TetrahedralFrameGroup)
    (z : FramePermutationField K) : g • z = frameWreathEquiv g • z := rfl

instance frameFieldFaithfulSMul : FaithfulSMul TetrahedralFrameGroup (FramePermutationField K) where
  eq_of_smul_eq_smul {g h} hgh := by
    apply frameWreathEquiv.injective
    exact FaithfulSMul.eq_of_smul_eq_smul hgh

@[simp] theorem frame_smul_coordinate (g : TetrahedralFrameGroup)
    (i : SymmetricBlockInvariants.BlockIndex) :
    g • PermutationInvariants.coordinate K i =
      PermutationInvariants.coordinate K (frameIndexRepresentation g i) := by
  rw [PermutationInvariants.coordinate, ← algebraMap.coe_smul', frame_smul_X]
  rfl

@[simp] theorem frame_tau_smul_field (z : FramePermutationField K) :
    (FrameGroup.tau : TetrahedralFrameGroup) • z = PermutationInvariants.swap K z := by
  rw [frame_smul_field, frameWreathEquiv_tau, WreathProductInvariants.tau_smul_field]

/-- The actual fixed field for the concrete matrix frame group on the eight-coordinate field. -/
def frameFixedField : IntermediateField K (FramePermutationField K) where
  __ := FixedPoints.subfield TetrahedralFrameGroup (FramePermutationField K)
  algebraMap_mem' a g := smul_algebraMap g a

/-- Surjectivity of the group isomorphism proves equality of the two actual fixed fields. -/
theorem frameFixedField_eq : frameFixedField K = WreathProductInvariants.fixedField K := by
  ext z
  change (∀ g : TetrahedralFrameGroup, g • z = z) ↔
    ∀ w : WreathProductInvariants.WreathGroup, w • z = z
  constructor
  · intro hz w
    obtain ⟨g, rfl⟩ := frameWreathEquiv.surjective w
    exact hz g
  · intro hz g
    exact hz (frameWreathEquiv g)

def frameFixedFieldWreathEquiv :
    frameFixedField K ≃ₐ[K] WreathProductInvariants.fixedField K :=
  IntermediateField.equivOfEq (frameFixedField_eq K)

/-- The actual tetrahedral-frame fixed field is rational in eight independent variables. -/
def frameFixedFieldEquiv [CharZero K] : frameFixedField K ≃ₐ[K] RationalField K 8 :=
  (frameFixedFieldWreathEquiv K).trans (WreathProductInvariants.fixedFieldEquiv K)

theorem frameFixedField_rational [CharZero K] : RationalOfDimension K (frameFixedField K) 8 :=
  ⟨frameFixedFieldEquiv K⟩

end M9.WreathFrameComparison
