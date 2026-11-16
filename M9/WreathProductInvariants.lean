module

public import M9.SymmetricBlockInvariants
public import M9.FrameAction

/-!
# The actual eight-coordinate wreath-product invariant field

The group is the checked normal-form model `(S₄ × S₄) ⋊ C₂` from
`FrameAction`. Its action permutes the eight original variables. The full
fixed field is proved to be the swap equalizer inside the actual separate
fixed field before the elementary-coordinate and swap equivalences are
composed.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace M9.WreathProductInvariants

open MvPolynomial
open SymmetricBlockInvariants

abbrev WreathGroup := FrameAction.FrameGroup (Equiv.Perm (Fin 4))
abbrev PermutationPolynomial (K : Type*) [Field K] := BlockPolynomial K
abbrev PermutationField (K : Type*) [Field K] := BlockField K

/-- A pair permutes within blocks; the odd generator first exchanges the blocks. -/
def indexPermutation (g : WreathGroup) : Equiv.Perm BlockIndex :=
  (Equiv.sumCongr g.first g.second) *
    if g.odd then Equiv.sumComm (Fin 4) (Fin 4) else 1

@[simp] theorem indexPermutation_even_left (a b : Equiv.Perm (Fin 4)) (i : Fin 4) :
    indexPermutation ⟨a, b, false⟩ (.inl i) = .inl (a i) := by
  simp [indexPermutation]

@[simp] theorem indexPermutation_even_right (a b : Equiv.Perm (Fin 4)) (i : Fin 4) :
    indexPermutation ⟨a, b, false⟩ (.inr i) = .inr (b i) := by
  simp [indexPermutation]

@[simp] theorem indexPermutation_odd_left (a b : Equiv.Perm (Fin 4)) (i : Fin 4) :
    indexPermutation ⟨a, b, true⟩ (.inl i) = .inr (b i) := by
  simp [indexPermutation]

@[simp] theorem indexPermutation_odd_right (a b : Equiv.Perm (Fin 4)) (i : Fin 4) :
    indexPermutation ⟨a, b, true⟩ (.inr i) = .inl (a i) := by
  simp [indexPermutation]

/-- The genuine wreath-product permutation representation, with its multiplication law. -/
def indexRepresentation : WreathGroup →* Equiv.Perm BlockIndex where
  toFun := indexPermutation
  map_one' := by
    apply Equiv.ext
    intro i
    rcases i with i | i <;> simp [indexPermutation]
  map_mul' g h := by
    rcases g with ⟨a, b, o⟩
    rcases h with ⟨a', b', o'⟩
    apply Equiv.ext
    intro i
    cases o <;> cases o' <;> rcases i with i | i <;>
      simp [FrameAction.FrameGroup.mul_even, FrameAction.FrameGroup.mul_odd]

theorem indexRepresentation_injective : Function.Injective indexRepresentation := by
  rintro ⟨a, b, o⟩ ⟨a', b', o'⟩ h
  have hpoint (i : BlockIndex) := congrArg (fun e : Equiv.Perm BlockIndex => e i) h
  cases o <;> cases o'
  · apply FrameAction.FrameGroup.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (hpoint (.inl i))
    · apply Equiv.ext
      intro i
      exact Sum.inr.inj (hpoint (.inr i))
    · rfl
  · have hbad := hpoint (.inl 0)
    simp only [indexRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
      indexPermutation_even_left, indexPermutation_odd_left] at hbad
    cases hbad
  · have hbad := hpoint (.inl 0)
    simp only [indexRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
      indexPermutation_even_left, indexPermutation_odd_left] at hbad
    cases hbad
  · apply FrameAction.FrameGroup.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (hpoint (.inr i))
    · apply Equiv.ext
      intro i
      exact Sum.inr.inj (hpoint (.inl i))
    · rfl

@[simp] theorem card_wreathGroup : Fintype.card WreathGroup = 1152 := by
  simp [WreathGroup, FrameAction.FrameGroup.card, Fintype.card_perm, Nat.factorial]

variable (K : Type*) [Field K]

/-- Rename the original eight polynomial coordinates by the actual wreath permutation. -/
def polynomialActionHom : WreathGroup →*
    (PermutationPolynomial K ≃ₐ[K] PermutationPolynomial K) where
  toFun g := MvPolynomial.renameEquiv K (indexRepresentation g)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro i
    simp [renameEquiv_apply]
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro i
    simp [renameEquiv_apply]

instance polynomialMulSemiringAction : MulSemiringAction WreathGroup (PermutationPolynomial K) :=
  MulSemiringAction.compHom (PermutationPolynomial K) (polynomialActionHom K)

instance polynomialSmulCommClass : SMulCommClass WreathGroup K (PermutationPolynomial K) where
  smul_comm g a p := (polynomialActionHom K g).toLinearEquiv.map_smul a p

@[simp] theorem polynomial_smul_X (g : WreathGroup) (i : BlockIndex) :
    g • (X i : PermutationPolynomial K) = X (indexRepresentation g i) := by
  change (polynomialActionHom K g) (X i) = _
  simp [polynomialActionHom, renameEquiv_apply]

theorem polynomialActionHom_injective : Function.Injective (polynomialActionHom K) := by
  intro g h hgh
  apply indexRepresentation_injective
  apply Equiv.ext
  intro i
  apply MvPolynomial.X_injective (R := K)
  simpa [polynomialActionHom, renameEquiv_apply] using
    congrArg (fun e : PermutationPolynomial K ≃ₐ[K] PermutationPolynomial K => e (X i)) hgh

instance polynomialFaithfulSMul : FaithfulSMul WreathGroup (PermutationPolynomial K) :=
  ⟨fun h => polynomialActionHom_injective K (AlgEquiv.ext h)⟩

instance fieldMulSemiringAction : MulSemiringAction WreathGroup (PermutationField K) :=
  IsFractionRing.mulSemiringAction WreathGroup (PermutationPolynomial K) (PermutationField K)

instance fieldSmulDistribClass :
    SMulDistribClass WreathGroup (PermutationPolynomial K) (PermutationField K) :=
  IsFractionRing.smulDistribClass WreathGroup (PermutationPolynomial K) (PermutationField K)

instance fieldSmulCommClass : SMulCommClass WreathGroup K (PermutationField K) :=
  IsFractionRing.smulCommClass WreathGroup K (PermutationPolynomial K) K (PermutationField K)

instance fieldFaithfulSMul : FaithfulSMul WreathGroup (PermutationField K) :=
  IsFractionRing.faithfulSMul WreathGroup (PermutationPolynomial K) (PermutationField K)

theorem pair_smul_polynomial (g : BlockGroup) (p : PermutationPolynomial K) :
    FrameAction.FrameGroup.pairHom g • p = g • p := by
  change MvPolynomial.rename (indexPermutation ⟨g.1, g.2, false⟩) p =
    MvPolynomial.rename (Equiv.sumCongr g.1 g.2) p
  simp [indexPermutation]

theorem tau_smul_polynomial (p : PermutationPolynomial K) :
    (FrameAction.FrameGroup.tau : WreathGroup) • p = polynomialSwap K p := by
  change MvPolynomial.rename (indexPermutation ⟨1, 1, true⟩) p = _
  simp [indexPermutation, polynomialSwap, renameEquiv_apply]

theorem pair_smul_field (g : BlockGroup) (z : PermutationField K) :
    FrameAction.FrameGroup.pairHom g • z = g • z := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (PermutationPolynomial K) z
  simp only [smul_div₀', ← algebraMap.coe_smul', pair_smul_polynomial]

theorem tau_smul_field (z : PermutationField K) :
    (FrameAction.FrameGroup.tau : WreathGroup) • z = PermutationInvariants.swap K z := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (PermutationPolynomial K) z
  simp only [smul_div₀', map_div₀, ← algebraMap.coe_smul', tau_smul_polynomial,
    ambientSwap_algebraMap]

/-- The actual rational fixed field of the full finite wreath action. -/
def fixedField : IntermediateField K (PermutationField K) where
  __ := FixedPoints.subfield WreathGroup (PermutationField K)
  algebraMap_mem' a g := smul_algebraMap g a

theorem mem_fixedField_iff (z : PermutationField K) :
    z ∈ fixedField K ↔ z ∈ rationalInvariants K ∧ PermutationInvariants.swap K z = z := by
  change (∀ g : WreathGroup, g • z = z) ↔
    (∀ g : BlockGroup, g • z = z) ∧ PermutationInvariants.swap K z = z
  constructor
  · intro hz
    exact ⟨fun g => by simpa only [pair_smul_field] using hz (FrameAction.FrameGroup.pairHom g),
      by simpa only [tau_smul_field] using hz FrameAction.FrameGroup.tau⟩
  · rintro ⟨hp, ht⟩ ⟨a, b, o⟩
    cases o
    · exact (pair_smul_field K (a, b) z).trans (hp (a, b))
    · change (FrameAction.FrameGroup.pairHom (a, b) * FrameAction.FrameGroup.tau) • z = z
      rw [mul_smul, tau_smul_field, ht, pair_smul_field, hp (a, b)]

/-- The full fixed-field identification is proved from the actual group generators. -/
theorem fixedField_eq_intersection :
    fixedField K = rationalInvariants K ⊓ PermutationInvariants.swapFixedField K := by
  ext z
  exact mem_fixedField_iff K z

/-- Restrict the actual elementary-coordinate map to the actual swap-fixed field. -/
def elementaryFixedMap : PermutationInvariants.swapFixedField K →ₐ[K] fixedField K :=
  ((((rationalInvariants K).val.comp (elementaryFieldEquiv K).toAlgHom).comp
    (PermutationInvariants.swapFixedField K).val).codRestrict (fixedField K).toSubalgebra (by
      intro z
      change (elementaryFieldEquiv K z.val).val ∈ fixedField K
      apply (mem_fixedField_iff K _).mpr
      refine ⟨(elementaryFieldEquiv K z.val).property, ?_⟩
      have hz : PermutationInvariants.swap K z.val = z.val := z.property
      rw [← elementaryFieldEquiv_swap_coe, hz]))

@[simp] theorem elementaryFixedMap_coe (z : PermutationInvariants.swapFixedField K) :
    (elementaryFixedMap K z).val = (elementaryFieldEquiv K z.val).val := rfl

theorem elementaryFixedMap_injective : Function.Injective (elementaryFixedMap K) := by
  intro z w hzw
  apply Subtype.ext
  apply (elementaryFieldEquiv K).injective
  apply Subtype.ext
  exact congrArg (fun z : fixedField K => z.val) hzw

/-- The full fixed field has no additional elements beyond the transported swap invariants. -/
theorem elementaryFixedMap_surjective : Function.Surjective (elementaryFixedMap K) := by
  intro z
  obtain ⟨hzsep, hzswap⟩ := (mem_fixedField_iff K z.val).mp z.property
  let w := (elementaryFieldEquiv K).symm ⟨z.val, hzsep⟩
  have hwval : (elementaryFieldEquiv K w).val = z.val := by
    exact congrArg Subtype.val ((elementaryFieldEquiv K).apply_symm_apply ⟨z.val, hzsep⟩)
  have hw : PermutationInvariants.swap K w = w := by
    apply (elementaryFieldEquiv K).injective
    apply Subtype.ext
    rw [elementaryFieldEquiv_swap_coe, hwval, hzswap]
  exact ⟨⟨w, hw⟩, Subtype.ext hwval⟩

/-- Elementary coordinates identify the actual full wreath fixed field with the checked swap equalizer. -/
def elementaryFixedEquiv : PermutationInvariants.swapFixedField K ≃ₐ[K] fixedField K :=
  AlgEquiv.ofBijective (elementaryFixedMap K)
    ⟨elementaryFixedMap_injective K, elementaryFixedMap_surjective K⟩

@[simp] theorem elementaryFixedEquiv_coe (z : PermutationInvariants.swapFixedField K) :
    (elementaryFixedEquiv K z).val = (elementaryFieldEquiv K z.val).val := rfl

/-- The invariant field of the actual eight-coordinate wreath action is rational in eight variables. -/
def fixedFieldEquiv [CharZero K] : fixedField K ≃ₐ[K] RationalField K 8 :=
  (elementaryFixedEquiv K).symm.trans (PermutationInvariants.swapFixedFieldEquiv K)

theorem fixedField_rational [CharZero K] : RationalOfDimension K (fixedField K) 8 :=
  ⟨fixedFieldEquiv K⟩

end M9.WreathProductInvariants
