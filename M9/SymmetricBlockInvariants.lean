module

public import M9.PermutationInvariants
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Separate symmetric invariants of two independent quadruples

The polynomial and rational fixed rings below use the actual permutation
action on the eight coordinates of Section 6. The elementary-symmetric
coordinates are obtained from the fundamental theorem twice; the passage to
rational invariants uses the finite invariant fraction-field theorem.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace M9.SymmetricBlockInvariants

open MvPolynomial

abbrev BlockIndex := Fin 4 ⊕ Fin 4
abbrev BlockGroup := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)
abbrev BlockPolynomial (K : Type*) [Field K] := MvPolynomial BlockIndex K
abbrev BlockField (K : Type*) [Field K] := FractionRing (BlockPolynomial K)
abbrev InnerPolynomial (K : Type*) [Field K] := MvPolynomial (Fin 4) K
abbrev NestedPolynomial (K : Type*) [Field K] := MvPolynomial (Fin 4) (InnerPolynomial K)

variable (K : Type*) [Field K]

/-- Regrouping the actual eight variables, without changing their coefficient ring. -/
def nestedEquiv : BlockPolynomial K ≃ₐ[K] NestedPolynomial K :=
  MvPolynomial.sumAlgEquiv K (Fin 4) (Fin 4)

def polynomialSwap : BlockPolynomial K ≃ₐ[K] BlockPolynomial K :=
  MvPolynomial.renameEquiv K (Equiv.sumComm (Fin 4) (Fin 4))

@[simp] theorem polynomialSwap_X (i : BlockIndex) :
    polynomialSwap K (X i) = X (Sum.swap i) := by
  simp [polynomialSwap, renameEquiv_apply]

theorem polynomialSwap_involutive : Function.Involutive (polynomialSwap K) := by
  intro p
  simp [polynomialSwap, renameEquiv_apply, rename_rename]

@[simp] theorem polynomialSwap_polynomialSwap (p : BlockPolynomial K) :
    polynomialSwap K (polynomialSwap K p) = p := polynomialSwap_involutive K p

def leftRename (σ : Equiv.Perm (Fin 4)) : BlockPolynomial K ≃ₐ[K] BlockPolynomial K :=
  MvPolynomial.renameEquiv K (Equiv.sumCongr σ (Equiv.refl (Fin 4)))

def rightRename (σ : Equiv.Perm (Fin 4)) : BlockPolynomial K ≃ₐ[K] BlockPolynomial K :=
  MvPolynomial.renameEquiv K (Equiv.sumCongr (Equiv.refl (Fin 4)) σ)

@[simp] theorem leftRename_X_left (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    leftRename K σ (X (.inl i)) = X (.inl (σ i)) := by
  simp [leftRename, renameEquiv_apply]

@[simp] theorem leftRename_X_right (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    leftRename K σ (X (.inr i)) = X (.inr i) := by
  simp [leftRename, renameEquiv_apply]

@[simp] theorem rightRename_X_left (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    rightRename K σ (X (.inl i)) = X (.inl i) := by
  simp [rightRename, renameEquiv_apply]

@[simp] theorem rightRename_X_right (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    rightRename K σ (X (.inr i)) = X (.inr (σ i)) := by
  simp [rightRename, renameEquiv_apply]

theorem nestedEquiv_leftRename (σ : Equiv.Perm (Fin 4)) (p : BlockPolynomial K) :
    nestedEquiv K (leftRename K σ p) = MvPolynomial.rename σ (nestedEquiv K p) := by
  have h : (nestedEquiv K).toAlgHom.comp (leftRename K σ).toAlgHom =
      ((MvPolynomial.rename σ).restrictScalars K).comp (nestedEquiv K).toAlgHom := by
    ext i
    rcases i with i | i <;> simp [nestedEquiv]
  exact DFunLike.congr_fun h p

theorem swap_rightRename (σ : Equiv.Perm (Fin 4)) (p : BlockPolynomial K) :
    polynomialSwap K (rightRename K σ p) = leftRename K σ (polynomialSwap K p) := by
  have h : (polynomialSwap K).toAlgHom.comp (rightRename K σ).toAlgHom =
      (leftRename K σ).toAlgHom.comp (polynomialSwap K).toAlgHom := by
    ext i
    rcases i with i | i <;> simp
  exact DFunLike.congr_fun h p

section OneBlock

variable (R : Type*) [CommRing R]

/-- Substitution by the four elementary symmetric polynomials. -/
def elementarySubstitution : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 4) R :=
  (MvPolynomial.symmetricSubalgebra (Fin 4) R).val.comp
    (MvPolynomial.esymmAlgEquiv (Fin 4) R (by simp)).toAlgHom

@[simp] theorem elementarySubstitution_X (i : Fin 4) :
    elementarySubstitution R (X i) = MvPolynomial.esymm (Fin 4) R (i + 1) := by
  simp [elementarySubstitution, MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom, aeval_X]

@[simp] theorem elementarySubstitution_C (r : R) :
    elementarySubstitution R (C r) = C r := by
  exact (elementarySubstitution R).commutes r

theorem elementarySubstitution_injective : Function.Injective (elementarySubstitution R) :=
  Subtype.val_injective.comp (MvPolynomial.esymmAlgEquiv (Fin 4) R (by simp)).injective

theorem elementarySubstitution_mem (p : MvPolynomial (Fin 4) R) :
    (elementarySubstitution R p).IsSymmetric :=
  (MvPolynomial.esymmAlgEquiv (Fin 4) R (by simp) p).property

theorem exists_elementarySubstitution_iff (p : MvPolynomial (Fin 4) R) :
    (∃ q, elementarySubstitution R q = p) ↔ p.IsSymmetric := by
  constructor
  · rintro ⟨q, rfl⟩
    exact elementarySubstitution_mem R q
  · intro hp
    obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgEquiv (n := 4) (Fin 4) R (by simp)).surjective ⟨p, hp⟩
    exact ⟨q, congrArg Subtype.val hq⟩

end OneBlock

/-- Substitute elementary symmetric coordinates in the first block only. -/
def leftSubstitution : BlockPolynomial K →ₐ[K] BlockPolynomial K :=
  (nestedEquiv K).symm.toAlgHom.comp
    (((elementarySubstitution (InnerPolynomial K)).restrictScalars K).comp
      (nestedEquiv K).toAlgHom)

/-- Substitute elementary symmetric coordinates in the second block only. -/
def rightSubstitution : BlockPolynomial K →ₐ[K] BlockPolynomial K :=
  (polynomialSwap K).toAlgHom.comp ((leftSubstitution K).comp (polynomialSwap K).toAlgHom)

theorem leftSubstitution_injective : Function.Injective (leftSubstitution K) :=
  (nestedEquiv K).symm.injective.comp
    ((elementarySubstitution_injective (InnerPolynomial K)).comp (nestedEquiv K).injective)

theorem rightSubstitution_injective : Function.Injective (rightSubstitution K) :=
  (polynomialSwap K).injective.comp
    ((leftSubstitution_injective K).comp (polynomialSwap K).injective)

theorem exists_leftSubstitution_iff (p : BlockPolynomial K) :
    (∃ q, leftSubstitution K q = p) ↔ ∀ σ, leftRename K σ p = p := by
  rw [show (∃ q, leftSubstitution K q = p) ↔
    ∃ q, elementarySubstitution (InnerPolynomial K) q = nestedEquiv K p from by
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨nestedEquiv K q, by simpa [leftSubstitution] using congrArg (nestedEquiv K) hq⟩
      · rintro ⟨q, hq⟩
        refine ⟨(nestedEquiv K).symm q, ?_⟩
        apply (nestedEquiv K).injective
        simpa [leftSubstitution] using hq,
    exists_elementarySubstitution_iff]
  constructor
  · intro hp σ
    apply (nestedEquiv K).injective
    rw [nestedEquiv_leftRename, hp σ]
  · intro hp σ
    rw [← nestedEquiv_leftRename, hp σ]

theorem exists_rightSubstitution_iff (p : BlockPolynomial K) :
    (∃ q, rightSubstitution K q = p) ↔ ∀ σ, rightRename K σ p = p := by
  constructor
  · rintro ⟨q, rfl⟩ σ
    apply (polynomialSwap K).injective
    rw [swap_rightRename]
    have hp := (exists_leftSubstitution_iff K
      (leftSubstitution K (polynomialSwap K q))).mp ⟨polynomialSwap K q, rfl⟩ σ
    simpa [rightSubstitution] using hp
  · intro hp
    have hs : ∀ σ, leftRename K σ (polynomialSwap K p) = polynomialSwap K p := by
      intro σ
      rw [← swap_rightRename, hp σ]
    obtain ⟨q, hq⟩ := (exists_leftSubstitution_iff K (polynomialSwap K p)).mpr hs
    refine ⟨polynomialSwap K q, ?_⟩
    simpa [rightSubstitution] using
      congrArg (polynomialSwap K) hq

/-- The actual elementary symmetric polynomials in the two original blocks. -/
def elementaryPolynomial : BlockIndex → BlockPolynomial K
  | .inl i => MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin 4) K (i + 1))
  | .inr i => MvPolynomial.rename Sum.inr (MvPolynomial.esymm (Fin 4) K (i + 1))

theorem nestedEquiv_rename_left (p : InnerPolynomial K) :
    nestedEquiv K (MvPolynomial.rename Sum.inl p) = MvPolynomial.map MvPolynomial.C p := by
  exact DFunLike.congr_fun (MvPolynomial.sumAlgEquiv_comp_rename_inl
    (R := K) (S₁ := Fin 4) (S₂ := Fin 4)) p

@[simp] theorem leftSubstitution_X_left (i : Fin 4) :
    leftSubstitution K (X (.inl i)) = elementaryPolynomial K (.inl i) := by
  apply (nestedEquiv K).injective
  change nestedEquiv K (leftSubstitution K (X (.inl i))) =
    nestedEquiv K (MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin 4) K (i + 1)))
  rw [nestedEquiv_rename_left, MvPolynomial.map_esymm]
  simp [leftSubstitution, nestedEquiv]

@[simp] theorem leftSubstitution_X_right (i : Fin 4) :
    leftSubstitution K (X (.inr i)) = X (.inr i) := by
  simp [leftSubstitution, nestedEquiv]

@[simp] theorem polynomialSwap_elementaryPolynomial (i : BlockIndex) :
    polynomialSwap K (elementaryPolynomial K i) = elementaryPolynomial K (Sum.swap i) := by
  rcases i with i | i <;>
    simp [polynomialSwap, elementaryPolynomial, renameEquiv_apply, rename_rename, Function.comp_def]

@[simp] theorem rightSubstitution_X_left (i : Fin 4) :
    rightSubstitution K (X (.inl i)) = X (.inl i) := by
  simp [rightSubstitution]

@[simp] theorem rightSubstitution_X_right (i : Fin 4) :
    rightSubstitution K (X (.inr i)) = elementaryPolynomial K (.inr i) := by
  simp [rightSubstitution]

@[simp] theorem rightRename_rename_left (σ : Equiv.Perm (Fin 4)) (p : InnerPolynomial K) :
    rightRename K σ (MvPolynomial.rename Sum.inl p) = MvPolynomial.rename Sum.inl p := by
  simp [rightRename, renameEquiv_apply, rename_rename, Function.comp_def]

@[simp] theorem leftRename_rename_right (σ : Equiv.Perm (Fin 4)) (p : InnerPolynomial K) :
    leftRename K σ (MvPolynomial.rename Sum.inr p) = MvPolynomial.rename Sum.inr p := by
  simp [leftRename, renameEquiv_apply, rename_rename, Function.comp_def]

theorem rightRename_leftSubstitution (σ : Equiv.Perm (Fin 4)) (p : BlockPolynomial K) :
    rightRename K σ (leftSubstitution K p) = leftSubstitution K (rightRename K σ p) := by
  have h : (rightRename K σ).toAlgHom.comp (leftSubstitution K) =
      (leftSubstitution K).comp (rightRename K σ).toAlgHom := by
    ext i
    rcases i with i | i <;> simp [elementaryPolynomial]
  exact DFunLike.congr_fun h p

theorem leftSubstitution_rename_right (p : InnerPolynomial K) :
    leftSubstitution K (MvPolynomial.rename Sum.inr p) = MvPolynomial.rename Sum.inr p := by
  have h : (leftSubstitution K).comp (MvPolynomial.rename Sum.inr) =
      (MvPolynomial.rename Sum.inr : InnerPolynomial K →ₐ[K] BlockPolynomial K) := by
    ext i
    simp
  exact DFunLike.congr_fun h p

/-- Simultaneously substitute the eight displayed elementary symmetric polynomials. -/
def blockSubstitution : BlockPolynomial K →ₐ[K] BlockPolynomial K :=
  (leftSubstitution K).comp (rightSubstitution K)

@[simp] theorem blockSubstitution_X (i : BlockIndex) :
    blockSubstitution K (X i) = elementaryPolynomial K i := by
  rcases i with i | i <;>
    simp [blockSubstitution, elementaryPolynomial, leftSubstitution_rename_right]

theorem blockSubstitution_eq_aeval :
    blockSubstitution K = MvPolynomial.aeval (elementaryPolynomial K) := by
  ext i
  simp

theorem blockSubstitution_injective : Function.Injective (blockSubstitution K) :=
  (leftSubstitution_injective K).comp (rightSubstitution_injective K)

/-- The two elementary symmetric quadruples are algebraically independent over `K`. -/
theorem algebraicIndependent_elementaryPolynomial :
    AlgebraicIndependent K (elementaryPolynomial K) := by
  rw [algebraicIndependent_iff_injective_aeval, ← blockSubstitution_eq_aeval]
  exact blockSubstitution_injective K

theorem blockSubstitution_fixed (p : BlockPolynomial K) :
    (∀ σ, leftRename K σ (blockSubstitution K p) = blockSubstitution K p) ∧
      (∀ σ, rightRename K σ (blockSubstitution K p) = blockSubstitution K p) := by
  constructor
  · exact (exists_leftSubstitution_iff K _).mp ⟨rightSubstitution K p, rfl⟩
  · intro σ
    change rightRename K σ (leftSubstitution K (rightSubstitution K p)) = _
    rw [rightRename_leftSubstitution,
      (exists_rightSubstitution_iff K _).mp ⟨p, rfl⟩ σ]
    rfl

/-- Every actual separately symmetric polynomial is a polynomial in the eight elementary ones. -/
theorem exists_blockSubstitution_iff (p : BlockPolynomial K) :
    (∃ q, blockSubstitution K q = p) ↔
      (∀ σ, leftRename K σ p = p) ∧ (∀ σ, rightRename K σ p = p) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact blockSubstitution_fixed K q
  · rintro ⟨hleft, hright⟩
    obtain ⟨q, hq⟩ := (exists_leftSubstitution_iff K p).mpr hleft
    have hqr : ∀ σ, rightRename K σ q = q := by
      intro σ
      apply leftSubstitution_injective K
      rw [← rightRename_leftSubstitution, hq, hright σ]
    obtain ⟨r, hr⟩ := (exists_rightSubstitution_iff K q).mpr hqr
    exact ⟨r, by simp only [blockSubstitution, AlgHom.comp_apply, hr, hq]⟩

/-- The product group acts on the original eight polynomial variables by separate permutations. -/
def polynomialActionHom : BlockGroup →* (BlockPolynomial K ≃ₐ[K] BlockPolynomial K) where
  toFun g := MvPolynomial.renameEquiv K (Equiv.sumCongr g.1 g.2)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | i <;> simp [renameEquiv_apply]
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | i <;> simp [renameEquiv_apply]

instance polynomialMulSemiringAction : MulSemiringAction BlockGroup (BlockPolynomial K) :=
  MulSemiringAction.compHom (BlockPolynomial K) (polynomialActionHom K)

instance polynomialSmulCommClass : SMulCommClass BlockGroup K (BlockPolynomial K) where
  smul_comm g a p := (polynomialActionHom K g).toLinearEquiv.map_smul a p

theorem polynomial_smul (g : BlockGroup) (p : BlockPolynomial K) :
    g • p = leftRename K g.1 (rightRename K g.2 p) := by
  have h : (polynomialActionHom K g).toAlgHom =
      (leftRename K g.1).toAlgHom.comp (rightRename K g.2).toAlgHom := by
    ext i
    rcases i with i | i <;> simp [polynomialActionHom, renameEquiv_apply]
  exact DFunLike.congr_fun h p

@[simp] theorem leftRename_one (p : BlockPolynomial K) : leftRename K 1 p = p := by
  have h : (leftRename K 1).toAlgHom = AlgHom.id K (BlockPolynomial K) := by
    ext i
    rcases i with i | i <;> simp
  exact DFunLike.congr_fun h p

@[simp] theorem rightRename_one (p : BlockPolynomial K) : rightRename K 1 p = p := by
  have h : (rightRename K 1).toAlgHom = AlgHom.id K (BlockPolynomial K) := by
    ext i
    rcases i with i | i <;> simp
  exact DFunLike.congr_fun h p

/-- The actual subalgebra of polynomials fixed by `S₄ × S₄`. -/
abbrev polynomialInvariants : Subalgebra K (BlockPolynomial K) :=
  FixedPoints.subalgebra K (BlockPolynomial K) BlockGroup

theorem mem_polynomialInvariants (p : BlockPolynomial K) :
    p ∈ polynomialInvariants K ↔
      (∀ σ, leftRename K σ p = p) ∧ (∀ σ, rightRename K σ p = p) := by
  change (∀ g : BlockGroup, g • p = p) ↔ _
  constructor
  · intro hp
    exact ⟨fun σ => by simpa [polynomial_smul] using hp (σ, 1),
      fun σ => by simpa [polynomial_smul] using hp (1, σ)⟩
  · rintro ⟨hl, hr⟩ g
    rw [polynomial_smul, hr g.2, hl g.1]

theorem blockSubstitution_range : (blockSubstitution K).range = polynomialInvariants K := by
  ext p
  exact (exists_blockSubstitution_iff K p).trans (mem_polynomialInvariants K p).symm

/-- The invariant polynomial ring is exactly a polynomial algebra in the two elementary quadruples. -/
def elementaryPolynomialEquiv : BlockPolynomial K ≃ₐ[K] polynomialInvariants K :=
  AlgEquiv.ofBijective
    ((blockSubstitution K).codRestrict (polynomialInvariants K)
      (fun p => (mem_polynomialInvariants K _).mpr (blockSubstitution_fixed K p)))
    ⟨fun p q hpq => blockSubstitution_injective K (congrArg Subtype.val hpq), fun p => by
      obtain ⟨q, hq⟩ := (exists_blockSubstitution_iff K p.val).mpr
        ((mem_polynomialInvariants K p.val).mp p.property)
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] theorem elementaryPolynomialEquiv_apply_coe (p : BlockPolynomial K) :
    (elementaryPolynomialEquiv K p).val = blockSubstitution K p := rfl

@[simp] theorem elementaryPolynomialEquiv_X_coe (i : BlockIndex) :
    (elementaryPolynomialEquiv K (X i)).val = elementaryPolynomial K i :=
  blockSubstitution_X K i

instance fieldMulSemiringAction : MulSemiringAction BlockGroup (BlockField K) :=
  IsFractionRing.mulSemiringAction BlockGroup (BlockPolynomial K) (BlockField K)

instance fieldSmulDistribClass : SMulDistribClass BlockGroup (BlockPolynomial K) (BlockField K) :=
  IsFractionRing.smulDistribClass BlockGroup (BlockPolynomial K) (BlockField K)

instance fieldSmulCommClass : SMulCommClass BlockGroup K (BlockField K) :=
  IsFractionRing.smulCommClass BlockGroup K (BlockPolynomial K) K (BlockField K)

/-- The actual intermediate field of separately symmetric rational functions. -/
def rationalInvariants : IntermediateField K (BlockField K) where
  __ := FixedPoints.subfield BlockGroup (BlockField K)
  algebraMap_mem' a g := smul_algebraMap g a

@[simp] theorem mem_rationalInvariants (z : BlockField K) :
    z ∈ rationalInvariants K ↔ ∀ g : BlockGroup, g • z = z := Iff.rfl

/-- Include an actual invariant polynomial into the actual invariant rational field. -/
def invariantPolynomialInclusion : polynomialInvariants K →ₐ[K] rationalInvariants K :=
  (((IsScalarTower.toAlgHom K (BlockPolynomial K) (BlockField K)).comp
    (polynomialInvariants K).val).codRestrict (rationalInvariants K).toSubalgebra (by
      intro p g
      change g • algebraMap (BlockPolynomial K) (BlockField K) p.val = _
      rw [← algebraMap.coe_smul', p.property g]
      rfl))

theorem invariantPolynomialInclusion_injective :
    Function.Injective (invariantPolynomialInclusion K) := by
  intro p q hpq
  apply Subtype.ext
  exact IsFractionRing.injective (BlockPolynomial K) (BlockField K) (congrArg Subtype.val hpq)

/-- The canonical fraction map lands in the actual fixed field. -/
def invariantFractionMap : FractionRing (polynomialInvariants K) →ₐ[K] rationalInvariants K :=
  IsFractionRing.liftAlgHom (invariantPolynomialInclusion_injective K)

@[simp] theorem invariantFractionMap_algebraMap (p : polynomialInvariants K) :
    invariantFractionMap K (algebraMap (polynomialInvariants K)
      (FractionRing (polynomialInvariants K)) p) = invariantPolynomialInclusion K p := by
  simp [invariantFractionMap]

/-- Finite-group invariant fractions come from fractions of the actual invariant ring. -/
theorem invariantFractionMap_surjective : Function.Surjective (invariantFractionMap K) := by
  let A := polynomialInvariants K
  let : Algebra (FractionRing A) (BlockField K) := FractionRing.liftAlgebra A (BlockField K)
  let : IsScalarTower A (FractionRing A) (BlockField K) :=
    FractionRing.isScalarTower_liftAlgebra A (BlockField K)
  let : Algebra.IsInvariant A (BlockPolynomial K) BlockGroup :=
    ⟨fun p hp => ⟨⟨p, hp⟩, rfl⟩⟩
  have hfixed : Algebra.IsInvariant (FractionRing A) (BlockField K) BlockGroup :=
    IsFractionRing.isInvariant BlockGroup A (BlockPolynomial K) (FractionRing A) (BlockField K)
  have hcomp : (rationalInvariants K).val.toRingHom.comp (invariantFractionMap K).toRingHom =
      algebraMap (FractionRing A) (BlockField K) := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro p
    change (invariantFractionMap K (algebraMap A (FractionRing A) p)).val = _
    rw [invariantFractionMap_algebraMap]
    change algebraMap (BlockPolynomial K) (BlockField K) p.val =
      algebraMap (FractionRing A) (BlockField K) (algebraMap A (FractionRing A) p)
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  intro z
  obtain ⟨w, hw⟩ := hfixed.isInvariant z.val z.property
  refine ⟨w, Subtype.ext ?_⟩
  exact (DFunLike.congr_fun hcomp w).trans hw

/-- The actual fixed rational field is the fraction field of the actual fixed polynomial ring. -/
def invariantFractionEquiv :
    FractionRing (polynomialInvariants K) ≃ₐ[K] rationalInvariants K :=
  AlgEquiv.ofBijective (invariantFractionMap K)
    ⟨(invariantFractionMap K).injective, invariantFractionMap_surjective K⟩

@[simp] theorem invariantFractionEquiv_apply (z : FractionRing (polynomialInvariants K)) :
    invariantFractionEquiv K z = invariantFractionMap K z := rfl

/-- The eight independent abstract elementary coordinates identify with the actual rational invariants. -/
def elementaryFieldEquiv : BlockField K ≃ₐ[K] rationalInvariants K :=
  (IsFractionRing.algEquivOfAlgEquiv (elementaryPolynomialEquiv K)).trans
    (invariantFractionEquiv K)

@[simp] theorem elementaryFieldEquiv_algebraMap (p : BlockPolynomial K) :
    (elementaryFieldEquiv K (algebraMap (BlockPolynomial K) (BlockField K) p)).val =
      algebraMap (BlockPolynomial K) (BlockField K) (blockSubstitution K p) := by
  simp only [elementaryFieldEquiv, AlgEquiv.trans_apply,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap, invariantFractionEquiv_apply,
    invariantFractionMap_algebraMap]
  rfl

def elementaryCoordinate (i : BlockIndex) : BlockField K :=
  algebraMap (BlockPolynomial K) (BlockField K) (elementaryPolynomial K i)

@[simp] theorem elementaryFieldEquiv_coordinate (i : BlockIndex) :
    (elementaryFieldEquiv K (PermutationInvariants.coordinate K i)).val =
      elementaryCoordinate K i := by
  simp [PermutationInvariants.coordinate, elementaryCoordinate]

theorem algebraicIndependent_elementaryCoordinate :
    AlgebraicIndependent K (elementaryCoordinate K) :=
  (algebraicIndependent_elementaryPolynomial K).map
    (f := IsScalarTower.toAlgHom K (BlockPolynomial K) (BlockField K))
    (IsFractionRing.injective _ _).injOn

/-- The displayed elementary rational functions generate exactly the actual separate fixed field. -/
theorem rationalInvariants_eq_adjoin :
    rationalInvariants K = IntermediateField.adjoin K (Set.range (elementaryCoordinate K)) := by
  let E := IntermediateField.adjoin K (Set.range (elementaryCoordinate K))
  have hcoordinate (i : BlockIndex) : elementaryCoordinate K i ∈ E :=
    IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  have hpoly (p : BlockPolynomial K) :
      algebraMap (BlockPolynomial K) (BlockField K) (blockSubstitution K p) ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C a =>
        change algebraMap (BlockPolynomial K) (BlockField K)
          (blockSubstitution K (algebraMap K (BlockPolynomial K) a)) ∈ E
        rw [(blockSubstitution K).commutes, ← IsScalarTower.algebraMap_apply]
        exact E.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
    | mul_X p i hp =>
        simpa only [map_mul, blockSubstitution_X, elementaryCoordinate] using
          E.mul_mem hp (hcoordinate i)
  have hfield (z : BlockField K) : (elementaryFieldEquiv K z).val ∈ E := by
    obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (BlockPolynomial K) z
    simpa only [map_div₀, IntermediateField.coe_div, elementaryFieldEquiv_algebraMap] using
      E.div_mem (hpoly p) (hpoly q)
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw⟩ := (elementaryFieldEquiv K).surjective ⟨z, hz⟩
    simpa only [hw] using hfield w
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change elementaryCoordinate K i ∈ rationalInvariants K
    simpa only [elementaryFieldEquiv_coordinate] using
      (elementaryFieldEquiv K (PermutationInvariants.coordinate K i)).property

/-- The actual separate fixed field is rational of transcendence degree eight. -/
theorem rationalInvariants_rational : RationalOfDimension K (rationalInvariants K) 8 := by
  let e : RationalField K 8 ≃ₐ[K] BlockField K :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K
      ((Fintype.equivFinOfCardEq (show Fintype.card BlockIndex = 8 by decide)).symm))
  exact ⟨(e.trans (elementaryFieldEquiv K)).symm⟩

theorem blockSubstitution_polynomialSwap (p : BlockPolynomial K) :
    blockSubstitution K (polynomialSwap K p) = polynomialSwap K (blockSubstitution K p) := by
  have h : (blockSubstitution K).comp (polynomialSwap K).toAlgHom =
      (polynomialSwap K).toAlgHom.comp (blockSubstitution K) := by
    ext i
    simp
  exact DFunLike.congr_fun h p

@[simp] theorem ambientSwap_algebraMap (p : BlockPolynomial K) :
    PermutationInvariants.swap K (algebraMap (BlockPolynomial K) (BlockField K) p) =
      algebraMap (BlockPolynomial K) (BlockField K) (polynomialSwap K p) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin 4) (Fin 4))) p

@[simp] theorem ambientSwap_elementaryCoordinate (i : BlockIndex) :
    PermutationInvariants.swap K (elementaryCoordinate K i) =
      elementaryCoordinate K (Sum.swap i) := by
  simp [elementaryCoordinate]

/-- The elementary-coordinate identification respects the actual interchange of the two blocks. -/
theorem elementaryFieldEquiv_swap_coe (z : PermutationInvariants.CoordinateField K) :
    (elementaryFieldEquiv K (PermutationInvariants.swap K z)).val =
      PermutationInvariants.swap K (elementaryFieldEquiv K z).val := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (BlockPolynomial K) z
  simp only [map_div₀, IntermediateField.coe_div, ambientSwap_algebraMap,
    elementaryFieldEquiv_algebraMap, blockSubstitution_polynomialSwap]

/-- Block interchange on the actual `S₄ × S₄` fixed field. -/
def invariantSwap : rationalInvariants K ≃ₐ[K] rationalInvariants K :=
  (elementaryFieldEquiv K).symm.trans ((PermutationInvariants.swap K).trans
    (elementaryFieldEquiv K))

@[simp] theorem invariantSwap_coe (z : rationalInvariants K) :
    (invariantSwap K z).val = PermutationInvariants.swap K z.val := by
  obtain ⟨w, rfl⟩ := (elementaryFieldEquiv K).surjective z
  simp [invariantSwap, elementaryFieldEquiv_swap_coe]

theorem invariantSwap_involutive : Function.Involutive (invariantSwap K) := by
  intro z
  apply Subtype.ext
  simp only [invariantSwap_coe, PermutationInvariants.swap_involutive K z.val]

end M9.SymmetricBlockInvariants
