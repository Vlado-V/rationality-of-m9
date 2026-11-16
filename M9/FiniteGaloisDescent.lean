module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic

/-!
# Finite Galois descent for actual semilinear vector spaces

The base is the actual `FixedPoints.subfield G L`. The action on the vector
space is an ordinary additive group action together with the standard
`SMulDistribClass G L V` semilinearity law. No descent or trivialization
conclusion is supplied as a hypothesis.

The proof uses Dedekind independence of field characters to construct
weighted orbit sums spanning the original vector space. An invariant basis
then descends to a basis of the actual fixed vectors over the fixed subfield.
This is the field-level algebraic input to the two no-name applications in
Section 6 of the pinned eight-page M9 manuscript.
-/

@[expose] public section
noncomputable section

namespace M9.FiniteGaloisDescent

open Module Submodule
open scoped BigOperators TensorProduct

variable (G L V : Type*) [Group G] [Field L] [MulSemiringAction G L]
  [AddCommGroup V] [Module L V] [DistribMulAction G V] [SMulDistribClass G L V]

/-- The actual field of elements fixed by the given group action. -/
abbrev FixedField := FixedPoints.subfield G L

/-- The actual fixed vectors, as a vector subspace over the actual fixed field. -/
def fixedVectors : Submodule (FixedField G L) V where
  carrier := MulAction.fixedPoints G V
  zero_mem' g := smul_zero g
  add_mem' hx hy g := by rw [smul_add, hx g, hy g]
  smul_mem' a x hx g := by
    change g • ((a : L) • x) = (a : L) • x
    rw [smul_distrib_smul, a.property g, hx g]

@[simp] theorem mem_fixedVectors (v : V) :
    v ∈ fixedVectors G L V ↔ ∀ g : G, g • v = v := Iff.rfl

/-- Artin's finite fixed-field theorem applies to the actual fixed subfield. -/
theorem fixedField_isGalois [Finite G] : IsGalois (FixedField G L) L :=
  IsGalois.of_fixed_field L G

theorem fixedField_finiteDimensional [Finite G] : FiniteDimensional (FixedField G L) L :=
  inferInstance

theorem finrank_fixedField [Fintype G] [FaithfulSMul G L] :
    finrank (FixedField G L) L = Fintype.card G :=
  FixedPoints.finrank_eq_card G L

section Spanning

variable [Fintype G] [FaithfulSMul G L]

def identityDelta : G → L := by
  classical
  exact Pi.single (1 : G) (1 : L)

/-- Dedekind independence of the actual field automorphisms gives a finite
linear combination of their evaluation columns equal to the identity delta. -/
theorem exists_deltaCoefficients :
    ∃ c : L →₀ L, ∀ g : G,
      (∑ a ∈ c.support, c a * (g • a)) = identityDelta G L g := by
  classical
  have hli : LinearIndependent L (fun g : G => (fun a : L => g • a)) := by
    exact (linearIndependent_monoidHom L L).comp
      (fun g => (MulSemiringAction.toRingAut G L g).toMonoidHom) (by
        intro g h heq
        apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
        intro a
        exact congrArg (fun f : L →* L => f a) heq)
  have hspan : span L (Set.range (fun a : L => (fun g : G => g • a))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hdelta : identityDelta G L ∈
      span L (Set.range (fun a : L => (fun g : G => g • a))) :=
    hspan.ge (Submodule.mem_top : identityDelta G L ∈ (⊤ : Submodule L (G → L)))
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hdelta
  refine ⟨c, ?_⟩
  intro g
  have hg := congrFun hc g
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, identityDelta] using hg

/-- A weighted orbit sum in the actual semilinear vector space. -/
def orbitSum (a : L) (v : V) : V := ∑ g : G, g • (a • v)

omit [FaithfulSMul G L] in
theorem orbitSum_fixed (a : L) (v : V) : orbitSum G L V a v ∈ fixedVectors G L V := by
  intro g
  simp only [orbitSum, Finset.smul_sum, ← mul_smul]
  exact Fintype.sum_bijective (fun h : G => g*h) (Group.mulLeft_bijective g)
    (fun h => (g*h) • (a • v)) (fun h => h • (a • v)) (fun h => rfl)

omit [FaithfulSMul G L] in
/-- The delta coefficients reconstruct every actual vector from fixed
weighted orbit sums. This proof uses no division by the group order. -/
theorem orbitSum_reconstruction (c : L →₀ L)
    (hc : ∀ g : G, (∑ a ∈ c.support, c a * (g • a)) = identityDelta G L g)
    (v : V) : (∑ a ∈ c.support, c a • orbitSum G L V a v) = v := by
  classical
  calc
    (∑ a ∈ c.support, c a • orbitSum G L V a v) =
        ∑ g : G, (∑ a ∈ c.support, c a * (g • a)) • (g • v) := by
      simp only [orbitSum, Finset.smul_sum, smul_distrib_smul, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    _ = ∑ g : G, identityDelta G L g • (g • v) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hc g]
    _ = v := by simp [identityDelta, Pi.single_apply]

/-- The actual fixed vectors span the entire original space after extending
scalars to the original field. This holds even without finite dimension. -/
theorem span_fixedVectors_eq_top :
    span L (fixedVectors G L V : Set V) = ⊤ := by
  classical
  obtain ⟨c,hc⟩ := exists_deltaCoefficients G L
  apply eq_top_iff.mpr
  intro v _
  rw [← orbitSum_reconstruction G L V c hc v]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span (orbitSum_fixed G L V a v))

end Spanning

section BasisDescent

variable {ι : Type*} [Fintype ι]

/-- In an invariant basis the entire semilinear action is coefficientwise.
This is the coordinate trivialization supplied by descent. -/
theorem basisCoordinates_smul (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (v : V) (i : ι) :
    b.equivFun (g • v) i = g • b.equivFun v i := by
  classical
  have hsum := congrArg (fun y : V => g • y) (b.sum_repr v)
  simp only [Finset.smul_sum, smul_distrib_smul, hb] at hsum
  have hcoord := congrArg (fun y : V => b.repr y i) hsum
  simpa [map_sum, map_smul, Finsupp.single_apply, Basis.equivFun_apply] using hcoord.symm

/-- Coordinates of a fixed vector in a fixed basis are actual fixed-field
elements. This is proved by uniqueness of the original field coordinates. -/
theorem basisCoordinates_fixed (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (x : fixedVectors G L V) (i : ι) :
    b.repr x.val i ∈ FixedField G L := by
  classical
  intro g
  have hsum := congrArg (fun y : V => g • y) (b.sum_repr x.val)
  simp only [Finset.smul_sum, smul_distrib_smul, hb, x.property g] at hsum
  have hcoord := congrArg (fun y : V => b.repr y i) hsum
  simpa [map_sum, map_smul, Finsupp.single_apply] using hcoord

/-- Any original-field basis consisting of fixed vectors is also a basis
of the actual fixed-vector space over the actual fixed field. -/
def basisFixedVectors (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) :
    Basis ι (FixedField G L) (fixedVectors G L V) := by
  classical
  let v : ι → fixedVectors G L V := fun i => ⟨b i,fun g => hb g i⟩
  have hli : LinearIndependent (FixedField G L) v :=
    LinearIndependent.of_comp (fixedVectors G L V).subtype
      (b.linearIndependent.restrict_scalars' (FixedField G L))
  refine Basis.mk hli ?_
  intro x _
  let c : ι → FixedField G L := fun i =>
    ⟨b.repr x.val i, basisCoordinates_fixed G L V b hb x i⟩
  have hsum : (∑ i, c i • v i) = x := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ i, b.repr x.val i • b i) = x.val
    exact b.sum_repr x.val
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

@[simp] theorem basisFixedVectors_val (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (i : ι) :
    (basisFixedVectors G L V b hb i).val = b i := by
  simp only [basisFixedVectors, Basis.mk_apply]

/-- The descended coordinates include into the original field as exactly
the original basis coordinates. -/
theorem basisFixedVectors_repr_coe (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (x : fixedVectors G L V) (i : ι) :
    (((basisFixedVectors G L V b hb).repr x i : FixedField G L) : L) = b.repr x.val i := by
  classical
  have hsum := congrArg Subtype.val ((basisFixedVectors G L V b hb).sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  change (∑ j, (((basisFixedVectors G L V b hb).repr x j : FixedField G L) : L) •
    (basisFixedVectors G L V b hb j).val) = x.val at hsum
  simp only [basisFixedVectors_val] at hsum
  have hcoord := congrArg (fun y : V => b.repr y i) hsum
  simpa [map_sum, map_smul, Finsupp.single_apply] using hcoord

end BasisDescent

section FiniteDimensionalDescent

variable [Finite G] [FaithfulSMul G L] [FiniteDimensional L V]

/-- Genuine finite semilinear descent: there is an original-field basis
made entirely of actual invariant vectors. -/
theorem exists_fixed_basis :
    ∃ b : Basis (Fin (finrank L V)) L V, ∀ (g : G) (i : Fin (finrank L V)),
      g • b i = b i := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hspan : ⊤ ≤ span L (fixedVectors G L V : Set V) :=
    (span_fixedVectors_eq_top G L V).ge
  let b := Basis.ofSpan hspan
  let := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, ?_⟩
  intro g i
  have hfix : b (e.symm i) ∈ fixedVectors G L V :=
    Basis.ofSpan_subset hspan (Set.mem_range_self (e.symm i))
  simpa only [Basis.coe_reindex, Function.comp_apply] using hfix g

/-- An invariant basis, constructed from the actual action and the theorem
above, rather than specified as descent data. -/
def invariantBasis : Basis (Fin (finrank L V)) L V :=
  Classical.choose (exists_fixed_basis G L V)

theorem invariantBasis_fixed (g : G) (i : Fin (finrank L V)) :
    g • invariantBasis G L V i = invariantBasis G L V i :=
  Classical.choose_spec (exists_fixed_basis G L V) g i

/-- The descended basis of the actual fixed-vector space. -/
def descendedBasis : Basis (Fin (finrank L V)) (FixedField G L) (fixedVectors G L V) :=
  basisFixedVectors G L V (invariantBasis G L V) (invariantBasis_fixed G L V)

instance fixedVectors_finiteDimensional : FiniteDimensional (FixedField G L) (fixedVectors G L V) :=
  (descendedBasis G L V).finiteDimensional_of_finite

/-- The actual fixed-vector space has the same dimension over the actual
fixed subfield as the original vector space over the original field. -/
theorem finrank_fixedVectors :
    finrank (FixedField G L) (fixedVectors G L V) = finrank L V := by
  rw [finrank_eq_card_basis (descendedBasis G L V), Fintype.card_fin]

/-- Genuine linear coordinates in which the original action changes only
the coefficient field. In particular, the coordinate variables can be
chosen invariant before passing to polynomial or rational functions. -/
theorem exists_coefficientwise_coordinates :
    ∃ e : V ≃ₗ[L] (Fin (finrank L V) → L),
      ∀ (g : G) (v : V), e (g • v) = fun i => g • e v i := by
  refine ⟨(invariantBasis G L V).equivFun, ?_⟩
  intro g v
  funext i
  exact basisCoordinates_smul G L V (invariantBasis G L V) (invariantBasis_fixed G L V) g v i

/-- Scalar extension of the actual fixed-vector space is the original
vector space. The pure-tensor formula below identifies this equivalence
with the canonical scalar multiplication map. -/
def scalarExtensionEquiv :
    (L ⊗[FixedField G L] fixedVectors G L V) ≃ₗ[L] V :=
  ((descendedBasis G L V).baseChange L).equivFun.trans (invariantBasis G L V).equivFun.symm

@[simp] theorem scalarExtensionEquiv_tmul (a : L) (x : fixedVectors G L V) :
    scalarExtensionEquiv G L V (a ⊗ₜ[FixedField G L] x) = a • x.val := by
  apply (invariantBasis G L V).equivFun.injective
  simp only [scalarExtensionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext i
  simp only [Basis.equivFun_apply, Basis.baseChange_repr_tmul]
  have hc := basisFixedVectors_repr_coe G L V (invariantBasis G L V)
    (invariantBasis_fixed G L V) x i
  change (((descendedBasis G L V).repr x i : FixedField G L) : L) * a = _
  rw [show (((descendedBasis G L V).repr x i : FixedField G L) : L) =
      (invariantBasis G L V).repr x.val i from hc]
  simp [map_smul, mul_comm]

end FiniteDimensionalDescent

end M9.FiniteGaloisDescent
