module

public import M9.FiniteGaloisDescent
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Tactic

/-!
# Finite-group no-name descent at the actual rational-field level

The coefficient fixed field is `FixedPoints.subfield G L`.  A finite
denominator norm proves that the fixed rational functions in independent
fixed variables are exactly the rational functions over this fixed field.
An actual fixed basis then supplies polynomial and rational coordinates on
the symmetric algebra of the semilinear degree-one coordinate module.

This is the field-algebra step.  A geometric free-locus or bundle descent
identification is a separate input to its applications.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.FiniteNoNameField

open scoped BigOperators

variable (G L : Type*) [Group G] [Field L] [MulSemiringAction G L]
variable (ι : Type*)

abbrev FixedField := FixedPoints.subfield G L
abbrev PolynomialRing := MvPolynomial ι L
abbrev RationalField := FractionRing (PolynomialRing L ι)

/-- The coefficient action fixes the independent variables. -/
instance polynomialAction : MulSemiringAction G (PolynomialRing L ι) where
  smul g p := MvPolynomial.map (MulSemiringAction.toRingHom G L g) p
  one_smul p := by ext α; simp
  mul_smul g h p := by ext α; simp [mul_smul]
  smul_zero g := map_zero _
  smul_add g p q := map_add _ _ _
  smul_one g := map_one _
  smul_mul g p q := map_mul _ _ _

@[simp] theorem polynomialAction_apply (g : G) (p : PolynomialRing L ι) :
    g • p = MvPolynomial.map (MulSemiringAction.toRingHom G L g) p := rfl

@[simp] theorem polynomialAction_coeff (g : G) (p : PolynomialRing L ι) (α : ι →₀ ℕ) :
    (g • p).coeff α = g • p.coeff α := by
  rw [polynomialAction_apply, MvPolynomial.coeff_map]
  rfl

instance rationalAction : MulSemiringAction G (RationalField L ι) :=
  IsFractionRing.mulSemiringAction G (PolynomialRing L ι) (RationalField L ι)

@[simp] theorem rationalAction_polynomial (g : G) (p : PolynomialRing L ι) :
    g • algebraMap (PolynomialRing L ι) (RationalField L ι) p =
      algebraMap (PolynomialRing L ι) (RationalField L ι) (g • p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

@[simp] theorem rationalAction_constant (g : G) (a : L) :
    g • algebraMap L (RationalField L ι) a = algebraMap L (RationalField L ι) (g • a) := by
  change g • algebraMap (PolynomialRing L ι) (RationalField L ι) (MvPolynomial.C a) =
    algebraMap (PolynomialRing L ι) (RationalField L ι) (MvPolynomial.C (g • a))
  rw [rationalAction_polynomial, polynomialAction_apply, MvPolynomial.map_C]
  rfl

@[simp] theorem rationalAction_variable (g : G) (i : ι) :
    g • algebraMap (PolynomialRing L ι) (RationalField L ι) (MvPolynomial.X i) =
      algebraMap (PolynomialRing L ι) (RationalField L ι) (MvPolynomial.X i) := by
  rw [rationalAction_polynomial, polynomialAction_apply, MvPolynomial.map_X]

def polynomialInclude : MvPolynomial ι (FixedField G L) →+* PolynomialRing L ι :=
  MvPolynomial.map (FixedField G L).subtype

theorem polynomialInclude_injective : Function.Injective (polynomialInclude G L ι) :=
  MvPolynomial.map_injective _ Subtype.val_injective

theorem polynomialInclude_fixed (p : MvPolynomial ι (FixedField G L)) (g : G) :
    g • polynomialInclude G L ι p = polynomialInclude G L ι p := by
  ext α
  simp only [polynomialAction_coeff, polynomialInclude, MvPolynomial.coeff_map]
  exact (p.coeff α).property g

/-- Fixed polynomial coefficients descend to the actual fixed subfield. -/
theorem fixed_polynomial_descends (p : PolynomialRing L ι) (hp : ∀ g : G, g • p = p) :
    ∃ q : MvPolynomial ι (FixedField G L), polynomialInclude G L ι q = p := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨α, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  refine ⟨⟨p.coeff α, ?_⟩, rfl⟩
  intro g
  exact (polynomialAction_coeff G L ι g p α).symm.trans
    (congrArg (fun q : PolynomialRing L ι => q.coeff α) (hp g))

def rationalInclude : FractionRing (MvPolynomial ι (FixedField G L)) →+* RationalField L ι :=
  IsFractionRing.lift (g := (algebraMap (PolynomialRing L ι) (RationalField L ι)).comp
    (polynomialInclude G L ι)) (by
      intro p q hpq
      apply polynomialInclude_injective G L ι
      exact (IsFractionRing.injective (PolynomialRing L ι) (RationalField L ι)) hpq)

@[simp] theorem rationalInclude_polynomial (p : MvPolynomial ι (FixedField G L)) :
    rationalInclude G L ι (algebraMap _ (FractionRing (MvPolynomial ι (FixedField G L))) p) =
      algebraMap (PolynomialRing L ι) (RationalField L ι) (polynomialInclude G L ι p) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] theorem rationalInclude_constant (a : FixedField G L) :
    rationalInclude G L ι (algebraMap (FixedField G L)
      (FractionRing (MvPolynomial ι (FixedField G L))) a) =
        algebraMap L (RationalField L ι) (a : L) := by
  change rationalInclude G L ι (algebraMap (MvPolynomial ι (FixedField G L))
    (FractionRing (MvPolynomial ι (FixedField G L))) (MvPolynomial.C a)) =
      algebraMap (PolynomialRing L ι) (RationalField L ι) (MvPolynomial.C (a : L))
  rw [rationalInclude_polynomial]
  simp only [polynomialInclude, MvPolynomial.map_C]
  rfl

theorem rationalInclude_fixed (f : FractionRing (MvPolynomial ι (FixedField G L))) (g : G) :
    g • rationalInclude G L ι f = rationalInclude G L ι f := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι (FixedField G L)) f
  simp only [map_div₀, rationalInclude_polynomial, smul_div₀', rationalAction_polynomial,
    polynomialInclude_fixed]

section Finite

variable [Finite G]

/-- Multiplying a denominator by all its conjugates makes an invariant
denominator.  This proves descent for rational functions, not just polynomials. -/
theorem fixed_rational_iff_descends (f : RationalField L ι) :
    (∀ g : G, g • f = f) ↔
      ∃ h : FractionRing (MvPolynomial ι (FixedField G L)), rationalInclude G L ι h = f := by
  classical
  let : Fintype G := Fintype.ofFinite G
  constructor
  · intro hf
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (PolynomialRing L ι) f
    let j := algebraMap (PolynomialRing L ι) (RationalField L ι)
    have hj : Function.Injective j := IsFractionRing.injective _ _
    have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
    have hjq : j q ≠ 0 := fun h => hq0 (hj (h.trans (map_zero j).symm))
    let d : PolynomialRing L ι := ∏ g : G, g • q
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g _ => by
      simpa only [smul_zero] using (MulAction.injective g).ne hq0)
    have hdf : ∀ g : G, g • d = d := Finset.smul_prod_perm q
    have hdiv : q ∣ d := by
      have hh := Finset.dvd_prod_of_mem (fun g : G => g • q) (Finset.mem_univ (1 : G))
      simpa only [one_smul] using hh
    obtain ⟨c, hc⟩ := hdiv
    have hjd : j d ≠ 0 := fun h => hd0 (hj (h.trans (map_zero j).symm))
    have hnum : j (p * c) = (j p / j q) * j d := by
      rw [hc, map_mul, map_mul]
      field_simp
    have hnf : ∀ g : G, g • (p * c) = p * c := by
      intro g
      apply hj
      rw [← rationalAction_polynomial, hnum, smul_mul', hf g,
        rationalAction_polynomial, hdf g]
    obtain ⟨n, hn⟩ := fixed_polynomial_descends G L ι (p * c) hnf
    obtain ⟨den, hden⟩ := fixed_polynomial_descends G L ι d hdf
    refine ⟨algebraMap _ (FractionRing (MvPolynomial ι (FixedField G L))) n /
      algebraMap _ (FractionRing (MvPolynomial ι (FixedField G L))) den, ?_⟩
    rw [map_div₀, rationalInclude_polynomial, rationalInclude_polynomial, hn, hden]
    apply (div_eq_iff hjd).mpr
    exact hnum
  · rintro ⟨h, rfl⟩ g
    exact rationalInclude_fixed G L ι h g

abbrev FixedRationalField := FixedPoints.subfield G (RationalField L ι)

theorem rationalInclude_fieldRange :
    (rationalInclude G L ι).fieldRange = FixedRationalField G L ι := by
  ext f
  exact (fixed_rational_iff_descends G L ι f).symm

def fixedRationalEquiv : FractionRing (MvPolynomial ι (FixedField G L)) ≃+*
    FixedRationalField G L ι :=
  (rationalInclude G L ι).rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr (rationalInclude_fieldRange G L ι))

def fixedBaseEmbedding : FixedField G L →+* FixedRationalField G L ι where
  toFun a := ⟨algebraMap L (RationalField L ι) (a : L), fun g => by
    rw [rationalAction_constant, a.property g]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance fixedRationalAlgebra : Algebra (FixedField G L) (FixedRationalField G L ι) :=
  (fixedBaseEmbedding G L ι).toAlgebra

/-- The actual finite-group invariant field is rational over its actual
fixed coefficient field, compatibly with the constant-field embeddings. -/
def fixedRationalAlgEquiv : FractionRing (MvPolynomial ι (FixedField G L)) ≃ₐ[FixedField G L]
    FixedRationalField G L ι where
  __ := fixedRationalEquiv G L ι
  commutes' a := by
    apply Subtype.ext
    exact rationalInclude_constant G L ι a

end Finite

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] [MulSemiringAction G B]

def transportActionHom (e : A ≃+* B) : G →* (A ≃+* A) where
  toFun g := (e.trans (MulSemiringAction.toRingEquiv G B g)).trans e.symm
  map_one' := by
    ext a
    change e.symm ((1 : G) • e a) = a
    rw [one_smul, e.symm_apply_apply]
  map_mul' g h := by
    ext a
    change e.symm ((g * h) • e a) = e.symm (g • e (e.symm (h • e a)))
    rw [e.apply_symm_apply, mul_smul]

/-- Transport a genuine ring action through a genuine coordinate isomorphism. -/
@[instance_reducible] def transportAction (e : A ≃+* B) : MulSemiringAction G A :=
  MulSemiringAction.compHom A (transportActionHom G e)

end Transport

section TransportField

variable {A B : Type*} [Field A] [Field B] [MulSemiringAction G B]

def transportedFixedField (e : A ≃+* B) : Subfield A :=
  letI := transportAction G e
  FixedPoints.subfield G A

/-- Equivariant coordinates identify the actual fixed subfields. -/
def transportFixedEquiv (e : A ≃+* B) :
    transportedFixedField G e ≃+* FixedPoints.subfield G B where
  toFun a := ⟨e a, by
    intro g
    have ha := a.property g
    change e.symm (g • e (a : A)) = (a : A) at ha
    apply e.symm.injective
    simpa only [RingEquiv.symm_apply_apply] using ha⟩
  invFun b := ⟨e.symm b, by
    intro g
    change e.symm (g • e (e.symm (b : B))) = e.symm (b : B)
    rw [e.apply_symm_apply, b.property g]⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul e a.val b.val)
  map_add' a b := Subtype.ext (map_add e a.val b.val)

end TransportField

section SymmetricCoordinates

variable (V : Type*) [AddCommGroup V] [Module L V]
variable {ι : Type*} [Fintype ι]

/-- The coordinate ring of the actual degree-one module. For functions on a
vector space, apply this to its dual representation. -/
abbrev CoordinateRing := SymmetricAlgebra L V
abbrev CoordinateField := FractionRing (CoordinateRing L V)

/-- The polynomial coordinate change supplied by an actual basis. -/
def polynomialCoordinates (b : Module.Basis ι L V) :
    CoordinateRing L V ≃ₐ[L] PolynomialRing L ι := SymmetricAlgebra.equivMvPolynomial b

/-- The same coordinate change on the actual fraction fields. -/
def rationalCoordinates (b : Module.Basis ι L V) :
    CoordinateField L V ≃ₐ[L] RationalField L ι :=
  IsFractionRing.algEquivOfAlgEquiv (polynomialCoordinates L V b)

omit [Fintype ι] in
@[simp] theorem rationalCoordinates_polynomial (b : Module.Basis ι L V)
    (p : CoordinateRing L V) :
    rationalCoordinates L V b (algebraMap (CoordinateRing L V) (CoordinateField L V) p) =
      algebraMap (PolynomialRing L ι) (RationalField L ι) (polynomialCoordinates L V b p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

theorem polynomialCoordinates_iota (b : Module.Basis ι L V) (v : V) :
    polynomialCoordinates L V b (SymmetricAlgebra.ι L V v) =
      ∑ i : ι, b.repr v i • MvPolynomial.X i := by
  calc
    _ = polynomialCoordinates L V b (SymmetricAlgebra.ι L V
        (∑ i : ι, b.repr v i • b i)) :=
      congrArg (fun w => polynomialCoordinates L V b (SymmetricAlgebra.ι L V w))
        (b.sum_repr v).symm
    _ = _ := by
      simp only [map_sum, map_smul, polynomialCoordinates, SymmetricAlgebra.equivMvPolynomial_ι_apply]

@[instance_reducible] def symmetricPolynomialAction (b : Module.Basis ι L V) : MulSemiringAction G (CoordinateRing L V) :=
  transportAction G (polynomialCoordinates L V b).toRingEquiv

@[instance_reducible] def symmetricRationalAction (b : Module.Basis ι L V) : MulSemiringAction G (CoordinateField L V) :=
  transportAction G (rationalCoordinates L V b).toRingEquiv

/-- The actual invariant subfield for the transported coordinate action. -/
abbrev SymmetricFixedField (b : Module.Basis ι L V) :=
  transportedFixedField G (rationalCoordinates L V b).toRingEquiv

omit [Fintype ι] in
theorem symmetricPolynomialAction_constant (b : Module.Basis ι L V) (g : G) (a : L) :
    letI := symmetricPolynomialAction G L V b
    g • algebraMap L (CoordinateRing L V) a = algebraMap L (CoordinateRing L V) (g • a) := by
  change (polynomialCoordinates L V b).symm
    (g • polynomialCoordinates L V b (algebraMap L (CoordinateRing L V) a)) = _
  apply (polynomialCoordinates L V b).injective
  rw [AlgEquiv.apply_symm_apply, (polynomialCoordinates L V b).commutes,
    (polynomialCoordinates L V b).commutes]
  change g • MvPolynomial.C a = MvPolynomial.C (g • a)
  rw [polynomialAction_apply, MvPolynomial.map_C]
  rfl

omit [Fintype ι] in
theorem symmetricRationalAction_constant (b : Module.Basis ι L V) (g : G) (a : L) :
    letI := symmetricRationalAction G L V b
    g • algebraMap L (CoordinateField L V) a = algebraMap L (CoordinateField L V) (g • a) := by
  change (rationalCoordinates L V b).symm
    (g • rationalCoordinates L V b (algebraMap L (CoordinateField L V) a)) = _
  apply (rationalCoordinates L V b).injective
  rw [AlgEquiv.apply_symm_apply, (rationalCoordinates L V b).commutes,
    (rationalCoordinates L V b).commutes, rationalAction_constant]

omit [Fintype ι] in
/-- The rational action really extends the polynomial action through the
canonical embedding into the actual fraction field. -/
theorem symmetricRationalAction_polynomial (b : Module.Basis ι L V) (g : G)
    (p : CoordinateRing L V) :
    letI := symmetricPolynomialAction G L V b
    letI := symmetricRationalAction G L V b
    g • algebraMap (CoordinateRing L V) (CoordinateField L V) p =
      algebraMap (CoordinateRing L V) (CoordinateField L V) (g • p) := by
  change (rationalCoordinates L V b).symm
    (g • rationalCoordinates L V b
      (algebraMap (CoordinateRing L V) (CoordinateField L V) p)) =
    algebraMap (CoordinateRing L V) (CoordinateField L V)
      ((polynomialCoordinates L V b).symm (g • polynomialCoordinates L V b p))
  apply (rationalCoordinates L V b).injective
  rw [AlgEquiv.apply_symm_apply, rationalCoordinates_polynomial,
    rationalCoordinates_polynomial, AlgEquiv.apply_symm_apply, rationalAction_polynomial]

section GivenAction

variable [DistribMulAction G V] [SMulDistribClass G L V]

theorem polynomialCoordinates_iota_smul (b : Module.Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (v : V) :
    g • polynomialCoordinates L V b (SymmetricAlgebra.ι L V v) =
      polynomialCoordinates L V b (SymmetricAlgebra.ι L V (g • v)) := by
  rw [polynomialCoordinates_iota, polynomialCoordinates_iota, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : b.repr (g • v) i = g • b.repr v i := by
    simpa only [Module.Basis.equivFun_apply] using
      FiniteGaloisDescent.basisCoordinates_smul G L V b hb g v i
  simp only [MvPolynomial.smul_eq_C_mul, polynomialAction_apply, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, hc]
  rfl

/-- The polynomial action extends the originally given semilinear action
on every degree-one vector, rather than merely fixing a new list of labels. -/
theorem symmetricPolynomialAction_iota (b : Module.Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (v : V) :
    letI := symmetricPolynomialAction G L V b
    g • SymmetricAlgebra.ι L V v = SymmetricAlgebra.ι L V (g • v) := by
  change (polynomialCoordinates L V b).symm
    (g • polynomialCoordinates L V b (SymmetricAlgebra.ι L V v)) = _
  apply (polynomialCoordinates L V b).injective
  rw [AlgEquiv.apply_symm_apply]
  exact polynomialCoordinates_iota_smul G L V b hb g v

/-- The actual fraction-field action also extends the given action on
degree-one coordinate functions. -/
theorem symmetricRationalAction_iota (b : Module.Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (v : V) :
    letI := symmetricRationalAction G L V b
    g • algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V v) =
      algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V (g • v)) := by
  change (rationalCoordinates L V b).symm
    (g • rationalCoordinates L V b
      (algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V v))) = _
  apply (rationalCoordinates L V b).injective
  rw [AlgEquiv.apply_symm_apply, rationalCoordinates_polynomial,
    rationalCoordinates_polynomial, rationalAction_polynomial,
    polynomialCoordinates_iota_smul G L V b hb g v]

end GivenAction

/-- Constants in the actual fixed field embed as actual constant rational
functions in the original symmetric-algebra fraction field. -/
def symmetricFixedBaseEmbedding (b : Module.Basis ι L V) :
    FixedField G L →+* SymmetricFixedField G L V b where
  toFun a := ⟨algebraMap L (CoordinateField L V) (a : L), by
    intro g
    change (rationalCoordinates L V b).symm
      (g • rationalCoordinates L V b (algebraMap L (CoordinateField L V) (a : L))) = _
    rw [(rationalCoordinates L V b).commutes, rationalAction_constant,
      a.property g, (rationalCoordinates L V b).symm.commutes]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance symmetricFixedAlgebra (b : Module.Basis ι L V) :
    Algebra (FixedField G L) (SymmetricFixedField G L V b) :=
  (symmetricFixedBaseEmbedding G L V b).toAlgebra

def symmetricFixedCoordinates (b : Module.Basis ι L V) :
    SymmetricFixedField G L V b ≃ₐ[FixedField G L] FixedRationalField G L ι where
  __ := transportFixedEquiv G (rationalCoordinates L V b).toRingEquiv
  commutes' a := by
    apply Subtype.ext
    exact (rationalCoordinates L V b).commutes (a : L)

/-- The field conclusion of no-name for an invariant basis. The companion
`symmetricRationalAction_iota` verifies that this is the actual extension of
the given action whenever the basis vectors are fixed. -/
def fixedSymmetricFieldAlgEquiv [Finite G] (b : Module.Basis ι L V) :
    SymmetricFixedField G L V b ≃ₐ[FixedField G L]
      FractionRing (MvPolynomial ι (FixedField G L)) :=
  (symmetricFixedCoordinates G L V b).trans (fixedRationalAlgEquiv G L ι).symm

end SymmetricCoordinates

section NoName

variable (V : Type*) [AddCommGroup V] [Module L V] [DistribMulAction G V]
  [SMulDistribClass G L V] [Finite G] [FaithfulSMul G L] [FiniteDimensional L V]

/-- The actual invariant field of the symmetric-algebra fraction field,
with its action constructed from genuine finite semilinear descent. -/
abbrev NoNameFixedField :=
  SymmetricFixedField G L V (FiniteGaloisDescent.invariantBasis G L V)

/-- Finite-group no-name at field level: the actual invariant field is a
rational extension of rank `finrank L V` over the actual fixed subfield. -/
def finiteNoNameAlgEquiv : NoNameFixedField G L V ≃ₐ[FixedField G L]
    FractionRing (MvPolynomial (Fin (Module.finrank L V)) (FixedField G L)) :=
  fixedSymmetricFieldAlgEquiv G L V (FiniteGaloisDescent.invariantBasis G L V)

/-- The action used in `finiteNoNameAlgEquiv` is the original semilinear
action on the actual degree-one coordinate module. -/
theorem finiteNoName_action_iota (g : G) (v : V) :
    letI := symmetricRationalAction G L V (FiniteGaloisDescent.invariantBasis G L V)
    g • algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V v) =
      algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V (g • v)) :=
  symmetricRationalAction_iota G L V _ (FiniteGaloisDescent.invariantBasis_fixed G L V) g v

/-- One endpoint records both compatibility with the originally given
semilinear action and the proved rational invariant-field isomorphism. -/
theorem finite_no_name :
    (letI := symmetricRationalAction G L V (FiniteGaloisDescent.invariantBasis G L V)
      ∀ (g : G) (a : L), g • algebraMap L (CoordinateField L V) a =
        algebraMap L (CoordinateField L V) (g • a)) ∧
    (letI := symmetricRationalAction G L V (FiniteGaloisDescent.invariantBasis G L V)
      ∀ (g : G) (v : V),
        g • algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V v) =
          algebraMap (CoordinateRing L V) (CoordinateField L V) (SymmetricAlgebra.ι L V (g • v))) ∧
    Nonempty (NoNameFixedField G L V ≃ₐ[FixedField G L]
      FractionRing (MvPolynomial (Fin (Module.finrank L V)) (FixedField G L))) :=
  ⟨symmetricRationalAction_constant G L V _, finiteNoName_action_iota G L V,
    ⟨finiteNoNameAlgEquiv G L V⟩⟩

end NoName

end M9.FiniteNoNameField
