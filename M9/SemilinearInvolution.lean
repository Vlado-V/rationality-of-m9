module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic

/-! The algebraic quadratic descent used in Section 5 of the pinned M9 paper.
The fixed base is the actual equalizer subfield of the automorphism. No
identification of an externally supplied base field with this subfield is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.SemilinearInvolution

variable {L : Type*} [Field L]

/-- The actual subfield of elements fixed by the given field automorphism. -/
def fixedField (σ : L ≃+* L) : Subfield L :=
  σ.toRingHom.eqLocusField (RingHom.id L)

@[simp] theorem mem_fixedField (σ : L ≃+* L) (x : L) :
    x ∈ fixedField σ ↔ σ x = x := Iff.rfl

@[simp] theorem apply_fixed (σ : L ≃+* L) (a : fixedField σ) : σ (a : L) = a := a.property

/-- The antisymmetric difference used in the manuscript. -/
def theta (σ : L ≃+* L) (b : L) : L := b-σ b

theorem theta_ne_zero (σ : L ≃+* L) {b : L} (hb : σ b ≠ b) : theta σ b ≠ 0 := by
  exact sub_ne_zero.mpr hb.symm

theorem theta_anti (σ : L ≃+* L) (hσ : Function.Involutive σ) (b : L) :
    σ (theta σ b) = -theta σ b := by
  simp only [theta, map_sub, hσ b]
  ring

theorem exists_theta (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl L) :
    ∃ b : L, theta σ b ≠ 0 ∧ σ (theta σ b) = -theta σ b := by
  have hmoved : ∃ b, σ b ≠ b := by
    by_contra h
    push Not at h
    exact hne (RingEquiv.ext h)
  obtain ⟨b,hb⟩ := hmoved
  exact ⟨b,theta_ne_zero σ hb,theta_anti σ hσ b⟩

theorem anti_div_fixed (σ : L ≃+* L) {θ x : L}
    (hθ : σ θ = -θ) (hx : σ x = -x) : x/θ ∈ fixedField σ := by
  change σ (x/θ) = x/θ
  rw [map_div₀, hx, hθ, neg_div_neg_eq]

/-- Every anti-invariant is a unique fixed scalar multiple of a nonzero
anti-invariant generator. -/
theorem anti_iff_fixed_mul (σ : L ≃+* L) {θ : L} (hθ0 : θ ≠ 0)
    (hθ : σ θ = -θ) (x : L) :
    σ x = -x ↔ ∃ a : fixedField σ, x = (a : L)*θ := by
  constructor
  · intro hx
    exact ⟨⟨x/θ,anti_div_fixed σ hθ hx⟩,(div_mul_cancel₀ x hθ0).symm⟩
  · rintro ⟨a,rfl⟩
    rw [map_mul, apply_fixed, hθ]
    ring

theorem fixed_mul_anti_unique (σ : L ≃+* L) {θ : L} (hθ0 : θ ≠ 0)
    {a b : fixedField σ} (h : (a : L)*θ=(b : L)*θ) : a=b := by
  apply Subtype.ext
  exact mul_right_cancel₀ hθ0 h

theorem fixed_part_mem (σ : L ≃+* L) (hσ : Function.Involutive σ) (x : L) :
    (x+σ x)/2 ∈ fixedField σ := by
  change σ ((x+σ x)/2) = (x+σ x)/2
  simp only [map_div₀, map_add, map_ofNat, hσ x]
  ring

theorem anti_part (σ : L ≃+* L) (hσ : Function.Involutive σ) (x : L) :
    σ ((x-σ x)/2) = -((x-σ x)/2) := by
  simp only [map_div₀, map_sub, map_ofNat, hσ x]
  ring

/-- The explicit fixed and anti-invariant decomposition, with characteristic
different from two stated as its exact required scalar condition. -/
theorem decomposition (σ : L ≃+* L) (htwo : (2 : L) ≠ 0) (x : L) :
    x=(x+σ x)/2+(x-σ x)/2 := by
  field_simp
  ring

theorem exists_fixed_coordinates (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (htwo : (2 : L) ≠ 0) {θ : L} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ) (x : L) :
    ∃ a b : fixedField σ, x=(a : L)+(b : L)*θ := by
  let a : fixedField σ := ⟨(x+σ x)/2,fixed_part_mem σ hσ x⟩
  let b : fixedField σ := ⟨((x-σ x)/2)/θ,anti_div_fixed σ hθ (anti_part σ hσ x)⟩
  refine ⟨a,b,?_⟩
  change x=(x+σ x)/2+(((x-σ x)/2)/θ)*θ
  rw [div_mul_cancel₀ _ hθ0]
  exact decomposition σ htwo x

/-- The two-coordinate linear map uses the actual fixed subfield's scalar
action on the ambient field. -/
def coordinateMap (σ : L ≃+* L) (θ : L) :
    (fixedField σ × fixedField σ) →ₗ[fixedField σ] L where
  toFun a := (a.1 : L)+(a.2 : L)*θ
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, Subfield.coe_add]; ring
  map_smul' a b := by
    change (a : L)*(b.1 : L)+((a : L)*(b.2 : L))*θ =
      (a : L)*((b.1 : L)+(b.2 : L)*θ)
    ring

theorem coordinateMap_injective (σ : L ≃+* L) (htwo : (2 : L) ≠ 0)
    {θ : L} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ) :
    Function.Injective (coordinateMap σ θ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨a,b⟩ h
  change (a : L)+(b : L)*θ=0 at h
  have hs : (a : L)-(b : L)*θ=0 := by
    simpa only [map_add, map_mul, apply_fixed, hθ, mul_neg, ← sub_eq_add_neg, map_zero]
      using congrArg σ h
  have ha : (a : L)=0 := by
    have hsum : (2 : L)*(a : L)=0 := by linear_combination h+hs
    exact (mul_eq_zero.mp hsum).resolve_left htwo
  have hb : (b : L)=0 := by
    have hprod : (b : L)*θ=0 := by simpa only [ha, zero_add] using h
    exact (mul_eq_zero.mp hprod).resolve_right hθ0
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

/-- Explicit quadratic descent: every ambient element has exactly two
coordinates over the actual fixed subfield. -/
def coordinateEquiv (σ : L ≃+* L) (hσ : Function.Involutive σ) (htwo : (2 : L) ≠ 0)
    {θ : L} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ) :
    (fixedField σ × fixedField σ) ≃ₗ[fixedField σ] L :=
  LinearEquiv.ofBijective (coordinateMap σ θ)
    ⟨coordinateMap_injective σ htwo hθ0 hθ,fun x => by
      obtain ⟨a,b,h⟩ := exists_fixed_coordinates σ hσ htwo hθ0 hθ x
      exact ⟨(a,b),h.symm⟩⟩

theorem finrank_fixedField (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (htwo : (2 : L) ≠ 0) (hne : σ ≠ RingEquiv.refl L) :
    Module.finrank (fixedField σ) L=2 := by
  obtain ⟨b,hθ0,hθ⟩ := exists_theta σ hσ hne
  rw [← (coordinateEquiv σ hσ htwo hθ0 hθ).finrank_eq]
  simp

/-- A proposed fixed base is the full fixed field once every ambient element
has two coordinates over it. This criterion does not presume the desired
fixed-field equality. -/
theorem fixedField_eq_of_coordinates (σ : L ≃+* L) (htwo : (2 : L) ≠ 0)
    (E : Subfield L) (hE : E ≤ fixedField σ) {θ : L} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ)
    (hcoordinates : ∀ x : L, ∃ a b : E, x=(a : L)+(b : L)*θ) : fixedField σ=E := by
  apply le_antisymm ?_ hE
  intro x hx
  obtain ⟨a,b,hxcoord⟩ := hcoordinates x
  have hσa : σ (a : L)=a := hE a.property
  have hσb : σ (b : L)=b := hE b.property
  have hanti : (a : L)-(b : L)*θ=(a : L)+(b : L)*θ := by
    calc
      (a : L)-(b : L)*θ=σ ((a : L)+(b : L)*θ) := by
        rw [map_add, map_mul, hσa, hσb, hθ]
        ring
      _ = σ x := congrArg σ hxcoord.symm
      _ = x := hx
      _ = (a : L)+(b : L)*θ := hxcoord
  have hprod : (2 : L)*((b : L)*θ)=0 := by linear_combination -hanti
  have hb : (b : L)=0 := ((mul_eq_zero.mp hprod).resolve_left htwo |> mul_eq_zero.mp).resolve_right hθ0
  rw [hxcoord, hb, zero_mul, add_zero]
  exact a.property

/-- If the generator's square lies in a fixed base, adjoining that generator
introduces only its two elementary coordinates. Inversion uses the actual
conjugate norm, so no finite-degree or fixed-field conclusion is an input. -/
theorem coordinates_of_mem_adjoin (σ : L ≃+* L) (E : Subfield L)
    (hE : E ≤ fixedField σ) {θ : L} (hθ : σ θ = -θ) (hsquare : θ^2 ∈ E)
    {x : L} (hx : x ∈ IntermediateField.adjoin E ({θ} : Set L)) :
    ∃ a b : E, x=(a : L)+(b : L)*θ := by
  let t : E := ⟨θ^2,hsquare⟩
  refine IntermediateField.adjoin_induction (F := E)
    (motive := fun x _ => ∃ a b : E, x=(a : L)+(b : L)*θ) ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨0,1,by simp⟩
  · intro a
    refine ⟨a,0,?_⟩
    change (a : L)=(a : L)+(0 : L)*θ
    simp
  · rintro x y _ _ ⟨a,b,hx⟩ ⟨c,d,hy⟩
    refine ⟨a+c,b+d,?_⟩
    simp only [Subfield.coe_add]
    rw [hx,hy]
    ring
  · rintro x _ ⟨a,b,hx⟩
    by_cases hx0 : x=0
    · exact ⟨0,0,by simp [hx0]⟩
    have hσa : σ (a : L)=a := hE a.property
    have hσb : σ (b : L)=b := hE b.property
    have hσx : σ x=(a : L)-(b : L)*θ := by
      rw [hx,map_add,map_mul,hσa,hσb,hθ]
      ring
    let n : E := a*a-b*b*t
    have hnorm : (n : L)=x*σ x := by
      simp only [n,Subfield.coe_sub,Subfield.coe_mul]
      change (a : L)*(a : L)-(b : L)*(b : L)*θ^2=x*σ x
      rw [hσx,hx]
      ring
    have hσx0 : σ x ≠ 0 := by simpa only [map_zero] using σ.injective.ne hx0
    have hn0 : (n : L) ≠ 0 := by rw [hnorm]; exact mul_ne_zero hx0 hσx0
    refine ⟨a/n,-b/n,?_⟩
    simp only [Subfield.coe_div,Subfield.coe_neg]
    calc
      x⁻¹=σ x/(n : L) := by
        rw [hnorm]
        field_simp
      _ = (a : L)/(n : L)+(-(b : L)/(n : L))*θ := by
        rw [hσx]
        ring
  · rintro x y _ _ ⟨a,b,hx⟩ ⟨c,d,hy⟩
    refine ⟨a*c+b*d*t,a*d+b*c,?_⟩
    simp only [Subfield.coe_add,Subfield.coe_mul]
    change x*y=(a : L)*(c : L)+(b : L)*(d : L)*θ^2+
      ((a : L)*(d : L)+(b : L)*(c : L))*θ
    rw [hx,hy]
    ring

/-- A fixed base whose quadratic generator generates the ambient field is
exactly the full fixed field. The square-membership hypothesis is essential. -/
theorem fixedField_eq_of_adjoin (σ : L ≃+* L) (htwo : (2 : L) ≠ 0)
    (E : Subfield L) (hE : E ≤ fixedField σ) {θ : L} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ)
    (hsquare : θ^2 ∈ E) (hgen : IntermediateField.adjoin E ({θ} : Set L)=⊤) :
    fixedField σ=E := by
  apply fixedField_eq_of_coordinates σ htwo E hE hθ0 hθ
  intro x
  apply coordinates_of_mem_adjoin σ E hE hθ hsquare
  rw [hgen]
  trivial

/-- A multivariate rational function field, realized by its actual fraction ring. -/
abbrev Rational (ι : Type*) (L : Type*) [Field L] := FractionRing (MvPolynomial ι L)

variable (ι : Type*)

/-- Extend the base automorphism coefficientwise, fixing all rational variables. -/
def rationalInvolution (σ : L ≃+* L) : Rational ι L ≃+* Rational ι L :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.mapEquiv ι σ)

@[simp] theorem rationalInvolution_polynomial (σ : L ≃+* L) (p : MvPolynomial ι L) :
    rationalInvolution ι σ (algebraMap (MvPolynomial ι L) (Rational ι L) p)=
      algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.map σ p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

@[simp] theorem rationalInvolution_constant (σ : L ≃+* L) (a : L) :
    rationalInvolution ι σ (algebraMap L (Rational ι L) a)=
      algebraMap L (Rational ι L) (σ a) := by
  change rationalInvolution ι σ (algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.C a))=
    algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.C (σ a))
  rw [rationalInvolution_polynomial,MvPolynomial.map_C]
  rfl

@[simp] theorem rationalInvolution_variable (σ : L ≃+* L) (i : ι) :
    rationalInvolution ι σ
      (algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.X i))=
      algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.X i) := by
  rw [rationalInvolution_polynomial,MvPolynomial.map_X]

theorem polynomialInvolution_involutive (σ : L ≃+* L) (hσ : Function.Involutive σ) :
    Function.Involutive (MvPolynomial.map σ : MvPolynomial ι L → MvPolynomial ι L) := by
  intro p
  ext α
  simp only [MvPolynomial.coeff_map]
  exact hσ (p.coeff α)

theorem rationalInvolution_involutive (σ : L ≃+* L) (hσ : Function.Involutive σ) :
    Function.Involutive (rationalInvolution ι σ) := by
  intro f
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι L) f
  simp only [map_div₀, rationalInvolution_polynomial,
    polynomialInvolution_involutive ι σ hσ p, polynomialInvolution_involutive ι σ hσ q]

/-- Include polynomials whose coefficients lie in the actual fixed base. -/
def polynomialInclude (σ : L ≃+* L) :
    MvPolynomial ι (fixedField σ) →+* MvPolynomial ι L :=
  MvPolynomial.map (fixedField σ).subtype

theorem polynomialInclude_injective (σ : L ≃+* L) :
    Function.Injective (polynomialInclude ι σ) :=
  MvPolynomial.map_injective _ Subtype.val_injective

theorem polynomialInclude_fixed (σ : L ≃+* L) (p : MvPolynomial ι (fixedField σ)) :
    MvPolynomial.map σ (polynomialInclude ι σ p)=polynomialInclude ι σ p := by
  ext α
  simp only [polynomialInclude, MvPolynomial.coeff_map]
  exact (p.coeff α).property

theorem fixed_polynomial_descends (σ : L ≃+* L) (p : MvPolynomial ι L)
    (hp : MvPolynomial.map σ p=p) :
    ∃ q : MvPolynomial ι (fixedField σ), polynomialInclude ι σ q=p := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨α,_,rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  refine ⟨⟨p.coeff α,?_⟩,rfl⟩
  change σ (p.coeff α)=p.coeff α
  exact (MvPolynomial.coeff_map σ p α).symm.trans
    (congrArg (fun q : MvPolynomial ι L => q.coeff α) hp)

/-- The genuine inclusion of rational functions over the actual fixed base. -/
def rationalInclude (σ : L ≃+* L) : Rational ι (fixedField σ) →+* Rational ι L :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial ι L) (Rational ι L)).comp
    (polynomialInclude ι σ)) (by
      intro p q hpq
      apply polynomialInclude_injective ι σ
      exact (IsFractionRing.injective (MvPolynomial ι L) (Rational ι L)) hpq)

@[simp] theorem rationalInclude_polynomial (σ : L ≃+* L) (p : MvPolynomial ι (fixedField σ)) :
    rationalInclude ι σ (algebraMap (MvPolynomial ι (fixedField σ)) (Rational ι (fixedField σ)) p)=
      algebraMap (MvPolynomial ι L) (Rational ι L) (polynomialInclude ι σ p) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] theorem rationalInclude_constant (σ : L ≃+* L) (a : fixedField σ) :
    rationalInclude ι σ (algebraMap (fixedField σ) (Rational ι (fixedField σ)) a)=
      algebraMap L (Rational ι L) (a : L) := by
  change rationalInclude ι σ
    (algebraMap (MvPolynomial ι (fixedField σ)) (Rational ι (fixedField σ)) (MvPolynomial.C a))=
      algebraMap (MvPolynomial ι L) (Rational ι L) (MvPolynomial.C (a : L))
  rw [rationalInclude_polynomial]
  simp only [polynomialInclude,MvPolynomial.map_C]
  rfl

theorem rationalInclude_fixed (σ : L ≃+* L) (f : Rational ι (fixedField σ)) :
    rationalInvolution ι σ (rationalInclude ι σ f)=rationalInclude ι σ f := by
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι (fixedField σ)) f
  simp only [map_div₀, rationalInclude_polynomial, rationalInvolution_polynomial,
    polynomialInclude_fixed]

/-- An invariant rational function descends by multiplying its denominator by
its conjugate. Both resulting polynomials have coefficients in the actual
fixed base. In particular this conclusion is proved, not assumed. -/
theorem fixed_rational_iff_descends (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (f : Rational ι L) :
    rationalInvolution ι σ f=f ↔
      ∃ g : Rational ι (fixedField σ), rationalInclude ι σ g=f := by
  constructor
  · intro hf
    obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι L) f
    let j := algebraMap (MvPolynomial ι L) (Rational ι L)
    have hj : Function.Injective j := IsFractionRing.injective _ _
    have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
    have hq' : j q ≠ 0 := fun hz => hq0 (hj (hz.trans (map_zero j).symm))
    have hσq : j (MvPolynomial.map σ q) ≠ 0 := by
      rw [← rationalInvolution_polynomial]
      simpa only [map_zero] using (rationalInvolution ι σ).injective.ne hq'
    have hcross : MvPolynomial.map σ p*q=p*MvPolynomial.map σ q := by
      apply hj
      rw [map_mul, map_mul]
      apply (div_eq_div_iff hσq hq').mp
      simpa only [map_div₀, rationalInvolution_polynomial] using hf
    have hn : MvPolynomial.map σ (p*MvPolynomial.map σ q)=p*MvPolynomial.map σ q := by
      rw [map_mul, polynomialInvolution_involutive ι σ hσ q]
      exact hcross
    have hd : MvPolynomial.map σ (q*MvPolynomial.map σ q)=q*MvPolynomial.map σ q := by
      rw [map_mul, polynomialInvolution_involutive ι σ hσ q, mul_comm]
    obtain ⟨n,hn⟩ := fixed_polynomial_descends ι σ _ hn
    obtain ⟨d,hd⟩ := fixed_polynomial_descends ι σ _ hd
    refine ⟨algebraMap _ (Rational ι (fixedField σ)) n /
      algebraMap _ (Rational ι (fixedField σ)) d,?_⟩
    rw [map_div₀, rationalInclude_polynomial, rationalInclude_polynomial, hn, hd,
      map_mul, map_mul]
    exact mul_div_mul_right _ _ hσq
  · rintro ⟨g,rfl⟩
    exact rationalInclude_fixed ι σ g

/-- The image of rational functions over the actual fixed base equals the
actual invariant subfield of the rational function field. -/
theorem rationalInclude_fieldRange (σ : L ≃+* L) (hσ : Function.Involutive σ) :
    (rationalInclude ι σ).fieldRange=fixedField (rationalInvolution ι σ) := by
  ext f
  exact (fixed_rational_iff_descends ι σ hσ f).symm

/-- Rationality of the actual invariant field when the independent rational
variables are fixed and only the coefficient field is acted on. -/
def fixedRationalEquiv (σ : L ≃+* L) (hσ : Function.Involutive σ) :
    Rational ι (fixedField σ) ≃+* fixedField (rationalInvolution ι σ) :=
  (rationalInclude ι σ).rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr (rationalInclude_fieldRange ι σ hσ))

/-- The fixed base embeds in the invariant field as actual constant rational
functions. This specifies the base algebra structure for the descent isomorphism. -/
def fixedBaseEmbedding (σ : L ≃+* L) : fixedField σ →+* fixedField (rationalInvolution ι σ) where
  toFun a := ⟨algebraMap L (Rational ι L) (a : L),by
    change rationalInvolution ι σ (algebraMap L (Rational ι L) (a : L))=_
    rw [rationalInvolution_constant,apply_fixed]
    rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance fixedRationalAlgebra (σ : L ≃+* L) :
    Algebra (fixedField σ) (fixedField (rationalInvolution ι σ)) :=
  (fixedBaseEmbedding ι σ).toAlgebra

/-- The invariant rational function field is a rational extension of its
actual fixed coefficient field, compatibly with the constant-field embeddings. -/
def fixedRationalAlgEquiv (σ : L ≃+* L) (hσ : Function.Involutive σ) :
    Rational ι (fixedField σ) ≃ₐ[fixedField σ] fixedField (rationalInvolution ι σ) where
  __ := fixedRationalEquiv ι σ hσ
  commutes' a := by
    apply Subtype.ext
    change rationalInclude ι σ (algebraMap (fixedField σ) (Rational ι (fixedField σ)) a)=
      algebraMap L (Rational ι L) (a : L)
    exact rationalInclude_constant ι σ a

theorem algebraMap_mem_fixedField {K : Type*} [Field K] [Algebra K L]
    (σ : L ≃ₐ[K] L) (a : K) : algebraMap K L a ∈ fixedField σ.toRingEquiv :=
  σ.commutes a

end M9.SemilinearInvolution
