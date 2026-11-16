module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Removing a central sign from a two-component stabilizer

The input consists of literal group maps, a central sign, a square root of
that sign implementing an involution, parity, and four actual normal forms.
The quotient is constructed with `QuotientGroup`; its semidirect-product
description is proved by checking a canonical lift is bijective.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace M9.CentralSignQuotient

abbrev C2 := Multiplicative (ZMod 2)

/-- The nonidentity element of the actual cyclic group of order two. -/
def epsilon : C2 := Multiplicative.ofAdd 1

@[simp] theorem epsilon_ne_one : epsilon ≠ (1 : C2) := by decide +kernel
@[simp] theorem epsilon_mul_self : epsilon * epsilon = (1 : C2) := by decide +kernel
theorem c2_cases (c : C2) : c = 1 ∨ c = epsilon := by
  revert c
  decide +kernel

/-- Every involution in a group gives the genuine homomorphism out of `C₂`. -/
def involutionHom {T : Type*} [Group T] (a : T) (ha : a * a = 1) : C2 →* T where
  toFun c := if c = 1 then 1 else a
  map_one' := by simp
  map_mul' c d := by
    rcases c2_cases c with rfl | rfl <;> rcases c2_cases d with rfl | rfl <;>
      simp [ha]

@[simp] theorem involutionHom_one {T : Type*} [Group T] (a : T) (ha : a * a = 1) :
    involutionHom a ha 1 = 1 := by simp [involutionHom]

@[simp] theorem involutionHom_epsilon {T : Type*} [Group T] (a : T) (ha : a * a = 1) :
    involutionHom a ha epsilon = a := by simp [involutionHom]

/-- The exact hypotheses supplied by a genuine four-normal-form classification. -/
structure Data (G H : Type*) [Group G] [Group H] where
  iota : G →* H
  iota_injective : Function.Injective iota
  psi : MulAut G
  psi_sq : psi * psi = 1
  z : H
  s : H
  z_central : ∀ h : H, z * h = h * z
  z_sq : z * z = 1
  s_sq : s * s = z
  conjugation : ∀ g : G, s * iota g = iota (psi g) * s
  z_not_range : z ∉ Set.range iota
  parity : H →* C2
  parity_iota : ∀ g : G, parity (iota g) = 1
  parity_s : parity s = epsilon
  normalForms : ∀ h : H, ∃ g : G,
    h = iota g ∨ h = z * iota g ∨ h = s * iota g ∨ h = z * s * iota g

namespace Data

variable {G H : Type*} [Group G] [Group H] (D : Data G H)

theorem z_ne_one : D.z ≠ 1 := by
  intro hz
  exact D.z_not_range ⟨1, by simpa using hz.symm⟩

theorem z_orderOf : orderOf D.z = 2 := by
  apply orderOf_eq_prime_iff.mpr
  exact ⟨by simpa only [pow_two] using D.z_sq, D.z_ne_one⟩

theorem z_inv : D.z⁻¹ = D.z := by
  calc
    D.z⁻¹ = D.z⁻¹ * (D.z * D.z) := by rw [D.z_sq, mul_one]
    _ = D.z := inv_mul_cancel_left _ _

@[simp] theorem parity_z : D.parity D.z = 1 := by
  rw [← D.s_sq, map_mul, D.parity_s, epsilon_mul_self]

/-- The central sign subgroup is represented by its two literal elements. -/
def signSubgroup : Subgroup H where
  carrier := {h | h = 1 ∨ h = D.z}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [D.z_sq]
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl (inv_one)
    · exact Or.inr D.z_inv

@[simp] theorem mem_signSubgroup (h : H) : h ∈ D.signSubgroup ↔ h = 1 ∨ h = D.z := Iff.rfl

theorem signSubgroup_eq_zpowers : D.signSubgroup = Subgroup.zpowers D.z := by
  apply le_antisymm
  · rintro h (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (Or.inr rfl)

instance signSubgroup_normal : D.signSubgroup.Normal := by
  apply Subgroup.normal_of_le_center
  rintro h (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_center_iff.mpr (fun h => (D.z_central h).symm)

abbrev Quotient := H ⧸ D.signSubgroup

def quotientMap : H →* D.Quotient := QuotientGroup.mk' D.signSubgroup

@[simp] theorem quotientMap_z : D.quotientMap D.z = 1 :=
  (QuotientGroup.eq_one_iff D.z).mpr (Or.inr rfl)

theorem quotientMap_eq_one_iff (h : H) : D.quotientMap h = 1 ↔ h = 1 ∨ h = D.z :=
  QuotientGroup.eq_one_iff h

theorem quotientMap_kernel : D.quotientMap.ker = Subgroup.zpowers D.z := by
  rw [quotientMap, QuotientGroup.ker_mk', D.signSubgroup_eq_zpowers]

def psiAction : C2 →* MulAut G := involutionHom D.psi D.psi_sq

abbrev Target := G ⋊[D.psiAction] C2

def quotientIota : G →* D.Quotient := D.quotientMap.comp D.iota

theorem quotientIota_injective : Function.Injective D.quotientIota := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  rcases (D.quotientMap_eq_one_iff (D.iota g)).mp hg with hi | hz
  · apply D.iota_injective
    simpa using hi
  · exact (D.z_not_range ⟨g, hz⟩).elim

theorem quotient_s_square : D.quotientMap D.s * D.quotientMap D.s = 1 := by
  rw [← map_mul, D.s_sq, D.quotientMap_z]

def quotientSwap : C2 →* D.Quotient := involutionHom (D.quotientMap D.s) D.quotient_s_square

theorem quotient_compatibility (c : C2) :
    D.quotientIota.comp (D.psiAction c).toMonoidHom =
      (MulAut.conj (D.quotientSwap c)).toMonoidHom.comp D.quotientIota := by
  rcases c2_cases c with rfl | rfl
  · ext g
    simp [psiAction, quotientSwap]
  · ext g
    change D.quotientMap (D.iota (D.psi g)) =
      D.quotientMap D.s * D.quotientMap (D.iota g) * (D.quotientMap D.s)⁻¹
    apply (eq_mul_inv_iff_mul_eq).mpr
    simpa only [map_mul] using congrArg D.quotientMap (D.conjugation g).symm

/-- The semidirect-product universal property produces the canonical quotient homomorphism. -/
def semidirectToQuotient : D.Target →* D.Quotient :=
  SemidirectProduct.lift D.quotientIota D.quotientSwap D.quotient_compatibility

@[simp] theorem semidirectToQuotient_inl (g : G) :
    D.semidirectToQuotient (SemidirectProduct.inl g) = D.quotientMap (D.iota g) :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp] theorem semidirectToQuotient_inr_epsilon :
    D.semidirectToQuotient (SemidirectProduct.inr epsilon) = D.quotientMap D.s := by
  simp [semidirectToQuotient, quotientSwap]

theorem semidirectToQuotient_apply (g : G) (c : C2) :
    D.semidirectToQuotient ⟨g, c⟩ = D.quotientMap (D.iota g) * D.quotientSwap c := rfl

theorem semidirectToQuotient_surjective : Function.Surjective D.semidirectToQuotient := by
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D.signSubgroup x
  rcases D.normalForms h with ⟨g, rfl | rfl | rfl | rfl⟩
  · exact ⟨SemidirectProduct.inl g, D.semidirectToQuotient_inl g⟩
  · refine ⟨SemidirectProduct.inl g, ?_⟩
    change D.semidirectToQuotient (SemidirectProduct.inl g) =
      D.quotientMap (D.z * D.iota g)
    simp only [semidirectToQuotient_inl, map_mul, quotientMap_z, one_mul]
  · refine ⟨SemidirectProduct.inr epsilon * SemidirectProduct.inl g, ?_⟩
    change D.semidirectToQuotient
      (SemidirectProduct.inr epsilon * SemidirectProduct.inl g) = D.quotientMap (D.s * D.iota g)
    simp only [map_mul, semidirectToQuotient_inr_epsilon, semidirectToQuotient_inl]
  · refine ⟨SemidirectProduct.inr epsilon * SemidirectProduct.inl g, ?_⟩
    change D.semidirectToQuotient
      (SemidirectProduct.inr epsilon * SemidirectProduct.inl g) = D.quotientMap (D.z * D.s * D.iota g)
    simp only [map_mul, semidirectToQuotient_inr_epsilon, semidirectToQuotient_inl,
      quotientMap_z, one_mul]

theorem semidirectToQuotient_injective : Function.Injective D.semidirectToQuotient := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨g, c⟩ hx
  rcases c2_cases c with rfl | rfl
  · have hq : D.quotientIota g = 1 := by
      simpa only [semidirectToQuotient_apply, quotientSwap, involutionHom_one, mul_one,
        quotientIota, MonoidHom.comp_apply] using hx
    have hg : g = 1 := by
      apply D.quotientIota_injective
      simpa using hq
    subst g
    rfl
  · have hs : D.quotientMap (D.iota g * D.s) = 1 := by
      simpa only [semidirectToQuotient_apply, quotientSwap, involutionHom_epsilon, map_mul] using hx
    have hpar : D.parity (D.iota g * D.s) = 1 := by
      rcases (D.quotientMap_eq_one_iff _).mp hs with he | he
      · rw [he, map_one]
      · rw [he, parity_z]
    have hbad : epsilon = 1 := by
      simpa only [map_mul, D.parity_iota, D.parity_s, one_mul] using hpar
    exact (epsilon_ne_one hbad).elim

/-- The canonical map is an isomorphism by the actual classification and disjointness proofs. -/
def semidirectQuotientEquiv : D.Target ≃* D.Quotient :=
  MulEquiv.ofBijective D.semidirectToQuotient
    ⟨D.semidirectToQuotient_injective, D.semidirectToQuotient_surjective⟩

/-- The central-sign quotient is the genuine semidirect product by the given involution. -/
def quotientEquiv : D.Quotient ≃* D.Target := D.semidirectQuotientEquiv.symm

@[simp] theorem semidirectQuotientEquiv_apply (x : D.Target) :
    D.semidirectQuotientEquiv x = D.semidirectToQuotient x := rfl

@[simp] theorem quotientEquiv_iota (g : G) :
    D.quotientEquiv (D.quotientMap (D.iota g)) = SemidirectProduct.inl g := by
  apply D.semidirectQuotientEquiv.injective
  simp [quotientEquiv]

@[simp] theorem quotientEquiv_s :
    D.quotientEquiv (D.quotientMap D.s) = SemidirectProduct.inr epsilon := by
  apply D.semidirectQuotientEquiv.injective
  simp [quotientEquiv]

/-- The explicit homomorphism from the original group has exactly the central sign as kernel. -/
def toSemidirect : H →* D.Target := D.quotientEquiv.toMonoidHom.comp D.quotientMap

theorem toSemidirect_kernel : D.toSemidirect.ker = Subgroup.zpowers D.z := by
  ext h
  change D.quotientEquiv (D.quotientMap h) = 1 ↔ h ∈ Subgroup.zpowers D.z
  rw [← map_one D.quotientEquiv, D.quotientEquiv.injective.eq_iff,
    ← D.signSubgroup_eq_zpowers]
  exact D.quotientMap_eq_one_iff h

@[simp] theorem toSemidirect_iota (g : G) :
    D.toSemidirect (D.iota g) = SemidirectProduct.inl g := D.quotientEquiv_iota g

@[simp] theorem toSemidirect_s : D.toSemidirect D.s = SemidirectProduct.inr epsilon :=
  D.quotientEquiv_s

@[simp] theorem toSemidirect_z : D.toSemidirect D.z = 1 := by
  change D.quotientEquiv (D.quotientMap D.z) = 1
  rw [D.quotientMap_z, map_one]

/-- The given actual parity agrees with the semidirect-product projection. -/
theorem toSemidirect_parity :
    SemidirectProduct.rightHom.comp D.toSemidirect = D.parity := by
  ext h
  rcases D.normalForms h with ⟨g, rfl | rfl | rfl | rfl⟩ <;>
    simp [MonoidHom.comp_apply, map_mul, D.parity_iota, D.parity_s]

/-- Parity is even precisely on the two literal connected-sign normal forms. -/
theorem parity_eq_one_iff (h : H) :
    D.parity h = 1 ↔ ∃ g : G, h = D.iota g ∨ h = D.z * D.iota g := by
  constructor
  · intro heven
    rcases D.normalForms h with ⟨g, hi | hi | hi | hi⟩
    · exact ⟨g, Or.inl hi⟩
    · exact ⟨g, Or.inr hi⟩
    · have hbad : epsilon = 1 := by
        simpa only [hi, map_mul, D.parity_s, D.parity_iota, mul_one] using heven
      exact (epsilon_ne_one hbad).elim
    · have hbad : epsilon = 1 := by
        simpa only [hi, map_mul, parity_z, D.parity_s, D.parity_iota, one_mul, mul_one] using heven
      exact (epsilon_ne_one hbad).elim
  · rintro ⟨g, rfl | rfl⟩ <;> simp [D.parity_iota]

theorem iota_ne_z_mul_iota (g h : G) : D.iota g ≠ D.z * D.iota h := by
  intro heq
  apply D.z_not_range
  refine ⟨g * h⁻¹, ?_⟩
  rw [map_mul, map_inv, heq, mul_assoc, mul_inv_cancel, mul_one]

theorem s_mul_iota_ne_iota (g h : G) : D.s * D.iota g ≠ D.iota h := by
  intro heq
  apply epsilon_ne_one
  simpa only [map_mul, D.parity_s, D.parity_iota, mul_one] using congrArg D.parity heq

instance zpowers_normal : (Subgroup.zpowers D.z).Normal := by
  rw [← D.signSubgroup_eq_zpowers]
  infer_instance

/-- The same isomorphism with the conventional cyclic-subgroup quotient written explicitly. -/
def centralQuotientEquiv : (H ⧸ Subgroup.zpowers D.z) ≃* D.Target :=
  (QuotientGroup.quotientMulEquivOfEq D.signSubgroup_eq_zpowers.symm).trans D.quotientEquiv

@[simp] theorem centralQuotientEquiv_mk (h : H) :
    D.centralQuotientEquiv (QuotientGroup.mk' (Subgroup.zpowers D.z) h) = D.toSemidirect h := by
  change D.quotientEquiv
    (QuotientGroup.quotientMulEquivOfEq D.signSubgroup_eq_zpowers.symm
      (QuotientGroup.mk h)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

@[simp] theorem centralQuotientEquiv_iota (g : G) :
    D.centralQuotientEquiv (QuotientGroup.mk' (Subgroup.zpowers D.z) (D.iota g)) =
      SemidirectProduct.inl g := by
  rw [centralQuotientEquiv_mk, toSemidirect_iota]

@[simp] theorem centralQuotientEquiv_s :
    D.centralQuotientEquiv (QuotientGroup.mk' (Subgroup.zpowers D.z) D.s) =
      SemidirectProduct.inr epsilon := by
  rw [centralQuotientEquiv_mk, toSemidirect_s]

end Data

end M9.CentralSignQuotient
