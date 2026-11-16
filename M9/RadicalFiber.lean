module

public import M9.PrimitiveRepresentation
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public meta import Lean.Elab.Tactic.Omega

/-!
# The linear radical fiber and symplectic reduction

All spaces and forms in this module are actual submodules and quotients.
The equivalences are linear-algebra fiber correspondences. They do not assert
that the radical construction is an algebraic morphism or is dominant.
-/

@[expose] public section
noncomputable section
namespace M9.RadicalFiber
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The ambient radical of the form restricted to a genuine subspace. -/
def radical (B : LinearMap.BilinForm K V) (U : Submodule K V) : Submodule K V :=
  U ⊓ B.orthogonal U

theorem mem_radical_iff (B : LinearMap.BilinForm K V) (hB : B.IsRefl) (U : Submodule K V) (x : V) :
    x ∈ radical B U ↔ x ∈ U ∧ ∀ y ∈ U, B x y = 0 := by
  constructor
  · rintro ⟨hx,ho⟩
    exact ⟨hx,fun y hy => hB y x (ho y hy)⟩
  · rintro ⟨hx,ho⟩
    exact ⟨hx,fun y hy => hB x y (ho y hy)⟩

theorem radical_eq_bot_iff (B : LinearMap.BilinForm K V) (hB : B.IsRefl) (U : Submodule K V) :
    radical B U = ⊥ ↔ (B.restrict U).Nondegenerate := by
  have hBU : (B.restrict U).IsRefl := fun x y => hB x.val y.val
  change radical B U = ⊥ ↔ LinearMap.Nondegenerate (B.restrict U)
  rw [hBU.nondegenerate_iff_separatingLeft]
  constructor
  · intro hr x hx
    apply Subtype.ext
    have hxrad : x.val ∈ radical B U :=
      (mem_radical_iff B hB U x.val).mpr ⟨x.property,fun y hy => hx ⟨y,hy⟩⟩
    simpa only [hr, Submodule.mem_bot, ZeroMemClass.coe_zero] using hxrad
  · intro hnd
    apply le_antisymm _ bot_le
    intro x hx
    rcases (mem_radical_iff B hB U x).mp hx with ⟨hU,hx⟩
    exact congrArg Subtype.val (hnd ⟨x,hU⟩ (fun y => hx y.val y.property))

/-- Descent of a reflexive bilinear form by a subspace of its actual kernel. -/
def quotientForm (B : LinearMap.BilinForm K V) (hB : B.IsRefl) (N : Submodule K V)
    (hN : N ≤ LinearMap.ker B) : LinearMap.BilinForm K (V ⧸ N) :=
  LinearMap.IsRefl.liftQ₂ B N hB hN

@[simp] theorem quotientForm_mk (B : LinearMap.BilinForm K V) (hB : B.IsRefl) (N : Submodule K V)
    (hN : N ≤ LinearMap.ker B) (x y : V) :
    quotientForm B hB N hN (N.mkQ x) (N.mkQ y) = B x y := rfl

theorem quotientForm_isAlt (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (N : Submodule K V)
    (hN : N ≤ LinearMap.ker B) : (quotientForm B hB.isRefl N hN).IsAlt := by
  intro x
  refine Submodule.Quotient.induction_on N x ?_
  intro x
  exact hB x

/-- The kernel quotient has a genuinely nondegenerate descended form. -/
theorem quotientForm_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (N : Submodule K V)
    (hN : N = LinearMap.ker B) :
    (quotientForm B hB.isRefl N hN.le).Nondegenerate := by
  apply (quotientForm_isAlt B hB N hN.le).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x
  refine Submodule.Quotient.induction_on N x ?_
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero N).mpr
  rw [hN]
  apply LinearMap.ext
  intro y
  exact hx (N.mkQ y)

/-- Nondegeneracy of an actual quotient subspace is equivalent to its original
radical being precisely the subspace being divided out. -/
theorem quotient_restrict_nondegenerate_iff (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (N : Submodule K V) (hN : N ≤ LinearMap.ker B) (U : Submodule K V) (hNU : N ≤ U) :
    ((quotientForm B hB.isRefl N hN).restrict (U.map N.mkQ)).Nondegenerate ↔
      radical B U = N := by
  have hQN := quotientForm_isAlt B hB N hN
  have hQU : ((quotientForm B hB.isRefl N hN).restrict (U.map N.mkQ)).IsRefl :=
    fun x y => hQN.isRefl x.val y.val
  constructor
  · intro hnd
    apply le_antisymm
    · intro x hx
      rcases (mem_radical_iff B hB.isRefl U x).mp hx with ⟨hxU,horth⟩
      have hq : (⟨N.mkQ x, ⟨x,hxU,rfl⟩⟩ : U.map N.mkQ) = 0 := by
        apply hnd.1
        rintro ⟨y,hy⟩
        rcases hy with ⟨y,hy,rfl⟩
        exact horth y hy
      exact (Submodule.Quotient.mk_eq_zero N).mp (congrArg Subtype.val hq)
    · intro x hx
      apply (mem_radical_iff B hB.isRefl U x).mpr
      refine ⟨hNU hx,fun y _ => ?_⟩
      exact LinearMap.congr_fun (hN hx) y
  · intro hr
    apply hQU.nondegenerate_iff_separatingLeft.mpr
    rintro ⟨x,hx⟩ horth
    rcases hx with ⟨x,hx,rfl⟩
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    rw [← hr]
    apply (mem_radical_iff B hB.isRefl U x).mpr
    exact ⟨hx,fun y hy => horth ⟨N.mkQ y,⟨y,hy,rfl⟩⟩⟩

/-- Radicals commute with the actual inclusion of a subspace. -/
theorem radical_map_subtype (B : LinearMap.BilinForm K V) (hB : B.IsRefl)
    (W : Submodule K V) (U : Submodule K W) :
    (radical (B.restrict W) U).map W.subtype = radical B (U.map W.subtype) := by
  have hBW : (B.restrict W).IsRefl := fun x y => hB x.val y.val
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    rcases (mem_radical_iff (B.restrict W) hBW U x).mp hx with ⟨hxU,hxorth⟩
    apply (mem_radical_iff B hB (U.map W.subtype) x.val).mpr
    refine ⟨⟨x,hxU,rfl⟩,?_⟩
    rintro y ⟨y,hy,rfl⟩
    exact hxorth y hy
  · intro hx
    rcases (mem_radical_iff B hB (U.map W.subtype) x).mp hx with ⟨hxU,hxorth⟩
    rcases hxU with ⟨x,hxmem,rfl⟩
    refine ⟨x,?_,rfl⟩
    apply (mem_radical_iff (B.restrict W) hBW U x).mpr
    exact ⟨hxmem,fun y hy => hxorth y.val ⟨y,hy,rfl⟩⟩

section Finite
variable [FiniteDimensional K V]

/-- Exact dimension formula for the actual image under a quotient projection. -/
theorem finrank_quotient_image (N U : Submodule K V) (hNU : N ≤ U) :
    finrank K (U.map N.mkQ) + finrank K N = finrank K U := by
  have hk : LinearMap.ker (N.mkQ.domRestrict U) = N.comap U.subtype := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hn : finrank K (N.comap U.subtype) = finrank K N :=
    (Submodule.comapSubtypeEquivOfLe hNU).finrank_eq
  have h := (N.mkQ.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hk, hn] at h
  exact h

/-- The actual perpendicular space to the subspace being reduced. -/
abbrev Perp (B : LinearMap.BilinForm K V) (L : Submodule K V) := B.orthogonal L

/-- The submodule divided out inside the perpendicular space. -/
def Inside (B : LinearMap.BilinForm K V) (L : Submodule K V) : Submodule K (Perp B L) :=
  L.comap (Perp B L).subtype

/-- Symplectic reduction as an actual quotient of actual submodules. -/
abbrev Reduced (B : LinearMap.BilinForm K V) (L : Submodule K V) :=
  Perp B L ⧸ Inside B L

theorem inside_le_kernel (B : LinearMap.BilinForm K V) (L : Submodule K V) :
    Inside B L ≤ LinearMap.ker (B.restrict (Perp B L)) := by
  intro x hx
  apply LinearMap.ext
  intro y
  exact y.property x.val hx

/-- The actual descended alternating form on the symplectic quotient. -/
def reducedForm (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (L : Submodule K V) :
    LinearMap.BilinForm K (Reduced B L) :=
  quotientForm (B.restrict (Perp B L)) (fun x y => hB.isRefl x.val y.val)
    (Inside B L) (inside_le_kernel B L)

@[simp] theorem reducedForm_mk (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (x y : Perp B L) :
    reducedForm B hB L ((Inside B L).mkQ x) ((Inside B L).mkQ y) = B x.val y.val := rfl

theorem reducedForm_isAlt (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (L : Submodule K V) :
    (reducedForm B hB L).IsAlt :=
  quotientForm_isAlt (B.restrict (Perp B L)) (fun x => hB x.val) _ (inside_le_kernel B L)

theorem ker_restrict_perp (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (L : Submodule K V) :
    LinearMap.ker (B.restrict (Perp B L)) = Inside B L := by
  ext x
  change (B.restrict (Perp B L)) x = 0 ↔ x.val ∈ L
  constructor
  · intro hx
    have ho : x.val ∈ B.orthogonal (B.orthogonal L) := by
      intro y hy
      exact hB.isRefl x.val y (LinearMap.congr_fun hx ⟨y,hy⟩)
    rw [B.orthogonal_orthogonal hnd hB.isRefl L] at ho
    exact ho
  · intro hx
    apply LinearMap.ext
    intro y
    exact y.property x.val hx

/-- Nondegeneracy is proved for the genuine reduced bilinear form. -/
theorem reducedForm_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (L : Submodule K V) :
    (reducedForm B hB L).Nondegenerate :=
  quotientForm_nondegenerate (B.restrict (Perp B L)) (fun x => hB x.val)
    (Inside B L) (ker_restrict_perp B hB hnd L).symm

/-- The exact additive dimension formula for isotropic reduction. -/
theorem finrank_reduced_add (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (L : Submodule K V) (hiso : L ≤ Perp B L) :
    finrank K (Reduced B L) + 2 * finrank K L = finrank K V := by
  have hN : finrank K (Inside B L) = finrank K L :=
    (Submodule.comapSubtypeEquivOfLe hiso).finrank_eq
  have hq := (Inside B L).finrank_quotient_add_finrank
  have hp := B.finrank_add_finrank_orthogonal hB.isRefl L
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot hnd, inf_bot_eq, finrank_bot, add_zero] at hp
  change finrank K (Reduced B L) + finrank K (Inside B L) = finrank K (Perp B L) at hq
  rw [hN] at hq
  change finrank K L + finrank K (Perp B L) = finrank K V at hp
  omega

/-- Quotient the actual intersection with the perpendicular space. -/
def quotientImage (B : LinearMap.BilinForm K V) (L U : Submodule K V) :
    Submodule K (Reduced B L) :=
  (U.comap (Perp B L).subtype).map (Inside B L).mkQ

/-- Take the actual inverse image, and then its inclusion into the ambient space. -/
def quotientPreimage (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (T : Submodule K (Reduced B L)) : Submodule K V :=
  (T.comap (Inside B L).mkQ).map (Perp B L).subtype

@[simp] theorem quotientImage_preimage (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (T : Submodule K (Reduced B L)) :
    quotientImage B L (quotientPreimage B L T) = T := by
  unfold quotientImage quotientPreimage
  rw [Submodule.comap_map_eq_of_injective (show Function.Injective (Perp B L).subtype from Subtype.val_injective)]
  exact Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _) _

theorem quotientPreimage_image (B : LinearMap.BilinForm K V) (L U : Submodule K V)
    (hLU : L ≤ U) (hUW : U ≤ Perp B L) :
    quotientPreimage B L (quotientImage B L U) = U := by
  have hNU : Inside B L ≤ U.comap (Perp B L).subtype := by
    intro x hx
    exact hLU hx
  unfold quotientPreimage quotientImage
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hNU, Submodule.map_comap_subtype,
    inf_eq_right.mpr hUW]

theorem radical_le_perp (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L U : Submodule K V) (hU : radical B U = L) : U ≤ Perp B L := by
  intro x hx y hy
  have hyrad : y ∈ radical B U := hU ▸ hy
  exact ((mem_radical_iff B hB.isRefl U y).mp hyrad).2 x hx

/-- Subspaces of a reduced symplectic space with nondegenerate restricted form. -/
def NondegenerateSubspace (B : LinearMap.BilinForm K V) (d : ℕ) :=
  {U : Submodule K V // finrank K U = d ∧ (B.restrict U).Nondegenerate}

/-- Ambient subspaces with an exactly prescribed radical. -/
def FiberSubspace (B : LinearMap.BilinForm K V) (L : Submodule K V) (d : ℕ) :=
  {U : Submodule K V // finrank K U = d + finrank K L ∧ radical B U = L}

theorem quotientImage_finrank_add (B : LinearMap.BilinForm K V) (L U : Submodule K V)
    (hiso : L ≤ Perp B L) (hLU : L ≤ U) (hUW : U ≤ Perp B L) :
    finrank K (quotientImage B L U) + finrank K L = finrank K U := by
  have hNU : Inside B L ≤ U.comap (Perp B L).subtype := fun _ hx => hLU hx
  have hNdim : finrank K (Inside B L) = finrank K L :=
    (Submodule.comapSubtypeEquivOfLe hiso).finrank_eq
  have hUdim : finrank K (U.comap (Perp B L).subtype) = finrank K U :=
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq
  have h := finrank_quotient_image (Inside B L) (U.comap (Perp B L).subtype) hNU
  change finrank K (quotientImage B L U) + finrank K (Inside B L) =
    finrank K (U.comap (Perp B L).subtype) at h
  rwa [hNdim,hUdim] at h

theorem quotientPreimage_finrank (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (hiso : L ≤ Perp B L) (T : Submodule K (Reduced B L)) :
    finrank K (quotientPreimage B L T) = finrank K T + finrank K L := by
  have hNdim : finrank K (Inside B L) = finrank K L :=
    (Submodule.comapSubtypeEquivOfLe hiso).finrank_eq
  have h := finrank_quotient_image (Inside B L) (T.comap (Inside B L).mkQ)
    ((Inside B L).le_comap_mkQ T)
  rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _),hNdim] at h
  exact (Submodule.finrank_map_subtype_eq (Perp B L) (T.comap (Inside B L).mkQ)).trans h.symm

theorem quotientImage_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L U : Submodule K V) (hiso : L ≤ Perp B L) (hr : radical B U = L) :
    ((reducedForm B hB L).restrict (quotientImage B L U)).Nondegenerate := by
  have hLU : L ≤ U := by rw [← hr]; exact inf_le_left
  have hUW := radical_le_perp B hB L U hr
  have hNU : Inside B L ≤ U.comap (Perp B L).subtype := fun _ hx => hLU hx
  have hr' : radical (B.restrict (Perp B L)) (U.comap (Perp B L).subtype) = Inside B L := by
    apply Submodule.map_injective_of_injective
      (f := (Perp B L).subtype) (show Function.Injective (Perp B L).subtype from Subtype.val_injective)
    rw [radical_map_subtype B hB.isRefl, Submodule.map_comap_subtype,
      inf_eq_right.mpr hUW,hr]
    change L = (L.comap (Perp B L).subtype).map (Perp B L).subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hiso]
  exact (quotient_restrict_nondegenerate_iff (B.restrict (Perp B L))
    (fun x => hB x.val) (Inside B L) (inside_le_kernel B L)
    (U.comap (Perp B L).subtype) hNU).mpr hr'

theorem quotientPreimage_radical (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hiso : L ≤ Perp B L) (T : Submodule K (Reduced B L))
    (hT : ((reducedForm B hB L).restrict T).Nondegenerate) :
    radical B (quotientPreimage B L T) = L := by
  have hNS := (Inside B L).le_comap_mkQ T
  have hr : radical (B.restrict (Perp B L)) (T.comap (Inside B L).mkQ) = Inside B L := by
    apply (quotient_restrict_nondegenerate_iff (B.restrict (Perp B L))
      (fun x => hB x.val) (Inside B L) (inside_le_kernel B L)
      (T.comap (Inside B L).mkQ) hNS).mp
    change ((reducedForm B hB L).restrict
      ((T.comap (Inside B L).mkQ).map (Inside B L).mkQ)).Nondegenerate
    rwa [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _)]
  unfold quotientPreimage
  rw [← radical_map_subtype B hB.isRefl, hr]
  change (L.comap (Perp B L).subtype).map (Perp B L).subtype = L
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hiso]

/-- The genuine radical fiber equals the nondegenerate-subspace fiber of the
actual reduced quotient. No geometric dominance is asserted. -/
def radicalFiberEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hiso : L ≤ Perp B L) (d : ℕ) :
    FiberSubspace B L d ≃ NondegenerateSubspace (reducedForm B hB L) d where
  toFun U := ⟨quotientImage B L U.val, by
    have hLU : L ≤ U.val := U.property.2.ge.trans inf_le_left
    have hUW := radical_le_perp B hB L U.val U.property.2
    have hdim := quotientImage_finrank_add B L U.val hiso hLU hUW
    refine ⟨?_,quotientImage_nondegenerate B hB L U.val hiso U.property.2⟩
    have hUdim := U.property.1
    omega⟩
  invFun T := ⟨quotientPreimage B L T.val, by
    refine ⟨?_,quotientPreimage_radical B hB L hiso T.val T.property.2⟩
    rw [quotientPreimage_finrank B L hiso, T.property.1]⟩
  left_inv U := by
    apply Subtype.ext
    have hLU : L ≤ U.val := U.property.2.ge.trans inf_le_left
    exact quotientPreimage_image B L U.val hLU (radical_le_perp B hB L U.val U.property.2)
  right_inv T := Subtype.ext (quotientImage_preimage B L T.val)

/-- Orthogonal complementation preserves nondegeneracy in the actual ambient form. -/
theorem orthogonal_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (U : Submodule K V) (hU : (B.restrict U).Nondegenerate) :
    (B.restrict (B.orthogonal U)).Nondegenerate := by
  apply (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl).mpr
  rw [B.orthogonal_orthogonal hnd hB.isRefl U]
  exact (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU).symm

/-- Orthogonal complementation as a genuine involutive correspondence of
nondegenerate subspaces of complementary dimensions. -/
def orthogonalEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (d e : ℕ) (hdim : finrank K V = d+e) :
    NondegenerateSubspace B d ≃ NondegenerateSubspace B e where
  toFun U := ⟨B.orthogonal U.val, by
    refine ⟨?_,orthogonal_nondegenerate B hB hnd U.val U.property.2⟩
    rw [B.finrank_orthogonal hnd,hdim,U.property.1]
    omega⟩
  invFun U := ⟨B.orthogonal U.val, by
    refine ⟨?_,orthogonal_nondegenerate B hB hnd U.val U.property.2⟩
    rw [B.finrank_orthogonal hnd,hdim,U.property.1]
    omega⟩
  left_inv U := Subtype.ext (B.orthogonal_orthogonal hnd hB.isRefl U.val)
  right_inv U := Subtype.ext (B.orthogonal_orthogonal hnd hB.isRefl U.val)

/-- Every line is isotropic for an alternating form. -/
theorem line_isotropic (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hL : finrank K L = 1) : L ≤ Perp B L := by
  intro x hx y hy
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hxne : (⟨x,hx⟩ : L) ≠ 0 := by
      intro h
      exact hx0 (congrArg Subtype.val h)
    obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hL hxne (⟨y,hy⟩ : L)
    have hc' : c • x = y := congrArg Subtype.val hc
    rw [← hc']
    simp [hB x]

/-- The 9-plane radical fiber is the nondegenerate 8-plane fiber in the actual
12-dimensional symplectic reduction. -/
def nineEightEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hL : finrank K L = 1) :
    {U : Submodule K V // finrank K U = 9 ∧ radical B U = L} ≃
      NondegenerateSubspace (reducedForm B hB L) 8 := by
  let e : {U : Submodule K V // finrank K U = 9 ∧ radical B U = L} ≃
      FiberSubspace B L 8 := Equiv.subtypeEquivRight (fun U => by
        change (finrank K U = 9 ∧ radical B U = L) ↔
          (finrank K U = 8 + finrank K L ∧ radical B U = L)
        simp only [hL])
  exact e.trans (radicalFiberEquiv B hB L (line_isotropic B hB L hL) 8)

@[simp] theorem nineEightEquiv_apply_val (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hL : finrank K L = 1)
    (U : {U : Submodule K V // finrank K U = 9 ∧ radical B U = L}) :
    (nineEightEquiv B hB L hL U).val = quotientImage B L U.val := rfl

@[simp] theorem nineEightEquiv_symm_apply_val (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (L : Submodule K V) (hL : finrank K L = 1)
    (T : NondegenerateSubspace (reducedForm B hB L) 8) :
    ((nineEightEquiv B hB L hL).symm T).val = quotientPreimage B L T.val := rfl

/-- The reduced space of a line in dimension fourteen really has dimension twelve. -/
theorem finrank_reduced_line (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank K V = 14)
    (L : Submodule K V) (hL : finrank K L = 1) : finrank K (Reduced B L) = 12 := by
  have hdim := finrank_reduced_add B hB hnd L (line_isotropic B hB L hL)
  rw [hV,hL] at hdim
  omega

/-- The complete linear fiber correspondence in a fourteen-dimensional
symplectic space. Its maps are quotient and perpendicular inverse image. -/
def nineFourEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank K V = 14)
    (L : Submodule K V) (hL : finrank K L = 1) :
    {U : Submodule K V // finrank K U = 9 ∧ radical B U = L} ≃
      NondegenerateSubspace (reducedForm B hB L) 4 := by
  have hE : finrank K (Reduced B L) = 8+4 := finrank_reduced_line B hB hnd hV L hL
  exact (nineEightEquiv B hB L hL).trans
    (orthogonalEquiv (reducedForm B hB L) (reducedForm_isAlt B hB L)
      (reducedForm_nondegenerate B hB hnd L) 8 4 hE)

@[simp] theorem nineFourEquiv_apply_val (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank K V = 14)
    (L : Submodule K V) (hL : finrank K L = 1)
    (U : {U : Submodule K V // finrank K U = 9 ∧ radical B U = L}) :
    (nineFourEquiv B hB hnd hV L hL U).val =
      (reducedForm B hB L).orthogonal (quotientImage B L U.val) := rfl

@[simp] theorem nineFourEquiv_symm_apply_val (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank K V = 14)
    (L : Submodule K V) (hL : finrank K L = 1)
    (Z : NondegenerateSubspace (reducedForm B hB L) 4) :
    ((nineFourEquiv B hB hnd hV L hL).symm Z).val =
      quotientPreimage B L ((reducedForm B hB L).orthogonal Z.val) := rfl

end Finite

section Concrete
variable (K : Type*) [Field K] [CharZero K]
open PrimitiveRepresentation

/-- The actual linear radical fiber for the previously proved coordinate model.
An exterior-power or Mukai identification is not part of this theorem. -/
def coordinateNineFourEquiv (L : Submodule K (Coordinates K)) (hL : finrank K L = 1) :
    {U : Submodule K (Coordinates K) // finrank K U = 9 ∧ radical (pairing K) U = L} ≃
      NondegenerateSubspace (reducedForm (pairing K) (pairing_isAlt K) L) 4 :=
  nineFourEquiv (pairing K) (pairing_isAlt K) (pairing_nondegenerate K)
    (finrank_coordinates K) L hL

end Concrete
end M9.RadicalFiber
