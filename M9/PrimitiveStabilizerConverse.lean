module

public import M9.PrimitiveStabilizer
public import M9.CentralSignQuotient

/-!
# Converse to the explicit primitive line-stabilizer construction

The covariance and directly computed spectrum of the genuine endomorphism
`K_(a+b)` force every actual line stabilizer to preserve or exchange the two
Lagrangian summands. No stabilizer-classification assumption is used.
-/

@[expose] public section
noncomputable section
namespace M9.PrimitiveStabilizer
open Module Matrix ExteriorPrimitive
open scoped Classical
variable (K : Type*) [Field K]

/-- The actual endomorphism associated with the actual split three-vector. -/
abbrev splitEndomorphism := PrimitiveEndomorphism.endomorphism K (a K+b K)

@[simp] theorem splitEndomorphism_proj (i : Fin 6) :
    splitEndomorphism K (LinearMap.proj i) =
      PrimitiveEndomorphism.splitSign K i • (LinearMap.proj i : Dual K (V K)) :=
  PrimitiveEndomorphism.endomorphism_split_proj K i

/-- The diagonal spectrum controls evaluation of every covector, not only basis covectors. -/
theorem splitEndomorphism_basisEval (α : Dual K (V K)) (j : Fin 6) :
    splitEndomorphism K α (basisVector K j) =
      PrimitiveEndomorphism.splitSign K j * α (basisVector K j) := by
  have hα : (∑ i : Fin 6, α (basisVector K i) • (LinearMap.proj i : Dual K (V K))) = α := by
    apply (Pi.basisFun K (Fin 6)).ext
    intro k
    simp [basisVector,Pi.basisFun_apply,LinearMap.sum_apply,LinearMap.smul_apply,Pi.single_apply]
  have hk := congrArg (fun β : Dual K (V K) => splitEndomorphism K β (basisVector K j)) hα
  simpa [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,basisVector,
    Pi.single_apply,smul_eq_mul,mul_comm] using hk.symm

/-- Genuine K-covariance, together with an actual proportionality of split vectors,
yields the intertwining identity used in the converse. -/
theorem line_endomorphism_intertwine (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) (α : Dual K (V K)) :
    splitEndomorphism K (h.val.dualMap α) = c^2 • h.val.dualMap (splitEndomorphism K α) := by
  have hn := PrimitiveEndomorphism.endomorphism_naturality_of_det_one K h.val
    (symplectic_det_one K h) (a K+b K) α
  change PrimitiveEndomorphism.endomorphism K (exteriorAction K h (a K+b K)) α = _ at hn
  rw [hc,PrimitiveEndomorphism.endomorphism_smul] at hn
  have hd := congrArg h.val.dualMap hn
  simpa only [LinearMap.smul_apply,map_smul,LinearEquiv.apply_symm_apply] using hd.symm

/-- The scalar of any actual line stabilizer has square either +1 or -1. -/
theorem line_scalar_square (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) : c^2 = 1 ∨ c^2 = -1 := by
  let β : Dual K (V K) := h.val.dualMap (LinearMap.proj 0)
  have hβ : splitEndomorphism K β = c^2 • β := by
    simpa [β,PrimitiveEndomorphism.splitSign] using
      line_endomorphism_intertwine K h c hc (LinearMap.proj 0)
  have hβne : β ≠ 0 := by
    intro hz
    have hp : (LinearMap.proj 0 : Dual K (V K)) = 0 :=
      h.val.dualMap.injective (by simpa [β] using hz)
    have hval := LinearMap.congr_fun hp (basisVector K 0)
    simpa [basisVector,Pi.single_apply] using hval
  have hs := LinearMap.congr_fun (PrimitiveEndomorphism.endomorphism_split_square K) β
  change splitEndomorphism K (splitEndomorphism K β) = β at hs
  rw [hβ,map_smul,hβ,smul_smul] at hs
  have hscalar : c^2*c^2=1 := (smul_left_injective K hβne) (by
    simpa only [one_smul] using hs)
  have hfactor : (c^2-1)*(c^2+1)=0 := by
    calc
      _ = c^2*c^2-1 := by ring
      _ = 0 := by rw [hscalar,sub_self]
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · exact Or.inl (sub_eq_zero.mp hplus)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp hminus)

/-- An exact coefficient consequence of the genuine intertwining identity. -/
theorem line_entry_relation (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) (i j : Fin 6) :
    PrimitiveEndomorphism.splitSign K j * h.val (basisVector K j) i =
      c^2 * PrimitiveEndomorphism.splitSign K i * h.val (basisVector K j) i := by
  have he := LinearMap.congr_fun (line_endomorphism_intertwine K h c hc (LinearMap.proj i))
    (basisVector K j)
  rw [splitEndomorphism_basisEval,splitEndomorphism_proj] at he
  simpa [LinearEquiv.dualMap_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,mul_assoc] using he

@[simp] theorem splitSign_e (i : Fin 3) : PrimitiveEndomorphism.splitSign K (eIndex i) = 1 := by
  simp [PrimitiveEndomorphism.splitSign,eIndex,i.isLt]

@[simp] theorem splitSign_f (i : Fin 3) : PrimitiveEndomorphism.splitSign K (fIndex i) = -1 := by
  have hi : ¬(fIndex i).val < 3 := by
    change ¬(3+i.val < 3)
    omega
  simp [PrimitiveEndomorphism.splitSign,hi]

/-- The actual lower/upper cross blocks vanish. -/
def PreservesSplit (h : Sp6 K) : Prop :=
  (∀ i j : Fin 3, h.val (e K i) (fIndex j)=0) ∧
  (∀ i j : Fin 3, h.val (f K i) (eIndex j)=0)

/-- The actual two diagonal blocks vanish. -/
def ExchangesSplit (h : Sp6 K) : Prop :=
  (∀ i j : Fin 3, h.val (e K i) (eIndex j)=0) ∧
  (∀ i j : Fin 3, h.val (f K i) (fIndex j)=0)

section CharacteristicZero
variable [CharZero K]

theorem zero_of_eq_neg (x : K) (hx : x = -x) : x=0 := by
  have htwo : (2 : K)*x=0 := by linear_combination hx
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

theorem preservesSplit_of_scalar_square_one (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) (hc2 : c^2=1) :
    PreservesSplit K h := by
  constructor
  · intro i j
    have he := line_entry_relation K h c hc (fIndex j) (eIndex i)
    simp only [splitSign_e,splitSign_f,hc2,one_mul,neg_one_mul] at he
    exact zero_of_eq_neg K _ he
  · intro i j
    have he := line_entry_relation K h c hc (eIndex j) (fIndex i)
    simp only [splitSign_e,splitSign_f,hc2,one_mul,neg_one_mul] at he
    exact zero_of_eq_neg K _ he.symm

theorem exchangesSplit_of_scalar_square_neg_one (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) (hc2 : c^2 = -1) :
    ExchangesSplit K h := by
  constructor
  · intro i j
    have he := line_entry_relation K h c hc (eIndex j) (eIndex i)
    simp only [splitSign_e,hc2,one_mul,mul_one,neg_one_mul] at he
    exact zero_of_eq_neg K _ he
  · intro i j
    have he := line_entry_relation K h c hc (fIndex j) (fIndex i)
    simp only [splitSign_f,hc2,neg_one_mul,neg_neg,one_mul] at he
    exact zero_of_eq_neg K _ he.symm

/-- Every element of the genuine primitive line stabilizer preserves or exchanges
the actual Lagrangian summands. This is a conclusion from K-covariance. -/
theorem stabilizer_preserves_or_exchanges (h : Sp6 K) (hh : h ∈ lineStabilizer K) :
    PreservesSplit K h ∨ ExchangesSplit K h := by
  obtain ⟨c,hc0,hc⟩ := (mem_lineStabilizer_iff K h).mp hh
  have hc' : exteriorAction K h (a K+b K) = c • (a K+b K) := congrArg Subtype.val hc
  rcases line_scalar_square K h c hc' with hc2 | hc2
  · exact Or.inl (preservesSplit_of_scalar_square_one K h c hc' hc2)
  · exact Or.inr (exchangesSplit_of_scalar_square_neg_one K h c hc' hc2)

/-- The actual upper-left block of a symplectic transformation. -/
def leftBlock (h : Sp6 K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => h.val (e K j) (eIndex i)

/-- The actual lower-right block of a symplectic transformation. -/
def rightBlock (h : Sp6 K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => h.val (f K j) (fIndex i)

theorem preserving_blocks_dual (h : Sp6 K) (hP : PreservesSplit K h) :
    (leftBlock K h).transpose * rightBlock K h = 1 := by
  ext i j
  have hs := sp6_omega K h (e K i) (f K j)
  rw [omega_e_f] at hs
  change (∑ k : Fin 3, (h.val (e K i) (eIndex k) * h.val (f K j) (fIndex k) -
    h.val (e K i) (fIndex k) * h.val (f K j) (eIndex k))) = _ at hs
  simp only [hP.1 i,hP.2 j,mul_zero,zero_mul,sub_zero] at hs
  simpa only [leftBlock,rightBlock,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hs

/-- Duality of the actual blocks identifies the lower block with the inverse transpose. -/
theorem rightBlock_eq_inverseTranspose (h : Sp6 K) (hP : PreservesSplit K h)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (hg : leftBlock K h = g.val) :
    rightBlock K h = (g⁻¹).val.transpose := by
  have hdual := preserving_blocks_dual K h hP
  rw [hg] at hdual
  have hcancel : (g⁻¹).val.transpose * g.val.transpose = 1 := by
    rw [← Matrix.transpose_mul]
    have he : g.val*(g⁻¹).val=1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [he,Matrix.transpose_one]
  calc
    rightBlock K h = 1 * rightBlock K h := (Matrix.one_mul _).symm
    _ = ((g⁻¹).val.transpose * g.val.transpose) * rightBlock K h := by rw [hcancel]
    _ = (g⁻¹).val.transpose * (g.val.transpose * rightBlock K h) := Matrix.mul_assoc _ _ _
    _ = (g⁻¹).val.transpose := by rw [hdual,Matrix.mul_one]

/-- Equality of actual preserving blocks identifies the original symplectic element. -/
theorem eq_block_of_leftBlock (h : Sp6 K) (hP : PreservesSplit K h)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (hg : leftBlock K h = g.val) : h = block K g := by
  have hd := rightBlock_eq_inverseTranspose K h hP g hg
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (splitBasis K).ext
  intro t
  cases t with
  | inl i =>
    change h.val (splitBasis K (Sum.inl i)) = (block K g).val (splitBasis K (Sum.inl i))
    rw [splitBasis_inl]
    apply (splitV K).injective
    apply Prod.ext <;> funext j
    · change h.val (e K i) (eIndex j) = (block K g).val (e K i) (eIndex j)
      rw [block_e_e]
      exact congrFun (congrFun hg j) i
    · change h.val (e K i) (fIndex j) = (block K g).val (e K i) (fIndex j)
      rw [block_e_f]
      exact hP.1 i j
  | inr i =>
    change h.val (splitBasis K (Sum.inr i)) = (block K g).val (splitBasis K (Sum.inr i))
    rw [splitBasis_inr]
    apply (splitV K).injective
    apply Prod.ext <;> funext j
    · change h.val (f K i) (eIndex j) = (block K g).val (f K i) (eIndex j)
      rw [block_f_e]
      exact hP.2 i j
    · change h.val (f K i) (fIndex j) = (block K g).val (f K i) (fIndex j)
      rw [block_f_f]
      exact congrFun (congrFun hd j) i

theorem aCoordinate_action_a (h : Sp6 K) :
    aCoordinate K (exteriorAction K h (a K)) = (leftBlock K h).det := by
  rw [a,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K (h.val (e K 0)) (h.val (e K 1)) (h.val (e K 2))) = (leftBlock K h).det
  rw [coordinate_wedge3,Matrix.det_fin_three]
  simp only [leftBlock]
  ring

theorem aCoordinate_action_b_of_preserves (h : Sp6 K) (hP : PreservesSplit K h) :
    aCoordinate K (exteriorAction K h (b K)) = 0 := by
  rw [b,exteriorAction_wedge3]
  change coordinate K (eIndex 0) (eIndex 1) (eIndex 2)
    (wedge3 K (h.val (f K 0)) (h.val (f K 1)) (h.val (f K 2))) = 0
  simp [coordinate_wedge3,hP.2]

/-- The scalar on rho is the actual determinant of the preserving three-dimensional block. -/
theorem leftBlock_det_of_scalar (h : Sp6 K) (hP : PreservesSplit K h) (c : K)
    (hc : exteriorAction K h (a K+b K) = c • (a K+b K)) : (leftBlock K h).det = c := by
  have ha := congrArg (aCoordinate K) hc
  simpa only [map_add,map_smul,aCoordinate_action_a,aCoordinate_action_b_of_preserves K h hP,
    aCoordinate_a,aCoordinate_b,add_zero,smul_eq_mul,mul_one] using ha

/-- A preserving symplectic element fixing rho is an actual special-linear block. -/
theorem eq_block_of_fixing_rho (h : Sp6 K) (hP : PreservesSplit K h)
    (hc : exteriorAction K h (a K+b K) = a K+b K) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, h = block K g := by
  have hd : (leftBlock K h).det = 1 := leftBlock_det_of_scalar K h hP 1 (by simpa using hc)
  let g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨leftBlock K h,hd⟩
  exact ⟨g,eq_block_of_leftBlock K h hP g rfl⟩

@[simp] theorem negativeIdentity_square : negativeIdentity K * negativeIdentity K = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change - -v = v
  exact neg_neg v

theorem negativeIdentity_central (h : Sp6 K) : negativeIdentity K * h = h * negativeIdentity K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change -h.val v = h.val (-v)
  exact (map_neg h.val v).symm

theorem negativeIdentity_mem_lineStabilizer : negativeIdentity K ∈ lineStabilizer K := by
  apply (mem_lineStabilizer_iff K _).mpr
  refine ⟨-1,neg_ne_zero.mpr one_ne_zero,?_⟩
  apply Subtype.ext
  change exteriorAction K (negativeIdentity K) (a K+b K) = (-1 : K) • (a K+b K)
  rw [exteriorAction_negativeIdentity]
  simp [add_comm]

theorem preservesSplit_negative_mul (h : Sp6 K) (hP : PreservesSplit K h) :
    PreservesSplit K (negativeIdentity K*h) := by
  constructor
  · intro i j
    change -h.val (e K i) (fIndex j)=0
    rw [hP.1 i j,neg_zero]
  · intro i j
    change -h.val (f K i) (eIndex j)=0
    rw [hP.2 i j,neg_zero]

/-- The preserving scalar-square-one case has the exact two signed block normal forms. -/
theorem normalForms_of_scalar_square_one (h : Sp6 K) (c : K)
    (hc : exteriorAction K h (a K+b K)=c • (a K+b K)) (hc2 : c^2=1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
      h=block K g ∨ h=negativeIdentity K*block K g := by
  have hP := preservesSplit_of_scalar_square_one K h c hc hc2
  have hfactor : (c-1)*(c+1)=0 := by
    calc
      _ = c^2-1 := by ring
      _ = 0 := by rw [hc2,sub_self]
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hc1 : c=1 := sub_eq_zero.mp hplus
    rw [hc1,one_smul] at hc
    obtain ⟨g,hg⟩ := eq_block_of_fixing_rho K h hP hc
    exact ⟨g,Or.inl hg⟩
  · have hc1 : c= -1 := add_eq_zero_iff_eq_neg.mp hminus
    have hn : exteriorAction K (negativeIdentity K*h) (a K+b K)=a K+b K := by
      rw [exteriorAction_mul]
      change exteriorAction K (negativeIdentity K) (exteriorAction K h (a K+b K)) = _
      rw [hc,hc1,exteriorAction_negativeIdentity]
      simp [add_comm]
    obtain ⟨g,hg⟩ := eq_block_of_fixing_rho K (negativeIdentity K*h)
      (preservesSplit_negative_mul K h hP) hn
    refine ⟨g,Or.inr ?_⟩
    have he := congrArg (fun x : Sp6 K => negativeIdentity K*x) hg
    simpa only [← mul_assoc,negativeIdentity_square,one_mul] using he

theorem exchanging_inverse (i : K) (hi : i^2 = -1) :
    (exchanging K i hi)⁻¹ = negativeIdentity K * exchanging K i hi := by
  apply (mul_left_injective (exchanging K i hi))
  change (exchanging K i hi)⁻¹ * exchanging K i hi =
    (negativeIdentity K * exchanging K i hi) * exchanging K i hi
  rw [inv_mul_cancel,mul_assoc,exchanging_square,negativeIdentity_square]

theorem exchanging_inverse_rho (i : K) (hi : i^2 = -1) :
    exteriorAction K (exchanging K i hi)⁻¹ (a K+b K) = i • (a K+b K) := by
  rw [exchanging_inverse,exteriorAction_mul]
  change exteriorAction K (negativeIdentity K)
    (exteriorAction K (exchanging K i hi) (a K+b K)) = _
  simp only [map_add,exchanging_a,exchanging_b,exteriorAction_negativeIdentity,
    LinearMap.neg_apply,LinearMap.id_apply]
  module

/-- The complete four normal forms of the actual primitive line stabilizer. -/
theorem stabilizer_normalForms (i : K) (hi : i^2 = -1)
    (h : Sp6 K) (hh : h ∈ lineStabilizer K) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
      h=block K g ∨ h=negativeIdentity K*block K g ∨
      h=exchanging K i hi*block K g ∨ h=negativeIdentity K*exchanging K i hi*block K g := by
  obtain ⟨c,hc0,hc⟩ := (mem_lineStabilizer_iff K h).mp hh
  have hc' : exteriorAction K h (a K+b K)=c • (a K+b K) := congrArg Subtype.val hc
  rcases line_scalar_square K h c hc' with hc2 | hc2
  · obtain ⟨g,hg|hg⟩ := normalForms_of_scalar_square_one K h c hc' hc2
    · exact ⟨g,Or.inl hg⟩
    · exact ⟨g,Or.inr (Or.inl hg)⟩
  · have hn : exteriorAction K ((exchanging K i hi)⁻¹*h) (a K+b K)=
        (c*i) • (a K+b K) := by
      rw [exteriorAction_mul]
      change exteriorAction K (exchanging K i hi)⁻¹ (exteriorAction K h (a K+b K)) = _
      rw [hc',map_smul,exchanging_inverse_rho,smul_smul]
    have hn2 : (c*i)^2=1 := by rw [mul_pow,hc2,hi]; ring
    obtain ⟨g,hg|hg⟩ := normalForms_of_scalar_square_one K ((exchanging K i hi)⁻¹*h) (c*i) hn hn2
    · refine ⟨g,Or.inr (Or.inr (Or.inl ?_))⟩
      have he := congrArg (fun x : Sp6 K => exchanging K i hi*x) hg
      simpa only [← mul_assoc,mul_inv_cancel,one_mul] using he
    · refine ⟨g,Or.inr (Or.inr (Or.inr ?_))⟩
      have he := congrArg (fun x : Sp6 K => exchanging K i hi*x) hg
      have he' : h=exchanging K i hi*(negativeIdentity K*block K g) := by
        simpa only [← mul_assoc,mul_inv_cancel,one_mul] using he
      rw [he',← mul_assoc,← negativeIdentity_central]

/-- The actual central sign cannot be a connected special-linear block. -/
theorem block_ne_negativeIdentity (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    block K g ≠ negativeIdentity K := by
  intro hg
  have hm : g.val = -(1 : Matrix (Fin 3) (Fin 3) K) := by
    ext j i
    have he := congrArg (fun h : Sp6 K => h.val (e K i) (eIndex j)) hg
    rw [block_e_e,negativeIdentity_apply] at he
    fin_cases i <;> fin_cases j <;>
      simpa [e,basisVector,eIndex,Pi.single_apply,Matrix.one_apply] using he
  have hd := congrArg Matrix.det hm
  rw [g.property,Matrix.det_neg,Matrix.det_one] at hd
  norm_num at hd

/-- The actual connected stabilizer embedding, with its subgroup membership proved. -/
def blockStabilizerHom : Matrix.SpecialLinearGroup (Fin 3) K →* lineStabilizer K where
  toFun g := ⟨block K g,block_mem_lineStabilizer K g⟩
  map_one' := Subtype.ext (blockHom K).map_one
  map_mul' g h := Subtype.ext ((blockHom K).map_mul g h)

theorem blockStabilizerHom_injective : Function.Injective (blockStabilizerHom K) := by
  intro g h he
  apply block_injective K
  exact congrArg Subtype.val he

/-- The actual central sign as an element of the actual line stabilizer. -/
def centralSign : lineStabilizer K := ⟨negativeIdentity K,negativeIdentity_mem_lineStabilizer K⟩

/-- The actual exchanging lift as an element of the actual line stabilizer. -/
def swappingElement (i : K) (hi : i^2 = -1) : lineStabilizer K :=
  ⟨exchanging K i hi,exchanging_mem_lineStabilizer K i hi⟩

theorem centralSign_not_range : centralSign K ∉ Set.range (blockStabilizerHom K) := by
  rintro ⟨g,hg⟩
  exact block_ne_negativeIdentity K g (congrArg Subtype.val hg)

/-- The actual scalar on the stabilized primitive line, extracted by its a-coordinate. -/
def lineScalar (h : lineStabilizer K) : K :=
  aCoordinate K (exteriorAction K h.val (a K+b K))

theorem lineScalar_spec (h : lineStabilizer K) :
    lineScalar K h ≠ 0 ∧ primitiveAction K h.val (rho K)=lineScalar K h • rho K := by
  obtain ⟨c,hc0,hc⟩ := (mem_lineStabilizer_iff K h.val).mp h.property
  have hc' : exteriorAction K h.val (a K+b K)=c • (a K+b K) := congrArg Subtype.val hc
  have hv : lineScalar K h = c := by
    unfold lineScalar
    rw [hc',map_smul,map_add,aCoordinate_a,aCoordinate_b]
    simp
  rw [hv]
  exact ⟨hc0,hc⟩

@[simp] theorem lineScalar_one : lineScalar K 1=1 := by
  change aCoordinate K (exteriorAction K 1 (a K+b K))=1
  rw [exteriorAction_one]
  simp

theorem lineScalar_mul (h g : lineStabilizer K) :
    lineScalar K (h*g)=lineScalar K h*lineScalar K g := by
  have hm : primitiveAction K (h*g).val (rho K)=
      (lineScalar K h*lineScalar K g) • rho K := by
    change primitiveAction K (h.val*g.val) (rho K)=_
    rw [primitiveAction_mul]
    change primitiveAction K h.val (primitiveAction K g.val (rho K))=_
    rw [(lineScalar_spec K g).2,map_smul,(lineScalar_spec K h).2,smul_smul,mul_comm]
  have hv := congrArg (fun r : Primitive K => aCoordinate K r.val) hm
  simpa [lineScalar,rho,primitiveAction_val] using hv

/-- The actual nonzero line scalars form a multiplicative character. -/
def lineCharacter : lineStabilizer K →* Kˣ where
  toFun h := Units.mk0 (lineScalar K h) (lineScalar_spec K h).1
  map_one' := Units.ext (lineScalar_one K)
  map_mul' h g := Units.ext (lineScalar_mul K h g)

theorem lineScalar_square (h : lineStabilizer K) :
    (lineScalar K h)^2=1 ∨ (lineScalar K h)^2 = -1 := by
  apply line_scalar_square K h.val (lineScalar K h)
  exact congrArg Subtype.val (lineScalar_spec K h).2

@[simp] theorem lineScalar_block (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    lineScalar K (blockStabilizerHom K g)=1 := by
  change aCoordinate K (exteriorAction K (block K g) (a K+b K))=1
  simp

@[simp] theorem lineScalar_swapping (i : K) (hi : i^2 = -1) :
    lineScalar K (swappingElement K i hi) = -i := by
  change aCoordinate K (exteriorAction K (exchanging K i hi) (a K+b K))= -i
  simp

@[simp] theorem lineScalar_centralSign : lineScalar K (centralSign K)= -1 := by
  change aCoordinate K (exteriorAction K (negativeIdentity K) (a K+b K))= -1
  rw [exteriorAction_negativeIdentity]
  simp

/-- Actual parity is supplied by the square of the actual primitive-line character. -/
def stabilizerParity : lineStabilizer K →* CentralSignQuotient.C2 where
  toFun h := if (lineScalar K h)^2=1 then 1 else CentralSignQuotient.epsilon
  map_one' := by rw [lineScalar_one]; simp
  map_mul' h g := by
    change (if (lineScalar K (h*g))^2=1 then 1 else CentralSignQuotient.epsilon) =
      (if (lineScalar K h)^2=1 then 1 else CentralSignQuotient.epsilon) *
      (if (lineScalar K g)^2=1 then 1 else CentralSignQuotient.epsilon)
    have hm : (lineScalar K (h*g))^2=(lineScalar K h)^2*(lineScalar K g)^2 := by
      rw [lineScalar_mul,mul_pow]
    have hn : (-1 : K) ≠ 1 := by norm_num
    rcases lineScalar_square K h with hh | hh <;> rcases lineScalar_square K g with hg | hg <;>
      simp [hm,hh,hg,hn]

@[simp] theorem stabilizerParity_block (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    stabilizerParity K (blockStabilizerHom K g)=1 := by
  simp [stabilizerParity]

@[simp] theorem stabilizerParity_swapping (i : K) (hi : i^2 = -1) :
    stabilizerParity K (swappingElement K i hi)=CentralSignQuotient.epsilon := by
  have hn : (-1 : K) ≠ 1 := by norm_num
  change (if (lineScalar K (swappingElement K i hi))^2=1 then 1 else CentralSignQuotient.epsilon) = _
  rw [lineScalar_swapping,neg_sq,hi,if_neg hn]

theorem inverseTranspose_involutive : Function.Involutive (PrimitiveRepresentation.inverseTranspose K) := by
  intro g
  apply Subtype.ext
  change ((PrimitiveRepresentation.inverseTranspose K g)⁻¹).val.transpose = g.val
  rw [PrimitiveRepresentation.inverseTranspose_inv]
  exact Matrix.transpose_transpose _

theorem inverseTranspose_mul (g h : Matrix.SpecialLinearGroup (Fin 3) K) :
    PrimitiveRepresentation.inverseTranspose K (g*h) =
      PrimitiveRepresentation.inverseTranspose K g * PrimitiveRepresentation.inverseTranspose K h := by
  apply Subtype.ext
  change ((g*h)⁻¹).val.transpose=(g⁻¹).val.transpose*(h⁻¹).val.transpose
  rw [_root_.mul_inv_rev]
  exact Matrix.transpose_mul _ _

/-- The actual automorphism of SL3 induced by the exchanging component. -/
def inverseTransposeAut : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) where
  toFun := PrimitiveRepresentation.inverseTranspose K
  invFun := PrimitiveRepresentation.inverseTranspose K
  left_inv := inverseTranspose_involutive K
  right_inv := inverseTranspose_involutive K
  map_mul' := inverseTranspose_mul K

@[simp] theorem inverseTransposeAut_square : inverseTransposeAut K * inverseTransposeAut K=1 := by
  apply DFunLike.ext
  intro g
  exact inverseTranspose_involutive K g

end CharacteristicZero
end M9.PrimitiveStabilizer
