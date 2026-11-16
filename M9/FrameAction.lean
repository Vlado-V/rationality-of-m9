module

public import M9.Basic
public import M9.TetrahedralGroup
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The left-right and transpose actions on ternary matrices

These are the matrix actions in Sections 4.1--4.2 of the M9 paper.  The
projective faithfulness result is conditional on the stated, literal
orthogonality and scalar-kernel properties of the input group representation.
It does not assume a presentation of the tetrahedral group.
-/

@[expose] public section
noncomputable section

namespace M9.FrameAction

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K
abbrev GL3 (K : Type*) [Field K] := Matrix.GeneralLinearGroup (Fin 3) K

variable {K : Type*} [Field K]

/-- The connected left-right action, in the paper's order of factors. -/
def leftRight (a b : GL3 K) : Mat3 K ≃ₗ[K] Mat3 K where
  toFun M := (b : Mat3 K) * M * (↑a⁻¹ : Mat3 K)
  invFun M := (↑b⁻¹ : Mat3 K) * M * (a : Mat3 K)
  left_inv M := by simp [Matrix.mul_assoc]
  right_inv M := by simp [Matrix.mul_assoc]
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp

@[simp] theorem leftRight_apply (a b : GL3 K) (M : Mat3 K) :
    leftRight a b M = (b : Mat3 K) * M * (↑a⁻¹ : Mat3 K) := rfl

@[simp] theorem leftRight_one : leftRight (1 : GL3 K) 1 = 1 := by
  ext M
  simp

/-- Multiplication of pairs gives composition of their actual matrix actions. -/
theorem leftRight_mul (a b a' b' : GL3 K) :
    leftRight (a * a') (b * b') = leftRight a b * leftRight a' b' := by
  ext M
  simp [Matrix.mul_assoc]

/-- Transposition is a linear involution on the nine-dimensional matrix space. -/
def transpose : Mat3 K ≃ₗ[K] Mat3 K where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  map_add' := Matrix.transpose_add
  map_smul' := Matrix.transpose_smul

@[simp] theorem transpose_apply (M : Mat3 K) : transpose M = M.transpose := rfl

@[simp] theorem transpose_mul_self : (transpose : Mat3 K ≃ₗ[K] Mat3 K) * transpose = 1 := by
  apply LinearEquiv.ext
  intro M
  exact Matrix.transpose_transpose M

/-- Orthogonality is precisely what makes transposition exchange the two factors. -/
theorem transpose_leftRight (a b : GL3 K)
    (ha : (a : Mat3 K).transpose = (↑a⁻¹ : Mat3 K))
    (hb : (b : Mat3 K).transpose = (↑b⁻¹ : Mat3 K)) :
    transpose * leftRight a b = leftRight b a * transpose := by
  have hai : (↑a⁻¹ : Mat3 K).transpose = (a : Mat3 K) := by
    rw [← ha, Matrix.transpose_transpose]
  apply LinearEquiv.ext
  intro M
  simp only [LinearEquiv.mul_apply, transpose_apply, leftRight_apply,
    Matrix.transpose_mul, hai, hb]
  simp only [Matrix.mul_assoc]

private theorem leftRight_scalar_aux (a b : GL3 K) (c : K)
    (h : ∀ M : Mat3 K, leftRight a b M = c • M) :
    c ≠ 0 ∧ (b : Mat3 K) = c • (a : Mat3 K) ∧
      ∀ M : Mat3 K, (a : Mat3 K) * M = M * (a : Mat3 K) := by
  have hb : (b : Mat3 K) = c • (a : Mat3 K) := by
    have h1 := congrArg (fun M : Mat3 K => M * (a : Mat3 K)) (h 1)
    simpa [Matrix.mul_assoc, Matrix.smul_mul] using h1
  have hc : c ≠ 0 := by
    intro hc
    have hz : (b : Mat3 K) = 0 := by simpa only [hc, zero_smul] using hb
    have h10 : (1 : Mat3 K) = 0 := by
      simpa [hz] using (Units.inv_mul b).symm
    exact one_ne_zero h10
  refine ⟨hc, hb, ?_⟩
  intro M
  have hm := congrArg (fun N : Mat3 K => N * (a : Mat3 K)) (h M)
  have hm' : c • ((a : Mat3 K) * M) = c • (M * (a : Mat3 K)) := by
    simpa [Matrix.mul_assoc, Matrix.smul_mul, hb] using hm
  exact smul_right_injective (Mat3 K) hc hm'

/-- An everywhere scalar left-right operator has scalar matrices in both factors. -/
theorem scalar_factors_of_leftRight_scalar (a b : GL3 K) (c : K)
    (h : ∀ M : Mat3 K, leftRight a b M = c • M) :
    ∃ u v : K, (a : Mat3 K) = u • 1 ∧ (b : Mat3 K) = v • 1 := by
  obtain ⟨_, hb, ha⟩ := leftRight_scalar_aux a b c h
  obtain ⟨u, hu⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => (ha (Matrix.single i j 1)).symm)
  have hau : (a : Mat3 K) = u • 1 := by
    rw [← hu]
    exact (Matrix.smul_one_eq_diagonal u).symm
  refine ⟨u, c * u, hau, ?_⟩
  rw [hb, hau, smul_smul]

/-- Ternary matrix multiplication is noncommutative over every field. -/
theorem mat3_not_commutative :
    ¬ (∀ X Y : Mat3 K, X * Y = Y * X) := by
  intro h
  have he := congrArg (fun M : Mat3 K => M 0 0)
    (h (Matrix.single 0 1 1) (Matrix.single 1 0 1))
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply] at he

/-- No transpose component acts as a scalar on all matrices. -/
theorem transpose_leftRight_not_scalar (a b : GL3 K) (c : K) :
    ¬ (∀ M : Mat3 K, leftRight a b M.transpose = c • M) := by
  intro h
  have hb : (b : Mat3 K) = c • (a : Mat3 K) := by
    have h1 := congrArg (fun M : Mat3 K => M * (a : Mat3 K)) (h 1)
    simpa [Matrix.mul_assoc, Matrix.smul_mul] using h1
  have hc : c ≠ 0 := by
    intro hc
    have hz : (b : Mat3 K) = 0 := by simpa only [hc, zero_smul] using hb
    have h10 : (1 : Mat3 K) = 0 := by
      simpa [hz] using (Units.inv_mul b).symm
    exact one_ne_zero h10
  have ht (M : Mat3 K) : (a : Mat3 K) * M.transpose * (↑a⁻¹ : Mat3 K) = M := by
    apply smul_right_injective (Mat3 K) hc
    simpa [leftRight_apply, hb, Matrix.smul_mul] using h M
  apply mat3_not_commutative (K := K)
  intro X Y
  calc
    X * Y = (a : Mat3 K) * (X * Y).transpose * (↑a⁻¹ : Mat3 K) := (ht _).symm
    _ = ((a : Mat3 K) * Y.transpose * (↑a⁻¹ : Mat3 K)) *
        ((a : Mat3 K) * X.transpose * (↑a⁻¹ : Mat3 K)) := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Y * X := by rw [ht, ht]

/-- Transposition is not an inner automorphism of the full ternary matrix space. -/
theorem transpose_not_inner (a : GL3 K) :
    ¬ (∀ M : Mat3 K, (a : Mat3 K) * M * (↑a⁻¹ : Mat3 K) = M.transpose) := by
  intro h
  apply transpose_leftRight_not_scalar a a 1
  intro M
  simpa only [leftRight_apply, Matrix.transpose_transpose, one_smul] using h M.transpose

/-- Normal forms for `(G × G) ⋊ C₂`, with `C₂` exchanging the factors. -/
@[ext] structure FrameGroup (G : Type*) where
  first : G
  second : G
  odd : Bool
  deriving DecidableEq

namespace FrameGroup

variable {G : Type*}

/-- The displayed normal forms have the expected product carrier. -/
def normalFormEquiv : FrameGroup G ≃ (G × G) × Bool where
  toFun x := ((x.first,x.second),x.odd)
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype G] : Fintype (FrameGroup G) :=
  Fintype.ofEquiv ((G × G) × Bool) normalFormEquiv.symm

@[simp] theorem card [Fintype G] :
    Fintype.card (FrameGroup G) = Fintype.card G * Fintype.card G * 2 := by
  simpa using Fintype.card_congr (normalFormEquiv (G := G))

variable [Group G]

def frameMul (x y : FrameGroup G) : FrameGroup G :=
  if x.odd then ⟨x.first * y.second, x.second * y.first, !y.odd⟩
  else ⟨x.first * y.first, x.second * y.second, y.odd⟩

def frameInv (x : FrameGroup G) : FrameGroup G :=
  if x.odd then ⟨x.second⁻¹, x.first⁻¹, true⟩
  else ⟨x.first⁻¹, x.second⁻¹, false⟩

instance : Group (FrameGroup G) where
  mul := frameMul
  one := ⟨1, 1, false⟩
  inv := frameInv
  mul_assoc x y z := by
    change frameMul (frameMul x y) z = frameMul x (frameMul y z)
    rcases x with ⟨a,b,o⟩
    rcases y with ⟨a',b',o'⟩
    rcases z with ⟨a'',b'',o''⟩
    cases o <;> cases o' <;> cases o'' <;> simp [frameMul, mul_assoc]
  one_mul x := by
    change frameMul ⟨1,1,false⟩ x = x
    rcases x with ⟨a,b,o⟩
    cases o <;> simp [frameMul]
  mul_one x := by
    change frameMul x ⟨1,1,false⟩ = x
    rcases x with ⟨a,b,o⟩
    cases o <;> simp [frameMul]
  inv_mul_cancel x := by
    change frameMul (frameInv x) x = ⟨1,1,false⟩
    rcases x with ⟨a,b,o⟩
    cases o <;> simp [frameMul, frameInv]

@[simp] theorem one_first : (1 : FrameGroup G).first = 1 := rfl
@[simp] theorem one_second : (1 : FrameGroup G).second = 1 := rfl
@[simp] theorem one_odd : (1 : FrameGroup G).odd = false := rfl

theorem mul_even (a b a' b' : G) (o : Bool) :
    (⟨a,b,false⟩ : FrameGroup G) * ⟨a',b',o⟩ = ⟨a*a',b*b',o⟩ := rfl

theorem mul_odd (a b a' b' : G) (o : Bool) :
    (⟨a,b,true⟩ : FrameGroup G) * ⟨a',b',o⟩ = ⟨a*b',b*a',!o⟩ := rfl

/-- The distinguished transpose involution. -/
def tau : FrameGroup G := ⟨1,1,true⟩

@[simp] theorem tau_squared : tau * tau = (1 : FrameGroup G) := by
  change (⟨1*1,1*1,false⟩ : FrameGroup G) = ⟨1,1,false⟩
  simp

/-- The even subgroup is the pair group. -/
def pairHom : G × G →* FrameGroup G where
  toFun x := ⟨x.1,x.2,false⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The odd generator conjugates by exchanging the factors. -/
theorem tau_pair_tau (a b : G) :
    tau * pairHom (a,b) * tau = pairHom (b,a) := by
  change (⟨1*b*1,1*a*1,false⟩ : FrameGroup G) = ⟨b,a,false⟩
  simp

end FrameGroup

variable {G : Type*} [Group G]

/-- The action of a frame-group normal form on the actual matrix vector space. -/
def frameOperator (ρ : G →* GL3 K) (x : FrameGroup G) : Mat3 K ≃ₗ[K] Mat3 K :=
  leftRight (ρ x.first) (ρ x.second) * if x.odd then transpose else 1

@[simp] theorem frameOperator_even (ρ : G →* GL3 K) (a b : G) :
    frameOperator ρ ⟨a,b,false⟩ = leftRight (ρ a) (ρ b) := by simp [frameOperator]

@[simp] theorem frameOperator_odd (ρ : G →* GL3 K) (a b : G) :
    frameOperator ρ ⟨a,b,true⟩ = leftRight (ρ a) (ρ b) * transpose := by
  simp [frameOperator]

/-- The representation law includes the factor swap in the transpose component. -/
def frameRepresentation (ρ : G →* GL3 K)
    (hOrth : ∀ g, (ρ g : Mat3 K).transpose = (↑(ρ g)⁻¹ : Mat3 K)) :
    FrameGroup G →* (Mat3 K ≃ₗ[K] Mat3 K) where
  toFun := frameOperator ρ
  map_one' := by simp [frameOperator]
  map_mul' x y := by
    rcases x with ⟨a,b,o⟩
    rcases y with ⟨a',b',o'⟩
    cases o <;> cases o'
    · simp [FrameGroup.mul_even, leftRight_mul]
    · simp [FrameGroup.mul_even, leftRight_mul, mul_assoc]
    · simp only [FrameGroup.mul_odd, Bool.not_false, frameOperator_odd,
        frameOperator_even, map_mul, leftRight_mul]
      simp only [mul_assoc]
      rw [transpose_leftRight _ _ (hOrth _) (hOrth _)]
    · simp only [FrameGroup.mul_odd, Bool.not_true, frameOperator_odd,
        frameOperator_even, map_mul, leftRight_mul]
      rw [mul_assoc, ← mul_assoc transpose, transpose_leftRight _ _ (hOrth _) (hOrth _)]
      simp [mul_assoc]

/-- A linear automorphism fixing every projective point is an everywhere scalar map. -/
theorem scalar_of_projectively_trivial (e : Mat3 K ≃ₗ[K] Mat3 K)
    (h : ∀ L : Projectivization K (Mat3 K), e • L = L) :
    ∃ c : K, ∀ M : Mat3 K, e M = c • M := by
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := e.toLinearMap) (fun M => by
      by_cases hM : M = 0
      · subst M
        intro hl
        exact hl.ne_zero 0 (by simp)
      · have hp := h (Projectivization.mk K M hM)
        rw [Projectivization.smul_mk] at hp
        obtain ⟨c, hcv⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hp
        intro hlin
        exact (LinearIndependent.pair_iff' hM).mp hlin c hcv)
  refine ⟨c, fun M => ?_⟩
  exact congrArg (fun f : Module.End K (Mat3 K) => f M) hc

/-- The induced action on actual projective points of the ternary matrix space. -/
def projectiveRepresentation (ρ : G →* GL3 K)
    (hOrth : ∀ g, (ρ g : Mat3 K).transpose = (↑(ρ g)⁻¹ : Mat3 K)) :
    FrameGroup G →* Equiv.Perm (Projectivization K (Mat3 K)) :=
  (MulAction.toPermHom (Mat3 K ≃ₗ[K] Mat3 K) (Projectivization K (Mat3 K))).comp
    (frameRepresentation ρ hOrth)

/-- The same projective representation, expressed as a standard group action. -/
@[instance_reducible] def projectiveAction (ρ : G →* GL3 K)
    (hOrth : ∀ g, (ρ g : Mat3 K).transpose = (↑(ρ g)⁻¹ : Mat3 K)) :
    MulAction (FrameGroup G) (Projectivization K (Mat3 K)) :=
  MulAction.compHom _ (frameRepresentation ρ hOrth)

/-- The projective action is faithful whenever the orthogonal representation has
no nonidentity scalar matrices.  Finiteness is not needed for this algebraic fact. -/
theorem projectiveRepresentation_injective (ρ : G →* GL3 K)
    (hOrth : ∀ g, (ρ g : Mat3 K).transpose = (↑(ρ g)⁻¹ : Mat3 K))
    (hScalar : ∀ g (c : K), (ρ g : Mat3 K) = c • 1 → g = 1) :
    Function.Injective (projectiveRepresentation ρ hOrth) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hfix (L : Projectivization K (Mat3 K)) : frameOperator ρ x • L = L :=
    congrArg (fun f : Equiv.Perm (Projectivization K (Mat3 K)) => f L) hx
  obtain ⟨c, hc⟩ := scalar_of_projectively_trivial (frameOperator ρ x) hfix
  rcases x with ⟨a,b,o⟩
  cases o
  · simp only [frameOperator_even] at hc
    obtain ⟨u,v,hu,hv⟩ := scalar_factors_of_leftRight_scalar (ρ a) (ρ b) c hc
    have ha := hScalar a u hu
    have hb := hScalar b v hv
    subst a
    subst b
    rfl
  · exact (transpose_leftRight_not_scalar (ρ a) (ρ b) c hc).elim

/-- The action is faithful in the standard typeclass sense as well. -/
theorem projectiveAction_faithful (ρ : G →* GL3 K)
    (hOrth : ∀ g, (ρ g : Mat3 K).transpose = (↑(ρ g)⁻¹ : Mat3 K))
    (hScalar : ∀ g (c : K), (ρ g : Mat3 K) = c • 1 → g = 1) :
    let _ := projectiveAction ρ hOrth
    FaithfulSMul (FrameGroup G) (Projectivization K (Mat3 K)) := by
  let _ := projectiveAction ρ hOrth
  refine ⟨fun {x y} hxy => projectiveRepresentation_injective ρ hOrth hScalar ?_⟩
  apply Equiv.ext
  exact hxy

/-- The special orthogonal group maps to the actual invertible matrix group. -/
def so3ToGL : Matrix.specialOrthogonalGroup (Fin 3) K →* GL3 K where
  toFun a :=
    { val := a.val
      inv := a.val.transpose
      val_inv := (Matrix.mem_orthogonalGroup_iff (Fin 3) K).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp a.property).1
      inv_val := (Matrix.mem_orthogonalGroup_iff' (Fin 3) K).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp a.property).1 }
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by apply Units.ext; rfl

@[simp] theorem so3ToGL_coe (a : Matrix.specialOrthogonalGroup (Fin 3) K) :
    (so3ToGL a : Mat3 K) = a.val := rfl

@[simp] theorem so3ToGL_orthogonal (a : Matrix.specialOrthogonalGroup (Fin 3) K) :
    (so3ToGL a : Mat3 K).transpose = (↑(so3ToGL a)⁻¹ : Mat3 K) := rfl

/-- In particular, any scalar-free subgroup of `SO₃` has a faithful projective
frame action.  This includes finite subgroups; no finiteness premise is required. -/
theorem so3_projectiveRepresentation_injective
    (ρ : G →* Matrix.specialOrthogonalGroup (Fin 3) K)
    (hScalar : ∀ g (c : K), (ρ g).val = c • (1 : Mat3 K) → g = 1) :
    Function.Injective
      (projectiveRepresentation (so3ToGL.comp ρ) (fun g => so3ToGL_orthogonal (ρ g))) := by
  apply projectiveRepresentation_injective
  exact hScalar

/-- The inverse transpose, as an actual automorphism of the invertible matrix group. -/
def contragredient : GL3 K →* GL3 K where
  toFun g :=
    { val := (↑g⁻¹ : Mat3 K).transpose
      inv := (g : Mat3 K).transpose
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := by apply Units.ext; simp
  map_mul' g h := by apply Units.ext; simp [Matrix.transpose_mul]

@[simp] theorem contragredient_coe (g : GL3 K) :
    (contragredient g : Mat3 K) = (↑g⁻¹ : Mat3 K).transpose := rfl

/-- The matrix invariant of a pair of invertible frames. -/
def frameInvariant (F H : GL3 K) : Mat3 K := (H : Mat3 K).transpose * (F : Mat3 K)

/-- The connected change of frames `(F,H) ↦ (gF,g⁻ᵀH)`. -/
def changeFrames (g : GL3 K) (FH : GL3 K × GL3 K) : GL3 K × GL3 K :=
  (g * FH.1, contragredient g * FH.2)

/-- `HᵀF` is invariant under the connected frame action. -/
theorem frameInvariant_changeFrames (g F H : GL3 K) :
    frameInvariant (g * F) (contragredient g * H) = frameInvariant F H := by
  simp [frameInvariant, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The fibers of the invariant are exactly the connected frame orbits, on the
actual invertible matrices.  This is the matrix identity underlying the quotient. -/
theorem frameInvariant_eq_iff (F H F' H' : GL3 K) :
    frameInvariant F' H' = frameInvariant F H ↔
      ∃ g : GL3 K, F' = g * F ∧ H' = contragredient g * H := by
  constructor
  · intro h
    refine ⟨F' * F⁻¹, by simp [mul_assoc], ?_⟩
    apply Units.ext
    change (H' : Mat3 K) = (↑((F' * F⁻¹)⁻¹) : Mat3 K).transpose * (H : Mat3 K)
    rw [mul_inv_rev, inv_inv]
    have he := congrArg (fun M : Mat3 K => (M * (↑F'⁻¹ : Mat3 K)).transpose) h
    simpa [frameInvariant, Matrix.transpose_mul, Matrix.mul_assoc] using he
  · rintro ⟨g,rfl,rfl⟩
    exact frameInvariant_changeFrames g F H

/-- Explicitly, changing by `F⁻¹` produces the representative `(I,(HᵀF)ᵀ)`. -/
theorem changeFrames_normalForm (F H : GL3 K) :
    ((changeFrames F⁻¹ (F,H)).1 : Mat3 K) = 1 ∧
      ((changeFrames F⁻¹ (F,H)).2 : Mat3 K) = (frameInvariant F H).transpose := by
  constructor
  · simp [changeFrames]
  · change (↑(F⁻¹)⁻¹ : Mat3 K).transpose * (H : Mat3 K) =
      (frameInvariant F H).transpose
    rw [inv_inv]
    simp [frameInvariant, Matrix.transpose_mul]

/-- The concrete signed-permutation frame group acting in Section 4.2. -/
abbrev TetrahedralFrameGroup := FrameGroup TetrahedralGroup.Gamma

/-- Its actual matrix representation, through the constructed subgroup of `SO₃(ℂ)`. -/
def tetrahedralGL : TetrahedralGroup.Gamma →* GL3 ℂ :=
  so3ToGL.comp TetrahedralGroup.gammaSubgroup.subtype

theorem tetrahedralGL_orthogonal (g : TetrahedralGroup.Gamma) :
    (tetrahedralGL g : Mat3 ℂ).transpose = (↑(tetrahedralGL g)⁻¹ : Mat3 ℂ) := rfl

/-- The concrete even and odd frame operators. -/
def tetrahedralRepresentation : TetrahedralFrameGroup →* (Mat3 ℂ ≃ₗ[ℂ] Mat3 ℂ) :=
  frameRepresentation tetrahedralGL tetrahedralGL_orthogonal

@[simp] theorem tetrahedralRepresentation_even_apply
    (a b : TetrahedralGroup.Gamma) (M : Mat3 ℂ) :
    tetrahedralRepresentation ⟨a,b,false⟩ M =
      TetrahedralGroup.matrix b * M * (TetrahedralGroup.matrix a).transpose := rfl

@[simp] theorem tetrahedralRepresentation_odd_apply
    (a b : TetrahedralGroup.Gamma) (M : Mat3 ℂ) :
    tetrahedralRepresentation ⟨a,b,true⟩ M =
      TetrahedralGroup.matrix b * M.transpose * (TetrahedralGroup.matrix a).transpose := rfl

/-- The actual finite frame-group action on projective ternary matrices. -/
def tetrahedralProjectiveRepresentation :
    TetrahedralFrameGroup →* Equiv.Perm (Projectivization ℂ (Mat3 ℂ)) :=
  projectiveRepresentation tetrahedralGL tetrahedralGL_orthogonal

/-- Faithfulness is instantiated using the proved scalar kernel of the concrete group. -/
theorem tetrahedralProjectiveRepresentation_injective :
    Function.Injective tetrahedralProjectiveRepresentation :=
  projectiveRepresentation_injective tetrahedralGL tetrahedralGL_orthogonal
    TetrahedralGroup.scalar_eq_one

@[simp] theorem card_tetrahedralFrameGroup : Fintype.card TetrahedralFrameGroup = 1152 := by
  rw [FrameGroup.card, TetrahedralGroup.card_gamma]

end M9.FrameAction
