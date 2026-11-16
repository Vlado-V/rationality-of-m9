module

public import M9.ExteriorPrimitive
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! The actual volume-contraction endomorphism of a three-vector. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.PrimitiveEndomorphism

open Module exteriorPower

section GeneralContraction

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Interior multiplication by a covector on the genuine exterior algebra. -/
abbrev interior (α : Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) α

theorem interior_ι_mul (α : Dual R M) (v : M) (x : ExteriorAlgebra R M) :
    interior α (ExteriorAlgebra.ι R v*x)=α v • x-ExteriorAlgebra.ι R v*interior α x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/-- Interior multiplication lowers the actual homogeneous exterior degree. -/
theorem interior_mem (α : Dual R M) (n : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^(n+1) M) : interior α x ∈ ⋀[R]^n M := by
  induction n generalizing x with
  | zero =>
    change x ∈ (LinearMap.range (ExteriorAlgebra.ι R))^1 at hx
    rw [pow_one] at hx
    obtain ⟨v,rfl⟩ := hx
    rw [CliffordAlgebra.contractLeft_ι]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    change x ∈ (LinearMap.range (ExteriorAlgebra.ι R))^(n+1+1) at hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro z hz y hy
      obtain ⟨v,rfl⟩ := hz
      rw [interior_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ hy
      · change ExteriorAlgebra.ι R v*interior α y ∈ (LinearMap.range (ExteriorAlgebra.ι R))^(n+1)
        rw [pow_succ']
        exact Submodule.mul_mem_mul ⟨v,rfl⟩ (ih hy)
    · intro z y hz hy
      rw [map_add]
      exact Submodule.add_mem _ hz hy

/-- Naturality of actual interior multiplication under any linear map. -/
theorem interior_map (f : M →ₗ[R] N) (α : Dual R N) (x : ExteriorAlgebra R M) :
    interior α (ExteriorAlgebra.map f x)=
      ExteriorAlgebra.map f (interior (α.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes,interior,CliffordAlgebra.contractLeft_algebraMap,map_zero]
  | add x y hx hy =>
    simp only [map_add,hx,hy]
  | ι_mul v x hx =>
    simp only [map_mul,ExteriorAlgebra.map_apply_ι,interior_ι_mul,
      map_sub,map_smul,LinearMap.comp_apply,hx]

/-- Interior multiplication restricted to homogeneous exterior powers. -/
def interiorPower (n : ℕ) : Dual R M →ₗ[R] (⋀[R]^(n+1) M) →ₗ[R] ⋀[R]^n M where
  toFun α := (interior α).domRestrict (⋀[R]^(n+1) M) |>.codRestrict (⋀[R]^n M)
    (fun x => interior_mem α n x.property)
  map_add' α β := by ext x; simp [interior,LinearMap.add_apply]
  map_smul' a α := by ext x; simp [interior]

@[simp] theorem interiorPower_val (n : ℕ) (α : Dual R M) (x : ⋀[R]^(n+1) M) :
    (interiorPower n α x : ExteriorAlgebra R M)=interior α (x : ExteriorAlgebra R M) := rfl

end GeneralContraction

section SixDimensions

variable (K : Type*) [Field K]

abbrev V := ExteriorPrimitive.V K
abbrev EA := ExteriorAlgebra K (V K)
abbrev Third := ExteriorPrimitive.Third K
abbrev Fifth := ⋀[K]^5 (V K)
abbrev Sixth := ⋀[K]^6 (V K)

theorem seventh_eq_zero (x : ⋀[K]^7 (V K)) : x=0 := by
  have hdim : finrank K (⋀[K]^7 (V K))=0 := by
    rw [exteriorPower.finrank_eq]
    norm_num [V,ExteriorPrimitive.V,Module.finrank_pi]
  have : Subsingleton (⋀[K]^7 (V K)) := Module.finrank_zero_iff.mp hdim
  exact Subsingleton.elim _ _

theorem vector_mul_sixth_eq_zero (v : V K) (vol : Sixth K) :
    ExteriorAlgebra.ι K v*(vol : EA K)=0 := by
  have hm : ExteriorAlgebra.ι K v*(vol : EA K) ∈ ⋀[K]^7 (V K) := by
    change ExteriorAlgebra.ι K v*(vol : EA K) ∈
      (LinearMap.range (ExteriorAlgebra.ι K))^(6+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul ⟨v,rfl⟩ vol.property
  exact congrArg Subtype.val (seventh_eq_zero K ⟨_,hm⟩)

/-- The elementary volume identity is proved from contraction of a zero
seven-vector, rather than imposed as a duality assumption. -/
theorem vector_mul_interior_volume (α : Dual K (V K)) (v : V K) (vol : Sixth K) :
    ExteriorAlgebra.ι K v*interior α (vol : EA K)=α v • (vol : EA K) := by
  have h := congrArg (interior α) (vector_mul_sixth_eq_zero K v vol)
  rw [interior_ι_mul,map_zero,sub_eq_zero] at h
  exact h.symm

/-- Actual contraction against a chosen top-degree volume. -/
def volumeContraction (vol : Sixth K) : Dual K (V K) →ₗ[K] Fifth K :=
  (LinearMap.applyₗ vol).comp (interiorPower 5)

@[simp] theorem volumeContraction_val (vol : Sixth K) (α : Dual K (V K)) :
    (volumeContraction K vol α : EA K)=interior α (vol : EA K) := rfl

theorem volumeContraction_injective (vol : Sixth K) (hvol : vol ≠ 0) :
    Function.Injective (volumeContraction K vol) := by
  have hvol' : (vol : EA K) ≠ 0 := fun h => hvol (Subtype.ext h)
  intro α β h
  apply LinearMap.ext
  intro v
  apply smul_left_injective K hvol'
  change α v • (vol : EA K)=β v • (vol : EA K)
  rw [← vector_mul_interior_volume K α v vol,← vector_mul_interior_volume K β v vol]
  exact congrArg (fun x : Fifth K => ExteriorAlgebra.ι K v*(x : EA K)) h

/-- The genuine volume-contraction isomorphism `V* ≃ Λ⁵V`. -/
def volumeContractionEquiv (vol : Sixth K) (hvol : vol ≠ 0) :
    Dual K (V K) ≃ₗ[K] Fifth K :=
  LinearEquiv.ofBijective (volumeContraction K vol)
    ⟨volumeContraction_injective K vol hvol,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Subspace.dual_finrank_eq,exteriorPower.finrank_eq]
        norm_num [V,ExteriorPrimitive.V,Module.finrank_pi])).mp
        (volumeContraction_injective K vol hvol)⟩

/-- The defining right side `(ι_αρ)∧ρ`, as an actual linear map in the covector. -/
def contractedSquare (ρ : Third K) : Dual K (V K) →ₗ[K] Fifth K :=
  ((exteriorPower.wedge K (V K) 2 3).flip ρ).comp
    ((LinearMap.applyₗ ρ).comp (interiorPower 2))

@[simp] theorem contractedSquare_val (ρ : Third K) (α : Dual K (V K)) :
    (contractedSquare K ρ α : EA K)=interior α (ρ : EA K)*(ρ : EA K) := rfl

/-- The endomorphism is defined by the inverse of actual volume contraction. -/
def withVolume (vol : Sixth K) (hvol : vol ≠ 0) (ρ : Third K) :
    Module.End K (Dual K (V K)) :=
  (volumeContractionEquiv K vol hvol).symm.toLinearMap.comp (contractedSquare K ρ)

theorem withVolume_spec (vol : Sixth K) (hvol : vol ≠ 0) (ρ : Third K)
    (α : Dual K (V K)) :
    volumeContraction K vol (withVolume K vol hvol ρ α)=contractedSquare K ρ α :=
  (volumeContractionEquiv K vol hvol).apply_symm_apply _

theorem withVolume_spec_ambient (vol : Sixth K) (hvol : vol ≠ 0) (ρ : Third K)
    (α : Dual K (V K)) :
    interior (withVolume K vol hvol ρ α) (vol : EA K)=
      interior α (ρ : EA K)*(ρ : EA K) :=
  congrArg Subtype.val (withVolume_spec K vol hvol ρ α)

theorem withVolume_smul (vol : Sixth K) (hvol : vol ≠ 0) (c : K) (ρ : Third K) :
    withVolume K vol hvol (c • ρ)=c^2 • withVolume K vol hvol ρ := by
  apply LinearMap.ext
  intro α
  apply volumeContraction_injective K vol hvol
  rw [withVolume_spec]
  rw [LinearMap.smul_apply,map_smul,withVolume_spec]
  apply Subtype.ext
  simp only [contractedSquare_val,SetLike.val_smul, map_smul,smul_mul_assoc,mul_smul_comm,
    smul_smul,pow_two]

theorem exteriorMap_injective (h : V K ≃ₗ[K] V K) :
    Function.Injective (ExteriorAlgebra.map h.toLinearMap) := by
  have hi : (ExteriorAlgebra.map h.symm.toLinearMap).comp
      (ExteriorAlgebra.map h.toLinearMap)=AlgHom.id K (EA K) := by
    rw [ExteriorAlgebra.map_comp_map]
    simp
  intro x y hxy
  have h' := congrArg (ExteriorAlgebra.map h.symm.toLinearMap) hxy
  change ((ExteriorAlgebra.map h.symm.toLinearMap).comp
    (ExteriorAlgebra.map h.toLinearMap)) x=
      ((ExteriorAlgebra.map h.symm.toLinearMap).comp
        (ExteriorAlgebra.map h.toLinearMap)) y at h'
  rw [hi] at h'
  exact h'

/-- Covariance in intertwining form for every genuine volume-preserving
linear equivalence. A symplectic transformation can supply volume preservation. -/
theorem withVolume_intertwine (vol : Sixth K) (hvol : vol ≠ 0)
    (h : V K ≃ₗ[K] V K)
    (hpres : ExteriorAlgebra.map h.toLinearMap (vol : EA K)=(vol : EA K))
    (ρ : Third K) (α : Dual K (V K)) :
    h.dualMap (withVolume K vol hvol (exteriorPower.map 3 h.toLinearMap ρ) α)=
      withVolume K vol hvol ρ (h.dualMap α) := by
  apply volumeContraction_injective K vol hvol
  apply Subtype.ext
  apply exteriorMap_injective K h
  let ρ' := exteriorPower.map 3 h.toLinearMap ρ
  change ExteriorAlgebra.map h.toLinearMap
    (interior ((withVolume K vol hvol ρ' α).comp h.toLinearMap) (vol : EA K))=
      ExteriorAlgebra.map h.toLinearMap
        (interior (withVolume K vol hvol ρ (h.dualMap α)) (vol : EA K))
  rw [← interior_map,hpres,withVolume_spec_ambient,withVolume_spec_ambient,map_mul]
  change interior α (ρ' : EA K)*(ρ' : EA K)=
    ExteriorAlgebra.map h.toLinearMap (interior (α.comp h.toLinearMap) (ρ : EA K))*
      ExteriorAlgebra.map h.toLinearMap (ρ : EA K)
  rw [← interior_map]
  simp only [ρ',exteriorPower.coe_map]

/-- The actual conjugation formula `K_(hρ)=h^(-t) K_ρ h^t`. -/
theorem withVolume_naturality (vol : Sixth K) (hvol : vol ≠ 0)
    (h : V K ≃ₗ[K] V K)
    (hpres : ExteriorAlgebra.map h.toLinearMap (vol : EA K)=(vol : EA K))
    (ρ : Third K) (α : Dual K (V K)) :
    withVolume K vol hvol (exteriorPower.map 3 h.toLinearMap ρ) α=
      h.dualMap.symm (withVolume K vol hvol ρ (h.dualMap α)) :=
  h.dualMap.eq_symm_apply.mpr (withVolume_intertwine K vol hvol h hpres ρ α)

theorem orderedVolume_ne_zero : ExteriorPrimitive.volume K ≠ 0 := by
  intro hz
  have h := congrArg (ExteriorPrimitive.volumeCoordinate K) hz
  simp at h

/-- The paper's genuine endomorphism for its ordered split volume. -/
def endomorphism (ρ : Third K) : Module.End K (Dual K (V K)) :=
  withVolume K (ExteriorPrimitive.volume K) (orderedVolume_ne_zero K) ρ

theorem endomorphism_spec (ρ : Third K) (α : Dual K (V K)) :
    interior (endomorphism K ρ α) (ExteriorPrimitive.volume K : EA K)=
      interior α (ρ : EA K)*(ρ : EA K) :=
  withVolume_spec_ambient K _ _ ρ α

theorem endomorphism_smul (c : K) (ρ : Third K) :
    endomorphism K (c • ρ)=c^2 • endomorphism K ρ :=
  withVolume_smul K _ _ c ρ

theorem endomorphism_naturality (h : V K ≃ₗ[K] V K)
    (hpres : ExteriorAlgebra.map h.toLinearMap (ExteriorPrimitive.volume K : EA K)=
      (ExteriorPrimitive.volume K : EA K)) (ρ : Third K) (α : Dual K (V K)) :
    endomorphism K (exteriorPower.map 3 h.toLinearMap ρ) α=
      h.dualMap.symm (endomorphism K ρ (h.dualMap α)) :=
  withVolume_naturality K _ _ h hpres ρ α

def generator (i : Fin 6) : EA K := ExteriorAlgebra.ι K (ExteriorPrimitive.basisVector K i)

theorem generator_swap (i j : Fin 6) (_h : j < i) :
    generator K i*generator K j= -(generator K j*generator K i) := by
  apply eq_neg_of_add_eq_zero_left
  exact ExteriorAlgebra.ι_add_mul_swap _ _

theorem generator_swap_assoc (i j : Fin 6) (x : EA K) (h : j < i) :
    generator K i*(generator K j*x)= -(generator K j*(generator K i*x)) := by
  rw [← mul_assoc,generator_swap K i j h,neg_mul,mul_assoc]

theorem generator_repeat (i : Fin 6) : generator K i*generator K i=0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem generator_repeat_assoc (i : Fin 6) (x : EA K) :
    generator K i*(generator K i*x)=0 := by
  rw [← mul_assoc,generator_repeat,zero_mul]

theorem wedge3_val (u v w : V K) :
    (ExteriorPrimitive.wedge3 K u v w : EA K)=
      ExteriorAlgebra.ι K u*(ExteriorAlgebra.ι K v*ExteriorAlgebra.ι K w) := by
  simp [ExteriorPrimitive.wedge3,ExteriorAlgebra.ιMulti_succ_apply]

theorem a_val : (ExteriorPrimitive.a K : EA K)=generator K 0*(generator K 1*generator K 2) :=
  wedge3_val K _ _ _

theorem b_val : (ExteriorPrimitive.b K : EA K)=generator K 3*(generator K 4*generator K 5) :=
  wedge3_val K _ _ _

theorem orderedVolume_val : (ExteriorPrimitive.volume K : EA K)=
    generator K 0*(generator K 1*(generator K 2*(generator K 3*(generator K 4*generator K 5)))) := by
  rw [ExteriorPrimitive.volume_coe,a_val,b_val]
  simp only [mul_assoc]

theorem orderedVolume_eq_ιMulti : ExteriorPrimitive.volume K=
    exteriorPower.ιMulti K 6 (ExteriorPrimitive.basisVector K) := by
  rw [ExteriorPrimitive.volume,ExteriorPrimitive.a,ExteriorPrimitive.b,ExteriorPrimitive.wedge3,
    ExteriorPrimitive.wedge3,ExteriorPrimitive.wedge_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The ordered volume transforms by the actual linear determinant. -/
theorem volumeCoordinate_map (h : V K →ₗ[K] V K) :
    ExteriorPrimitive.volumeCoordinate K
      (exteriorPower.map 6 h (ExteriorPrimitive.volume K))=LinearMap.det h := by
  rw [orderedVolume_eq_ιMulti,exteriorPower.map_apply_ιMulti]
  simp only [ExteriorPrimitive.volumeCoordinate,exteriorPower.pairingDual_ιMulti_ιMulti,
    Function.comp_apply]
  rw [← LinearMap.det_toMatrix']
  rw [← Matrix.det_transpose]
  congr 1

theorem map_volume_eq_det_smul (h : V K →ₗ[K] V K) :
    exteriorPower.map 6 h (ExteriorPrimitive.volume K)=LinearMap.det h • ExteriorPrimitive.volume K := by
  apply (ExteriorPrimitive.volumeEquiv K).injective
  simp only [ExteriorPrimitive.volumeEquiv_apply,volumeCoordinate_map,map_smul,
    ExteriorPrimitive.volumeCoordinate_volume,smul_eq_mul,mul_one]

/-- The exact volume preservation needed for covariance follows from the
actual determinant-one condition. -/
theorem map_volume_of_det_one (h : V K →ₗ[K] V K) (hdet : LinearMap.det h=1) :
    ExteriorAlgebra.map h (ExteriorPrimitive.volume K : EA K)=
      (ExteriorPrimitive.volume K : EA K) := by
  have hv := map_volume_eq_det_smul K h
  rw [hdet,one_smul] at hv
  simpa only [exteriorPower.coe_map] using congrArg Subtype.val hv

theorem endomorphism_naturality_of_det_one (h : V K ≃ₗ[K] V K)
    (hdet : LinearMap.det h.toLinearMap=1) (ρ : Third K) (α : Dual K (V K)) :
    endomorphism K (exteriorPower.map 3 h.toLinearMap ρ) α=
      h.dualMap.symm (endomorphism K ρ (h.dualMap α)) :=
  endomorphism_naturality K h (map_volume_of_det_one K h.toLinearMap hdet) ρ α

@[simp] theorem interior_generator (i j : Fin 6) :
    interior (LinearMap.proj i : Dual K (V K)) (generator K j)=
      algebraMap K (EA K) (if i=j then 1 else 0) := by
  rw [generator,CliffordAlgebra.contractLeft_ι]
  congr 1
  simp [ExteriorPrimitive.basisVector,Pi.single_apply]

theorem interior_generator_mul (i j : Fin 6) (x : EA K) :
    interior (LinearMap.proj i : Dual K (V K)) (generator K j*x)=
      (if i=j then (1 : K) else 0) • x-generator K j*interior (LinearMap.proj i) x := by
  rw [generator,interior_ι_mul]
  congr 2
  simp [ExteriorPrimitive.basisVector,Pi.single_apply]

def splitSign (i : Fin 6) : K := if i.val<3 then 1 else -1

/-- Coordinate covectors have the two asserted eigenvalues, by a direct
calculation in the genuine exterior algebra. -/
theorem endomorphism_split_proj (i : Fin 6) :
    endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K) (LinearMap.proj i)=
      splitSign K i • (LinearMap.proj i : Dual K (V K)) := by
  apply volumeContraction_injective K (ExteriorPrimitive.volume K) (orderedVolume_ne_zero K)
  rw [endomorphism,withVolume_spec]
  apply Subtype.ext
  change interior (LinearMap.proj i : Dual K (V K))
      ((ExteriorPrimitive.a K : EA K)+(ExteriorPrimitive.b K : EA K))*
      ((ExteriorPrimitive.a K : EA K)+(ExteriorPrimitive.b K : EA K))=
    interior (splitSign K i • (LinearMap.proj i : Dual K (V K)))
      (ExteriorPrimitive.volume K : EA K)
  fin_cases i <;>
    simp [a_val,b_val,splitSign,interior_generator_mul,
      mul_add,mul_assoc,generator_swap_assoc,generator_swap,generator_repeat_assoc,generator_repeat]

theorem dualBasis_eq_proj (i : Fin 6) :
    (Pi.basisFun K (Fin 6)).dualBasis i=(LinearMap.proj i : Dual K (V K)) := by
  apply LinearMap.ext
  intro v
  simp

/-- The actual endomorphism of `a+b` is the claimed split diagonal in the
dual of the ordered symplectic basis. -/
theorem endomorphism_split_matrix :
    LinearMap.toMatrix (Pi.basisFun K (Fin 6)).dualBasis (Pi.basisFun K (Fin 6)).dualBasis
      (endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K))=Matrix.diagonal (splitSign K) := by
  classical
  have heig (j : Fin 6) :
      endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K) ((Pi.basisFun K (Fin 6)).dualBasis j)=
        splitSign K j • (Pi.basisFun K (Fin 6)).dualBasis j := by
    rw [dualBasis_eq_proj]
    exact endomorphism_split_proj K j
  ext i j
  rw [LinearMap.toMatrix_apply,heig]
  by_cases hij : i=j
  · subst j
    simp
  · simp [hij,Ne.symm hij]

theorem splitSign_square (i : Fin 6) : splitSign K i*splitSign K i=1 := by
  unfold splitSign
  split_ifs <;> ring

/-- The genuine split endomorphism is an involution. -/
theorem endomorphism_split_square :
    (endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K)).comp
      (endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K))=LinearMap.id := by
  apply (Pi.basisFun K (Fin 6)).dualBasis.ext
  intro i
  rw [dualBasis_eq_proj]
  change endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K)
    (endomorphism K (ExteriorPrimitive.a K+ExteriorPrimitive.b K) (LinearMap.proj i))=
      (LinearMap.proj i : Dual K (V K))
  rw [endomorphism_split_proj,map_smul,endomorphism_split_proj,smul_smul,splitSign_square,one_smul]

end SixDimensions

end M9.PrimitiveEndomorphism
