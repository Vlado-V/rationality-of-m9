module

public import M9.PrimitiveProjectiveStabilizer
public import Mathlib.LinearAlgebra.Center

/-!
# The global projective symplectic action and its literal point stabilizer

The projective symplectic group is the actual six-dimensional symplectic group
modulo the cyclic central sign. The primitive projective action is descended
through this quotient, and its actual stabilizer at `[a+b]` is identified with
the previously proved stabilizer quotient and hence with `SL₃ ⋊ C₂`.
-/

@[expose] public section
noncomputable section
namespace M9.PrimitiveProjectiveAction
open Module ExteriorPrimitive PrimitiveStabilizer
open scoped Classical
variable (K : Type*) [Field K] [CharZero K]

/-- The actual central sign subgroup of the global symplectic group. -/
def globalSigns : Subgroup (Sp6 K) := Subgroup.zpowers (negativeIdentity K)

instance globalSigns_normal : (globalSigns K).Normal := by
  apply Subgroup.normal_of_le_center
  apply Subgroup.zpowers_le.mpr
  exact Subgroup.mem_center_iff.mpr (fun h => (negativeIdentity_central K h).symm)

/-- The actual projective symplectic quotient, before its primitive action is considered. -/
abbrev PSp6 := Sp6 K ⧸ globalSigns K

/-- The canonical quotient of the actual symplectic group by its central sign. -/
def projection : Sp6 K →* PSp6 K := QuotientGroup.mk' (globalSigns K)

/-- The central sign acts trivially on every actual primitive projective point. -/
theorem negativeIdentity_projective :
    projectiveAction K (negativeIdentity K) = 1 := by
  apply Equiv.Perm.ext
  intro L
  induction L using Projectivization.ind with
  | h r hr =>
    change primitiveRepresentation K (negativeIdentity K) • Projectivization.mk K r hr =
      Projectivization.mk K r hr
    rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff]
    refine ⟨(-1 : Kˣ),?_⟩
    apply Subtype.ext
    change (-1 : K) • r.val = exteriorAction K (negativeIdentity K) r.val
    rw [exteriorAction_negativeIdentity]
    change (-1 : K) • r.val = -r.val
    exact neg_one_smul K r.val

theorem globalSigns_le_projective_kernel : globalSigns K ≤ (projectiveAction K).ker := by
  apply Subgroup.zpowers_le.mpr
  exact negativeIdentity_projective K

/-- The actual primitive projective action of the actual global quotient group. -/
def primitiveAction : PSp6 K →* Equiv.Perm (Projectivization K (Primitive K)) :=
  QuotientGroup.lift (globalSigns K) (projectiveAction K) (globalSigns_le_projective_kernel K)

@[simp] theorem primitiveAction_projection (h : Sp6 K) :
    primitiveAction K (projection K h) = projectiveAction K h := rfl

/-- The literal point stabilizer inside the descended global projective action. -/
def pointStabilizer : Subgroup (PSp6 K) :=
  (MulAction.stabilizer (Equiv.Perm (Projectivization K (Primitive K))) (rhoProjective K)).comap
    (primitiveAction K)

@[simp] theorem projection_mem_pointStabilizer (h : Sp6 K) :
    projection K h ∈ pointStabilizer K ↔ h ∈ lineStabilizer K := Iff.rfl

/-- Projection from the actual linear stabilizer to the actual projective point stabilizer. -/
def stabilizerProjection : lineStabilizer K →* pointStabilizer K where
  toFun h := ⟨projection K h.val,(projection_mem_pointStabilizer K h.val).mpr h.property⟩
  map_one' := Subtype.ext (projection K).map_one
  map_mul' h g := Subtype.ext ((projection K).map_mul h.val g.val)

theorem stabilizerProjection_surjective : Function.Surjective (stabilizerProjection K) := by
  intro h
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (globalSigns K) h.val
  have hg' : projection K g = h.val := hg
  have hfix : g ∈ lineStabilizer K := (projection_mem_pointStabilizer K g).mp (hg' ▸ h.property)
  exact ⟨⟨g,hfix⟩,Subtype.ext hg'⟩

/-- The actual global sign subgroup is the image of the actual stabilizer's sign subgroup. -/
theorem map_stabilizerSigns :
    (PrimitiveProjectiveStabilizer.centralSignSubgroup K).map (lineStabilizer K).subtype =
      globalSigns K := by
  rw [MonoidHom.map_zpowers]
  rfl

/-- The projection kernel is exactly the cyclic subgroup of the actual central sign. -/
theorem stabilizerProjection_kernel : (stabilizerProjection K).ker =
    PrimitiveProjectiveStabilizer.centralSignSubgroup K := by
  have hker : (stabilizerProjection K).ker = (globalSigns K).comap (lineStabilizer K).subtype := by
    ext h
    change stabilizerProjection K h = 1 ↔ h.val ∈ globalSigns K
    rw [Subtype.ext_iff]
    change projection K h.val = 1 ↔ h.val ∈ globalSigns K
    exact QuotientGroup.eq_one_iff _
  rw [hker,← map_stabilizerSigns K,
    Subgroup.comap_map_eq_self_of_injective (lineStabilizer K).subtype_injective]

/-- The literal stabilizer in the global PSp action is the actual linear stabilizer modulo sign. -/
def stabilizerQuotientEquiv : PrimitiveProjectiveStabilizer.projectiveLineStabilizer K ≃*
    pointStabilizer K :=
  QuotientGroup.liftEquiv (PrimitiveProjectiveStabilizer.centralSignSubgroup K)
    (stabilizerProjection_surjective K) (stabilizerProjection_kernel K).symm

@[simp] theorem stabilizerQuotientEquiv_mk (h : lineStabilizer K) :
    stabilizerQuotientEquiv K
      (QuotientGroup.mk' (PrimitiveProjectiveStabilizer.centralSignSubgroup K) h) =
      stabilizerProjection K h := rfl

/-- The literal stabilizer of `[a+b]` in the actual global projective symplectic action
is the genuine semidirect product from the manuscript. -/
def actualStabilizerEquiv (i : K) (hi : i^2 = -1) :
    pointStabilizer K ≃* PrimitiveProjectiveStabilizer.specialLinearSemidirect K :=
  (stabilizerQuotientEquiv K).symm.trans
    (PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv K i hi)

/-- The completely concrete complex stabilizer isomorphism. -/
def complexActualStabilizerEquiv : pointStabilizer ℂ ≃*
    PrimitiveProjectiveStabilizer.specialLinearSemidirect ℂ :=
  actualStabilizerEquiv ℂ Complex.I (by simp)

/-- The actual projective action on the original six-dimensional vector space. -/
def vectorProjectiveRepresentation : Sp6 K →* Equiv.Perm (Projectivization K (V K)) :=
  (MulAction.toPermHom (V K ≃ₗ[K] V K) (Projectivization K (V K))).comp (symplecticGroup K).subtype

/-- The global sign acts trivially on the original projective vector space. -/
theorem negativeIdentity_vectorProjective : vectorProjectiveRepresentation K (negativeIdentity K)=1 := by
  apply Equiv.Perm.ext
  intro L
  induction L using Projectivization.ind with
  | h v hv =>
    change (negativeIdentity K).val • Projectivization.mk K v hv = Projectivization.mk K v hv
    rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff]
    refine ⟨(-1 : Kˣ),?_⟩
    change (-1 : K) • v = -v
    exact neg_one_smul K v

/-- A linear transformation fixing every actual projective point is scalar. -/
theorem scalar_of_projectively_trivial (h : V K ≃ₗ[K] V K)
    (hh : ∀ L : Projectivization K (V K), h • L=L) :
    ∃ c : K, ∀ v : V K, h v=c • v := by
  obtain ⟨c,hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := h.toLinearMap) (fun v => by
      by_cases hv : v=0
      · subst v
        intro hlin
        exact hlin.ne_zero 0 (by simp)
      · have hp := hh (Projectivization.mk K v hv)
        rw [Projectivization.smul_mk] at hp
        obtain ⟨c,hcv⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hp
        intro hlin
        exact (LinearIndependent.pair_iff' hv).mp hlin c hcv)
  refine ⟨c,fun v => ?_⟩
  exact congrArg (fun f : Module.End K (V K) => f v) hc

/-- The kernel of the original projective symplectic representation is exactly the sign subgroup. -/
theorem vectorProjectiveRepresentation_kernel :
    (vectorProjectiveRepresentation K).ker = globalSigns K := by
  apply le_antisymm
  · intro h hh
    have hrep : vectorProjectiveRepresentation K h=1 := hh
    have hfix : ∀ L : Projectivization K (V K), h.val • L=L := by
      intro L
      exact congrArg (fun p : Equiv.Perm (Projectivization K (V K)) => p L) hrep
    obtain ⟨c,hc⟩ := scalar_of_projectively_trivial K h.val hfix
    have hs := sp6_omega K h (e K 0) (f K 0)
    rw [hc,hc] at hs
    simp only [map_smul,LinearMap.smul_apply,omega_e_f,ite_true,smul_eq_mul,mul_one] at hs
    have hc2 : c^2=1 := by simpa only [pow_two] using hs
    have hf : (c-1)*(c+1)=0 := by
      calc
        _ = c^2-1 := by ring
        _ = 0 := by rw [hc2,sub_self]
    rcases mul_eq_zero.mp hf with hp | hm
    · have hc1 : c=1 := sub_eq_zero.mp hp
      have he : h=1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        change h.val v=v
        simpa only [hc1,one_smul] using hc v
      rw [he]
      exact Subgroup.one_mem _
    · have hc1 : c= -1 := add_eq_zero_iff_eq_neg.mp hm
      have he : h=negativeIdentity K := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        change h.val v = -v
        rw [hc,hc1,neg_one_smul]
      rw [he]
      exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    exact negativeIdentity_vectorProjective K

/-- The actual six-dimensional projective action of PSp. -/
def vectorAction : PSp6 K →* Equiv.Perm (Projectivization K (V K)) :=
  QuotientGroup.lift (globalSigns K) (vectorProjectiveRepresentation K)
    (vectorProjectiveRepresentation_kernel K).ge

/-- Thus the global quotient is genuinely the projective symplectic group: its original
six-dimensional projective representation is faithful. -/
theorem vectorAction_injective : Function.Injective (vectorAction K) :=
  (QuotientGroup.injective_lift_iff (globalSigns K) (vectorProjectiveRepresentation K)
    (vectorProjectiveRepresentation_kernel K).ge).mpr (vectorProjectiveRepresentation_kernel K).symm

@[simp] theorem stabilizerQuotientEquiv_symm_projection (h : lineStabilizer K) :
    (stabilizerQuotientEquiv K).symm (stabilizerProjection K h) =
      QuotientGroup.mk' (PrimitiveProjectiveStabilizer.centralSignSubgroup K) h := by
  apply (stabilizerQuotientEquiv K).injective
  rw [MulEquiv.apply_symm_apply,stabilizerQuotientEquiv_mk]

/-- Connected blocks correspond to the actual connected factor of the literal point stabilizer. -/
@[simp] theorem actualStabilizerEquiv_block (i : K) (hi : i^2 = -1)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    actualStabilizerEquiv K i hi (stabilizerProjection K (blockStabilizerHom K g)) =
      SemidirectProduct.inl g := by
  simp only [actualStabilizerEquiv,MulEquiv.trans_apply,stabilizerQuotientEquiv_symm_projection,
    PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv_block]

/-- The actual exchanging lift becomes the involution in the literal projective point stabilizer. -/
@[simp] theorem actualStabilizerEquiv_swapping (i : K) (hi : i^2 = -1) :
    actualStabilizerEquiv K i hi (stabilizerProjection K (swappingElement K i hi)) =
      SemidirectProduct.inr CentralSignQuotient.epsilon := by
  simp only [actualStabilizerEquiv,MulEquiv.trans_apply,stabilizerQuotientEquiv_symm_projection,
    PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv_swapping]

end M9.PrimitiveProjectiveAction
