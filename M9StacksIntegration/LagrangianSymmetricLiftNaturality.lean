module

public import StacksFrontier.LinearAlgebra.SymmetricPower.TensorSquareCauchy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification

/-! Actual semilinear naturality of the universal symmetric-square lift. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module
open scoped BigOperators TensorProduct

namespace M9Native.LagrangianSymmetricLiftNaturality

variable {R S : Type*} [CommRing R] [CommRing S]
variable {Q Q' M M' : Type*} [AddCommGroup Q] [Module R Q]
  [AddCommGroup Q'] [Module S Q'] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module S M']

theorem symMapₛₗ_product (ρ : R →+* S) (u : Q →ₛₗ[ρ] Q') (a b : Q) :
    SymPow.symMapₛₗ 2 ρ u
      (SymPow.sqMul (LinearMap.id : Q →ₗ[R] Q) (a ⊗ₜ[R] b))=
      SymPow.sqMul LinearMap.id (u a ⊗ₜ[S] u b) := by
  apply Subtype.ext
  simp only [SymPow.symMapₛₗ_coe,SymPow.sqMul_tmul,LinearMap.id_apply,
    map_mul,SymmetricAlgebra.mapₛₗ_ι]

/-- Every commuting square of actual symmetric bilinear maps induces
the corresponding commuting square of native symmetric powers. -/
theorem sqLift_naturality (ρ : R →+* S) (u : Q →ₛₗ[ρ] Q') (v : M →ₛₗ[ρ] M')
    (B : Q →ₗ[R] Q →ₗ[R] M) (hB : ∀ a b,B a b=B b a)
    (B' : Q' →ₗ[S] Q' →ₗ[S] M') (hB' : ∀ a b,B' a b=B' b a)
    (h : ∀ a b,v (B a b)=B' (u a) (u b))
    (x : SymPow.symmetricPower 2 R Q) :
    v (SymPow.sqLift B hB x)=SymPow.sqLift B' hB' (SymPow.symMapₛₗ 2 ρ u x) := by
  let f : SymPow.symmetricPower 2 R Q →ₛₗ[ρ] M' :=
    { toFun := fun x => v (SymPow.sqLift B hB x)
      map_add' x y := by simp
      map_smul' r x := by simp }
  let g : SymPow.symmetricPower 2 R Q →ₛₗ[ρ] M' :=
    { toFun := fun x => SymPow.sqLift B' hB' (SymPow.symMapₛₗ 2 ρ u x)
      map_add' x y := by simp
      map_smul' r x := by simp }
  have heq : f=g := by
    apply SymPow.ext_of_prod_ι
    intro s
    have hp : (⟨∏ i : Fin 2,SymmetricAlgebra.ι R Q (s i),
        SymmetricAlgebra.prod_ι_mem R s⟩ : SymPow.symmetricPower 2 R Q)=
        SymPow.sqMul LinearMap.id (s 0 ⊗ₜ[R] s 1) := by
      apply Subtype.ext
      simp [Fin.prod_univ_succ,SymPow.sqMul_tmul]
    rw [hp]
    change v (SymPow.sqLift B hB _)=SymPow.sqLift B' hB' (SymPow.symMapₛₗ 2 ρ u _)
    rw [symMapₛₗ_product,SymPow.sqLift_sqMul_tmul,SymPow.sqLift_sqMul_tmul]
    exact h _ _
  exact LinearMap.congr_fun heq x

end M9Native.LagrangianSymmetricLiftNaturality
