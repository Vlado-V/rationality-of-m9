module

public import M9StacksIntegration.HyperplaneCokernel

/-! The chosen-kernel cokernel comparison retains the actual quotient
diagram. This supplies the normalization needed for the original
hyperplane evaluation and the native zero-scheme quotient. -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace M9Native.HyperplaneCokernelProjection

open HyperplaneCokernel

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {F E L K : C} (q : F ⟶ E) (p : F ⟶ L) [Epi q] [Epi p]

@[reassoc]
theorem chosenKernel_quotient (i : K ⟶ F) (hi : i ≫ q = 0)
    (hK : IsLimit (KernelFork.ofι i hi)) :
    q ≫ cokernel.π (kernel.ι p ≫ q) ≫ (cokernelIsoOfKernel q p i hi hK).hom =
      p ≫ cokernel.π (i ≫ p) := by
  dsimp only [cokernelIsoOfKernel]
  rw [Iso.trans_hom,Iso.trans_hom,Iso.symm_hom,cokernelIso_quotient_assoc,
    cokernelEpiComp_inv,cokernel.π_desc_assoc,π_comp_cokernelIsoOfEq_hom]

end M9Native.HyperplaneCokernelProjection
end
