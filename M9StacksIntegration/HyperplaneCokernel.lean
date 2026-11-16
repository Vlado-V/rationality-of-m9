module

public import Mathlib.CategoryTheory.Abelian.Basic

/-! Cokernels of a quotient restricted to the kernel of another
quotient. The comparison follows from the actual two quotient maps and
their categorical kernels, rather than a supplied cokernel comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace M9Native.HyperplaneCokernel

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {F E L : C} (q : F ⟶ E) (p : F ⟶ L) [Epi q] [Epi p]

abbrev restrictedMap : kernel p ⟶ E := kernel.ι p ≫ q

def comparisonHom : cokernel (restrictedMap q p) ⟶ cokernel (restrictedMap p q) :=
  cokernel.desc (restrictedMap q p)
    (Abelian.epiDesc q (p ≫ cokernel.π (restrictedMap p q)) (by
      simpa only [← Category.assoc,restrictedMap] using cokernel.condition (restrictedMap p q)))
    (by
      dsimp only [restrictedMap]
      rw [Category.assoc,Abelian.comp_epiDesc,← Category.assoc,kernel.condition,zero_comp])

omit [Epi p] in
@[reassoc]
theorem quotient_comparisonHom :
    q ≫ cokernel.π (restrictedMap q p) ≫ comparisonHom q p =
      p ≫ cokernel.π (restrictedMap p q) := by
  simp only [comparisonHom,cokernel.π_desc,Abelian.comp_epiDesc]

theorem comparisonHom_comp :
    comparisonHom q p ≫ comparisonHom p q = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (restrictedMap q p))).mp
  apply (cancel_epi q).mp
  simp only [Category.comp_id]
  rw [quotient_comparisonHom_assoc,quotient_comparisonHom]

/-- The two actual cokernels are canonically isomorphic. -/
def cokernelIso : cokernel (kernel.ι p ≫ q) ≅ cokernel (kernel.ι q ≫ p) where
  hom := comparisonHom q p
  inv := comparisonHom p q
  hom_inv_id := comparisonHom_comp q p
  inv_hom_id := comparisonHom_comp p q

@[reassoc]
theorem cokernelIso_quotient :
    q ≫ cokernel.π (kernel.ι p ≫ q) ≫ (cokernelIso q p).hom =
      p ≫ cokernel.π (kernel.ι q ≫ p) :=
  quotient_comparisonHom q p

/-- The same comparison for any proved kernel presentation of the
first quotient, rather than a particular chosen kernel object. -/
def cokernelIsoOfKernel {K : C} (i : K ⟶ F) (hi : i ≫ q = 0)
    (hK : IsLimit (KernelFork.ofι i hi)) :
    cokernel (kernel.ι p ≫ q) ≅ cokernel (i ≫ p) := by
  let e : K ≅ kernel q := hK.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ kernel.ι q = i :=
    hK.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  exact cokernelIso q p ≪≫
    (cokernelEpiComp e.hom (kernel.ι q ≫ p)).symm ≪≫
      cokernelIsoOfEq (by rw [← Category.assoc,he])

end M9Native.HyperplaneCokernel
end
