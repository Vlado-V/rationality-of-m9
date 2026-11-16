module

public import M9StacksIntegration.SectionZeroCokernel
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison

/-! Original-field cohomology of the actual evaluation cokernel is
the structure-sheaf cohomology of the same native section-zero scheme.
No finite, reduced, support or length comparison hypothesis is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.SectionZeroCokernelCohomology

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E,⊤))

def evaluationCohomologyIso (n : ℕ) :
    cohomologyOverField k f (cokernel (dualEvalHom E s)) n ≅
      structureSheafCohomology ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f) n :=
  cohomologyOverFieldIso k f (SectionZeroCokernel.evaluationCokernelIso E s) n ≪≫
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k
      (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι f
      (SheafOfModules.unit (Stacks.Chow.zeroSchemeOfSection X E s).subscheme.ringCatSheaf) n).symm ≪≫
    (structureSheafCohomologyIsoCohomologyOverField k
      ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f) n).symm

theorem finrank_evaluationCokernel_H0 :
    finrank k (cohomologyOverField k f (cokernel (dualEvalHom E s)) 0) =
      finrank k (structureSheafCohomology
        ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f) 0) :=
  (evaluationCohomologyIso k f E s 0).toLinearEquiv.finrank_eq

end M9Native.SectionZeroCokernelCohomology
end
