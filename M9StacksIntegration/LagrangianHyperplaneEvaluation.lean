module

public import M9StacksIntegration.SymplecticQuotientEvaluation
public import M9StacksIntegration.LagrangianUniversalSections
public import M9StacksIntegration.SectionZeroCokernelCohomology

/-! The original symplectic hyperplane evaluation and its native
section-zero scheme. All objects use the original six-space, quotient,
structural coefficients, and symplectic functional. No cokernel or
support identification is a definition or an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianHyperplaneEvaluation

open LagrangianMatrixChart LagrangianUniversalSections

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (l : X ⟶ LagrangianGrassmannian.space k) (v : Fin 6 → k)

theorem original_quotient_epi : Epi (quotientMap k l) :=
  (LagrangianUniversalSections.quotient k l).map_epi

theorem bundle_finiteLocallyFree : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (bundle k l) :=
  (bundle_rank k l).isFiniteLocallyFree

attribute [local instance] bundle_finiteLocallyFree

abbrev originalSection : Γ(bundle k l,⊤) :=
  (quotientMap k l).app ⊤ (constantVector k f v)

abbrev omegaMap : freeOn X 6 ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SymplecticQuotientEvaluation.omegaFunctional (constantVector k f v)

/-- The canonical hyperplane subsheaf for the original functional
omega(v,-), before restricting the original quotient to it. -/
abbrev hyperplaneSheaf : X.Modules := kernel (C := X.Modules) (omegaMap k f v)

abbrev hyperplaneEvaluation : hyperplaneSheaf k f v ⟶ bundle k l :=
  kernel.ι (C := X.Modules) (omegaMap k f v) ≫ quotientMap k l

abbrev hyperplaneCokernel : X.Modules := cokernel (C := X.Modules) (hyperplaneEvaluation k f l v)

/-- The full original native zero ideal of q(v), retaining multiplicities. -/
abbrev zeroIdeal : X.IdealSheafData :=
  Stacks.Chow.zeroSchemeOfSection X (bundle k l) (originalSection k f l v)

abbrev zeroProjection : (zeroIdeal k f l v).subscheme ⟶ Spec (.of k) :=
  (zeroIdeal k f l v).subschemeι ≫ f

end M9Native.LagrangianHyperplaneEvaluation
end
