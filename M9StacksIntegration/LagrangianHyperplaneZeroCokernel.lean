module

public import M9StacksIntegration.LagrangianHyperplaneEpimorphism
public import M9StacksIntegration.SymplecticQuotientKernel
public import M9StacksIntegration.HyperplaneCokernelProjection

/-! The original symplectic hyperplane evaluation has cokernel the
structure module of the full native zero scheme of the original section
q(v). The true symplectic kernel, epimorphy, zero ideal, and original-field
cohomology comparisons are derived; no identification or length bound
is supplied as an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianHyperplaneZeroCokernel

open LagrangianUniversalSections LagrangianHyperplaneEvaluation
open LagrangianHyperplaneEpimorphism SymplecticQuotientEvaluation

attribute [local instance] LagrangianHyperplaneEvaluation.bundle_finiteLocallyFree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (l : X ⟶ LagrangianGrassmannian.space k)

/-- The actual cokernel comparison uses the proved original universal
symplectic kernel and the actual nonzero-vector functional. -/
def evaluationCokernelIso (v : Fin 6 → k) (hv : v ≠ 0) :
    hyperplaneCokernel k f l v ≅
      cokernel (dualEvalHom (bundle k l) (originalSection k f l v)) := by
  let : Epi (quotientMap k l) := original_quotient_epi k l
  let : Epi (omegaMap k f v) := omegaMap_epi k f v hv
  have hK := SymplecticQuotientKernel.universalDualEmbedding_isKernel k l
  have hi : dualEmbedding (quotientMap k l) ≫ quotientMap k l = 0 :=
    SymplecticIsotropicAnnihilation.dualEmbedding_comp_quotient (bundle k l)
      (quotientMap k l) (LagrangianUniversalSectionInjection.universal_quotient_annihilates k l)
  exact HyperplaneCokernel.cokernelIsoOfKernel (C := X.Modules) (quotientMap k l) (omegaMap k f v)
      (dualEmbedding (quotientMap k l)) hi hK ≪≫
    cokernelIsoOfEq (dualEmbedding_comp_omegaFunctional (quotientMap k l) (constantVector k f v))

/-- The two halves of Mukai II4.4 refer to the same full native zero
scheme, including its nilpotent structure. -/
def cokernelIso (v : Fin 6 → k) (hv : v ≠ 0) :
    hyperplaneCokernel k f l v ≅ SectionZeroCokernel.structureModule (zeroIdeal k f l v) :=
  evaluationCokernelIso k f l v hv ≪≫
    SectionZeroCokernel.evaluationCokernelIso (bundle k l) (originalSection k f l v)

@[reassoc]
theorem cokernelIso_quotient (v : Fin 6 → k) (hv : v ≠ 0) :
    quotientMap k l ≫ cokernel.π (hyperplaneEvaluation k f l v) ≫
      (cokernelIso k f l v hv).hom =
        omegaMap k f v ≫ SectionZeroCokernel.quotientMap (zeroIdeal k f l v) := by
  let : Epi (quotientMap k l) := original_quotient_epi k l
  let : Epi (omegaMap k f v) := omegaMap_epi k f v hv
  dsimp only [cokernelIso,evaluationCokernelIso]
  rw [Iso.trans_hom,Iso.trans_hom,Category.assoc,
    HyperplaneCokernelProjection.chosenKernel_quotient_assoc,
    π_comp_cokernelIsoOfEq_hom_assoc,SectionZeroCokernel.evaluationCokernelIso_projection]

/-- The actual original-field cohomology is that of the same native
section-zero scheme, without a support or length hypothesis. -/
def cohomologyIso (v : Fin 6 → k) (hv : v ≠ 0) (n : ℕ) :
    cohomologyOverField k f (hyperplaneCokernel k f l v) n ≅
      structureSheafCohomology (zeroProjection k f l v) n :=
  cohomologyOverFieldIso k f (evaluationCokernelIso k f l v hv) n ≪≫
    SectionZeroCokernelCohomology.evaluationCohomologyIso k f (bundle k l)
      (originalSection k f l v) n

theorem finrank_hyperplaneCokernel_H0 (v : Fin 6 → k) (hv : v ≠ 0) :
    finrank k (cohomologyOverField k f (hyperplaneCokernel k f l v) 0) =
      finrank k (structureSheafCohomology (zeroProjection k f l v) 0) :=
  (cohomologyIso k f l v hv 0).toLinearEquiv.finrank_eq

end M9Native.LagrangianHyperplaneZeroCokernel
end
