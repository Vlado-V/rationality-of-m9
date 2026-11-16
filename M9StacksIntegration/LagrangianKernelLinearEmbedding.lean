module

public import M9StacksIntegration.LagrangianCommonKernelSpan
public import M9StacksIntegration.LagrangianPluckerLinear

/-!
# The actual closed P4 inside the original primitive P13

The coordinate-form map is restriction to the actual original five-space
inside the actual primitive exterior kernel. Injectivity of that inclusion
proves surjectivity on forms. The symmetric-algebra map and its native Proj
map therefore give a genuine closed linear embedding, with literal original
primitive-basis coefficient formulas.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.LagrangianKernelLinearEmbedding

open LagrangianField LagrangianCommonKernelSpan

variable (k : Type u) [Field k] [CharZero k]

/-- The actual original five-space, included in the actual primitive exterior kernel. -/
def inclusionFive : (Fin 5 → k) →ₗ[k] Primitive k :=
  (primitiveEquiv k).toLinearMap.comp (LagrangianCommonKernelSpan.embedding k)

theorem inclusionFive_injective : Function.Injective (inclusionFive k) :=
  (primitiveEquiv k).injective.comp (LagrangianCommonKernelSpan.embedding_injective k)

/-- Restriction of genuine primitive coordinate forms, in the original five-coordinate basis. -/
def restrictionToFive : Module.Dual k (Primitive k) →ₗ[k] (Fin 5 → k) :=
  (Pi.basisFun k (Fin 5)).toDualEquiv.symm.toLinearMap.comp (inclusionFive k).dualMap

theorem restrictionToFive_apply (ell : Module.Dual k (Primitive k)) (a : Fin 5) :
    restrictionToFive k ell a = ell (inclusionFive k (Pi.single a 1)) := by
  have h := congrArg (fun e : Module.Dual k (Fin 5 → k) => e (Pi.basisFun k (Fin 5) a))
    ((Pi.basisFun k (Fin 5)).toDualEquiv.apply_symm_apply ((inclusionFive k).dualMap ell))
  simp only [Basis.toDualEquiv_apply, Basis.toDual_apply_left] at h
  simpa only [restrictionToFive, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Pi.basisFun_repr, Pi.basisFun_apply,
    LinearMap.dualMap_apply] using h

theorem restrictionToFive_surjective : Function.Surjective (restrictionToFive k) := by
  have h : Function.Surjective (inclusionFive k).dualMap :=
    @LinearMap.dualMap_surjective_of_injective k (Fin 5 → k) (Primitive k)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (inclusionFive k) (inclusionFive_injective k)
  exact (Pi.basisFun k (Fin 5)).toDualEquiv.symm.surjective.comp h

/-- The exact coefficients of the original primitive determinant forms. -/
theorem restrictionToFive_basis (j : Fin 14) (a : Fin 5) :
    restrictionToFive k ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j) a =
      embeddingFourteen k (Pi.single a 1) j := by
  rw [restrictionToFive_apply, Basis.dualBasis_apply]
  simp only [LagrangianPluckerLinear.primitiveBasis14, inclusionFive, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Basis.map_repr, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, embeddingFourteen, Basis.equivFun_apply]

abbrev gradedHom := SymPow.gradedSymAlgMap (restrictionToFive k)

theorem gradedHom_surjective : Function.Surjective (gradedHom k) :=
  SymPow.symAlgMap_surjective (restrictionToFive k) (restrictionToFive_surjective k)

/-- The actual native Proj map of the proved surjection on primitive forms. -/
def linearEmbedding : projectiveSpaceOfModule k (Fin 5 → k) ⟶
    projectiveSpaceOfModule k (Module.Dual k (Primitive k)) :=
  Proj.map (gradedHom k) (Proj.irrelevant_le_map_of_surjective _ (gradedHom_surjective k))

theorem linearEmbedding_isClosedImmersion : IsClosedImmersion (linearEmbedding k) :=
  Proj.isClosedImmersion_map_of_surjective' _ (gradedHom_surjective k)

/-- The actual P4-to-original-P13 map, using the actual native basis isomorphisms. -/
def fixedLinearEmbedding : projectiveSpaceOver 4 (Spec (.of k)) ⟶
    projectiveSpaceOver 13 (Spec (.of k)) :=
  (basisProjectiveSpaceIso (Pi.basisFun k (Fin 5))).hom ≫ linearEmbedding k ≫
    (LagrangianPluckerLinear.primitiveProjectiveIso k).inv

theorem fixedLinearEmbedding_isClosedImmersion : IsClosedImmersion (fixedLinearEmbedding k) := by
  letI := linearEmbedding_isClosedImmersion k
  dsimp [fixedLinearEmbedding]
  infer_instance

end M9Native.LagrangianKernelLinearEmbedding
