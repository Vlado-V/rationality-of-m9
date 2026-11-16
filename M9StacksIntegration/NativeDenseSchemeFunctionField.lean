module

public import M9StacksIntegration.AlgebraicSpaceDenseSchemeFunctionField
public import M9StacksIntegration.NativeDenseAffineVariety

@[expose] public section

/-! The genuine dense affine chart and its actual structural function-field
comparison are produced together from native integral finite-type geometry.
Neither a chart, its integrality, nor a function-field identification is
supplied as a premise. Native integrality remains a genuine geometric input;
this is not a theorem asserting integrality or rationality of M9. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
attribute [local instance] Space.pointTopology

namespace M9Native.NativeDenseSchemeFunctionField

open AlgebraicSpaceDenseSchemeFunctionField
  M9StacksIntegration.AllTestNativeOriginalPullbacks

universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Genuine native integrality and local finite type produce the SAME-site
affine integral dense chart, its literal all-original-test dense-open map,
and an original-field algebra equivalence with its actual generic stalk. -/
theorem exists_dense_affine_chart_with_functionField
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hInt : Space.IsIntegralSpace B (Spec (.of K)) hK X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from X.obj)) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK) (j : yoneda.obj U ⟶ X.obj)
      (hU : IsIntegral (chartScheme K B hK U)),
      IsAffine (chartScheme K B hK U) ∧
      IsSeparated (chartStructureMap K B hK U) ∧
      LocallyOfFiniteType (chartStructureMap K B hK U) ∧
      QuasiCompact (chartStructureMap K B hK U) ∧
      Space.IsOpenImmersion B (Spec (.of K)) hK j ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) j) ∧
      M9StandaloneDraft.DenseOpen K (originalChart K B hK X U j) ∧
      (letI := hU
       letI := Space.functionField B (Spec (.of K)) hK X.property hInt
       letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra
         K B hK X.property hInt
       letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
       Nonempty (Space.rationalFunctions B (Spec (.of K)) hK X.property ≃ₐ[K]
         (chartScheme K B hK U).functionField)) := by
  obtain ⟨U, j, hA, hU, hs, hf, hq, hj, hd, hdo⟩ :=
    M9StacksIntegration.NativeDenseAffineVariety.exists_original_dense_affine_chart
      K B hK X hInt hft
  let : IsIntegral (chartScheme K B hK U) := hU
  exact ⟨U, j, hU, hA, hs, hf, hq, hj, hd, hdo,
    ⟨functionFieldAlgEquiv K B hK X.property hInt U j hj hd⟩⟩

end M9Native.NativeDenseSchemeFunctionField
