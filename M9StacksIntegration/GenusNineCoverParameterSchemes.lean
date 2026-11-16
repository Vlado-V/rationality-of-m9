module

public import M9StacksIntegration.GenusNineGroundFieldPolarizedModels
public import M9StacksIntegration.ConstantProjectiveLinePolarization
public import M9StacksIntegration.PolarizedCurveCoverScheme

/-! Actual fixed-degree cover parameter schemes of the constructed
finite affine genus-nine source models. Both original polarizations,
the native graph locus, and the finite-type maps are constructed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GenusNineCoverParameterSchemes

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K))) {m : ℕ}
  (D : GenusNineGroundFieldPolarizedModels.Model.{u} K m)

abbrev sourceContained : B.Contains D.total := D.total_contains B hK
abbrev parameterContained : B.Contains D.parameter := D.parameter_contains B hK
abbrev target : Scheme.{u} := ConstantProjectiveLinePolarization.target K D.structureMap
abbrev targetProjection : target K D ⟶ D.parameter :=
  ConstantProjectiveLinePolarization.projection K D.structureMap
abbrev targetContained : B.Contains (target K D) :=
  ConstantProjectiveLinePolarization.target_contains K D.structureMap B (parameterContained K B hK D)
abbrev targetLine : (target K D).Modules :=
  ConstantProjectiveLinePolarization.targetLine K D.structureMap

abbrev sourceSite := PolarizedCurveCoverScheme.sourceSite B (sourceContained K B hK D)
abbrev targetSite := PolarizedCurveCoverScheme.targetSite B (targetContained K B hK D)
abbrev baseSite := PolarizedCurveCoverScheme.baseSite B (parameterContained K B hK D)
abbrev sourceMap := PolarizedCurveCoverScheme.sourceMap B (sourceContained K B hK D)
  (parameterContained K B hK D) D.projection
abbrev targetMap := PolarizedCurveCoverScheme.targetMap B (targetContained K B hK D)
  (parameterContained K B hK D) (targetProjection K D)

abbrev locus (d : ℕ) :=
  PolarizedCurveCoverScheme.coverLocus B (sourceContained K B hK D) (targetContained K B hK D)
    (parameterContained K B hK D) D.projection (targetProjection K D) D.line (targetLine K D) d

abbrev projection (d : ℕ) :=
  PolarizedCurveCoverScheme.coverProjection B (sourceContained K B hK D) (targetContained K B hK D)
    (parameterContained K B hK D) D.projection (targetProjection K D) D.line (targetLine K D) d

/-- Each actual affine genus-nine polarized source has five actual
finite-type scheme parameter spaces for the true graph polynomials. -/
theorem exists_five_parameterSchemes :
    ∃ (Y : Fin 5 → BigFppfOver B integerBase (B.contains_integerBase))
      (A : ∀ i, yoneda.obj (Y i) ⟶
        (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).toFunctor)
      (q : ∀ i, Y i ⟶ baseSite K B hK D),
      (∀ i, IsIso (A i)) ∧
      (∀ i, A i ≫ projection K B hK D
        (BoundedPencilGraphPolynomial.degreeIndex i) = yoneda.map (q i)) ∧
      (∀ i, Space.QuasiCompactFiniteType
        ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (q i))) :=
  PolarizedCurveCoverScheme.exists_five_coverSchemes B
    (sourceContained K B hK D) (targetContained K B hK D) (parameterContained K B hK D)
    D.projection (targetProjection K D) D.line (targetLine K D)
    D.relativelyAmple (ConstantProjectiveLinePolarization.targetLine_isRelativelyAmple K D.structureMap)

end M9Native.GenusNineCoverParameterSchemes
end
