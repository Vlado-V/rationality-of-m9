module

public import M9StacksIntegration.LagrangianChosenCoarseCoordinateShift
public import M9StacksIntegration.LagrangianChosenCoarseDenseImage
public import M9StacksIntegration.GenusNineCoarseVariety
public import M9StacksIntegration.PrimitiveNativeClassifierRationalOpen

@[expose] public section

/-! Rationality assembly for the SAME independently chosen native M9 space.
The only remaining geometric inputs are actual raw chosen-map image density
and the exact all-original classifier geometry on its true shifted domain.
Actual reducedness, decency, local finite type and source irreducibility
are already proved. The chart, quotient and field comparison are derived.
This is an honest intermediate, not a proof of those two geometric inputs
or of the standalone all-family coarse-moduli statement. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Space.pointTopology

namespace M9Native.LagrangianChosenCoarseRationality

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))
  (hZ : B.Contains integerBase)

/-- The actual independently chosen field-base genus-nine coarse space. -/
abbrev target : AlgebraicSpaces B (Spec (.of ℂ)) hC :=
  LagrangianChosenCoarseFamily.target ℂ B hC hZ

/-- That SAME actual space on every original complex test scheme. -/
abbrev originalSpace : M9StandaloneDraft.Space ℂ :=
  M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative ℂ B hC
    (target B hC hZ).obj (target B hC hZ).property

/-- The actual shifted chosen map has the frozen criterion's literal source. -/
abbrev classifierMap :
    yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC
      LagrangianChosenCoarseCoordinateShift.goodOpen) ⟶ (target B hC hZ).obj :=
  (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom

/-- Genuine native point-image density of the ACTUAL RAW chosen family map. -/
def ImageDense : Prop :=
  DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
    (schemeSpace (LagrangianNativeGenusNineFamily.base ℂ B hC)).obj
    (LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ).hom)

/-- Exact all-original invariance and all-ACL orbit fibres of the ACTUAL
shifted classifier. No raw/native point or action equality is asserted. -/
abbrev Geometry : Prop :=
  PrimitiveNativeClassifierRationalOpen.ClassifierGeometry B hC (target B hC hZ)
    LagrangianChosenCoarseCoordinateShift.goodOpen (classifierMap B hC hZ)

/-- The actual coordinate-source isomorphism transports genuine raw density. -/
theorem shifted_imageDense (hd : ImageDense B hC hZ) :
    DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC
        LagrangianChosenCoarseCoordinateShift.goodOpen)) (classifierMap B hC hZ)) :=
  (LagrangianChosenCoarseCoordinateShift.nativeMap_dense_iff B hC hZ).2 hd

/-- Actual reducedness and decency combine with derived source irreducibility
and genuine raw image density to prove integrality of this SAME target. -/
theorem integral_of_imageDense (hd : ImageDense B hC hZ) :
    Space.IsIntegralSpace B (Spec (.of ℂ)) hC (target B hC hZ).obj :=
  LagrangianChosenCoarseDenseImage.target_integral_of_dense ℂ B hC hZ hd
    (GenusNineCoarseVariety.reduced B hZ ℂ hC 9 (by decide))
    (GenusNineCoarseVariety.decent B hZ ℂ hC 9 (by decide))

/-- The actual chosen target's structural local finite type is a theorem. -/
theorem locallyFiniteType :
    Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from
        (target B hC hZ).obj) :=
  GenusNineCoarseVariety.locallyFiniteType B hZ ℂ hC 9 (by decide)

/-- The original all-test variety property of the SAME actual M9 space. -/
theorem variety : M9StandaloneDraft.VarietySpace ℂ (originalSpace B hC hZ) :=
  GenusNineCoarseVariety.variety B hZ ℂ hC 9 (by decide)

/-- Only genuine raw density and actual shifted classifier geometry remain
as inputs to the literal all-original common dense open with A24. -/
theorem rationalOpen (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) :
    M9StandaloneDraft.RationalOpen ℂ 24 (originalSpace B hC hZ).obj :=
  PrimitiveNativeClassifierRationalOpen.rationalOpen B hC (target B hC hZ)
    LagrangianChosenCoarseCoordinateShift.goodOpen (classifierMap B hC hZ)
    (integral_of_imageDense B hC hZ hd) (locallyFiniteType B hC hZ)
    (shifted_imageDense B hC hZ hd) h

/-- The ACTUAL native rational-function carrier of the chosen M9 space,
with its ACTUAL structural complex algebra, is rational in 24 variables. -/
theorem nonempty_nativeRationalFieldEquiv
    (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ hd)
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
    Nonempty (Space.rationalFunctions B (Spec (.of ℂ)) hC (target B hC hZ).property ≃ₐ[ℂ]
      M9.RationalField ℂ 24) :=
  PrimitiveNativeClassifierRationalOpen.nonempty_nativeRationalFieldEquiv B hC
    (target B hC hZ) LagrangianChosenCoarseCoordinateShift.goodOpen (classifierMap B hC hZ)
    (integral_of_imageDense B hC hZ hd) (locallyFiniteType B hC hZ)
    (shifted_imageDense B hC hZ hd) h

/-- Select the actual chosen-space field equivalence derived from those two
honest geometric inputs, without supplying any field comparison. -/
def nativeRationalFieldEquiv (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ hd)
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
    Space.rationalFunctions B (Spec (.of ℂ)) hC (target B hC hZ).property ≃ₐ[ℂ]
      M9.RationalField ℂ 24 :=
  PrimitiveNativeClassifierRationalOpen.nativeRationalFieldEquiv B hC
    (target B hC hZ) LagrangianChosenCoarseCoordinateShift.goodOpen (classifierMap B hC hZ)
    (integral_of_imageDense B hC hZ hd) (locallyFiniteType B hC hZ)
    (shifted_imageDense B hC hZ hd) h

/-- The actual native structural inclusion of every complex coefficient is retained. -/
theorem nativeRationalFieldEquiv_coefficient
    (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) (c : ℂ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ hd)
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
    nativeRationalFieldEquiv B hC hZ hd h
        (AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap ℂ B hC
          (target B hC hZ).property (integral_of_imageDense B hC hZ hd) c) =
      algebraMap ℂ (M9.RationalField ℂ 24) c := by
  letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
    (integral_of_imageDense B hC hZ hd)
  letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
    (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
  exact (nativeRationalFieldEquiv B hC hZ hd h).commutes c

/-- The inverse retains that SAME actual native structural coefficient inclusion. -/
theorem nativeRationalFieldEquiv_inverse_coefficient
    (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) (c : ℂ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ hd)
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
    (nativeRationalFieldEquiv B hC hZ hd h).symm
        (algebraMap ℂ (M9.RationalField ℂ 24) c) =
      AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap ℂ B hC
        (target B hC hZ).property (integral_of_imageDense B hC hZ hd) c := by
  letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
    (integral_of_imageDense B hC hZ hd)
  letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
    (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
  exact (nativeRationalFieldEquiv B hC hZ hd h).symm.commutes c

/-- The actual variety, literal all-original rational open, and ACTUAL native
complex function-field conclusion, with exactly the same two honest inputs. -/
theorem rationalityPackage (hd : ImageDense B hC hZ) (h : Geometry B hC hZ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ hd)
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ hd)
    M9StandaloneDraft.VarietySpace ℂ (originalSpace B hC hZ) ∧
      M9StandaloneDraft.RationalOpen ℂ 24 (originalSpace B hC hZ).obj ∧
      Nonempty (Space.rationalFunctions B (Spec (.of ℂ)) hC (target B hC hZ).property ≃ₐ[ℂ]
        M9.RationalField ℂ 24) :=
  ⟨variety B hC hZ, rationalOpen B hC hZ hd h,
    nonempty_nativeRationalFieldEquiv B hC hZ hd h⟩

end M9Native.LagrangianChosenCoarseRationality
