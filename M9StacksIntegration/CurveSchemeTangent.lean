module

public import M9StacksIntegration.SmoothCotangentExt
public import M9StacksIntegration.DualExtNaturality
public import M9StacksIntegration.SmoothCurveTangentCohomology
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquivExt
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The original curve deformation tangent space and actual tangent H¹

STAGED ONLY until the exact original native deformation provider and the
unconditional smooth-curve tangent cohomology provider are checked.

The source is the actual native dual-number deformation space. Its class
map is the original 08UC difference class, its scalar structures are the
canonical native structures, and the target uses actual dual differentials.
The evaluation-natural Ext cancellation is retained for the cover arrows.
-/

attribute [local instance 10000] SheafOfModules.hasDerivedCategory
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples
open M9Native.InvertibleExtCancellation

universe u

namespace M9Native.CurveSchemeTangent

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Both original scalar modules use the literal same native category-linear structure. -/
theorem originalExtModule_eq (G : X.Modules) :
    schemeTangentExtModule (Over.mk f) G = SmoothCotangentExt.nativeExtModule f G 1 := rfl

/-- Actual native scheme deformations map to actual tangent H¹. The first
map is the original difference-class classifier, not a supplied tangent identification. -/
def tangentLinearEquivH1 [IsCurve k f] [Smooth f] :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
      ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
    schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))))) :=
    ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
  let := modulesLinearOverField k f
  let := schemeTangentExtModule (Over.mk f) (unit X)
  let := CurveTangentLineGeometry.differentials_isInvertible f
  exact (schemeTangentSpaceLinearEquivExt (Λ := Λ) (Over.mk f)).trans
    ((SmoothCotangentExt.ordinaryExtLinearEquiv f (unit X) 1).trans
      (DualExtNaturality.dualExtOneCohomologyLinearEquiv f
        (Scheme.Hom.relativeDifferentials f)))

/-- The actual classifier retains the literal native difference-class map
before the explicit locally-small-to-ordinary Ext comparison. -/
theorem tangentLinearEquivH1_apply [IsCurve k f] [Smooth f]
    (v : schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f)) :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
      ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
    letI := modulesLinearOverField k f
    letI := schemeTangentExtModule (Over.mk f) (unit X)
    letI := CurveTangentLineGeometry.differentials_isInvertible f
    tangentLinearEquivH1 (Λ := Λ) f v =
      DualExtNaturality.dualExtOneCohomologyLinearEquiv f
        (Scheme.Hom.relativeDifferentials f)
        (SmoothCotangentExt.ordinaryExtLinearEquiv f (unit X) 1
          (schemeTangentSpaceLinearEquivExt (Λ := Λ) (Over.mk f) v)) := by
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))))) :=
    ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
  let := modulesLinearOverField k f
  let := schemeTangentExtModule (Over.mk f) (unit X)
  let := CurveTangentLineGeometry.differentials_isInvertible f
  rfl

/-- The lifted dual-number model has the same canonical native vector-space
structure, through the original rank-one-module comparison. -/
def liftedTangentLinearEquivH1 [IsCurve k f] [Smooth f] :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
      ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
    tangentSpaceArtinian Λ k
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))) ≃ₗ[k]
      cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 1 := by
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))))) :=
    ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
  exact (tangentSpaceArtinianLinearEquivUnlifted
    (schemeDeformationBased (Λ := Λ) (Over.mk f))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation
    (schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f))).trans
      (tangentLinearEquivH1 (Λ := Λ) f)

variable [IsCurve k f] [Smooth f] [IsProper f] [IsAlgClosed k]

/-- The original unlifted scheme deformation tangent space in genus nine has dimension24. -/
theorem tangent_finrank_genus_nine (hg : genus f = 9) :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
      ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
    Module.finrank k (schemeTangentSpace (Λ := Λ) (k := k) (Over.mk f)) = 24 := by
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))))) :=
    ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
  exact (tangentLinearEquivH1 (Λ := Λ) f).finrank_eq.trans
    (SmoothCurveTangentCohomology.tangent_h1 f hg)

/-- The same actual dimension in the lifted model consumed by the hull theorem. -/
theorem liftedTangent_finrank_genus_nine (hg : genus f = 9) :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))))) :=
      ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
    Module.finrank k (tangentSpaceArtinian Λ k
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f)))) = 24 := by
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) (Over.mk f)).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk f)).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))))) :=
    ⟨schlessingerConditionS2_schemeDeformation (Λ := Λ) (Over.mk f)⟩
  exact (liftedTangentLinearEquivH1 (Λ := Λ) f).finrank_eq.trans
    (SmoothCurveTangentCohomology.tangent_h1 f hg)

end M9Native.CurveSchemeTangent
