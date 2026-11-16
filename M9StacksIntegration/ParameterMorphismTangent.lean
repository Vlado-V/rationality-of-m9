module

public import M9StacksIntegration.ParameterMorphismDeformation
public import M9StacksIntegration.ParameterTangentH1
public import M9StacksIntegration.SchemeMorphismSourceH1Map

/-!
# Actual parameter-family tangent classes factor through morphism deformations

Pulling an actual family morphism back along the original tangent arrow
constructs a genuine native morphism deformation. Forgetting its source
returns exactly the actual family class, so the H¹ image containment is
derived from a real preimage for every tangent vector.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.ParameterMorphismTangent

variable {X Y T S : Scheme.{u}}
  (p : X ⟶ T) [Flat p] (q : Y ⟶ T) [Flat q]
  (h : X ⟶ Y) (hh : h ≫ q = p) (s : T ⟶ S) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

local instance residueTangentModule : Module κ (DottedTangentArrow s x) :=
  inferInstanceAs (Module (T.residueField x) (DottedTangentArrow s x))

/-- The original morphism on the actual scheme-theoretic residue-field fibres. -/
abbrev fibreMap : (ParameterTangentDeformation.fibre p x).left ⟶
    (ParameterTangentDeformation.fibre q x).left :=
  ParameterMorphismDeformation.pulledMap (Z := Spec (.of κ))
    p q h hh (T.fromSpecResidueField x)

omit [Flat p] [Flat q] in
/-- Its original base triangle. -/
theorem fibreMap_over :
    fibreMap p q h hh x ≫ (ParameterTangentDeformation.fibre q x).hom =
      (ParameterTangentDeformation.fibre p x).hom :=
  ParameterMorphismDeformation.pulledMap_toBase p q h hh (T.fromSpecResidueField x)

/-- The genuine original morphism deformation defined by the actual tangent arrow. -/
def morphismObject (θ : DottedTangentArrow s x) :=
  ParameterMorphismDeformation.fibreObject (k := κ)
    p q h hh (T.fromSpecResidueField x)
    (coordBase (Λ := κ) (FGModuleCat.of κ (ULift.{u} κ)))
    (ParameterTangentH1.liftedArrow s x θ).val
    (ParameterTangentH1.liftedArrow s x θ).property

/-- Its literal original native morphism tangent class. -/
def morphismClass (θ : DottedTangentArrow s x) :=
  tangentClassAt
    (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection (Λ := κ) (k := κ)
      (fibreMap p q h hh x) (ParameterTangentDeformation.fibre p x).hom
      (ParameterTangentDeformation.fibre q x).hom (fibreMap_over p q h hh x)))
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _)
    (FGModuleCat.of κ (ULift.{u} κ)) (morphismObject p q h hh s x θ)

/-- Source forgetting sends this actual morphism class to exactly the
original family class, with the actual ULift coefficient model retained. -/
theorem sourceEndpoint_class (θ : DottedTangentArrow s x) :
    (SchemeMorphismSourceObstruction.endpointTangentMap
      (ParameterTangentDeformation.fibre p x).hom
      (ParameterTangentDeformation.fibre q x).hom
      (fibreMap p q h hh x) (fibreMap_over p q h hh x)
      (morphismClass p q h hh s x θ)).1 =
        ParameterTangentH1.tangentEndpointLinearMap p s x θ := by
  change tangentMapAt _ _
    (schemeMorphismSourceBased (Λ := κ) (k := κ) (fibreMap p q h hh x)
      (ParameterTangentDeformation.fibre p x).hom
      (ParameterTangentDeformation.fibre q x).hom (fibreMap_over p q h hh x))
    (FGModuleCat.of κ (ULift.{u} κ)) (morphismClass p q h hh s x θ) = _
  rw [morphismClass, tangentMapAt_tangentClassAt,
    ParameterTangentH1.tangentEndpointLinearMap_apply]
  rfl

set_option maxRecDepth 1024 in
/-- The actual H¹ value of the family tangent comes from the original
source-forgetting tangent map on a genuine morphism deformation. -/
theorem sourceH1_class [IsCurve κ (ParameterTangentDeformation.fibre p x).hom]
    [Smooth (ParameterTangentDeformation.fibre p x).hom]
    (θ : DottedTangentArrow s x) :
    StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
      (ParameterTangentDeformation.fibre p x).hom
      (SchemeMorphismSourceObstruction.endpointTangentMap
        (ParameterTangentDeformation.fibre p x).hom
        (ParameterTangentDeformation.fibre q x).hom
        (fibreMap p q h hh x) (fibreMap_over p q h hh x)
        (morphismClass p q h hh s x θ)).1 =
      ParameterTangentH1.tangentH1LinearMap p s x θ :=
  congrArg (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
    (ParameterTangentDeformation.fibre p x).hom)
    (sourceEndpoint_class p q h hh s x θ)

set_option maxRecDepth 1024 in
/-- A genuine range containment, proved by constructing each original
morphism-deformation preimage. No desired image relation is assumed. -/
theorem tangentH1_range_le_sourceForgetting
    [IsCurve κ (ParameterTangentDeformation.fibre p x).hom]
    [Smooth (ParameterTangentDeformation.fibre p x).hom] :
    LinearMap.range (ParameterTangentH1.tangentH1LinearMap p s x) ≤
      LinearMap.range
        ((StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
          (ParameterTangentDeformation.fibre p x).hom).toLinearMap.comp
          ((LinearMap.fst κ _ _).comp
            (SchemeMorphismSourceObstruction.endpointTangentMap
              (ParameterTangentDeformation.fibre p x).hom
              (ParameterTangentDeformation.fibre q x).hom
              (fibreMap p q h hh x) (fibreMap_over p q h hh x)))) := by
  rintro v ⟨θ, rfl⟩
  exact ⟨morphismClass p q h hh s x θ, sourceH1_class p q h hh s x θ⟩

set_option maxRecDepth 1024 in
/-- The constructed preimage is evaluated by the separately checked original
source-forgetting H¹ map itself. -/
theorem actual_sourceForgettingH1_morphismClass
    [IsCurve κ (ParameterTangentDeformation.fibre p x).hom]
    [Smooth (ParameterTangentDeformation.fibre p x).hom]
    (θ : DottedTangentArrow s x) :
    SchemeMorphismSourceH1.sourceForgettingH1
      (ParameterTangentDeformation.fibre p x).hom
      (ParameterTangentDeformation.fibre q x).hom
      (fibreMap p q h hh x) (fibreMap_over p q h hh x)
      (morphismClass p q h hh s x θ) =
        ParameterTangentH1.tangentH1LinearMap p s x θ :=
  sourceH1_class p q h hh s x θ

set_option maxRecDepth 1024 in
/-- The genuine family tangent image lies in the actual original morphism
source-forgetting H¹ image, with no containment premise. -/
theorem tangentH1_range_le_actual_sourceForgettingH1
    [IsCurve κ (ParameterTangentDeformation.fibre p x).hom]
    [Smooth (ParameterTangentDeformation.fibre p x).hom] :
    LinearMap.range (ParameterTangentH1.tangentH1LinearMap p s x) ≤
      LinearMap.range (SchemeMorphismSourceH1.sourceForgettingH1
        (ParameterTangentDeformation.fibre p x).hom
        (ParameterTangentDeformation.fibre q x).hom
        (fibreMap p q h hh x) (fibreMap_over p q h hh x)) :=
  tangentH1_range_le_sourceForgetting p q h hh s x

end M9Native.ParameterMorphismTangent
