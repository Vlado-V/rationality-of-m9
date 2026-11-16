module

public import M9StacksIntegration.DirectC9FibreGeometry
public import M9StacksIntegration.DirectC9FamilyDegree
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import M9StacksIntegration.BaseFieldGraph

/-!
# The degree-eight family at an actual original-field point

The fibre at a prescribed over-k point is the ORIGINAL curve, through
the actual graph pullback square. Its actual pulled-back invertible
module has native degree eight for the ORIGINAL structure morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower

universe u

namespace M9Native.DirectC9OriginalPoint

/-- Relative degree over a field is the absolute native degree. This
uses actual field-extension invariance on the actual standard fibre. -/
theorem relativeDegree_eq_absolute (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (hdimF : ∀ t : Spec (.of k), topologicalKrullDim (f.fiber t) ≤ 1)
    (t : Spec (.of k)) (x : Stacks.Picard.ofScheme X) :
    relativeInvertibleDegreeHomAt f hdimF t x = invertibleCurveDegreeHom k f hdim x := by
  letI : Algebra k ((Spec (.of k)).residueField t) :=
    (Spec.preimage ((Spec (.of k)).fromSpecResidueField t)).hom.toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField t))) =
      (Spec (.of k)).fromSpecResidueField t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
    rw [CommRingCat.ofHom_hom,Spec.map_preimage]
  have hsq : IsPullback (f.fiberι t) (f.fiberToSpecResidueField t) f
      (Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField t)))) := by
    rw [hs]
    exact IsPullback.of_hasPullback f _
  exact invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k
    ((Spec (.of k)).residueField t) hsq hdim (hdimF t) x

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open PoincareChern (lineClass)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

/-- The actual original curve's standard fibres are actual dimension-one curves. -/
theorem original_fibre_dimension_le_one (t : Spec (.of k)) :
    topologicalKrullDim (C.hom.fiber t) ≤ 1 := by
  letI : GeometricallyIntegral C.hom := DirectC9FibreGeometry.original_geometricallyIntegral k C
  letI : GeometricallyIntegral (C.hom.fiberToSpecResidueField t) := inferInstance
  letI : IsIntegral (C.hom.fiber t) := inferInstance
  letI : SmoothOfRelativeDimension 1 (C.hom.fiberToSpecResidueField t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback C.hom ((Spec (.of k)).fromSpecResidueField t)) inferInstance
  exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (C.hom.fiberToSpecResidueField t) 1).le

variable (c₀ : power C 0 ⟶ C) (p : Spec (.of k) ⟶ (power C 9).left)
  (hp : p ≫ (power C 9).hom = 𝟙 _)

/-- The actual original curve embeds in the actual family over the prescribed point. -/
abbrev pointGraph : C.left ⟶ familySpace C :=
  BaseFieldGraph.graph C.hom (power C 9).hom p hp

theorem pointGraph_isPullback :
    IsPullback (pointGraph k C p hp) C.hom (familyProjection C) p :=
  BaseFieldGraph.isPullback_graph C.hom (power C 9).hom p hp

/-- The actual pulled-back degree-eight module on the original curve. -/
abbrev pointLine : C.left.Modules :=
  (Scheme.Modules.pullback (pointGraph k C p hp)).obj (degreeEightLine C c₀)

instance pointLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible C.left.presheaf C.left.ringCatSheaf.2
      (pointLine k C c₀ p hp) :=
  Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (pointGraph k C p hp)
    (degreeEightLine C c₀)

/-- The actual Picard class on the ORIGINAL curve has actual degree eight. -/
theorem pointLine_class_degree :
    invertibleCurveDegreeHom k C.hom (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le
      (@lineClass C.left (pointLine k C c₀ p hp) (pointLine_isInvertible k C c₀ p hp)) = 8 := by
  let c := IsLocalRing.closedPoint k
  have h8 := relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
    (pointGraph_isPullback k C p hp) (DirectC9FibreGeometry.fibre_dimension_le_one k C)
    (original_fibre_dimension_le_one k C) c
    (@lineClass (familySpace C) (degreeEightLine C c₀) (degreeEightLine_isInvertible C c₀))
  rw [DirectC9FamilyDegree.degreeEightLine_degree C c₀
    (DirectC9FibreGeometry.fibre_dimension_le_one k C) (p c)] at h8
  have heq := @PoincareChern.lineClass_pullback C.left (familySpace C) (pointGraph k C p hp)
    (degreeEightLine C c₀) (degreeEightLine_isInvertible C c₀)
  have habs := relativeDegree_eq_absolute k C.hom
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le
    (original_fibre_dimension_le_one k C) c
    (@lineClass C.left (pointLine k C c₀ p hp) (pointLine_isInvertible k C c₀ p hp))
  exact habs.symm.trans ((congrArg
    (relativeInvertibleDegreeHomAt C.hom (original_fibre_dimension_le_one k C) c) heq).trans h8)

/-- The same assertion for the actual module degree, not a replacement representative. -/
theorem pointLine_degree :
    let hL := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (pointLine_isInvertible k C c₀ p hp)
    @invertibleCurveDegree k _ C.left C.hom _
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le (pointLine k C c₀ p hp) hL = 8 := by
  simpa only [invertibleCurveDegreeHom_picardClass] using pointLine_class_degree k C c₀ p hp

end M9Native.DirectC9OriginalPoint
