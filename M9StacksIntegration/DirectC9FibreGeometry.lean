module

public import M9StacksIntegration.DirectC9PoincareFamily
public import M9StacksIntegration.PoincareLargeDegreeField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# The actual curve fibres of the actual ninth-power projection

All residue-field fibres are base changes of the original smooth proper
integral curve. The fibre-curve and dimension statements below are proved
for that actual projection; no dimension bound or replacement curve is
assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.DirectC9FibreGeometry

open DirectC9PoincareFamily (projection)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  smoothOfRelativeDimension_one_of_isCurve k C.hom

/-- The original integral curve is geometrically irreducible over the
actual algebraically closed ground field. -/
theorem original_geometricallyIrreducible : GeometricallyIrreducible C.hom :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k C.left C.hom

/-- Geometric reducedness and irreducibility are derived for the actual
original curve. -/
theorem original_geometricallyIntegral : GeometricallyIntegral C.hom := by
  letI := original_geometricallyIrreducible k C
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom

instance projection_isProper : IsProper (pullback.snd C.hom (power C 9).hom) :=
  inferInstanceAs (IsProper (pullback.snd C.hom (power C 9).hom))

instance projection_smooth : Smooth (pullback.snd C.hom (power C 9).hom) :=
  inferInstanceAs (Smooth (pullback.snd C.hom (power C 9).hom))

instance projection_isFlat : Flat (pullback.snd C.hom (power C 9).hom) := inferInstance

/-- The actual proper smooth projection is of finite presentation. -/
theorem projection_finitePresentation : FinitePresentation (pullback.snd C.hom (power C 9).hom) :=
  ⟨inferInstance,inferInstance,IsSeparated.instQuasiSeparated _⟩

instance projection_geometricallyIntegral : GeometricallyIntegral (pullback.snd C.hom (power C 9).hom) := by
  letI := original_geometricallyIntegral k C
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd C.hom (power C 9).hom))

instance fibre_geometricallyIntegral (t : (power C 9).left) :
    GeometricallyIntegral ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) := inferInstance

instance fibre_isIntegral (t : (power C 9).left) :
    IsIntegral ((pullback.snd C.hom (power C 9).hom).fiber t) := inferInstance

instance fibre_isProper (t : (power C 9).left) :
    IsProper ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (pullback.snd C.hom (power C 9).hom)
      ((power C 9).left.fromSpecResidueField t)) inferInstance

instance fibre_relativeDimension (t : (power C 9).left) :
    SmoothOfRelativeDimension 1 ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) := by
  have hπ : SmoothOfRelativeDimension 1 (pullback.snd C.hom (power C 9).hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback C.hom (power C 9).hom) inferInstance
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback (pullback.snd C.hom (power C 9).hom) ((power C 9).left.fromSpecResidueField t)) hπ

/-- The actual fibre has dimension exactly one. -/
theorem fibre_dimension (t : (power C 9).left) :
    topologicalKrullDim ((pullback.snd C.hom (power C 9).hom).fiber t) = 1 :=
  topologicalKrullDim_eq_of_smoothOfRelativeDimension
    ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) 1

instance fibre_isCurve (t : (power C 9).left) :
    IsCurve ((power C 9).left.residueField t) ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) where
  toIsVariety := { }
  topologicalKrullDim_eq_one := fibre_dimension k C t

/-- The fibre bound required by the native relative-degree theorem is
proved for every point of the actual base. -/
theorem fibre_dimension_le_one (t : (power C 9).left) :
    topologicalKrullDim ((pullback.snd C.hom (power C 9).hom).fiber t) ≤ 1 :=
  (fibre_dimension k C t).le

/-- The actual ground-field algebra on each actual residue field. -/
abbrev residueAlgebra (t : (power C 9).left) :
    Algebra k ((power C 9).left.residueField t) :=
  (Spec.preimage ((power C 9).left.fromSpecResidueField t ≫ (power C 9).hom)).hom.toAlgebra

theorem residueAlgebra_specMap (t : (power C 9).left) :
    letI := residueAlgebra k C t
    Spec.map (CommRingCat.ofHom (algebraMap k ((power C 9).left.residueField t))) =
      (power C 9).left.fromSpecResidueField t ≫ (power C 9).hom := by
  letI := residueAlgebra k C t
  change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
  rw [CommRingCat.ofHom_hom,Spec.map_preimage]

/-- The literal fibre is a genuine field extension of the original
curve with its original structure map. -/
theorem fibre_isPullback_original (t : (power C 9).left) :
    letI := residueAlgebra k C t
    IsPullback ((pullback.snd C.hom (power C 9).hom).fiberι t ≫ (fst C (power C 9)).left)
      ((pullback.snd C.hom (power C 9).hom).fiberToSpecResidueField t) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k ((power C 9).left.residueField t)))) := by
  letI := residueAlgebra k C t
  rw [residueAlgebra_specMap k C t]
  exact IsPullback.paste_horiz (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback C.hom (power C 9).hom)

end M9Native.DirectC9FibreGeometry
