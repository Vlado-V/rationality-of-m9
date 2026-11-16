module

public import M9StacksIntegration.LagrangianIncidenceIntegral
public import M9StacksIntegration.LagrangianGeometricGenericSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# Connectedness of every original five-hyperplane LG section

The proper original incidence has integral total space, normal integral
parameter Grassmannian, and a genuinely geometrically integral generic
fibre.  Native Stein factorization therefore makes every original fibre
geometrically connected, without any regular-prefix or generic-parameter
hypothesis on that fibre.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianIncidenceConnected

open LagrangianLinearSections

variable (K : Type u) [Field K]

theorem parameter_normal : AlgebraicGeometry.IsNormal (parameter K) :=
  isNormal_of_isRegular (parameter K)
    (isRegular_of_smooth_over_field (parameterProjection K))

variable [CharZero K] [IsAlgClosed K]

/-- All actual total-space generic points lie over the actual generic
parameter, by the proved total integrality and original dominance. -/
theorem genericPoints_map (x : family K) (hx : x ∈ genericPoints (family K)) :
    familyProjection K x = genericPoint (parameter K) := by
  have hx' : x = genericPoint (family K) := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
  subst x
  have h := (genericPoint_spec (family K)).image (familyProjection K).continuous
  rw [Set.image_univ, (familyProjection K).denseRange.closure_range] at h
  exact ((genericPoint_spec (parameter K)).eq h).symm

/-- The canonical scalar map of the original generic fibre is an
isomorphism, derived from actual proper geometric integrality. -/
theorem generic_fibre_globalSections_isIso :
    IsIso ((Scheme.ΓSpecIso ((parameter K).residueField (genericPoint (parameter K)))).inv ≫
      ((familyProjection K).fiberToSpecResidueField (genericPoint (parameter K))).appTop) := by
  let : GeometricallyIntegral
      ((familyProjection K).fiberToSpecResidueField (genericPoint (parameter K))) :=
    LagrangianGeometricGenericSections.generic_fibre_geometricallyIntegral K
  let : IsProper
      ((familyProjection K).fiberToSpecResidueField (genericPoint (parameter K))) :=
    inferInstanceAs (IsProper (pullback.snd (familyProjection K)
      ((parameter K).fromSpecResidueField (genericPoint (parameter K)))))
  exact isIso_globalSections_of_geometricallyIntegral
    ((parameter K).residueField (genericPoint (parameter K)))
    ((familyProjection K).fiberToSpecResidueField (genericPoint (parameter K)))

/-- Every fibre of the ORIGINAL unrestricted universal incidence is
geometrically connected.  Every Stein hypothesis is derived. -/
instance familyProjection_geometricallyConnected : GeometricallyConnected (familyProjection K) := by
  let : AlgebraicGeometry.IsNormal (parameter K) := parameter_normal K
  exact Stacks.SteinFactorization.geometricallyConnected_of_isNormal
    (familyProjection K) (genericPoints_map K) (generic_fibre_globalSections_isIso K)

theorem fibre_geometricallyConnected (y : parameter K) :
    GeometricallyConnected ((familyProjection K).fiberToSpecResidueField y) := inferInstance

/-- Every actual field-valued parameter, including outside the smooth
open, has a connected original scheme-theoretic fibre. -/
theorem baseChange_connected (L : Type u) [Field L] (p : Spec (.of L) ⟶ parameter K) :
    ConnectedSpace (pullback (C := Scheme.{u}) (familyProjection K) p) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (familyProjection K) p)

end M9Native.LagrangianIncidenceConnected

end
