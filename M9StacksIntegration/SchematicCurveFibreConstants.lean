module

public import M9StacksIntegration.SchematicGlobalFunctions
public import M9StacksIntegration.AllTestNativeSchematicCharts
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Actual native global functions on schematic curve fibres

The schematic pullback is compared with the actual presheaf fibre
product by its Cartesian isomorphism. Both projections are retained.
The constants theorem is applied over the field of the original native
point, and the proved identity-chart comparison transfers the actual
global-functions map. No genus, rank-H0 or universal-H0 premise occurs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.SchematicCurveFibreConstants
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

-- Native CurvesH01 uses these same explicit presheaf-limit instances:
-- avoid repeatedly searching through the many represented-space limits.
local instance (priority := high) hasPullbacks_presheaf :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) := (hasPullbacks_presheaf B hZ).has_limit _

/-- The actual native fibre projection has bijective global-functions
pullback, for every native field point of an original schematic proper
smooth geometrically connected relative curve. -/
theorem field_fibre_globalFunctions_bijective
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hc : GeometricallyConnected ((BigFppfOver.toScheme B integerBase hZ).map q))
    (p : FieldValuedPoint B integerBase hZ (schemeSpace T).obj) :
    Function.Bijective (globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd (schemeSpaceMap q).hom
          (schemeSpaceMap p.value).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ
          (schemeSpaceMap q) (schemeSpaceMap p.value) ⟶ schemeSpace p.siteObject)) := by
  let a : p.siteObject ⟶ T := p.value
  let v := pullback.snd q a
  let g := (BigFppfOver.toScheme B integerBase hZ).map v
  have sq := (IsPullback.of_hasPullback q a).map
    (BigFppfOver.toScheme B integerBase hZ)
  let : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) sq hp
  let : SmoothOfRelativeDimension 1 g :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) sq hs
  let : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  let : GeometricallyConnected g :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hc
  let : GeometricallyReduced g := geometricallyReduced_of_smooth g
  let : IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ g.appTop) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper p.carrier g
  let : IsIso g.appTop := by
    have he : (Scheme.ΓSpecIso (.of p.carrier)).hom ≫
        ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ g.appTop) = g.appTop := by simp
    rw [← he]
    infer_instance
  have hv : Function.Bijective (globalFunctionsMap B integerBase hZ (schemeSpaceMap v)) :=
    SchematicGlobalFunctions.bijective_of_bijective_appTop B integerBase hZ v
      (asIso g.appTop).commRingCatIsoToRingEquiv.bijective
  have sqp := (IsPullback.of_hasPullback q a).map yoneda
  let e₀ := sqp.isoPullback
  let F := AlgebraicSpaces.fiberProduct B integerBase hZ
    (schemeSpaceMap q) (schemeSpaceMap p.value)
  let e : schemeSpace (pullback q a) ≅ F :=
    { hom := ObjectProperty.homMk e₀.hom
      inv := ObjectProperty.homMk e₀.inv
      hom_inv_id := ObjectProperty.hom_ext _ e₀.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ e₀.inv_hom_id }
  let r : F ⟶ schemeSpace p.siteObject :=
    ObjectProperty.homMk (pullback.snd (schemeSpaceMap q).hom (schemeSpaceMap p.value).hom)
  have he : e.hom ≫ r = schemeSpaceMap v :=
    ObjectProperty.hom_ext _ sqp.isoPullback_hom_snd
  have heinj : Function.Injective (globalFunctionsMap B integerBase hZ e.hom) := by
    apply Function.LeftInverse.injective (g := globalFunctionsMap B integerBase hZ e.inv)
    intro z
    change ((globalFunctionsMap B integerBase hZ e.inv).comp
      (globalFunctionsMap B integerBase hZ e.hom)) z = z
    rw [← globalFunctionsMap_comp, e.inv_hom_id, globalFunctionsMap_id]
    rfl
  have heq (z) : globalFunctionsMap B integerBase hZ e.hom
      (globalFunctionsMap B integerBase hZ r z) =
        globalFunctionsMap B integerBase hZ (schemeSpaceMap v) z := by
    change ((globalFunctionsMap B integerBase hZ e.hom).comp
      (globalFunctionsMap B integerBase hZ r)) z = _
    rw [← globalFunctionsMap_comp, he]
  change Function.Bijective (globalFunctionsMap B integerBase hZ r)
  constructor
  · intro x y hxy
    apply hv.1
    exact (heq x).symm.trans ((congrArg (globalFunctionsMap B integerBase hZ e.hom) hxy).trans
      (heq y))
  · intro y
    obtain ⟨x, hx⟩ := hv.2 (globalFunctionsMap B integerBase hZ e.hom y)
    refine ⟨x, heinj ?_⟩
    exact (heq x).trans hx

end M9Native.SchematicCurveFibreConstants
