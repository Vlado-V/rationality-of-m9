module

public import M9StacksIntegration.NativeSmoothGenusCurveClassifier
public import M9StacksIntegration.UniversalLagrangianCurveFamily
public import M9StacksIntegration.UniversalLagrangianCurveGenus
public import M9StacksIntegration.LagrangianGeometricGenericSections

/-!
# The actual original universal family in its genuine native genus stack

The point is the constructed Bertini point of the original universal
family, lifted to its literal canonical good open. Its actual native
fibre genus is constant on the whole original family. The proved
geometric connectedness and universal H0, rather than family-class or
classifying-map premises, give the actual genus-substack object and
Cartesian classifier.

The numerical identification of this actual fibre genus with nine is
a separate LG-degree/adjunction theorem. This module does not claim that
identification or M9 rationality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.UniversalLagrangianNativeGenus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9StacksIntegration.NativeSchematicCurveFamily
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open SmoothIntegralHyperplaneCuts LagrangianBertiniPoint

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- The constructed original Bertini point in the actual canonical
good open, with no point or smooth-fibre premise. -/
def bertiniGoodPoint : Spec (.of K) ⟶ (goodOpen K).toScheme :=
  LagrangianConnectedPointCriterion.goodPoint K (parameterPoint K)
    (parameterPoint_projection K) (pointFibre_dimension K)

/-- The actual cohomological genus of an actual original restricted fibre.
Its numerical value is not built into this definition. -/
def fibreGenus : ℕ := genus (pullback.snd (restrictedProjection K) (bertiniGoodPoint K))

/-- The computed family genus is the actual native genus of the original
constructed five-cut curve. Both fibre isomorphisms retain the original
Spec K projection; no field automorphism or genus comparison is assumed. -/
theorem fibreGenus_eq_fiveCut_genus :
    fibreGenus K = genus (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) := by
  have hIso {A B : Scheme.{u}} (p : B ⟶ Spec (.of K)) [IsProper p]
      (e : A ≅ B) : genus (e.hom ≫ p) = genus p := by
    refine genus_baseChange K K e.hom (e.hom ≫ p) p ?_
    rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let hp : ∀ t : Spec (.of K), parameterPoint K t ∈ goodOpen K :=
    parameterPoint_lands_goodOpen K
  have hOpen := hIso (pullback.snd (familyProjection K) (parameterPoint K))
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K) (parameterPoint K) hp)
  rw [OpenRestrictionPointFiber.fiberIso_hom_snd] at hOpen
  change fibreGenus K = genus (pullback.snd (familyProjection K) (parameterPoint K)) at hOpen
  have hCut := hIso (pullback.snd (familyProjection K) (parameterPoint K)) (cutIsoPointFibre K)
  rw [cutIsoPointFibre_hom_base] at hCut
  exact hOpen.trans hCut.symm

/-- The unchanged original family satisfies the full all-field curve
condition with its actual native fibre genus. Its geometric connectedness
is proved by the original Bertini/spreading construction. -/
theorem original_schemeCurve :
    M9StandaloneDraft.SchemeCurve (restrictedProjection K) (fibreGenus K) :=
  UniversalLagrangianCurveGenus.schemeCurve_of_geometricallyConnected K (bertiniGoodPoint K)

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Actual native genus membership of the literal original universal
family. Only containment in the chosen site is parameterized. -/
theorem family_membership
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    IsSmoothH0FamilyOfFibreGenus B hZ (fibreGenus K)
      (UniversalLagrangianCurveFamily.family B hZ K hU hV) := by
  have hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map
        (UniversalLagrangianCurveFamily.siteProjection B hZ K hU hV)) (fibreGenus K) := by
    change M9StandaloneDraft.SchemeCurve (restrictedProjection K) (fibreGenus K)
    exact original_schemeCurve K
  simpa only [UniversalLagrangianCurveFamily.family, schemeCurveFamily] using
    NativeSmoothGenusCurveClassifier.schemeCurveFamily_membership B hZ
      (UniversalLagrangianCurveFamily.siteProjection B hZ K hU hV) (fibreGenus K) hq

/-- The same literal original native family as an object of its actual
genus stack, with its membership proved above. -/
def moduliObject
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.obj :=
  ⟨UniversalLagrangianCurveFamily.family B hZ K hU hV, family_membership K B hZ hU hV⟩

/-- The genuine Cartesian classifier of the original universal family.
No genus, family-class or classifying-map premise is supplied. -/
def classifyingMor
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p
      (UniversalLagrangianCurveFamily.family B hZ K hU hV).base := by
  let : (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).2.isFibered
  exact Functor.FiberedMor.OfFiberObj.fiberedMor
    (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p
    (UniversalLagrangianCurveFamily.family B hZ K hU hV).base
    (show (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p.obj
      (moduliObject K B hZ hU hV) = _ from rfl)

/-- Evaluation over the identity recovers the same original family
inside the true native genus substack. -/
def classifiesOriginalFamily
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    (classifyingMor K B hZ hU hV).toFunctor.obj
      (Functor.FiberedMor.unit (UniversalLagrangianCurveFamily.family B hZ K hU hV).base) ≅
      moduliObject K B hZ hU hV := by
  let : (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).2.isFibered
  exact Functor.Fiber.fiberInclusion.mapIso
    (Functor.FiberedMor.OfFiberObj.fiberIso
      (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p
      (UniversalLagrangianCurveFamily.family B hZ K hU hV).base
      (show (moduliSmoothCurvesOfGenus B hZ (fibreGenus K)).val.p.obj
        (moduliObject K B hZ hU hV) = _ from rfl)
      (classifyingMor K B hZ hU hV).obj_over_unit)

end M9Native.UniversalLagrangianNativeGenus
