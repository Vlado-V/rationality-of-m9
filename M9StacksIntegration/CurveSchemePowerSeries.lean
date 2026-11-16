module

public import M9StacksIntegration.CurveSchemeProrepresentability
public import M9StacksIntegration.PowerSeriesLocalDimension
public import M9StacksIntegration.Private.HullTangentComparison
public import M9StacksIntegration.Private.RepresentedPowerSeriesDimension
public import StacksFrontier.Deformation.Examples.Geometric.SchemesUnobstructedUnconditional
public import StacksFrontier.Deformation.Smooth.Unobstructed
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic

/-!
# An actual power-series hull of the actual smooth curve deformation problem

The hull is constructed by original Schlessinger existence on the actual
scheme deformation category. Original 0DZQ proves unobstructedness from
smoothness, and original 0DZK constructs its power-series model. There is
no supplied formal object, identification, smoothness or ringdimension.
The actual canonical hull tangent dimension is separately pinned to24.
The original relative power-series tangent theorem and the zero tangent of
the coefficient field then identify the variable count and actual ring
dimension with24, without a dimension premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples

universe u

namespace M9Native.CurveSchemePowerSeries

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]

/-- An actual formal hull of the original scheme deformation category exists. -/
theorem existsFormalHull :
    ∃ ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)),
      IsHull (schemeDeformation_cofibered (Over.mk f)) ξ := by
  letI : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  let 𝓕 := schemeDeformationBased (Λ := k) (Over.mk f)
  let hD := isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f)
  let hS2 := schlessingerConditionS2_schemeDeformation (Λ := k) (Over.mk f)
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  letI : Algebra.IsSeparable (residueImageField k k) k :=
    (CurveSchemeProrepresentability.classical_baseField k).isSeparable
  letI : FiniteDimensional k (tangentSpaceArtinian k k
    (isomorphismClasses 𝓕 hD.predeformation.cofibered)) :=
    finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓕 hD.predeformation hS2
      (finiteDimensional_schemeTangentSpace (Λ := k) (Over.mk f))
  obtain ⟨ξ,hξ,-⟩ := exists_hull_isomorphismClasses k k 𝓕 hD.predeformation
    (schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS)
    (schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS) inferInstance
  exact ⟨ξ,hξ⟩

/-- The formal object is the actual hull just constructed, not an independent model. -/
def formalHull : FormalObject (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)) :=
  (existsFormalHull f).choose

theorem formalHull_isHull : IsHull (schemeDeformation_cofibered (Over.mk f)) (formalHull f) :=
  (existsFormalHull f).choose_spec

/-- Original 0DZQ derives unobstructedness from the actual smooth curve. -/
theorem unobstructed :
    IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := k) (Over.mk f))) := by
  letI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  letI : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  letI : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  letI : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  apply isSmooth_baseProjection_schemeDeformationCategoryProjection_of_lci (Over.mk f)
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le (syntomic_of_smooth f)
  simpa only [Scheme.Hom.smoothLocus_eq_top,TopologicalSpace.Opens.coe_top,Set.compl_univ]
    using (Set.finite_empty : (∅ : Set X).Finite)

/-- Original 0DZK constructs a genuine finite power-series model for this actual hull. -/
theorem formalHull_powerSeries :
    ∃ n : ℕ, Nonempty ((formalHull f).base ≃ₐ[k] MvPowerSeries (Fin n) k) :=
  (isSmooth_baseProjection_iff_powerSeries
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).predeformation
    (formalHull f) (formalHull_isHull f).1
    (CurveSchemeProrepresentability.classical_baseField k)).mp (unobstructed f)

/-- The variable count belongs to the constructed native formal hull. -/
def variableCount : ℕ := (formalHull_powerSeries f).choose

/-- The actual scalar-compatible formal-ring model. -/
def powerSeriesEquiv :
    (formalHull f).base ≃ₐ[k] MvPowerSeries (Fin (variableCount f)) k :=
  (formalHull_powerSeries f).choose_spec.some

/-- The actual hull-ring dimension follows from its actually constructed model. -/
theorem formalHull_krullDimension :
    ringKrullDim (formalHull f).base = (variableCount f : WithBot ℕ∞) :=
  PowerSeriesLocalDimension.krullDimension_of_powerSeriesEquiv (powerSeriesEquiv f)

/-- Genus nine pins the tangent dimension of that very formal base, through
its actual hull differential and the original source-deformation classifier. -/
theorem formalHull_tangent_finrank_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    Module.finrank k (tangentSpaceArtinian k k (restrictedCoyoneda (formalHull f).base)) = 24 := by
  let 𝓕 := schemeDeformationBased (Λ := k) (Over.mk f)
  let hp := (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k)
    (Over.mk f)).predeformation
  let hS2 := schlessingerConditionS2_schemeDeformation (Λ := k) (Over.mk f)
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  exact (HullTangentComparison.tangentLinearEquiv 𝓕 hp hS2 (formalHull f)
    (formalHull_isHull f).2).finrank_eq.trans
      (CurveSchemeTangent.liftedTangent_finrank_genus_nine (Λ := k) f hg)

/-- The variable count of the actual constructed formal model is24. -/
theorem formalHull_variableCount_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    variableCount f = 24 := by
  have h := RepresentedPowerSeriesDimension.tangent_finrank_of_model
    (formalHull f).base (powerSeriesEquiv f)
  rw [formalHull_tangent_finrank_genus_nine f hg] at h
  exact h.symm

/-- The original constructed scheme-deformation hull has actual Krull dimension24. -/
theorem formalHull_krullDimension_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    ringKrullDim (formalHull f).base = (24 : WithBot ℕ∞) := by
  rw [formalHull_krullDimension,formalHull_variableCount_genus_nine f hg]
  norm_num

end M9Native.CurveSchemePowerSeries
