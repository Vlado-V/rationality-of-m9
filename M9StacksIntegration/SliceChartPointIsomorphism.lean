module

public import M9StacksIntegration.PointedParameterDeformation

/-!
# Equal original chart maps give isomorphic represented slice tests

This uses the native reversed morphism of pointed deformations and the
genuine cofibered-in-groupoids structure of the represented slice.  The
isomorphism lies in the original fibre over the same Artinian algebra.

The map comparison is the chart-free specialization of the proof in the
pinned native `StacksFrontier.Deformation.Artin.SliceTangentSpace` (Apache-2.0),
using its public `exists_morphism_of_deformationMap_eq`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Deformation
open Deformation.Artin Deformation.Artin.SliceTangent

universe u

namespace M9Native.SliceChartPointIsomorphism

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V : BigFppfOver B S hS}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {iΛ : Spec (.of Λ) ⟶ S} {v₀ : Over V}
  {hv₀ : (Over.forget V ⋙ Over.post B.inclusion).obj v₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Equal original chart maps give a genuine reversed deformation morphism. -/
theorem exists_morphism_of_chartPointMap_eq
    {a b : DeformationObject iΛ (Over.forget V ⋙ Over.post B.inclusion) v₀ hv₀}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (ha : a.algebra = A) (hb : b.algebra = A)
    (h : chartPointMap a ha = chartPointMap b hb) :
    ∃ m : DeformationMorphism iΛ (Over.forget V ⋙ Over.post B.inclusion) v₀ hv₀ a b,
      m.ringHom = eqToHom (ha.trans hb.symm) := by
  apply exists_morphism_of_deformationMap_eq
  subst hb
  rw [chartPointMap, chartPointMap, eqToHom_refl, specMap_id, Category.id_comp] at h
  rw [← h]

/-- The original represented slice has its actual native groupoid fibres. -/
theorem projection_cofibered : IsCofiberedInGroupoids (sliceBased iΛ v₀ hv₀).p :=
  (predeformationCategory_isPredeformationCategory B hS iΛ
    (Over.forget V) v₀ hv₀ (Functor.IsFiberedInGroupoids.over_forget V)).cofibered

/-- Same chart map means isomorphism in the same original Artinian fibre. -/
def isoOfChartPointMapEq
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (a b : (sliceBased iΛ v₀ hv₀).p.Fiber A)
    (h : chartPointMap a.val a.property = chartPointMap b.val b.property) : a ≅ b := by
  let hex := exists_morphism_of_chartPointMap_eq a.property b.property h
  let m := Classical.choose hex
  have hm := Classical.choose_spec hex
  have hlift : (sliceBased iΛ v₀ hv₀).p.IsHomLift (𝟙 A) m := by
    apply IsHomLift.of_fac' (sliceBased iΛ v₀ hv₀).p (𝟙 A) m
      a.property b.property
    change m.ringHom = _
    simpa only [Category.id_comp, Category.comp_id, eqToHom_trans] using hm
  exact Functor.Fiber.isoMk (isoOfIsHomLiftId projection_cofibered m hlift) hlift

/-- In particular these are genuinely isomorphic objects of the original fibre. -/
theorem isIsomorphic_of_chartPointMap_eq
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (a b : (sliceBased iΛ v₀ hv₀).p.Fiber A)
    (h : chartPointMap a.val a.property = chartPointMap b.val b.property) :
    Nonempty (a ≅ b) := ⟨isoOfChartPointMapEq a b h⟩

/-- The converse follows from the original morphism formula, without a chart. -/
theorem chartPointMap_eq_of_iso
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {a b : (sliceBased iΛ v₀ hv₀).p.Fiber A} (e : a ≅ b) :
    chartPointMap a.val a.property = chartPointMap b.val b.property := by
  have : (sliceBased iΛ v₀ hv₀).p.IsHomLift (𝟙 A) e.hom.val := e.hom.property
  have hm := IsHomLift.fac' (sliceBased iΛ v₀ hv₀).p (𝟙 A) e.hom.val
  have h := chartPointMap_of_morphism a.property b.property e.hom.val (𝟙 A) hm
  simpa only [specMap_id, Category.id_comp] using h.symm

/-- Equality of the actual maps exactly detects isomorphism of original tests. -/
theorem chartPointMap_eq_iff_isIsomorphic
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (a b : (sliceBased iΛ v₀ hv₀).p.Fiber A) :
    chartPointMap a.val a.property = chartPointMap b.val b.property ↔ Nonempty (a ≅ b) :=
  ⟨isIsomorphic_of_chartPointMap_eq a b, fun ⟨e⟩ => chartPointMap_eq_of_iso e⟩

end M9Native.SliceChartPointIsomorphism
