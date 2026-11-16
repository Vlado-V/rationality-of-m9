module

public import Mathlib.Basic.Complex.Basic
public import M9StacksIntegration.GenusNineMukaiLinearSection
public import M9StacksIntegration.LagrangianGoodOpenFieldBaseChange

@[expose] public section

/-!
# Original good complex-family fibres for arbitrary extension-field curves

The same-field Mukai producer constructs the whole native L-fibre from
an original genus-nine curve with no degree-five pencil. The actual
cartesian incidence family and smooth-locus reflection then construct
its parameter in the unchanged original good K-family. All field and
parameter triangles are retained; no fibre isomorphism or good-open
membership is supplied as a premise.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.GenusNineMukaiCrossField
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianIncidenceParameterBaseChange LagrangianGoodOpenFieldBaseChange

variable {K L : Type u} [Field K] [Field L] [CharZero L] [IsAlgClosed L]
  (φ : K →+* L) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of L)) [IsCurve L f] [IsProper f] [Smooth f]

/-- The constructed native parameter and original good-family parameter
satisfy the exact field-base-change triangle. The entire original curve
is the original restricted-family fibre over its unchanged Spec L base. -/
theorem exists_goodParameterMap_fibreIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries L f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (pL : Spec (.of L) ⟶ parameter L)
      (pK : Spec (.of L) ⟶ (goodOpen K).toScheme)
      (e : X ≅ pullback (restrictedProjection K) pK),
      pK ≫ (goodOpen K).ι = parameterMap K L (Spec.map (CommRingCat.ofHom φ)) pL ∧
      pL ≫ parameterProjection L = 𝟙 _ ∧
      (∀ t : Spec (.of L), pL t ∈ goodOpen L) ∧
      pK ≫ (goodOpen K).ι ≫ parameterProjection K = Spec.map (CommRingCat.ofHom φ) ∧
      e.hom ≫ pullback.snd (restrictedProjection K) pK = f := by
  obtain ⟨pL,hpL,hgood,e,he⟩ :=
    GenusNineMukaiLinearSection.exists_good_fibreIso L f hg hnp
  let pK := goodParameter φ pL hgood
  refine ⟨pL,pK,e ≪≫ nativeGoodFibreIso φ pL hgood,
    goodParameter_comp φ pL hgood,hpL,hgood,?_,?_⟩
  · rw [← Category.assoc, goodParameter_comp, parameterMap_projection,
      ← Category.assoc, hpL, Category.id_comp]
  · change (e.hom ≫ (nativeGoodFibreIso φ pL hgood).hom) ≫
      pullback.snd (restrictedProjection K) (goodParameter φ pL hgood) = f
    rw [Category.assoc, nativeGoodFibreIso_hom_base]
    exact he

/-- Every original nonpentagonal genus-nine extension-field curve is an
actual fibre of the original good family, with the original field map. -/
theorem exists_original_goodFibreIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries L f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (p : Spec (.of L) ⟶ (goodOpen K).toScheme)
      (e : X ≅ pullback (restrictedProjection K) p),
      p ≫ (goodOpen K).ι ≫ parameterProjection K = Spec.map (CommRingCat.ofHom φ) ∧
      e.hom ≫ pullback.snd (restrictedProjection K) p = f := by
  obtain ⟨_,p,e,_,_,_,hp,he⟩ := exists_goodParameterMap_fibreIso φ f hg hnp
  exact ⟨p,e,hp,he⟩

/-- The actual original complex family covers every original algebraically
closed characteristic-zero extension-field curve with genus nine and no
pencil of degree five. Its native L-parameter and all original triangles
are part of the conclusion. -/
theorem exists_complex_goodParameterMap_fibreIso
    (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (φ : ℂ →+* L)
    {X : Scheme} (f : X ⟶ Spec (.of L)) [IsCurve L f] [IsProper f] [Smooth f]
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries L f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (pL : Spec (.of L) ⟶ parameter L)
      (pC : Spec (.of L) ⟶ (goodOpen ℂ).toScheme)
      (e : X ≅ pullback (restrictedProjection ℂ) pC),
      pC ≫ (goodOpen ℂ).ι = parameterMap ℂ L (Spec.map (CommRingCat.ofHom φ)) pL ∧
      pL ≫ parameterProjection L = 𝟙 _ ∧
      (∀ t : Spec (.of L), pL t ∈ goodOpen L) ∧
      pC ≫ (goodOpen ℂ).ι ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom φ) ∧
      e.hom ≫ pullback.snd (restrictedProjection ℂ) pC = f :=
  exists_goodParameterMap_fibreIso φ f hg hnp

end M9Native.GenusNineMukaiCrossField
