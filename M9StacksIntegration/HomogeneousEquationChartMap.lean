module

public import M9StacksIntegration.HomogeneousEquationChart
public import M9StacksIntegration.SplitQuadricChartCoordinates

/-! A genuine polynomial presentation of a homogeneous zero-scheme
chart identifies that full chart with Spec of its presented ring. The
actual ambient coordinate map and its closed-immersion kernel are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveChart

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.HomogeneousEquationChartMap

variable (K : Type u) [CommRing K] (n d : ℕ)
    {ι : Type v} [Finite ι] (F : ι → polyGrading K n d) (p : Fin (n+1))
    (R : Type u) [CommRing R] (χ : MvPolynomial (Fin n) K →+* R)
    (hχ : Function.Surjective χ)
    (hker : RingHom.ker χ = HomogeneousEquationChart.chartIdeal K n d F p)

def chartRingIso :
    Γ((HomogeneousEquationChart.ideal K n d F).subscheme,
      subschemeChart (HomogeneousEquationChart.inclusion K n d F) p) ≃+* R :=
  (HomogeneousEquationChart.chartQuotientEquiv K n d F p).symm.trans
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hχ))

theorem chartRingIso_presentation (a : MvPolynomial (Fin n) K) :
    chartRingIso K n d F p R χ hχ hker
      (chartPresentation (HomogeneousEquationChart.inclusion K n d F) p a) = χ a := by
  have hq : HomogeneousEquationChart.chartQuotientEquiv K n d F p
      (Ideal.Quotient.mk (HomogeneousEquationChart.chartIdeal K n d F p) a) =
      chartPresentation (HomogeneousEquationChart.inclusion K n d F) p a := by
    simp only [HomogeneousEquationChart.chartQuotientEquiv, RingEquiv.trans_apply,
      Ideal.quotEquivOfEq_mk]
    rfl
  rw [← hq]
  change ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hχ))
    ((HomogeneousEquationChart.chartQuotientEquiv K n d F p).symm
      (HomogeneousEquationChart.chartQuotientEquiv K n d F p
        (Ideal.Quotient.mk _ a))) = χ a
  rw [RingEquiv.symm_apply_apply]
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def schemeIso :
    (subschemeChart (HomogeneousEquationChart.inclusion K n d F) p).toScheme ≅ Spec (.of R) :=
  (isAffineOpen_subschemeChart (HomogeneousEquationChart.inclusion K n d F) p).isoSpec ≪≫
    (Scheme.Spec.mapIso (chartRingIso K n d F p R χ hχ hker).toCommRingCatIso.op).symm

theorem schemeIso_inv_value
    (r : Γ((HomogeneousEquationChart.ideal K n d F).subscheme,
      subschemeChart (HomogeneousEquationChart.inclusion K n d F) p)) :
    (schemeIso K n d F p R χ hχ hker).inv.appTop
        ((subschemeChart (HomogeneousEquationChart.inclusion K n d F) p).topIso.inv r) =
      (Scheme.ΓSpecIso (.of R)).inv (chartRingIso K n d F p R χ hχ hker r) := by
  rw [schemeIso, Iso.trans_inv, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Spec.map (CommRingCat.ofHom (chartRingIso K n d F p R χ hχ hker).toRingHom)).appTop
    ((isAffineOpen_subschemeChart (HomogeneousEquationChart.inclusion K n d F) p).isoSpec.inv.appTop
      ((subschemeChart (HomogeneousEquationChart.inclusion K n d F) p).topIso.inv r)) = _
  rw [IsAffineOpen.isoSpec_inv_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (chartRingIso K n d F p R χ hχ hker).toRingHom)) r).symm

abbrev ambientOpen : (AlgebraicGeometry.Proj (polyGrading K n)).Opens :=
  Proj.basicOpen (polyGrading K n) (MvPolynomial.X p)

def ambientMap : Spec (.of R) ⟶ (ambientOpen K n p).toScheme :=
  (schemeIso K n d F p R χ hχ hker).inv ≫
    (HomogeneousEquationChart.inclusion K n d F ∣_ ambientOpen K n p)

/-- Every actual ambient coordinate has the original presentation value. -/
theorem ambientMap_presentation (a : MvPolynomial (Fin n) K) :
    (ambientMap K n d F p R χ hχ hker).appTop
        ((ambientOpen K n p).topIso.inv (sectionsChartEquiv K p a)) =
      (Scheme.ΓSpecIso (.of R)).inv (χ a) := by
  rw [ambientMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hr := SplitQuadricChartCoordinates.morphismRestrict_scalar
    (HomogeneousEquationChart.inclusion K n d F) (ambientOpen K n p) (sectionsChartEquiv K p a)
  exact (congrArg (fun r => (schemeIso K n d F p R χ hχ hker).inv.appTop r) hr).trans
    ((schemeIso_inv_value K n d F p R χ hχ hker
      (chartPresentation (HomogeneousEquationChart.inclusion K n d F) p a)).trans
        (congrArg (fun r => (Scheme.ΓSpecIso (.of R)).inv r)
          (chartRingIso_presentation K n d F p R χ hχ hker a)))

/-- The full closed immersion represented by the genuine chart has the
actual restricted equation ideal, with no radical or point comparison. -/
theorem ambientMap_kernel : (ambientMap K n d F p R χ hχ hker).ker =
    (HomogeneousEquationChart.ideal K n d F).comap (ambientOpen K n p).ι := by
  rw [ambientMap, Scheme.Hom.ker_comp_of_isIso]
  let H := isPullback_morphismRestrict (HomogeneousEquationChart.inclusion K n d F)
    (ambientOpen K n p)
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    HomogeneousEquationChart.inclusion, Scheme.IdealSheafData.ker_subschemeι]

end M9Native.HomogeneousEquationChartMap
