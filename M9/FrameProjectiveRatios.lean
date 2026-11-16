module

public import M9.FrameProjectiveGeometry

/-! Normalized affine-ratio formulas for the actual native generic-stalk action. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 400000

namespace M9.FrameProjectiveRatios

open CategoryTheory AlgebraicGeometry MvPolynomial Matrix TopologicalSpace
open ProjectiveFunctionField ProjectiveGeometry FrameProjectiveGeometry

theorem genericPoint_eq_zeroPrime :
    genericPoint matrixSpace = ProjectiveFunctionField.projectiveGenericPoint 8 :=
  (genericPoint_spec matrixSpace).eq (ProjectiveFunctionField.projectiveGenericPoint_dense 8)

theorem genericPoint_mem_basicOpen (f : HomogeneousRing) (hf : f ≠ 0) :
    genericPoint matrixSpace ∈ Proj.basicOpen Grading f := by
  rw [genericPoint_eq_zeroPrime]
  change f ∉ (⊥ : Ideal HomogeneousRing)
  exact fun h => hf (Ideal.mem_bot.mp h)

/-- Restriction of the actual generic stalk is compatible with pullback to
the full source of an open immersion into a specified target open. -/
theorem genericPullback_appLE {Y X : Scheme} [IrreducibleSpace Y] [IrreducibleSpace X]
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens)
    (hU : genericPoint X ∈ U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    X.presheaf.germ U (genericPoint X) hU ≫ (openImmersionFunctionFieldIso f).hom =
      f.appLE U ⊤ h ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  simp only [Scheme.Hom.appLE, Category.assoc]
  rw [Y.presheaf.germ_res]
  exact f.germ_stalkMap U (genericPoint Y) _

theorem chartMap_preimage_coordinateOpen (i : Fin 9) :
    ProjectiveFunctionField.chartMap 8 i ⁻¹ᵁ
      ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i = ⊤ := by
  simp [ProjectiveFunctionField.chartMap, ProjectiveChart.projectiveAffineChartMap]

/-- The original chart immersion pulls a homogeneous-localization section
back to its literal dehomogenized polynomial. -/
theorem chartMap_appLE_awayToSection (i : Fin 9)
    (h : ⊤ ≤ ProjectiveFunctionField.chartMap 8 i ⁻¹ᵁ
      ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i) :
    Proj.awayToSection Grading (X i) ≫
      (ProjectiveFunctionField.chartMap 8 i).appLE
        (ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i) ⊤ h =
      CommRingCat.ofHom (ProjectiveChartToPolynomial.projectiveChartToPolynomial 8 i) ≫
        (Scheme.ΓSpecIso (.of (chartPolynomial 8 i))).inv := by
  let U := ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i
  let e := ProjectiveChart.projectiveCoordinateIsoSpec 8 i
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hcomp := Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (by simp)
  change U.ι.appLE U ⊤ _ ≫ e.inv.appTop =
    (ProjectiveFunctionField.chartMap 8 i).appLE U ⊤ _ at hcomp
  rw [← hcomp, hι, ← Category.assoc]
  change (Proj.awayToSection Grading (X i) ≫ U.topIso.inv) ≫
    ((Spec.map (CommRingCat.ofHom (ProjectiveChartToPolynomial.projectiveChartToPolynomial 8 i)) ≫
      (Proj.basicOpenIsoSpec Grading (X i)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).inv).appTop) = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  have hbasic : Proj.awayToSection Grading (X i) ≫ U.topIso.inv ≫
      (Proj.basicOpenIsoSpec Grading (X i)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).inv.appTop =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away Grading (X i)))).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away Grading (X i)))).hom).mp
    calc
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away Grading (X i)))).hom ≫
          (Proj.awayToSection Grading (X i) ≫ U.topIso.inv ≫
            (Proj.basicOpenIsoSpec Grading (X i)
              (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).inv.appTop) =
        ((Proj.basicOpenIsoSpec Grading (X i)
          (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).inv ≫
          (Proj.basicOpenIsoSpec Grading (X i)
          (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).hom).appTop := by
        rw [Scheme.Hom.comp_appTop]
        change _ = (Proj.basicOpenToSpec Grading (X i)).app ⊤ ≫ _
        rw [Proj.basicOpenToSpec_app_top]
        simp only [Category.assoc]
        rfl
      _ = _ := by simp only [Iso.inv_hom_id, Scheme.Hom.id_appTop, Iso.hom_inv_id]
  have hbasic' : (Proj.awayToSection Grading (X i) ≫ U.topIso.inv) ≫
      (Proj.basicOpenIsoSpec Grading (X i)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) Nat.zero_lt_one).inv.appTop =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away Grading (X i)))).inv := by
    simpa only [Category.assoc] using hbasic
  rw [hbasic']
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

/-- Actual germs of polynomial chart sections in the native projective field. -/
def chartGerm (i : Fin 9) : chartPolynomial 8 i →+* matrixFunctionField :=
  (matrixSpace.presheaf.germ (Proj.basicOpen Grading (X i)) (genericPoint matrixSpace)
      (genericPoint_mem_basicOpen _ (MvPolynomial.X_ne_zero i))).hom.comp
    ((Proj.awayToSection Grading (X i)).hom.comp
      (PolynomialToProjectiveChart.polynomialToProjectiveChart 8 i))

theorem chartGerm_eq_chartPolynomialToFunctionField (i : Fin 9) :
    chartGerm i = chartPolynomialToFunctionField 8 i := by
  apply RingHom.ext
  intro p
  apply (chartFunctionFieldEquiv 8 i).injective
  change (chartFunctionFieldEquiv 8 i) (chartGerm i p) =
    (chartFunctionFieldEquiv 8 i) ((chartFunctionFieldEquiv 8 i).symm
      (algebraMap (chartPolynomial 8 i) (chartScheme 8 i).functionField p))
  rw [AlgEquiv.apply_symm_apply]
  change (openImmersionFunctionFieldIso (ProjectiveFunctionField.chartMap 8 i)).hom
      (chartGerm i p) = algebraMap (chartPolynomial 8 i) (chartScheme 8 i).functionField p
  have hpre : ⊤ ≤ ProjectiveFunctionField.chartMap 8 i ⁻¹ᵁ
      ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i :=
    (chartMap_preimage_coordinateOpen i).ge
  have h := genericPullback_appLE (ProjectiveFunctionField.chartMap 8 i)
    (ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i)
    (genericPoint_mem_basicOpen _ (MvPolynomial.X_ne_zero i)) hpre
  have happ := chartMap_appLE_awayToSection i hpre
  have hh := congrArg (fun k => (Proj.awayToSection Grading (X i)) ≫ k) h
  rw [← Category.assoc (Proj.awayToSection Grading (X i))
    ((ProjectiveFunctionField.chartMap 8 i).appLE
      (ProjectiveCoordinateCover.projectiveCoordinateOpen 8 i) ⊤ hpre)
    ((chartScheme 8 i).presheaf.germ ⊤ (genericPoint (chartScheme 8 i)) (by trivial)), happ] at hh
  have hp := congrArg (fun k : CommRingCat.of (HomogeneousLocalization.Away Grading (X i)) ⟶
      (chartScheme 8 i).functionField =>
        k (PolynomialToProjectiveChart.polynomialToProjectiveChart 8 i p)) hh
  have hpoly := RingHom.congr_fun (PolynomialToProjectiveChart.projectiveChartToPolynomial_comp 8 i) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at hpoly
  change (openImmersionFunctionFieldIso (ProjectiveFunctionField.chartMap 8 i)).hom
      (chartGerm i p) =
    (chartScheme 8 i).presheaf.germ ⊤ (genericPoint (chartScheme 8 i)) (by trivial)
      ((Scheme.ΓSpecIso (.of (chartPolynomial 8 i))).inv
        ((ProjectiveChartToPolynomial.projectiveChartToPolynomial 8 i)
          (PolynomialToProjectiveChart.polynomialToProjectiveChart 8 i p))) at hp
  rw [hpoly] at hp
  exact hp

/-- The native stalk/localization identification at the actual generic point. -/
def stalkCoordinates : matrixFunctionField ≃+*
    HomogeneousLocalization.AtPrime Grading (genericPoint matrixSpace).asHomogeneousIdeal.toIdeal :=
  (Proj.stalkIso Grading (genericPoint matrixSpace)).commRingCatIsoToRingEquiv

def ratioPresentation (f g : HomogeneousRing) (hf : f ∈ Grading 1) (hg : g ∈ Grading 1)
    (hg0 : g ≠ 0) : HomogeneousLocalization.NumDenSameDeg Grading
      (genericPoint matrixSpace).asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨1,⟨f,hf⟩,⟨g,hg⟩,genericPoint_mem_basicOpen g hg0⟩

/-- The actual native generic germ of a homogeneous linear ratio. -/
def ratioGerm (f g : HomogeneousRing) (hf : f ∈ Grading 1) (hg : g ∈ Grading 1)
    (hg0 : g ≠ 0) : matrixFunctionField :=
  matrixSpace.presheaf.germ (Proj.basicOpen Grading g) (genericPoint matrixSpace)
    (genericPoint_mem_basicOpen g hg0)
    (Proj.awayToSection Grading g
      (HomogeneousLocalization.Away.mk Grading hg 1 f (by simpa using hf)))

theorem stalkCoordinates_ratioGerm (f g : HomogeneousRing) (hf : f ∈ Grading 1)
    (hg : g ∈ Grading 1) (hg0 : g ≠ 0) :
    stalkCoordinates (ratioGerm f g hf hg hg0) =
      HomogeneousLocalization.mk (ratioPresentation f g hf hg hg0) := by
  have h := ProjectiveSpectrum.Proj.awayToSection_germ Grading g (genericPoint matrixSpace)
    (genericPoint_mem_basicOpen g hg0)
  have hv := congrArg (fun k => k (HomogeneousLocalization.Away.mk Grading hg 1 f
    (by simpa using hf))) h
  change ratioGerm f g hf hg hg0 =
    stalkCoordinates.symm (HomogeneousLocalization.mapId Grading
      (Submonoid.powers_le.mpr (genericPoint_mem_basicOpen g hg0))
      (HomogeneousLocalization.Away.mk Grading hg 1 f (by simpa using hf))) at hv
  rw [hv, RingEquiv.apply_symm_apply]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.mapId, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, pow_one,
    GradedRingHom.id_apply]
  rfl

@[simp] theorem ratioGerm_self (g : HomogeneousRing) (hg : g ∈ Grading 1) (hg0 : g ≠ 0) :
    ratioGerm g g hg hg hg0 = 1 := by
  apply stalkCoordinates.injective
  rw [stalkCoordinates_ratioGerm, map_one]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self _ _

/-- Cross multiplication is proved inside the actual homogeneous localization. -/
theorem ratioGerm_cross (f g t : HomogeneousRing)
    (hf : f ∈ Grading 1) (hg : g ∈ Grading 1) (ht : t ∈ Grading 1)
    (hg0 : g ≠ 0) (ht0 : t ≠ 0) :
    ratioGerm f t hf ht ht0 = ratioGerm f g hf hg hg0 * ratioGerm g t hg ht ht0 := by
  apply stalkCoordinates.injective
  rw [map_mul, stalkCoordinates_ratioGerm, stalkCoordinates_ratioGerm, stalkCoordinates_ratioGerm]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, ratioPresentation]
  ring

theorem ratioGerm_ne_zero (f g : HomogeneousRing) (hf : f ∈ Grading 1)
    (hg : g ∈ Grading 1) (hf0 : f ≠ 0) (hg0 : g ≠ 0) : ratioGerm f g hf hg hg0 ≠ 0 := by
  intro hz
  have h := ratioGerm_cross g f g hg hf hg hf0 hg0
  rw [ratioGerm_self, hz, mul_zero] at h
  exact one_ne_zero h

theorem ratioGerm_div (f g t : HomogeneousRing)
    (hf : f ∈ Grading 1) (hg : g ∈ Grading 1) (ht : t ∈ Grading 1)
    (hg0 : g ≠ 0) (ht0 : t ≠ 0) :
    ratioGerm f g hf hg hg0 = ratioGerm f t hf ht ht0 / ratioGerm g t hg ht ht0 :=
  (eq_div_iff (ratioGerm_ne_zero g t hg ht hg0 ht0)).mpr
    (ratioGerm_cross f g t hf hg ht hg0 ht0).symm

/-- Normalization is the actual dehomogenizing chart polynomial, numbered
by the original native affine-coordinate equivalence. -/
def normalizedPolynomial (i : Fin 9) (f : HomogeneousRing) : MvPolynomial (Fin 8) ℂ :=
  chartCoordinatesEquiv 8 i (Dehomogenization.dehomogenize i f)

theorem functionFieldEquiv_ratioGerm_coordinateDenominator (i : Fin 9)
    (f : HomogeneousRing) (hf : f ∈ Grading 1) :
    functionFieldEquiv 8 i
      (ratioGerm f (X i) hf (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i)
        (MvPolynomial.X_ne_zero i)) =
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (normalizedPolynomial i f) := by
  have hpoly := PolynomialToProjectiveChart.polynomialToProjectiveChart_dehomogenize 8 i 1 f
    (by simpa using hf)
  have hGerm : ratioGerm f (X i) hf
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) (MvPolynomial.X_ne_zero i) =
      chartGerm i (Dehomogenization.dehomogenize i f) := by
    unfold ratioGerm chartGerm
    simp only [RingHom.comp_apply]
    rw [hpoly]
  rw [hGerm, chartGerm_eq_chartPolynomialToFunctionField, functionFieldEquiv_chartPolynomial]
  rfl

theorem functionFieldEquiv_ratioGerm (i : Fin 9) (f g : HomogeneousRing)
    (hf : f ∈ Grading 1) (hg : g ∈ Grading 1) (hg0 : g ≠ 0) :
    functionFieldEquiv 8 i (ratioGerm f g hf hg hg0) =
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (normalizedPolynomial i f) /
        algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (normalizedPolynomial i g) := by
  rw [ratioGerm_div f g (X i) hf hg
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) hg0 (MvPolynomial.X_ne_zero i),
    map_div₀, functionFieldEquiv_ratioGerm_coordinateDenominator,
    functionFieldEquiv_ratioGerm_coordinateDenominator]

theorem genericPullback_app {Y X : Scheme} [IrreducibleSpace Y] [IrreducibleSpace X]
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : genericPoint X ∈ U) :
    X.presheaf.germ U (genericPoint X) hU ≫ (openImmersionFunctionFieldIso f).hom =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y)
        (by change f (genericPoint Y) ∈ U; rw [genericPoint_eq_of_isOpenImmersion]; exact hU) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint Y) _

/-- Generic-stalk restriction commutes with the original pullback on any open. -/
theorem nativePullback_germ (f : Aut matrixSpace)
    (hf : f.asIso.hom ≫ projection 8 = projection 8)
    (U : matrixSpace.Opens) (hU : genericPoint matrixSpace ∈ U) :
    matrixSpace.presheaf.germ U (genericPoint matrixSpace) hU ≫
        CommRingCat.ofHom (nativePullback f hf).toRingHom =
      f.asIso.hom.app U ≫ matrixSpace.presheaf.germ (f.asIso.hom ⁻¹ᵁ U) (genericPoint matrixSpace)
        (by change f.asIso.hom (genericPoint matrixSpace) ∈ U
            rw [genericPoint_eq_of_isOpenImmersion]; exact hU) :=
  genericPullback_app f.asIso.hom U hU

theorem substitution_injective (B : GL9) : Function.Injective (substitution (B : Matrix9)) := by
  intro p q h
  have heq := congrArg (substitution (↑B⁻¹ : Matrix9)) h
  have hinv : (substitution (↑B⁻¹ : Matrix9)).comp (substitution (B : Matrix9)) =
      GradedRingHom.id Grading := by
    rw [substitution_comp, Units.mul_inv, substitution_one]
  have hp := congrArg (fun k : Grading →+*ᵍ Grading => k p) hinv
  have hq := congrArg (fun k : Grading →+*ᵍ Grading => k q) hinv
  exact hp.symm.trans (heq.trans hq)

/-- The actual native generic-stalk pullback sends a homogeneous ratio to
the ratio of its original transformed numerator and denominator. -/
theorem projectiveLinear_ratioGerm (B : GL9) (f g : HomogeneousRing)
    (hf : f ∈ Grading 1) (hg : g ∈ Grading 1) (hg0 : g ≠ 0) :
    nativePullback (projectiveLinear B) (projectiveLinear_over B) (ratioGerm f g hf hg hg0) =
      ratioGerm (substitution (B : Matrix9) f) (substitution (B : Matrix9) g)
        ((substitution (B : Matrix9)).map_mem hf) ((substitution (B : Matrix9)).map_mem hg)
        (fun h => hg0 ((substitution_injective B) (h.trans (map_zero _).symm))) := by
  let φ := substitution (B : Matrix9)
  have hφg : φ g ≠ 0 := fun h => hg0 ((substitution_injective B) (h.trans (map_zero _).symm))
  have h := nativePullback_germ (projectiveLinear B) (projectiveLinear_over B)
    (Proj.basicOpen Grading g) (genericPoint_mem_basicOpen g hg0)
  have hmap := Proj.awayToSection_comp_appLE φ (substitution_irrelevant_le B) hg
  change Proj.awayToSection Grading g ≫
    (Proj.map φ (substitution_irrelevant_le B)).appLE (Proj.basicOpen Grading g)
      ((Proj.map φ (substitution_irrelevant_le B)) ⁻¹ᵁ Proj.basicOpen Grading g) le_rfl = _ at hmap
  rw [Scheme.Hom.appLE_eq_app] at hmap
  have hh := congrArg (fun k => Proj.awayToSection Grading g ≫ k) h
  change Proj.awayToSection Grading g ≫
      matrixSpace.presheaf.germ (Proj.basicOpen Grading g) (genericPoint matrixSpace) _ ≫
        CommRingCat.ofHom (nativePullback (projectiveLinear B) (projectiveLinear_over B)).toRingHom =
    Proj.awayToSection Grading g ≫ (Proj.map φ (substitution_irrelevant_le B)).app
      (Proj.basicOpen Grading g) ≫ matrixSpace.presheaf.germ (Proj.basicOpen Grading (φ g))
        (genericPoint matrixSpace) (genericPoint_mem_basicOpen _ hφg) at hh
  rw [← Category.assoc (Proj.awayToSection Grading g)
    ((Proj.map φ (substitution_irrelevant_le B)).app (Proj.basicOpen Grading g))
    (matrixSpace.presheaf.germ (Proj.basicOpen Grading (φ g))
      (genericPoint matrixSpace) (genericPoint_mem_basicOpen _ hφg)), hmap] at hh
  have hp := congrArg (fun k : CommRingCat.of (HomogeneousLocalization.Away Grading g) ⟶
      matrixFunctionField => k (HomogeneousLocalization.Away.mk Grading hg 1 f
        (by simpa using hf))) hh
  change nativePullback (projectiveLinear B) (projectiveLinear_over B) (ratioGerm f g hf hg hg0) =
    matrixSpace.presheaf.germ (Proj.basicOpen Grading (φ g)) (genericPoint matrixSpace)
      (genericPoint_mem_basicOpen _ hφg)
      (Proj.awayToSection Grading (φ g) (HomogeneousLocalization.Away.map φ g
        (HomogeneousLocalization.Away.mk Grading hg 1 f (by simpa using hf)))) at hp
  rw [HomogeneousLocalization.Away.map_mk] at hp
  exact hp

theorem coordinateRatio_eq_ratioGerm (i : Fin 9) (a : Fin 8) :
    coordinateRatio 8 i a =
      ratioGerm (X (finSuccAboveEquiv i a)) (X i)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 (finSuccAboveEquiv i a))
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 8 i) (MvPolynomial.X_ne_zero i) := by
  rw [coordinateRatio, ← chartGerm_eq_chartPolynomialToFunctionField]
  unfold chartGerm ratioGerm
  simp only [RingHom.comp_apply, PolynomialToProjectiveChart.polynomialToProjectiveChart_X,
    PolynomialToProjectiveChart.projectiveChartRatio]

/-- The normalized affine-coordinate formula for the actual native frame
action: numerator and denominator are the original transformed linear forms. -/
theorem functionFieldEquiv_fieldRepresentation_coordinateRatio (w : W) (i : Fin 9) (a : Fin 8) :
    functionFieldEquiv 8 i (fieldRepresentation w (coordinateRatio 8 i a)) =
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (normalizedPolynomial i (linearForms (matrixRepresentation w⁻¹ : Matrix9) (finSuccAboveEquiv i a))) /
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (normalizedPolynomial i (linearForms (matrixRepresentation w⁻¹ : Matrix9) i)) := by
  rw [coordinateRatio_eq_ratioGerm]
  change functionFieldEquiv 8 i
    (nativePullback (projectiveLinear (matrixRepresentation w⁻¹))
      (projectiveLinear_over (matrixRepresentation w⁻¹)) _) = _
  rw [projectiveLinear_ratioGerm, functionFieldEquiv_ratioGerm]
  simp only [substitution_X]

/-- The same exact formula in the chart's rational-field coordinates. -/
theorem fieldRepresentation_normalized (w : W) (i : Fin 9) (a : Fin 8) :
    functionFieldEquiv 8 i
      (fieldRepresentation w ((functionFieldEquiv 8 i).symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (X a)))) =
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (normalizedPolynomial i (linearForms (matrixRepresentation w⁻¹ : Matrix9) (finSuccAboveEquiv i a))) /
      algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (normalizedPolynomial i (linearForms (matrixRepresentation w⁻¹ : Matrix9) i)) := by
  have h : (functionFieldEquiv 8 i).symm
      (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (X a)) = coordinateRatio 8 i a := by
    apply (functionFieldEquiv 8 i).injective
    rw [AlgEquiv.apply_symm_apply, functionFieldEquiv_coordinateRatio]
  rw [h]
  exact functionFieldEquiv_fieldRepresentation_coordinateRatio w i a

end M9.FrameProjectiveRatios
