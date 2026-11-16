module

public import M9StacksIntegration.LagrangianPluckerEpimorphism
public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.ProjectiveSectionFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange

/-!
# The native projective map of the actual fourteen determinant sections

The actual universal determinant sections generate the actual determinant
line.  Their native projective morphism is identified with the already
constructed primitive Plucker embedding by the literal determinant
coordinates on the genuine affine matrix cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianPluckerGeneration

open AlgebraicGeometry.Grassmannian
open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerTrivialization LagrangianPluckerEpimorphism
open LagrangianSectionGeneration LagrangianAffineDeterminant
open LagrangianDeterminantSections
open Stacks.ProjectiveFromSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

/-- The actual section-map dictionary also gives epimorphy from native
stalk generation. -/
theorem sectionMap_epi_of_generatesStalks {X : Scheme.{u}} {Q : X.Modules}
    [Stacks.Ample.IsInvertibleModule X Q] {r : ℕ} (s : Fin r → Γ(Q, ⊤))
    (hs : GeneratesStalks s) : Epi (sectionMap X Q s) := by
  have he := epi_freeHomEquiv_symm_of_generatesStalks
    (fun i : ULift.{u} (Fin r) => s i.down) ((generatesStalks_ulift_iff s).mpr hs)
  exact (sectionMap_eq_freeHomEquiv X Q s).symm ▸ he

/-- Source naturality over the same original base. -/
theorem comp_toProjectiveSpaceOver_sameBase {X T S : Scheme.{u}} {Q : X.Modules}
    [Stacks.Ample.IsInvertibleModule X Q] {n : ℕ}
    (s : Fin (n + 1) → Γ(Q, ⊤)) (hs : GeneratesStalks s)
    (f : T ⟶ X) (p : X ⟶ S)
    (ht : GeneratesStalks fun j => pullbackGlobalSections f Q (s j)) :
    f ≫ toProjectiveSpaceOver s hs p =
      toProjectiveSpaceOver (fun j => pullbackGlobalSections f Q (s j)) ht (f ≫ p) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, toProjectiveSpaceOver_fst]
  · simp only [Category.assoc, toProjectiveSpaceOver_snd]
    exact comp_toProjectiveSpaceAtUniverse s hs f ht

variable (K : Type u) [Field K]

instance determinantLine_isInvertibleModule :
    Stacks.Ample.IsInvertibleModule (space K) (determinantLine K) :=
  isInvertibleModule_of_isFiniteLocallyFreeOfRank_one (determinantLine K)

instance pulledDeterminantLine_isInvertibleModule {T : Scheme.{u}} (f : T ⟶ space K) :
    Stacks.Ample.IsInvertibleModule T ((Scheme.Modules.pullback f).obj (determinantLine K)) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback f (determinantLine K)

/-- The genuine affine chart trivialization of the actual determinant line. -/
def chartLineIso {T : Scheme.{u}} [IsAffine T] (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι) :
    (Scheme.Modules.pullback f).obj (determinantLine K) ≅ ProjectiveSectionFunctions.UnitLine T :=
  chartDeterminantIso K f ι g hfg ≪≫ affineDeterminantIso T

/-- This actual line isomorphism carries the original fourteen pulled
sections to their literal primitive Plucker chart functions. -/
theorem chartLineIso_primitive {T : Scheme.{u}} [IsAffine T] (f : T ⟶ space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι) (j : Fin 14) :
    (chartLineIso K f ι g hfg).hom.app ⊤
        (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) =
      LagrangianPlucker.chartCoordinates K f ι g j := by
  exact (affineDeterminantIso_coordinate T
    ((chartDeterminantIso K f ι g hfg).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))).trans
    (chartDeterminantIso_primitive_coordinates K f ι g hfg j)

/-- The determinant of every actual isomorphic test-scheme quotient is
rank one; the result is derived from the literal universal quotient. -/
theorem transportedDeterminant_rank {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (Scheme.Modules.exteriorPower Q 3) 1 := by
  have hp : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback f).obj (determinantLine K)) 1 :=
    isFiniteLocallyFreeOfRank_pullback f.base f.toRingCatSheafHom
      (determinantLine K) 1 (determinantLine_rank K)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (determinantTransportIso K f e) hp

/-- Invertibility of the test determinant is an actual consequence of
its isomorphism to the universal determinant pullback. -/
theorem transportedDeterminant_isInvertibleModule {T : Scheme.{u}} (f : T ⟶ space K)
    {Q : T.Modules} (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    Stacks.Ample.IsInvertibleModule T (Scheme.Modules.exteriorPower Q 3) := by
  let := transportedDeterminant_rank K f e
  exact isInvertibleModule_of_isFiniteLocallyFreeOfRank_one _

variable [CharZero K]

/-- The actual generating tuple, with no generation premise. -/
def primitiveTuple : Stacks.ProjectiveSpaceModuli.GeneratingTuple (space K) 13 :=
  ⟨determinantLine K, inferInstance, primitiveSections K, primitiveSections_generatesStalks K⟩

/-- The original determinant family generates after every actual scheme pullback. -/
theorem pulledPrimitiveSections_generatesStalks {T : Scheme.{u}} (f : T ⟶ space K) :
    GeneratesStalks fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j) :=
  (Stacks.ProjectiveSpaceModuli.pullbackTuple f (primitiveTuple K)).generates

/-- The chart functions generate the actual unit line by actual transport
of the genuine universal section quotient. -/
theorem chartCoordinates_generatesStalks {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι) :
    GeneratesStalks (show Fin 14 → Γ(ProjectiveSectionFunctions.UnitLine T, ⊤)
      from LagrangianPlucker.chartCoordinates K f ι g) := by
  let sf := fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j)
  let := sectionMap_epi_of_generatesStalks sf (pulledPrimitiveSections_generatesStalks K f)
  have hep : Epi (sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
      (chartLineIso K f ι g hfg).hom) := inferInstance
  have hmap : sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
        (chartLineIso K f ι g hfg).hom =
      sectionMap T (ProjectiveSectionFunctions.UnitLine T)
        (LagrangianPlucker.chartCoordinates K f ι g) :=
    (sectionMap_postcomp T sf (chartLineIso K f ι g hfg).hom).trans
      (congrArg (sectionMap T (ProjectiveSectionFunctions.UnitLine T))
        (funext fun j => chartLineIso_primitive K f ι g hfg j))
  exact generatesStalks_of_sectionMap_epi T _ _ (hmap ▸ hep)

/-- On each genuine affine matrix chart, the projective morphism of the
actual determinant sections is the literal chart-function morphism. -/
theorem comp_determinantProjectiveMap {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι) :
    f ≫ toProjectiveSpaceOver (primitiveSections K) (primitiveSections_generatesStalks K)
        (projection K) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (LagrangianPlucker.chartCoordinates K f ι g)
        (LagrangianPlucker.chartCoordinates_span K f ι g hfg) (f ≫ projection K) := by
  calc
    _ = toProjectiveSpaceOver
        (fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j))
        (pulledPrimitiveSections_generatesStalks K f) (f ≫ projection K) :=
      comp_toProjectiveSpaceOver_sameBase (primitiveSections K)
        (primitiveSections_generatesStalks K) f (projection K)
        (pulledPrimitiveSections_generatesStalks K f)
    _ = toProjectiveSpaceOver
        (show Fin 14 → Γ(ProjectiveSectionFunctions.UnitLine T, ⊤)
          from LagrangianPlucker.chartCoordinates K f ι g)
        (chartCoordinates_generatesStalks K f ι g hfg) (f ≫ projection K) :=
      ProjectiveSectionIso.toProjectiveSpaceOver_iso _ _
        (pulledPrimitiveSections_generatesStalks K f)
        (chartCoordinates_generatesStalks K f ι g hfg)
        (chartLineIso K f ι g hfg) (chartLineIso_primitive K f ι g hfg) (f ≫ projection K)
    _ = _ := ProjectiveSectionFunctions.toProjectiveSpaceOver_unit
      (LagrangianPlucker.chartCoordinates K f ι g) (chartCoordinates_generatesStalks K f ι g hfg)
      (LagrangianPlucker.chartCoordinates_span K f ι g hfg) (f ≫ projection K)

/-- The native projective evaluation of the original fourteen determinant
sections is exactly the actual primitive Plucker embedding. -/
theorem primitivePlucker_eq_toProjectiveSpaceOver :
    LagrangianPlucker.primitivePlucker K =
      toProjectiveSpaceOver (primitiveSections K) (primitiveSections_generatesStalks K)
        (projection K) := by
  apply (LagrangianPlucker.matrixCover K).hom_ext
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  let := matrixCover_chart_isAffine K ι
  exact (LagrangianPluckerClosed.comp_primitivePlucker K
    ((LagrangianPlucker.matrixCover K).f ι) ι (LagrangianPlucker.matrixChartIntegral K ι)
    (LagrangianPlucker.matrixChartIntegral_diagram K ι)).trans
    (comp_determinantProjectiveMap K ((LagrangianPlucker.matrixCover K).f ι) ι
      (LagrangianPlucker.matrixChartIntegral K ι)
      (LagrangianPlucker.matrixChartIntegral_diagram K ι)).symm

/-- The same exact equality on the integral projective model. -/
theorem integralPrimitivePlucker_eq_toProjectiveSpaceAtUniverse :
    LagrangianPlucker.integralPrimitivePlucker K =
      toProjectiveSpaceAtUniverse (primitiveSections K) (primitiveSections_generatesStalks K) := by
  have h := congrArg (fun f => f ≫ pullback.snd _ _)
    (primitivePlucker_eq_toProjectiveSpaceOver K)
  simpa only [LagrangianPlucker.primitivePlucker_toIntegral, toProjectiveSpaceOver_snd] using h

/-- On every test scheme, the actual primitive Plucker map is the native
projective map of the original determinant sections of the transported
actual quotient. -/
theorem comp_primitivePlucker_eq_toProjectiveSpaceOver {T : Scheme.{u}}
    (f : T ⟶ space K) {Q : T.Modules}
    [Stacks.Ample.IsInvertibleModule T (Scheme.Modules.exteriorPower Q 3)]
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    f ≫ LagrangianPlucker.primitivePlucker K =
      toProjectiveSpaceOver
        (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
          ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom))
        (primitiveSection_generatesStalks K f e) (f ≫ projection K) := by
  calc
    _ = f ≫ toProjectiveSpaceOver (primitiveSections K) (primitiveSections_generatesStalks K)
        (projection K) := congrArg (fun q => f ≫ q) (primitivePlucker_eq_toProjectiveSpaceOver K)
    _ = toProjectiveSpaceOver
        (fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j))
        (pulledPrimitiveSections_generatesStalks K f) (f ≫ projection K) :=
      comp_toProjectiveSpaceOver_sameBase (primitiveSections K)
        (primitiveSections_generatesStalks K) f (projection K)
        (pulledPrimitiveSections_generatesStalks K f)
    _ = _ := ProjectiveSectionIso.toProjectiveSpaceOver_iso _ _
      (pulledPrimitiveSections_generatesStalks K f) (primitiveSection_generatesStalks K f e)
      (determinantTransportIso K f e) (determinantTransportIso_primitive K f e) (f ≫ projection K)

/-- The genuine integral Plucker pullback of the actual twisting sheaf
has precisely the original fourteen determinant sections. -/
theorem exists_integralDeterminantLineIso :
    ∃ e : (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13) ≅ determinantLine K,
      ∀ j, e.hom.app ⊤
        (Stacks.TwistPullbackPinned.pullbackCoordSection
          (LagrangianPlucker.integralPrimitivePlucker K) j) = primitiveSections K j := by
  apply Stacks.ProjectiveSpaceModuli.isomorphic_tautological_of_isPinned (t := primitiveTuple K)
  intro j
  rw [integralPrimitivePlucker_eq_toProjectiveSpaceAtUniverse K]
  exact ι_toProjectiveSpaceAtUniverse (primitiveSections K) (primitiveSections_generatesStalks K) j

/-- The actual twisting-line isomorphism, retaining the original section
coordinates rather than only an equality of abstract line classes. -/
def integralDeterminantLineIso :
    (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13) ≅ determinantLine K :=
  Classical.choose (exists_integralDeterminantLineIso K)

theorem integralDeterminantLineIso_coordinate (j : Fin 14) :
    (integralDeterminantLineIso K).hom.app ⊤
      (Stacks.TwistPullbackPinned.pullbackCoordSection
        (LagrangianPlucker.integralPrimitivePlucker K) j) = primitiveSections K j :=
  Classical.choose_spec (exists_integralDeterminantLineIso K) j

/-- The actual projective hyperplane line pulled back along the actual
primitive Plucker embedding is the actual universal quotient determinant. -/
def determinantLineO1Iso :
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of K))) ≅
        determinantLine K :=
  (Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
      (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).app
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13) ≪≫
    (Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).app
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13) ≪≫
        integralDeterminantLineIso K

/-- The actual O(1) identification over the base field retains each
original homogeneous coordinate. -/
theorem determinantLineO1Iso_coordinate (j : Fin 14) :
    (determinantLineO1Iso K).hom.app ⊤
      (pullbackGlobalSections (LagrangianPlucker.primitivePlucker K)
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of K)))
        (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13)
          (Stacks.TwistPullbackPinned.coordGlobalSection.{u} 13 j))) = primitiveSections K j := by
  let M := Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13
  let p := LagrangianPlucker.primitivePlucker K
  let q := projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K))
  let s := Stacks.TwistPullbackPinned.coordGlobalSection.{u} 13 j
  have hc := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp p q M s
  have hn := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr
    (LagrangianPlucker.primitivePlucker_toIntegral K) M s
  have h := (congrArg (fun t =>
      ((Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).hom.app M).app ⊤ t)
    hc).trans hn
  exact (congrArg ((integralDeterminantLineIso K).hom.app ⊤) h).trans
    (integralDeterminantLineIso_coordinate K j)

end M9Native.LagrangianPluckerGeneration
