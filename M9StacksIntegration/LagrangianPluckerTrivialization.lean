module

public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.LagrangianDeterminantPullback
public import M9StacksIntegration.LagrangianPrimitiveSectionsPullback

/-! Actual matrix-chart trivializations of the universal determinant line,
and generation of its literal primitive Plucker sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
namespace M9Native.LagrangianPluckerTrivialization
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianPullback M9Native.LagrangianDeterminantSections
open M9Native.LagrangianDeterminantPullback M9Native.LagrangianPluckerQuotient
open AlgebraicGeometry.Grassmannian

/-- The actual presentation isomorphism follows from the proved naturality
of the representing quotient functor. -/
theorem pullbackPresentation_comp_isomorphic {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {k n : ℕ} (q : QuotientPresentation X k n) :
    (pullbackPresentation g (pullbackPresentation f q)).Isomorphic
      (pullbackPresentation (g ≫ f) q) :=
  presentation_isomorphic_of_class_eq
    (congrFun (pullbackPointsMap_comp f g k n) (⟦q⟧ : Points X k n)).symm

variable (K : Type u) [Field K]

/-- The actual quotient on LG, pulled to a native matrix chart, is the
literal normalized chart quotient with its quotient map preserved. -/
theorem quotientOnLG_chart_isomorphic {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    ∃ e : (pullbackPresentation f (quotientOnLG K)).target ≅ freeOn T 3,
      (pullbackPresentation f (quotientOnLG K)).map ≫ e.hom=chartQuotientMap 3 6 ι g := by
  obtain ⟨e₁,h₁⟩ := pullbackPresentation_comp_isomorphic (inclusion K) f (universalQuotient K)
  obtain ⟨e₂,h₂⟩ := pullbackUniversal_chart_isomorphic K (f ≫ inclusion K) ι g hfg
  refine ⟨e₁.trans e₂,?_⟩
  rw [Iso.trans_hom,← Category.assoc,h₁,h₂]

def chartQuotientIso {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    (pullbackPresentation f (quotientOnLG K)).target ≅ freeOn T 3 :=
  Classical.choose (quotientOnLG_chart_isomorphic K f ι g hfg)

theorem chartQuotientIso_triangle {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    (pullbackPresentation f (quotientOnLG K)).map ≫ (chartQuotientIso K f ι g hfg).hom=
      chartQuotientMap 3 6 ι g :=
  Classical.choose_spec (quotientOnLG_chart_isomorphic K f ι g hfg)

/-- The actual pulled determinant line is identified with the actual
third exterior power of the native free rank-three quotient. -/
def chartDeterminantIso {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    (Scheme.Modules.pullback f).obj (determinantLine K) ≅ Scheme.Modules.exteriorPower (freeOn T 3) 3 := by
  let e := chartQuotientIso K f ι g hfg
  haveI : IsIso (exteriorPowerMap T e.hom 3) := by
    rw [exteriorPowerMap_eq_native]
    infer_instance
  exact (exteriorPullbackIso f (quotientOnLG K).target 3).trans (asIso (exteriorPowerMap T e.hom 3))

/-- The chart determinant isomorphism retains every actual quotient minor. -/
theorem chartDeterminantIso_minor {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) (c : Fin 3 ↪ Fin 6) :
    (chartDeterminantIso K f ι g hfg).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (minorSection (space K) (quotientOnLG K).map c))=
      minorSection T (chartQuotientMap 3 6 ι g) c := by
  change (exteriorPowerMap T (chartQuotientIso K f ι g hfg).hom 3).app ⊤
    ((exteriorPullbackIso f (quotientOnLG K).target 3).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (minorSection (space K) (quotientOnLG K).map c)))=_
  rw [minorSection_pullback]
  exact (minorSection_postcomp T (pullbackPresentation f (quotientOnLG K)).map
    (chartQuotientIso K f ι g hfg).hom c).trans
      (congrArg (fun q => minorSection T q c) (chartQuotientIso_triangle K f ι g hfg))


/-- Every primitive determinant section is transported literally to its normalized
quotient section on every native test-scheme chart. -/
theorem chartDeterminantIso_primitive {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) (j : Fin 14) :
    (chartDeterminantIso K f ι g hfg).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j))=
      primitiveSection T K (M9Native.LagrangianPlucker.coefficientMap K f)
        (chartQuotientMap 3 6 ι g) j := by
  change (exteriorPowerMap T (chartQuotientIso K f ι g hfg).hom 3).app ⊤
    ((exteriorPullbackIso f (quotientOnLG K).target 3).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))=_
  rw [M9Native.LagrangianPrimitiveSectionsPullback.primitiveSections_pullback]
  exact (primitiveSection_postcomp T K (M9Native.LagrangianPlucker.coefficientMap K f)
      (pullbackPresentation f (quotientOnLG K)).map (chartQuotientIso K f ι g hfg).hom j).trans
    (congrArg (fun q => primitiveSection T K (M9Native.LagrangianPlucker.coefficientMap K f) q j)
      (chartQuotientIso_triangle K f ι g hfg))

/-- In the actual determinant trivialization these are exactly the frozen
fourteen actual primitive Plucker chart functions. -/
theorem chartDeterminantIso_primitive_coordinates {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) (j : Fin 14) :
    freeDeterminantCoordinates T ((chartDeterminantIso K f ι g hfg).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))=
      M9Native.LagrangianPlucker.chartCoordinates K f ι g j := by
  rw [chartDeterminantIso_primitive,primitiveSection_freeCoordinates]
  rfl

end M9Native.LagrangianPluckerTrivialization
