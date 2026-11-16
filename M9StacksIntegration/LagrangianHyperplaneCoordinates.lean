module

public import M9StacksIntegration.LagrangianPluckerGeneration

/-! The actual native projective hyperplane line on LG is the original
universal quotient determinant line, retaining all fourteen coordinates
and all coefficient vectors. Vanishing is compared on every test scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace M9Native.LagrangianHyperplaneCoordinates

open LagrangianGrassmannian LagrangianPluckerQuotient
variable (K : Type u) [Field K] [CharZero K]

/-- The literal native projective hyperplane line, using the actual
composite of the original Plucker map with integral projective space. -/
abbrev hyperplaneLine : (space K).Modules :=
  (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K ≫
    projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13)

/-- The actual fourteen original homogeneous coordinate sections. -/
def coordinateSection (j : Fin 14) : Γ(hyperplaneLine K, ⊤) :=
  Stacks.TwistPullbackPinned.pullbackCoordSection
    (LagrangianPlucker.primitivePlucker K ≫
      projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K))) j

/-- The actual hyperplane line isomorphism retaining the original
primitive-coordinate convention. -/
def lineIso : hyperplaneLine K ≅ determinantLine K :=
  (Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).app
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13) ≪≫
    LagrangianPluckerGeneration.integralDeterminantLineIso K

/-- The isomorphism sends every native coordinate to the corresponding
original determinant section. -/
theorem lineIso_coordinate (j : Fin 14) :
    (lineIso K).hom.app ⊤ (coordinateSection K j) = primitiveSections K j := by
  let M := Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13
  let s := Stacks.TwistPullbackPinned.coordGlobalSection.{u} 13 j
  have hn := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr
    (LagrangianPlucker.primitivePlucker_toIntegral K) M s
  have h := (congrArg
    ((LagrangianPluckerGeneration.integralDeterminantLineIso K).hom.app ⊤) hn).trans
      (LagrangianPluckerGeneration.integralDeterminantLineIso_coordinate K j)
  simpa only [lineIso, coordinateSection, Iso.trans_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Stacks.TwistPullbackPinned.pullbackCoordSection,
    projectiveSpaceOver.toIntegralAtUniverse] using h

/-- The scalar map induced by the original LG structure morphism. -/
abbrev coefficientMap : K →+* Γ(space K, ⊤) :=
  LagrangianPlucker.coefficientMap K (𝟙 _)

/-- The actual projective hyperplane section for an original coefficient vector. -/
def linearSection (v : Fin 14 → K) : Γ(hyperplaneLine K, ⊤) :=
  ∑ i : Fin 14, coefficientMap K (v i) • coordinateSection K i

/-- The same coefficient vector in the original quotient determinant line. -/
def determinantSection (v : Fin 14 → K) : Γ(determinantLine K, ⊤) :=
  ∑ i : Fin 14, coefficientMap K (v i) • primitiveSections K i

/-- All coefficient vectors are retained by the actual line isomorphism. -/
theorem lineIso_linearSection (v : Fin 14 → K) :
    (lineIso K).hom.app ⊤ (linearSection K v) = determinantSection K v := by
  simp only [linearSection, determinantSection, map_sum, Scheme.Modules.Hom.app_smul,
    lineIso_coordinate]

/-- Actual pullback vanishing of every original hyperplane section is
exactly actual pullback vanishing of its original determinant section. -/
theorem pullback_linearSection_zero_iff {T : Scheme.{u}} (f : T ⟶ space K)
    (v : Fin 14 → K) :
    pullbackGlobalSections f (hyperplaneLine K) (linearSection K v) = 0 ↔
      pullbackGlobalSections f (determinantLine K) (determinantSection K v) = 0 := by
  have h := LagrangianMatrixChart.pullbackSection_eq_zero_iff_of_iso f
    (lineIso K) (linearSection K v)
  rw [lineIso_linearSection] at h
  exact h

end M9Native.LagrangianHyperplaneCoordinates
