module

public import M9StacksIntegration.DirectC9TwoTerm
public import M9StacksIntegration.GraphPointPushforward

/-!
# Genuine ordinary rows from a moving or fixed graph Cartier twist

The third derived image is the actual restriction to the ORIGINAL
section: the graph divisor projection is an actual isomorphism. Its
rank-one concentration follows from the proved finite-flat line theorem.
Thus actual concentrated first and middle images give actual ordinary
ShortExact maps, with no Grothendieck-class or Chern identity as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.CurvePower
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.DirectC9GraphTwistRows

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

local instance graph_closed (y : power C 9 ⟶ C) :
    IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 9) y) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 9) y

local instance graph_cartier (y : power C 9 ⟶ C) :
    @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C)
      (Stacks.Hilbert.pointIdeal C (power C 9) y) :=
  (GraphNormalPicard.graphFamily C (power C 9) y).isEffectiveCartierDivisor_ideal

variable (y : power C 9 ⟶ C) (M : (familySpace C).Modules)
  [hM : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf (familySpace C).ringCatSheaf.2 M]

abbrev graphTwistSequence : ShortComplex (familySpace C).Modules :=
  @DirectC9TwoTerm.divisorTwistSequence (familySpace C)
    (Stacks.Hilbert.pointIdeal C (power C 9) y) (graph_cartier k C y) M
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hM)

theorem graphTwistSequence_shortExact : (graphTwistSequence k C y M).ShortExact :=
  @DirectC9TwoTerm.divisorTwistSequence_shortExact (familySpace C)
    (Stacks.Hilbert.pointIdeal C (power C 9) y) (graph_cartier k C y) M
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hM)

instance graphTwistMiddle_isInvertible :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf (familySpace C).ringCatSheaf.2
      (graphTwistSequence k C y M).X₂ := by
  let G : (familySpace C).Modules := Stacks.Divisors.modulesInvertibleSheaf
    (Stacks.Hilbert.pointIdeal C (power C 9) y)
  letI hG : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 G :=
    @Stacks.Divisors.isInvertible_invertibleSheaf_picard (familySpace C)
      (Stacks.Hilbert.pointIdeal C (power C 9) y) (graph_cartier k C y)
  exact @PoincareChern.lineTensor_isInvertible (familySpace C) M G hM hG

/-- The actual third derived image is the actual line on the actual graph section. -/
def graphTwist_lastDerivedIso :
    derivedPushforwardModule (familyProjection C) (graphTwistSequence k C y M).X₃ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        ((Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).obj
          (graphTwistSequence k C y M).X₂) := by
  let D := Stacks.Hilbert.pointIdeal C (power C 9) y
  let L := (Scheme.Modules.pullback D.subschemeι).obj (graphTwistSequence k C y M).X₂
  letI hL : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 L :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj D.subschemeι
      (graphTwistSequence k C y M).X₂
  letI : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hL
  have hQC : L.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible L
  let pD := GraphPointPushforward.pointProjection C (power C 9) y
  letI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank pD 1 :=
    Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal C (power C 9) y
  exact DirectImageTwoTerm.derivedPushforwardOfAffinePushforwardIso D.subschemeι
      (familyProjection C) L hQC ≪≫
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward pD L 1
      (DirectC9Bundles.finiteFlat_line_hasDerivedRank pD 1 L) ≪≫
    (DerivedCategory.singleFunctor (power C 9).left.Modules 0).mapIso
      (GraphPointPushforward.pointPushforwardIso C (power C 9) y
        (graphTwistSequence k C y M).X₂)

/-- Actual Cartier geometry and actual degree-zero images give actual ordinary row maps. -/
theorem exists_graphTwist_shortExact (E₁ E₂ : (power C 9).left.Modules)
    (e₁ : derivedPushforwardModule (familyProjection C) M ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj E₁)
    (e₂ : derivedPushforwardModule (familyProjection C) (graphTwistSequence k C y M).X₂ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj E₂) :
    ∃ (a : E₁ ⟶ E₂)
      (b : E₂ ⟶ (Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).obj
        (graphTwistSequence k C y M).X₂) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact :=
  DirectImageTwoTerm.exists_shortExact_of_derivedImages (familyProjection C)
    (graphTwistSequence k C y M) (graphTwistSequence_shortExact k C y M) E₁ E₂ _ e₁ e₂
    (graphTwist_lastDerivedIso k C y M)

end M9Native.DirectC9GraphTwistRows
