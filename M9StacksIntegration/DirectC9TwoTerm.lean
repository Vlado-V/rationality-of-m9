module

public import M9StacksIntegration.DirectC9Bundles
public import M9StacksIntegration.DirectImageTwoTerm
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwistDivisor
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-!
# The actual restriction differential on the ninth curve power

The actual Cartier restriction sequence of the normalized degree-eight
line supplies a distinguished triangle. Its last two terms are the actual
ordinary rank-ten bundles, proved by cohomology and base change. Full
faithfulness recovers a genuine bundle morphism; its cochain mapping
cocone represents the actual derived direct image of that degree-eight
line. No fibre map or Chern-class identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 10000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated MonoidalCategory Opposite
open Stacks.CurvePower
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.DirectC9TwoTerm

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric
  SheafOfModules.hasDerivedCategory AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

section Cartier

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  (M : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

/-- The literal maps of the native Cartier restriction sequence. -/
def divisorTwistSequence : ShortComplex X.Modules :=
  ShortComplex.mk
    ((ρ_ M).inv ≫ M ◁ (Stacks.Divisors.modulesInvertibleSheaf D).unitHomEquiv.symm
      (Stacks.Divisors.canonicalSections D))
    ((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app
      (M ⊗ Stacks.Divisors.modulesInvertibleSheaf D))
    (Stacks.Divisors.isShortExactTwistSequence_canonicalSections D M).choose

theorem divisorTwistSequence_shortExact : (divisorTwistSequence D M).ShortExact :=
  (Stacks.Divisors.isShortExactTwistSequence_canonicalSections D M).choose_spec

end Cartier

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open DirectC9Bundles (E10 F10)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C)

local instance normalized_isInvertibleAG :
    SheafOfModules.IsInvertible (familySpace C).sheaf.obj (familySpace C).ringCatSheaf.property
      (degreeEightLine C c₀) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (degreeEightLine_isInvertible C c₀)

local instance fixedFamily_isEffectiveCartier (q : ℕ) :
    @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C) (constantFamily C c₀ q).ideal :=
  constantFamily_isEffectiveCartier C c₀ q

/-- The actual degree-ten fixed-point Cartier restriction sequence. -/
abbrev restrictionSequence : ShortComplex (familySpace C).Modules :=
  divisorTwistSequence (constantFamily C c₀ 9).ideal (degreeEightLine C c₀)

theorem restrictionSequence_shortExact : (restrictionSequence k C c₀).ShortExact :=
  divisorTwistSequence_shortExact (constantFamily C c₀ 9).ideal (degreeEightLine C c₀)

/-- The native positive-divisor sheaf and the retained twist are the same actual module. -/
def restrictionSequence_middleIso :
    (restrictionSequence k C c₀).X₂ ≅ DirectC9Cohomology.twistedLine k C c₀ 9 :=
  Iso.refl _

/-- The actual middle derived image is the retained ordinary E10 in degree zero. -/
def restrictionSequence_middleDerivedIso (hg : genus C.hom = 9) :
    derivedPushforwardModule (familyProjection C) (restrictionSequence k C c₀).X₂ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (E10 k C c₀) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
    (familyProjection C).toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor (familySpace C).Modules 0).mapIso
        (restrictionSequence_middleIso k C c₀)) ≪≫
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (familyProjection C)
      (DirectC9Cohomology.twistedLine k C c₀ 9) 10
      (DirectC9Bundles.twistedLine_hasDerivedRank k C c₀ hg 9 (by omega))

/-- The actual restriction derived image is the retained ordinary F10 in degree zero. -/
def restrictionSequence_lastDerivedIso :
    derivedPushforwardModule (familyProjection C) (restrictionSequence k C c₀).X₃ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (F10 k C c₀) := by
  let D := (constantFamily C c₀ 9).ideal
  let L := DirectC9Bundles.restrictedTwist k C c₀ 9
  letI : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (DirectC9Bundles.restrictedTwist_isInvertible k C c₀ 9)
  have hL : L.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible L
  exact DirectImageTwoTerm.derivedPushforwardOfAffinePushforwardIso
    D.subschemeι (familyProjection C) L hL ≪≫
      DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward
        (DirectC9Bundles.fixedDivisorProjection k C c₀ 9) L 10
        (DirectC9Bundles.restrictedTwist_hasDerivedRank k C c₀ 9)

/-- The actual original degree-eight family has a genuine global E10-to-F10 triangle. -/
theorem exists_restrictionTriangle (hg : genus C.hom = 9) :
    ∃ (a : derivedPushforwardModule (familyProjection C) (degreeEightLine C c₀) ⟶
        (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (E10 k C c₀))
      (d : E10 k C c₀ ⟶ F10 k C c₀)
      (b : (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (F10 k C c₀) ⟶
        (derivedPushforwardModule (familyProjection C) (degreeEightLine C c₀))⟦(1 : ℤ)⟧),
      Triangle.mk a ((DerivedCategory.singleFunctor (power C 9).left.Modules 0).map d) b ∈
        distTriang (DerivedCategory (power C 9).left.Modules) :=
  DirectImageTwoTerm.exists_twoTermTriangle_of_shortExact (familyProjection C)
    (restrictionSequence k C c₀) (restrictionSequence_shortExact k C c₀)
    (restrictionSequence_middleDerivedIso k C c₀ hg) (restrictionSequence_lastDerivedIso k C c₀)

/-- In particular, one actual rank-ten bundle differential represents the actual derived image. -/
theorem exists_twoTermRepresentation (hg : genus C.hom = 9) :
    ∃ d : E10 k C c₀ ⟶ F10 k C c₀,
      Nonempty (derivedPushforwardModule (familyProjection C) (degreeEightLine C c₀) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCocone
          ((CochainComplex.singleFunctor (power C 9).left.Modules 0).map d))) := by
  obtain ⟨a,d,b,hT⟩ := exists_restrictionTriangle k C c₀ hg
  exact ⟨d,DirectImageTwoTerm.twoTerm_mappingCocone_representation a d b hT⟩

end M9Native.DirectC9TwoTerm
