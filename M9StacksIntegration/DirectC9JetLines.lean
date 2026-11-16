module

public import M9StacksIntegration.DirectC9Bundles
public import M9StacksIntegration.DirectC9NormalizationClass
public import M9StacksIntegration.GraphPointPushforward

/-!
# The actual normalization-section lines of the F10 jets are units

The same degree-ten twist is used for every jet. Its section
restriction is trivial by the actual normalized-family isomorphism
and the proved zero self-restriction class of each fixed Cartier
divisor. The actual restricted normal twist is trivial for the same
reason. Equality of genuine Picard classes supplies actual line
isomorphisms; no jet filtration or Chern identity is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower

universe u

namespace M9Native.DirectC9JetLines

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection familyClass)
open DirectC9NormalizationClass (normalizationSection)
open PoincareChern (lineClass)

/-- An actual invertible module of zero actual Picard class is
isomorphic to the actual unit module. -/
theorem nonempty_iso_unit_of_lineClass_zero {Y : Scheme.{u}} (L : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (h : lineClass L = 0) : Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  let : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (SheafOfModules.unit Y.ringCatSheaf) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (SheafOfModules.isInvertible_unit Y.presheaf Y.ringCatSheaf.2)
  apply (Stacks.SheafOfModules.picardClass_eq_iff Y.presheaf Y.ringCatSheaf.2
    _ _ hL inferInstance).1
  exact h.trans (Stacks.SheafOfModules.picardClass_zero Y.presheaf Y.ringCatIsSheaf).symm

/-- A genuine section-unit isomorphism gives the corresponding
zero Picard pullback class, with arbitrary schemes kept abstract. -/
theorem pullbackClass_eq_zero_of_sectionIso {Y T : Scheme.{u}} (σ : T ⟶ Y)
    (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (e : Nonempty ((Scheme.Modules.pullback σ).obj L ≅
      SheafOfModules.unit T.ringCatSheaf)) :
    Stacks.Picard.schemePullbackClass σ (lineClass L) = 0 := by
  let : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      (SheafOfModules.unit T.ringCatSheaf) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (SheafOfModules.isInvertible_unit T.presheaf T.ringCatSheaf.2)
  exact (PoincareChern.lineClass_pullback σ L).symm.trans
    ((PoincareChern.lineClass_congr e.some).trans
      (Stacks.SheafOfModules.picardClass_zero T.presheaf T.ringCatIsSheaf))

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom] (c₀ : power C 0 ⟶ C)

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

local instance fixedGraph_isClosedImmersion :
    IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 9) (constantPoint C c₀)) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 9) _

abbrev negativeFixedLine (q : ℕ) : (familySpace C).Modules :=
  Stacks.Divisors.negativeTwist (constantFamily C c₀ q).ideal

instance negativeFixedLine_isInvertible (q : ℕ) :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (negativeFixedLine k C c₀ q) := by
  let := (constantFamily C c₀ q).isEffectiveCartierDivisor_ideal
  exact Stacks.Divisors.isInvertible_negativeTwist_picard (constantFamily C c₀ q).ideal

omit [IsAlgClosed k] [IsProper C.hom] in
/-- The actual normalized degree-eight class, with the literal
fibre-product family model used by the ordinary pushforwards. -/
theorem degreeEightLine_nativeClass :
    @lineClass (familySpace C) (degreeEightLine C c₀) (degreeEightLine_isInvertible C c₀) =
      Stacks.Picard.schemePullbackClass (familyProjection C)
        (-Stacks.Picard.schemePullbackClass (normalizationSection C c₀)
          (@lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀))) +
      @lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀) :=
  @normalizedLine_class (familySpace C) (power C 9).left
    (familyProjection C) (normalizationSection C c₀) (baseline C c₀)
    (baseline_isInvertible C c₀)

/-- The actual degree-ten twist has zero section class. -/
theorem twistedLine_sectionClass (q : ℕ) :
    lineClass ((Scheme.Modules.pullback (normalizationSection C c₀)).obj
      (DirectC9Cohomology.twistedLine k C c₀ q)) = 0 := by
  rw [PoincareChern.lineClass_pullback, DirectC9Cohomology.twistedLine_class,
    Stacks.Picard.schemePullbackClass_add,
    DirectC9NormalizationClass.constantFamily_sectionClass, add_zero]
  let B : Stacks.Picard.ofScheme (familySpace C) :=
    @lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀)
  let H := Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀)
  have hσ : normalizationSection C c₀ ≫ familyProjection C = 𝟙 _ :=
    Stacks.Hilbert.pointGraph_comp_hom C (power C 9) (constantPoint C c₀)
  have hcalc : H (Stacks.Picard.schemePullbackClass (familyProjection C) (-H B) + B) = 0 := by
    rw [map_add]
    change Stacks.Picard.schemePullbackClass (normalizationSection C c₀)
      (Stacks.Picard.schemePullbackClass (familyProjection C) (-H B)) + H B = 0
    rw [Stacks.Picard.schemePullbackClass_comp, hσ,
      Stacks.Picard.schemePullbackClass_id, neg_add_cancel]
  exact (congrArg H (degreeEightLine_nativeClass k C c₀)).trans hcalc

theorem nonempty_twistedLine_sectionIso (q : ℕ) :
    Nonempty ((Scheme.Modules.pullback (normalizationSection C c₀)).obj
      (DirectC9Cohomology.twistedLine k C c₀ q) ≅
        SheafOfModules.unit (power C 9).left.ringCatSheaf) :=
  nonempty_iso_unit_of_lineClass_zero _ (twistedLine_sectionClass k C c₀ q)

omit [IsAlgClosed k] in
/-- The restricted actual normal twist is also a unit line. -/
theorem negativeFixedLine_sectionClass (q : ℕ) :
    lineClass ((Scheme.Modules.pullback (normalizationSection C c₀)).obj
      (negativeFixedLine k C c₀ q)) = 0 := by
  let := (constantFamily C c₀ q).isEffectiveCartierDivisor_ideal
  have hn : lineClass (negativeFixedLine k C c₀ q) =
      -familyClass C (constantFamily C c₀ q) :=
    Stacks.Divisors.negativeTwistPicardClass_eq_neg (constantFamily C c₀ q).ideal
  rw [PoincareChern.lineClass_pullback, hn]
  change (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
    (-familyClass C (constantFamily C c₀ q)) = 0
  rw [map_neg]
  change -Stacks.Picard.schemePullbackClass (normalizationSection C c₀)
    (familyClass C (constantFamily C c₀ q)) = 0
  rw [DirectC9NormalizationClass.constantFamily_sectionClass, neg_zero]

abbrev kernelTwist (q : ℕ) : (familySpace C).Modules :=
  Scheme.Modules.tensorObj (negativeFixedLine k C c₀ q)
    (DirectC9Cohomology.twistedLine k C c₀ 9)

instance kernelTwist_isInvertible (q : ℕ) :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (kernelTwist k C c₀ q) :=
  PoincareChern.lineTensor_isInvertible _ _

theorem kernelTwist_sectionClass (q : ℕ) :
    lineClass ((Scheme.Modules.pullback (normalizationSection C c₀)).obj
      (kernelTwist k C c₀ q)) = 0 := by
  rw [PoincareChern.lineClass_pullback, PoincareChern.lineClass_tensor,
    Stacks.Picard.schemePullbackClass_add, ← PoincareChern.lineClass_pullback,
    ← PoincareChern.lineClass_pullback,
    negativeFixedLine_sectionClass, twistedLine_sectionClass, add_zero]

theorem nonempty_kernelTwist_sectionIso (q : ℕ) :
    Nonempty ((Scheme.Modules.pullback (normalizationSection C c₀)).obj
      (kernelTwist k C c₀ q) ≅ SheafOfModules.unit (power C 9).left.ringCatSheaf) :=
  nonempty_iso_unit_of_lineClass_zero _ (kernelTwist_sectionClass k C c₀ q)

/-- The first actual restriction image is the actual unit bundle. -/
theorem nonempty_firstJet_iso_unit :
    Nonempty (DirectC9Bundles.restrictionPushforward k C c₀ 0 ≅
      SheafOfModules.unit (power C 9).left.ringCatSheaf) :=
  ⟨GraphPointPushforward.pointPushforwardIso C (power C 9) (constantPoint C c₀)
      (DirectC9Cohomology.twistedLine k C c₀ 9) ≪≫
    (nonempty_twistedLine_sectionIso k C c₀ 9).some⟩

end M9Native.DirectC9JetLines
