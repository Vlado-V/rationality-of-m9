module

public import M9StacksIntegration.DirectC9GraphTwistRows
public import M9StacksIntegration.DirectC9TwistLineIsos
public import M9StacksIntegration.DirectC9JetLines

/-!
# Actual unit-quotient rows from E10 to E18

The same normalized degree-eight family is twisted by one more actual
fixed-point graph. The actual quotient is its actual section pullback,
proved to be an actual unit line. Genuine high-degree cohomology and the
actual Cartier sequence supply the ordinary row maps. No split
extension, K-zero-to-Chern rule or chosen Chern identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace M9Native.DirectC9UnitTwistRows

attribute [local instance 10000] HasDerivedCategory.standard

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open DirectC9Bundles (twistPushforward)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

include hg

/-- The actual fixed-point addition has an actual UNIT QUOTIENT, for each large-degree twist. -/
theorem exists_unitTwistRow (q : ℕ) (hq : 8 ≤ q) :
    ∃ (a : twistPushforward k C c₀ q ⟶ twistPushforward k C c₀ (q + 1))
      (b : twistPushforward k C c₀ (q + 1) ⟶
        (show (power C 9).left.Modules from SheafOfModules.unit (power C 9).left.ringCatSheaf))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  have hq' : 8 ≤ q + 1 := by omega
  let y := constantPoint C c₀
  let M : (familySpace C).Modules := DirectC9Cohomology.twistedLine k C c₀ q
  letI hM : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 M := DirectC9Cohomology.twistedLine_isInvertible k C c₀ q
  let S : ShortComplex (familySpace C).Modules := DirectC9GraphTwistRows.graphTwistSequence k C y M
  let eLine : S.X₂ ≅ DirectC9Cohomology.twistedLine k C c₀ (q + 1) :=
    DirectC9TwistLineIsos.fixedTwistIso k C c₀ q
  let e₁ : derivedPushforwardModule (familyProjection C) M ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (twistPushforward k C c₀ q) :=
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (familyProjection C) M (q + 1)
      (DirectC9Bundles.twistedLine_hasDerivedRank k C c₀ hg q hq)
  let e₂ : derivedPushforwardModule (familyProjection C) S.X₂ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj (twistPushforward k C c₀ (q + 1)) :=
    (derivedPushforward (familyProjection C).toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor (familySpace C).Modules 0).mapIso eLine) ≪≫
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (familyProjection C)
      (DirectC9Cohomology.twistedLine k C c₀ (q + 1)) ((q + 1) + 1)
      (DirectC9Bundles.twistedLine_hasDerivedRank k C c₀ hg (q + 1) hq')
  obtain ⟨a,b,w,hs⟩ := DirectC9GraphTwistRows.exists_graphTwist_shortExact k C y M
    (twistPushforward k C c₀ q) (twistPushforward k C c₀ (q + 1)) e₁ e₂
  let eQ : (Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).obj S.X₂ ≅
      (show (power C 9).left.Modules from SheafOfModules.unit (power C 9).left.ringCatSheaf) :=
    (Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).mapIso eLine ≪≫
      (DirectC9JetLines.nonempty_twistedLine_sectionIso k C c₀ (q + 1)).some
  have w' : a ≫ (b ≫ eQ.hom) = 0 := by rw [← Category.assoc,w,zero_comp]
  let e : ShortComplex.mk a b w ≅ ShortComplex.mk a (b ≫ eQ.hom) w' :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eQ (by simp) (by simp)
  exact ⟨a,b ≫ eQ.hom,w',ShortComplex.shortExact_of_iso e hs⟩

/-- The actual row, with maps chosen from the proved ordinary geometric sequence. -/
def unitTwistRow (q : ℕ) (hq : 8 ≤ q) : ShortComplex (power C 9).left.Modules :=
  let h := exists_unitTwistRow k C c₀ hg q hq
  ShortComplex.mk h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose

theorem unitTwistRow_shortExact (q : ℕ) (hq : 8 ≤ q) :
    (unitTwistRow k C c₀ hg q hq).ShortExact :=
  (exists_unitTwistRow k C c₀ hg q hq).choose_spec.choose_spec.choose_spec

end M9Native.DirectC9UnitTwistRows
