module

public import M9StacksIntegration.DirectC9GraphTwistRows
public import M9StacksIntegration.DirectC9TwistLineIsos
public import M9StacksIntegration.DirectC9MovingQuotientClass

/-!
# The nine actual moving-graph ordinary short exact rows

Every row has the retained actual ordinary direct images as its first
and middle bundles, and the literal actual moving quotient line as its
last bundle. The maps arise from the genuine Cartier restriction
sequence and actual derived cohomology, followed by an actual line
isomorphism. No K-zero or Chern formula is an input.
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

namespace M9Native.DirectC9MovingRows

attribute [local instance 10000] HasDerivedCategory.standard

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open DirectC9Bundles (movingPushforward)
open DirectC9MovingQuotientClass (movingQuotientLine)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

include hg

/-- Each original moving-graph addition induces a genuine ordinary bundle ShortExact row. -/
theorem exists_movingRow (j : ℕ) (hj : j + 1 ≤ 9) :
    ∃ (a : movingPushforward k C c₀ j (by omega) ⟶ movingPushforward k C c₀ (j + 1) hj)
      (b : movingPushforward k C c₀ (j + 1) hj ⟶ movingQuotientLine C c₀ j hj)
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  have hj₀ : j ≤ 9 := by omega
  let i : Fin 9 := ⟨j,by omega⟩
  let y := coord C 9 i
  let M : (familySpace C).Modules := partialLine C c₀ j hj₀
  letI hM : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 M := partialLine_isInvertible C c₀ j hj₀
  let S : ShortComplex (familySpace C).Modules := DirectC9GraphTwistRows.graphTwistSequence k C y M
  let eLine : S.X₂ ≅ partialLine C c₀ (j + 1) hj := DirectC9TwistLineIsos.movingTwistIso k C c₀ j hj
  let e₁ : derivedPushforwardModule (familyProjection C) M ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        (movingPushforward k C c₀ j hj₀) :=
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (familyProjection C) M (9 + j)
      (DirectC9Bundles.partialLine_hasDerivedRank k C c₀ hg j hj₀)
  let e₂ : derivedPushforwardModule (familyProjection C) S.X₂ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        (movingPushforward k C c₀ (j + 1) hj) :=
    (derivedPushforward (familyProjection C).toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor (familySpace C).Modules 0).mapIso eLine) ≪≫
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (familyProjection C)
      (partialLine C c₀ (j + 1) hj) (9 + (j + 1))
      (DirectC9Bundles.partialLine_hasDerivedRank k C c₀ hg (j + 1) hj)
  obtain ⟨a,b,w,hs⟩ := DirectC9GraphTwistRows.exists_graphTwist_shortExact k C y M
    (movingPushforward k C c₀ j hj₀) (movingPushforward k C c₀ (j + 1) hj) e₁ e₂
  let q : (Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).obj S.X₂ ≅
      movingQuotientLine C c₀ j hj :=
    (Scheme.Modules.pullback (Stacks.Hilbert.pointGraph C (power C 9) y)).mapIso eLine
  have w' : a ≫ (b ≫ q.hom) = 0 := by rw [← Category.assoc,w,zero_comp]
  let e : ShortComplex.mk a b w ≅ ShortComplex.mk a (b ≫ q.hom) w' :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) q (by simp) (by simp)
  exact ⟨a,b ≫ q.hom,w',ShortComplex.shortExact_of_iso e hs⟩

/-- The actual row, with the actual maps chosen from the proved geometric existence. -/
def movingRow (j : ℕ) (hj : j + 1 ≤ 9) : ShortComplex (power C 9).left.Modules :=
  let h := exists_movingRow k C c₀ hg j hj
  ShortComplex.mk h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose

theorem movingRow_shortExact (j : ℕ) (hj : j + 1 ≤ 9) : (movingRow k C c₀ hg j hj).ShortExact :=
  (exists_movingRow k C c₀ hg j hj).choose_spec.choose_spec.choose_spec

end M9Native.DirectC9MovingRows
