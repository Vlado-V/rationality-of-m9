module

public import M9StacksIntegration.DirectC9Bundles
public import M9StacksIntegration.DirectC9NormalizationClass
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-!
# Actual line isomorphisms for the fixed and moving Cartier rows

These are genuine sheaf isomorphisms. The successive moving and fixed
positive divisors are their literal native Cartier sums, so proved
Picard equalities yield the actual tensor-line isomorphisms. The final
eighteen-point twist cancels its actual dual line by evaluation.
No Chern, K-zero, numerical or ordinary-base-change identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory Stacks.CurvePower
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DirectC9TwistLineIsos

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection familyClass)
open DirectC9NormalizationClass (graphFamilyClass)
open PoincareChern (lineClass)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C)

local instance graphIdeal_cartier (y : power C 9 ⟶ C) :
    @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C)
      (Stacks.Hilbert.pointIdeal C (power C 9) y) :=
  (GraphNormalPicard.graphFamily C (power C 9) y).isEffectiveCartierDivisor_ideal

abbrev graphLine (y : power C 9 ⟶ C) : (familySpace C).Modules :=
  Stacks.Divisors.divisorSheaf (Stacks.Hilbert.pointIdeal C (power C 9) y)

instance graphLine_isInvertible (y : power C 9 ⟶ C) :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf (familySpace C).ringCatSheaf.2
      (graphLine k C y) :=
  @Stacks.Divisors.isInvertible_invertibleSheaf_picard (familySpace C)
    (Stacks.Hilbert.pointIdeal C (power C 9) y) (graphIdeal_cartier k C y)

theorem graphLine_class (y : power C 9 ⟶ C) :
    @lineClass (familySpace C) (graphLine k C y) (graphLine_isInvertible k C y) =
      graphFamilyClass C y := rfl

/-- Adding the next literal coordinate graph gives the next actual partial line. -/
theorem nonempty_movingTwistIso (j : ℕ) (hj : j + 1 ≤ 9) :
    Nonempty (Scheme.Modules.tensorObj (partialLine C c₀ j (by omega))
      (graphLine k C (coord C 9 ⟨j,by omega⟩)) ≅ partialLine C c₀ (j + 1) hj) := by
  have hj₀ : j ≤ 9 := by omega
  let i : Fin 9 := ⟨j,by omega⟩
  let A : (familySpace C).Modules := partialLine C c₀ j hj₀
  let B : (familySpace C).Modules := partialLine C c₀ (j + 1) hj
  let G : (familySpace C).Modules := graphLine k C (coord C 9 i)
  letI hA : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 A := partialLine_isInvertible C c₀ j hj₀
  letI hB : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 B := partialLine_isInvertible C c₀ (j + 1) hj
  letI hG : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 G := graphLine_isInvertible k C (coord C 9 i)
  apply @PoincareChern.nonempty_tensorIso_of_lineClass_eq (familySpace C) A G B hA hG hB
  have hf : familyClass C (partialFamily C c₀ (j + 1) hj) =
      familyClass C (partialFamily C c₀ j hj₀) + graphFamilyClass C (coord C 9 i) :=
    DirectC9NormalizationClass.familyAddPoint_class C (partialFamily C c₀ j hj₀)
      (coord C 9 i)
      (Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 9) _)
  let n := Stacks.Picard.schemePullbackClass (familyProjection C)
    (@lineClass (power C 9).left (inverseNormalizationLine C c₀)
      (DirectC9FamilyDegree.inverseNormalizationLine_isInvertible C c₀))
  have hp : @lineClass (familySpace C) A hA = n + familyClass C (partialFamily C c₀ j hj₀) :=
    DirectC9FamilyDegree.partialLine_class C c₀ j hj₀
  have hn : @lineClass (familySpace C) B hB = n + familyClass C (partialFamily C c₀ (j + 1) hj) :=
    DirectC9FamilyDegree.partialLine_class C c₀ (j + 1) hj
  have hg : @lineClass (familySpace C) G hG = graphFamilyClass C (coord C 9 i) :=
    graphLine_class k C (coord C 9 i)
  exact hn.trans ((congrArg (fun z : Stacks.Picard.ofScheme (familySpace C) => n + z) hf).trans
    ((add_assoc _ _ _).symm.trans
      (congrArg₂ (fun x y : Stacks.Picard.ofScheme (familySpace C) => x + y) hp.symm hg.symm)))

def movingTwistIso (j : ℕ) (hj : j + 1 ≤ 9) :
    Scheme.Modules.tensorObj (partialLine C c₀ j (by omega))
      (graphLine k C (coord C 9 ⟨j,by omega⟩)) ≅ partialLine C c₀ (j + 1) hj :=
  (nonempty_movingTwistIso k C c₀ j hj).some

/-- One further fixed graph gives the next actual twist of the same normalized line. -/
theorem nonempty_fixedTwistIso (q : ℕ) :
    Nonempty (Scheme.Modules.tensorObj (DirectC9Cohomology.twistedLine k C c₀ q)
      (graphLine k C (constantPoint C c₀)) ≅ DirectC9Cohomology.twistedLine k C c₀ (q + 1)) := by
  have hf : familyClass C (constantFamily C c₀ (q + 1)) =
      familyClass C (constantFamily C c₀ q) + graphFamilyClass C (constantPoint C c₀) :=
    DirectC9NormalizationClass.familyAddPoint_class C (constantFamily C c₀ q)
      (constantPoint C c₀)
      (Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 9) _)
  apply PoincareChern.nonempty_tensorIso_of_lineClass_eq
    (DirectC9Cohomology.twistedLine k C c₀ q) (graphLine k C (constantPoint C c₀))
    (DirectC9Cohomology.twistedLine k C c₀ (q + 1))
  rw [DirectC9Cohomology.twistedLine_class,DirectC9Cohomology.twistedLine_class,graphLine_class,hf]
  exact (add_assoc _ _ _).symm

def fixedTwistIso (q : ℕ) :
    Scheme.Modules.tensorObj (DirectC9Cohomology.twistedLine k C c₀ q)
      (graphLine k C (constantPoint C c₀)) ≅ DirectC9Cohomology.twistedLine k C c₀ (q + 1) :=
  (nonempty_fixedTwistIso k C c₀ q).some

/-- The actual O(18c0) dual pair cancels, as a genuine tensor-sheaf isomorphism. -/
def twist18IsoPartialNine :
    DirectC9Cohomology.twistedLine k C c₀ 17 ≅ partialLine C c₀ 9 (by omega) := by
  let A : (familySpace C).Modules := (Scheme.Modules.pullback (familyProjection C)).obj
    (inverseNormalizationLine C c₀)
  let B : (familySpace C).Modules := positiveLine C c₀
  let D : (familySpace C).Modules := fixedLine C c₀ 17
  letI : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 D := fixedLine_isInvertible C c₀ 17
  exact (α_ A (Scheme.Modules.tensorObj B (dualSheaf D)) D) ≪≫
    (tensorLeft A).mapIso
      ((α_ B (dualSheaf D) D) ≪≫
        (tensorLeft B).mapIso (Stacks.SheafOfModules.Scheme.evaluationIso (familySpace C) D) ≪≫
          (ρ_ B))

/-- The retained actual ordinary E18 is the last actual moving ordinary bundle. -/
def E18IsoMovingNine :
    DirectC9Bundles.E18 k C c₀ ≅ DirectC9Bundles.movingPushforward k C c₀ 9 (by omega) :=
  (Scheme.Modules.pushforward (familyProjection C)).mapIso (twist18IsoPartialNine k C c₀)

end M9Native.DirectC9TwistLineIsos
