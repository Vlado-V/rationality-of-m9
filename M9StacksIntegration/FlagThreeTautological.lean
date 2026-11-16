module

public import M9StacksIntegration.FlagTowerTautologicalLines
public import M9StacksIntegration.FlagThreeQuotient
public import M9StacksIntegration.FullFlagQuotient

/-!
# The actual rank-three quotient filtration and the literal O(1) tower

The original three quotient pieces used by the incidence bundle are
identified with the original successive tautological lines. In full
rank three the top quotient is the actual pullback of the original
bundle, and its quotient map normalizes this comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower

universe u

namespace M9Native.FlagThreeTautological

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

/-- The actual identity point of the original native representing tower. -/
def universalPoint :
    {g : FlagThreeQuotient.space D ⟶ (tower 3 D).1 //
      g ≫ (tower 3 D).2 = FlagThreeQuotient.projection D} := ⟨𝟙 _, Category.id_comp _⟩

/-- The actual first quotient line is the first original tautological O(1). -/
def line1Iso : FlagThreeQuotient.line1 D ≅
    FlagTowerTautologicalLines.line0 D 2 (FlagThreeQuotient.projection D) (universalPoint D) :=
  FlagTowerTautologicalLines.firstLineIso D 2 (FlagThreeQuotient.projection D) (universalPoint D)

/-- The actual middle kernel line is the second original tautological O(1). -/
def line2Iso : FlagThreeQuotient.line2 D ≅
    FlagTowerTautologicalLines.line1 D 1 (FlagThreeQuotient.projection D) (universalPoint D) :=
  FlagTowerTautologicalLines.secondLineIso D (FlagThreeQuotient.projection D) (universalPoint D)

/-- The actual last kernel line is the third original tautological O(1). -/
def line3Iso : FlagThreeQuotient.line3 D ≅
    FlagTowerTautologicalLines.line2 D 0 (FlagThreeQuotient.projection D) (universalPoint D) :=
  FlagTowerTautologicalLines.thirdLineIso D (FlagThreeQuotient.projection D) (universalPoint D)

variable [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]

/-- In full rank three the original top quotient is the original bundle pullback. -/
def fullQuotientIso : FlagThreeQuotient.quotientBundle D 2 ≅
    (Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj D :=
  by
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj D) 3 :=
      @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
        (FlagThreeQuotient.projection D) D 3 hD
    exact FullFlagQuotient.quotientIso 2 (FlagThreeQuotient.universalFlag D)

@[reassoc]
theorem quotientMap_fullQuotientIso :
    FlagThreeQuotient.quotientMap D 2 ≫ (fullQuotientIso D).hom =
      𝟙 ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj D) :=
  by
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj D) 3 :=
      @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
        (FlagThreeQuotient.projection D) D 3 hD
    exact FullFlagQuotient.quotientIso_π 2 (FlagThreeQuotient.universalFlag D)

end M9Native.FlagThreeTautological
