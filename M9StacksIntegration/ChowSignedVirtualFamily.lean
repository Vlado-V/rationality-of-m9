module

public import M9StacksIntegration.ChowVirtualDuality
public import M9StacksIntegration.ChowVirtualPullback
public import M9StacksIntegration.ChowLineProperPush

/-!
# The signed-source family in genuine projective flag pushforwards

A positive quotient root of D naturally produces the signed inverse
Chern family of D. At the original base D=E-dual, genuine native Chern
duality identifies this with the ordinary inverse family of E. Flat
pullback and proper pushforward are the literal native maps, and their
naturality is derived here without identifying pullback with duality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace M9Native.ChowSignedVirtualFamily
open GradedCapVirtualSchur

/-- The actual Chern family times the signed actual source inverse. -/
def family (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (F D : X.Modules) (rF rD : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D rD] :
    GradedCapFamily (chowGroup C q) :=
  chernFamily C q F rF * capFamilySignScale (inverseFamily C q D rD)

/-- On the original dual source, true native Chern duality removes the
sign. No pullback/duality comparison or Chern-family premise is assumed. -/
theorem dual_source_eq_virtual (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E rE] :
    letI := isFiniteLocallyFreeOfRank_dualSheaf E rE hE
    family C q F (dualSheaf E) rF rE = virtualFamily C q F E rF rE := by
  letI := isFiniteLocallyFreeOfRank_dualSheaf E rE hE
  exact congrArg (fun a : GradedCapFamily (chowGroup C q) => chernFamily C q F rF * a)
    (ChowVirtualDuality.signed_inverse_dualFamily C q E rE)

/-- Actual flat pullback transports the signed-source family using the
original two sheaf isomorphisms, without commuting inverse and pullback
by definition. -/
theorem flatPullback (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hf : f ≫ qX = qY) (d : ℕ) (hd : RelativeDimension f d)
    (D : X.Modules) (rD : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D rD]
    (D' : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D' rD]
    (eD : D' ≅ (Scheme.Modules.pullback f).obj D)
    (F : X.Modules) (rF : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
    (F' : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F' rF]
    (eF : F' ≅ (Scheme.Modules.pullback f).obj F) :
    Intertwines (ChowVirtualPullback.actualPull C qX qY f hf d hd)
      (family C qX F D rF rD) (family C qY F' D' rF rD) :=
  (intertwines_chernFamily C qX F rF qY f hf d hd F' eF).convolve
    (Stacks.Chow.Intertwines.capFamilySignScale
      (ChowVirtualPullback.inverseFamily_flatPullback C qX qY f hf d hd D rD D' eD))

/-- Literal actual proper pushforward transports the same ordered
family. Only the genuine native zero-grade cast is present. -/
theorem properPush (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX)
    (D : Y.Modules) (rD : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D rD]
    (D' : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D' rD]
    (eD : D' ≅ (Scheme.Modules.pullback p).obj D)
    (F : Y.Modules) (rF : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
    (F' : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F' rF]
    (eF : F' ≅ (Scheme.Modules.pullback p).obj F) :
    Intertwines (d:=0) (ChowLineProperPush.actualPush C qX qY p hp)
      (family C qX F' D' rF rD) (family C qY F D rF rD) :=
  (ChowLineProperPush.properPush_intertwines_chernFamily C qX qY p hp F rF F' eF).convolve
    (Stacks.Chow.Intertwines.capFamilySignScale
      (ChowLineProperPush.properPush_intertwines_inverseFamily C qX qY p hp D rD D' eD))

end M9Native.ChowSignedVirtualFamily
