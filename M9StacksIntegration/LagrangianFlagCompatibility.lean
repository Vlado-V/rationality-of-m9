module

public import M9StacksIntegration.FlagTowerLines
public import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian

/-!
# Actual quotient bundles through the native two descriptions of a flag

This file preserves every named quotient.  It identifies the actual
pullback of each universal flag quotient, rather than using only an
isomorphism of schemes over the base.  The all-test comparison is the
literal native comap of the actual universal quotient epimorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianDegree

open Stacks.FlagTower

section ComapMaps

variable {T : Scheme.{u}} {M Q : T.Modules} (π : M ⟶ Q) [Epi π]

/-- The literal native comap quotient comparison, normalized by its quotient map. -/
def comapQuotientIso (S : Subobject Q) :
    cokernel (comapSub π S).arrow ≅ cokernel S.arrow :=
  FlagQuotientLines.quotientIso π S

@[reassoc]
theorem comapQuotientIso_π (S : Subobject Q) :
    cokernel.π (comapSub π S).arrow ≫ (comapQuotientIso π S).hom =
      π ≫ cokernel.π S.arrow := FlagQuotientLines.quotientIso_π π S

/-- The actual quotient map of nested subobjects. -/
abbrev subQuotientStep {A : T.Modules} {S S' : Subobject A} (h : S ≤ S') :
    cokernel S.arrow ⟶ cokernel S'.arrow := FlagQuotientLines.quotientStep h

/-- The original quotient-step square is genuinely preserved. -/
theorem comapQuotientIso_step {S S' : Subobject Q} (h : S ≤ S') :
    subQuotientStep (comapSub_mono π h) ≫ (comapQuotientIso π S').hom =
      (comapQuotientIso π S).hom ≫ subQuotientStep h :=
  FlagQuotientLines.quotientIso_step π h

/-- The actual graded kernel lines of the literal native comap agree. -/
def comapKernelLineIso {S S' : Subobject Q} (h : S ≤ S') :
    kernel (subQuotientStep (comapSub_mono π h)) ≅ kernel (subQuotientStep h) :=
  FlagQuotientLines.quotientKernelIso π h

@[reassoc]
theorem comapKernelLineIso_hom_ι {S S' : Subobject Q} (h : S ≤ S') :
    (comapKernelLineIso π h).hom ≫ kernel.ι (subQuotientStep h) =
      kernel.ι (subQuotientStep (comapSub_mono π h)) ≫ (comapQuotientIso π S).hom :=
  FlagQuotientLines.quotientKernelIso_hom_ι π h

end ComapMaps

section Pullback

variable {X : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (m : ℕ)

/-- The original actual universal native flag. -/
abbrev towerUniversalFlag := FlagTowerLines.universalFlag E m

/-- The actual universal quotient, retaining its original index. -/
abbrev towerUniversalQuotient (j : Fin m) := FlagTowerLines.universalQuotient E m j

/-- The actual original universal graded kernel line. -/
abbrev towerUniversalKernelLine {a b : Fin m} (h : a ≤ b) :=
  FlagTowerLines.universalKernelLine E m h

/-- The full all-test native flag is its actual sheaf pullback. -/
theorem towerFlagAlong_eq_pullback {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f}) :
    towerEquiv m E f g =
      Flag.pullback g.1
        (((Scheme.Modules.pullbackComp g.1 (tower m E).2).app E ≪≫
          (Scheme.Modules.pullbackCongr g.2).app E).symm)
        (towerUniversalFlag E m) := FlagTowerLines.flagAlong_eq_pullback E m f g

/-- Each original quotient is the actual pullback of its named universal quotient. -/
def towerQuotientAlongIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f}) (j : Fin m) :
    cokernel ((towerEquiv m E f g).sub j).arrow ≅
      (Scheme.Modules.pullback g.1).obj (towerUniversalQuotient E m j) :=
  FlagTowerLines.quotientAlongIso E m f g j

/-- Each actual kernel line is the pullback of the original named universal line. -/
def towerKernelLineAlongIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f})
    {a b : Fin m} (h : a ≤ b) :
    kernel (subQuotientStep ((towerEquiv m E f g).antitone h)) ≅
      (Scheme.Modules.pullback g.1).obj (towerUniversalKernelLine E m h) :=
  FlagTowerLines.kernelLineAlongIso E m f g h

end Pullback

section TwoTowers

variable (l n : ℕ) (X : Scheme.{u}) (hln : l < n)

/-- The native two-tower equivalence carries the actual universal
quotient flag to the literal comap flag, for every test scheme. -/
theorem twoTowerFlags_eq_comap {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f}) :
    towerBEquiv l n X f (towerPointsEquiv l n X hln f g) =
      Flag.comap (presMap l n f (towerAEquiv l n X f g).1.1)
        (towerAEquiv l n X f g).2 :=
  (towerBEquiv l n X f).apply_symm_apply
    (compareEquiv l n hln f (towerAEquiv l n X f g))

/-- Actual quotient sheaves are identified through the literal comap;
this is stronger than equality of the corresponding field points. -/
def twoTowerQuotientIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f})
    (j : Fin (n-l)) :
    cokernel ((towerBEquiv l n X f
      (towerPointsEquiv l n X hln f g)).sub j).arrow ≅
        cokernel (((towerAEquiv l n X f g).2).sub j).arrow :=
  eqToIso (congrArg (fun F : Flag
      ((Scheme.Modules.pullback f).obj (freeModule n X)) (n-l) =>
        cokernel (F.sub j).arrow) (twoTowerFlags_eq_comap l n X hln f g)) ≪≫
    comapQuotientIso (presMap l n f (towerAEquiv l n X f g).1.1)
      (((towerAEquiv l n X f g).2).sub j)

/-- The two-tower comparison identifies the actual named kernel lines
of every test flag, not only its quotient isomorphism classes. -/
def twoTowerKernelLineIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f})
    {a b : Fin (n-l)} (h : a ≤ b) :
    kernel (subQuotientStep ((towerBEquiv l n X f
      (towerPointsEquiv l n X hln f g)).antitone h)) ≅
        kernel (subQuotientStep (((towerAEquiv l n X f g).2).antitone h)) :=
  eqToIso (congrArg (fun F : Flag
      ((Scheme.Modules.pullback f).obj (freeModule n X)) (n-l) =>
        kernel (subQuotientStep (F.antitone h))) (twoTowerFlags_eq_comap l n X hln f g)) ≪≫
    comapKernelLineIso (presMap l n f (towerAEquiv l n X f g).1.1)
      (((towerAEquiv l n X f g).2).antitone h)

/-- The genuine two-tower scheme isomorphism preserves the actual
named universal quotient sheaves. -/
def flagTowerUniversalQuotientIso (j : Fin (n-l)) :
    (Scheme.Modules.pullback (flagTowerIso l n X hln).hom).obj
      (@towerUniversalQuotient X (freeModule n X)
        (isFiniteLocallyFree_freeModule n X) (n-l) j) ≅
    @towerUniversalQuotient (AlgebraicGeometry.Grassmannian.schemeOver l n X)
      (universalQuotient l n X).target
      (isFiniteLocallyFree_universalQuotient l n X) (n-l) j := by
  let g : {g : (towerA l n X).1 ⟶ (towerA l n X).1 //
      g ≫ towerAProj l n X = towerAProj l n X} := ⟨𝟙 _, by simp⟩
  let h := towerPointsEquiv l n X hln (towerAProj l n X) g
  exact (@towerQuotientAlongIso X (freeModule n X)
      (isFiniteLocallyFree_freeModule n X) (n-l)
      (towerA l n X).1 (towerAProj l n X) h j).symm ≪≫
    twoTowerQuotientIso l n X hln (towerAProj l n X) g j

/-- The genuine scheme isomorphism preserves the original actual
universal kernel lines across both descriptions of the flag tower. -/
def flagTowerUniversalKernelLineIso {a b : Fin (n-l)} (hab : a ≤ b) :
    (Scheme.Modules.pullback (flagTowerIso l n X hln).hom).obj
      (@towerUniversalKernelLine X (freeModule n X)
        (isFiniteLocallyFree_freeModule n X) (n-l) a b hab) ≅
    @towerUniversalKernelLine (AlgebraicGeometry.Grassmannian.schemeOver l n X)
      (universalQuotient l n X).target
      (isFiniteLocallyFree_universalQuotient l n X) (n-l) a b hab := by
  let g : {g : (towerA l n X).1 ⟶ (towerA l n X).1 //
      g ≫ towerAProj l n X = towerAProj l n X} := ⟨𝟙 _, by simp⟩
  let h := towerPointsEquiv l n X hln (towerAProj l n X) g
  exact (@towerKernelLineAlongIso X (freeModule n X)
      (isFiniteLocallyFree_freeModule n X) (n-l)
      (towerA l n X).1 (towerAProj l n X) h a b hab).symm ≪≫
    twoTowerKernelLineIso l n X hln (towerAProj l n X) g hab

end TwoTowers

end M9Native.LagrangianDegree
