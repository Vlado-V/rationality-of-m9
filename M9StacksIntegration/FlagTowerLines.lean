module

public import M9StacksIntegration.FlagPullbackLineBundles
public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower

/-!
# Original native tower quotients and named kernel lines

These comparisons use the original native flag and tower, for every test
scheme and every morphism into that tower. Local freeness is supplied by
the original flag ranks. Quotient maps and their original nested steps
normalize the line identifications; the line is the actual kernel of the
actual quotient step, not an independently chosen isomorphic bundle.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.FlagTower

universe u

namespace M9Native.FlagTowerLines

section Flags

variable {T : Scheme.{u}} {M : T.Modules} {m : ℕ} (F : Flag M m)

/-- The original indexed native quotient sheaf. -/
abbrev quotient (j : Fin m) : T.Modules := cokernel (F.sub j).arrow

/-- The original epimorphism from the larger native quotient. -/
abbrev quotientStep {a b : Fin m} (h : a ≤ b) : quotient F b ⟶ quotient F a :=
  FlagQuotientLines.quotientStep (F.antitone h)

/-- The actual kernel line for an adjacent original quotient step. -/
abbrev kernelLine {a b : Fin m} (h : a ≤ b) : T.Modules := kernel (quotientStep F h)

variable {T' : Scheme.{u}} (k : T' ⟶ T) {M' : T'.Modules}
  (e : M' ≅ (Scheme.Modules.pullback k).obj M)

/-- Quotient comparison for the literal original native pulled-back flag. -/
def pullbackQuotientIso (j : Fin m) :
    quotient (Flag.pullback k e F) j ≅ (Scheme.Modules.pullback k).obj (quotient F j) := by
  letI := isLocallyFree_of_rank (F.rank j)
  exact PullbackQuotientLines.quotientIso k e (F.sub j)

@[reassoc]
theorem pullbackQuotientIso_π (j : Fin m) :
    cokernel.π ((Flag.pullback k e F).sub j).arrow ≫ (pullbackQuotientIso F k e j).hom =
      e.hom ≫ (Scheme.Modules.pullback k).map (cokernel.π (F.sub j).arrow) := by
  have := isLocallyFree_of_rank (F.rank j)
  exact PullbackQuotientLines.quotientIso_π k e (F.sub j)

/-- The literal original quotient steps are preserved, including their maps. -/
theorem pullbackQuotientIso_step {a b : Fin m} (h : a ≤ b) :
    quotientStep (Flag.pullback k e F) h ≫ (pullbackQuotientIso F k e a).hom =
      (pullbackQuotientIso F k e b).hom ≫
        (Scheme.Modules.pullback k).map (quotientStep F h) := by
  have := isLocallyFree_of_rank (F.rank a)
  have := isLocallyFree_of_rank (F.rank b)
  exact PullbackQuotientLines.quotientIso_step k e (F.antitone h)

/-- Actual original native kernel lines commute with arbitrary test pullback. -/
def pullbackKernelLineIso {a b : Fin m} (h : a ≤ b) :
    kernelLine (Flag.pullback k e F) h ≅ (Scheme.Modules.pullback k).obj (kernelLine F h) := by
  letI := isLocallyFree_of_rank (F.rank a)
  letI := isLocallyFree_of_rank (F.rank b)
  exact FlagPullbackLineBundles.quotientKernelIso k e (F.antitone h)

@[reassoc]
theorem pullbackKernelLineIso_hom_map_ι {a b : Fin m} (h : a ≤ b) :
    (pullbackKernelLineIso F k e h).hom ≫
        (Scheme.Modules.pullback k).map (kernel.ι (quotientStep F h)) =
      kernel.ι (quotientStep (Flag.pullback k e F) h) ≫
        (pullbackQuotientIso F k e b).hom := by
  have := isLocallyFree_of_rank (F.rank a)
  have := isLocallyFree_of_rank (F.rank b)
  exact FlagPullbackLineBundles.quotientKernelIso_hom_map_ι k e (F.antitone h)

end Flags

section Towers

variable {X : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (m : ℕ)

/-- The literal native universal flag on the original representing tower. -/
def universalFlag : Flag ((Scheme.Modules.pullback (tower m E).2).obj E) m :=
  towerEquiv m E (tower m E).2 ⟨𝟙 _, by simp⟩

/-- The actual native indexed universal quotient on the original tower. -/
abbrev universalQuotient (j : Fin m) : (tower m E).1.Modules :=
  quotient (universalFlag E m) j

/-- The actual kernel of a native universal quotient step. -/
abbrev universalKernelLine {a b : Fin m} (h : a ≤ b) : (tower m E).1.Modules :=
  kernelLine (universalFlag E m) h

/-- Equality of the full native all-test flag, rather than only field points. -/
theorem flagAlong_eq_pullback {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f}) :
    towerEquiv m E f g =
      Flag.pullback g.1
        (((Scheme.Modules.pullbackComp g.1 (tower m E).2).app E ≪≫
          (Scheme.Modules.pullbackCongr g.2).app E).symm)
        (universalFlag E m) := by
  simpa only [Category.comp_id, universalFlag] using
    towerEquiv_comp m E g.1 (tower m E).2 ⟨𝟙 _, by simp⟩ f g.2

/-- Each named actual quotient of an arbitrary tower point is its universal pullback. -/
def quotientAlongIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f}) (j : Fin m) :
    quotient (towerEquiv m E f g) j ≅
      (Scheme.Modules.pullback g.1).obj (universalQuotient E m j) :=
  eqToIso (congrArg (fun F : Flag ((Scheme.Modules.pullback f).obj E) m => quotient F j)
      (flagAlong_eq_pullback E m f g)) ≪≫
    pullbackQuotientIso (universalFlag E m) g.1
      (((Scheme.Modules.pullbackComp g.1 (tower m E).2).app E ≪≫
        (Scheme.Modules.pullbackCongr g.2).app E).symm) j

/-- Each named actual kernel line is the pullback of the universal kernel line. -/
def kernelLineAlongIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f})
    {a b : Fin m} (h : a ≤ b) :
    kernelLine (towerEquiv m E f g) h ≅
      (Scheme.Modules.pullback g.1).obj (universalKernelLine E m h) :=
  eqToIso (congrArg (fun F : Flag ((Scheme.Modules.pullback f).obj E) m => kernelLine F h)
      (flagAlong_eq_pullback E m f g)) ≪≫
    pullbackKernelLineIso (universalFlag E m) g.1
      (((Scheme.Modules.pullbackComp g.1 (tower m E).2).app E ≪≫
        (Scheme.Modules.pullbackCongr g.2).app E).symm) h

end Towers

end M9Native.FlagTowerLines
