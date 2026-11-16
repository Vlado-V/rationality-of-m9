module

public import M9StacksIntegration.SymmetricSquareBundleDeterminant
public import M9StacksIntegration.SchemeWedgeDuality
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# Actual sections of the dual on a finite-free open

The comparison evaluates the original native local module morphism.
Its bijectivity is proved from genuine original finite-free frames.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.SymmetricSquareBundleDeterminant

universe u

namespace M9Native.SymmetricSquareDualSections

variable {X : Scheme.{u}}

/-- Actual evaluation of a native local dual morphism on the original sections. -/
def dualSectionsMap (F : X.Modules) (U : X.Opens) :
    Γ(dualSheaf F, U) →ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(F, U) where
  toFun a :=
    { toFun x := Stacks.SheafOfModules.evalSection X.presheaf F.val (SheafOfModules.unit X.ringCatSheaf).val (op U) a x
      map_add' x y := Stacks.SheafOfModules.evalSection_add_right _ _ _ _ a x y
      map_smul' r x := Stacks.SheafOfModules.evalSection_smul_right _ _ _ _ r a x }
  map_add' a b := LinearMap.ext fun x =>
    Stacks.SheafOfModules.evalSection_add_left _ _ _ _ a b x
  map_smul' r a := LinearMap.ext fun x =>
    Stacks.SheafOfModules.evalSection_smul_left _ _ _ _ r a x

/-- Its literal restriction equation retains the original scalar map. -/
theorem dualSectionsMap_restrict (F : X.Modules) (U V : X.Opens) (h : V ≤ U)
    (a : Γ(dualSheaf F, U)) (x : Γ(F, U)) :
    dualSectionsMap F V ((dualSheaf F).presheaf.map (homOfLE h).op a)
        (F.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h).op (dualSectionsMap F U a x) :=
  Stacks.SheafOfModules.evalSection_naturality X.presheaf F.val (SheafOfModules.unit X.ringCatSheaf).val
    (homOfLE h).op a x

/-- The basis of the original restricted sections supplied by an actual frame. -/
def freeBasisOver (F : X.Modules) (W : X.Opens) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (V : (Over W)ᵒᵖ) : Module.Basis I ((X.ringCatSheaf.over W).obj.obj V)
      ((F.over W).val.obj V) := by
  letI : DecidableEq I := Classical.decEq I
  exact (Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj)
    (ι := I) (X.ringCatSheaf.over W).property V).map
      (((SheafOfModules.evaluation (X.ringCatSheaf.over W) V).mapIso e).toLinearEquiv.symm)

theorem freeBasisOver_apply (F : X.Modules) (W : X.Opens) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (V : (Over W)ᵒᵖ) (i : I) :
    letI : DecidableEq I := Classical.decEq I
    freeBasisOver F W I e V i = e.inv.val.app V
      (Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj)
        (ι := I) (X.ringCatSheaf.over W).property V i) := by
  letI : DecidableEq I := Classical.decEq I
  exact Module.Basis.map_apply _ _ _

/-- The true finite-free evaluation comparison is bijective. -/
theorem dualSectionsMap_bijective_of_iso_free_over (F : X.Modules) (W : X.Opens)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    Function.Bijective (dualSectionsMap F W) := by
  classical
  let T := Over.mk (𝟙 W)
  let hT := SchemeWedgeDuality.TerminalOver.isTerminalMkId W
  let b := freeBasisOver F W I e
  have hb : ∀ (V : (Over W)ᵒᵖ) (i : I),
      (F.over W).val.map (hT.from V.unop).op (b (op T) i) = b V i := by
    intro V i
    have hn := PresheafOfModules.naturality_apply e.inv.val (hT.from V.unop).op
      (Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj) (ι := I)
        (X.ringCatSheaf.over W).property (op T) i)
    have hf := Stacks.SheafOfModules.freeCoordBasis_map
      (O := (X.sheaf.over W).obj) (ι := I) (X.ringCatSheaf.over W).property
      (hT.from V.unop).op i
    change (F.over W).val.map (hT.from V.unop).op
      (freeBasisOver F W I e (op T) i) = freeBasisOver F W I e V i
    rw [freeBasisOver_apply, freeBasisOver_apply]
    exact hn.symm.trans (congrArg (fun z => e.inv.val.app V z) hf)
  have hbij := SchemeWedgeDuality.TerminalBasis.bijective_evalBasis hT b hb
    (Q := ((SheafOfModules.unit X.ringCatSheaf).over W).val)
  refine ⟨?_, ?_⟩
  · intro a c hac
    apply hbij.1
    funext i
    exact DFunLike.congr_fun hac (b (op T) i)
  · intro l
    obtain ⟨a, ha⟩ := hbij.2 (fun i => l (b (op T) i))
    refine ⟨a, ?_⟩
    apply (b (op T)).ext
    intro i
    exact congrFun ha i

/-- The original free frame restricted to a smaller open, using the native slice comparison. -/
def originalFrameOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u)
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    F.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) I :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso e ≪≫
      SchemeWedgeDuality.overMapFreeIso (J := Opens.grothendieckTopology X)
        (Osharp := X.sheaf) (homOfLE h) I

/-- The canonical evaluation map is an equivalence on every open in the genuine free frame. -/
def dualSectionsEquivOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    Γ(dualSheaf F, U) ≃ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(F, U) :=
  LinearEquiv.ofBijective (dualSectionsMap F U)
    (dualSectionsMap_bijective_of_iso_free_over F U I (originalFrameOn F W U h I e))

@[simp] theorem dualSectionsEquivOn_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (a : Γ(dualSheaf F, U)) :
    dualSectionsEquivOn F W U h I e a = dualSectionsMap F U a := rfl

/-- Genuine finite freeness of the original section module on that original frame. -/
theorem moduleFreeOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    Module.Free Γ(X, U) Γ(F, U) :=
  Module.Free.of_basis (freeBasisOver F U I (originalFrameOn F W U h I e) (op (Over.mk (𝟙 U))))

/-- Genuine finite generation of the same original section module. -/
theorem moduleFiniteOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    Module.Finite Γ(X, U) Γ(F, U) :=
  Module.Finite.of_basis (freeBasisOver F U I (originalFrameOn F W U h I e) (op (Over.mk (𝟙 U))))

end M9Native.SymmetricSquareDualSections
