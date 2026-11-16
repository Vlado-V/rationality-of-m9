module

public import M9StacksIntegration.ChowFreeBundleChern
public import M9StacksIntegration.ChowLineFamilyComparison
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.FreeTensorTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist

/-!
# The genuine total Chern family of an actual free line twist

The literal original free sheaf has a proved successor biproduct.
Actual tensor colimit preservation and its actual unit isomorphism
give the successor biproduct for its line twist. Genuine split exact
rows, native Whitney, and the frozen rank-one line-cap comparison then
give c(O^r tensor N)=(1+lineFamily N)^r. No Chern-product or K-zero
formula is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowFreeLineTensor

open ChowCapWords GradedLineCapSubring ChowFreeBundleChern

variable {X : Scheme.{u}}

/-- The original scheme tensor object, with its original free first factor. -/
abbrev freeTensor (N : InvertibleLine X) (r : ℕ) : X.Modules :=
  Scheme.Modules.tensorObj (freeBundle X r) N.1

local instance freeRank (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeBundle X r) r :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r

local instance lineRank (N : InvertibleLine X) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X N.1 N.2

local instance tensorRank (N : InvertibleLine X) (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeTensor N r) r := by
  letI := N.2
  exact isFiniteLocallyFreeOfRank_sheafTensor (freeBundle X r) r N.1

/-- Tensoring the original free-line unit isomorphism gives the actual named line. -/
def freeOneTensorIso (N : InvertibleLine X) : freeTensor N 1 ≅ N.1 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj N.1).mapIso
    (freeOneIsoUnit X) ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 N.1

/-- The actual tensor functor carries the proved original free successor
splitting to an actual split successor row with quotient N. -/
def freeSuccTensorIso (N : InvertibleLine X) (r : ℕ) :
    freeTensor N (r+1) ≅ freeTensor N r ⊞ N.1 := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj N.1
  letI := Stacks.preservesColimitsOfSize_sheafTensorRight.{u,u,u,u} X.sheaf N.1
  exact T.mapIso (freeSuccIsoBiprod X r) ≪≫
    T.mapIso (biprod.isoCoprod (freeBundle X r) (freeBundle X 1)) ≪≫
    (PreservesColimitPair.iso T (freeBundle X r) (freeBundle X 1)).symm ≪≫
    (biprod.isoCoprod (T.obj (freeBundle X r)) (T.obj (freeBundle X 1))).symm ≪≫
    biprod.mapIso (Iso.refl _) (freeOneTensorIso N)

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The actual total Chern family equals the power of the ORIGINAL line-cap family. -/
theorem chernFamily_freeTensor (N : InvertibleLine X) (r : ℕ) :
    chernFamily C q (freeTensor N r) r = (1 + lineFamily C q N)^r := by
  induction r with
  | zero =>
    rw [pow_zero]
    exact chernFamily_of_rank_zero C q (freeTensor N 0)
  | succ r ih =>
    let E : X.Modules := freeTensor N r
    let F : X.Modules := N.1
    let i : E ⟶ E ⊞ F := biprod.inl
    let p : E ⊞ F ⟶ F := biprod.snd
    have w : i ≫ p = 0 := biprod.inl_snd
    have hS : (ShortComplex.mk i p w).ShortExact :=
      (ShortComplex.Splitting.ofHasBinaryBiproduct E F).shortExact
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E ⊞ F) (r+1) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (freeSuccTensorIso N r)
        (tensorRank N (r+1))
    have hW := chernFamily_eq_mul_of_shortExact C q (ShortComplex.mk i p w) hS r 1
    have hE : chernFamily C q (freeTensor N (r+1)) (r+1) =
        chernFamily C q (E ⊞ F) (r+1) :=
      chernFamily_congr C q (E ⊞ F) (r+1) (freeSuccTensorIso N r) rfl
    rw [hE, hW, ih, ChowLineFamilyComparison.chernFamily_eq_one_add_lineFamily C q N,
      pow_succ]

/-- A genuine bundle isomorphism to the original free line twist gives
the same genuine Chern identity, without a K-zero or product premise. -/
theorem chernFamily_of_iso_freeTensor (E : X.Modules) (N : InvertibleLine X) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (e : E ≅ Scheme.Modules.tensorObj
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) N.1) :
    chernFamily C q E r = (1 + lineFamily C q N)^r :=
  (chernFamily_congr C q (freeTensor N r) r e rfl).trans (chernFamily_freeTensor C q N r)

end M9Native.ChowFreeLineTensor
