module

public import M9StacksIntegration.PoincareFiniteFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum

/-!
# The genuine integral Chow Chern family of an actual free bundle

The literal native free sheaf on ULift(Fin r) has rank r. Its successor
is genuinely isomorphic to the biproduct of the rank-r free bundle and
the rank-one free bundle. The actual split short exact sequence,
native Whitney and the genuine unit-line isomorphism prove c(O^r)=1.

The final endpoint accepts an actual bundle isomorphism to this free
sheaf. A K-zero rank relation or a Chern-vanishing premise is not used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowFreeBundleChern

/-- The actual free sheaf in the ordinary-bundle normalization API. -/
abbrev freeBundle (X : Scheme.{u}) (r : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))

local instance freeRank (X : Scheme.{u}) (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeBundle X r) r :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r

/-- The actual free line, with the genuine free-on-PUnit unit iso. -/
def freeOneIsoUnit (X : Scheme.{u}) :
    freeBundle X 1 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u+1}).toIso ≪≫
      Stacks.SheafOfModules.Site.freePUnitIso

/-- Reindexing the actual free basis gives the actual successor
biproduct, with its actual structural injection and projection. -/
def freeSuccIsoBiprod (X : Scheme.{u}) (r : ℕ) :
    freeBundle X (r+1) ≅ freeBundle X r ⊞ freeBundle X 1 := by
  let ei : ULift.{u} (Fin (r+1)) ≃ ULift.{u} (Fin r) ⊕ ULift.{u} (Fin 1) :=
    Equiv.ulift.trans ((finSumFinEquiv (m := r) (n := 1)).symm.trans
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
  exact (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso ei.toIso ≪≫
    (SheafOfModules.freeSumIso (R := X.ringCatSheaf)
      (ULift.{u} (Fin r)) (ULift.{u} (Fin 1))).symm ≪≫
        (biprod.isoCoprod (freeBundle X r) (freeBundle X 1)).symm

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

/-- The actual free bundle has actual Chern cap family one on every
original integral Chow group, by genuine split rows and Whitney. -/
theorem chernFamily_free (r : ℕ) :
    chernFamily C q (freeBundle X r) r = 1 := by
  have hone : chernFamily C q (freeBundle X 1) 1 = 1 :=
    chernFamily_eq_one_of_iso_unit C q (freeBundle X 1) (freeOneIsoUnit X)
  induction r with
  | zero => exact chernFamily_of_rank_zero C q (freeBundle X 0)
  | succ r ih =>
    let E : X.Modules := freeBundle X r
    let F : X.Modules := freeBundle X 1
    let i : E ⟶ E ⊞ F := biprod.inl
    let p : E ⊞ F ⟶ F := biprod.snd
    have w : i ≫ p = 0 := biprod.inl_snd
    have hS : (ShortComplex.mk i p w).ShortExact :=
      (ShortComplex.Splitting.ofHasBinaryBiproduct E F).shortExact
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E ⊞ F) (r+1) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (freeSuccIsoBiprod X r)
        (freeRank X (r+1))
    have hW := chernFamily_eq_mul_of_shortExact C q (ShortComplex.mk i p w) hS r 1
    have hE : chernFamily C q (freeBundle X (r+1)) (r+1) =
        chernFamily C q (E ⊞ F) (r+1) :=
      chernFamily_congr C q (E ⊞ F) (r+1) (freeSuccIsoBiprod X r) rfl
    rw [hE, hW, ih, hone, one_mul]

/-- A genuine actual free trivialization, rather than a rank relation
in K-zero, gives the same proved Chern-family conclusion. -/
theorem chernFamily_eq_one_of_iso_free (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :
    chernFamily C q E r = 1 := by
  rw [chernFamily_congr C q (freeBundle X r) r e rfl, chernFamily_free]

end M9Native.ChowFreeBundleChern
