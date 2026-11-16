module

public import M9StacksIntegration.ChowCapDegreePicard

/-!
# Actual Cartier graph restriction on finite Picard families

The canonical representatives are compared by actual module
isomorphisms. The resulting restriction is the already-proved Cartier
cap-degree formula on the original immersion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.PicardCartierCapDegreeRestriction

open Stacks.Chow CurveTopChowClass ChowCapDegree ChowCapDegreePicard CurvePowerChowFunctional

attribute [local instance] ChowCapDegree.isInvertible_sheaf_of_presheaf
  ChowCapDegreePicard.chosenLine_isInvertible

theorem capDegreePicard_pullback_eq (k : Type u) [Field k] {X Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) [IsProper fY] (g : Y ⟶ X)
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X) :
    capDegreePicard k fY (fun j => Stacks.Picard.schemePullbackClass g (x j)) =
      capDegree k fY (fun j => (Scheme.Modules.pullback g).obj (chosenLine (x j)).1) := by
  apply capDegree_congr_iso
  intro j
  exact nonempty_chosenLine_pullback_iso g (x j)

theorem capDegreePicard_snoc_divisor (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i]
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor i.ker]
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X)
    (hn : schemeDeltaDimension (fieldChowSituation k) f = (((m : ℤ) + 1) : EInt)) :
    capDegreePicard k f
        (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme X) x (Stacks.Divisors.picardClass i.ker))
        (identityChowClass (fieldChowSituation k) f ((m + 1 : ℕ) : ℤ)) =
      capDegreePicard k (i ≫ f) (fun j => Stacks.Picard.schemePullbackClass i (x j))
        (identityChowClass (fieldChowSituation k) (i ≫ f) m) := by
  let L : Fin m → X.Modules := fun j => (chosenLine (x j)).1
  let M : Fin (m + 1) → X.Modules :=
    Fin.snoc (α := fun _ => X.Modules) L (Stacks.Divisors.modulesInvertibleSheaf i.ker)
  let : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j) :=
    fun j => chosenLine_isInvertible (x j)
  let hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j) :=
    CartierCapDegreeRestriction.isInvertible_snoc_divisor L i.ker
  have hc : (fun j => Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf (M j) (hM j)) =
      Fin.snoc (α := fun _ => Stacks.Picard.ofScheme X) x (Stacks.Divisors.picardClass i.ker) := by
    funext j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · rw [Fin.snoc_last]
      apply (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr
      exact ⟨eqToIso (by dsimp only [M]; rw [Fin.snoc_last]; rfl)⟩
    · rw [Fin.snoc_castSucc]
      have hh : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
          (M q.castSucc) (hM q.castSucc) =
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
          (chosenLine (x q)).1 (chosenLine (x q)).2 := by
        apply (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr
        exact ⟨eqToIso (by dsimp only [M]; rw [Fin.snoc_castSucc])⟩
      exact hh.trans (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace (x q))
  have hleft : capDegreePicard k f
        (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme X) x (Stacks.Divisors.picardClass i.ker)) =
      capDegree k f M := by
    rw [← hc]
    exact capDegreePicard_classes k f M
  rw [hleft]
  rw [CartierCapDegreeRestriction.capDegree_snoc_divisor k f i L hn]
  rw [capDegreePicard_pullback_eq k (i ≫ f) i x]

end M9Native.PicardCartierCapDegreeRestriction
