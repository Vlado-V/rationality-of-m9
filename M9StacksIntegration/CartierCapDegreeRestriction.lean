module

public import M9StacksIntegration.ChowCapDegree
public import M9StacksIntegration.ClosedImmersionChernCap

/-!
# Actual cap-degree restriction to the original Cartier immersion

The final factor is the actual positive module of the original Cartier
ideal. Capping first with it gives pushforward of the actual source
fundamental class. The proved proper projection formula then restricts
all remaining actual modules to that same original source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CartierCapDegreeRestriction

open Stacks.Chow CurveTopChowClass ChowCapDegree

theorem identityChowClass_cast (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {d e : ℤ} (h : d = e) :
    chowGroupCast C f h (identityChowClass C f d) = identityChowClass C f e := by
  subst h
  rfl

theorem invCap_fundamental_succ (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i]
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor i.ker]
    (d : ℤ) (hn : schemeDeltaDimension C f = ((d + 1 : ℤ) : EInt)) :
    letI := Stacks.Divisors.isInvertible_invertibleSheaf_picard i.ker
    (invCap C f (Stacks.Divisors.modulesInvertibleSheaf i.ker)).capOnChow C f d
        (identityChowClass C f (d + 1)) =
      properChowPushforward C (i ≫ f) f i rfl d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (i ≫ f) f i rfl d)
        (identityChowClass C (i ≫ f) d) := by
  have h := ClosedImmersionChernCap.invCap_fundamental_eq_pushforward C f i (d + 1) hn
  have hd : d + 1 - 1 = d := by omega
  rw [hd] at h
  exact h

theorem isInvertible_snoc_divisor {X : Scheme.{u}} {m : ℕ} (L : Fin m → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (D : X.IdealSheafData) [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]
    (j : Fin (m + 1)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Fin.snoc (α := fun _ => X.Modules) L (Stacks.Divisors.modulesInvertibleSheaf D) j) := by
  refine Fin.lastCases ?_ (fun q => ?_) j
  · rw [Fin.snoc_last]
    exact @Stacks.Divisors.isInvertible_invertibleSheaf X D hD
  · rw [Fin.snoc_castSucc]
    infer_instance

theorem capDegree_snoc_divisor (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i]
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor i.ker]
    {m : ℕ} (L : Fin m → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hn : schemeDeltaDimension (fieldChowSituation k) f = (((m : ℤ) + 1) : EInt)) :
    letI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Fin.snoc (α := fun _ => X.Modules) L (Stacks.Divisors.modulesInvertibleSheaf i.ker) j) :=
        isInvertible_snoc_divisor L i.ker
    capDegree k f (Fin.snoc (α := fun _ => X.Modules) L (Stacks.Divisors.modulesInvertibleSheaf i.ker))
        (identityChowClass (fieldChowSituation k) f ((m + 1 : ℕ) : ℤ)) =
      capDegree k (i ≫ f) (fun j => (Scheme.Modules.pullback i).obj (L j))
        (identityChowClass (fieldChowSituation k) (i ≫ f) m) := by
  let : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Fin.snoc (α := fun _ => X.Modules) L (Stacks.Divisors.modulesInvertibleSheaf i.ker) j) :=
        isInvertible_snoc_divisor L i.ker
  rw [capDegree_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [identityChowClass_cast, invCap_fundamental_succ (fieldChowSituation k) f i m hn]
  exact (capDegree_properChowPushforward k f (i ≫ f) i rfl L
    (identityChowClass (fieldChowSituation k) (i ≫ f) m)).symm

end M9Native.CartierCapDegreeRestriction
