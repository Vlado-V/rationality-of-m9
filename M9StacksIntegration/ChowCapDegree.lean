/-
Generic cap-degree definitions and proofs replayed from pinned Stacks
Variety.NumericalIntersections.ChowDegree, section CapDegree. The
numerical intersection comparison and its additional imports are not
part of this leaf. Stacks source pin and exact hashes are recorded in
its source replay receipt; the original package is Apache-2.0.
-/
module

public import M9StacksIntegration.ChowCapWords
public import M9StacksIntegration.CurveSingleCapDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ChowCapDegree

open Stacks.Chow

theorem isInvertible_sheaf_of_presheaf {X : Scheme.{u}} (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := h

attribute [local instance] isInvertible_sheaf_of_presheaf

theorem iteratedChernCapOnChow_append_singleton (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Os : List (ChernCapOperator C f)) (O : ChernCapOperator C f) (d : ℤ)
    (x : chowGroup C f (d + ((Os ++ [O]).length : ℤ)))
    (y : chowGroup C f (d + (Os.length : ℤ) + 1)) (hxy : x ≍ y)
    (z : chowGroup C f (d + (Os.length : ℤ)))
    (hz : z ≍ O.capOnChow C f (d + (Os.length : ℤ)) y) :
    iteratedChernCapOnChow C f (Os ++ [O]) d x =
      iteratedChernCapOnChow C f Os d z := by
  rw [iteratedChernCapOnChow_append C f Os [O] d x y hxy,
    iteratedChernCapOnChow_singleton_eq C f O (d + (Os.length : ℤ)) y y (HEq.rfl)]
  exact congrArg (iteratedChernCapOnChow C f Os d) (eq_of_heq hz.symm)

section CapDegree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The iterated first Chern class cap** `α ↦ c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ α`, from `A_d(X)` to
`A_0(X)`, for a family of `d` invertible modules on a scheme proper over a field: the cap with
`c₁(𝓛_d)` is taken first and the cap with `c₁(𝓛_1)` last, each being the operation of
[Stacks, Tag 02TI]. -/
def iteratedFirstChernCap {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    chowGroup (fieldChowSituation k) f d →+ chowGroup (fieldChowSituation k) f 0 :=
  (iteratedChernCapOnChow (fieldChowSituation k) f
      (List.ofFn fun j => invCap (fieldChowSituation k) f (L j)) 0).comp
    (chowGroupCast (fieldChowSituation k) f (by simp)).toAddMonoidHom

/-- The degree `deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ α)` of the iterated first Chern class cap of a class
`α ∈ A_d(X)`, the degree being that of [Stacks, Tag 0AZ1]. -/
def capDegree {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    chowGroup (fieldChowSituation k) f d →+ ℤ :=
  (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
      (IsLocalRing.closedPoint k)).comp (iteratedFirstChernCap k f L)

/-- With no module the degree of the iterated cap is the degree of the class. -/
theorem capDegree_zero (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (a : chowGroup (fieldChowSituation k) f 0) :
    capDegree k f L a =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) a := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1

/-- **Peeling off the innermost cap.** The last module of the family is capped first. -/
theorem capDegree_succ {d : ℕ} (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (a : chowGroup (fieldChowSituation k) f ((d + 1 : ℕ) : ℤ)) :
    capDegree k f L a =
      capDegree k f (fun j : Fin d => L j.castSucc)
        ((invCap (fieldChowSituation k) f (L (Fin.last d))).capOnChow (fieldChowSituation k) f
          (d : ℤ)
          (chowGroupCast (fieldChowSituation k) f (by push_cast; ring) a)) := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine congrArg (chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)) ?_
  have hlist : (List.ofFn fun j => invCap (fieldChowSituation k) f (L j)) =
      (List.ofFn fun j : Fin d => invCap (fieldChowSituation k) f (L j.castSucc)) ++
        [invCap (fieldChowSituation k) f (L (Fin.last d))] := by
    rw [List.ofFn_succ', List.concat_eq_append]
  set C := fieldChowSituation k
  set Os := List.ofFn fun j : Fin d => invCap C f (L j.castSucc)
  set O := invCap C f (L (Fin.last d))
  have hOs : (Os.length : ℤ) = d := by simp [Os]
  have e₁ : ((d + 1 : ℕ) : ℤ) = 0 + ((Os ++ [O]).length : ℤ) := by
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, hOs]; ring
  have e₂ : ((d + 1 : ℕ) : ℤ) = 0 + (Os.length : ℤ) + 1 := by rw [hOs]; push_cast; ring
  have e₃ : (d : ℤ) = 0 + (Os.length : ℤ) := by rw [hOs]; ring
  refine chowGroup_eq_of_heq C f ((iteratedChernCapOnChow_heq_of_eq C f hlist 0
    (y := chowGroupCast C f e₁ a) ?_).trans ?_)
  · exact (chowGroupCast_heq C f _ a).trans (chowGroupCast_heq C f _ a).symm
  · rw [iteratedChernCapOnChow_append_singleton C f Os O 0 _ (chowGroupCast C f e₂ a)
      ((chowGroupCast_heq C f _ a).trans (chowGroupCast_heq C f _ a).symm)
      (chowGroupCast C f e₃ (O.capOnChow C f (d : ℤ)
          (chowGroupCast C f (by push_cast; ring) a)))]
    refine (chowGroupCast_heq C f _ _).trans ?_
    exact capOnChow_heq C f O e₃ ((chowGroupCast_heq C f _ a).trans
      (chowGroupCast_heq C f _ a).symm)

/-- **The degree is invariant under proper pushforward**: a zero cycle class and its proper
pushforward along a morphism of schemes proper over the field have the same degree. -/
theorem chowDegree_properChowPushforward {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY) (z : chowGroup (fieldChowSituation k) fY 0) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) fY
        (IsLocalRing.closedPoint k) z =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k)
        (properChowPushforward (fieldChowSituation k) fY f g hg 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            fY f g hg 0) z) := by
  subst hg
  simp only [chowDegree, AddMonoidHom.comp_apply]
  congr 1
  exact (properChowPushforward_properChowPushforward (fieldChowSituation k) (g ≫ f) f
    (𝟙 (fieldChowSituation k).S) g f rfl (Category.comp_id f) 0 z).symm

/-- **The degree of the iterated cap is invariant under proper pushforward**, by the projection
formula of Stacks 02SU:
`deg(c₁(g^*𝓛_1) ∩ ⋯ ∩ c₁(g^*𝓛_d) ∩ β) = deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ g_*β)`. -/
theorem capDegree_properChowPushforward {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY) {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (β : chowGroup (fieldChowSituation k) fY d) :
    capDegree k fY (fun j => (Scheme.Modules.pullback g).obj (L j)) β =
      capDegree k f L (properChowPushforward (fieldChowSituation k) fY f g hg d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
          fY f g hg d) β) := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [chowDegree_properChowPushforward k f fY g hg]
  refine congrArg (chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)) ?_
  set C := fieldChowSituation k
  have e₁ : (d : ℤ) = 0 + ((List.ofFn fun j =>
      invCap C fY ((Scheme.Modules.pullback g).obj (L j))).length : ℤ) := by simp
  have e₂ : (d : ℤ) = 0 + ((List.ofFn fun j => invCap C f (L j)).length : ℤ) := by simp
  set β' := properChowPushforward C fY f g hg d
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY f g hg d) β
  have hy : chowGroupCast C f e₂ β' ≍ properChowPushforward C fY f g hg _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY f g hg _)
        (chowGroupCast C fY e₁ β) :=
    (chowGroupCast_heq C f e₂ β').trans (properChowPushforward_heq C fY f g hg e₁
      (chowGroupCast_heq C fY e₁ β).symm)
  exact properChowPushforward_iteratedChernCapOnChow_ofFn C fY f g hg L 0
    (chowGroupCast C fY e₁ β) (chowGroupCast C f e₂ β') hy

end CapDegree

end M9Native.ChowCapDegree
