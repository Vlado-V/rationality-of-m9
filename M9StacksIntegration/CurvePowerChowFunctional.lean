module

public import M9StacksIntegration.ChowCapWords
public import M9StacksIntegration.CurvePowerGraphCartier
public import M9StacksIntegration.CurvePowerGraphContextInduction
public import M9StacksIntegration.CurveCapEulerDegree

/-!
# The literal Chow-cap degree functional on actual partition maps

Each factor is an actual invertible module, each cap is the native
first Chern cap, and the final map is the native proper zero-cycle
degree. The fundamental cycle is taken in its actual native grading.
There is no externally supplied intersection functional or recurrence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerChowFunctional

open Stacks.Chow CurveTopChowClass ChowCapWords CurvePowerGraphMaps
open CurvePowerGraphLocal

def chosenLine {X : Scheme.{u}} (x : Stacks.Picard.ofScheme X) : InvertibleLine X :=
  ⟨(Stacks.Picard.picardRepresentative X.toRingedSpace x).obj,
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).property⟩

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

def wordDegree (Ls : List (InvertibleLine X)) : ℤ :=
  chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
    f (IsLocalRing.closedPoint k)
    (iteratedChernCapOnChow (fieldChowSituation k) f
      (Ls.map (lineCap (fieldChowSituation k) f)) 0
      (identityChowClass (fieldChowSituation k) f
        (0 + ((Ls.map (lineCap (fieldChowSituation k) f)).length : ℤ))))

theorem wordDegree_perm {Ls Ms : List (InvertibleLine X)} (h : Ls.Perm Ms) :
    wordDegree k f Ls = wordDegree k f Ms := by
  unfold wordDegree
  congr 1
  apply iterated_lineCaps_eq_of_perm (fieldChowSituation k) f h
  have hd : (0 : ℤ) + ((Ls.map (lineCap (fieldChowSituation k) f)).length : ℤ) =
      0 + ((Ms.map (lineCap (fieldChowSituation k) f)).length : ℤ) := by
    simp only [List.length_map]
    rw [h.length_eq]
  have hh : ∀ d e : ℤ, d = e →
      HEq (identityChowClass (fieldChowSituation k) f d)
        (identityChowClass (fieldChowSituation k) f e) := by
    rintro d e rfl
    rfl
  exact hh _ _ hd

theorem wordDegree_nil_zero [IsIntegral X]
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) ≠ 0) :
    wordDegree k f [] = 0 := by
  change chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)
    (iteratedChernCapOnChow (fieldChowSituation k) f [] 0
      (identityChowClass (fieldChowSituation k) f 0)) = 0
  rw [identityChowClass_eq_zero_of_genericDimension_ne (fieldChowSituation k) f 0 hd,
    map_zero, map_zero]

theorem wordDegree_nil_base : wordDegree k (𝟙 (Spec (.of k))) [] = 1 := by
  change chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) (𝟙 (Spec (.of k)))
    (IsLocalRing.closedPoint k)
    (iteratedChernCapOnChow (fieldChowSituation k) (𝟙 (Spec (.of k))) [] 0
      (identityChowClass (fieldChowSituation k) (𝟙 (Spec (.of k))) 0)) = 1
  rw [chowGroup_eq_of_heq (fieldChowSituation k) (𝟙 (Spec (.of k)))
    (iteratedChernCapOnChow_nil_heq (fieldChowSituation k) (𝟙 (Spec (.of k))) 0 _)]
  rw [identityChowClass, chowDegree_mk, cycleDegree_id]
  have hδ : relativeDimension (fieldChowSituation k).dimensionFunction
      (𝟙 (fieldChowSituation k).S) (genericPoint (fieldChowSituation k).S) = 0 := by
    rw [relativeDimension_id]
    exact fieldChowSituation_dimensionFunction_eq_zero k _
  rw [cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation k)
    (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) 0 hδ]
  have hs : (IsLocalRing.closedPoint k : (fieldChowSituation k).S) =
      genericPoint (fieldChowSituation k).S := Subsingleton.elim _ _
  simp [hs]

variable (C : Over (Spec (.of k))) [IsProper C.hom]
  (c₀ : power C 0 ⟶ C)

abbrev LineClass {S : Scheme.{u}} (D : Over S) (n : ℕ) : Type (u + 1) :=
  Stacks.Picard.ofScheme (power D n).left

def partitionFunctional (ambient : ℕ) (word : List (LineClass C ambient)) (s : State) : ℤ :=
  wordDegree k (power C s.length).hom (word.map fun x =>
    chosenLine (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left x))

theorem partitionFunctional_perm (ambient : ℕ) {word word' : List (LineClass C ambient)}
    (h : word.Perm word') (s : State) :
    partitionFunctional k C c₀ ambient word s =
      partitionFunctional k C c₀ ambient word' s :=
  wordDegree_perm k _ (h.map _)

theorem partitionFunctional_nil_positive [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (ambient : ℕ) (s : State) (hs : 0 < s.length) :
    partitionFunctional k C c₀ ambient [] s = 0 := by
  have : IsIntegral (power C s.length).left := (isVariety_power C s.length).toIsIntegral
  apply wordDegree_nil_zero k (power C s.length).hom
  have hdim : topologicalKrullDim (power C s.length).left =
      (s.length : WithBot ℕ∞) := by
    rw [(isVariety_power_and_topologicalKrullDim C s.length).2, hC, mul_one]
  rw [relativeDimension_fieldChowSituation_genericPoint (power C s.length).hom hdim]
  exact_mod_cast Nat.ne_of_gt hs

abbrev Letter (ambient : ℕ) := Fin ambient ⊕ (Fin ambient × Fin ambient)

variable [SmoothOfRelativeDimension 1 C.hom]

def letterClass (ambient : ℕ) : Letter ambient → LineClass C ambient
  | .inl i => Stacks.Picard.schemePullbackClass
      (reindex C (fun _ : Fin 1 => i)).left (CurvePowerGraphCartier.graphClass C 0 c₀)
  | .inr (i, j) => Stacks.Picard.schemePullbackClass
      (reindex C ![i, j]).left (CurvePowerGraphCartier.graphClass C 1 (coord C 1 0))

def tautologicalFunctional (ambient : ℕ) (word : List (Letter ambient)) (s : State) : ℤ :=
  partitionFunctional k C c₀ ambient (word.map (letterClass k C c₀ ambient)) s

theorem tautologicalFunctional_perm (ambient : ℕ) {word word' : List (Letter ambient)}
    (h : word.Perm word') (s : State) :
    tautologicalFunctional k C c₀ ambient word s =
      tautologicalFunctional k C c₀ ambient word' s :=
  partitionFunctional_perm k C c₀ ambient (h.map _) s

theorem tautologicalFunctional_nil_positive [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (ambient : ℕ) (s : State) (hs : 0 < s.length) :
    tautologicalFunctional k C c₀ ambient [] s = 0 :=
  partitionFunctional_nil_positive k C c₀ hC ambient s hs

theorem actual_gamma_empty [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (t : ℤ) (ambient : ℕ)
    (ctx : CurvePowerGraphContextInduction.ValidContext) :
    CurvePowerGraphInduction.gammaValue t
      (CurvePowerGraphContextInduction.transported (tautologicalFunctional k C c₀ ambient))
      ctx [] = 0 := by
  exact CurvePowerGraphContextInduction.gammaValue_nil t
    (tautologicalFunctional k C c₀ ambient)
    (fun s hs => tautologicalFunctional_nil_positive k C c₀ hC ambient s hs) ctx

end M9Native.CurvePowerChowFunctional
