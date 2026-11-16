module

public import M9StacksIntegration.CurvePowerGammaDiagonal

/-!
# Actual modified-diagonal vanishing against all tautological words

Every restriction step is constructed from the actual point and
diagonal caps. The context is selected by the proved finite-mask
algorithm. The local certificates rebase it to a shorter word, and
the actual empty-word value is zero by positive curve-power dimension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGammaVanishing

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphInduction CurvePowerGraphContextSelection CurvePowerGammaPoint
open CurvePowerChowFunctional CurvePowerDiagonalSelfRestriction

def child (t : ℤ) (frame : AdmissibleFrame) (kind : LocalKind) :
    Option (ℤ × AdmissibleFrame) :=
  match h : rebase t frame.val kind with
  | none => none
  | some (w,c) => some (w, ⟨c, admissible_rebase t frame.val frame.property kind w c h⟩)

theorem child_val (t : ℤ) (frame : AdmissibleFrame) (kind : LocalKind) :
    (child t frame kind).map (fun (w,c) => (w,c.val)) = rebase t frame.val kind := by
  unfold child
  split <;> simp_all

def descendant {Factor : Type*} (t : ℤ) (frame : AdmissibleFrame) (kind : LocalKind)
    (tail : List Factor) : Option (Descendant AdmissibleFrame Factor) :=
  (child t frame kind).map fun (w,c) => ⟨w,c,tail⟩

theorem descendant_length {Factor : Type*} (t : ℤ) (frame : AdmissibleFrame)
    (kind : LocalKind) (tail : List Factor) (d : Descendant AdmissibleFrame Factor)
    (hd : descendant t frame kind tail = some d) : d.word.length ≤ tail.length := by
  cases hc : child t frame kind with
  | none => simp [descendant, hc] at hd
  | some p =>
      rcases p with ⟨w,c⟩
      have he : (⟨w,c,tail⟩ : Descendant AdmissibleFrame Factor) = d := by
        simpa only [descendant, hc, Option.map_some, Option.some.injEq] using hd
      rw [← he]

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem expected_descendant (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame)
    (kind : LocalKind) (tail : List (Letter ambient)) :
    realization t (tautologicalFunctional k C c₀ ambient tail ∘ transport frame.val)
        (expected kind) =
      descendantValue t (actualFunctional k C c₀ ambient) (descendant t frame kind tail) := by
  have he := expected_rebase t (tautologicalFunctional k C c₀ ambient tail) frame.val kind
  have hv := child_val t frame kind
  cases hc : child t frame kind with
  | none =>
      have hr : rebase t frame.val kind = none := by
        simpa only [hc, Option.map_none] using hv.symm
      simpa only [hr, rebasedValue, descendant, hc, Option.map_none, descendantValue] using he
  | some p =>
      rcases p with ⟨w,c⟩
      have hr : rebase t frame.val kind = some (w,c.val) := by
        simpa only [hc, Option.map_some] using hv.symm
      simp only [descendant, hc, Option.map_some, descendantValue, gammaValue]
      have hf : actualFunctional k C c₀ ambient c tail =
          tautologicalFunctional k C c₀ ambient tail ∘ transport c.val := by
        funext s
        rfl
      rw [hf]
      simpa only [hr, rebasedValue, Function.comp_apply] using he

variable [IsAlgClosed k] [IsVariety k C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem gammaValue_nil (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame) :
    gammaValue t (actualFunctional k C c₀ ambient) frame [] = 0 := by
  let ctx : CurvePowerGraphContextInduction.ValidContext := ⟨frame.val,frame.property.1⟩
  have hf : actualFunctional k C c₀ ambient frame [] =
      CurvePowerGraphContextInduction.transported (tautologicalFunctional k C c₀ ambient) ctx [] := by
    funext s
    rfl
  exact (congrArg (fun A : State → ℤ => realization t A (embed localGamma)) hf).trans
    (CurvePowerChowFunctional.actual_gamma_empty k C c₀ hC t ambient ctx)

theorem exists_restrictionStep (ambient : ℕ) (frame : AdmissibleFrame)
    (factor : Letter ambient) (tail : List (Letter ambient)) :
    Nonempty (RestrictionStep (selfDegree k C hC) (actualFunctional k C c₀ ambient)
      frame factor tail) := by
  let t := selfDegree k C hC
  let F := actualFunctional k C c₀ ambient
  have hzero (c : Combination) : realization t (fun _ : State => (0 : ℤ)) c = 0 :=
    realization_zero_of_keys t (fun _ => 0) c (fun _ _ => rfl)
  let zeroStep (hz : gammaValue t F frame (factor :: tail) = 0) :
      RestrictionStep t F frame factor tail := {
    kind := .point 0
    afterRestriction := fun _ => 0
    descendant := none
    length_le := fun _ hd => by cases hd
    restriction_eq := hz.trans (hzero (action (.point 0))).symm
    rebase_eq := hzero (expected (.point 0)) }
  let actionStep (next : AdmissibleFrame) (kind : LocalKind)
      (hr : gammaValue t F frame (factor :: tail) =
        realization t (tautologicalFunctional k C c₀ ambient tail ∘ transport next.val)
          (action kind)) : RestrictionStep t F frame factor tail := {
    kind := kind
    afterRestriction := tautologicalFunctional k C c₀ ambient tail ∘ transport next.val
    descendant := descendant t next kind tail
    length_le := fun d hd => descendant_length t next kind tail d hd
    restriction_eq := hr
    rebase_eq := expected_descendant k C c₀ t ambient next kind tail }
  cases factor with
  | inl v =>
      let next := selectedFrame frame v.val v.val
      have hsel := gammaValue_selectedFrame k C c₀ t ambient frame v.val v.val (.inl v :: tail)
      have hc := selectPair_covered_or_marked frame.val frame.property v.val v.val v.val (Or.inl rfl)
      rcases hc with ⟨i,hi⟩ | ⟨hl,hs⟩
      · exact ⟨actionStep next (.point i) (hsel.trans
          (gammaValue_point_restriction k C c₀ hC t ambient next i v hi tail))⟩
      · exact ⟨zeroStep (hsel.trans (gammaValue_point_marked k C c₀ t ambient next v tail hl hs))⟩
  | inr p =>
      rcases p with ⟨v,w⟩
      let next := selectedFrame frame v.val w.val
      have hsel := gammaValue_selectedFrame k C c₀ t ambient frame v.val w.val (.inr (v,w) :: tail)
      have hv := selectPair_covered_or_marked frame.val frame.property v.val w.val v.val (Or.inl rfl)
      have hw := selectPair_covered_or_marked frame.val frame.property v.val w.val w.val (Or.inr rfl)
      rcases hv with ⟨i,hi⟩ | ⟨hlv,hsv⟩
      · rcases hw with ⟨j,hj⟩ | ⟨hlw,hsw⟩
        · exact ⟨actionStep next (.diagonal i j) (hsel.trans
            (CurvePowerGammaDiagonal.gammaValue_diagonal_restriction k C c₀ hC
              ambient next i j v w hi hj tail))⟩
        · have hm := CurvePowerGammaDiagonal.gammaValue_diagonal_right_marked
            k C c₀ t ambient next v w tail hlw hsw
          exact ⟨actionStep next (.point i) (hsel.trans (hm.trans
            (gammaValue_point_restriction k C c₀ hC t ambient next i v hi tail)))⟩
      · rcases hw with ⟨j,hj⟩ | ⟨hlw,hsw⟩
        · have hm := CurvePowerGammaDiagonal.gammaValue_diagonal_left_marked
            k C c₀ t ambient next v w tail hlv hsv
          exact ⟨actionStep next (.point j) (hsel.trans (hm.trans
            (gammaValue_point_restriction k C c₀ hC t ambient next j w hj tail)))⟩
        · have hm := CurvePowerGammaDiagonal.gammaValue_diagonal_left_marked
            k C c₀ t ambient next v w tail hlv hsv
          exact ⟨zeroStep (hsel.trans (hm.trans
            (gammaValue_point_marked k C c₀ t ambient next w tail hlw hsw)))⟩

def restrictionStep (ambient : ℕ) (frame : AdmissibleFrame)
    (factor : Letter ambient) (tail : List (Letter ambient)) :
    RestrictionStep (selfDegree k C hC) (actualFunctional k C c₀ ambient) frame factor tail :=
  Classical.choice (exists_restrictionStep k C c₀ hC ambient frame factor tail)

theorem gammaValue_eq_zero (ambient : ℕ) (frame : AdmissibleFrame)
    (word : List (Letter ambient)) :
    gammaValue (selfDegree k C hC) (actualFunctional k C c₀ ambient) frame word = 0 :=
  CurvePowerGraphKeyInduction.gammaValue_zero_of_nil_and_restrictions
    (selfDegree k C hC) (actualFunctional k C c₀ ambient)
    (fun frame => gammaValue_nil k C c₀ hC (selfDegree k C hC) ambient frame)
    (fun frame factor tail => restrictionStep k C c₀ hC ambient frame factor tail)
    frame word

end M9Native.CurvePowerGammaVanishing
