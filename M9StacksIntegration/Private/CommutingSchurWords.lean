module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Tactic.NoncommRing

/-!
# Ordered Schur words in an arbitrary ring

Only the displayed commutation hypotheses are used. In particular the ambient
ring need not be commutative; actual operator commutation must be supplied by
the geometric application.
-/

@[expose] public section

universe u

namespace M9Native.CommutingSchurWords

variable {R : Type u} [Ring R]

/-- The six-word order change uses just these six pairwise commutations. -/
theorem schur_words_of_commute (a1 a2 a3 a4 a5 : R)
    (h14 : Commute a1 a4) (h24 : Commute a2 a4) (h25 : Commute a2 a5)
    (h13 : Commute a1 a3) (h15 : Commute a1 a5) (h35 : Commute a3 a5) :
    a3*a3*a3 - a3*a2*a4 - a2*a4*a3 + a2*a2*a5 + a1*a4*a4 - a1*a3*a5 =
      a3*a3*a3 - a3*a4*a2 - a4*a2*a3 + a4*a4*a1 + a5*a2*a2 - a5*a3*a1 := by
  have h324 := h24.right_comm a3
  have h243 := congrArg (fun z : R => z*a3) h24.eq
  have h225 := (h25.right_comm a2).trans (congrArg (fun z : R => z*a2) h25.eq)
  have h144 := (congrArg (fun z : R => z*a4) h14.eq).trans (h14.right_comm a4)
  have h135 := (h35.right_comm a1).trans
    ((congrArg (fun z : R => z*a3) h15.eq).trans (h13.right_comm a5))
  rw [h324,h243,h225,h144,h135]
  abel

/-- With five indexed operators, index0 corresponds to a1 and index4 to a5. -/
theorem schur_words_of_pairwise (a : Fin 5 → R)
    (h : Pairwise (fun i j => Commute (a i) (a j))) :
    a 2*a 2*a 2 - a 2*a 1*a 3 - a 1*a 3*a 2 + a 1*a 1*a 4 +
        a 0*a 3*a 3 - a 0*a 2*a 4 =
      a 2*a 2*a 2 - a 2*a 3*a 1 - a 3*a 1*a 2 + a 3*a 3*a 0 +
        a 4*a 1*a 1 - a 4*a 2*a 0 :=
  schur_words_of_commute (a 0) (a 1) (a 2) (a 3) (a 4)
    (@h 0 3 (by decide)) (@h 1 3 (by decide)) (@h 1 4 (by decide))
    (@h 0 2 (by decide)) (@h 0 4 (by decide)) (@h 2 4 (by decide))

/-- The intermediate quadratic expansion commutes x only with c1,c2,c3.
The coefficient c3*c2 keeps its literal order. -/
theorem middle_quadratic (x c1 c2 c3 c4 : R)
    (h1 : Commute x c1) (h2 : Commute x c2) (h3 : Commute x c3) :
    (c3-x*c2)*(c3-x*c2) - (c2-x*c1)*(c4-x*c3) =
      c3*c3 - c2*c4 + x*(c1*c4-c3*c2) + (x*x)*(c2*c2-c1*c3) := by
  noncomm_ring [h1.symm.eq,h2.symm.eq,h3.symm.eq,
    h1.symm.left_comm,h2.symm.left_comm,h3.symm.left_comm]

end M9Native.CommutingSchurWords
