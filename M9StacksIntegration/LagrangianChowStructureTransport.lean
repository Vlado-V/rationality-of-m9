module

public import M9StacksIntegration.LagrangianFlagFundamentalTransport
public import M9StacksIntegration.LagrangianChowPolynomials

/-! Transport of the same actual operational caps along equality of
the original structure maps. No pullback along a new morphism is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.LagrangianChowStructureTransport

open ChowCapWords GradedLineCapSubring LagrangianFlagFundamentalTransport

variable (C : ChowSituation.{u}) {X : Scheme.{u}}
  (q q' : X ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q')

/-- The operational ring is transported only along a true map equality. -/
def familyEquiv : GradedCapFamily (chowGroup C q) ≃+* GradedCapFamily (chowGroup C q') := by
  subst q'
  exact RingEquiv.refl _

theorem familyEquiv_apply (A : GradedCapFamily (chowGroup C q))
    (k : ℤ) (i : ℕ) (α : chowGroup C q k) :
    familyEquiv C q q' h A k i (structureMapCast C q q' h k α) =
      structureMapCast C q q' h (k-(i:ℤ)) (A k i α) := by
  subst q'
  rfl

theorem familyEquiv_lineFamily (L : InvertibleLine X) :
    familyEquiv C q q' h (lineFamily C q L) = lineFamily C q' L := by
  subst q'
  rfl

theorem familyEquiv_chernFamily (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] :
    familyEquiv C q q' h (chernFamily C q E r) = chernFamily C q' E r := by
  subst q'
  rfl

theorem familyEquiv_evaluate (L : Fin 3 → InvertibleLine X)
    (P : MvPolynomial (Fin 3) ℤ) :
    familyEquiv C q q' h (LagrangianChowPolynomials.evaluate C q L P) =
      LagrangianChowPolynomials.evaluate C q' L P := by
  subst q'
  rfl

/-- The literal evaluated cap commutes with the same structure-map transport. -/
theorem evaluate_structureMapCast (L : Fin 3 → InvertibleLine X)
    (P : MvPolynomial (Fin 3) ℤ) (k : ℤ) (i : ℕ) (α : chowGroup C q k) :
    structureMapCast C q q' h (k-(i:ℤ))
      (LagrangianChowPolynomials.evaluate C q L P k i α) =
        LagrangianChowPolynomials.evaluate C q' L P k i
          (structureMapCast C q q' h k α) := by
  subst q'
  rfl

/-- The same identity with the output grade transported explicitly. -/
theorem evaluate_capTo_structureMapCast (L : Fin 3 → InvertibleLine X)
    (P : MvPolynomial (Fin 3) ℤ) (k : ℤ) (i : ℕ) (m : ℤ)
    (hm : k-(i:ℤ)=m) (α : chowGroup C q k) :
    structureMapCast C q q' h m
      (capTo (LagrangianChowPolynomials.evaluate C q L P) i hm α) =
        capTo (LagrangianChowPolynomials.evaluate C q' L P) i hm
          (structureMapCast C q q' h k α) := by
  subst q'
  rfl

/-- The two original displayed grade-transport spellings agree. -/
theorem capTo_eq_chowGroupCast (A : GradedCapFamily (chowGroup C q))
    (k : ℤ) (i : ℕ) (m : ℤ) (hm : k-(i:ℤ)=m) (α : chowGroup C q k) :
    capTo A i hm α = chowGroupCast C q hm (A k i α) := by
  apply eq_of_heq
  exact (gradedDegreeCast_heq _ _).trans (chowGroupCast_heq C q hm _).symm

/-- The proved degree-zero display can be normalized before substituting
an actual native degree homomorphism on a geometric scheme. -/
theorem degree_twelve_cast {G : ℤ → Type u} [∀ k, AddCommGroup (G k)]
    (a : GradedCapFamily G) (α : G 12) (degree : G 0 → ℤ) :
    degree (capTo a 12 (by decide : (12:ℤ)-(12:ℕ)=0) α) = degree (a 12 12 α) := by
  rfl

/-- Equality of the original proper structure maps preserves their
actual native degree homomorphism, as well as the actual cap operators. -/
theorem degree_structureMapCast (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    [Subsingleton C.S] [IsProper q] [IsProper q'] (s : C.S)
    (α : chowGroup C q 0) :
    chowDegree C hδ q' s (structureMapCast C q q' h 0 α) = chowDegree C hδ q s α := by
  subst q'
  rfl

end M9Native.LagrangianChowStructureTransport
