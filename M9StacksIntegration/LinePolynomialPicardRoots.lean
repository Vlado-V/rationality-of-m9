module

public import M9StacksIntegration.ChowPicardLineFamily
public import M9StacksIntegration.LinePolynomialEvaluation

/-!
# Actual Picard identities bind polynomial roots to the same line caps

The actual Picard-to-line-family homomorphism is lifted to the proved
commutative subring using its genuine line representatives and the
injective inclusion. Thus true finite integer Picard identities give
equalities of evaluated roots. No numerical Picard equality, Chern
formula or compatibility with a separate realization is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v w

namespace M9Native.LinePolynomialPicardRoots

open Stacks.Chow ChowCapWords ChowPicardLineFamily GradedLineCapSubring
open CurvePowerChowFunctional LinePolynomialEvaluation

variable {X : Scheme.{u}}

def nativeLine (M : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M) : InvertibleLine X :=
  ⟨M, (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf X.ringCatSheaf.2 M).1 hM⟩

theorem actualClass_nativeLine (M : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M) :
    actualClass (nativeLine M hM) = @PoincareChern.lineClass X M hM := rfl

theorem actualClass_chosenLine (x : Stacks.Picard.ofScheme X) :
    actualClass (chosenLine x) = x := by
  change Stacks.SheafOfModules.picardClass X.presheaf X.ringCatSheaf.2
    (chosenLine x).1 _ = x
  exact Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

def picardRoot (x : Stacks.Picard.ofScheme X) : lineSubring C q :=
  lineRoot C q (representativeLine X x)

theorem inclusion_picardRoot (x : Stacks.Picard.ofScheme X) :
    inclusion C q (picardRoot C q x) = familyHom C q x := rfl

theorem picardRoot_class (L : InvertibleLine X) :
    picardRoot C q (actualClass L) = lineRoot C q L := by
  apply inclusion_injective C q
  exact familyHom_class C q L

def picardRootHom : Stacks.Picard.ofScheme X →+ lineSubring C q :=
  AddMonoidHom.mk' (picardRoot C q) fun x y => by
    apply inclusion_injective C q
    calc
      inclusion C q (picardRoot C q (x + y)) = familyHom C q (x + y) := rfl
      _ = familyHom C q x + familyHom C q y := (familyHom C q).map_add x y
      _ = inclusion C q (picardRoot C q x) + inclusion C q (picardRoot C q y) := rfl
      _ = inclusion C q (picardRoot C q x + picardRoot C q y) :=
        ((inclusion C q).toAddMonoidHom.map_add (picardRoot C q x) (picardRoot C q y)).symm

theorem inclusion_picardRootHom (x : Stacks.Picard.ofScheme X) :
    inclusion C q (picardRootHom C q x) = familyHom C q x := rfl

theorem picardRootHom_class (L : InvertibleLine X) :
    picardRootHom C q (actualClass L) = lineRoot C q L := picardRoot_class C q L

theorem picardRootHom_chosenLine (x : Stacks.Picard.ofScheme X) :
    picardRootHom C q x = lineRoot C q (chosenLine x) := by
  simpa only [actualClass_chosenLine] using picardRootHom_class C q (chosenLine x)

theorem evaluation_chosenLine_X {α : Type v} (x : α → Stacks.Picard.ofScheme X) (i : α) :
    evaluation C q (fun j => chosenLine (x j)) (MvPolynomial.X i) = picardRootHom C q (x i) := by
  change MvPolynomial.eval₂Hom (Int.castRingHom (lineSubring C q))
    (fun j => lineRoot C q (chosenLine (x j))) (MvPolynomial.X i) = _
  rw [MvPolynomial.eval₂Hom_X']
  exact (picardRootHom_chosenLine C q (x i)).symm

def linearPolynomial {α : Type v} {I : Type w} [Fintype I]
    (v : I → α) (weights : I → ℤ) : MvPolynomial α ℤ :=
  ∑ i, weights i • MvPolynomial.X (v i)

theorem evaluation_linearPolynomial {α : Type v} {I : Type w} [Fintype I]
    (x : α → Stacks.Picard.ofScheme X) (v : I → α) (weights : I → ℤ) :
    evaluation C q (fun j => chosenLine (x j)) (linearPolynomial v weights) =
      picardRootHom C q (∑ i, weights i • x (v i)) := by
  let E := (evaluation C q (fun j => chosenLine (x j))).toAddMonoidHom
  change E (∑ i, weights i • MvPolynomial.X (v i)) = _
  calc
    E (∑ i, weights i • MvPolynomial.X (v i)) =
        ∑ i, E (weights i • MvPolynomial.X (v i)) :=
      map_sum E (fun i => weights i • MvPolynomial.X (v i)) Finset.univ
    _ = ∑ i, weights i • picardRootHom C q (x (v i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (E.map_zsmul _ _).trans
        (congrArg (fun a => weights i • a) (evaluation_chosenLine_X C q x (v i)))
    _ = ∑ i, picardRootHom C q (weights i • x (v i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ((picardRootHom C q).map_zsmul _ _).symm
    _ = picardRootHom C q (∑ i, weights i • x (v i)) :=
      (map_sum (picardRootHom C q) (fun i => weights i • x (v i)) Finset.univ).symm

theorem evaluation_line_of_class_eq {α : Type v} {I : Type w} [Fintype I]
    (x : α → Stacks.Picard.ofScheme X) (v : I → α) (weights : I → ℤ)
    (L : InvertibleLine X) (h : actualClass L = ∑ i, weights i • x (v i)) :
    evaluation C q (fun j => chosenLine (x j)) (linearPolynomial v weights) = lineRoot C q L :=
  (evaluation_linearPolynomial C q x v weights).trans
    ((congrArg (picardRootHom C q) h).symm.trans (picardRootHom_class C q L))

theorem nativeEvaluation_line_of_class_eq {α : Type v} {I : Type w} [Fintype I]
    (x : α → Stacks.Picard.ofScheme X) (v : I → α) (weights : I → ℤ)
    (L : InvertibleLine X) (h : actualClass L = ∑ i, weights i • x (v i)) :
    nativeEvaluation C q (fun j => chosenLine (x j)) (linearPolynomial v weights) =
      lineFamily C q L :=
  congrArg (inclusion C q) (evaluation_line_of_class_eq C q x v weights L h)

end M9Native.LinePolynomialPicardRoots
