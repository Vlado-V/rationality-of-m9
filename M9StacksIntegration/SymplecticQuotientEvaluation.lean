module

public import M9StacksIntegration.MukaiPointLine
public import M9StacksIntegration.LagrangianPluckerDuality
public import M9StacksIntegration.SectionConormalEvaluation

/-!
# The genuine free-six symplectic dual embedding and its evaluation sign

The native free-dual coordinates and the original reindexed Mathlib J
give actual sheaf isomorphisms. The quotient dual embedding and the
symplectic functional use these same isomorphisms in opposite directions.
Actual dual-evaluation naturality then proves the positive evaluation
identity without a kernel, exactness, isotropy, or sign premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian

namespace M9Native.SymplecticQuotientEvaluation

open LagrangianMatrixChart

/-- The original J in the original first-three/last-three basis. Its
inverse is the actual negative J; both equations are checked as maps. -/
def symplecticIso (X : Scheme.{u}) : freeOn X 6 ≅ freeOn X 6 where
  hom := Stacks.FreeSheafMatrix.ofMatrix (LagrangianTransitivity.standardForm Γ(X,⊤))
  inv := Stacks.FreeSheafMatrix.ofMatrix (-LagrangianTransitivity.standardForm Γ(X,⊤))
  hom_inv_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id,
      Matrix.neg_mul, LagrangianPluckerDuality.standardForm_squared, neg_neg]
  inv_hom_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id,
      Matrix.mul_neg, LagrangianPluckerDuality.standardForm_squared, neg_neg]

variable {X : Scheme.{u}}

/-- The actual quotient dual, placed in the original free six-space
by the original signed symplectic identification. -/
def dualEmbedding {Q : X.Modules} (q : freeOn X 6 ⟶ Q) :
    dualSheaf Q ⟶ freeOn X 6 :=
  MukaiPointLine.pointLineMap q ≫ (symplecticIso X).hom

/-- The actual functional associated with the original global free
section, in the orientation omega(section,-). -/
def omegaFunctional (t : Γ(freeOn X 6,⊤)) :
    freeOn X 6 ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (symplecticIso X).inv ≫ (MukaiPointLine.coordinatesIso X 6).inv ≫
    AlgebraicGeometry.dualEvalHom (freeOn X 6) t

/-- Native dual evaluation is natural for an actual sheaf map and
the actual original global section, on every open. -/
theorem dualEvalHom_naturality {F G : X.Modules} (q : F ⟶ G) (t : Γ(F,⊤)) :
    dualMap q ≫ AlgebraicGeometry.dualEvalHom F t =
      AlgebraicGeometry.dualEvalHom G (q.app ⊤ t) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext α
  change evalAt F ((dualMap q).app U α) (F.presheaf.map (homOfLE le_top).op t) =
    evalAt G α (G.presheaf.map (homOfLE le_top).op (q.app ⊤ t))
  have hn := ConcreteCategory.congr_hom
    (q.val.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) t
  exact (dualPairing_dualMap q α (Over.mk (𝟙 U)) _).trans
    (congrArg (evalAt G α) hn)

/-- The frozen point-line pairing and the literal native zero-scheme
evaluation are the same whole-sheaf morphism. -/
theorem sectionPairing_eq_dualEvalHom (Q : X.Modules) (t : Γ(Q,⊤)) :
    MukaiPointLine.sectionPairing Q t = AlgebraicGeometry.dualEvalHom Q t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext α
  change dualPairing (dualSheaf Q) ((toDoubleDual Q).app ⊤ t)
    (Over.mk (homOfLE (show U ≤ ⊤ from le_top))) α =
      evalAt Q α (Q.presheaf.map (homOfLE le_top).op t)
  exact toDoubleDual_dualPairing Q t
    (Over.mk (homOfLE (show U ≤ ⊤ from le_top))) α

/-- The chosen original symplectic orientation gives the PLUS native
dual evaluation identity, before any isotropy or kernel argument. -/
theorem dualEmbedding_comp_omegaFunctional {Q : X.Modules}
    (q : freeOn X 6 ⟶ Q) (t : Γ(freeOn X 6,⊤)) :
    dualEmbedding q ≫ omegaFunctional t =
      AlgebraicGeometry.dualEvalHom Q (q.app ⊤ t) := by
  change (dualMap q ≫ (MukaiPointLine.coordinatesIso X 6).hom ≫
    (symplecticIso X).hom) ≫ ((symplecticIso X).inv ≫
      (MukaiPointLine.coordinatesIso X 6).inv ≫ AlgebraicGeometry.dualEvalHom _ t) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact dualEvalHom_naturality q t

/-- Whole-sheaf quotient-dual coordinates in the original basis,
retaining literal evaluation rather than a chosen local scalar. -/
theorem pointLineMap_projection {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (j : Fin 6) :
    MukaiPointLine.pointLineMap q ≫ SheafOfModules.freeProjection (ULift.up.{u} j) =
      AlgebraicGeometry.dualEvalHom Q (q.app ⊤ (freeBasisSection X 6 j)) := by
  change dualMap q ≫ MukaiPointLine.coordinatesMap X 6 ≫
    SheafOfModules.freeProjection (ULift.up.{u} j) = _
  rw [MukaiPointLine.coordinatesMap_projection, sectionPairing_eq_dualEvalHom]
  exact dualEvalHom_naturality q _

end M9Native.SymplecticQuotientEvaluation
