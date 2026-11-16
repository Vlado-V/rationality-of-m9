module

public import M9StacksIntegration.SymplecticIsotropicAnnihilation

/-!
# The actual original symplectic functional in free coordinates

The formula follows from the original signed symplectic dual embedding
and the genuine local free expansion. The statement concerns arbitrary
actual global free sections and has no normalizer or pairing premise.
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

namespace M9Native.SymplecticFunctionalCoordinates

open LagrangianMatrixChart LagrangianDualCoefficients
open SymplecticQuotientEvaluation SymplecticQuotientCoordinates SymplecticIsotropicAnnihilation

variable {X : Scheme.{u}}

theorem freeCoordinate_top (r : ℕ) (w : Γ(freeOn X r,⊤)) (j : Fin r) :
    freeCoordinate r ⊤ w j = freeSectionCoordinates X r w j := by
  rw [freeSectionCoordinates_apply, freeProj_eq_freeProjection]
  rfl

/-- Actual free-dual/symplectic identification, with both original coordinate orders retained. -/
def originalDualIso (X : Scheme.{u}) : dualSheaf (freeOn X 6) ≅ freeOn X 6 :=
  MukaiPointLine.coordinatesIso X 6 ≪≫ symplecticIso X

theorem dualEmbedding_identity :
    dualEmbedding (𝟙 (freeOn X 6)) = (originalDualIso X).hom := by
  change dualMap (𝟙 (freeOn X 6)) ≫
    (MukaiPointLine.coordinatesIso X 6).hom ≫ (symplecticIso X).hom = _
  rw [dualMap_id, Category.id_comp]
  rfl

/-- On every actual open the shared functional is omega(t restricted,w)
in the original free coordinates. -/
theorem omegaFunctional_open_pairing (t : Γ(freeOn X 6,⊤)) (U : X.Opens)
    (w : Γ(freeOn X 6,U)) :
    (omegaFunctional t).app U w =
      LagrangianCotangentFormula.symplecticPair
        (freeCoordinate 6 U ((freeOn X 6).presheaf.map (homOfLE le_top).op t))
        (freeCoordinate 6 U w) := by
  let α : Γ(dualSheaf (freeOn X 6),U) := (originalDualIso X).inv.app U w
  have hw : (dualEmbedding (𝟙 (freeOn X 6))).app U α = w := by
    rw [dualEmbedding_identity]
    exact congrArg (fun f : freeOn X 6 ⟶ freeOn X 6 => f.app U w)
      (originalDualIso X).inv_hom_id
  have he (i : Fin 3) : coefficientMap (𝟙 (freeOn X 6)) U α (i.castAdd 3) =
      freeCoordinate 6 U w (Fin.natAdd 3 i) := by
    have h := dualEmbedding_coordinate_last (𝟙 (freeOn X 6)) U α i
    rw [hw] at h
    exact h.symm
  have hf (i : Fin 3) : coefficientMap (𝟙 (freeOn X 6)) U α (Fin.natAdd 3 i) =
      -freeCoordinate 6 U w (i.castAdd 3) := by
    have h := dualEmbedding_coordinate_first (𝟙 (freeOn X 6)) U α i
    rw [hw] at h
    rw [h, neg_neg]
  change (AlgebraicGeometry.dualEvalHom (freeOn X 6) t).app U α = _
  rw [AlgebraicGeometry.dualEvalHom_app]
  have ht := evaluate_quotient_free (freeOn X 6) (𝟙 (freeOn X 6)) U α
    ((freeOn X 6).presheaf.map (homOfLE le_top).op t)
  change evalAt (freeOn X 6) α ((freeOn X 6).presheaf.map (homOfLE le_top).op t) = _ at ht
  rw [ht, Fin.sum_univ_add (a := 3) (b := 3)]
  simp only [he, hf]
  change (∑ i : Fin 3,
      freeCoordinate 6 U ((freeOn X 6).presheaf.map (homOfLE le_top).op t) (i.castAdd 3) *
      freeCoordinate 6 U w (Fin.natAdd 3 i)) +
    (∑ i : Fin 3,
      freeCoordinate 6 U ((freeOn X 6).presheaf.map (homOfLE le_top).op t) (Fin.natAdd 3 i) *
      -freeCoordinate 6 U w (i.castAdd 3)) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The shared actual functional is exactly omega(t,w) in the literal original free basis. -/
theorem omegaFunctional_top_pairing (t w : Γ(freeOn X 6,⊤)) :
    (omegaFunctional t).app ⊤ w =
      LagrangianCotangentFormula.symplecticPair
        (freeSectionCoordinates X 6 t) (freeSectionCoordinates X 6 w) := by
  have h := omegaFunctional_open_pairing t ⊤ w
  have hi : homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top) = 𝟙 ⊤ := Subsingleton.elim _ _
  have hc (z : Γ(freeOn X 6,⊤)) :
      freeCoordinate 6 ⊤ z = freeSectionCoordinates X 6 z :=
    funext (fun j => freeCoordinate_top 6 z j)
  simpa only [hi, op_id, (freeOn X 6).presheaf.map_id,
    ConcreteCategory.id_apply, hc] using h

end M9Native.SymplecticFunctionalCoordinates
