module

public import M9StacksIntegration.SymplecticQuotientCoordinates

/-!
# Genuine isotropy kills the original symplectic dual embedding

Actual local free expansions and frozen dual coefficient isotropy give
zero against every local functional. Finite locally free reflexivity
then gives the original whole-sheaf zero composition. No dual-kernel
identification or exactness is an input.
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

namespace M9Native.SymplecticIsotropicAnnihilation

open LagrangianMatrixChart LagrangianDualCoefficients LagrangianGrassmannian
open SymplecticQuotientEvaluation SymplecticQuotientCoordinates

variable {X : Scheme.{u}}

/-- The actual original finite-free basis inclusion, with its scheme module type. -/
abbrev basisInclusion (r : ℕ) (j : Fin r) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ freeOn X r :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j)

theorem freeBasis_restrict (r : ℕ) (U : X.Opens) (j : Fin r) :
    (Scheme.Modules.Hom.app (basisInclusion (X := X) r j) U) (1 : Γ(X,U)) =
      (freeOn X r).presheaf.map (homOfLE le_top).op (freeBasisSection X r j) := by
  have h := ConcreteCategory.congr_hom
    ((basisInclusion (X := X) r j).val.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X,⊤))
  change (Scheme.Modules.Hom.app (basisInclusion (X := X) r j) U)
    (X.presheaf.map (homOfLE le_top).op (1 : Γ(X,⊤))) =
    (freeOn X r).presheaf.map (homOfLE le_top).op
      (Scheme.Modules.Hom.app (basisInclusion (X := X) r j) ⊤ (1 : Γ(X,⊤))) at h
  have hb : Scheme.Modules.Hom.app (basisInclusion (X := X) r j) ⊤ (1 : Γ(X,⊤)) =
      freeBasisSection X r j := rfl
  simpa only [map_one, hb] using h

/-- The actual finite free decomposition on every open follows from
the actual sum of the coordinate projections and inclusions. -/
theorem freeSection_open_expansion (r : ℕ) (U : X.Opens) (w : Γ(freeOn X r,U)) :
    w = ∑ j : Fin r, freeCoordinate r U w j •
      (freeOn X r).presheaf.map (homOfLE le_top).op (freeBasisSection X r j) := by
  classical
  let ev : (freeOn X r ⟶ freeOn X r) →+ Γ(freeOn X r,U) :=
    { toFun := fun a => a.app U w
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev
    (SheafOfModules.sum_freeProjection_comp_ιFree
      (R := X.ringCatSheaf) (I := ULift.{u} (Fin r)))
  rw [map_sum] at h
  have hs : (∑ j : ULift.{u} (Fin r),
      (Scheme.Modules.Hom.app (basisInclusion (X := X) r j.down) U)
        (freeCoordinate r U w j.down)) =
      ∑ j : Fin r, freeCoordinate r U w j •
        (freeOn X r).presheaf.map (homOfLE le_top).op (freeBasisSection X r j) := by
    refine Fintype.sum_equiv Equiv.ulift _ _ ?_
    rintro ⟨j⟩
    have hm := Scheme.Modules.Hom.app_smul (basisInclusion (X := X) r j)
      (freeCoordinate r U w j) (1 : Γ(X,U))
    have hm' : (Scheme.Modules.Hom.app (basisInclusion (X := X) r j) U)
        (freeCoordinate r U w j) = freeCoordinate r U w j •
          (Scheme.Modules.Hom.app (basisInclusion (X := X) r j) U) (1 : Γ(X,U)) := by
      simpa only [smul_eq_mul, mul_one] using hm
    exact hm'.trans (congrArg (fun z => freeCoordinate r U w j • z) (freeBasis_restrict r U j))
  exact h.symm.trans hs

theorem evaluate_quotient_free (Q : X.Modules) (q : freeOn X 6 ⟶ Q) (U : X.Opens)
    (β : Γ(dualSheaf Q,U)) (w : Γ(freeOn X 6,U)) :
    evalAt Q β (q.app U w) = ∑ j : Fin 6, freeCoordinate 6 U w j * coefficientMap q U β j := by
  let L : Γ(freeOn X 6,U) →ₗ[Γ(X,U)] Γ(X,U) :=
    { toFun := fun z => evalAt Q β (q.app U z)
      map_add' := fun z z' => by rw [map_add, evalAt_add_right]
      map_smul' := fun a z => by
        simp only [Scheme.Modules.Hom.app_smul, evalAt_smul_right, RingHom.id_apply] }
  have hb (j : Fin 6) : L ((freeOn X 6).presheaf.map (homOfLE le_top).op
      (freeBasisSection X 6 j)) = coefficientMap q U β j := by
    have hn := ConcreteCategory.congr_hom
      (q.val.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (freeBasisSection X 6 j)
    exact congrArg (evalAt Q β) hn
  have h := congrArg L (freeSection_open_expansion 6 U w)
  simpa only [map_sum, map_smul, smul_eq_mul, hb, L, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- Original local coefficient isotropy is the actual contraction of
the original quotient with its actual symplectic dual embedding. -/
theorem dualEmbedding_pairing (Q : X.Modules) (q : freeOn X 6 ⟶ Q) (U : X.Opens)
    (α β : Γ(dualSheaf Q,U)) :
    evalAt Q β (q.app U ((dualEmbedding q).app U α)) =
      LagrangianCotangentFormula.symplecticPair (coefficientMap q U α) (coefficientMap q U β) := by
  rw [evaluate_quotient_free, Fin.sum_univ_add (a := 3) (b := 3)]
  simp only [dualEmbedding_coordinate_first, dualEmbedding_coordinate_last]
  change (∑ i : Fin 3, -(coefficientMap q U α (Fin.natAdd 3 i)) *
      coefficientMap q U β (i.castAdd 3)) +
    (∑ i : Fin 3, coefficientMap q U α (i.castAdd 3) *
      coefficientMap q U β (Fin.natAdd 3 i)) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dualEmbedding_pairing_zero (Q : X.Modules) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    evalAt Q β (q.app U ((dualEmbedding q).app U α)) = 0 := by
  rw [dualEmbedding_pairing]
  exact LagrangianLocalPairing.coefficientMap_isotropic q hq U α β

/-- Reflexivity turns the actual local zero pairings into the actual
global zero composite. The kernel identification is not assumed. -/
theorem dualEmbedding_comp_quotient (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q]
    (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q) :
    dualEmbedding q ≫ q = 0 := by
  let := isIso_toDoubleDual_of_isFiniteLocallyFree Q
  apply (cancel_mono (toDoubleDual Q)).1
  rw [zero_comp]
  apply Scheme.Modules.hom_ext
  intro U
  ext α
  apply dualPairing_ext (F := dualSheaf Q)
  intro W β
  change dualPairing (dualSheaf Q)
    ((toDoubleDual Q).app U ((dualEmbedding q ≫ q).app U α)) W β = _
  rw [toDoubleDual_dualPairing]
  change evalAt Q β (Q.presheaf.map W.hom.op ((dualEmbedding q ≫ q).app U α)) = 0
  have hn := ConcreteCategory.congr_hom ((dualEmbedding q ≫ q).val.naturality W.hom.op) α
  change (dualEmbedding q ≫ q).app W.left
    ((dualSheaf Q).presheaf.map W.hom.op α) =
    Q.presheaf.map W.hom.op ((dualEmbedding q ≫ q).app U α) at hn
  rw [← hn]
  exact dualEmbedding_pairing_zero Q q hq W.left ((dualSheaf Q).presheaf.map W.hom.op α) β

end M9Native.SymplecticIsotropicAnnihilation
