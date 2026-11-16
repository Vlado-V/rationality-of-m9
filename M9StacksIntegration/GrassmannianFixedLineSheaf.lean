module

public import M9StacksIntegration.GrassmannianSplitQuotient
public import M9StacksIntegration.GrassmannianFixedLineAlgebra
public import M9StacksIntegration.PrimitiveFreeMatrixPullback
public import M9StacksIntegration.LagrangianIncidenceFieldFrame

/-! The actual free-sheaf quotient by a fixed nonzero field vector,
with the original native line column and arbitrary test schemes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.GrassmannianFixedLineSheaf
open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix
open LagrangianMatrixChart LagrangianFreeMatrixPullback
open LagrangianIncidenceLineEvaluation LagrangianIncidenceFieldFrame
open PrimitiveFreeMatrixPullback SectionZeroIdealFactorization

section FreeMaps
variable {X Y : Scheme.{u}} {m n : ℕ}

theorem freeHomEquiv_top {Q : X.Modules} (q : freeOn X m ⟶ Q) (j : Fin m) :
    (Q.freeHomEquiv q (ULift.up.{u} j)).eval (op ⊤) =
      q.app ⊤ (freeBasisSection X m j) := by
  rw [SheafOfModules.freeHomEquiv_apply]
  change q.app ⊤ ((SheafOfModules.freeSection (R := X.ringCatSheaf)
    (ULift.up.{u} j)).eval (op ⊤)) = _
  congr 1

theorem freeHom_ext_top {Q : X.Modules} (q q' : freeOn X m ⟶ Q)
    (h : ∀ j, q.app ⊤ (freeBasisSection X m j) =
      q'.app ⊤ (freeBasisSection X m j)) : q = q' := by
  apply Q.freeHomEquiv.injective
  funext j
  rcases j with ⟨j⟩
  apply Stacks.PresheafOfModules.sections_ext_top
  change (Q.freeHomEquiv q (ULift.up.{u} j)).eval (op ⊤) =
    (Q.freeHomEquiv q' (ULift.up.{u} j)).eval (op ⊤)
  rw [freeHomEquiv_top, freeHomEquiv_top]
  exact h j

theorem coordinates_basis_map (a : freeOn X m ⟶ freeOn X n) (i : Fin n) (j : Fin m) :
    freeSectionCoordinates X n (a.app ⊤ (freeBasisSection X m j)) i = toMatrix a i j :=
  freeCoordinates_map_basis a i j

theorem column_eq_sum (a : freeOn X m ⟶ freeOn X n) (j : Fin m) :
    a.app ⊤ (freeBasisSection X m j) =
      ∑ i : Fin n, toMatrix a i j • freeBasisSection X n i := by
  have h := LagrangianFreeMatrixPullback.eq_sum_coordinates_basis X n
    (a.app ⊤ (freeBasisSection X m j))
  simpa only [coordinates_basis_map] using h

theorem map_section_coordinates (a : freeOn X m ⟶ freeOn X n)
    (z : Γ(freeOn X m, ⊤)) :
    freeSectionCoordinates X n (a.app ⊤ z) =
      (toMatrix a).mulVec (freeSectionCoordinates X m z) := by
  funext i
  calc
    _ = freeSectionCoordinates X n
        (a.app ⊤ (∑ j : Fin m, freeSectionCoordinates X m z j • freeBasisSection X m j)) i :=
      congrArg (fun w => freeSectionCoordinates X n (a.app ⊤ w) i)
        (LagrangianFreeMatrixPullback.eq_sum_coordinates_basis X m z)
    _ = ∑ j : Fin m, freeSectionCoordinates X m z j * toMatrix a i j := by
      simp only [map_sum, Scheme.Modules.Hom.app_smul, map_smul,
        Finset.sum_apply, Pi.smul_apply, coordinates_basis_map, smul_eq_mul]
    _ = _ := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

def pulledMap (f : Y ⟶ X) (a : freeOn X m ⟶ freeOn X n) :
    freeOn Y m ⟶ freeOn Y n :=
  (pullbackFreeIso f m).inv ≫ (Scheme.Modules.pullback f).map a ≫
    (pullbackFreeIso f n).hom

theorem pulledMap_column (f : Y ⟶ X) (a : freeOn X m ⟶ freeOn X n) (j : Fin m) :
    (pulledMap f a).app ⊤ (freeBasisSection Y m j) =
      ∑ i : Fin n, f.appTop (toMatrix a i j) • freeBasisSection Y n i := by
  change (pullbackFreeIso f n).hom.app ⊤
    (((Scheme.Modules.pullback f).map a).app ⊤
      ((pullbackFreeIso f m).inv.app ⊤ (freeBasisSection Y m j))) = _
  rw [PrimitiveFreeMatrixPullback.inverse_freeBasisSection_pullback,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections, column_eq_sum]
  simp only [map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, PrimitiveFreeMatrixPullback.freeBasisSection_pullback]

theorem pulledMap_matrix (f : Y ⟶ X) (a : freeOn X m ⟶ freeOn X n) :
    toMatrix (pulledMap f a) = (toMatrix a).map f.appTop.hom := by
  ext i j
  rw [← coordinates_basis_map (pulledMap f a) i j]
  rw [pulledMap_column]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis]
  simp
end FreeMaps

variable (K : Type u) [Field K]

def scalarMap {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) : K →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom

theorem scalarMap_comp {S T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (f : S ⟶ T) :
    scalarMap K (f ≫ p) = f.appTop.hom.comp (scalarMap K p) := by
  ext c
  rfl

def constantMap {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) {m n : ℕ}
    (M : Matrix (Fin n) (Fin m) K) : freeOn T m ⟶ freeOn T n :=
  ofMatrix (M.map (scalarMap K p))

theorem constantMap_matrix {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) {m n : ℕ}
    (M : Matrix (Fin n) (Fin m) K) :
    toMatrix (constantMap K p M) = M.map (scalarMap K p) := toMatrix_ofMatrix _

theorem constantMap_pullback {S T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (f : S ⟶ T)
    {m n : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    pulledMap f (constantMap K p M) = constantMap K (f ≫ p) M := by
  apply toMatrix_injective
  rw [pulledMap_matrix, constantMap_matrix, constantMap_matrix]
  ext i j
  rfl

theorem constantMap_pullback_inv {S T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (f : S ⟶ T)
    {m n : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    (pullbackFreeIso f m).inv ≫ (Scheme.Modules.pullback f).map (constantMap K p M) =
      constantMap K (f ≫ p) M ≫ (pullbackFreeIso f n).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f n).inv)
    (constantMap_pullback K p f M)
  simp only [pulledMap, Category.assoc] at h
  rw [(pullbackFreeIso f n).hom_inv_id, Category.comp_id] at h
  exact h

variable {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (v : Fin 14 → K) (hv : v ≠ 0)

def splitMap : GrassmannianSplitQuotient.SplitMap T where
  quotient := constantMap K p (GrassmannianFixedLineAlgebra.quotientMatrix K v hv)
  splitting := constantMap K p (GrassmannianFixedLineAlgebra.splittingMatrix K v hv)
  split_identity := by
    apply toMatrix_injective
    rw [toMatrix_comp, constantMap_matrix, constantMap_matrix, toMatrix_id]
    exact GrassmannianFixedLineAlgebra.mapped_quotient_splitting K (scalarMap K p) v hv

theorem splitMap_quotient_matrix :
    toMatrix (splitMap K p v hv).quotient =
      (GrassmannianFixedLineAlgebra.quotientMatrix K v hv).map (scalarMap K p) :=
  constantMap_matrix K p _

theorem splitMap_splitting_matrix :
    toMatrix (splitMap K p v hv).splitting =
      (GrassmannianFixedLineAlgebra.splittingMatrix K v hv).map (scalarMap K p) :=
  constantMap_matrix K p _

/-- The literal scalar-extended vector used by the original incidence equation. -/
abbrev vectorSection : Γ(freeOn T 14, ⊤) :=
  coefficientVector T (fun i => scalarMap K p (v i))

/-- The original native unit-to-free column, with no chosen quotient frame. -/
abbrev lineColumn : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ freeOn T 14 :=
  coefficientColumn T (fun i => scalarMap K p (v i))

theorem lineColumn_top_one : Scheme.Modules.Hom.app (X := T) (lineColumn K p v) ⊤ (1 : Γ(T, ⊤)) = vectorSection K p v :=
  coefficientColumn_top_one _ _

theorem vectorSection_coordinates :
    freeSectionCoordinates T 14 (vectorSection K p v) = fun i => scalarMap K p (v i) := by
  funext i
  simp only [vectorSection, coefficientVector, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, freeCoordinates_basis, smul_eq_mul]
  simp

theorem quotient_vectorSection :
    Scheme.Modules.Hom.app (X := T) (splitMap K p v hv).quotient ⊤ (vectorSection K p v) = 0 := by
  apply (freeSectionCoordinates T 13).injective
  rw [map_section_coordinates, map_zero, vectorSection_coordinates]
  rw [splitMap_quotient_matrix]
  exact GrassmannianFixedLineAlgebra.mapped_quotient_vector K (scalarMap K p) v hv

theorem projector_vectorSection :
    Scheme.Modules.Hom.app (X := T) (GrassmannianSplitQuotient.projector (splitMap K p v hv)) ⊤
      (vectorSection K p v) = vectorSection K p v := by
  change vectorSection K p v - Scheme.Modules.Hom.app (X := T) (splitMap K p v hv).splitting ⊤
    (Scheme.Modules.Hom.app (X := T) (splitMap K p v hv).quotient ⊤ (vectorSection K p v)) = _
  rw [quotient_vectorSection, map_zero, sub_zero]

/-- The discarded actual free-sheaf projector has every column in the
prescribed line, with the exact scalar coefficient. -/
theorem projector_column (j : Fin 14) :
    Scheme.Modules.Hom.app (X := T) (GrassmannianSplitQuotient.projector (splitMap K p v hv)) ⊤
      (freeBasisSection T 14 j) =
        scalarMap K p (GrassmannianFixedLineAlgebra.coefficients K v hv j) •
          vectorSection K p v := by
  apply (freeSectionCoordinates T 14).injective
  funext i
  change freeSectionCoordinates T 14
    (freeBasisSection T 14 j -
      Scheme.Modules.Hom.app (X := T) ((splitMap K p v hv).quotient ≫ (splitMap K p v hv).splitting) ⊤
        (freeBasisSection T 14 j)) i = _
  rw [map_sub, Pi.sub_apply, freeCoordinates_basis, coordinates_basis_map,
    toMatrix_comp, splitMap_splitting_matrix, splitMap_quotient_matrix,
    GrassmannianFixedLineAlgebra.mapped_splitting_quotient]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, map_smul,
    Pi.smul_apply, vectorSection_coordinates, smul_eq_mul]
  ring

/-- Projector annihilation is exactly annihilation of the actual fixed
column, even when the quotient target has no global frame. -/
theorem projector_comp_eq_zero_iff_column {Q : T.Modules} (q : freeOn T 14 ⟶ Q) :
    GrassmannianSplitQuotient.projector (splitMap K p v hv) ≫ q = 0 ↔
      lineColumn K p v ≫ q = 0 := by
  rw [coefficientColumn_comp_eq_zero_iff]
  constructor
  · intro h
    have hh := congrArg (fun a : freeOn T 14 ⟶ Q => a.app ⊤ (vectorSection K p v)) h
    change q.app ⊤
      (Scheme.Modules.Hom.app (X := T) (GrassmannianSplitQuotient.projector (splitMap K p v hv)) ⊤
        (vectorSection K p v)) = 0 at hh
    rwa [projector_vectorSection] at hh
  · intro h
    apply freeHom_ext_top
    intro j
    change q.app ⊤
      (Scheme.Modules.Hom.app (X := T) (GrassmannianSplitQuotient.projector (splitMap K p v hv)) ⊤
        (freeBasisSection T 14 j)) = 0
    rw [projector_column, Scheme.Modules.Hom.app_smul, h, smul_zero]

def KillsColumn (q : QuotientPresentation T 9 14) : Prop := lineColumn K p v ≫ q.map = 0

theorem killsColumn_iff_of_isomorphic {q q' : QuotientPresentation T 9 14}
    (h : q.Isomorphic q') : KillsColumn K p v q ↔ KillsColumn K p v q' := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro hq
    change lineColumn K p v ≫ q'.map = 0
    rw [← he, ← Category.assoc, hq, zero_comp]
  · intro hq
    apply (cancel_mono e.hom).1
    change (lineColumn K p v ≫ q.map) ≫ e.hom =
      (0 : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ q.target) ≫ e.hom
    rw [Category.assoc, he, hq, zero_comp]

/-- The original fixed-line condition on the native quotient classes. -/
def KillsColumnPoint : Points T 9 14 → Prop :=
  Quotient.lift (KillsColumn K p v) (by
    intro q q' h
    apply propext
    induction h with
    | rel _ _ h => exact killsColumn_iff_of_isomorphic K p v h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h h' => exact h.trans h')

theorem killsPoint_iff (x : Points T 9 14) :
    GrassmannianSplitQuotient.KillsPoint (splitMap K p v hv) x ↔ KillsColumnPoint K p v x := by
  refine Quotient.inductionOn x fun q => ?_
  exact projector_comp_eq_zero_iff_column K p v hv q.map

/-- The genuine fixed-line Grassmannian functor, on every test scheme. -/
def pointsEquiv : Points T 8 13 ≃ {x : Points T 9 14 // KillsColumnPoint K p v x} :=
  (GrassmannianSplitQuotient.pointsEquiv (splitMap K p v hv)).trans
    { toFun := fun x => ⟨x.1, (killsPoint_iff K p v hv x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (killsPoint_iff K p v hv x.1).mpr x.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

abbrev liftPoints : Points T 8 13 → Points T 9 14 :=
  GrassmannianSplitQuotient.liftPoints (splitMap K p v hv)

theorem liftPoints_injective : Function.Injective (liftPoints K p v hv) :=
  GrassmannianSplitQuotient.liftPoints_injective (splitMap K p v hv)

theorem liftPoints_kills (x : Points T 8 13) : KillsColumnPoint K p v (liftPoints K p v hv x) :=
  (pointsEquiv K p v hv x).2

theorem exists_liftPoints_iff (x : Points T 9 14) :
    (∃ y : Points T 8 13, liftPoints K p v hv y = x) ↔ KillsColumnPoint K p v x := by
  rw [GrassmannianSplitQuotient.exists_liftPoints_iff]
  exact killsPoint_iff K p v hv x

theorem liftPoints_natural {S : Scheme.{u}} (f : S ⟶ T) (x : Points T 8 13) :
    pullbackPointsMap f 9 14 (liftPoints K p v hv x) =
      liftPoints K (f ≫ p) v hv (pullbackPointsMap f 8 13 x) :=
  GrassmannianSplitQuotient.liftPoints_natural (splitMap K p v hv) f
    (splitMap K (f ≫ p) v hv)
    (constantMap_pullback_inv K p f (GrassmannianFixedLineAlgebra.quotientMatrix K v hv)) x

end M9Native.GrassmannianFixedLineSheaf
