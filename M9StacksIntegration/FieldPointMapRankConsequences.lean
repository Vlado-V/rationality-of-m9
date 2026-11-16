module

public import M9StacksIntegration.FieldPointMapRank
public import M9StacksIntegration.FreeSheafMatrixFiberRank

/-! Genuine fibre-rank invariance under actual field pullback and
actual sheaf isomorphisms. A framed field-point matrix therefore computes
the original residue rank, without a supplied fibre identification. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.ModuleSkyscraper

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.ModuleSkyscraper.modulesStalkFunctor Stacks.ModuleSkyscraper.presheafStalkFunctor

universe u

namespace M9Native.FieldPointMapRankConsequences

open SpecFieldStalkSections FieldPointMapRank FieldBaseChangeRank
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

theorem finrank_range_sections_eq_mapRankAt {A B : (Spec (.of K)).Modules} (a : A ⟶ B) :
    finrank K (LinearMap.range (moduleSpecΓFunctor.map a).hom) =
      MukaiSemiIrreducible.mapRankAt a (point K) := by
  let : Field (localRing K) := FieldPointMapRank.localRingField K
  let : Algebra (localRing K) ((Spec (.of K)).residueField (point K)) :=
    ((Spec (.of K)).residue (point K)).hom.toAlgebra
  rw [FieldPointMapRank.finrank_range_sections_eq_stalk K a]
  exact (FieldBaseChangeRank.finrank_range_baseChange (localRing K)
    ((Spec (.of K)).residueField (point K))
      ((modulesStalkFunctor (Spec (.of K)) (point K)).map a).hom).symm

variable {X : Scheme.{u}}

theorem mapRankAt_pullback {A B : X.Modules} (a : A ⟶ B) (p : Spec (.of K) ⟶ X) :
    MukaiSemiIrreducible.mapRankAt ((Scheme.Modules.pullback p).map a) (point K) =
      MukaiSemiIrreducible.mapRankAt a (p (point K)) :=
  (finrank_range_sections_eq_mapRankAt K ((Scheme.Modules.pullback p).map a)).symm.trans
    (FieldPointMapRank.finrank_range_pullbackSections_eq_mapRankAt K a p)

omit K in
theorem mapRankAt_iso_conjugate {A A' B B' : X.Modules} (a : A ⟶ B)
    (e : A' ≅ A) (e' : B ≅ B') (x : X) :
    MukaiSemiIrreducible.mapRankAt (e.hom ≫ a ≫ e'.hom) x =
      MukaiSemiIrreducible.mapRankAt a x := by
  let T := modulesStalkFunctor X x ⋙ ModuleCat.extendScalars (X.residue x).hom
  have hlin : (T.map (e.hom ≫ a ≫ e'.hom)).hom =
      (T.mapIso e').toLinearEquiv.toLinearMap.comp
        ((T.map a).hom.comp (T.mapIso e).toLinearEquiv.toLinearMap) := by
    simp only [CategoryTheory.Functor.map_comp]
    rfl
  change finrank (X.residueField x) (LinearMap.range (T.map (e.hom ≫ a ≫ e'.hom)).hom) =
    finrank (X.residueField x) (LinearMap.range (T.map a).hom)
  rw [hlin]
  exact FieldBaseChangeRank.finrank_range_equiv (X.residueField x) _
    (T.mapIso e).toLinearEquiv (T.mapIso e').toLinearEquiv

theorem mapRankAt_of_point_frame {m n : ℕ} {B : X.Modules}
    (a : freeOn X m ⟶ B) (p : Spec (.of K) ⟶ X)
    (e : (Scheme.Modules.pullback p).obj B ≅ freeOn (Spec (.of K)) n)
    (M : Matrix (Fin n) (Fin m) K)
    (h : (pullbackFreeIso p m).inv ≫ (Scheme.Modules.pullback p).map a ≫ e.hom =
      Stacks.FreeSheafMatrix.ofMatrix
        (M.map (Scheme.ΓSpecIso (.of K)).inv.hom)) :
    MukaiSemiIrreducible.mapRankAt a (p (point K)) = M.rank := by
  rw [← mapRankAt_pullback K a p]
  have he := mapRankAt_iso_conjugate ((Scheme.Modules.pullback p).map a)
    (pullbackFreeIso p m).symm e (point K)
  simp only [Iso.symm_hom] at he
  rw [h] at he
  exact he.symm.trans (FreeSheafMatrixFiberRank.mapRankAt_ofMatrix_map K
    (Scheme.ΓSpecIso (.of K)).inv.hom M (point K))

end M9Native.FieldPointMapRankConsequences
