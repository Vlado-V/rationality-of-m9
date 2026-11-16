module

public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPullbackMap

/-!
# Transposing a genuine degree-zero projection square

For an additive adjunction the cochain adjoint is the degreewise
adjoint. A genuine degree-zero projection square therefore gives the
full cochain square to the original single complexes. The actual
cotangent cokernel construction supplies this square in the application.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v'

namespace M9Native.AdjointCochainProjection

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
  {K : CochainComplex C ℤ} {M : CochainComplex D ℤ}
  (α : K ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)

/-- The actual cochain adjoint is its actual component adjoint. -/
theorem transpose_f (i : ℤ) :
    (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv K M).symm α).f i =
      (adj.homEquiv _ _).symm (α.f i) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rfl

variable {A : C} {B : D}
  (p : K ⟶ (CochainComplex.singleFunctor C 0).obj A)
  (q : M ⟶ (CochainComplex.singleFunctor D 0).obj B)
  (k : A ⟶ R.obj B)

/-- The actual module projection square gives the actual cochain
adjoint square, with no cochain covariance premise. -/
theorem transpose_projection_square
    (hk : p.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ k =
      α.f 0 ≫ R.map (q.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom)) :
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv K M).symm α ≫ q =
      (L.mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
        (singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).hom.app A ≫
        (CochainComplex.singleFunctor D 0).map ((adj.homEquiv _ _).symm k) := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom).mp
  have h := adj.homEquiv_naturality_right_square
    (p.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 A).hom) k
    (α.f 0) (q.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom)
    ((Category.assoc _ _ _).trans hk)
  simpa only [HomologicalComplex.comp_f, transpose_f,
    Functor.mapHomologicalComplex_map_f, singleMapHomologicalComplex_hom_app_self,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

end M9Native.AdjointCochainProjection
