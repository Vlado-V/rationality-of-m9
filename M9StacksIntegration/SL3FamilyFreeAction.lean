module

public import M9StacksIntegration.SL3ReducedFamilyNaturality
public import M9StacksIntegration.PrimitiveFreeMatrixPullback

@[expose] public section

/-! The actual varying reduced SL3 matrix acts on genuine native quotient
presentations, naturally over every test scheme over the complex numbers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix

namespace M9Native.SL3FamilyFreeAction

open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

abbrev base : Scheme := Spec (.of ℂ)

def scalarMap (T : Over base) : ℂ →+* Γ(T.left, ⊤) :=
  GraphGrassmannianLinearAction.scalarMap ℂ T.hom

def familyMatrix (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    Matrix (Fin 12) (Fin 12) Γ(T.left, ⊤) :=
  (SL3ReducedFamily.matrixGL Γ(T.left, ⊤) g).val

theorem familyMatrix_one (T : Over base) : familyMatrix T 1 = 1 := by
  rw [familyMatrix, SL3ReducedFamilyNaturality.matrixGL_block,
    SL3ReducedFamilyNaturality.blockMatrix, inv_one]
  change (Matrix.fromBlocks (SL3SymmetricCoordinates.matrix Γ(T.left, ⊤) 1) 0 0
    (SL3SymmetricCoordinates.matrix Γ(T.left, ⊤) 1).transpose).submatrix
      SL3ReducedFamilyNaturality.coordinateIndex.symm
        SL3ReducedFamilyNaturality.coordinateIndex.symm = 1
  rw [SL3SymmetricCoordinates.matrix_one, Matrix.transpose_one, Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem familyMatrix_natural {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    familyMatrix T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g) =
      (familyMatrix T g).map f.left.appTop.hom :=
  (SL3ReducedFamilyNaturality.matrixGL_map Γ(T.left, ⊤) f.left.appTop.hom g).symm

def freeIso (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    freeOn T.left 12 ≅ freeOn T.left 12 where
  hom := Stacks.FreeSheafMatrix.ofMatrix (familyMatrix T g)
  inv := Stacks.FreeSheafMatrix.ofMatrix ((SL3ReducedFamily.matrixGL Γ(T.left, ⊤) g)⁻¹).val
  hom_inv_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    exact Units.inv_mul _
  inv_hom_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    exact Units.mul_inv _

theorem freeIso_matrix (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    Stacks.FreeSheafMatrix.toMatrix (freeIso T g).hom = familyMatrix T g :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

theorem freeIso_one (T : Over base) : (freeIso T 1).hom = 𝟙 (freeOn T.left 12) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [freeIso_matrix, familyMatrix_one, Stacks.FreeSheafMatrix.toMatrix_id]

theorem freeIso_pullback {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    PrimitiveFreeMatrixPullback.pulledFreeEnd f.left 12 (freeIso T g).hom =
      (freeIso T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [PrimitiveFreeMatrixPullback.pulledFreeEnd_matrix, freeIso_matrix, freeIso_matrix,
    familyMatrix_natural]

theorem freeIso_pullback_inv {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    (pullbackFreeIso f.left 12).inv ≫ (Scheme.Modules.pullback f.left).map (freeIso T g).hom =
      (freeIso T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)).hom ≫
        (pullbackFreeIso f.left 12).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f.left 12).inv) (freeIso_pullback f g)
  simp only [PrimitiveFreeMatrixPullback.pulledFreeEnd, Category.assoc] at h
  rw [(pullbackFreeIso f.left 12).hom_inv_id, Category.comp_id] at h
  exact h

/-- Positive precomposition agrees with the frozen reduced native action. -/
def transform (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤))
    (q : QuotientPresentation T.left 4 12) : QuotientPresentation T.left 4 12 := by
  let : Epi q.map := q.map_epi
  exact { target := q.target
          map := (freeIso T g).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic (T : Over base)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤))
    {q q' : QuotientPresentation T.left 4 12} (h : q.Isomorphic q') :
    (transform T g q).Isomorphic (transform T g q') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change ((freeIso T g).hom ≫ q.map) ≫ e.hom = (freeIso T g).hom ≫ q'.map
  rw [Category.assoc, he]

theorem transform_one (T : Over base) (q : QuotientPresentation T.left 4 12) :
    (transform T 1 q).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change ((freeIso T 1).hom ≫ q.map) ≫ 𝟙 _ = q.map
  rw [freeIso_one, Category.id_comp, Category.comp_id]

theorem pullback_transform {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤))
    (q : QuotientPresentation T.left 4 12) :
    (pullbackPresentation f.left (transform T g q)).Isomorphic
      (transform T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)
        (pullbackPresentation f.left q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f.left 12).inv ≫
    (Scheme.Modules.pullback f.left).map ((freeIso T g).hom ≫ q.map)) ≫ 𝟙 _ =
      (freeIso T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)).hom ≫
        (pullbackFreeIso f.left 12).inv ≫ (Scheme.Modules.pullback f.left).map q.map
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc, freeIso_pullback_inv,
    Category.assoc]

def transformPoints (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) :
    Points T.left 4 12 → Points T.left 4 12 :=
  Quotient.lift (fun q => (⟦transform T g q⟧ : Points T.left 4 12)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic T g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one (T : Over base) (x : Points T.left 4 12) :
    transformPoints T 1 x = x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one T q))

theorem transformPoints_natural {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.SpecialLinearGroup (Fin 3) Γ(T.left, ⊤)) (x : Points T.left 4 12) :
    pullbackPointsMap f.left 4 12 (transformPoints T g x) =
      transformPoints T' (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)
        (pullbackPointsMap f.left 4 12 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform f g q))

theorem familyMatrix_constant (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    familyMatrix T (Matrix.SpecialLinearGroup.map (scalarMap T) g) =
      (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g)).val.map (scalarMap T) := by
  rw [familyMatrix, ← SL3ReducedFamilyNaturality.matrixGL_map, SL3ReducedFamily.matrixGL_eq_original]

theorem freeIso_constant (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    (freeIso T (Matrix.SpecialLinearGroup.map (scalarMap T) g)).hom =
      (GraphGrassmannianLinearAction.constantFreeIso ℂ T.hom
        (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g))).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [freeIso_matrix, familyMatrix_constant,
    GraphGrassmannianLinearAction.constantFreeIso_matrix]
  rfl

theorem transformPoints_constant (T : Over base) (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (x : Points T.left 4 12) :
    transformPoints T (Matrix.SpecialLinearGroup.map (scalarMap T) g) x =
      GraphGrassmannianLinearAction.transformPoints ℂ T.hom
        (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g)) x := by
  refine Quotient.inductionOn x fun q => ?_
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _, ?_⟩
  change ((freeIso T (Matrix.SpecialLinearGroup.map (scalarMap T) g)).hom ≫ q.map) ≫ 𝟙 _ =
    (GraphGrassmannianLinearAction.constantFreeIso ℂ T.hom
      (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g))).hom ≫ q.map
  rw [freeIso_constant, Category.comp_id]

/-- At a genuine field test scheme the varying free map is exactly the
original reduced field matrix, with the frozen positive-precomposition convention. -/
theorem freeIso_spec (L : Type) [Field L] [CharZero L]
    (b : Spec (.of L) ⟶ base) (g : Matrix.SpecialLinearGroup (Fin 3) L) :
    (freeIso (Over.mk b) (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g)).hom =
      (GraphGrassmannianLinearAction.constantFreeIso L (𝟙 (Spec (.of L)))
        (ReducedGraphAction.matrixRepresentation L (SemidirectProduct.inl g))).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [freeIso_matrix, GraphGrassmannianLinearAction.constantFreeIso_matrix]
  change (SL3ReducedFamily.matrixGL Γ(Spec (.of L), ⊤)
      (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g)).val =
    (ReducedGraphAction.matrixRepresentation L (SemidirectProduct.inl g)).val.map
      (GraphGrassmannianLinearAction.scalarMap L (𝟙 (Spec (.of L))))
  rw [← SL3ReducedFamilyNaturality.matrixGL_map, SL3ReducedFamily.matrixGL_eq_original]
  congr 1

theorem transformPoints_spec (L : Type) [Field L] [CharZero L]
    (b : Spec (.of L) ⟶ base) (g : Matrix.SpecialLinearGroup (Fin 3) L)
    (x : Points (Spec (.of L)) 4 12) :
    transformPoints (Over.mk b)
      (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g) x =
      GraphGrassmannianLinearAction.transformPoints L (𝟙 (Spec (.of L)))
        (ReducedGraphAction.matrixRepresentation L (SemidirectProduct.inl g)) x := by
  refine Quotient.inductionOn x fun q => ?_
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _, ?_⟩
  change ((freeIso (Over.mk b)
      (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g)).hom ≫ q.map) ≫ 𝟙 _ =
    (GraphGrassmannianLinearAction.constantFreeIso L (𝟙 (Spec (.of L)))
      (ReducedGraphAction.matrixRepresentation L (SemidirectProduct.inl g))).hom ≫ q.map
  rw [freeIso_spec, Category.comp_id]

end M9Native.SL3FamilyFreeAction
