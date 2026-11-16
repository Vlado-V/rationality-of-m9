module

import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

public import M9StacksIntegration.PrimitiveFreeMatrixPullback
public import M9StacksIntegration.PrimitiveRingFieldBridge
public import M9StacksIntegration.Sp6GroupScheme
public import M9StacksIntegration.LagrangianSymplecticAction

/-! The genuine primitive free-fourteen family and its action on actual quotient presentations. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveFamilyFreeAction

open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

abbrev base : Scheme := Spec (.of ℂ)

def scalarMap (T : Over base) : ℂ →+* Γ(T.left,⊤) :=
  LagrangianSymplecticAction.scalarMap ℂ T.hom

theorem scalarMap_natural {T T' : Over base} (f : T' ⟶ T) :
    scalarMap T' = f.left.appTop.hom.comp (scalarMap T) := by
  change LagrangianSymplecticAction.scalarMap ℂ T'.hom = _
  rw [← f.w]
  exact LagrangianSymplecticAction.scalarMap_comp ℂ T.hom f.left

def familyMatrix (T : Over base) (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    Matrix (Fin 14) (Fin 14) Γ(T.left,⊤) :=
  PrimitiveRingCoordinates.primitiveMatrix Γ(T.left,⊤) (scalarMap T) g

theorem familyMatrix_one (T : Over base) : familyMatrix T 1 = 1 :=
  PrimitiveRingCoordinates.primitiveMatrix_one _ _

theorem familyMatrix_mul (T : Over base) (g h : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    familyMatrix T (g*h) = familyMatrix T g * familyMatrix T h :=
  PrimitiveRingCoordinates.primitiveMatrix_mul _ _ g h

theorem familyMatrix_natural {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    familyMatrix T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g) =
      (familyMatrix T g).map f.left.appTop.hom := by
  rw [familyMatrix, scalarMap_natural]
  exact PrimitiveRingCoordinates.primitiveMatrix_map _ _ _ g

theorem familyMatrix_fromOriginal (T : Over base) (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    familyMatrix T (Sp6GroupScheme.mapMatrix (scalarMap T) (PrimitiveRingFieldBridge.fromOriginal h)) =
      (LinearMap.toMatrix' (PrimitiveRingFieldBridge.originalCoordinateLinear h).toLinearMap).map
        (scalarMap T) := by
  have ht := PrimitiveRingCoordinates.primitiveMatrix_map ℂ (RingHom.id ℂ) (scalarMap T)
    (PrimitiveRingFieldBridge.fromOriginal h)
  rw [RingHom.comp_id, PrimitiveRingFieldBridge.primitiveMatrix_fromOriginal_eq_toMatrix] at ht
  exact ht

def constantPointOn (T : Over base) (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    T ⟶ Sp6GroupScheme.obj base :=
  (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 base)) ≫
    Sp6GroupScheme.constantPoint ℂ (PrimitiveRingFieldBridge.fromOriginal h)

theorem pointsMulEquiv_constantPointOn (T : Over base) (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    Sp6GroupScheme.pointsMulEquiv base T (constantPointOn T h) =
      Sp6GroupScheme.mapMatrix (scalarMap T) (PrimitiveRingFieldBridge.fromOriginal h) := by
  rw [constantPointOn, Sp6GroupScheme.pointsMulEquiv_natural,
    Sp6GroupScheme.pointsMulEquiv_constantPoint]
  apply Subtype.ext
  ext i j
  rfl

/-- Constants in the actual group scheme act by the literal scalar extension of the original
primitive representation in the original radical coordinates. -/
theorem familyMatrix_constantPointOn (T : Over base) (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    familyMatrix T (Sp6GroupScheme.pointsMulEquiv base T (constantPointOn T h)) =
      (LinearMap.toMatrix' (PrimitiveRingFieldBridge.originalCoordinateLinear h).toLinearMap).map
        (scalarMap T) := by
  rw [pointsMulEquiv_constantPointOn, familyMatrix_fromOriginal]

/-- The actual family of automorphisms of the native free-fourteen sheaf. -/
def freeIso (T : Over base) (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    freeOn T.left 14 ≅ freeOn T.left 14 := by
  let a := Stacks.FreeSheafMatrix.ofMatrix (familyMatrix T g)
  have : IsIso a := (Stacks.FreeSheafMatrix.isIso_iff_isUnit_det a).mpr (by
    rw [Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (PrimitiveRingCoordinates.primitiveMatrix_isUnit _ _ g))
  exact asIso a

theorem freeIso_matrix (T : Over base) (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    Stacks.FreeSheafMatrix.toMatrix (freeIso T g).hom = familyMatrix T g :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

theorem freeIso_one (T : Over base) : (freeIso T 1).hom = 𝟙 (freeOn T.left 14) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [freeIso_matrix, familyMatrix_one, Stacks.FreeSheafMatrix.toMatrix_id]

theorem freeIso_mul (T : Over base) (g h : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    (freeIso T (g*h)).hom = (freeIso T h).hom ≫ (freeIso T g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, freeIso_matrix, freeIso_matrix,
    freeIso_matrix, familyMatrix_mul]

theorem freeIso_pullback {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    PrimitiveFreeMatrixPullback.pulledFreeEnd f.left 14 (freeIso T g).hom =
      (freeIso T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g)).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [PrimitiveFreeMatrixPullback.pulledFreeEnd_matrix, freeIso_matrix, freeIso_matrix,
    familyMatrix_natural]

theorem freeIso_pullback_inv {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    (pullbackFreeIso f.left 14).inv ≫ (Scheme.Modules.pullback f.left).map (freeIso T g).hom =
      (freeIso T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g)).hom ≫
        (pullbackFreeIso f.left 14).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f.left 14).inv) (freeIso_pullback f g)
  simp only [PrimitiveFreeMatrixPullback.pulledFreeEnd, Category.assoc] at h
  rw [(pullbackFreeIso f.left 14).hom_inv_id, Category.comp_id] at h
  exact h

/-- Inverse precomposition sends a quotient's kernel to its primitive transform. -/
def transform (T : Over base) (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤))
    (q : QuotientPresentation T.left 9 14) : QuotientPresentation T.left 9 14 := by
  let : Epi q.map := q.map_epi
  exact { target := q.target
          map := (freeIso T g⁻¹).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic (T : Over base)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤))
    {q q' : QuotientPresentation T.left 9 14} (h : q.Isomorphic q') :
    (transform T g q).Isomorphic (transform T g q') := by
  obtain ⟨e,he⟩ := h
  refine ⟨e, ?_⟩
  change ((freeIso T g⁻¹).hom ≫ q.map) ≫ e.hom = (freeIso T g⁻¹).hom ≫ q'.map
  rw [Category.assoc, he]

theorem transform_one (T : Over base) (q : QuotientPresentation T.left 9 14) :
    (transform T 1 q).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change ((freeIso T (1 : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤))⁻¹).hom ≫ q.map) ≫
    𝟙 _ = q.map
  rw [inv_one, freeIso_one, Category.id_comp, Category.comp_id]

theorem transform_mul (T : Over base) (g h : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤))
    (q : QuotientPresentation T.left 9 14) :
    (transform T g (transform T h q)).Isomorphic (transform T (g*h) q) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((freeIso T g⁻¹).hom ≫ (freeIso T h⁻¹).hom ≫ q.map) ≫ 𝟙 _ =
    (freeIso T (g*h)⁻¹).hom ≫ q.map
  simp only [_root_.mul_inv_rev, freeIso_mul, Category.comp_id, Category.assoc]

theorem pullback_transform {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤))
    (q : QuotientPresentation T.left 9 14) :
    (pullbackPresentation f.left (transform T g q)).Isomorphic
      (transform T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g)
        (pullbackPresentation f.left q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f.left 14).inv ≫
    (Scheme.Modules.pullback f.left).map ((freeIso T g⁻¹).hom ≫ q.map)) ≫ 𝟙 _ =
      (freeIso T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g)⁻¹).hom ≫
        (pullbackFreeIso f.left 14).inv ≫ (Scheme.Modules.pullback f.left).map q.map
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc, freeIso_pullback_inv,
    Category.assoc, map_inv]

def transformPoints (T : Over base) (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    Points T.left 9 14 → Points T.left 9 14 :=
  Quotient.lift (fun q => (⟦transform T g q⟧ : Points T.left 9 14)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic T g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one (T : Over base) (x : Points T.left 9 14) :
    transformPoints T 1 x = x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one T q))

theorem transformPoints_mul (T : Over base)
    (g h : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) (x : Points T.left 9 14) :
    transformPoints T g (transformPoints T h x) = transformPoints T (g*h) x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_mul T g h q))

theorem transformPoints_natural {T T' : Over base} (f : T' ⟶ T)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) (x : Points T.left 9 14) :
    pullbackPointsMap f.left 9 14 (transformPoints T g x) =
      transformPoints T' (Sp6GroupScheme.mapMatrix f.left.appTop.hom g)
        (pullbackPointsMap f.left 9 14 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform f g q))

end M9Native.PrimitiveFamilyFreeAction
