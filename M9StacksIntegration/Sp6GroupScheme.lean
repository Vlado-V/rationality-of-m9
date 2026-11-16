module

public import M9StacksIntegration.Sp6CoordinateRing
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Action
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear

/-!
# The actual symplectic group scheme and all of its test-scheme points

The affine integral model is the spectrum of the displayed symplectic
coordinate ring. Its base change to any scheme represents symplectic
matrices over global sections on every test scheme. Yoneda supplies the
genuine internal group structure from literal matrix multiplication.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace M9Native.Sp6GroupScheme

open Sp6CoordinateRing

variable {R A : Type u} [CommRing R] [CommRing A]

def mapMatrix (ρ : R →+* A) :
    Matrix.symplecticGroup (Fin 3) R →* Matrix.symplecticGroup (Fin 3) A where
  toFun g := ⟨g.val.map ρ, SymplecticGroup.map_mem g.property ρ⟩
  map_one' := Subtype.ext (Matrix.map_one _ (map_zero ρ) (map_one ρ))
  map_mul' _ _ := Subtype.ext Matrix.map_mul

@[simp] theorem mapMatrix_apply (ρ : R →+* A)
    (g : Matrix.symplecticGroup (Fin 3) R) (i j : Index) :
    (mapMatrix ρ g : Matrix Index Index A) i j = ρ (g.val i j) := rfl

def pointsFunctor : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Matrix.symplecticGroup (Fin 3) (Scheme.Γ.obj T))
  map f := GrpCat.ofHom (mapMatrix (Scheme.Γ.map f).hom)
  map_id T := by
    ext g i j
    rfl
  map_comp f g := by
    ext h i j
    rfl

abbrev integralScheme : Scheme.{u} := Spec (.of CoordinateRing)

def schemePointsEquiv (T : Scheme.{u}) :
    (T ⟶ integralScheme) ≃ Matrix.symplecticGroup (Fin 3) Γ(T,⊤) :=
  (specRingHomEquiv CoordinateRing T).trans (Sp6CoordinateRing.homEquiv Γ(T,⊤))

def representableBy : (pointsFunctor.{u} ⋙ forget GrpCat).RepresentableBy integralScheme where
  homEquiv {X} := schemePointsEquiv X
  homEquiv_comp {X Y} f g := by
    apply Subtype.ext
    ext i j
    change (specRingHomEquiv CoordinateRing X (f ≫ g)) (coordinate i j) =
      (Scheme.Γ.map f.op).hom ((specRingHomEquiv CoordinateRing Y g) (coordinate i j))
    rw [specRingHomEquiv_comp]
    rfl

abbrev integralBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

def integralProjection : integralScheme ⟶ integralBase :=
  specULiftZIsTerminal.from integralScheme

/-- The native symplectic group scheme over the chosen base scheme. -/
def obj (S : Scheme.{u}) : Over S :=
  Over.mk (pullback.snd integralProjection (specULiftZIsTerminal.from S))

abbrev overPointsFunctor (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ pointsFunctor

def overRepresentableBy (S : Scheme.{u}) :
    (overPointsFunctor S ⋙ forget GrpCat).RepresentableBy (obj S) where
  homEquiv {T} :=
    ({ toFun := fun p => p.left ≫ pullback.fst integralProjection (specULiftZIsTerminal.from S)
       invFun := fun p => Over.homMk
         (pullback.lift p T.hom (specULiftZIsTerminal.hom_ext _ _))
         (pullback.lift_snd _ _ _)
       left_inv := fun p => Over.OverMorphism.ext (pullback.hom_ext
         (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans p.w.symm))
       right_inv := fun p => pullback.lift_fst _ _ _ } :
      (T ⟶ obj S) ≃ (T.left ⟶ integralScheme)).trans (schemePointsEquiv T.left)
  homEquiv_comp {T T'} f g := by
    change schemePointsEquiv T.left
      ((f.left ≫ g.left) ≫ pullback.fst integralProjection (specULiftZIsTerminal.from S)) =
      (pointsFunctor.map f.left.op)
        (schemePointsEquiv T'.left
          (g.left ≫ pullback.fst integralProjection (specULiftZIsTerminal.from S)))
    rw [Category.assoc]
    exact representableBy.homEquiv_comp f.left _

instance groupObj (S : Scheme.{u}) : GrpObj (obj S) :=
  GrpObj.ofRepresentableBy (obj S) (overPointsFunctor S) (overRepresentableBy S)

def groupScheme (S : Scheme.{u}) : GroupSchemeOverPoints S :=
  GrpObj.toGroupSchemeOverPoints (obj S)

/-- All test-scheme points, with their actual matrix group law. -/
def pointsMulEquiv (S : Scheme.{u}) (T : Over S) :
    (T ⟶ obj S) ≃* Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤) where
  toEquiv := (overRepresentableBy S).homEquiv
  map_mul' := ((yonedaGrpObjIsoOfRepresentableBy (obj S)
    (overPointsFunctor S) (overRepresentableBy S)).hom.app (op T)).hom.map_mul

theorem pointsMulEquiv_natural {S : Scheme.{u}} {T T' : Over S} (f : T' ⟶ T)
    (g : T ⟶ obj S) :
    pointsMulEquiv S T' (f ≫ g) = mapMatrix f.left.appTop.hom (pointsMulEquiv S T g) := by
  exact (overRepresentableBy S).homEquiv_comp f g

@[simp] theorem pointsMulEquiv_one (S : Scheme.{u}) (T : Over S) :
    pointsMulEquiv S T 1 = 1 := (pointsMulEquiv S T).map_one

@[simp] theorem pointsMulEquiv_mul (S : Scheme.{u}) (T : Over S)
    (g h : T ⟶ obj S) :
    pointsMulEquiv S T (g*h) = pointsMulEquiv S T g * pointsMulEquiv S T h :=
  (pointsMulEquiv S T).map_mul g h

/-- The genuine constant point associated to a matrix over the base field/ring. -/
def constantPoint (K : Type u) [CommRing K] (g : Matrix.symplecticGroup (Fin 3) K) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ obj (Spec (.of K)) :=
  (pointsMulEquiv (Spec (.of K)) (Over.mk (𝟙 _))).symm
    (mapMatrix (Scheme.ΓSpecIso (.of K)).inv.hom g)

@[simp] theorem pointsMulEquiv_constantPoint (K : Type u) [CommRing K]
    (g : Matrix.symplecticGroup (Fin 3) K) :
    pointsMulEquiv (Spec (.of K)) (Over.mk (𝟙 _)) (constantPoint K g) =
      mapMatrix (Scheme.ΓSpecIso (.of K)).inv.hom g :=
  (pointsMulEquiv _ _).apply_symm_apply _

end M9Native.Sp6GroupScheme
