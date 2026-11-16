module

public import M9StacksIntegration.Sp6GaussCellCoordinates
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual principal-open Gauss chart of the frozen Sp6 scheme

The target ring is the original frozen symplectic coordinate ring,
localized at the actual determinant of its universal top-left block.
The all-test-scheme equivalences construct a genuine scheme
isomorphism with the parameter chart by uniqueness of representing
objects. No property of field-valued points is used to build this iso.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.Sp6GaussPrincipalOpen

open Sp6GaussCellFunctor

def determinant : Sp6CoordinateRing.CoordinateRing.{u} :=
  Sp6CoordinateRing.universalMatrix.toBlocks₁₁.det

abbrev CoordinateRing : Type u := Localization.Away determinant.{u}
abbrev scheme : Scheme.{u} := Spec (.of CoordinateRing.{u})
abbrev parameterScheme : Scheme.{u} := Spec (.of Sp6GaussCellCoordinates.CoordinateRing.{u})

/-- Universal mapping property of a literal principal localization. -/
def awayHomEquiv {A R : Type u} [CommRing A] [CommRing R] (a : A) :
    (Localization.Away a →+* R) ≃ {f : A →+* R // IsUnit (f a)} where
  toFun f := ⟨f.comp (algebraMap A (Localization.Away a)),
    (IsLocalization.Away.algebraMap_isUnit a).map f⟩
  invFun p := IsLocalization.Away.lift a p.property
  left_inv f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    exact IsLocalization.Away.lift_comp a _
  right_inv p := by
    apply Subtype.ext
    exact IsLocalization.Away.lift_comp a _

variable (R : Type u) [CommRing R]

theorem hom_determinant (f : Sp6CoordinateRing.CoordinateRing.{u} →+* R) :
    f determinant = (Sp6CoordinateRing.matrixOfHom R f).val.toBlocks₁₁.det :=
  RingHom.map_det f Sp6CoordinateRing.universalMatrix.toBlocks₁₁

theorem evaluation_determinant (g : Matrix.symplecticGroup (Fin 3) R) :
    Sp6CoordinateRing.evaluation.{u} R g determinant.{u} = g.val.toBlocks₁₁.det := by
  have hm : Sp6CoordinateRing.matrixOfHom R (Sp6CoordinateRing.evaluation.{u} R g) = g :=
    (Sp6CoordinateRing.homEquiv R).apply_symm_apply g
  exact (hom_determinant R (Sp6CoordinateRing.evaluation.{u} R g)).trans
    (congrArg (fun M : Matrix.symplecticGroup (Fin 3) R => M.val.toBlocks₁₁.det) hm)

def coordinateHomCellEquiv :
    {f : Sp6CoordinateRing.CoordinateRing.{u} →+* R // IsUnit (f determinant)} ≃ Cell R where
  toFun p := ⟨Sp6CoordinateRing.homEquiv R p.val, by
    change IsUnit (Sp6CoordinateRing.matrixOfHom R p.val).val.toBlocks₁₁.det
    rw [← hom_determinant]
    exact p.property⟩
  invFun g := ⟨Sp6CoordinateRing.evaluation R g.val, by
    rw [evaluation_determinant]
    exact g.property⟩
  left_inv p := by
    apply Subtype.ext
    exact (Sp6CoordinateRing.homEquiv R).symm_apply_apply p.val
  right_inv g := by
    apply Subtype.ext
    exact (Sp6CoordinateRing.homEquiv R).apply_symm_apply g.val

def homEquiv : (CoordinateRing.{u} →+* R) ≃ Cell R :=
  (awayHomEquiv determinant).trans (coordinateHomCellEquiv R)

theorem homEquiv_comp {S : Type u} [CommRing S]
    (f : CoordinateRing.{u} →+* R) (ρ : R →+* S) :
    homEquiv S (ρ.comp f) = mapCell ρ (homEquiv R f) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  rfl

/-- The literal unit-cell functor on all test schemes. -/
def pointsFunctor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Cell (Scheme.Γ.obj T)
  map f := TypeCat.ofHom (mapCell (Scheme.Γ.map f).hom)
  map_id T := by
    ext g i j
    rfl
  map_comp f g := by
    ext h i j
    rfl

def principalRepresentableBy : pointsFunctor.{u}.RepresentableBy scheme.{u} where
  homEquiv {T} := (specRingHomEquiv CoordinateRing.{u} T).trans (homEquiv Γ(T,⊤))
  homEquiv_comp {X Y} f g := by
    change homEquiv Γ(X,⊤) (specRingHomEquiv CoordinateRing X (f ≫ g)) =
      mapCell (Scheme.Γ.map f.op).hom
        (homEquiv Γ(Y,⊤) (specRingHomEquiv CoordinateRing Y g))
    rw [specRingHomEquiv_comp]
    exact homEquiv_comp _ _ _

def parameterRepresentableBy : pointsFunctor.{u}.RepresentableBy parameterScheme.{u} where
  homEquiv {T} := (specRingHomEquiv Sp6GaussCellCoordinates.CoordinateRing.{u} T).trans
    ((Sp6GaussCellCoordinates.homEquiv Γ(T,⊤)).trans gaussEquiv)
  homEquiv_comp {X Y} f g := by
    change gaussEquiv (Sp6GaussCellCoordinates.homEquiv Γ(X,⊤)
      (specRingHomEquiv Sp6GaussCellCoordinates.CoordinateRing X (f ≫ g))) =
        mapCell (Scheme.Γ.map f.op).hom
          (gaussEquiv (Sp6GaussCellCoordinates.homEquiv Γ(Y,⊤)
            (specRingHomEquiv Sp6GaussCellCoordinates.CoordinateRing Y g)))
    rw [specRingHomEquiv_comp, Sp6GaussCellCoordinates.homEquiv_comp]
    exact (gaussEquiv_natural _ _).symm

/-- The genuine parameter/principal-open scheme isomorphism. -/
def chartIso : parameterScheme.{u} ≅ scheme.{u} :=
  parameterRepresentableBy.uniqueUpToIso principalRepresentableBy

def inclusion : scheme.{u} ⟶ Sp6GroupScheme.integralScheme.{u} :=
  Spec.map (CommRingCat.ofHom (algebraMap Sp6CoordinateRing.CoordinateRing CoordinateRing))

instance inclusion_isOpenImmersion : IsOpenImmersion inclusion.{u} := by
  dsimp [inclusion, scheme, Sp6GroupScheme.integralScheme]
  infer_instance

/-- The actual Gauss chart map into the original frozen Sp6 scheme. -/
def chart : parameterScheme.{u} ⟶ Sp6GroupScheme.integralScheme.{u} :=
  chartIso.hom ≫ inclusion

instance chart_isOpenImmersion : IsOpenImmersion chart.{u} := by
  dsimp [chart]
  infer_instance

/-- The principal-open representing point is literally the original
symplectic point after the actual localization inclusion. -/
theorem principalPoints_val {T : Scheme.{u}} (f : T ⟶ scheme.{u}) :
    (principalRepresentableBy.homEquiv f).val =
      Sp6GroupScheme.schemePointsEquiv T (f ≫ inclusion) := by
  have hf : specRingHomEquiv CoordinateRing T f =
      (Scheme.Γ.map f.op).hom.comp (Scheme.ΓSpecIso (.of CoordinateRing)).inv.hom := by
    simpa only [Category.comp_id, specRingHomEquiv_id] using
      specRingHomEquiv_comp CoordinateRing f (𝟙 scheme)
  have hn : specRingHomEquiv Sp6CoordinateRing.CoordinateRing T (f ≫ inclusion) =
      (specRingHomEquiv CoordinateRing T f).comp
        (algebraMap Sp6CoordinateRing.CoordinateRing CoordinateRing) := by
    rw [specRingHomEquiv_comp, inclusion, specRingHomEquiv_specMap, hf]
    rfl
  apply Subtype.ext
  ext i j
  change (specRingHomEquiv CoordinateRing T f)
      (algebraMap Sp6CoordinateRing.CoordinateRing CoordinateRing
        (Sp6CoordinateRing.coordinate i j)) =
    (specRingHomEquiv Sp6CoordinateRing.CoordinateRing T (f ≫ inclusion))
      (Sp6CoordinateRing.coordinate i j)
  rw [hn]
  rfl

/-- Every actual test-scheme point with actual unit top-left
determinant factors through this actual Gauss open immersion. -/
theorem exists_chart_factor {T : Scheme.{u}} (p : T ⟶ Sp6GroupScheme.integralScheme.{u})
    (hp : IsUnit (Sp6GroupScheme.schemePointsEquiv T p).val.toBlocks₁₁.det) :
    ∃ z : T ⟶ parameterScheme.{u}, z ≫ chart = p := by
  let c : Cell Γ(T,⊤) := ⟨Sp6GroupScheme.schemePointsEquiv T p,hp⟩
  let f : T ⟶ scheme := principalRepresentableBy.homEquiv.symm c
  refine ⟨f ≫ chartIso.inv, ?_⟩
  rw [chart, Category.assoc, Iso.inv_hom_id_assoc]
  apply (Sp6GroupScheme.schemePointsEquiv T).injective
  rw [← principalPoints_val]
  exact congrArg Subtype.val (principalRepresentableBy.homEquiv.apply_symm_apply c)

end M9Native.Sp6GaussPrincipalOpen

