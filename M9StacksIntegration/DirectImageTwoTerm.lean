module

public import M9StacksIntegration.PoincareOrdinaryDegreeZero
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Algebra.Homology.ShortComplex.ShortExactMkOfIso

/-!
# Genuine ordinary bundles in an actual derived restriction triangle

The differential is recovered from the actual geometric short exact
sequence by full faithfulness of modules in degree zero. The resulting
actual two-term complex represents the actual derived direct image.
No Chern identity or chosen fibre map is supplied as an assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry RingedSpaceModuleAdjunction Opposite
open CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit derivedPushforwardCompIso
    derivedPushforwardCommShift derivedPushforward_isTriangulated)
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace M9Native.DirectImageTwoTerm


attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-- If the actual derived image is a module in degree zero, it is
isomorphic to the actual ordinary direct image in degree zero. -/
def derivedPushforwardIsoSinglePushforward
    {Y S : Scheme.{u}} (p : Y ⟶ S) (L : Y.Modules) (r : ℕ)
    (h : ProperFlatFibreEulerCharacteristic.HasDerivedPushforwardRank p L 0 r) :
    ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p L ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward p).obj L) :=
  let E := h.choose
  let e := h.choose_spec.2.some
  e ≪≫ (DerivedCategory.singleFunctor S.Modules 0).mapIso
    (M9Native.PoincareChern.OrdinaryDegreeZero.pushforwardIsoOfIsoSingle e).symm

/-- Pushing an ordinary direct image along an affine morphism is
the same derived object as pushing along the composite, for a
quasi-coherent module. -/
def derivedPushforwardOfAffinePushforwardIso
    {Z Y S : Scheme.{u}} (i : Z ⟶ Y) [IsAffineHom i] (p : Y ⟶ S)
    (L : Z.Modules) (hL : L.IsQuasicoherent) :
    ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p
        ((Scheme.Modules.pushforward i).obj L) ≅
      ProperFlatFibreEulerCharacteristic.derivedPushforwardModule (i ≫ p) L :=
  (derivedPushforward p.toLRSHom.toShHom).mapIso
      (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
        i 0 L hL) ≪≫
    (derivedPushforwardCompIso i.toLRSHom.toShHom p.toLRSHom.toShHom).app
      ((DerivedCategory.singleFunctor Z.Modules 0).obj L)

/-- A genuine short exact sequence whose last two derived images are
modules in degree zero supplies an actual global two-term presentation
of the first derived image.  No differential is assumed: it is recovered
from the restriction map in the distinguished triangle. -/
theorem exists_twoTermTriangle_of_shortExact
    {Y S : Scheme.{u}} (p : Y ⟶ S) (C : ShortComplex Y.Modules)
    (hC : C.ShortExact) {E F : S.Modules}
    (eE : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₂ ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj E)
    (eF : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₃ ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj F) :
    ∃ (a : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₁ ⟶
        (DerivedCategory.singleFunctor S.Modules 0).obj E)
      (d : E ⟶ F)
      (b : (DerivedCategory.singleFunctor S.Modules 0).obj F ⟶
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₁)⟦(1 : ℤ)⟧),
      Triangle.mk a ((DerivedCategory.singleFunctor S.Modules 0).map d) b ∈
        distTriang (DerivedCategory S.Modules) := by
  let R := derivedPushforward p.toLRSHom.toShHom
  letI : R.CommShift ℤ := derivedPushforwardCommShift p.toLRSHom.toShHom
  haveI : R.IsTriangulated := derivedPushforward_isTriangulated p.toLRSHom.toShHom
  let T := R.mapTriangle.obj hC.singleTriangle
  let a := T.mor₁ ≫ eE.hom
  let d := (DerivedCategory.singleFunctor S.Modules 0).preimage
    (eE.inv ≫ T.mor₂ ≫ eF.hom)
  let b := eF.inv ≫ T.mor₃
  refine ⟨a, d, b, ?_⟩
  have hT : T ∈ distTriang (DerivedCategory S.Modules) :=
    R.map_distinguished _ hC.singleTriangle_distinguished
  apply isomorphic_distinguished T hT _
  refine Triangle.isoMk _ _ (Iso.refl _) eE.symm eF.symm ?_ ?_ ?_
  · simp [a, Category.assoc]
  · simp [d, Category.assoc]
  · simp [b, Category.assoc]

/-- A triangle `K → E[0] → F[0]` identifies `K` with the actual
cochain mapping cocone of the indicated module morphism.  Thus the
preceding triangle statement is a two-term complex, rather than only
a relation between classes in a Grothendieck group. -/
theorem twoTerm_mappingCocone_representation
    {A : Type*} [Category* A] [Abelian A]
    {K : DerivedCategory A} {E F : A}
    (a : K ⟶ (DerivedCategory.singleFunctor A 0).obj E) (d : E ⟶ F)
    (b : (DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((DerivedCategory.singleFunctor A 0).map d) b ∈
      distTriang (DerivedCategory A)) :
    Nonempty (K ≅ DerivedCategory.Q.obj (CochainComplex.mappingCocone
      ((CochainComplex.singleFunctor A 0).map d))) := by
  let φ := (CochainComplex.singleFunctor A 0).map d
  let T := Triangle.mk a ((DerivedCategory.singleFunctor A 0).map d) b
  let T' := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle φ)
  have hT' : T' ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  let e : T.rotate ≅ T'.rotate :=
    isoTriangleOfIso₁₂ _ _ (rot_of_distTriang T hT) (rot_of_distTriang T' hT')
      (Iso.refl _) (Iso.refl _) (by
        change (DerivedCategory.singleFunctor A 0).map d =
          DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map d)
        rfl)
  exact ⟨(shiftShiftNeg K (1 : ℤ)).symm ≪≫
    (shiftFunctor (DerivedCategory A) (-1 : ℤ)).mapIso (Triangle.π₃.mapIso e) ≪≫
    shiftShiftNeg _ (1 : ℤ)⟩

/-- A short exact sequence whose three actual derived images are modules
in degree zero gives a short exact sequence of those modules.  The maps
are obtained by applying the actual degree-zero homology functor. -/
theorem exists_shortExact_of_derivedImages
    {Y S : Scheme.{u}} (p : Y ⟶ S) (C : ShortComplex Y.Modules)
    (hC : C.ShortExact) (E₁ E₂ E₃ : S.Modules)
    (e₁ : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₁ ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj E₁)
    (e₂ : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₂ ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj E₂)
    (e₃ : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule p C.X₃ ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj E₃) :
    ∃ (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  let R := derivedPushforward p.toLRSHom.toShHom
  letI : R.CommShift ℤ := derivedPushforwardCommShift p.toLRSHom.toShHom
  letI : R.IsTriangulated := derivedPushforward_isTriangulated p.toLRSHom.toShHom
  let T := R.mapTriangle.obj hC.singleTriangle
  have hT : T ∈ distTriang (DerivedCategory S.Modules) :=
    R.map_distinguished _ hC.singleTriangle_distinguished
  let H := DerivedCategory.homologyFunctor S.Modules 0
  have hm : IsZero ((DerivedCategory.homologyFunctor S.Modules (-1)).obj T.obj₃) :=
    (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj E₃ (by norm_num)).of_iso
      ((DerivedCategory.homologyFunctor S.Modules (-1)).mapIso e₃)
  have hp : IsZero ((DerivedCategory.homologyFunctor S.Modules 1).obj T.obj₁) :=
    (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj E₁ (by norm_num)).of_iso
      ((DerivedCategory.homologyFunctor S.Modules 1).mapIso e₁)
  haveI : Mono (H.map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (-1) 0 (by norm_num)).2 (hm.eq_of_src _ _)
  haveI : Epi (H.map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT 0 1 (by norm_num)).2 (hp.eq_of_tgt _ _)
  let C₀ := ShortComplex.mk (H.map T.mor₁) (H.map T.mor₂)
    (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])
  have hC₀ : C₀.ShortExact :=
    ⟨DerivedCategory.HomologySequence.exact₂ T hT 0⟩
  let q₁ := H.mapIso e₁ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules 0).app E₁
  let q₂ := H.mapIso e₂ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules 0).app E₂
  let q₃ := H.mapIso e₃ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules 0).app E₃
  let a := q₁.inv ≫ H.map T.mor₁ ≫ q₂.hom
  let b := q₂.inv ≫ H.map T.mor₂ ≫ q₃.hom
  have w : a ≫ b = 0 := by
    simp only [a, b, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, comp_distTriang_mor_zero₁₂ _ hT,
      Functor.map_zero, zero_comp, comp_zero]
  refine ⟨a, b, w, ShortComplex.shortExact_of_iso ?_ hC₀⟩
  exact ShortComplex.isoMk q₁ q₂ q₃
    (by simp [a, C₀, Category.assoc]) (by simp [b, C₀, Category.assoc])


end M9Native.DirectImageTwoTerm
