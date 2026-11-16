module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionHomAlgebraExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPullbackMap

/-! Actual maps of solution structure sheaves along a different special
space, obtained by conjugating the original ringed-space morphism through
the checked native solution/extension space identifications. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace M9Native.SolutionThickenedSheafMapAlong

/-- Rewrite only the underlying continuous map of an actual ringed-space
morphism; its comorphism is transported along that actual equality. -/
def changeBase {A B : RingedSpace.{u,u}} (m : A ⟶ B)
    (b : A.carrier ⟶ B.carrier) (hb : m.hom.base = b) : A ⟶ B :=
  ⟨{ base := b, c := by subst b; exact m.hom.c }⟩

theorem changeBase_eq {A B : RingedSpace.{u,u}} (m : A ⟶ B)
    (b : A.carrier ⟶ B.carrier) (hb : m.hom.base = b) : changeBase m b hb = m := by
  subst b
  rfl

variable {Y X S S' : RingedSpace.{u,u}} {t : S ⟶ S'}
  {ht : IsFirstOrderThickening t} {fY : Y ⟶ S} {fX : X ⟶ S}
  {F : SheafOfModules.{u} (structureSheafRing Y)}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {cY : (modulePullback fY).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ F}
  {cX : (modulePullback fX).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (QY : DeformationSolution t ht fY F cY) (QX : DeformationSolution t ht fX G cX)
  (g : X ⟶ Y) (φ : QX.X' ⟶ QY.X') (hφ : QX.i ≫ φ = g ≫ QY.i)

/-- The original total-space map in the actual native extension-space
coordinates. -/
def spaceMap : QX.toAlgebraExtension.space ⟶ QY.toAlgebraExtension.space :=
  QX.fromSpace ≫ φ ≫ QY.toSpace

include hφ in
theorem spaceMap_base : (spaceMap QY QX φ).hom.base = g.hom.base := by
  have hb : QX.baseIso.hom ≫ φ.hom.base = g.hom.base ≫ QY.baseIso.hom :=
    congrArg (fun m : X ⟶ QY.X' => m.hom.base) hφ
  change QX.baseIso.hom ≫ φ.hom.base ≫ QY.baseIso.inv = g.hom.base
  rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same true map with underlying continuous map literally g. -/
def alongSpace : QX.toAlgebraExtension.space ⟶ QY.toAlgebraExtension.space :=
  changeBase (spaceMap QY QX φ) g.hom.base (spaceMap_base QY QX g φ hφ)

theorem alongSpace_eq : alongSpace QY QX g φ hφ = spaceMap QY QX φ :=
  changeBase_eq _ _ _

/-- Its actual comorphism, read on the original special spaces. -/
abbrev sheafMap : QY.thickenedSheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj QX.thickenedSheaf :=
  ObjectProperty.homMk (alongSpace QY QX g φ hφ).hom.c

/-- The actual reduction square, as a ringed-space equality. -/
theorem reduction_square : QX.toAlgebraExtension.thickening ≫ alongSpace QY QX g φ hφ =
    g ≫ QY.toAlgebraExtension.thickening := by
  rw [alongSpace_eq]
  change QX.toAlgebraExtension.thickening ≫ (QX.fromSpace ≫ φ ≫ QY.toSpace) = _
  calc
    _ = (QX.i ≫ (QX.toSpace ≫ QX.fromSpace)) ≫ φ ≫ QY.toSpace := by
      have h := congrArg (fun m => m ≫ QX.fromSpace ≫ φ ≫ QY.toSpace)
        QX.i_comp_toSpace.symm
      simpa only [Category.assoc] using h
    _ = (QX.i ≫ φ) ≫ QY.toSpace := by
      rw [QX.toSpace_fromSpace, Category.comp_id]
      simp only [Category.assoc]
    _ = (g ≫ QY.i) ≫ QY.toSpace := by rw [hφ]
    _ = _ := by rw [Category.assoc, QY.i_comp_toSpace]

/-- The original sheaf map commutes with the actual reductions. -/
theorem sheafMap_comp_reduction :
    sheafMap QY QX g φ hφ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map QX.thickenedSheafReduction =
      QY.thickenedSheafReduction ≫ structureComorphism g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  apply funext
  intro U
  change (alongSpace QY QX g φ hφ).hom.c.app U ≫
      QX.thickenedReduction.app ((Opens.map g.hom.base).op.obj U) =
    QY.thickenedReduction.app U ≫ g.hom.c.app U
  have h := SheafedSpace.congr_hom_app (reduction_square QY QX g φ hφ) U
  change (alongSpace QY QX g φ hφ).hom.c.app U ≫
      QX.thickenedReduction.app ((Opens.map g.hom.base).op.obj U) =
    (QY.thickenedReduction.app U ≫ g.hom.c.app U) ≫
      X.presheaf.map (𝟙 ((Opens.map g.hom.base).op.obj U)) at h
  rw [X.presheaf.map_id] at h
  exact h.trans (Category.comp_id _)

/-- The actual algebra/base square, with no supplied sheaf compatibility. -/
theorem over_square (hbase : φ ≫ QY.f' = QX.f') :
    alongSpace QY QX g φ hφ ≫ QY.toAlgebraExtension.over = QX.toAlgebraExtension.over := by
  rw [alongSpace_eq]
  change (QX.fromSpace ≫ φ ≫ QY.toSpace) ≫ QY.toAlgebraExtension.over = _
  calc
    _ = QX.fromSpace ≫ (φ ≫ QY.f') := by
      simp only [Category.assoc, QY.toSpace_comp_over]
    _ = QX.fromSpace ≫ QX.f' := by rw [hbase]
    _ = (QX.fromSpace ≫ QX.toSpace) ≫ QX.toAlgebraExtension.over := by
      rw [Category.assoc, QX.toSpace_comp_over]
    _ = _ := by rw [QX.fromSpace_toSpace, Category.id_comp]

end M9Native.SolutionThickenedSheafMapAlong
