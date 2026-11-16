module

public import M9StacksIntegration.SplitAlgebraExtensionClass
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPull

/-! Read actual morphisms on the opens of a solution. A retraction of its
closed immersion gives a genuine algebra section after forgetting the base. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sheaves.RingedSpaceDifferentials (structureSheafMap)

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.SolutionSplitBaseSection

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

theorem baseIso_inv_comp {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) : Q.baseIso.inv ≫ r.hom.base = q.hom.base := by
  have hb : Q.baseIso.hom ≫ q.hom.base = r.hom.base :=
    congrArg (fun a : X ⟶ T => a.hom.base) h
  rw [← hb, Iso.inv_hom_id_assoc]

theorem opens_read {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) (V : Opens T.carrier) :
    (Opens.map q.hom.base).obj V =
      (Opens.map Q.baseIso.inv).obj ((Opens.map r.hom.base).obj V) := by
  rw [← Opens.map_comp_obj, baseIso_inv_comp Q q r h]

def readPresheafMap {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) : T.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat.{u} r.hom.base).obj Q.thickenedPresheaf where
  app V := q.hom.c.app V ≫ Q.X'.presheaf.map (eqToHom (congrArg op (opens_read Q q r h V.unop)))
  naturality {V W} k := by
    have hnat := q.hom.c.naturality k
    simp only [TopCat.Presheaf.pushforward_obj_map] at hnat ⊢
    rw [reassoc_of% hnat]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun a => q.hom.c.app V ≫ Q.X'.presheaf.map a) (Subsingleton.elim _ _)

def readSheafMap {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) : T.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} r.hom.base).obj Q.thickenedSheaf :=
  ObjectProperty.homMk (readPresheafMap Q q r h)

def readBase {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) : inverseImageBaseRing r ⟶ Q.thickenedSheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} r.hom.base).homEquiv _ _).symm
    (readSheafMap Q q r h)

theorem readBase_original : readBase Q Q.f' (f ≫ t) Q.comm = Q.thickenedSheafBase := rfl

theorem readSheafMap_reduction {T : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) :
    readSheafMap Q q r h ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} r.hom.base).map Q.thickenedSheafReduction =
        structureSheafMap r := by
  subst r
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (Q.i.hom.base ≫ q.hom.base)
  change Q.comorphismOnOpensSheafMap q ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} (Q.i.hom.base ≫ q.hom.base)).map
      Q.thickenedSheafReduction = structureSheafMap (Q.i ≫ q)
  have he := Q.comorphismOnOpens_adjoint_comp_reduction q
  calc
    _ = (A.homEquiv _ _)
        ((A.homEquiv _ _).symm (Q.comorphismOnOpensSheafMap q) ≫
          Q.thickenedSheafReduction) := by
      simpa only [Equiv.apply_symm_apply] using
        (A.homEquiv_naturality_right
          ((A.homEquiv _ _).symm (Q.comorphismOnOpensSheafMap q))
          Q.thickenedSheafReduction).symm
    _ = (A.homEquiv _ _) (Stacks.SheafOfModules.ringedSpaceStructureMap (Q.i ≫ q)) :=
      congrArg (A.homEquiv _ _) he
    _ = _ := Equiv.apply_symm_apply _ _

theorem readSheafMap_comp {T U : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) (s : T ⟶ U) :
    readSheafMap Q (q ≫ s) (r ≫ s) (by rw [← Category.assoc, h]) =
      structureSheafMap s ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} s.hom.base).map (readSheafMap Q q r h) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  change (s.hom.c.app V ≫ q.hom.c.app _) ≫ Q.X'.presheaf.map (eqToHom _) =
    s.hom.c.app V ≫ (q.hom.c.app _ ≫ Q.X'.presheaf.map (eqToHom _))
  rw [Category.assoc]

theorem readBase_comp {T U : RingedSpace.{u, u}} (q : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) (s : T ⟶ U) :
    readBase Q (q ≫ s) (r ≫ s) (by rw [← Category.assoc, h]) =
      baseInverseImageRingMap r s ≫ readBase Q q r h := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (r ≫ s).hom.base).homEquiv _ _).injective
  have he := adjointBaseHom_baseInverseImageRingMap_comp (t := s) r
    Q.thickenedSheaf (readBase Q q r h)
  change _ = structureSheafMap s ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} s.hom.base).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        r.hom.base).homEquiv _ _) (readBase Q q r h)) at he
  have hc : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      r.hom.base).homEquiv _ _) (readBase Q q r h) = readSheafMap Q q r h :=
    Equiv.apply_symm_apply _ _
  rw [hc] at he
  exact (Equiv.apply_symm_apply _ _).trans ((readSheafMap_comp Q q r h s).trans he.symm)

def sectionOfRetraction (q : Q.X' ⟶ X) (h : Q.i ≫ q = 𝟙 X) :
    X.sheaf ⟶ Q.thickenedSheaf := readSheafMap Q q (𝟙 X) h

theorem sectionOfRetraction_reduction (q : Q.X' ⟶ X) (h : Q.i ≫ q = 𝟙 X) :
    sectionOfRetraction Q q h ≫ Q.thickenedSheafReduction = 𝟙 _ :=
  readSheafMap_reduction Q q (𝟙 X) h

theorem readBase_retraction (q : Q.X' ⟶ X) (h : Q.i ≫ q = 𝟙 X) :
    readBase Q q (𝟙 X) h = structureRingMap (𝟙 X) ≫ sectionOfRetraction Q q h := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (𝟙 X.carrier)
  change (A.homEquiv _ _).symm (sectionOfRetraction Q q h) =
    (A.homEquiv _ _).symm (𝟙 _) ≫ sectionOfRetraction Q q h
  exact (congrArg (A.homEquiv _ _).symm (Category.id_comp _).symm).trans
    (A.homEquiv_naturality_right_symm (𝟙 _) (sectionOfRetraction Q q h))

theorem readBase_split (q : Q.X' ⟶ X) (h : Q.i ≫ q = 𝟙 X)
    {T : RingedSpace.{u, u}} (r : X ⟶ T) :
    readBase Q (q ≫ r) r (by rw [← Category.assoc, h, Category.id_comp]) =
      structureRingMap r ≫ sectionOfRetraction Q q h := by
  have he := readBase_comp Q q (𝟙 X) h r
  rw [readBase_retraction Q q h] at he
  exact he.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ sectionOfRetraction Q q h) (baseInverseImageRingMap_comp (𝟙 X) r)))

theorem readBase_congr {T : RingedSpace.{u, u}} (q q' : Q.X' ⟶ T) (r : X ⟶ T)
    (h : Q.i ≫ q = r) (h' : Q.i ≫ q' = r) (hq : q = q') :
    readBase Q q r h = readBase Q q' r h' := by
  subst q'
  rfl

/-- The forgotten extension is genuinely split when the total space has
an actual retraction over the unthickened base. -/
theorem restrictBase_extClass_eq_zero (p : S' ⟶ S) (q : Q.X' ⟶ X)
    (h : Q.i ≫ q = 𝟙 X)
    (hbase : q ≫ ((f ≫ t) ≫ p) = Q.f' ≫ p) :
    (Q.toAlgebraExtension.restrictBase p).toPresented.extClass = 0 := by
  have hr := readBase_comp Q Q.f' (f ≫ t) Q.comm p
  have hc := readBase_congr Q (Q.f' ≫ p) (q ≫ ((f ≫ t) ≫ p))
    ((f ≫ t) ≫ p) (by rw [← Category.assoc, Q.comm])
    (by rw [← Category.assoc, h, Category.id_comp]) hbase.symm
  have hb : structureRingMap ((f ≫ t) ≫ p) ≫ sectionOfRetraction Q q h =
      (Q.toAlgebraExtension.restrictBase p).base := by
    exact ((hr.trans (congrArg (baseInverseImageRingMap (f ≫ t) p ≫ ·)
      (readBase_original Q))).symm.trans (hc.trans (readBase_split Q q h _))).symm
  exact SplitAlgebraExtensionClass.extClass_eq_zero_of_algebra_section
    (Q.toAlgebraExtension.restrictBase p) (sectionOfRetraction Q q h)
    (sectionOfRetraction_reduction Q q h) hb

end M9Native.SolutionSplitBaseSection
