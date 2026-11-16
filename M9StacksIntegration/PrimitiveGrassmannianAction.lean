module

import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

public import M9StacksIntegration.PrimitiveFamilyFreeAction
public import M9StacksIntegration.GrassmannianCharts

/-!
# The genuine symplectic group-scheme action on the native Gr(9,14)

The actual universal pair of a symplectic matrix and a quotient presentation
defines a scheme morphism through the native Grassmannian classifier.
Its laws and all-test-scheme compatibility follow from the original quotient
presentations and their canonical pullbacks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveGrassmannianAction

open AlgebraicGeometry.Grassmannian PrimitiveFamilyFreeAction

abbrev space : Scheme := GrassmannianCharts.space ℂ 9 14
abbrev projection : space ⟶ base := GrassmannianCharts.projection ℂ 9 14
abbrev overSpace : Over base := Over.mk projection
abbrev group : Over base := Sp6GroupScheme.obj base

/-- The literal native quotient class of a Grassmannian morphism. -/
def pointClass {T : Scheme} (p : T ⟶ space) : Points T 9 14 :=
  (functorData 9 14).objEquiv T ((schemeRepresentableBy 9 14).homEquiv
    (p ≫ GrassmannianCharts.toIntegral ℂ 9 14))

theorem pointClass_comp {S T : Scheme} (f : T ⟶ S) (p : S ⟶ space) :
    pointClass (f ≫ p) = pullbackPointsMap f 9 14 (pointClass p) := by
  change (functorData 9 14).objEquiv T ((schemeRepresentableBy 9 14).homEquiv
    ((f ≫ p) ≫ GrassmannianCharts.toIntegral ℂ 9 14)) = _
  rw [Category.assoc, (schemeRepresentableBy 9 14).homEquiv_comp]
  exact LagrangianGrassmannian.pointsEquiv_map f 9 14 _

/-- Classification into the original base-changed native Grassmannian. -/
def classifying {T : Scheme} (b : T ⟶ base) (q : Points T 9 14) : T ⟶ space :=
  pullback.lift b
    ((schemeRepresentableBy 9 14).homEquiv.symm (((functorData 9 14).objEquiv T).symm q))
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem classifying_projection {T : Scheme} (b : T ⟶ base)
    (q : Points T 9 14) : classifying b q ≫ projection = b := pullback.lift_fst _ _ _

theorem classifying_class {T : Scheme} (b : T ⟶ base) (q : Points T 9 14) :
    pointClass (classifying b q) = q := by
  rw [pointClass, classifying, pullback.lift_snd, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

theorem hom_ext {T : Scheme} (f h : T ⟶ space)
    (hb : f ≫ projection = h ≫ projection) (hc : pointClass f = pointClass h) : f = h := by
  apply pullback.hom_ext
  · exact hb
  · apply (schemeRepresentableBy 9 14).homEquiv.injective
    apply ((functorData 9 14).objEquiv T).injective
    exact hc

abbrev parameterSpace : Over base := group ⊗ overSpace

def universalMatrix : Matrix.symplecticGroup (Fin 3) Γ(parameterSpace.left,⊤) :=
  Sp6GroupScheme.pointsMulEquiv base parameterSpace (fst group overSpace)

def universalClass : Points parameterSpace.left 9 14 :=
  pointClass (snd group overSpace).left

/-- The actual scheme morphism induced by inverse precomposition of the universal quotient. -/
def actionLeft : parameterSpace.left ⟶ space :=
  classifying parameterSpace.hom (transformPoints parameterSpace universalMatrix universalClass)

def action : parameterSpace ⟶ overSpace :=
  Over.homMk actionLeft (classifying_projection _ _)

/-- Every test scheme sees precisely the original transformed quotient presentation class. -/
theorem action_pointClass (T : Over base) (g : T ⟶ group) (x : T ⟶ overSpace) :
    pointClass ((lift g x ≫ action).left) =
      transformPoints T (Sp6GroupScheme.pointsMulEquiv base T g) (pointClass x.left) := by
  let f : T ⟶ parameterSpace := lift g x
  have hg := Sp6GroupScheme.pointsMulEquiv_natural f (fst group overSpace)
  rw [show f ≫ fst group overSpace = g from lift_fst g x] at hg
  change Sp6GroupScheme.pointsMulEquiv base T g =
    Sp6GroupScheme.mapMatrix f.left.appTop.hom universalMatrix at hg
  have hx : pullbackPointsMap f.left 9 14 universalClass = pointClass x.left := by
    rw [universalClass, ← pointClass_comp]
    change pointClass ((f ≫ snd group overSpace).left) = pointClass x.left
    rw [show f ≫ snd group overSpace = x from lift_snd g x]
  have hn := transformPoints_natural f universalMatrix universalClass
  rw [← hg, hx] at hn
  change pointClass (f.left ≫ actionLeft) = _
  rw [pointClass_comp, actionLeft, classifying_class]
  exact hn

/-- The native group-scheme action, with its laws proved on every test scheme. -/
def nativeAction : (Sp6GroupScheme.groupScheme base).Action overSpace where
  act := action
  one_smul T x := by
    apply Over.OverMorphism.ext
    apply hom_ext
    · exact (lift (1 : T ⟶ group) x ≫ action).w.trans x.w.symm
    · rw [action_pointClass, Sp6GroupScheme.pointsMulEquiv_one, transformPoints_one]
  mul_smul T g h x := by
    apply Over.OverMorphism.ext
    apply hom_ext
    · exact (lift (g*h) x ≫ action).w.trans
        (lift g (lift h x ≫ action) ≫ action).w.symm
    · rw [action_pointClass, action_pointClass, action_pointClass,
        Sp6GroupScheme.pointsMulEquiv_mul]
      exact (transformPoints_mul T _ _ _).symm

theorem nativeAction_act : nativeAction.act = action := rfl

/-- The original constant symplectic transformations act through the exact scalar-extended
primitive matrix, with the quotient convention fixed by inverse precomposition. -/
theorem constant_action_pointClass (T : Over base) (h : M9.PrimitiveStabilizer.Sp6 ℂ)
    (x : T ⟶ overSpace) :
    pointClass ((lift (constantPointOn T h) x ≫ action).left) =
      transformPoints T (Sp6GroupScheme.mapMatrix (scalarMap T) (PrimitiveRingFieldBridge.fromOriginal h))
        (pointClass x.left) := by
  rw [action_pointClass, pointsMulEquiv_constantPointOn]

end M9Native.PrimitiveGrassmannianAction
