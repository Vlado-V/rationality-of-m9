module

public import M9StacksIntegration.PrimitiveGeometricQuotientField
public import M9StacksIntegration.StandaloneFunctionFieldRationalOpen

@[expose] public section

/-! Integration with a genuinely represented dense open of the actual
target presheaf. Both the actual native source map q and the actual dense
open j are retained. Construction of the coarse space, its classifier,
its dense schematic open and geometric orbit classification remain the
explicit geometric inputs of this theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

namespace M9Native.PrimitiveGeometricQuotientRationalOpen

open PrimitiveGrassmannianAction PrimitiveGeometricQuotientField
open StandaloneFunctionFieldRationalOpen

variable (U : space.Opens) [Nonempty U] (V : Variety ℂ)
    (q : U.toScheme ⟶ V.toScheme) [IsDominant q]
    (h : Geometry U V.structureMap q)

def originalOpen : M9StandaloneDraft.Schemes ℂ := Over.mk (U.ι ≫ projection)

def originalMap : originalOpen U ⟶ originalVariety ℂ V :=
  Over.homMk q h.over_base

/-- The actual candidate classifier is the literal composition of the
actual map q with the original dense-open target immersion j. -/
def classifier {M : M9StandaloneDraft.Presheaves ℂ}
    (j : yoneda.obj (originalVariety ℂ V) ⟶ M) :
    yoneda.obj (originalOpen U) ⟶ M :=
  yoneda.map (originalMap U V q h) ≫ j

omit [Nonempty U] [IsDominant q] in
/-- The classifier retains the actual map on every original test scheme. -/
theorem classifier_natural {M : M9StandaloneDraft.Presheaves ℂ}
    (j : yoneda.obj (originalVariety ℂ V) ⟶ M)
    {T : M9StandaloneDraft.Schemes ℂ} (x : T ⟶ originalOpen U) :
    yoneda.map x ≫ classifier U V q h j =
      yoneda.map (x ≫ originalMap U V q h) ≫ j := by
  rw [classifier, Functor.map_comp, Category.assoc]

include U q h in
/-- The actual map's geometric invariance and orbit-fiber criterion yield
a genuine common dense open of the actual target with affine24. The field
identity used by the strict native theorem is derived, not a hypothesis. -/
theorem rationalOpen {M : M9StandaloneDraft.Presheaves ℂ}
    (j : yoneda.obj (originalVariety ℂ V) ⟶ M)
    (hj : M9StandaloneDraft.DenseOpen ℂ j) :
    M9StandaloneDraft.RationalOpen ℂ 24 M := by
  have hV : M9StandaloneDraft.RationalOpen ℂ 24 (yoneda.obj (originalVariety ℂ V)) :=
    rationalOpen_of_structuralFunctionFieldEquiv ℂ 24 V
      ⟨PrimitiveGeometricQuotientField.rationalEquiv U V.structureMap q h⟩
  exact StandaloneRationalOpenComposition.rationalOpen_comp ℂ 24 j hj hV

end M9Native.PrimitiveGeometricQuotientRationalOpen
