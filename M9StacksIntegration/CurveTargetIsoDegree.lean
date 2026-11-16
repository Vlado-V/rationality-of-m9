module

public import M9StacksIntegration.PencilDegreePullback
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant

/-! Actual target-isomorphism transport of curves, nonconstancy and native field degree. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CurveTargetIsoDegree

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
  (e : Y ≅ Z) (he : e.hom ≫ pZ = pY)

include he in
/-- The actual source model is a curve by its genuine isomorphism over the original field. -/
theorem isCurve [IsCurve k pZ] : IsCurve k pY := by
  have : IsIntegral Y := IsIntegral.of_isIso e.inv
  have : IsSeparated pY := by rw [← he]; infer_instance
  have : LocallyOfFiniteType pY := by rw [← he]; infer_instance
  have : QuasiCompact pY := by rw [← he]; infer_instance
  have hv : IsVariety k pY := IsVariety.mk
  refine (isCurve_iff k pY).mpr ⟨hv, ?_⟩
  exact (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq e.hom).trans
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := pZ))

/-- The original nonconstant map remains nonconstant under the actual target isomorphism. -/
theorem nonconstant_comp (g : X ⟶ Y)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    ¬ ∃ z : Z, ∀ x : X, (g ≫ e.hom).base x = z := by
  rintro ⟨z, hz⟩
  apply hnc
  refine ⟨e.inv z, fun x => ?_⟩
  have hx : e.hom (g x) = z := hz x
  have hi : e.inv (e.hom (g x)) = g x := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  exact hi.symm.trans (congrArg e.inv hx)

include he in
/-- Both are the actual native function-field degree, with equality derived
from the genuine target isomorphism rather than a supplied degree comparison. -/
theorem curveMapDegree_comp_iso (pX : X ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsCurve k pZ]
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    PencilDegreePullback.curveMapDegree pX pZ (g ≫ e.hom)
      (by rw [Category.assoc, he, hg]) (nonconstant_comp e g hnc) =
        PencilDegreePullback.curveMapDegree pX pY g hg hnc := by
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_isCurve_comp k pX pY g hg
  have : IsDominant g := isDominant_of_not_constant k pX pY g hnc
  have hc : (g ≫ e.hom) ≫ pZ = pX := by rw [Category.assoc, he, hg]
  have : LocallyOfFiniteType (g ≫ e.hom) :=
    locallyOfFiniteType_of_isCurve_comp k pX pZ _ hc
  have : IsDominant (g ≫ e.hom) :=
    isDominant_of_not_constant k pX pZ _ (nonconstant_comp e g hnc)
  change degreeOver (g ≫ e.hom) = degreeOver g
  exact degreeOver_eq_degreeOver_of_isIso (g ≫ e.hom) g e.hom rfl

end M9Native.CurveTargetIsoDegree
