module

public import M9StacksIntegration.CurveTargetIsoDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound

/-!
# Actual source-isomorphism transport for curve covers

The degree is the original native degree of the extension of function
fields. Its invariance is proved from the actual function-field map of
the source isomorphism and the functoriality of those maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CurveSourceIsoDegree

variable {A B Y : Scheme.{u}}

/-- Precomposing with a genuine source isomorphism preserves nonconstancy. -/
theorem nonconstant_precomp (e : A ≅ B) (g : B ⟶ Y)
    (hnc : ¬ ∃ y : Y, ∀ b : B, g.base b = y) :
    ¬ ∃ y : Y, ∀ a : A, (e.hom ≫ g).base a = y := by
  rintro ⟨y, hy⟩
  apply hnc
  refine ⟨y, fun b => ?_⟩
  have hb : g (e.hom (e.inv b)) = y := hy (e.inv b)
  have hi : e.hom (e.inv b) = b := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  exact (congrArg g hi).symm.trans hb

/-- The actual native degree is unchanged by a genuine source isomorphism.
The two extension structures are compared, rather than identified by a premise. -/
theorem degreeOver_precomp_iso (e : A ≅ B) (g : B ⟶ Y)
    [IsIntegral A] [IsIntegral B] [IsIntegral Y]
    [LocallyOfFiniteType g] [IsDominant g] :
    degreeOver (e.hom ≫ g) = degreeOver g := by
  have : IsDominant e.hom := (isDominant_iff e.hom).mpr
    (Function.Surjective.denseRange e.hom.homeomorph.surjective)
  let : Algebra Y.functionField B.functionField :=
    (dominantFunctionFieldMap g).toAlgebra
  let : Algebra Y.functionField A.functionField :=
    (dominantFunctionFieldMap (e.hom ≫ g)).toAlgebra
  rw [degreeOver_eq_finrank (e.hom ≫ g) rfl, degreeOver_eq_finrank g rfl]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl Y.functionField)
    (RingEquiv.ofBijective (dominantFunctionFieldMap e.hom)
      (bijective_dominantFunctionFieldMap_of_isIso e.hom)) ?_
  exact Stacks.Chow.dominantFunctionFieldMap_comp e.hom g

variable {k : Type u} [Field k]
  (pA : A ⟶ Spec (.of k)) (pB : B ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) (e : A ≅ B) (he : e.hom ≫ pB = pA)

include he in
/-- The native curve-map degree, including its original field triangles,
is unchanged under the actual source comparison. -/
theorem curveMapDegree_precomp_iso [IsCurve k pA] [IsCurve k pB] [IsCurve k pY]
    (g : B ⟶ Y) (hg : g ≫ pY = pB)
    (hnc : ¬ ∃ y : Y, ∀ b : B, g.base b = y) :
    PencilDegreePullback.curveMapDegree pA pY (e.hom ≫ g)
      (by rw [Category.assoc, hg, he]) (nonconstant_precomp e g hnc) =
        PencilDegreePullback.curveMapDegree pB pY g hg hnc := by
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_isCurve_comp k pB pY g hg
  have : IsDominant g := isDominant_of_not_constant k pB pY g hnc
  change degreeOver (e.hom ≫ g) = degreeOver g
  exact degreeOver_precomp_iso e g

include he in
/-- Genus is transported through the genuine source isomorphism over the
same original field. -/
theorem genus_eq [IsProper pB] : genus pA = genus pB := by
  rw [← he]
  exact genus_comp_iso_eq k pB e

end M9Native.CurveSourceIsoDegree
