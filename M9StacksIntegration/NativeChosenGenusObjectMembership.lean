module

public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier

/-! Original field curves extracted from the actual chosen smooth-genus
source. Membership follows from the actual open-substack object and the
hom-shrink counit. The field scheme model and its bounded native map are
constructed from that membership with the original coefficient retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.NativeGenusNineFieldObjectCurve

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

section AllBases
variable (g : ℕ) (hg : 2 ≤ g)
  (x : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj)

/-- The actual open-substack property gives cohomological genus on the
same recovered original family, over every native base. -/
theorem originalProjection_cohomological :
    IsSmoothH0Family B hZ
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x) ∧
    CurveFamily.HasGenus B hZ
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x) g := by
  let y := (StackChangeOfBaseClassifier.originalProjection B (Spec (.of K)) integerBase
    hK hZ (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg)).obj x
  let F := (curvesSmallEquivalenceOver B hZ).inv.functor.obj y.obj
  have hy : (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property y.obj :=
    y.property
  let : (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property.IsClosedUnderIsomorphisms :=
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).strictlyFull
  have hr : (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property
      ((curvesSmallEquivalenceOver B hZ).hom.functor.obj F) :=
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property.prop_of_iso
      ((curvesSmallEquivalenceOver B hZ).counitIso.app y.obj).symm hy
  exact (curvesSmallOpenSubstack_property_iff B hZ
    (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2) F).mp hr

/-- ANY actual chosen smooth-genus object has the true original
field-fibre genus property. No native membership is supplied. -/
theorem originalProjection_membership :
    IsSmoothH0FamilyOfFibreGenus B hZ g
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x) := by
  have h := originalProjection_cohomological B hZ K hK g hg x
  let F := (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x
  exact ⟨h.1,
    (F.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
        (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions
          h.1.2) g).mpr h.2⟩
end AllBases

abbrev source := M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)
abbrev rawProjection := NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK 9 (by decide)

variable (L : Type u) [Field L] (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)

/-- The actual native field object with its specified original coefficient. -/
abbrev fieldBase : BigFppfOver B (Spec (.of K)) hK :=
  siteObject B (Spec (.of K)) hK hL (Spec.map (CommRingCat.ofHom coefficient))

abbrev integerFieldBase : BigFppfOver B integerBase hZ :=
  (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
    (fieldBase B K hK L hL coefficient)

/-- The coefficient triangle has the actual original integer-field base. -/
theorem integerFieldBase_eq :
    integerFieldBase B hZ K hK L hL coefficient = integerSiteObject B hZ hL := by
  refine CostructuredArrow.obj_ext
    (integerFieldBase B hZ K hK L hL coefficient) (integerSiteObject B hZ hL) rfl ?_
  simp only [eqToHom_refl, Functor.map_id, Category.id_comp]
  apply B.inclusion.map_injective
  exact specULiftZIsTerminal.hom_ext _ _

variable (z : (source B hZ K hK).val.val.obj)
  (hz : (source B hZ K hK).val.val.p.obj z = fieldBase B K hK L hL coefficient)

include hz in
theorem rawFamily_base :
    ((rawProjection B hZ K hK).obj z).base = integerFieldBase B hZ K hK L hL coefficient :=
  (Functor.congr_obj
    (NativeSmoothGenusCoarseClassifier.originalProjection_comp B hZ K hK 9 (by decide)) z).trans
    (congrArg (fun V => (Over.map
      (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V) hz)

include hz in
theorem rawFamily_integerBase :
    ((rawProjection B hZ K hK).obj z).base = integerSiteObject B hZ hL :=
  (rawFamily_base B hZ K hK L hL coefficient z hz).trans
    (integerFieldBase_eq B hZ K hK L hL coefficient)


end M9Native.NativeGenusNineFieldObjectCurve
end
