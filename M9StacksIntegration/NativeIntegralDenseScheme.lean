module

public import M9StacksIntegration.NativeDenseSchematicOriginal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding

/-!
# Actual integrality of a represented dense open in an integral native space

Reducedness is obtained from the actual reduced native atlas by a true
represented etale pullback and flat descent. Irreducibility and nonemptiness
use the actual native point map and its genuine scheme-point homeomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.NativeIntegralDenseScheme
attribute [local instance] Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual native open predicate gives actual represented etaleness. -/
theorem etale_of_open
    {X : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X)
    (ha : Space.IsOpenImmersion B (Spec (.of K)) hK a) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf a := by
  apply MorphismProperty.relative_monotone (F := yoneda) (P :=
    MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)) (P' :=
    MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)) _ _ ha
  intro V W f hf
  haveI : IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of K)) hK).map f) := hf
  change Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map f)
  infer_instance

/-- Actual native reducedness forces reducedness of every actual etale
representing scheme, by the literal scheme pullback of its reduced atlas. -/
theorem scheme_isReduced_of_etale
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK X.obj
      (fun T : Scheme.{u} => IsReduced T))
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf a) :
    IsReduced ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) := by
  obtain ⟨V, b, hbs, hbe, hV⟩ := hr
  let R := hbe.rep.pullback a
  let r : R ⟶ V := hbe.rep.fst' a
  let s : R ⟶ U := hbe.rep.snd a
  have hp : IsPullback (yoneda.map r) (yoneda.map s) b a := hbe.rep.isPullback' a
  haveI : IsReduced ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V) := hV
  haveI : Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r) :=
    he.property b (yoneda.map s) r hp.flip
  haveI : IsReduced ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj R) :=
    AlgebraicGeometry.isReduced_of_etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r)
  haveI : Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map s) :=
    hbe.property_snd a
  haveI : Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map s) :=
    hbs.property_snd a
  exact AlgebraicGeometry.isReduced_of_flat_of_surjective
    ((BigFppfOver.toScheme B (Spec (.of K)) hK).map s)

/-- A genuinely dense native open in an irreducible native point space
has an irreducible actual representing scheme, including nonemptiness. -/
theorem scheme_irreducible_of_dense_open
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hi : IrreducibleSpace (Space.points B (Spec (.of K)) hK X.obj))
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj)
    (ha : Space.IsOpenImmersion B (Spec (.of K)) hK a)
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a)) :
    IrreducibleSpace ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) := by
  letI := hi
  haveI : Mono a := Space.mono_of_isOpenImmersion B (Spec (.of K)) hK a ha
  have he : Topology.IsOpenEmbedding
      (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (Space.continuous_pointsMap B (Spec (.of K)) hK a)
      (Space.pointsMap_injective_of_mono B (Spec (.of K)) hK a)
      (Space.isOpenMap_pointsMap_of_isOpenImmersion B (Spec (.of K)) hK a ha)
  haveI : Nonempty (Space.points B (Spec (.of K)) hK (yoneda.obj U)) :=
    hd.nonempty_iff.mpr inferInstance
  haveI : IrreducibleSpace (Space.points B (Spec (.of K)) hK (yoneda.obj U)) :=
    he.irreducibleSpace
  exact (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).irreducibleSpace_iff.mp
    inferInstance

/-- Native reducedness and genuine point irreducibility imply integrality
of the SAME actual representing scheme of a dense open. -/
theorem scheme_isIntegral_of_dense_open
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK X.obj
      (fun T : Scheme.{u} => IsReduced T))
    (hi : IrreducibleSpace (Space.points B (Spec (.of K)) hK X.obj))
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj)
    (ha : Space.IsOpenImmersion B (Spec (.of K)) hK a)
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a)) :
    IsIntegral ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) := by
  haveI := scheme_isReduced_of_etale K B hK X hr U a (etale_of_open K B hK U a ha)
  haveI := scheme_irreducible_of_dense_open K B hK X hi U a ha hd
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The native integral-space predicate produces a genuinely integral
scheme dense open; neither the scheme nor its integrality is assumed. -/
theorem exists_native_integral_dense_scheme
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hI : Space.IsIntegralSpace B (Spec (.of K)) hK X.obj) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj),
      Space.IsOpenImmersion B (Spec (.of K)) hK a ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a) ∧
      IsIntegral ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) := by
  obtain ⟨U, a, ha, hd⟩ :=
    NativeDenseSchematicOriginal.exists_native_dense_scheme K B hK X hI.2.1
  exact ⟨U, a, ha, hd, scheme_isIntegral_of_dense_open K B hK X hI.1 hI.2.2 U a ha hd⟩

end M9StacksIntegration.NativeIntegralDenseScheme
