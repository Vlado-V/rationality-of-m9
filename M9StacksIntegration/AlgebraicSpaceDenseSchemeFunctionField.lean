module

public import M9StacksIntegration.AlgebraicSpaceFunctionFieldScalars
public import M9StacksIntegration.NativeGenericFieldPoints

@[expose] public section

/-! The native rational-function ring of an integral algebraic space is
identified with the actual generic stalk of a represented dense open scheme.
The comparison is induced by the two actual monomorphic generic points;
its scalar compatibility is derived from their maps to the original base.
Integrality, the represented open and its density remain geometric inputs.
No moduli integrality or rationality is asserted here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
attribute [local instance] Space.pointTopology

namespace M9Native.AlgebraicSpaceDenseSchemeFunctionField

universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))
  {X : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of K)) hK X)
  (hInt : Space.IsIntegralSpace B (Spec (.of K)) hK X)
  (U : BigFppfOver B (Spec (.of K)) hK)

abbrev chartScheme : Scheme.{u} :=
  (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U

abbrev chartStructureMap : chartScheme K B hK U ⟶ Spec (.of K) :=
  B.inclusion.map U.hom

variable [IsIntegral (chartScheme K B hK U)]

/-- The generic stalk's spectrum belongs to the SAME actual site; this
bound is derived from the original chart, rather than supplied separately. -/
theorem contains_chartFunctionField :
    B.Contains (Spec (chartScheme K B hK U).functionField) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ U.left.property
    ((Scheme.mk_stalk_le_size _ (genericPoint (chartScheme K B hK U))).trans
      (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- The actual generic-stalk morphism, retained as a morphism of the site. -/
def chartGenericMap : B.obj (contains_chartFunctionField K B hK U) ⟶ U.left :=
  B.inclusion.preimage (NativeFunctionFieldFunctor.genericSpec (chartScheme K B hK U))

theorem chartGenericMap_scheme :
    B.inclusion.map (chartGenericMap K B hK U) =
      NativeFunctionFieldFunctor.genericSpec (chartScheme K B hK U) :=
  B.inclusion.map_preimage _

/-- The original function field itself represents the chart's generic point. -/
def chartGenericPoint : Space.FieldValuedPoint B (Spec (.of K)) hK (yoneda.obj U) where
  carrier := (chartScheme K B hK U).functionField
  contained := contains_chartFunctionField K B hK U
  toBase := B.inclusion.map (chartGenericMap K B hK U ≫ U.hom)
  value := Over.homMk (chartGenericMap K B hK U)

theorem chartGenericPoint_class :
    (chartGenericPoint K B hK U).class B (Spec (.of K)) hK (yoneda.obj U) =
      (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).symm
        (genericPoint (chartScheme K B hK U)) := by
  apply (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).injective
  rw [Homeomorph.apply_symm_apply, Space.schemePointsHomeomorph_apply,
    Space.pointsToScheme_class]
  change B.inclusion.map (chartGenericMap K B hK U)
    (IsLocalRing.closedPoint (chartScheme K B hK U).functionField) = _
  rw [chartGenericMap_scheme]
  exact Scheme.fromSpecStalk_closedPoint

variable (j : yoneda.obj U ⟶ X)

def imageGenericPoint : Space.FieldValuedPoint B (Spec (.of K)) hK X :=
  Space.FieldValuedPoint.map B (Spec (.of K)) hK (yoneda.obj U) j
    (chartGenericPoint K B hK U)

/-- Actual density carries the actual chart generic point to the native
generic point of the space. There is no supplied generic-point equality. -/
theorem imageGenericPoint_class
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) j)) :
    (imageGenericPoint K B hK U j).class B (Spec (.of K)) hK X =
      Space.genericPoint B (Spec (.of K)) hK hX hInt := by
  let := Space.t0Space_points_of_isDecentSpace B (Spec (.of K)) hK hX hInt.2.1
  have hc := (genericPoint_spec (chartScheme K B hK U)).image
    (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).symm.continuous
  rw [Set.image_univ,
    (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).symm.surjective.range_eq] at hc
  rw [closure_univ] at hc
  rw [← chartGenericPoint_class K B hK U] at hc
  have hi := hc.image (Space.continuous_pointsMap B (Spec (.of K)) hK j)
  rw [Set.image_univ, hd.closure_range] at hi
  exact (Space.isGenericPoint_genericPoint B (Spec (.of K)) hK hX hInt).eq hi |>.symm

/-- The generic point map is monomorphic because both the actual chart
inclusion and the actual generic-stalk morphism are monomorphic. -/
theorem imageGenericPoint_mono (hj : Space.IsOpenImmersion B (Spec (.of K)) hK j) :
    Mono (Space.fieldMorphism B (Spec (.of K)) hK X (imageGenericPoint K B hK U j)) := by
  have : Mono j := Space.mono_of_isOpenImmersion B (Spec (.of K)) hK j hj
  have : Mono (chartGenericMap K B hK U) :=
    B.inclusion.mono_of_mono_map (by
      rw [chartGenericMap_scheme]
      exact inferInstanceAs (Mono ((chartScheme K B hK U).fromSpecStalk
        (genericPoint (chartScheme K B hK U)))))
  have : Mono (chartGenericPoint K B hK U).value := by
    change Mono (Over.homMk (chartGenericMap K B hK U) :
      (chartGenericPoint K B hK U).siteObject B (Spec (.of K)) hK (yoneda.obj U) ⟶ U)
    exact (Over.forget _).mono_of_mono_map (by infer_instance)
  rw [imageGenericPoint, Space.fieldMorphism_map,
    Space.fieldMorphism_yoneda]
  infer_instance

variable (hj : Space.IsOpenImmersion B (Spec (.of K)) hK j)
  (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) j))

/-- The unique native generic-point comparison is obtained from the two
actual monomorphic representatives of the SAME generic point. -/
def genericPointIso :
    (Space.genericRep B (Spec (.of K)) hK hX hInt).siteObject B (Spec (.of K)) hK X ≅
      (imageGenericPoint K B hK U j).siteObject B (Spec (.of K)) hK X := by
  have := (Space.residueFieldRepresentative B (Spec (.of K)) hK X hInt.2.1
    (Space.genericPoint B (Spec (.of K)) hK hX hInt)).property.2
  have := imageGenericPoint_mono K B hK U j hj
  exact (Space.iso_of_mono_of_point_eq B (Spec (.of K)) hK X hX
    (Space.genericRep B (Spec (.of K)) hK hX hInt) (imageGenericPoint K B hK U j)
    ((Space.genericRep_class B (Spec (.of K)) hK hX hInt).trans
      (imageGenericPoint_class K B hK hX hInt U j hd).symm)).choose

/-- The derived comparison retains the actual generic classifier value. -/
theorem genericPointIso_value :
    X.map (genericPointIso K B hK hX hInt U j hj hd).hom.op
        (imageGenericPoint K B hK U j).value =
      (Space.genericRep B (Spec (.of K)) hK hX hInt).value := by
  have := (Space.residueFieldRepresentative B (Spec (.of K)) hK X hInt.2.1
    (Space.genericPoint B (Spec (.of K)) hK hX hInt)).property.2
  have := imageGenericPoint_mono K B hK U j hj
  exact (Space.iso_of_mono_of_point_eq B (Spec (.of K)) hK X hX
    (Space.genericRep B (Spec (.of K)) hK hX hInt) (imageGenericPoint K B hK U j)
    ((Space.genericRep_class B (Spec (.of K)) hK hX hInt).trans
      (imageGenericPoint_class K B hK hX hInt U j hd).symm)).choose_spec

/-- The inverse comparison followed by the native generic classifier is
the actual chart generic-stalk map followed by the original open map j. -/
theorem genericPointIso_inverse_classifier :
    yoneda.map (genericPointIso K B hK hX hInt U j hj hd).inv ≫
        Space.fieldMorphism B (Spec (.of K)) hK X
          (Space.genericRep B (Spec (.of K)) hK hX hInt) =
      yoneda.map (chartGenericPoint K B hK U).value ≫ j := by
  have hh : yoneda.map (genericPointIso K B hK hX hInt U j hj hd).hom ≫
        Space.fieldMorphism B (Spec (.of K)) hK X (imageGenericPoint K B hK U j) =
      Space.fieldMorphism B (Spec (.of K)) hK X
        (Space.genericRep B (Spec (.of K)) hK hX hInt) := by
    change yoneda.map _ ≫ yonedaEquiv.symm _ = yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left, genericPointIso_value K B hK hX hInt U j hj hd]
  have hi : yoneda.map (genericPointIso K B hK hX hInt U j hj hd).inv ≫
        Space.fieldMorphism B (Spec (.of K)) hK X
          (Space.genericRep B (Spec (.of K)) hK hX hInt) =
      Space.fieldMorphism B (Spec (.of K)) hK X (imageGenericPoint K B hK U j) := by
    rw [← hh, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      (yoneda (C := BigFppfOver B (Spec (.of K)) hK)).map_id, Category.id_comp]
  exact hi.trans (Space.fieldMorphism_map_yoneda B (Spec (.of K)) hK X j
    (chartGenericPoint K B hK U))

/-- The comparison of field spectra is induced by that actual native iso. -/
def genericSpectrumMap :
    Spec (chartScheme K B hK U).functionField ⟶
      Spec (.of (AlgebraicSpaceFunctionFieldScalars.genericResidueField K B hK hX hInt)) :=
  (BigFppfOver.toScheme B (Spec (.of K)) hK).map
    (genericPointIso K B hK hX hInt U j hj hd).inv

instance genericSpectrumMap_isIso :
    IsIso (genericSpectrumMap K B hK hX hInt U j hj hd) := by
  unfold genericSpectrumMap
  infer_instance

/-- The original structure morphism, not an independent scalar comparison,
is preserved by the actual generic spectrum map. -/
theorem genericSpectrumMap_over_base :
    genericSpectrumMap K B hK hX hInt U j hj hd ≫
        AlgebraicSpaceFunctionFieldScalars.genericStructureMap K B hK hX hInt =
      Spec.map (CommRingCat.ofHom
        (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U))) := by
  have hw := congrArg B.inclusion.map
    (Over.w (genericPointIso K B hK hX hInt U j hj hd).inv)
  rw [Functor.map_comp] at hw
  change genericSpectrumMap K B hK hX hInt U j hj hd ≫
    AlgebraicSpaceFunctionFieldScalars.genericStructureMap K B hK hX hInt =
      B.inclusion.map (chartGenericMap K B hK U ≫ U.hom) at hw
  rw [hw, Functor.map_comp, chartGenericMap_scheme]
  exact NativeGenericFieldPoints.genericSpec_structure K (chartStructureMap K B hK U)

/-- Native rational functions evaluated in the actual chart generic stalk.
Both coefficient structures come from their original structural morphisms. -/
def functionFieldAlgHom :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    Space.rationalFunctions B (Spec (.of K)) hK hX →ₐ[K]
      (chartScheme K B hK U).functionField := by
  letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
  letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
  exact AlgebraicSpaceFunctionFieldScalars.genericEvaluationAlgHom K B hK hX hInt
    (chartScheme K B hK U).functionField
    (genericSpectrumMap K B hK hX hInt U j hj hd)
    (genericSpectrumMap_over_base K B hK hX hInt U j hj hd)

theorem functionFieldAlgHom_bijective :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    Function.Bijective (functionFieldAlgHom K B hK hX hInt U j hj hd) := by
  let q := genericSpectrumMap K B hK hX hInt U j hj hd
  have : IsIso (Scheme.Spec.map (Spec.preimage q).op) := by
    change IsIso (Spec.map (Spec.preimage q))
    rw [Spec.map_preimage]
    exact genericSpectrumMap_isIso K B hK hX hInt U j hj hd
  have : IsIso (Spec.preimage q) :=
    (isIso_op_iff _).mp
      ((Functor.FullyFaithful.ofFullyFaithful Scheme.Spec).isIso_of_isIso_map _)
  exact (ConcreteCategory.bijective_of_isIso (Spec.preimage q)).comp
    (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt).bijective

/-- The actual native rational-function ring and the actual dense chart
generic stalk are isomorphic over the original field. -/
def functionFieldAlgEquiv :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    Space.rationalFunctions B (Spec (.of K)) hK hX ≃ₐ[K]
      (chartScheme K B hK U).functionField := by
  letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
  letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
  exact AlgEquiv.ofBijective (functionFieldAlgHom K B hK hX hInt U j hj hd)
    (functionFieldAlgHom_bijective K B hK hX hInt U j hj hd)

/-- The comparison is the native rational-function evaluation along the
derived actual generic-spectrum map. -/
theorem functionFieldAlgEquiv_apply
    (f : Space.rationalFunctions B (Spec (.of K)) hK hX) :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    functionFieldAlgEquiv K B hK hX hInt U j hj hd f =
      (Spec.preimage (genericSpectrumMap K B hK hX hInt U j hj hd)).hom
        (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt f) := rfl

/-- The original structural coefficient inclusion is preserved. -/
theorem functionFieldAlgEquiv_coefficient (c : K) :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    functionFieldAlgEquiv K B hK hX hInt U j hj hd
        (AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap K B hK hX hInt c) =
      GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U) c := by
  let := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
  let := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
  exact (functionFieldAlgEquiv K B hK hX hInt U j hj hd).commutes c

/-- The inverse retains the same original structural coefficient map. -/
theorem functionFieldAlgEquiv_inverse_coefficient (c : K) :
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
    (functionFieldAlgEquiv K B hK hX hInt U j hj hd).symm
        (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U) c) =
      AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap K B hK hX hInt c := by
  let := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra K B hK hX hInt
  let := (GrassmannianCharts.structureScalarMap K (chartStructureMap K B hK U)).toAlgebra
  exact (functionFieldAlgEquiv K B hK hX hInt U j hj hd).symm.commutes c

end M9Native.AlgebraicSpaceDenseSchemeFunctionField
