module

public import M9StacksIntegration.CurveFieldClassifierH1
public import M9StacksIntegration.CurveFieldClassifierSmooth
public import M9StacksIntegration.SliceTangentArrowCoordinates
public import M9StacksIntegration.SliceChartPointIsomorphism
public import M9StacksIntegration.ParameterStructuralResidue
public import M9StacksIntegration.ParameterTangentH1

/-!
# The original parameter-family H1 map of a smooth classifying family

The differential is the actual native chart differential. Its value on a
represented square-zero test is proved equal to the SAME pre-existing
ParameterTangentH1 map of the original pulled scheme family. Native smooth
lifting therefore gives surjectivity of that map. At a closed point over
an algebraically closed ground field, its structural residue map is the
proved isomorphism, with no identification of the residue field and the
ground field.

Smoothness is a property of the genuinely constructed classifying stack
morphism of the specified scheme family. This does not assert that an
arbitrary atlas has a schematic universal total space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Artin.SliceTangent Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local instance] M9Native.ParameterTangentH1.residueTangentModule

universe u
namespace M9Native.CurveAtlasTangentH1

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K)) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

variable (hk : B.Contains (Spec (.of (IsLocalRing.ResidueField (T.presheaf.stalk x)))))
  [IsCurve (IsLocalRing.ResidueField (T.presheaf.stalk x))
    (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom]

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p
local instance fibreProper :
    IsProper (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom :=
  inferInstanceAs (IsProper (pullback.snd p (T.fromSpecResidueField x)))
local instance fibreSmooth :
    Smooth (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom :=
  inferInstanceAs (Smooth (pullback.snd p (T.fromSpecResidueField x)))

local instance parameterFibreProper : IsProper (ParameterTangentDeformation.fibre p x).hom :=
  inferInstanceAs (IsProper (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom)
local instance parameterFibreSmooth : Smooth (ParameterTangentDeformation.fibre p x).hom :=
  inferInstanceAs (Smooth (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom)
local instance parameterFibreCurve : IsCurve κ (ParameterTangentDeformation.fibre p x).hom :=
  inferInstanceAs (IsCurve κ (ParameterFamilyDeformation.fibre p (T.fromSpecResidueField x)).hom)

open CurveFieldClassifierPullback CurveFieldClassifierDeformation

abbrev parameter := parameterDeformations B hZ hK hX hT p s hk (T.fromSpecResidueField x)

/-- The actual native chart map of a marked test in its original coefficient fibre. -/
abbrev testMap (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :=
  chartPointMap z.val z.property

/-- The actual marked test has the original residue triangle. -/
theorem testMap_residue (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    residueSpecMap (coordBase (Λ := κ) W) ≫ testMap B hZ hK hX hT p s x hk W z =
      T.fromSpecResidueField x :=
  (residue_chartPointMap z.val z.property).trans
    (parameterPoint_map B hZ hK hX hT p s hk (T.fromSpecResidueField x))

/-- The structural triangle uses the genuine residue-to-ground map. -/
theorem testMap_ground (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    testMap B hZ hK hX hT p s x hk W z ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap κ (coordBase (Λ := κ) W))) ≫
        (T.fromSpecResidueField x ≫ s) :=
  chartPointMap_comp z.val z.property

/-- The literal native represented test of that SAME original chart map. -/
def canonicalTest (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W) :=
  ⟨parameterTest B hZ hK hX hT p s hk (T.fromSpecResidueField x)
    (coordBase (Λ := κ) W) (testMap B hZ hK hX hT p s x hk W z)
    (testMap_residue B hZ hK hX hT p s x hk W z)
    (testMap_ground B hZ hK hX hT p s x hk W z), rfl⟩

/-- It has exactly the original chart map, rather than a classifying-map premise. -/
theorem testMap_canonicalTest (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    testMap B hZ hK hX hT p s x hk W (canonicalTest B hZ hK hX hT p s x hk W z) =
      testMap B hZ hK hX hT p s x hk W z := by
  change SliceTangent.chartPointMap
    (parameterTest B hZ hK hX hT p s hk (T.fromSpecResidueField x)
      (coordBase (Λ := κ) W) (testMap B hZ hK hX hT p s x hk W z)
      (testMap_residue B hZ hK hX hT p s x hk W z)
      (testMap_ground B hZ hK hX hT p s x hk W z)) rfl = _
  rw [SliceTangent.chartPointMap, eqToHom_refl, specMap_id, Category.id_comp]
  exact parameterTest_map B hZ hK hX hT p s hk (T.fromSpecResidueField x)
    (coordBase (Λ := κ) W) (testMap B hZ hK hX hT p s x hk W z)
    (testMap_residue B hZ hK hX hT p s x hk W z)
    (testMap_ground B hZ hK hX hT p s x hk W z)

/-- Hence the native tests are genuinely isomorphic in the SAME Artinian fibre. -/
def canonicalTestIso (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    z ≅ canonicalTest B hZ hK hX hT p s x hk W z :=
  SliceChartPointIsomorphism.isoOfChartPointMapEq z
    (canonicalTest B hZ hK hX hT p s x hk W z)
    (testMap_canonicalTest B hZ hK hX hT p s x hk W z).symm

/-- The actual dotted tangent arrow furnished by the original square-zero coordinates. -/
def tangentArrow
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber
      (coordBase (Λ := κ) (FGModuleCat.of κ κ))) : DottedTangentArrow s x :=
  SliceTangentArrowCoordinates.tangentArrow
    (B := B) (S := Spec (.of K)) (hS := hK)
    (V := base B hZ hK hX hT p s)
    (iΛ := T.fromSpecResidueField x ≫ s)
    (v₀ := parameterPoint B hZ hK hX hT p s hk (T.fromSpecResidueField x))
    (hv₀ := parameterPoint_base B hZ hK hX hT p s hk (T.fromSpecResidueField x)) x
    (parameterPoint_map B hZ hK hX hT p s hk (T.fromSpecResidueField x)) rfl z

/-- The actual coordinate map of this dotted arrow is precisely the original native test map. -/
theorem tangentArrow_toSpec
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber
      (coordBase (Λ := κ) (FGModuleCat.of κ κ))) :
    NativeSquareZeroCoordinates.toSpec κ (FGModuleCat.of κ κ) ≫
        (tangentArrow B hZ hK hX hT p s x hk z).val =
      testMap B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z :=
  SliceTangentArrowCoordinates.toSpec_tangentArrow
    (B := B) (S := Spec (.of K)) (hS := hK)
    (V := base B hZ hK hX hT p s)
    (iΛ := T.fromSpecResidueField x ≫ s)
    (v₀ := parameterPoint B hZ hK hX hT p s hk (T.fromSpecResidueField x))
    (hv₀ := parameterPoint_base B hZ hK hX hT p s hk (T.fromSpecResidueField x)) x
    (parameterPoint_map B hZ hK hX hT p s hk (T.fromSpecResidueField x)) rfl z

/-- Its original family class is the SAME literal pulled-family class of the native test. -/
theorem sourceClass_eq_parameterTangent
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber
      (coordBase (Λ := κ) (FGModuleCat.of κ κ))) :
    tangentClassAt.{u,u,u}
      (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection
        (ParameterTangentDeformation.fibre p x)) (FGModuleCat.of κ κ)
      (ParameterFamilyDeformation.fibreObject p (T.fromSpecResidueField x)
        (coordBase (Λ := κ) (FGModuleCat.of κ κ))
        (testMap B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z)
        (testMap_residue B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z)) =
    ParameterTangentDeformation.tangentLinearMap p s x
      (tangentArrow B hZ hK hX hT p s x hk z) := by
  change ParameterTangentDeformation.coordinateClass p x (FGModuleCat.of κ κ)
      ⟨testMap B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z,
        testMap_residue B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z⟩ =
    ParameterTangentDeformation.coordinateClass p x (FGModuleCat.of κ κ)
      (ParameterTangentDeformation.tangentArrow s x
        (tangentArrow B hZ hK hX hT p s x hk z))
  exact congrArg (ParameterTangentDeformation.coordinateClass p x (FGModuleCat.of κ κ))
    (Subtype.ext (tangentArrow_toSpec B hZ hK hX hT p s x hk z).symm)

variable (hfinite : LocallyOfFiniteType (T.fromSpecResidueField x ≫ s))
  (hqc : QuasiCompact (T.fromSpecResidueField x ≫ s))

/-- The genuine differential class equals the actual original scheme class
under the constructed target equivalence, for all finite coefficients. -/
theorem derivative_class_compare (W : FGModuleCat.{u} κ)
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber (coordBase (Λ := κ) W)) :
    CurveFieldClassifierSmooth.derivative B hZ hK hAlg hX hT p s hk
        (T.fromSpecResidueField x) hfinite hqc W
      (tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (parameter B hZ hK hX hT p s x hk).projection)
        (CurveFieldClassifierSmooth.sourceStructure B hZ hK hX hT p s hk
          (T.fromSpecResidueField x) hfinite hqc) W z) =
    CurveFieldTargetTangent.tangentEquivalence B hZ hK hAlg hk
      (T.fromSpecResidueField x ≫ s) (ParameterTangentDeformation.fibre p x).hom
      hfinite hqc W
      (tangentClassAt.{u,u,u}
        (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
        (isDeformationCategory_schemeDeformationCategoryProjection
          (ParameterTangentDeformation.fibre p x)) W
        (ParameterFamilyDeformation.fibreObject p (T.fromSpecResidueField x)
          (coordBase (Λ := κ) W) (testMap B hZ hK hX hT p s x hk W z)
          (testMap_residue B hZ hK hX hT p s x hk W z))) := by
  have hz := (tangentClassAt_eq_iff.{u,u,u}
    (BasedCategory.ofFunctor (parameter B hZ hK hX hT p s x hk).projection)
    (CurveFieldClassifierSmooth.sourceStructure B hZ hK hX hT p s hk
      (T.fromSpecResidueField x) hfinite hqc) W z
      (canonicalTest B hZ hK hX hT p s x hk W z)).mpr
    ⟨canonicalTestIso B hZ hK hX hT p s x hk W z⟩
  have hd := CurveFieldClassifierSmooth.derivative_class B hZ hK hAlg hX hT p s hk
    (T.fromSpecResidueField x) hfinite hqc W
    (canonicalTest B hZ hK hX hT p s x hk W z)
  have hc := CurveFieldClassifierH1.classified_tangent_class B hZ hK hAlg p s hk
    (T.fromSpecResidueField x) hfinite hqc W hX hT
    (testMap B hZ hK hX hT p s x hk W z)
    (testMap_residue B hZ hK hX hT p s x hk W z)
    (testMap_ground B hZ hK hX hT p s x hk W z)
  exact (congrArg (CurveFieldClassifierSmooth.derivative B hZ hK hAlg hX hT p s hk
    (T.fromSpecResidueField x) hfinite hqc W) hz).trans (hd.trans hc)

/-- The proved H1 coordinates on the ACTUAL field-stack tangent. -/
abbrev targetH1 := CurveFieldTargetTangent.unliftedTangentLinearEquivH1 B hZ hK hAlg hk
  (T.fromSpecResidueField x ≫ s) (ParameterTangentDeformation.fibre p x).hom hfinite hqc

set_option maxRecDepth 4096 in
/-- The derivative on every genuine represented rank-one test is the SAME
pre-existing ParameterTangentH1 map, including the actual coefficient Iso. -/
theorem tangentH1_derivative_class
    (z : (parameter B hZ hK hX hT p s x hk).projection.Fiber
      (coordBase (Λ := κ) (FGModuleCat.of κ κ))) :
    ParameterTangentH1.tangentH1LinearMap p s x (tangentArrow B hZ hK hX hT p s x hk z) =
      targetH1 B hZ hK hAlg p s x hk hfinite hqc
        (CurveFieldClassifierSmooth.derivative B hZ hK hAlg hX hT p s hk
          (T.fromSpecResidueField x) hfinite hqc (FGModuleCat.of κ κ)
          (tangentClassAt.{u,u,u}
            (BasedCategory.ofFunctor (parameter B hZ hK hX hT p s x hk).projection)
            (CurveFieldClassifierSmooth.sourceStructure B hZ hK hX hT p s hk
              (T.fromSpecResidueField x) hfinite hqc) (FGModuleCat.of κ κ) z)) := by
  symm
  have hd := derivative_class_compare B hZ hK hAlg hX hT p s x hk hfinite hqc
    (FGModuleCat.of κ κ) z
  have hc := sourceClass_eq_parameterTangent B hZ hK hX hT p s x hk z
  let E := targetH1 B hZ hK hAlg p s x hk hfinite hqc
  let v := tangentClassAt.{u,u,u}
    (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
    (isDeformationCategory_schemeDeformationCategoryProjection
      (ParameterTangentDeformation.fibre p x)) (FGModuleCat.of κ κ)
    (ParameterFamilyDeformation.fibreObject p (T.fromSpecResidueField x)
      (coordBase (Λ := κ) (FGModuleCat.of κ κ))
      (testMap B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z)
      (testMap_residue B hZ hK hX hT p s x hk (FGModuleCat.of κ κ) z))
  calc
    _ = E (CurveFieldTargetTangent.tangentEquivalence B hZ hK hAlg hk
        (T.fromSpecResidueField x ≫ s) (ParameterTangentDeformation.fibre p x).hom
        hfinite hqc (FGModuleCat.of κ κ) v) := congrArg E hd
    _ = StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
        (ParameterTangentDeformation.fibre p x).hom
        (tangentModuleMapAt (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (ParameterTangentDeformation.fibre p x)) (fgModuleCatULiftSelfIso (k := κ)).inv v) :=
      CurveFieldTargetTangent.unliftedTangentLinearEquivH1_comparison B hZ hK hAlg hk
        (T.fromSpecResidueField x ≫ s) (ParameterTangentDeformation.fibre p x).hom
        hfinite hqc v
    _ = _ := congrArg
      (fun w => StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
        (ParameterTangentDeformation.fibre p x).hom
        (tangentModuleMapAt (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (ParameterTangentDeformation.fibre p x)) (fgModuleCatULiftSelfIso (k := κ)).inv w)) hc

include hk hfinite hqc in
/-- Actual smooth lifting gives surjectivity of the SAME original
parameter-family H1 map. No KS comparison or surjectivity premise is supplied. -/
theorem tangentH1_surjective_of_smooth
    (hOpen : IsOpenImmersion (T.fromSpecResidueField x ≫ s))
    (hsm : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (originalFamily B hZ hX hT p) s)) :
    Function.Surjective (ParameterTangentH1.tangentH1LinearMap p s x) := by
  have := hOpen
  intro y
  let E := targetH1 B hZ hK hAlg p s x hk hfinite hqc
  obtain ⟨v, hv⟩ := E.surjective y
  obtain ⟨u, hu⟩ := CurveFieldClassifierSmooth.derivative_surjective B hZ hK hAlg hX hT p s hk
    (T.fromSpecResidueField x) hfinite hqc hsm (FGModuleCat.of κ κ) v
  obtain ⟨z, hz⟩ := tangentClassAt_surjective.{u,u,u}
    (BasedCategory.ofFunctor (parameter B hZ hK hX hT p s x hk).projection)
    (CurveFieldClassifierSmooth.sourceStructure B hZ hK hX hT p s hk
      (T.fromSpecResidueField x) hfinite hqc) (FGModuleCat.of κ κ) u
  refine ⟨tangentArrow B hZ hK hX hT p s x hk z, ?_⟩
  calc
    _ = E (CurveFieldClassifierSmooth.derivative B hZ hK hAlg hX hT p s hk
        (T.fromSpecResidueField x) hfinite hqc (FGModuleCat.of κ κ)
        (tangentClassAt.{u,u,u}
          (BasedCategory.ofFunctor (parameter B hZ hK hX hT p s x hk).projection)
          (CurveFieldClassifierSmooth.sourceStructure B hZ hK hX hT p s hk
            (T.fromSpecResidueField x) hfinite hqc) (FGModuleCat.of κ κ) z)) :=
      tangentH1_derivative_class B hZ hK hAlg hX hT p s x hk hfinite hqc z
    _ = E v := by rw [hz, hu]
    _ = y := hv

include hk in
/-- At a closed point over an algebraically closed ground field, all
relative Artin-point hypotheses follow from the ACTUAL residue isomorphism. -/
theorem tangentH1_surjective_of_closed [IsAlgClosed K] [LocallyOfFiniteType s]
    (hx : IsClosed ({x} : Set T))
    (hsm : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg
        (originalFamily B hZ hX hT p) s)) :
    Function.Surjective (ParameterTangentH1.tangentH1LinearMap p s x) := by
  obtain ⟨hf, hq⟩ := ParameterStructuralResidue.structuralPoint_finite K s x hx
  exact tangentH1_surjective_of_smooth B hZ hK hAlg hX hT p s x hk hf hq
    (ParameterStructuralResidue.structuralPoint_isOpenImmersion K s x hx) hsm

set_option maxRecDepth 4096 in
/-- Equality under the SAME original H1 map means a genuine isomorphism
of the two actual pulled families over the identity of the coefficient algebra. -/
theorem parameterH1_eq_iff_liftedFamilyIso (θ η : DottedTangentArrow s x) :
    ParameterTangentH1.tangentH1LinearMap p s x θ =
      ParameterTangentH1.tangentH1LinearMap p s x η ↔
    IsIsomorphic (ParameterTangentH1.liftedObject p s x θ)
      (ParameterTangentH1.liftedObject p s x η) := by
  let E := StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := κ)
    (ParameterTangentDeformation.fibre p x).hom
  have hθ := ParameterTangentH1.tangentH1LinearMap_apply p s x θ
  have hη := ParameterTangentH1.tangentH1LinearMap_apply p s x η
  constructor
  · intro h
    apply (tangentClassAt_eq_iff.{u,u,u}
      (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection
        (ParameterTangentDeformation.fibre p x)) (FGModuleCat.of κ (ULift.{u} κ)) _ _).mp
    exact E.injective (hθ.symm.trans (h.trans hη))
  · intro h
    have hc := (tangentClassAt_eq_iff.{u,u,u}
      (schemeDeformationBased (Λ := κ) (ParameterTangentDeformation.fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection
        (ParameterTangentDeformation.fibre p x)) (FGModuleCat.of κ (ULift.{u} κ)) _ _).mpr h
    exact hθ.trans ((congrArg E hc).trans hη.symm)

/-- The actual relative kernel is isomorphism to the genuine family
pulled along the zero tangent arrow; it is not assumed to vanish. -/
theorem parameterH1_eq_zero_iff_liftedFamilyIso (θ : DottedTangentArrow s x) :
    ParameterTangentH1.tangentH1LinearMap p s x θ = 0 ↔
    IsIsomorphic (ParameterTangentH1.liftedObject p s x θ)
      (ParameterTangentH1.liftedObject p s x 0) := by
  simpa only [map_zero] using parameterH1_eq_iff_liftedFamilyIso p s x θ 0

end M9Native.CurveAtlasTangentH1
