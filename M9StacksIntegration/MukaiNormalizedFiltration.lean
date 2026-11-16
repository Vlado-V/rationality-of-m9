module

public import M9StacksIntegration.CurveLineSubbundle
public import M9StacksIntegration.InvertibleExtCancellation
public import M9StacksIntegration.MukaiHomCoefficient

/-!
# Normalize the actual line filtration and retain the original middle bundle

An actual line quotient is tensored by its actual inverse. The genuine
inverse-tensor unit isomorphism changes its target to the actual structure
sheaf. Exactness is transported by an actual isomorphism of short
complexes. Applied to the proved line-subbundle construction this produces
the normalized sequence without assuming any line filtration.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiNormalizedFiltration

open M9Native.MukaiCupAlternating M9Native.MukaiTensorSection
open M9Native.MukaiHomCoefficient

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The genuine inverse of the actual quotient line bundle. -/
abbrev inverseLine (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] : X.Modules :=
  Scheme.Modules.tensorInverse M

/-- The actual sequence after inverse twisting and the actual unit
isomorphism on the quotient. -/
def normalizedSequence (S : ShortComplex X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₃] :
    ShortComplex X.Modules := by
  let T := tensorRight (inverseLine S.X₃)
  letI := tensorRight_additive (inverseLine S.X₃)
  refine ShortComplex.mk (T.map S.f)
    (T.map S.g ≫ (M9Native.InvertibleExtCancellation.inverseTensorUnitIso S.X₃).hom) ?_
  rw [← Category.assoc, ← T.map_comp, S.zero, T.map_zero, zero_comp]

/-- The normalized sequence is genuinely isomorphic to the tensor image
of the original actual sequence. -/
def normalizedSequenceIso (S : ShortComplex X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₃] :
    letI := tensorRight_additive (inverseLine S.X₃)
    S.map (tensorRight (inverseLine S.X₃)) ≅ normalizedSequence S := by
  letI := tensorRight_additive (inverseLine S.X₃)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (M9Native.InvertibleExtCancellation.inverseTensorUnitIso S.X₃) ?_ ?_
  · simp only [normalizedSequence, ShortComplex.map_f, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
  · simp only [normalizedSequence, ShortComplex.map_g, Iso.refl_hom, Category.id_comp]

/-- Exactness of the actual normalized sequence follows from exactness
of tensoring by the actual invertible inverse. -/
theorem normalizedSequence_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₃] :
    (normalizedSequence S).ShortExact := by
  let := Scheme.Modules.isInvertible_tensorInverse S.X₃
  let := tensorRight_additive (inverseLine S.X₃)
  let : (tensorRight (inverseLine S.X₃)).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor (inverseLine S.X₃)
  exact (ShortComplex.shortExact_iff_of_iso (normalizedSequenceIso S)).mp
    (hS.map_of_exact (tensorRight (inverseLine S.X₃)))

/-- Every genuine rank-two bundle on the original smooth integral curve
has an actual normalized line sequence; no such sequence is assumed. -/
theorem exists_normalized_line_sequence_on_smooth_curve
    (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    (F : X.Modules) (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    ∃ (L M : X.Modules),
      SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L ∧
      ∃ hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M,
      letI := hM
      ∃ (i : tensor L (inverseLine M) ⟶ tensor F (inverseLine M))
        (q : tensor F (inverseLine M) ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
        (w : i ≫ q = 0), (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨L,M,hL,hM,_,i,q,w,hS⟩ :=
    M9Native.CurveLineSubbundle.exists_line_subbundle_on_smooth_curve k f F hF
  let := hM
  let S := ShortComplex.mk i q w
  let Z := normalizedSequence S
  exact ⟨L,M,hL,hM,Z.f,Z.g,Z.zero,normalizedSequence_shortExact hS⟩

/-- The original actual symmetry of the tensor product sheaf. -/
abbrev tensorSwap (A B : X.Modules) : tensor A B ≅ tensor B A :=
  Stacks.SheafOfModules.Invertible.tensorProductBraiding.{u,u,u}
    X.sheaf.obj X.ringCatSheaf.property A B

/-- The actual middle bundle after normalizing the quotient and
tensoring by `E tensor M` is isomorphic to the original `E tensor F`. -/
def normalizedTensorMiddleIso (E F M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    tensor (tensor F (inverseLine M)) (tensor E M) ≅ tensor E F := by
  let T : X.Modules ⥤ X.Modules ⥤ X.Modules :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf
  let inner : tensor M (tensor F (inverseLine M)) ≅ F :=
    (tensorAssociator M F (inverseLine M)).symm ≪≫
      (T.mapIso (tensorSwap M F)).app (inverseLine M) ≪≫
      tensorAssociator F M (inverseLine M) ≪≫
      (T.obj F).mapIso (M9Native.InvertibleExtCancellation.inverseTensorUnitIso M) ≪≫
      unitRightIso F
  exact tensorSwap (tensor F (inverseLine M)) (tensor E M) ≪≫
    tensorAssociator E M (tensor F (inverseLine M)) ≪≫ (T.obj E).mapIso inner

end M9Native.MukaiNormalizedFiltration
