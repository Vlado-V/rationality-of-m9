module

public import M9StacksIntegration.MukaiGeneratedImageRank
public import M9StacksIntegration.MukaiSaturationGenericRank

/-!
# The literal image of the original finite evaluation

This is the categorical image of the original evaluation O^r -> E,
prior to saturation. Coherence and torsion freeness make that very
image locally free on the regular curve. Its generic stalk is proved
to have the original evaluation rank, so its rank is derived. The
canonical monomorphism into the independently constructed saturation
and the lifts of the original sections are retained literally.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace M9Native.MukaiEvaluationImage

open MukaiSaturationRank

variable {X : Scheme.{u}}

/-- Surjectivity of the actual local-ring stalk map of an original
sheaf epimorphism. -/
theorem stalkMap_surjective {F E : X.Modules} (φ : F ⟶ E) [Epi φ] (x : X) :
    Function.Surjective (stalkMap φ x) := by
  have h := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := X.ringCatSheaf) φ).mp inferInstance x
  intro t
  obtain ⟨s,hs⟩ := h t
  exact ⟨s,(stalkMap_native φ x s).trans hs⟩

/-- The literal categorical image is coherent for an original map of
coherent sheaves. -/
theorem image_isCoherent {F E : X.Modules} [hF : F.IsCoherent] [hE : E.IsCoherent]
    (φ : F ⟶ E) : (image φ).IsCoherent := by
  let : (CategoryTheory.Abelian.image φ).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_image hF hE φ
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (CategoryTheory.Abelian.imageIsoImage φ).symm

/-- The original image inclusion and the original map have exactly
the same image on their actual local-ring stalks. -/
theorem range_image_stalk_eq_range {F E : X.Modules} (φ : F ⟶ E) (x : X) :
    LinearMap.range (stalkMap (image.ι φ) x) = LinearMap.range (stalkMap φ x) := by
  have hs := stalkMap_surjective (factorThruImage φ) x
  have hcomp : (stalkMap (image.ι φ) x).comp (stalkMap (factorThruImage φ) x) =
      stalkMap φ x := by
    ext m
    change stalkMap (image.ι φ) x (stalkMap (factorThruImage φ) x m) = stalkMap φ x m
    rw [← stalkMap_comp,image.fac]
  calc
    _ = LinearMap.range ((stalkMap (image.ι φ) x).comp
        (stalkMap (factorThruImage φ) x)) := by
      rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hs,Submodule.map_top]
    _ = _ := congrArg LinearMap.range hcomp

/-- The dimension of the original image's generic stalk is the
genuine generic rank of the original map. -/
theorem finrank_image_generic_eq_range [IsIntegral X] {F E : X.Modules}
    (φ : F ⟶ E) [(image φ).IsCoherent] :
    Module.finrank (X.presheaf.stalk (genericPoint X)) (Stalk (image φ) (genericPoint X)) =
      Module.finrank (X.presheaf.stalk (genericPoint X))
        (LinearMap.range (stalkMap φ (genericPoint X))) := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let : Module.Finite (X.presheaf.stalk (genericPoint X)) (Stalk (image φ) (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent (image φ) (genericPoint X)
  rw [← range_image_stalk_eq_range φ (genericPoint X)]
  exact (LinearMap.finrank_range_of_inj (stalkMap_injective (image.ι φ) (genericPoint X))).symm

/-- The rank of the literal categorical image is derived from the
actual original generic stalk map on a regular integral curve. -/
theorem image_rank_of_generic_rank [IsIntegral X]
    {F E : X.Modules} [F.IsCoherent] [hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
    (φ : F ⟶ E) (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1) (d : ℕ)
    (hd : Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.range (stalkMap φ (genericPoint X))) = d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) d := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : (image φ).IsCoherent := image_isCoherent φ
  let : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  let : (image φ).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (image φ)
  let : (image φ).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hET : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr hE
  have hIT := MukaiGeneratedImage.isTorsionFree_of_mono (image.ι φ) hET
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ) :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (image φ)).mp hIT
  have hdimI := (finrank_image_generic_eq_range φ).trans hd
  have hfr : Scheme.Modules.fiberRank (image φ) (genericPoint X) = d :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (image φ)).trans hdimI
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (image φ) d (genericPoint X) hfr

section Evaluation

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The actual image of the original finite tuple evaluation. -/
abbrev evaluationImage {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) : X.Modules :=
  image (MukaiSemiIrreducible.evaluation k f E s)

/-- The original finite free source is coherent, so its literal
evaluation image has the computed original generic rank. -/
theorem evaluationImage_rank [IsIntegral X] {r : ℕ}
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
    (s : Fin r → cohomologyOverField k f E 0)
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1) (d : ℕ)
    (hd : MukaiEvaluationGenericRank.genericRank k f E s = d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (evaluationImage k f E s) d := by
  let A := TupleEvaluationFiber.tupleFreeSheaf (X := X) r
  have hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv (ULift.{u} (Fin r)) r Equiv.ulift
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : A.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X A
  exact image_rank_of_generic_rank (MukaiSemiIrreducible.evaluation k f E s) hreg hdim d hd

/-- Native H0 injectivity of the original categorical image inclusion. -/
theorem cohomologyMap_image_injective {F E : X.Modules} (φ : F ⟶ E) :
    Function.Injective (cohomologyOverFieldMap k f (image.ι φ) 0) := by
  have hS : (ShortComplex.cokernelSequence (image.ι φ)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono (image.ι φ); infer_instance
      epi_g := by change Epi (cokernel.π (image.ι φ)); infer_instance }
  obtain ⟨_,hinj,_⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact hinj

/-- The canonical actual lift of an original source section into its
literal image, through the public H0/sections linear comparison. -/
def liftedSectionH0 {F E : X.Modules} (φ : F ⟶ E) (s : F.sections) :
    cohomologyOverField k f (image φ) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (image φ)).inv
    ((_root_.SheafOfModules.sectionsMap (factorThruImage φ) s).eval (op ⊤))

theorem cohomologyMap_liftedSectionH0 {F E : X.Modules} (φ : F ⟶ E) (s : F.sections) :
    cohomologyOverFieldMap k f (image.ι φ) 0 (liftedSectionH0 k f φ s) =
      (cohomologyOverFieldZeroLinearIso k f E).inv
        ((_root_.SheafOfModules.sectionsMap φ s).eval (op ⊤)) := by
  apply (ModuleCat.mono_iff_injective (cohomologyOverFieldZeroLinearIso k f E).hom).mp
    inferInstance
  rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
  simp only [liftedSectionH0,Iso.inv_hom_id_apply]
  change (_root_.SheafOfModules.sectionsMap (image.ι φ)
      (_root_.SheafOfModules.sectionsMap (factorThruImage φ) s)).eval (op ⊤) = _
  rw [← _root_.SheafOfModules.sectionsMap_comp,image.fac]

/-- Every original finite-tuple section has a canonical lift into the
literal generated image, mapping to that exact original H0 section. -/
theorem evaluation_lift_maps_to_section {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (i : Fin r) :
    cohomologyOverFieldMap k f (image.ι (MukaiSemiIrreducible.evaluation k f E s)) 0
      (liftedSectionH0 k f (MukaiSemiIrreducible.evaluation k f E s)
        (_root_.SheafOfModules.freeSection (ULift.up i))) = s i := by
  rw [cohomologyMap_liftedSectionH0,MukaiSemiIrreducible.evaluation_freeSection,
    MukaiSemiIrreducible.sectionOfH0_eval_top,Iso.hom_inv_id_apply]

/-- The literal generated image retains the original independent
tuple, and therefore has at least its number of actual sections. -/
theorem evaluationImage_h0_lower_bound {r : ℕ} (E : X.Modules)
    [FiniteDimensional k (cohomologyOverField k f E 0)]
    (s : Fin r → cohomologyOverField k f E 0) (hs : LinearIndependent k s) :
    r ≤ Module.finrank k (cohomologyOverField k f (evaluationImage k f E s) 0) := by
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : FiniteDimensional k (cohomologyOverField k f (image φ) 0) :=
    Module.Finite.of_injective (cohomologyOverFieldMap k f (image.ι φ) 0).hom
      (cohomologyMap_image_injective k f φ)
  let t : Fin r → cohomologyOverField k f (image φ) 0 := fun i =>
    liftedSectionH0 k f φ (_root_.SheafOfModules.freeSection (ULift.up i))
  have ht : LinearIndependent k t := by
    apply LinearIndependent.of_comp (cohomologyOverFieldMap k f (image.ι φ) 0).hom
    convert hs using 1
    funext i
    exact evaluation_lift_maps_to_section k f E s i
  simpa only [Fintype.card_fin] using ht.fintype_card_le_finrank

end Evaluation

section Saturation

variable [IsIntegral X] {F E : X.Modules} (φ : F ⟶ E) [(cokernel φ).IsQuasicoherent]

/-- The actual categorical image has its canonical monomorphism into
the independently constructed prescribed saturation. -/
def imageToSaturation : image φ ⟶ MukaiEvaluationSaturation.saturation φ :=
  image.lift
    { I := MukaiEvaluationSaturation.saturation φ
      m := MukaiEvaluationSaturation.inclusion φ
      e := MukaiEvaluationSaturation.factor φ
      fac := MukaiEvaluationSaturation.factor_inclusion φ }

@[reassoc (attr := simp)] theorem imageToSaturation_inclusion :
    imageToSaturation φ ≫ MukaiEvaluationSaturation.inclusion φ = image.ι φ :=
  image.lift_fac _

instance imageToSaturation_mono : Mono (imageToSaturation φ) := by
  dsimp [imageToSaturation]
  infer_instance

@[reassoc (attr := simp)] theorem factorThruImage_imageToSaturation :
    factorThruImage φ ≫ imageToSaturation φ = MukaiEvaluationSaturation.factor φ :=
  image.fac_lift _

end Saturation

end M9Native.MukaiEvaluationImage
