module

public import M9StacksIntegration.LagrangianPluckerFactor
public import M9StacksIntegration.LagrangianProjectiveSections
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective

/-! Comparison with the actual native Grassmannian Plucker closed immersion.
The comparison is proved on coordinate rings, and hence for all test schemes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.ProjectiveSpaceChartRatio
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianPluckerClosed
open M9Native.LagrangianPluckerLinear M9Native.LagrangianPluckerFactor
open M9Native.LagrangianProjectiveSections
open AlgebraicGeometry.Grassmannian

section RingCoordinates
variable {K U R : Type u} [CommRing K] [AddCommGroup U] [Module K U] [CommRing R]
  {n : ℕ}

theorem symmetricRingHom_ext (b : Basis (Fin (n+1)) K U)
    (f g : SymmetricAlgebra K U →+* R)
    (hC : ∀ a : K,f (algebraMap K (SymmetricAlgebra K U) a)=
      g (algebraMap K (SymmetricAlgebra K U) a))
    (hX : ∀ i,f (SymmetricAlgebra.ι K U (b i))=g (SymmetricAlgebra.ι K U (b i))) : f=g := by
  have h : f.comp (SymPow.gradedMvPolynomialInv b).toRingHom=
      g.comp (SymPow.gradedMvPolynomialInv b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,
        SymPow.gradedMvPolynomialInv_apply,← MvPolynomial.algebraMap_eq,AlgEquiv.commutes] using hC a
    · intro i
      simpa only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,
        SymPow.gradedMvPolynomialInv_apply,SymmetricAlgebra.equivMvPolynomial_symm_X] using hX i
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun h ((SymPow.gradedMvPolynomialHom b) z)
  simpa only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,
    SymPow.gradedMvPolynomialHom_apply,SymPow.gradedMvPolynomialInv_apply,
    AlgEquiv.symm_apply_apply] using hz

theorem moduleEvaluation_algebraMap (b : Basis (Fin (n+1)) K U)
    (κ : K →+* R) (s : Fin (n+1) → R) (a : K) :
    moduleEvaluation b κ s (algebraMap K (SymmetricAlgebra K U) a)=κ a := by
  change (MvPolynomial.eval₂Hom κ s)
    ((SymmetricAlgebra.equivMvPolynomial b) (algebraMap K (SymmetricAlgebra K U) a))=κ a
  rw [AlgEquiv.commutes]
  exact MvPolynomial.eval₂Hom_C κ s a

theorem moduleEvaluation_basis (b : Basis (Fin (n+1)) K U)
    (κ : K →+* R) (s : Fin (n+1) → R) (i : Fin (n+1)) :
    moduleEvaluation b κ s (SymmetricAlgebra.ι K U (b i))=s i := by
  change (MvPolynomial.eval₂Hom κ s)
    ((SymmetricAlgebra.equivMvPolynomial b) (SymmetricAlgebra.ι K U (b i)))=s i
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply,MvPolynomial.eval₂Hom_X']
end RingCoordinates

variable (K : Type u) [Field K]

def fullBasis : Basis (Fin (pluckerDim 3 6+1)) K (FullCoordinates K) :=
  (Pi.basisFun K MinorIndex).reindex (pluckerIndexEquiv 3 6)

/-- The actual base change of the native full quotient-minor Plucker map. -/
def nativeGrassPlucker : M9Native.LagrangianGrassmannian.grassmannian K ⟶
    projectiveSpaceOver (pluckerDim 3 6) (Spec (.of K)) :=
  pullback.lift (M9Native.LagrangianGrassmannian.grassmannianProjection K)
    (pullback.snd _ _ ≫ pluckerMap 3 6) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem nativeGrassPlucker_projection :
    nativeGrassPlucker K ≫ pullback.fst _ _=
      M9Native.LagrangianGrassmannian.grassmannianProjection K := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem nativeGrassPlucker_toIntegral :
    nativeGrassPlucker K ≫ pullback.snd _ _=pullback.snd _ _ ≫ pluckerMap 3 6 :=
  pullback.lift_snd _ _ _

theorem nativeGrassPlucker_isPullback :
    IsPullback (nativeGrassPlucker K) (pullback.snd _ _) (pullback.snd _ _) (pluckerMap 3 6) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst _ _) (h₂₂ := terminal.from (projectiveSpaceAtUniverse.{u} (pluckerDim 3 6)))
  · simpa only [nativeGrassPlucker_projection,terminal.comp_from] using
      (IsPullback.of_hasPullback (terminal.from (Spec (.of K)))
        (terminal.from (scheme.{u} 3 6)))
  · exact nativeGrassPlucker_toIntegral K
  · exact IsPullback.of_hasPullback _ _

instance nativeGrassPlucker_isClosedImmersion : IsClosedImmersion (nativeGrassPlucker K) :=
  MorphismProperty.of_isPullback (nativeGrassPlucker_isPullback K).flip inferInstance

def nativeFullLGPlucker : M9Native.LagrangianGrassmannian.space K ⟶
    projectiveSpaceOver (pluckerDim 3 6) (Spec (.of K)) :=
  M9Native.LagrangianGrassmannian.inclusion K ≫ nativeGrassPlucker K

instance nativeFullLGPlucker_isClosedImmersion : IsClosedImmersion (nativeFullLGPlucker K) :=
  inferInstanceAs (IsClosedImmersion
    (M9Native.LagrangianGrassmannian.inclusion K ≫ nativeGrassPlucker K))

def fullProjectiveIso : projectiveSpaceOver (pluckerDim 3 6) (Spec (.of K)) ≅
    projectiveSpaceOfModule K (FullCoordinates K) := basisProjectiveSpaceIso (fullBasis K)


variable [CharZero K]


omit [CharZero K] in
theorem fullBasis_apply (i : Fin (pluckerDim 3 6+1)) :
    fullBasis K i=Pi.basisFun K MinorIndex ((pluckerIndexEquiv 3 6).symm i) :=
  Basis.reindex_apply _ _ _

theorem chart_evaluation_comp {T : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ M9Native.LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=
      g ≫ chart 3 6 ι) :
    (moduleEvaluation (primitiveBasis14 K).dualBasis
      (baseRingHom (f ≫ M9Native.LagrangianGrassmannian.projection K))
      (M9Native.LagrangianPlucker.chartCoordinates K f ι g)).comp
        (primitiveGradedHom K).toRingHom=
      moduleEvaluation (fullBasis K)
        (baseRingHom (f ≫ M9Native.LagrangianGrassmannian.projection K)) (pluckerSections (k:=3) (n:=6) ι g) := by
  apply symmetricRingHom_ext (fullBasis K)
  · intro a
    change moduleEvaluation (primitiveBasis14 K).dualBasis
        (baseRingHom (f ≫ M9Native.LagrangianGrassmannian.projection K))
        (M9Native.LagrangianPlucker.chartCoordinates K f ι g)
        (SymPow.symAlgMap (primitiveLinearMap K)
          (algebraMap K (SymmetricAlgebra K (FullCoordinates K)) a))=_
    rw [AlgHom.commutes,moduleEvaluation_algebraMap,moduleEvaluation_algebraMap]
  · intro i
    rw [moduleEvaluation_basis]
    simp only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,SymPow.gradedSymAlgMap_apply,
      primitiveGradedHom,SymPow.symAlgMap_ι,fullBasis_apply]
    change primitiveEvaluation K (M9Native.LagrangianPlucker.coefficientMap K f)
        (M9Native.LagrangianPlucker.chartCoordinates K f ι g)
        (SymmetricAlgebra.ι K _ (primitiveLinearMap K
          (Pi.basisFun K MinorIndex ((pluckerIndexEquiv 3 6).symm i))))=_
    rw [primitiveEvaluation_coordinate]
    change M9Native.LagrangianRing.minorFourteen Γ(T,⊤)
        (M9Native.LagrangianPlucker.coefficientMap K f) ((pluckerIndexEquiv 3 6).symm i)
        (M9Native.LagrangianRing.rowFourteen Γ(T,⊤)
          (M9Native.LagrangianPlucker.coefficientMap K f)
          (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι g)))=_
    rw [M9Native.LagrangianRing.nativeMinor_from_rowFourteen _ _ _
      (M9Native.LagrangianPlucker.chart_rows_isotropic K f ι g hfg)]
    rw [toMatrix_chartQuotientMap]
    rfl



omit [CharZero K] in
theorem comp_nativeFullLGPlucker {T : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ M9Native.LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=
      g ≫ chart 3 6 ι) :
    f ≫ nativeFullLGPlucker K=
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (pluckerSections (k:=3) (n:=6) ι g) (span_pluckerSections (k:=3) (n:=6) ι g)
        (f ≫ M9Native.LagrangianGrassmannian.projection K) := by
  apply pullback.hom_ext
  · simp [nativeFullLGPlucker,M9Native.LagrangianGrassmannian.projection,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst]
  · rw [nativeFullLGPlucker,Category.assoc,Category.assoc,nativeGrassPlucker_toIntegral,
      ← Category.assoc,← Category.assoc,hfg,Category.assoc,chart_comp_pluckerMap,comp_chartPluckerMap,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]

theorem comp_primitivePlucker {T : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ M9Native.LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=
      g ≫ chart 3 6 ι) :
    f ≫ M9Native.LagrangianPlucker.primitivePlucker K=
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (M9Native.LagrangianPlucker.chartCoordinates K f ι g)
        (M9Native.LagrangianPlucker.chartCoordinates_span K f ι g hfg)
        (f ≫ M9Native.LagrangianGrassmannian.projection K) := by
  apply pullback.hom_ext
  · simp [Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst]
  · rw [Category.assoc,M9Native.LagrangianPlucker.primitivePlucker_toIntegral,
      M9Native.LagrangianPlucker.comp_integralPrimitivePlucker K f ι g hfg,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]
    rfl


/-- The global primitive quotient-row Plucker map agrees scheme-theoretically
with the original native Grassmannian Plucker map after the actual linear embedding. -/
theorem primitivePlucker_comp_linearEmbedding :
    M9Native.LagrangianPluckerLinear.primitivePlucker K ≫ linearEmbedding K=
      nativeFullLGPlucker K ≫ (fullProjectiveIso K).hom := by
  apply (M9Native.LagrangianPlucker.matrixCover K).hom_ext
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  let f := (M9Native.LagrangianPlucker.matrixCover K).f ι
  let g := M9Native.LagrangianPlucker.matrixChartIntegral K ι
  have hfg := M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι
  have hV := congrArg (fun h => (h ≫ (primitiveProjectiveIso K).hom) ≫ linearEmbedding K)
    (comp_primitivePlucker K f ι g hfg)
  have hU := congrArg (fun h => h ≫ (fullProjectiveIso K).hom)
    (comp_nativeFullLGPlucker K f ι g hfg)
  have hLin := fromSections_comp_linearMap (fullBasis K) (primitiveBasis14 K).dualBasis
    (primitiveLinearMap K) (primitiveLinearMap_surjective K)
    (f ≫ M9Native.LagrangianGrassmannian.projection K)
    (pluckerSections (k:=3) (n:=6) ι g) (span_pluckerSections (k:=3) (n:=6) ι g)
    (M9Native.LagrangianPlucker.chartCoordinates K f ι g)
    (M9Native.LagrangianPlucker.chartCoordinates_span K f ι g hfg)
    (chart_evaluation_comp K f ι g hfg)
  calc
    _ = (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
          (M9Native.LagrangianPlucker.chartCoordinates K f ι g)
          (M9Native.LagrangianPlucker.chartCoordinates_span K f ι g hfg)
          (f ≫ M9Native.LagrangianGrassmannian.projection K) ≫
        (primitiveProjectiveIso K).hom) ≫ linearEmbedding K := by
      simpa only [M9Native.LagrangianPluckerLinear.primitivePlucker,Category.assoc] using hV
    _ = Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
          (pluckerSections (k:=3) (n:=6) ι g) (span_pluckerSections (k:=3) (n:=6) ι g)
          (f ≫ M9Native.LagrangianGrassmannian.projection K) ≫
        (fullProjectiveIso K).hom := hLin
    _ = _ := by simpa only [Category.assoc] using hU.symm

/-- The actual primitive fourteen-coordinate projective space is a closed
linear subspace of the native full-minor projective space. -/
def fixedLinearEmbedding : projectiveSpaceOver 13 (Spec (.of K)) ⟶
    projectiveSpaceOver (pluckerDim 3 6) (Spec (.of K)) :=
  (primitiveProjectiveIso K).hom ≫ linearEmbedding K ≫ (fullProjectiveIso K).inv

instance fixedLinearEmbedding_isClosedImmersion : IsClosedImmersion (fixedLinearEmbedding K) :=
  inferInstanceAs (IsClosedImmersion
    ((primitiveProjectiveIso K).hom ≫ linearEmbedding K ≫ (fullProjectiveIso K).inv))

@[reassoc] theorem primitivePlucker_comp_fixedLinearEmbedding :
    M9Native.LagrangianPlucker.primitivePlucker K ≫ fixedLinearEmbedding K=
      nativeFullLGPlucker K := by
  have h := congrArg (fun f => f ≫ (fullProjectiveIso K).inv)
    (primitivePlucker_comp_linearEmbedding K)
  simpa only [M9Native.LagrangianPluckerLinear.primitivePlucker,fixedLinearEmbedding,
    Category.assoc,Iso.hom_inv_id,Category.comp_id] using h

/-- The genuine global fourteen-coordinate Plucker morphism of the actual
Lagrangian Grassmannian is a closed immersion. -/
instance primitivePlucker_isClosedImmersion :
    IsClosedImmersion (M9Native.LagrangianPlucker.primitivePlucker K) := by
  have : IsClosedImmersion
      (M9Native.LagrangianPlucker.primitivePlucker K ≫ fixedLinearEmbedding K) := by
    rw [primitivePlucker_comp_fixedLinearEmbedding]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (fixedLinearEmbedding K)

instance modulePrimitivePlucker_isClosedImmersion :
    IsClosedImmersion (M9Native.LagrangianPluckerLinear.primitivePlucker K) :=
  inferInstanceAs (IsClosedImmersion (M9Native.LagrangianPlucker.primitivePlucker K ≫
    (primitiveProjectiveIso K).hom))


/-- The actual Lagrangian Grassmannian is projective over its base field,
via the proved genuine fourteen-coordinate closed immersion. -/
theorem isProjectiveMorphism_projection :
    IsProjectiveMorphism (M9Native.LagrangianGrassmannian.projection K) := by
  exact ⟨13,M9Native.LagrangianPlucker.primitivePlucker K,inferInstance,
    M9Native.LagrangianPlucker.primitivePlucker_projection K⟩

/-- Projectivity of the actual LG structure morphism. -/
theorem isProjective_projection :
    IsProjective (M9Native.LagrangianGrassmannian.projection K) :=
  (isProjectiveMorphism_projection K).isProjective

end M9Native.LagrangianPluckerClosed
