module
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

public import M9StacksIntegration.LagrangianSymplecticAction
public import M9StacksIntegration.BaseFieldPoints
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective

/-! Actual translated affine-six charts on the native LG scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix TopologicalSpace

universe u

namespace M9Native.LagrangianTranslatedCharts

open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianTransitivity M9Native.LagrangianSymplecticAction

variable (K : Type u) [Field K]

theorem firstSubmap_comp_standard (T : Scheme.{u}) :
    coordinateSubmap T 3 6 firstPivot ≫
      Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(T,⊤))=𝟙 (freeOn T 3) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  change Stacks.FreeSheafMatrix.toMatrix
    (SheafOfModules.freeMap (R:=T.ringCatSheaf)
      (fun i : ULift.{u} (Fin 3) => ULift.up (firstPivot i.down)) ≫
        Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(T,⊤)))=_
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    Stacks.FreeSheafMatrix.toMatrix_freeMap]
  have hid : Stacks.FreeSheafMatrix.toMatrix (𝟙 (freeOn T 3))=1 :=
    Stacks.FreeSheafMatrix.toMatrix_id (X:=T) 3
  rw [hid]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  exact standardQuotient_first Γ(T,⊤) i j

theorem exists_integral_chart_factor_of_epi {T : Scheme.{u}} (f : T ⟶ grassmannian K)
    (hepi : Epi (coordinateSubmap T 3 6 firstPivot ≫
      (pullbackPresentation f (universalQuotient K)).map)) :
    ∃ g : T ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k:=3) (n:=6) firstPivot) (ULift.{u} ℤ))),
      g ≫ chart 3 6 firstPivot=f ≫ pullback.snd _ _ := by
  let x := (schemeRepresentableBy 3 6).homEquiv (f ≫ pullback.snd _ _)
  have hx : coordinateChartCondition 3 6 firstPivot T x :=
    ⟨pullbackPresentation f (universalQuotient K),(pullbackUniversal_class K f).symm,hepi⟩
  let y : (coordinateChartSubfunctor.{u} 3 6 firstPivot).obj (op T) := ⟨x,hx⟩
  let g := (coordinateChartPointsEquiv T 3 6 firstPivot).symm y
  refine ⟨g,?_⟩
  apply (schemeRepresentableBy 3 6).homEquiv.injective
  change (representableBy 3 6).homEquiv (g ≫ chartMap 3 6 firstPivot)=x
  rw [homEquiv_comp_chartMap]
  exact congrArg Subtype.val ((coordinateChartPointsEquiv T 3 6 firstPivot).apply_symm_apply y)

theorem exists_matrixChart_factor_of_epi {T : Scheme.{u}} (f : T ⟶ grassmannian K)
    (hepi : Epi (coordinateSubmap T 3 6 firstPivot ≫
      (pullbackPresentation f (universalQuotient K)).map)) :
    ∃ a : T ⟶ Spec (.of (MatrixRing K)),a ≫ matrixChart K=f := by
  obtain ⟨g,hg⟩ := exists_integral_chart_factor_of_epi K f hepi
  let z : T ⟶ M9Native.GrassmannianCharts.chartSpace K 3 6 firstPivot :=
    pullback.lift (f ≫ grassmannianProjection K) g (terminal.hom_ext _ _)
  have hz : z ≫ M9Native.GrassmannianCharts.chartOver K 3 6 firstPivot=f := by
    apply pullback.hom_ext
    · rw [Category.assoc,M9Native.GrassmannianCharts.chartOver_projection]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc,M9Native.GrassmannianCharts.chartOver_toIntegral,
        ← Category.assoc,pullback.lift_snd,hg]
  let em : Spec (.of (MatrixRing K)) ≅ M9Native.GrassmannianCharts.chartSpace K 3 6 firstPivot :=
    (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).symm ≪≫ chartCoordinatesIso K
  refine ⟨z ≫ em.inv,?_⟩
  change (z ≫ em.inv) ≫ (em.hom ≫ M9Native.GrassmannianCharts.chartOver K 3 6 firstPivot)=f
  rw [Category.assoc,em.inv_hom_id_assoc]
  exact hz

/-- Standard quotient data give a genuine factor through the checked affine-six big cell. -/
theorem exists_bigCell_factor_of_standard_quotient {T : Scheme.{u}} (p : T ⟶ space K)
    (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅ freeOn T 3)
    (he : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom=
      Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(T,⊤))) :
    ∃ z : T ⟶ Spec (.of (MvPolynomial (Fin 6) K)),z ≫ bigCell K=p := by
  let q := pullbackPresentation (p ≫ inclusion K) (universalQuotient K)
  have hs : (coordinateSubmap T 3 6 firstPivot ≫ q.map) ≫ e.hom=𝟙 (freeOn T 3) := by
    rw [Category.assoc,he]
    exact firstSubmap_comp_standard T
  have hm : coordinateSubmap T 3 6 firstPivot ≫ q.map=e.inv :=
    (cancel_mono e.hom).mp (hs.trans e.inv_hom_id.symm)
  have hepi : Epi (coordinateSubmap T 3 6 firstPivot ≫ q.map) := by
    rw [hm]
    infer_instance
  obtain ⟨a,ha⟩ := exists_matrixChart_factor_of_epi K (p ≫ inclusion K) hepi
  let l : T ⟶ lagrangianChart K := pullback.lift a p ha
  refine ⟨l ≫ (lagrangianChartIsoPolynomialSix K).hom,?_⟩
  rw [bigCell,Category.assoc,(lagrangianChartIsoPolynomialSix K).hom_inv_id_assoc]
  exact pullback.lift_snd _ _ _

theorem exists_point_action_bigCell (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K=𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (z : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin 6) K))),
      z ≫ bigCell K=p ≫ action K g := by
  obtain ⟨g,e,he⟩ := exists_point_action_normalForm K p hp
  obtain ⟨z,hz⟩ := exists_bigCell_factor_of_standard_quotient K (p ≫ action K g) e he
  exact ⟨g,z,hz⟩

def translatedBigCell (g : Matrix.symplecticGroup (Fin 3) K) :
    Spec (.of (MvPolynomial (Fin 6) K)) ⟶ space K := bigCell K ≫ action K g

instance translatedBigCell_isOpenImmersion (g : Matrix.symplecticGroup (Fin 3) K) :
    IsOpenImmersion (translatedBigCell K g) := by
  change IsOpenImmersion (bigCell K ≫ (symplecticAutomorphism K g).hom)
  infer_instance

@[reassoc (attr := simp)] theorem translatedBigCell_projection
    (g : Matrix.symplecticGroup (Fin 3) K) :
    translatedBigCell K g ≫ projection K=
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ:=Fin 6) (R:=K))) := by
  rw [translatedBigCell,Category.assoc,action_projection,bigCell_projection]

/-- Every actual base-field point lies in an actual translated affine-six chart. -/
theorem exists_translatedBigCell_point (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K=𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (z : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin 6) K))),z ≫ translatedBigCell K g=p := by
  obtain ⟨g,z,hz⟩ := exists_point_action_bigCell K p hp
  refine ⟨g⁻¹,z,?_⟩
  rw [translatedBigCell,← Category.assoc,hz,Category.assoc,action_mul,mul_inv_cancel,action_one,
    Category.comp_id]

instance projection_locallyOfFiniteType : LocallyOfFiniteType (projection K) := by
  change LocallyOfFiniteType (inclusion K ≫ (Grassmannian.schemeOver.over 3 6 (base K)).hom)
  infer_instance

instance projection_quasiCompact : QuasiCompact (projection K) := by
  have : IsProper (Grassmannian.schemeOver.over 3 6 (base K)).hom :=
    isProper_of_isProjectiveMorphism _ (Grassmannian.isProjectiveMorphism_schemeOver 3 6 (base K))
  change QuasiCompact (inclusion K ≫ (Grassmannian.schemeOver.over 3 6 (base K)).hom)
  infer_instance

section AlgebraicallyClosed
variable [IsAlgClosed K]

/-- The actual open translated charts cover all scheme points, by the closed-point theorem. -/
theorem translatedBigCell_cover (x : space K) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K,x ∈ Set.range (translatedBigCell K g) := by
  let U : (space K).Opens := ⨆ g : Matrix.symplecticGroup (Fin 3) K,(translatedBigCell K g).opensRange
  have hx : x ∈ U := by
    by_contra hnot
    let : JacobsonSpace (space K) := LocallyOfFiniteType.jacobsonSpace (projection K)
    obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints
      (Z:=((U : Set (space K))ᶜ)) ⟨x,hnot⟩ U.isOpen.isClosed_compl.isLocallyClosed
    let p := pointOfClosedPoint (projection K) y hyc
    obtain ⟨g,z,hz⟩ := exists_translatedBigCell_point K p (pointOfClosedPoint_comp _ _ _)
    apply hy
    apply Opens.mem_iSup.mpr
    refine ⟨g,Scheme.Hom.mem_opensRange.mpr ⟨z (IsLocalRing.closedPoint K),?_⟩⟩
    exact (congrArg (fun f : Spec (.of K) ⟶ space K => f (IsLocalRing.closedPoint K)) hz).trans
      (pointOfClosedPoint_apply _ _ _ _)
  obtain ⟨g,hg⟩ := Opens.mem_iSup.mp hx
  exact ⟨g,Scheme.Hom.mem_opensRange.mp hg⟩

def translatedCover : (space K).OpenCover :=
  Scheme.Cover.mkOfCovers (Matrix.symplecticGroup (Fin 3) K)
    (fun _ => Spec (.of (MvPolynomial (Fin 6) K))) (translatedBigCell K)
    (fun x => by
      obtain ⟨g,y,hy⟩ := translatedBigCell_cover K x
      exact ⟨g,y,hy⟩)

omit [IsAlgClosed K] in
theorem polynomialSix_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 6
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ:=Fin 6) (R:=K)))) := by
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 6)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap K (MvPolynomial (Fin 6) K)).IsStandardSmoothOfRelativeDimension 6
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 6
    (MvPolynomial.renameEquiv K (Equiv.refl (Fin 6)))

/-- Actual smoothness of relative dimension six follows from the actual affine-six open cover. -/
instance smoothOfRelativeDimension_projection : SmoothOfRelativeDimension 6 (projection K) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 6 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 6)
    (translatedCover K) fun g => ?_
  change SmoothOfRelativeDimension 6 (translatedBigCell K g ≫ projection K)
  rw [translatedBigCell_projection]
  exact polynomialSix_smoothOfRelativeDimension K

instance smooth_projection : Smooth (projection K) :=
  SmoothOfRelativeDimension.smooth 6 (projection K)

end AlgebraicallyClosed

end M9Native.LagrangianTranslatedCharts

end
