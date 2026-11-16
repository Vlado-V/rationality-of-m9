module

public import M9StacksIntegration.LagrangianRingCoordinates
public import M9StacksIntegration.LagrangianMatrixChart
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-! Genuine primitive Plucker coordinates on the native LG. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u

namespace M9Native.LagrangianPlucker

open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart

/-- The two actual exterior-sheaf descriptions of the quotient bivector coincide. -/
theorem actualSigma_eq (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3) :
    (M9Native.LagrangianGrassmannian.exteriorPowerMap X q 2).app ⊤ (sigmaSection X)=
      quotientSigmaSheaf X q := by
  unfold sigmaSection quotientSigmaSheaf
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [M9Native.LagrangianGrassmannian.exteriorPowerMap_wedgeSection,
    M9Native.ExteriorEvaluation.sectionComparison_ιMulti]
  rfl

/-- The actual quotient section corresponds to the literal module bivector
for its actual native coefficient matrix, without a normalized-pivot hypothesis. -/
theorem quotientSigmaSheaf_eq_matrix (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3) :
    quotientSigmaSheaf X q=freeExteriorSectionsEquiv X 2 3
      (M9Native.LagrangianRing.quotientSigma Γ(X,⊤) (Stacks.FreeSheafMatrix.toMatrix q)) := by
  unfold quotientSigmaSheaf M9Native.LagrangianRing.quotientSigma
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [freeExteriorSectionsEquiv_ιMulti]
  apply congrArg (M9Native.ExteriorEvaluation.sectionComparison (freeOn X 3) 2 ⊤)
  apply congrArg (exteriorPower.ιMulti Γ(X,⊤) 2)
  funext j
  fin_cases j
  all_goals
    apply (freeSectionCoordinates X 3).injective
    funext k
    rw [LinearEquiv.apply_symm_apply]
    exact freeCoordinates_map_basis q k _

/-- Annihilation of the actual sheaf bivector implies the literal native
matrix rows are isotropic over its coordinate ring. -/
theorem rows_isotropic_of_annihilatesSigma (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3)
    (hq : AnnihilatesSigma X q) (i j : Fin 3) :
    M9Native.LagrangianRing.omega Γ(X,⊤) (Stacks.FreeSheafMatrix.toMatrix q i)
      (Stacks.FreeSheafMatrix.toMatrix q j)=0 := by
  have hz : freeExteriorSectionsEquiv X 2 3
      (M9Native.LagrangianRing.quotientSigma Γ(X,⊤) (Stacks.FreeSheafMatrix.toMatrix q))=0 :=
    (quotientSigmaSheaf_eq_matrix X q).symm.trans ((actualSigma_eq X q).symm.trans hq)
  exact M9Native.LagrangianRing.rows_isotropic_of_quotientSigma_zero Γ(X,⊤)
    (Stacks.FreeSheafMatrix.toMatrix q)
    ((map_eq_zero_iff _ (freeExteriorSectionsEquiv X 2 3).injective).mp hz) i j

variable (K : Type u) [Field K]

def coefficientMap {T : Scheme.{u}} (f : T ⟶ M9Native.LagrangianGrassmannian.space K) :
    K →+* Γ(T,⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ projection K).appTop).hom

theorem chart_rows_isotropic {T : Scheme.{u}} (f : T ⟶ M9Native.LagrangianGrassmannian.space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) (i j : Fin 3) :
    M9Native.LagrangianRing.omega Γ(T,⊤) (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι g) i)
      (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι g) j)=0 := by
  obtain ⟨e,he⟩ := pullbackUniversal_chart_isomorphic K (f ≫ inclusion K) ι g hfg
  have hf := (factorsThrough_iff_pullbackQuotient_annihilates K (f ≫ inclusion K)).mp ⟨f,rfl⟩
  have hq := (annihilatesSigma_iff_of_iso T _ _ e he).mp hf
  exact rows_isotropic_of_annihilatesSigma T (chartQuotientMap 3 6 ι g) hq i j

variable [CharZero K]

def chartCoordinates {T : Scheme.{u}} (f : T ⟶ M9Native.LagrangianGrassmannian.space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ)))) :
    Fin 14 → Γ(T,⊤) :=
  M9Native.LagrangianRing.rowFourteen Γ(T,⊤) (coefficientMap K f)
    (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι g))

theorem chartCoordinates_span {T : Scheme.{u}} (f : T ⟶ M9Native.LagrangianGrassmannian.space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    Ideal.span (Set.range (chartCoordinates K f ι g))=⊤ := by
  apply M9Native.LagrangianRing.span_rowFourteen_eq_top Γ(T,⊤) (coefficientMap K f) _
    (chart_rows_isotropic K f ι g hfg) ι
  have hdet : Matrix.det ((Stacks.FreeSheafMatrix.toMatrix
      (chartQuotientMap 3 6 ι g)).submatrix id ι)=1 := by
    rw [toMatrix_chartQuotientMap]
    convert Matrix.det_one (R:=Γ(T,⊤)) (n:=Fin 3) using 2
    ext i j
    rw [Matrix.submatrix_apply,chartMatrix_apply_self,Matrix.one_apply]
    rfl
  rw [hdet]
  exact isUnit_one



open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

/-- A genuine chart morphism to the primitive projective thirteen-space. -/
def chartProjectiveMap {T : Scheme.{u}} (f : T ⟶ M9Native.LagrangianGrassmannian.space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    T ⟶ projectiveSpaceAtUniverse.{u} 13 :=
  toProjectiveSpaceAtUniverse (chartCoordinates K f ι g) (chartCoordinates_span K f ι g hfg)

omit [CharZero K] in
theorem coefficientMap_comp {T T' : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (t : T' ⟶ T) :
    coefficientMap K (t ≫ f)=t.appTop.hom.comp (coefficientMap K f) := by
  ext a
  rfl

theorem rowTwenty_map {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (M : Matrix (Fin 3) (Fin 6) R) :
    M9Native.LagrangianRing.rowTwenty S (M.map ρ)=ρ ∘ M9Native.LagrangianRing.rowTwenty R M := by
  funext j
  rw [Function.comp_apply,M9Native.LagrangianRing.rowTwenty_eq_minor,
    M9Native.LagrangianRing.rowTwenty_eq_minor]
  change ((M.submatrix id (M9Native.LagrangianRing.triple j)).map ρ).det=
    ρ (M.submatrix id (M9Native.LagrangianRing.triple j)).det
  exact (RingHom.map_det ρ _).symm

omit [CharZero K] in
theorem rowFourteen_map {R S : Type*} [CommRing R] [CommRing S]
    (f : K →+* R) (ρ : R →+* S) (M : Matrix (Fin 3) (Fin 6) R) :
    M9Native.LagrangianRing.rowFourteen S (ρ.comp f) (M.map ρ)=
      ρ ∘ M9Native.LagrangianRing.rowFourteen R f M := by
  unfold M9Native.LagrangianRing.rowFourteen
  rw [rowTwenty_map]
  funext j
  exact (RingHom.map_mulVec ρ ((M9Native.LagrangianField.projectionMatrix K).map f)
    (M9Native.LagrangianRing.rowTwenty R M) j).symm

omit [CharZero K] in
/-- Actual primitive chart coordinates commute with arbitrary pullback of
schemes, using the actual structural scalar map. -/
theorem chartCoordinates_comp {T T' : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (t : T' ⟶ T) :
    chartCoordinates K (t ≫ f) ι (t ≫ g)=t.appTop ∘ chartCoordinates K f ι g := by
  have hM : Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι (t ≫ g))=
      (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι g)).map t.appTop.hom := by
    rw [toMatrix_chartQuotientMap,toMatrix_chartQuotientMap,← chartMatrix_map]
    rfl
  unfold chartCoordinates
  rw [hM,coefficientMap_comp]
  exact rowFourteen_map K _ _ _

/-- The actual chart morphisms have the canonical scheme-pullback naturality. -/
theorem comp_chartProjectiveMap {T T' : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι)
    (t : T' ⟶ T)
    (htfg : ((t ≫ f) ≫ inclusion K) ≫ pullback.snd _ _=(t ≫ g) ≫ chart 3 6 ι) :
    t ≫ chartProjectiveMap K f ι g hfg=
      chartProjectiveMap K (t ≫ f) ι (t ≫ g) htfg := by
  have hs : Ideal.span (Set.range (fun j => t.appTop (chartCoordinates K f ι g j)))=⊤ := by
    exact (congrArg (fun v : Fin 14 → Γ(T',⊤) => Ideal.span (Set.range v))
      (chartCoordinates_comp K f ι g t)).symm.trans
        (chartCoordinates_span K (t ≫ f) ι (t ≫ g) htfg)
  rw [chartProjectiveMap,hasPullbackNaturality t _ _ hs]
  exact toProjectiveSpaceAtUniverse_congr (chartCoordinates_comp K f ι g t).symm _ _

/-- The actual fourteen-coordinate morphisms agree for any two native
quotient charts representing the same LG morphism. -/
theorem chartProjectiveMap_compat {T : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι κ : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) κ) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι)
    (hfh : (f ≫ inclusion K) ≫ pullback.snd _ _=h ≫ chart 3 6 κ) :
    chartProjectiveMap K f ι g hfg=chartProjectiveMap K f κ h hfh := by
  obtain ⟨E,hE,hM⟩ := exists_isUnit_det_chartMatrix_eq_mul g h (hfg.symm.trans hfh)
  have hv : chartCoordinates K f ι g=fun j => (hE.unit : Γ(T,⊤))*chartCoordinates K f κ h j := by
    unfold chartCoordinates
    rw [toMatrix_chartQuotientMap,toMatrix_chartQuotientMap,hM,
      M9Native.LagrangianRing.rowFourteen_mul]
    funext j
    simp only [Pi.smul_apply,smul_eq_mul,IsUnit.unit_spec]
  have hs : Ideal.span (Set.range (fun j => (hE.unit : Γ(T,⊤))*chartCoordinates K f κ h j))=⊤ := by
    rw [span_range_unit_smul]
    exact chartCoordinates_span K f κ h hfh
  rw [chartProjectiveMap,toProjectiveSpaceAtUniverse_congr hv _ hs]
  exact hasUnitInvariance hE.unit _ _ hs



/-- The actual native Grassmannian matrix cover pulled back to the actual LG. -/
def matrixCover : (M9Native.LagrangianGrassmannian.space K).OpenCover :=
  (M9Native.GrassmannianCharts.matrixCover K 3 6).pullback₁ (inclusion K)

def matrixChartIntegral (ι : Fin 3 ↪ Fin 6) : (matrixCover K).X ι ⟶
    Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))) :=
  (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom (inclusion K) ι ≫
    AffineSpace.toSpecMvPoly (ChartIndex.{u} (k:=3) (n:=6) ι) (Spec (.of K))

omit [CharZero K] in
theorem matrixChartIntegral_diagram (ι : Fin 3 ↪ Fin 6) :
    ((matrixCover K).f ι ≫ inclusion K) ≫ pullback.snd _ _=
      matrixChartIntegral K ι ≫ chart 3 6 ι := by
  have h := (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom_map (inclusion K) ι
  calc
    _ = ((M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom (inclusion K) ι ≫
        (M9Native.GrassmannianCharts.matrixCover K 3 6).f ι) ≫ pullback.snd _ _ :=
      congrArg (fun q => q ≫ pullback.snd _ _) h.symm
    _ = (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom (inclusion K) ι ≫
        ((M9Native.GrassmannianCharts.matrixCover K 3 6).f ι ≫ pullback.snd _ _) :=
      Category.assoc _ _ _
    _ = (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom (inclusion K) ι ≫
        (AffineSpace.toSpecMvPoly (ChartIndex.{u} (k:=3) (n:=6) ι) (Spec (.of K)) ≫
          chart 3 6 ι) :=
      congrArg (fun q => (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom
        (inclusion K) ι ≫ q) (M9Native.GrassmannianCharts.chartOver_toIntegral K 3 6 ι)
    _ = _ := (Category.assoc _ _ _).symm

def matrixProjectiveMap (ι : Fin 3 ↪ Fin 6) :
    (matrixCover K).X ι ⟶ projectiveSpaceAtUniverse.{u} 13 :=
  chartProjectiveMap K ((matrixCover K).f ι) ι (matrixChartIntegral K ι)
    (matrixChartIntegral_diagram K ι)

theorem matrixProjectiveMap_compat (ι κ : Fin 3 ↪ Fin 6) :
    pullback.fst ((matrixCover K).f ι) ((matrixCover K).f κ) ≫ matrixProjectiveMap K ι=
      pullback.snd _ _ ≫ matrixProjectiveMap K κ := by
  let ti := pullback.fst ((matrixCover K).f ι) ((matrixCover K).f κ)
  let tj := pullback.snd ((matrixCover K).f ι) ((matrixCover K).f κ)
  have hi : ((ti ≫ (matrixCover K).f ι) ≫ inclusion K) ≫ pullback.snd _ _=
      (ti ≫ matrixChartIntegral K ι) ≫ chart 3 6 ι := by
    simpa only [Category.assoc] using congrArg (fun h => ti ≫ h) (matrixChartIntegral_diagram K ι)
  have hj : ((tj ≫ (matrixCover K).f κ) ≫ inclusion K) ≫ pullback.snd _ _=
      (tj ≫ matrixChartIntegral K κ) ≫ chart 3 6 κ := by
    simpa only [Category.assoc] using congrArg (fun h => tj ≫ h) (matrixChartIntegral_diagram K κ)
  have hcommon : ti ≫ (matrixCover K).f ι=tj ≫ (matrixCover K).f κ := pullback.condition
  calc
    _ = chartProjectiveMap K (ti ≫ (matrixCover K).f ι) ι (ti ≫ matrixChartIntegral K ι) hi :=
      comp_chartProjectiveMap K _ ι _ (matrixChartIntegral_diagram K ι) ti hi
    _ = chartProjectiveMap K (tj ≫ (matrixCover K).f κ) κ (tj ≫ matrixChartIntegral K κ) hj := by
      have hj' : ((ti ≫ (matrixCover K).f ι) ≫ inclusion K) ≫ pullback.snd _ _=
          (tj ≫ matrixChartIntegral K κ) ≫ chart 3 6 κ := by
        simpa only [hcommon] using hj
      simpa only [← hcommon] using chartProjectiveMap_compat K
        (ti ≫ (matrixCover K).f ι) ι κ (ti ≫ matrixChartIntegral K ι)
        (tj ≫ matrixChartIntegral K κ) hi hj'
    _ = _ := (comp_chartProjectiveMap K _ κ _ (matrixChartIntegral_diagram K κ) tj hj).symm

/-- The genuine primitive Plucker morphism, glued from actual native
quotient charts over their genuine overlaps. -/
def integralPrimitivePlucker :
    M9Native.LagrangianGrassmannian.space K ⟶ projectiveSpaceAtUniverse.{u} 13 :=
  (matrixCover K).glueMorphisms (matrixProjectiveMap K) (matrixProjectiveMap_compat K)

@[reassoc (attr := simp)] theorem matrixCover_comp_integralPrimitivePlucker (ι : Fin 3 ↪ Fin 6) :
    (matrixCover K).f ι ≫ integralPrimitivePlucker K=matrixProjectiveMap K ι :=
  (matrixCover K).ι_glueMorphisms _ _ ι

/-- The actual primitive Plucker morphism over the actual base field. -/
def primitivePlucker :
    M9Native.LagrangianGrassmannian.space K ⟶ projectiveSpaceOver 13 (Spec (.of K)) :=
  pullback.lift (projection K) (integralPrimitivePlucker K) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem primitivePlucker_projection :
    primitivePlucker K ≫ pullback.fst _ _=projection K := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem primitivePlucker_toIntegral :
    primitivePlucker K ≫ pullback.snd _ _=integralPrimitivePlucker K := pullback.lift_snd _ _ _



/-- The global glued morphism has the literal fourteen quotient-minor
coordinates for every test-scheme morphism landing in a native chart. -/
theorem comp_integralPrimitivePlucker {T : Scheme.{u}}
    (f : T ⟶ M9Native.LagrangianGrassmannian.space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    f ≫ integralPrimitivePlucker K=chartProjectiveMap K f ι g hfg := by
  let gK : T ⟶ M9Native.GrassmannianCharts.chartSpace K 3 6 ι :=
    pullback.lift (f ≫ projection K) g (terminal.hom_ext _ _)
  have hgK : gK ≫ M9Native.GrassmannianCharts.chartOver K 3 6 ι=f ≫ inclusion K := by
    apply pullback.hom_ext
    · simp only [Category.assoc,M9Native.GrassmannianCharts.chartOver_projection,gK,pullback.lift_fst]
    · simpa only [Category.assoc,M9Native.GrassmannianCharts.chartOver_toIntegral,gK,
        pullback.lift_snd_assoc] using hfg.symm
  let l : T ⟶ (matrixCover K).X ι := pullback.lift f gK hgK.symm
  have hl : l ≫ (matrixCover K).f ι=f := pullback.lift_fst _ _ _
  have hlC : l ≫ (M9Native.GrassmannianCharts.matrixCover K 3 6).pullbackHom
      (inclusion K) ι=gK := pullback.lift_snd _ _ _
  have hg : gK ≫ AffineSpace.toSpecMvPoly (ChartIndex.{u} (k:=3) (n:=6) ι)
      (Spec (.of K))=g := pullback.lift_snd _ _ _
  have hlg : l ≫ matrixChartIntegral K ι=g :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫
      AffineSpace.toSpecMvPoly (ChartIndex.{u} (k:=3) (n:=6) ι) (Spec (.of K))) hlC).trans hg)
  have hcomp : ((l ≫ (matrixCover K).f ι) ≫ inclusion K) ≫ pullback.snd _ _=
      (l ≫ matrixChartIntegral K ι) ≫ chart 3 6 ι := by
    simpa only [Category.assoc] using congrArg (fun q => l ≫ q) (matrixChartIntegral_diagram K ι)
  calc
    _ = (l ≫ (matrixCover K).f ι) ≫ integralPrimitivePlucker K :=
      congrArg (fun q => q ≫ integralPrimitivePlucker K) hl.symm
    _ = l ≫ matrixProjectiveMap K ι := by
      rw [Category.assoc,matrixCover_comp_integralPrimitivePlucker]
    _ = _ := by
      simpa only [matrixProjectiveMap,hl,hlg] using comp_chartProjectiveMap K
        ((matrixCover K).f ι) ι (matrixChartIntegral K ι) (matrixChartIntegral_diagram K ι) l hcomp

end M9Native.LagrangianPlucker
