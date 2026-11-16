module

public import M9StacksIntegration.Sp6GaussBaseChart
public import M9StacksIntegration.Sp6AdmissibleCellMatrices
public import M9StacksIntegration.GroupObjectRightTranslation

/-! Eight genuine Gauss open charts of the original symplectic group. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace M9Native.Sp6GaussTranslatedCharts

open LagrangianAdmissibleMinors (Choice)

section Matrices

variable {R S : Type u} [CommRing R] [CommRing S]

theorem map_swap (ρ : R →+* S) (s : Choice) :
    Sp6GroupScheme.mapMatrix ρ (LagrangianAdmissibleCharts.swap R s) =
      LagrangianAdmissibleCharts.swap S s := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    by_cases hij : i = j
    · subst j
      by_cases hs : s i <;>
        simp [Sp6GroupScheme.mapMatrix, LagrangianAdmissibleCharts.swap,
          LagrangianAdmissibleCharts.swapMatrix, Matrix.fromBlocks,
          LagrangianAdmissibleCharts.keep, LagrangianAdmissibleCharts.take, hs]
    · simp [Sp6GroupScheme.mapMatrix, LagrangianAdmissibleCharts.swap,
        LagrangianAdmissibleCharts.swapMatrix, Matrix.fromBlocks, Matrix.diagonal, hij]

theorem map_commonMatrix (ρ : R →+* S) :
    Sp6GroupScheme.mapMatrix ρ (Sp6AdmissibleCellMatrices.commonMatrix R) =
      Sp6AdmissibleCellMatrices.commonMatrix S := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    by_cases hij : i = j <;>
      simp [Sp6GroupScheme.mapMatrix, Sp6AdmissibleCellMatrices.commonMatrix,
        PrimitiveGaussFamily.upper, Matrix.fromBlocks, hij]

theorem isUnit_topLeft_map (ρ : R →+* S)
    (g : Matrix.symplecticGroup (Fin 3) R) (hg : IsUnit g.val.toBlocks₁₁.det) :
    IsUnit (Sp6GroupScheme.mapMatrix ρ g).val.toBlocks₁₁.det := by
  have hd : ρ g.val.toBlocks₁₁.det =
      (Sp6GroupScheme.mapMatrix ρ g).val.toBlocks₁₁.det :=
    RingHom.map_det ρ _
  exact hd ▸ hg.map ρ

end Matrices

section BaseRing

variable (K : Type u) [CommRing K]

abbrev source : Scheme.{u} := Sp6GaussBaseChart.source K
abbrev group : Scheme.{u} := Sp6GaussBaseChart.group K

def swapPoint (s : Choice) :
    𝟙_ (Over (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K)) :=
  Sp6GroupScheme.constantPoint K (LagrangianAdmissibleCharts.swap K s)

def rightSwap (s : Choice) :
    Sp6GroupScheme.obj (Spec (.of K)) ≅ Sp6GroupScheme.obj (Spec (.of K)) :=
  GroupObjectRightTranslation.rightTranslation (swapPoint K s)

def rightSwapScheme (s : Choice) : group K ≅ group K :=
  (Over.forget (Spec (.of K))).mapIso (rightSwap K s)

def chart (s : Choice) : source K ⟶ group K :=
  Sp6GaussBaseChart.chart K ≫ (rightSwapScheme K s).inv

def overChart (s : Choice) :
    Over.mk (Sp6GaussBaseChart.projection K) ⟶ Sp6GroupScheme.obj (Spec (.of K)) :=
  Sp6GaussBaseChart.overChart K ≫ (rightSwap K s).inv

@[simp] theorem overChart_left (s : Choice) : (overChart K s).left = chart K s := rfl

instance chart_isOpenImmersion (s : Choice) : IsOpenImmersion (chart K s) := by
  dsimp [chart]
  infer_instance

@[reassoc] theorem chart_projection (s : Choice) :
    chart K s ≫ (Sp6GroupScheme.obj (Spec (.of K))).hom =
      Sp6GaussBaseChart.projection K := (overChart K s).w

/-- Right translation acts by the literal signed-column-swap matrix on
all actual test-scheme points. -/
theorem pointsMulEquiv_rightSwap {T : Over (Spec (.of K))}
    (p : T ⟶ Sp6GroupScheme.obj (Spec (.of K))) (s : Choice) :
    Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T (p ≫ (rightSwap K s).hom) =
      Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T p *
        LagrangianAdmissibleCharts.swap Γ(T.left,⊤) s := by
  have hc : Sp6GroupScheme.pointsMulEquiv (Spec (.of K))
      (𝟙_ (Over (Spec (.of K)))) (swapPoint K s) =
      Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of K)).inv.hom
        (LagrangianAdmissibleCharts.swap K s) :=
    Sp6GroupScheme.pointsMulEquiv_constantPoint K (LagrangianAdmissibleCharts.swap K s)
  rw [rightSwap, GroupObjectRightTranslation.comp_rightTranslation,
    Sp6GroupScheme.pointsMulEquiv_mul, Sp6GroupScheme.pointsMulEquiv_natural]
  rw [hc, map_swap]
  exact congrArg
    (fun q : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤) =>
      Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T p * q)
    (map_swap T.hom.appTop.hom s)

/-- An actual unit swapped minor gives an actual factorization through
its particular translated Gauss open. -/
theorem exists_overChart_factor {T : Over (Spec (.of K))}
    (p : T ⟶ Sp6GroupScheme.obj (Spec (.of K))) (s : Choice)
    (hp : IsUnit ((Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T p) *
      LagrangianAdmissibleCharts.swap Γ(T.left,⊤) s).val.toBlocks₁₁.det) :
    ∃ z : T ⟶ Over.mk (Sp6GaussBaseChart.projection K), z ≫ overChart K s = p := by
  have hu : IsUnit (Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T
      (p ≫ (rightSwap K s).hom)).val.toBlocks₁₁.det := by
    rw [pointsMulEquiv_rightSwap]
    exact hp
  obtain ⟨z,hz⟩ := Sp6GaussBaseChart.exists_overChart_factor K
    (p ≫ (rightSwap K s).hom) hu
  refine ⟨z,?_⟩
  rw [overChart, ← Category.assoc, hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end BaseRing

section Fields

variable (K : Type u) [Field K]

/-- Every extension-field-valued point factors through one of the
actual eight open charts, without an algebraic-closure assumption. -/
theorem exists_chart_factor_point (L : Type u) [Field L] (p : Spec (.of L) ⟶ group K) :
    ∃ (s : Choice) (z : Spec (.of L) ⟶ source K), z ≫ chart K s = p := by
  let T : Over (Spec (.of K)) := Over.mk (p ≫ (Sp6GroupScheme.obj (Spec (.of K))).hom)
  let p' : T ⟶ Sp6GroupScheme.obj (Spec (.of K)) := Over.homMk p rfl
  let gΓ : Matrix.symplecticGroup (Fin 3) Γ(Spec (.of L),⊤) :=
    Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T p'
  let ρ := (Scheme.ΓSpecIso (.of L)).hom.hom
  let τ := (Scheme.ΓSpecIso (.of L)).inv.hom
  let g := Sp6GroupScheme.mapMatrix ρ gΓ
  obtain ⟨s,hs⟩ := Sp6AdmissibleCellMatrices.exists_unit_topLeft_after_swap g
  have hg : Sp6GroupScheme.mapMatrix τ (g * LagrangianAdmissibleCharts.swap L s) =
      gΓ * LagrangianAdmissibleCharts.swap Γ(Spec (.of L),⊤) s := by
    rw [map_mul, map_swap]
    congr 1
    apply Subtype.ext
    ext i j
    exact (Scheme.ΓSpecIso (.of L)).hom_inv_id_apply (gΓ.val i j)
  have hu := isUnit_topLeft_map τ (g * LagrangianAdmissibleCharts.swap L s) hs
  rw [hg] at hu
  obtain ⟨z,hz⟩ := exists_overChart_factor K p' s hu
  refine ⟨s,z.left,?_⟩
  exact congrArg (fun q => q.left) hz

/-- The literal upper(I) constant point lies in all eight actual cells. -/
theorem exists_common_chart_point :
    ∃ p : Spec (.of K) ⟶ group K, ∀ s : Choice,
      ∃ z : Spec (.of K) ⟶ source K, z ≫ chart K s = p := by
  let p := Sp6GroupScheme.constantPoint K (Sp6AdmissibleCellMatrices.commonMatrix K)
  refine ⟨p.left, fun s => ?_⟩
  let gΓ : Matrix.symplecticGroup (Fin 3) Γ(Spec (.of K),⊤) :=
    Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) (Over.mk (𝟙 _)) p
  have hg : gΓ = Sp6AdmissibleCellMatrices.commonMatrix Γ(Spec (.of K),⊤) := by
    dsimp only [gΓ,p]
    rw [Sp6GroupScheme.pointsMulEquiv_constantPoint, map_commonMatrix]
  have hu : IsUnit (gΓ * LagrangianAdmissibleCharts.swap Γ(Spec (.of K),⊤) s).val.toBlocks₁₁.det := by
    rw [hg]
    exact Sp6AdmissibleCellMatrices.commonMatrix_unit_all _ s
  obtain ⟨z,hz⟩ := exists_overChart_factor K p s hu
  exact ⟨z.left,congrArg (fun q => q.left) hz⟩

theorem exists_point_in_all_charts :
    ∃ x : group K, ∀ s : Choice, x ∈ Set.range (chart K s) := by
  obtain ⟨p,hp⟩ := exists_common_chart_point K
  refine ⟨p (IsLocalRing.closedPoint K),fun s => ?_⟩
  obtain ⟨z,hz⟩ := hp s
  exact ⟨z (IsLocalRing.closedPoint K),
    congrArg (fun f : Spec (.of K) ⟶ group K => f (IsLocalRing.closedPoint K)) hz⟩

theorem charts_cover (x : group K) : ∃ s : Choice,x ∈ Set.range (chart K s) := by
  obtain ⟨s,z,hz⟩ := exists_chart_factor_point K ((group K).residueField x)
    ((group K).fromSpecResidueField x)
  refine ⟨s,z (IsLocalRing.closedPoint ((group K).residueField x)),?_⟩
  exact (congrArg (fun f : Spec (.of ((group K).residueField x)) ⟶ group K =>
    f (IsLocalRing.closedPoint ((group K).residueField x))) hz).trans
      ((group K).fromSpecResidueField_apply x _)

def admissibleCover : (group K).OpenCover :=
  Scheme.Cover.mkOfCovers Choice (fun _ => source K) (chart K)
    (fun x => by obtain ⟨s,y,hy⟩ := charts_cover K x; exact ⟨s,y,hy⟩)

end Fields

end M9Native.Sp6GaussTranslatedCharts
