module

public import M9StacksIntegration.SL3FamilyFreeAction
public import M9StacksIntegration.SL3CoordinateBaseChange
public import M9StacksIntegration.PrimitiveUniversalFieldAction

@[expose] public section

/-! The genuine varying connected stabilizer family on the original native
Gr4(12), evaluated at the original generic point. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
open scoped TensorProduct

namespace M9Native.SL3UniversalFieldAction

open AlgebraicGeometry.Grassmannian
open PrimitiveUniversalFieldAction (algebraSpecOver algebraSpecOver_comp algebraSpecOver_id)

abbrev space : Scheme := ReducedGraphAction.space ℂ
abbrev projection : space ⟶ SL3FamilyFreeAction.base := GrassmannianCharts.projection ℂ 4 12
abbrev overSpace : Over SL3FamilyFreeAction.base := Over.mk projection
abbrev A := SL3CoordinateRing.CoordinateRing ℂ
abbrev E := space.functionField
abbrev TensorRing := A ⊗[ℂ] E
abbrev parameter : Scheme := Spec (.of TensorRing)
abbrev fieldOver : Over SL3FamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ E)
abbrev parameterOver : Over SL3FamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ TensorRing)

instance parameter_isDomain : IsDomain TensorRing :=
  (Algebra.TensorProduct.comm ℂ A E).toRingEquiv.isDomain_iff.mpr inferInstance

def genericOverPoint : fieldOver ⟶ overSpace :=
  NativeGenericFieldPoints.overPoint ℂ projection rfl (AlgHom.id ℂ E)

theorem genericOverPoint_left : genericOverPoint.left = NativeFunctionFieldFunctor.genericSpec space := by
  change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ NativeFunctionFieldFunctor.genericSpec space = _
  change Spec.map (𝟙 space.functionField) ≫ NativeFunctionFieldFunctor.genericSpec space = _
  exact (congrArg (fun q : Spec space.functionField ⟶ Spec space.functionField =>
    q ≫ NativeFunctionFieldFunctor.genericSpec space) (Spec.map_id space.functionField)).trans
      (Category.id_comp _)

def universalGroupMatrix : Matrix.SpecialLinearGroup (Fin 3) TensorRing :=
  SL3CoordinateRing.homEquiv ℂ (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing)

def universalMatrix : Matrix.SpecialLinearGroup (Fin 3) Γ(parameter, ⊤) :=
  Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of TensorRing)).inv.hom universalGroupMatrix

def universalX : parameterOver ⟶ overSpace :=
  algebraSpecOver (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) ≫ genericOverPoint

def projectionMap : parameter ⟶ space := universalX.left

def actionMap : parameter ⟶ space :=
  GraphGrassmannianLinearAction.classify ℂ parameterOver.hom
    (SL3FamilyFreeAction.transformPoints parameterOver universalMatrix
      (GraphGrassmannianLinearAction.pointClass ℂ projectionMap))

def actionOver : parameterOver ⟶ overSpace :=
  Over.homMk actionMap (GraphGrassmannianLinearAction.classify_projection ℂ _ _)

theorem action_pointClass :
    GraphGrassmannianLinearAction.pointClass ℂ actionMap =
      SL3FamilyFreeAction.transformPoints parameterOver universalMatrix
        (GraphGrassmannianLinearAction.pointClass ℂ projectionMap) :=
  GraphGrassmannianLinearAction.classify_class ℂ _ _

theorem action_pointClass_natural {T : Over SL3FamilyFreeAction.base} (p : T ⟶ parameterOver) :
    GraphGrassmannianLinearAction.pointClass ℂ (p.left ≫ actionMap) =
      SL3FamilyFreeAction.transformPoints T (Matrix.SpecialLinearGroup.map p.left.appTop.hom universalMatrix)
        (GraphGrassmannianLinearAction.pointClass ℂ (p.left ≫ projectionMap)) := by
  rw [GraphGrassmannianLinearAction.pointClass_comp, action_pointClass,
    SL3FamilyFreeAction.transformPoints_natural, ← GraphGrassmannianLinearAction.pointClass_comp]

/-- Native spectrum/global-section naturality gives the literal matrix,
over arbitrary commutative rings. -/
theorem specMap_matrix {R S : Type} [CommRing R] [CommRing S]
    (ρ : R →+* S) (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.SpecialLinearGroup.map (Spec.map (CommRingCat.ofHom ρ)).appTop.hom
      (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of R)).inv.hom g) =
      Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of S)).inv.hom
        (Matrix.SpecialLinearGroup.map ρ g) := by
  apply Subtype.ext
  ext i j
  exact congrArg (fun q : CommRingCat.of R ⟶ Γ(Spec (.of S), ⊤) => q (g.val i j))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)).symm

def slice (χ : A →ₐ[ℂ] ℂ) : fieldOver ⟶ parameterOver :=
  algebraSpecOver (TensorEvaluationSeparation.algebraEvaluate (E := E) χ)

theorem slice_projection (χ : A →ₐ[ℂ] ℂ) : slice χ ≫ universalX = genericOverPoint := by
  rw [slice, universalX, ← Category.assoc, algebraSpecOver_comp]
  have he : (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).comp
      (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) = AlgHom.id ℂ E := by
    ext e
    simp
  rw [he, algebraSpecOver_id, Category.id_comp]

theorem slice_projection_left (χ : A →ₐ[ℂ] ℂ) :
    (slice χ).left ≫ projectionMap = NativeFunctionFieldFunctor.genericSpec space := by
  exact (congrArg (fun q : fieldOver ⟶ overSpace => q.left) (slice_projection χ)).trans
    genericOverPoint_left

abbrev overField (L : Type) [Field L] [Algebra ℂ L] : Over SL3FamilyFreeAction.base :=
  Over.mk (Sp6AffineBaseChange.specAlgebraMap ℂ L)

theorem scalarMap_spec {L : Type} [Field L] [Algebra ℂ L] :
    SL3FamilyFreeAction.scalarMap (overField L) =
      (Scheme.ΓSpecIso (.of L)).inv.hom.comp (algebraMap ℂ L) := by
  ext c
  exact congrArg (fun q : CommRingCat.of ℂ ⟶ Γ(Spec (.of L), ⊤) => q c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ L))).symm

variable {L : Type} [Field L] [Algebra ℂ L]

def parameterAlgebra (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    TensorRing →ₐ[ℂ] L :=
  Algebra.TensorProduct.lift (SL3CoordinateRing.evaluation ℂ g) s
    (fun _ _ => Commute.all _ _)

theorem parameterAlgebra_left (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    (parameterAlgebra g s).comp (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing) =
      SL3CoordinateRing.evaluation ℂ g := by
  ext a
  simp [parameterAlgebra]

theorem parameterAlgebra_right (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    (parameterAlgebra g s).comp (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing) = s := by
  ext e
  simp [parameterAlgebra]

def parameterPoint (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    overField L ⟶ parameterOver := algebraSpecOver (parameterAlgebra g s)

theorem parameterPoint_projection (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    parameterPoint g s ≫ universalX = NativeGenericFieldPoints.overPoint ℂ projection rfl s := by
  rw [parameterPoint, universalX, ← Category.assoc, algebraSpecOver_comp, parameterAlgebra_right]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ genericOverPoint.left =
    Spec.map (CommRingCat.ofHom s.toRingHom) ≫ NativeFunctionFieldFunctor.genericSpec space
  exact congrArg (fun q : fieldOver.left ⟶ space => Spec.map (CommRingCat.ofHom s.toRingHom) ≫ q)
    genericOverPoint_left

theorem parameterPoint_projection_left (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    (parameterPoint g s).left ≫ projectionMap = NativeGenericPullbackEvaluation.point s.toRingHom :=
  congrArg (fun q : overField L ⟶ overSpace => q.left) (parameterPoint_projection g s)

theorem parameterAlgebra_groupMatrix (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    Matrix.SpecialLinearGroup.map (parameterAlgebra g s).toRingHom universalGroupMatrix = g := by
  rw [universalGroupMatrix, ← SL3CoordinateRing.homEquiv_comp, parameterAlgebra_left]
  exact (SL3CoordinateRing.homEquiv ℂ).apply_symm_apply g

theorem parameterPoint_matrix (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    Matrix.SpecialLinearGroup.map (parameterPoint g s).left.appTop.hom universalMatrix =
      Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g := by
  have h := specMap_matrix (parameterAlgebra g s).toRingHom universalGroupMatrix
  rw [parameterAlgebra_groupMatrix] at h
  exact h

theorem parameterPoint_action_class (g : Matrix.SpecialLinearGroup (Fin 3) L) (s : E →ₐ[ℂ] L) :
    GraphGrassmannianLinearAction.pointClass ℂ ((parameterPoint g s).left ≫ actionMap) =
      SL3FamilyFreeAction.transformPoints (overField L)
        (Matrix.SpecialLinearGroup.map (Scheme.ΓSpecIso (.of L)).inv.hom g)
          (GraphGrassmannianLinearAction.pointClass ℂ (NativeGenericPullbackEvaluation.point s.toRingHom)) := by
  rw [action_pointClass_natural, parameterPoint_matrix, parameterPoint_projection_left]

end M9Native.SL3UniversalFieldAction
