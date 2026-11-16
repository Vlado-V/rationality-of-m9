module

public import M9StacksIntegration.GrassmannianCharts
public import M9StacksIntegration.LagrangianFreeMatrixPullback
public import M9StacksIntegration.NativeFunctionFieldFunctor
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

/-! Actual constant linear change of ambient six-space on the native
four-plane Grassmannian, constructed through its genuine quotient functor. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.GrassmannianLinearAction

open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianFreeMatrixPullback M9Native.LagrangianGrassmannian
open M9Native.LagrangianMatrixChart

variable (K : Type u) [Field K]

abbrev GL6 := Matrix.GeneralLinearGroup (Fin 6) K
abbrev space := GrassmannianCharts.space K 4 6
abbrev projection := GrassmannianCharts.projection K 4 6

def scalarMap {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) : K →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop).hom

theorem scalarMap_comp {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S) :
    scalarMap K (f ≫ b) = f.appTop.hom.comp (scalarMap K b) := by
  ext c
  rfl

def constantMatrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K) :
    Matrix (Fin 6) (Fin 6) Γ(T, ⊤) := g.val.map (scalarMap K b)

def constantFreeIso {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K) :
    freeOn T 6 ≅ freeOn T 6 where
  hom := Stacks.FreeSheafMatrix.ofMatrix (constantMatrix K b g)
  inv := Stacks.FreeSheafMatrix.ofMatrix (constantMatrix K b g⁻¹)
  hom_inv_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    change (g⁻¹).val.map (scalarMap K b) * g.val.map (scalarMap K b) = 1
    rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_hom_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    change g.val.map (scalarMap K b) * (g⁻¹).val.map (scalarMap K b) = 1
    rw [← Matrix.map_mul, Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem constantFreeIso_matrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K) :
    Stacks.FreeSheafMatrix.toMatrix (constantFreeIso K b g).hom = constantMatrix K b g :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

theorem constantFreeIso_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) :
    (constantFreeIso K b 1).hom = 𝟙 (freeOn T 6) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [constantFreeIso_matrix, Stacks.FreeSheafMatrix.toMatrix_id]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem constantFreeIso_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL6 K) :
    (constantFreeIso K b (g * h)).hom =
      (constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, constantFreeIso_matrix,
    constantFreeIso_matrix, constantFreeIso_matrix]
  exact Matrix.map_mul

theorem constantFreeIso_pullback {S T : Scheme.{u}} (b : S ⟶ Spec (.of K))
    (f : T ⟶ S) (g : GL6 K) :
    pulledFreeEnd f (constantFreeIso K b g).hom = (constantFreeIso K (f ≫ b) g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [pulledFreeEnd_matrix, constantFreeIso_matrix, constantFreeIso_matrix]
  ext i j
  change f.appTop (scalarMap K b (g.val i j)) = scalarMap K (f ≫ b) (g.val i j)
  rw [scalarMap_comp]
  rfl

theorem constantFreeIso_pullback_inv {S T : Scheme.{u}} (b : S ⟶ Spec (.of K))
    (f : T ⟶ S) (g : GL6 K) :
    (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map (constantFreeIso K b g).hom =
      (constantFreeIso K (f ≫ b) g).hom ≫ (pullbackFreeIso f 6).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f 6).inv)
    (constantFreeIso_pullback K b f g)
  simp only [pulledFreeEnd, Category.assoc] at h
  rw [(pullbackFreeIso f 6).hom_inv_id, Category.comp_id] at h
  exact h

def transform {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K)
    (q : QuotientPresentation T 4 6) : QuotientPresentation T 4 6 := by
  letI : Epi q.map := q.map_epi
  exact { target := q.target
          map := (constantFreeIso K b g).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K)
    {q q' : QuotientPresentation T 4 6} (h : q.Isomorphic q') :
    (transform K b g q).Isomorphic (transform K b g q') := by
  obtain ⟨e,he⟩ := h
  refine ⟨e, ?_⟩
  change ((constantFreeIso K b g).hom ≫ q.map) ≫ e.hom =
    (constantFreeIso K b g).hom ≫ q'.map
  rw [Category.assoc, he]

theorem transform_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (q : QuotientPresentation T 4 6) : (transform K b 1 q).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change ((constantFreeIso K b 1).hom ≫ q.map) ≫ 𝟙 _ = q.map
  rw [constantFreeIso_one, Category.id_comp, Category.comp_id]

theorem transform_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL6 K)
    (q : QuotientPresentation T 4 6) :
    (transform K b h (transform K b g q)).Isomorphic (transform K b (g * h) q) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom ≫ q.map) ≫ 𝟙 _ =
    (constantFreeIso K b (g * h)).hom ≫ q.map
  rw [Category.comp_id, constantFreeIso_mul, Category.assoc]

theorem pullback_transform {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : GL6 K) (q : QuotientPresentation S 4 6) :
    (pullbackPresentation f (transform K b g q)).Isomorphic
      (transform K (f ≫ b) g (pullbackPresentation f q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f 6).inv ≫
    (Scheme.Modules.pullback f).map ((constantFreeIso K b g).hom ≫ q.map)) ≫ 𝟙 _ =
      (constantFreeIso K (f ≫ b) g).hom ≫
        (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q.map
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc,
    constantFreeIso_pullback_inv, Category.assoc]

def transformPoints {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL6 K) :
    Points T 4 6 → Points T 4 6 :=
  Quotient.lift (fun q => (⟦transform K b g q⟧ : Points T 4 6)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic K b g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (x : Points T 4 6) :
    transformPoints K b 1 x = x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one K b q))

theorem transformPoints_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL6 K)
    (x : Points T 4 6) :
    transformPoints K b h (transformPoints K b g x) = transformPoints K b (g * h) x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_mul K b g h q))

theorem transformPoints_natural {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : GL6 K) (x : Points S 4 6) :
    pullbackPointsMap f 4 6 (transformPoints K b g x) =
      transformPoints K (f ≫ b) g (pullbackPointsMap f 4 6 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform K b f g q))

def pointClass {T : Scheme.{u}} (f : T ⟶ space K) : Points T 4 6 :=
  (functorData 4 6).objEquiv T ((schemeRepresentableBy 4 6).homEquiv
    (f ≫ GrassmannianCharts.toIntegral K 4 6))

theorem pointClass_comp {S T : Scheme.{u}} (f : T ⟶ S) (p : S ⟶ space K) :
    pointClass K (f ≫ p) = pullbackPointsMap f 4 6 (pointClass K p) := by
  have h := M9Native.LagrangianGrassmannian.pointsEquiv_map f 4 6
    ((schemeRepresentableBy 4 6).homEquiv (p ≫ GrassmannianCharts.toIntegral K 4 6))
  rw [← (schemeRepresentableBy 4 6).homEquiv_comp] at h
  simpa only [pointClass, Category.assoc] using h

def classify {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T 4 6) : T ⟶ space K :=
  pullback.lift p ((schemeRepresentableBy 4 6).homEquiv.symm
    (((functorData 4 6).objEquiv T).symm x)) (terminal.hom_ext _ _)

@[reassoc] theorem classify_projection {T : Scheme.{u}} (p : T ⟶ Spec (.of K))
    (x : Points T 4 6) : classify K p x ≫ projection K = p := pullback.lift_fst _ _ _

theorem classify_class {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T 4 6) :
    pointClass K (classify K p x) = x := by
  simp only [pointClass, classify, GrassmannianCharts.toIntegral, pullback.lift_snd,
    Equiv.apply_symm_apply]

theorem hom_ext {T : Scheme.{u}} (f h : T ⟶ space K)
    (hb : f ≫ projection K = h ≫ projection K) (hc : pointClass K f = pointClass K h) : f = h := by
  apply pullback.hom_ext
  · exact hb
  · apply (schemeRepresentableBy 4 6).homEquiv.injective
    apply ((functorData 4 6).objEquiv T).injective
    exact hc

/-- Precomposition of the universal quotient by the actual constant matrix. -/
def action (g : GL6 K) : space K ⟶ space K :=
  classify K (projection K) (transformPoints K (projection K) g (pointClass K (𝟙 _)))

@[reassoc] theorem action_projection (g : GL6 K) : action K g ≫ projection K = projection K :=
  classify_projection _ _ _

theorem action_class (g : GL6 K) :
    pointClass K (action K g) = transformPoints K (projection K) g (pointClass K (𝟙 _)) :=
  classify_class _ _ _

/-- The action is realized on the actual quotient class over every test scheme. -/
theorem pointClass_action {T : Scheme.{u}} (p : T ⟶ space K) (g : GL6 K) :
    pointClass K (p ≫ action K g) =
      transformPoints K (p ≫ projection K) g (pointClass K p) := by
  rw [pointClass_comp, action_class, transformPoints_natural]
  have hp : pullbackPointsMap p 4 6 (pointClass K (𝟙 (space K))) = pointClass K p := by
    simpa only [Category.comp_id] using (pointClass_comp K p (𝟙 (space K))).symm
  rw [hp]

theorem action_one : action K 1 = 𝟙 (space K) := by
  apply hom_ext K
  · rw [action_projection, Category.id_comp]
  · rw [action_class, transformPoints_one]

theorem action_mul (g h : GL6 K) : action K g ≫ action K h = action K (g * h) := by
  apply hom_ext K
  · rw [Category.assoc, action_projection, action_projection, action_projection]
  · rw [pointClass_action, action_projection, action_class, action_class, transformPoints_mul]

def rightAutomorphism (g : GL6 K) : space K ≅ space K where
  hom := action K g
  inv := action K g⁻¹
  hom_inv_id := by rw [action_mul, mul_inv_cancel, action_one]
  inv_hom_id := by rw [action_mul, inv_mul_cancel, action_one]

instance action_isIso (g : GL6 K) : IsIso (action K g) :=
  (rightAutomorphism K g).isIso_hom

instance action_isDominant (g : GL6 K) : IsDominant (action K g) :=
  ⟨(action K g).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- Pullback on the actual native generic stalk of the Grassmannian. -/
def fieldAutomorphism (g : GL6 K) : (space K).functionField ≃ₐ[K] (space K).functionField := by
  let e := GrassmannianCharts.openImmersionFunctionFieldIso (action K g)
  refine { __ := e.commRingCatIsoToRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (action K g) (projection K)
  rw [action_projection] at h
  exact DFunLike.congr_fun h c

theorem fieldAutomorphism_eq_map (g : GL6 K) :
    (fieldAutomorphism K g).toRingHom = NativeDominantFunctionField.map (action K g) := by
  change (GrassmannianCharts.openImmersionFunctionFieldIso (action K g)).hom.hom = _
  simp only [GrassmannianCharts.openImmersionFunctionFieldIso, NativeDominantFunctionField.map,
    Iso.trans_hom, asIso_hom]

theorem dominantMap_congr {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    NativeDominantFunctionField.map f = NativeDominantFunctionField.map g := by
  subst g
  rfl

theorem fieldAutomorphism_one : fieldAutomorphism K 1 = 1 := by
  apply AlgEquiv.ext
  intro x
  change (fieldAutomorphism K 1).toRingHom x = x
  rw [fieldAutomorphism_eq_map, dominantMap_congr (action_one K), NativeFunctionFieldFunctor.map_id]
  rfl

theorem fieldAutomorphism_mul (g h : GL6 K) :
    fieldAutomorphism K (g * h) = fieldAutomorphism K g * fieldAutomorphism K h := by
  apply AlgEquiv.ext
  intro x
  change (fieldAutomorphism K (g * h)).toRingHom x =
    (fieldAutomorphism K g).toRingHom ((fieldAutomorphism K h).toRingHom x)
  rw [fieldAutomorphism_eq_map, fieldAutomorphism_eq_map, fieldAutomorphism_eq_map,
    dominantMap_congr (action_mul K g h).symm, NativeFunctionFieldFunctor.map_comp]
  rfl

/-- The genuine constant ambient-linear field action. -/
def fieldRepresentation : GL6 K →* ((space K).functionField ≃ₐ[K] (space K).functionField) where
  toFun := fieldAutomorphism K
  map_one' := fieldAutomorphism_one K
  map_mul' := fieldAutomorphism_mul K

end M9Native.GrassmannianLinearAction
