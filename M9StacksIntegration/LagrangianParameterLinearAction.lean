module

public import M9StacksIntegration.GrassmannianCharts
public import M9StacksIntegration.PrimitiveFreeMatrixPullback
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

/-! Actual constant GL14 changes of the original native Gr9(14) parameter,
constructed through its genuine quotient functor. This is the parameter
automorphism used to retain the raw/original primitive coordinate change;
it asserts no family or classifier invariance. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.LagrangianParameterLinearAction

open AlgebraicGeometry.Grassmannian
open M9Native.PrimitiveFreeMatrixPullback M9Native.LagrangianGrassmannian
open M9Native.LagrangianMatrixChart

variable (K : Type u) [Field K]

abbrev GL14 := Matrix.GeneralLinearGroup (Fin 14) K
abbrev space := GrassmannianCharts.space K 9 14
abbrev projection := GrassmannianCharts.projection K 9 14

def scalarMap {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) : K →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop).hom

theorem scalarMap_comp {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S) :
    scalarMap K (f ≫ b) = f.appTop.hom.comp (scalarMap K b) := by
  ext c
  rfl

def constantMatrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K) :
    Matrix (Fin 14) (Fin 14) Γ(T, ⊤) := g.val.map (scalarMap K b)

def constantFreeIso {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K) :
    freeOn T 14 ≅ freeOn T 14 where
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

theorem constantFreeIso_matrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K) :
    Stacks.FreeSheafMatrix.toMatrix (constantFreeIso K b g).hom = constantMatrix K b g :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

theorem constantFreeIso_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) :
    (constantFreeIso K b 1).hom = 𝟙 (freeOn T 14) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [constantFreeIso_matrix, Stacks.FreeSheafMatrix.toMatrix_id]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem constantFreeIso_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL14 K) :
    (constantFreeIso K b (g * h)).hom =
      (constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, constantFreeIso_matrix,
    constantFreeIso_matrix, constantFreeIso_matrix]
  exact Matrix.map_mul

theorem constantFreeIso_pullback {S T : Scheme.{u}} (b : S ⟶ Spec (.of K))
    (f : T ⟶ S) (g : GL14 K) :
    pulledFreeEnd f 14 (constantFreeIso K b g).hom = (constantFreeIso K (f ≫ b) g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [pulledFreeEnd_matrix, constantFreeIso_matrix, constantFreeIso_matrix]
  ext i j
  change f.appTop (scalarMap K b (g.val i j)) = scalarMap K (f ≫ b) (g.val i j)
  rw [scalarMap_comp]
  rfl

theorem constantFreeIso_pullback_inv {S T : Scheme.{u}} (b : S ⟶ Spec (.of K))
    (f : T ⟶ S) (g : GL14 K) :
    (pullbackFreeIso f 14).inv ≫ (Scheme.Modules.pullback f).map (constantFreeIso K b g).hom =
      (constantFreeIso K (f ≫ b) g).hom ≫ (pullbackFreeIso f 14).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f 14).inv)
    (constantFreeIso_pullback K b f g)
  simp only [pulledFreeEnd, Category.assoc] at h
  rw [(pullbackFreeIso f 14).hom_inv_id, Category.comp_id] at h
  exact h

def transform {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K)
    (q : QuotientPresentation T 9 14) : QuotientPresentation T 9 14 := by
  letI : Epi q.map := q.map_epi
  exact { target := q.target
          map := (constantFreeIso K b g).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K)
    {q q' : QuotientPresentation T 9 14} (h : q.Isomorphic q') :
    (transform K b g q).Isomorphic (transform K b g q') := by
  obtain ⟨e,he⟩ := h
  refine ⟨e, ?_⟩
  change ((constantFreeIso K b g).hom ≫ q.map) ≫ e.hom =
    (constantFreeIso K b g).hom ≫ q'.map
  rw [Category.assoc, he]

theorem transform_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (q : QuotientPresentation T 9 14) : (transform K b 1 q).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change ((constantFreeIso K b 1).hom ≫ q.map) ≫ 𝟙 _ = q.map
  rw [constantFreeIso_one, Category.id_comp, Category.comp_id]

theorem transform_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL14 K)
    (q : QuotientPresentation T 9 14) :
    (transform K b h (transform K b g q)).Isomorphic (transform K b (g * h) q) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom ≫ q.map) ≫ 𝟙 _ =
    (constantFreeIso K b (g * h)).hom ≫ q.map
  rw [Category.comp_id, constantFreeIso_mul, Category.assoc]

theorem pullback_transform {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : GL14 K) (q : QuotientPresentation S 9 14) :
    (pullbackPresentation f (transform K b g q)).Isomorphic
      (transform K (f ≫ b) g (pullbackPresentation f q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f 14).inv ≫
    (Scheme.Modules.pullback f).map ((constantFreeIso K b g).hom ≫ q.map)) ≫ 𝟙 _ =
      (constantFreeIso K (f ≫ b) g).hom ≫
        (pullbackFreeIso f 14).inv ≫ (Scheme.Modules.pullback f).map q.map
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc,
    constantFreeIso_pullback_inv, Category.assoc]

def transformPoints {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g : GL14 K) :
    Points T 9 14 → Points T 9 14 :=
  Quotient.lift (fun q => (⟦transform K b g q⟧ : Points T 9 14)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic K b g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (x : Points T 9 14) :
    transformPoints K b 1 x = x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one K b q))

theorem transformPoints_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (g h : GL14 K)
    (x : Points T 9 14) :
    transformPoints K b h (transformPoints K b g x) = transformPoints K b (g * h) x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_mul K b g h q))

theorem transformPoints_natural {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : GL14 K) (x : Points S 9 14) :
    pullbackPointsMap f 9 14 (transformPoints K b g x) =
      transformPoints K (f ≫ b) g (pullbackPointsMap f 9 14 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform K b f g q))

def pointClass {T : Scheme.{u}} (f : T ⟶ space K) : Points T 9 14 :=
  (functorData 9 14).objEquiv T ((schemeRepresentableBy 9 14).homEquiv
    (f ≫ GrassmannianCharts.toIntegral K 9 14))

theorem pointClass_comp {S T : Scheme.{u}} (f : T ⟶ S) (p : S ⟶ space K) :
    pointClass K (f ≫ p) = pullbackPointsMap f 9 14 (pointClass K p) := by
  have h := M9Native.LagrangianGrassmannian.pointsEquiv_map f 9 14
    ((schemeRepresentableBy 9 14).homEquiv (p ≫ GrassmannianCharts.toIntegral K 9 14))
  rw [← (schemeRepresentableBy 9 14).homEquiv_comp] at h
  simpa only [pointClass, Category.assoc] using h

def classify {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T 9 14) : T ⟶ space K :=
  pullback.lift p ((schemeRepresentableBy 9 14).homEquiv.symm
    (((functorData 9 14).objEquiv T).symm x)) (terminal.hom_ext _ _)

@[reassoc] theorem classify_projection {T : Scheme.{u}} (p : T ⟶ Spec (.of K))
    (x : Points T 9 14) : classify K p x ≫ projection K = p := pullback.lift_fst _ _ _

theorem classify_class {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T 9 14) :
    pointClass K (classify K p x) = x := by
  simp only [pointClass, classify, GrassmannianCharts.toIntegral, pullback.lift_snd,
    Equiv.apply_symm_apply]

theorem hom_ext {T : Scheme.{u}} (f h : T ⟶ space K)
    (hb : f ≫ projection K = h ≫ projection K) (hc : pointClass K f = pointClass K h) : f = h := by
  apply pullback.hom_ext
  · exact hb
  · apply (schemeRepresentableBy 9 14).homEquiv.injective
    apply ((functorData 9 14).objEquiv T).injective
    exact hc

/-- Precomposition of the universal quotient by the actual constant matrix. -/
def action (g : GL14 K) : space K ⟶ space K :=
  classify K (projection K) (transformPoints K (projection K) g (pointClass K (𝟙 _)))

@[reassoc] theorem action_projection (g : GL14 K) : action K g ≫ projection K = projection K :=
  classify_projection _ _ _

theorem action_class (g : GL14 K) :
    pointClass K (action K g) = transformPoints K (projection K) g (pointClass K (𝟙 _)) :=
  classify_class _ _ _

/-- The action is realized on the actual quotient class over every test scheme. -/
theorem pointClass_action {T : Scheme.{u}} (p : T ⟶ space K) (g : GL14 K) :
    pointClass K (p ≫ action K g) =
      transformPoints K (p ≫ projection K) g (pointClass K p) := by
  rw [pointClass_comp, action_class, transformPoints_natural]
  have hp : pullbackPointsMap p 9 14 (pointClass K (𝟙 (space K))) = pointClass K p := by
    simpa only [Category.comp_id] using (pointClass_comp K p (𝟙 (space K))).symm
  rw [hp]

theorem action_one : action K 1 = 𝟙 (space K) := by
  apply hom_ext K
  · rw [action_projection, Category.id_comp]
  · rw [action_class, transformPoints_one]

theorem action_mul (g h : GL14 K) : action K g ≫ action K h = action K (g * h) := by
  apply hom_ext K
  · rw [Category.assoc, action_projection, action_projection, action_projection]
  · rw [pointClass_action, action_projection, action_class, action_class, transformPoints_mul]

def rightAutomorphism (g : GL14 K) : space K ≅ space K where
  hom := action K g
  inv := action K g⁻¹
  hom_inv_id := by rw [action_mul, mul_inv_cancel, action_one]
  inv_hom_id := by rw [action_mul, inv_mul_cancel, action_one]

instance action_isIso (g : GL14 K) : IsIso (action K g) :=
  (rightAutomorphism K g).isIso_hom

instance action_isDominant (g : GL14 K) : IsDominant (action K g) :=
  ⟨(action K g).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

end M9Native.LagrangianParameterLinearAction
