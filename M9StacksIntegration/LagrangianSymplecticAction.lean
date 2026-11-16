module
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

public import M9StacksIntegration.LagrangianFreeMatrixPullback
public import M9StacksIntegration.MukaiLagrangianMap

/-!
# The actual constant symplectic action on the native LG scheme

Precomposition of the actual universal quotient by the constant free-six
symplectic automorphism defines the action through the native Grassmannian
classifier and the genuine zero-ideal universal property. Scheme equality
is proved by the classifier and actual quotient isomorphisms over every
test scheme.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.LagrangianSymplecticAction

open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianTransitivity M9Native.LagrangianSigmaInvariance
open M9Native.LagrangianFreeMatrixPullback

variable (K : Type u) [Field K]

def scalarMap {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) : K →+* Γ(T,⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop).hom

theorem scalarMap_comp {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S) :
    scalarMap K (f ≫ b)=f.appTop.hom.comp (scalarMap K b) := by
  ext c
  rfl

def constantMatrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) : Matrix (Fin 6) (Fin 6) Γ(T,⊤) :=
  (matrixSix K g).map (scalarMap K b)

def constantFreeIso {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) : freeOn T 6 ≅ freeOn T 6 :=
  freeSymplecticIso T (mapSymplectic K (scalarMap K b) g)

theorem constantFreeIso_matrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) :
    Stacks.FreeSheafMatrix.toMatrix (constantFreeIso K b g).hom=constantMatrix K b g := by
  rw [constantFreeIso,freeSymplecticIso_matrix,matrixSix_map]
  rfl

theorem matrixSix_one : matrixSix K (1 : Matrix.symplecticGroup (Fin 3) K)=1 := by
  change (1 : Matrix SplitIndex SplitIndex K).submatrix splitIndex.symm splitIndex.symm=1
  exact Matrix.submatrix_one_equiv splitIndex.symm

theorem matrixSix_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    matrixSix K (g*h)=matrixSix K g * matrixSix K h := by
  change ((g : Matrix SplitIndex SplitIndex K)*(h : Matrix SplitIndex SplitIndex K)).submatrix
    splitIndex.symm splitIndex.symm=_
  exact (Matrix.submatrix_mul_equiv _ _ splitIndex.symm splitIndex.symm splitIndex.symm).symm

theorem constantFreeIso_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) :
    (constantFreeIso K b 1).hom=𝟙 (freeOn T 6) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [constantFreeIso_matrix,Stacks.FreeSheafMatrix.toMatrix_id,constantMatrix,matrixSix_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Composition reverses the matrix order, as actual sheaf morphisms do. -/
theorem constantFreeIso_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g h : Matrix.symplecticGroup (Fin 3) K) :
    (constantFreeIso K b (g*h)).hom=(constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,constantFreeIso_matrix,constantFreeIso_matrix,
    constantFreeIso_matrix]
  exact congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M.map (scalarMap K b))
    (matrixSix_mul K g h) |>.trans Matrix.map_mul

/-- Constant matrices commute with arbitrary actual canonical pullback. -/
theorem constantFreeIso_pullback {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    pulledFreeEnd f (constantFreeIso K b g).hom=(constantFreeIso K (f ≫ b) g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [pulledFreeEnd_matrix,constantFreeIso_matrix,constantFreeIso_matrix]
  ext i j
  change f.appTop (scalarMap K b (matrixSix K g i j))=
    scalarMap K (f ≫ b) (matrixSix K g i j)
  rw [scalarMap_comp]
  rfl

theorem constantFreeIso_pullback_inv {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map (constantFreeIso K b g).hom=
      (constantFreeIso K (f ≫ b) g).hom ≫ (pullbackFreeIso f 6).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f 6).inv)
    (constantFreeIso_pullback K b f g)
  simp only [pulledFreeEnd,Category.assoc] at h
  rw [(pullbackFreeIso f 6).hom_inv_id,Category.comp_id] at h
  exact h

def transform {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) (q : QuotientPresentation T 3 6) :
    QuotientPresentation T 3 6 := by
  letI : Epi q.map := q.map_epi
  exact { target := q.target
          map := (constantFreeIso K b g).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) {q q' : QuotientPresentation T 3 6}
    (h : q.Isomorphic q') : (transform K b g q).Isomorphic (transform K b g q') := by
  obtain ⟨e,he⟩ := h
  refine ⟨e,?_⟩
  change ((constantFreeIso K b g).hom ≫ q.map) ≫ e.hom=
    (constantFreeIso K b g).hom ≫ q'.map
  rw [Category.assoc,he]

theorem transform_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (q : QuotientPresentation T 3 6) :
    (transform K b 1 q).Isomorphic q := by
  refine ⟨Iso.refl _,?_⟩
  change ((constantFreeIso K b 1).hom ≫ q.map) ≫ 𝟙 _=q.map
  rw [constantFreeIso_one,Category.id_comp,Category.comp_id]

theorem transform_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g h : Matrix.symplecticGroup (Fin 3) K) (q : QuotientPresentation T 3 6) :
    (transform K b h (transform K b g q)).Isomorphic (transform K b (g*h) q) := by
  refine ⟨Iso.refl _,?_⟩
  change ((constantFreeIso K b h).hom ≫ (constantFreeIso K b g).hom ≫ q.map) ≫ 𝟙 _=
    (constantFreeIso K b (g*h)).hom ≫ q.map
  rw [Category.comp_id,constantFreeIso_mul,Category.assoc]

theorem pullback_transform {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) K) (q : QuotientPresentation S 3 6) :
    (pullbackPresentation f (transform K b g q)).Isomorphic
      (transform K (f ≫ b) g (pullbackPresentation f q)) := by
  refine ⟨Iso.refl _,?_⟩
  change ((pullbackFreeIso f 6).inv ≫
    (Scheme.Modules.pullback f).map ((constantFreeIso K b g).hom ≫ q.map)) ≫ 𝟙 _=
      (constantFreeIso K (f ≫ b) g).hom ≫
        (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q.map
  rw [Category.comp_id,Functor.map_comp,← Category.assoc,constantFreeIso_pullback_inv,Category.assoc]

def transformPoints {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g : Matrix.symplecticGroup (Fin 3) K) : Points T 3 6 → Points T 3 6 :=
  Quotient.lift (fun q => (⟦transform K b g q⟧ : Points T 3 6)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic K b g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (x : Points T 3 6) :
    transformPoints K b 1 x=x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one K b q))

theorem transformPoints_mul {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (g h : Matrix.symplecticGroup (Fin 3) K) (x : Points T 3 6) :
    transformPoints K b h (transformPoints K b g x)=transformPoints K b (g*h) x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_mul K b g h q))

theorem transformPoints_natural {S T : Scheme.{u}} (b : S ⟶ Spec (.of K)) (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) K) (x : Points S 3 6) :
    pullbackPointsMap f 3 6 (transformPoints K b g x)=
      transformPoints K (f ≫ b) g (pullbackPointsMap f 3 6 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform K b f g q))

def pointClass {T : Scheme.{u}} (p : T ⟶ space K) : Points T 3 6 :=
  ⟦pullbackPresentation (p ≫ inclusion K) (universalQuotient K)⟧

abbrev lagrangianUniversal : QuotientPresentation (space K) 3 6 :=
  M9Native.MukaiLagrangianMap.lagrangianQuotient K

theorem pointClass_id : pointClass K (𝟙 (space K))=⟦lagrangianUniversal K⟧ := by
  change (⟦pullbackPresentation ((𝟙 _) ≫ inclusion K) (universalQuotient K)⟧ : Points _ 3 6)=_
  rw [Category.id_comp]
  rfl

theorem pointClass_comp {S T : Scheme.{u}} (f : T ⟶ S) (p : S ⟶ space K) :
    pointClass K (f ≫ p)=pullbackPointsMap f 3 6 (pointClass K p) := by
  change pullbackPointsMap ((f ≫ p) ≫ inclusion K) 3 6 ⟦universalQuotient K⟧=
    pullbackPointsMap f 3 6 (pullbackPointsMap (p ≫ inclusion K) 3 6 ⟦universalQuotient K⟧)
  rw [Category.assoc,pullbackPointsMap_comp]
  rfl

/-- The actual native quotient classifier separates scheme morphisms over the base. -/
theorem hom_ext {T : Scheme.{u}} (f h : T ⟶ space K)
    (hb : f ≫ projection K=h ≫ projection K) (hc : pointClass K f=pointClass K h) : f=h := by
  apply (cancel_mono (inclusion K)).mp
  apply pullback.hom_ext
  · simpa only [projection,Category.assoc] using hb
  · apply (schemeRepresentableBy 3 6).homEquiv.injective
    apply ((functorData 3 6).objEquiv T).injective
    exact (pullbackUniversal_class K (f ≫ inclusion K)).symm.trans
      (hc.trans (pullbackUniversal_class K (h ≫ inclusion K)))

def transformedUniversal (g : Matrix.symplecticGroup (Fin 3) K) :
    QuotientPresentation (space K) 3 6 :=
  transform K (projection K) g (lagrangianUniversal K)

theorem lagrangianUniversal_annihilates : AnnihilatesSigma (space K) (lagrangianUniversal K).map :=
  (factorsThrough_iff_pullbackQuotient_annihilates K (inclusion K)).mp ⟨𝟙 _,by simp⟩

theorem transformedUniversal_annihilates (g : Matrix.symplecticGroup (Fin 3) K) :
    AnnihilatesSigma (space K) (transformedUniversal K g).map :=
  (annihilatesSigma_precomp_iff (space K) (lagrangianUniversal K).map
    (mapSymplectic K (scalarMap K (projection K)) g)).mpr (lagrangianUniversal_annihilates K)

def actionClassifying (g : Matrix.symplecticGroup (Fin 3) K) : space K ⟶ grassmannian K :=
  M9Native.MukaiLagrangianMap.classifying K (projection K) (transformedUniversal K g)

theorem exists_action (g : Matrix.symplecticGroup (Fin 3) K) :
    ∃ a : space K ⟶ space K,a ≫ inclusion K=actionClassifying K g := by
  obtain ⟨e,he⟩ := M9Native.MukaiLagrangianMap.classifying_pullback_isomorphic
    K (projection K) (transformedUniversal K g)
  apply (factorsThrough_iff_pullbackQuotient_annihilates K (actionClassifying K g)).mpr
  exact (annihilatesSigma_iff_of_iso (space K) _ _ e he).mpr (transformedUniversal_annihilates K g)

/-- The actual scheme morphism, constructed from the actual universal quotient. -/
def action (g : Matrix.symplecticGroup (Fin 3) K) : space K ⟶ space K :=
  Classical.choose (exists_action K g)

@[reassoc] theorem action_inclusion (g : Matrix.symplecticGroup (Fin 3) K) :
    action K g ≫ inclusion K=actionClassifying K g := Classical.choose_spec (exists_action K g)

@[reassoc (attr := simp)] theorem action_projection (g : Matrix.symplecticGroup (Fin 3) K) :
    action K g ≫ projection K=projection K := by
  change (action K g ≫ inclusion K) ≫ grassmannianProjection K=_
  rw [action_inclusion]
  exact M9Native.MukaiLagrangianMap.classifying_projection K (projection K) (transformedUniversal K g)

theorem action_class (g : Matrix.symplecticGroup (Fin 3) K) :
    pointClass K (action K g)=⟦transformedUniversal K g⟧ := by
  rw [pointClass,pullbackUniversal_class,action_inclusion]
  exact M9Native.MukaiLagrangianMap.classifying_class K (projection K) (transformedUniversal K g)

/-- The actual action on every test scheme is precomposition of its actual quotient. -/
theorem pointClass_action {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    pointClass K (p ≫ action K g)=
      transformPoints K (p ≫ projection K) g (pointClass K p) := by
  have hp : pointClass K p=pullbackPointsMap p 3 6 ⟦lagrangianUniversal K⟧ := by
    simpa only [Category.comp_id,pointClass_id] using pointClass_comp K p (𝟙 (space K))
  rw [pointClass_comp,action_class]
  exact (transformPoints_natural K (projection K) p g ⟦lagrangianUniversal K⟧).trans
    (congrArg (transformPoints K (p ≫ projection K) g) hp.symm)

/-- A genuine target isomorphism identifies the pulled-back acted quotient
with precomposition of the original quotient on every test scheme. -/
theorem pullback_action_isomorphic {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    (pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).Isomorphic
      (transform K (p ≫ projection K) g
        (pullbackPresentation (p ≫ inclusion K) (universalQuotient K))) :=
  presentation_isomorphic_of_class_eq (pointClass_action K p g)

theorem action_one : action K 1=𝟙 (space K) := by
  apply hom_ext K
  · simpa only [Category.id_comp] using action_projection K 1
  · rw [action_class,pointClass_id]
    exact transformPoints_one K (projection K) ⟦lagrangianUniversal K⟧

/-- Quotient precomposition gives an actual right action of the symplectic group. -/
theorem action_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    action K g ≫ action K h=action K (g*h) := by
  apply hom_ext K
  · rw [Category.assoc,action_projection,action_projection,action_projection]
  · rw [pointClass_action,action_projection,action_class,action_class]
    exact transformPoints_mul K (projection K) g h ⟦lagrangianUniversal K⟧

/-- The genuine native LG scheme automorphism, with its inverse proved on quotient data. -/
def symplecticAutomorphism (g : Matrix.symplecticGroup (Fin 3) K) : space K ≅ space K where
  hom := action K g
  inv := action K g⁻¹
  hom_inv_id := by rw [action_mul,mul_inv_cancel,action_one]
  inv_hom_id := by rw [action_mul,inv_mul_cancel,action_one]

def symplecticAutomorphismOver (g : Matrix.symplecticGroup (Fin 3) K) :
    Over.mk (projection K) ≅ Over.mk (projection K) :=
  Over.isoMk (symplecticAutomorphism K g) (action_projection K g)

theorem scalarMap_id (c : K) : scalarMap K (𝟙 (Spec (.of K))) c=(Scheme.ΓSpecIso (.of K)).inv c := by
  simp only [scalarMap,Scheme.Hom.id_appTop,Category.comp_id]

/-- Evaluating a true global symplectic matrix on `Spec K` and extending it
back along the structural scalar map recovers its actual sheaf automorphism. -/
theorem constantFreeIso_of_evaluation
    (g : Matrix.symplecticGroup (Fin 3) Γ(Spec (.of K),⊤)) :
    (constantFreeIso K (𝟙 (Spec (.of K)))
      (mapSymplectic Γ(Spec (.of K),⊤) (Scheme.ΓSpecIso (.of K)).hom.hom g)).hom=
        (freeSymplecticIso (Spec (.of K)) g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [constantFreeIso_matrix,freeSymplecticIso_matrix,constantMatrix,matrixSix_map]
  ext i j
  change scalarMap K (𝟙 (Spec (.of K)))
    ((Scheme.ΓSpecIso (.of K)).hom (matrixSix Γ(Spec (.of K),⊤) g i j))=_
  rw [scalarMap_id]
  exact (Scheme.ΓSpecIso (.of K)).hom_inv_id_apply _

/-- On actual `K`-points over the identity base map the scheme action
realizes the previously proved genuine quotient normal form. -/
theorem exists_point_action_normalForm (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K=𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (e : (pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of K)) 3),
      (pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).map ≫ e.hom=
        Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(Spec (.of K),⊤)) := by
  obtain ⟨g,e,he⟩ := exists_pullbackUniversal_normalForm K K p
  let gK := mapSymplectic Γ(Spec (.of K),⊤) (Scheme.ΓSpecIso (.of K)).hom.hom g
  obtain ⟨a,ha⟩ := pullback_action_isomorphic K p gK
  refine ⟨gK,a ≪≫ e,?_⟩
  rw [Iso.trans_hom,← Category.assoc,ha]
  change ((constantFreeIso K (p ≫ projection K) gK).hom ≫
    (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map) ≫ e.hom=_
  rw [hp,constantFreeIso_of_evaluation,Category.assoc]
  exact he

end M9Native.LagrangianSymplecticAction

end
