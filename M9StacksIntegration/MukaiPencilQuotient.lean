module

public import M9StacksIntegration.MukaiBundle
public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.MukaiDualSpanSections
public import M9StacksIntegration.CurveDivisorSections
public import M9StacksIntegration.FiniteCopowerBasisChange
public import M9StacksIntegration.FiniteCopowerBasisEvaluation
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual pencil quotient of a dual span

For an effective Cartier divisor `D`, complete bases of the actual two- and
three-dimensional section spaces, and epimorphic pencil and net evaluations,
`completePencilSequence_shortExact` constructs
`0 ⟶ O(D) ⟶ dualSpan β ⟶ I_D ⊗ β ⟶ 0` on the original complete net.
The concrete inclusion and projection are retained in the short complex.

An actual basis extending the included pencil sections factors evaluation
through `ξ ⊞ O`. The kernel sequence of this composite gives the exact
sequence before dualizing. Native exterior comparison identifies the pencil
kernel dual with `ξ`; native tensor-right cancellation identifies the other
kernel with the actual Cartier ideal. The source change of basis is linear
in the original native base-field scalar structure and commutes with the
actual evaluation maps. `completePencilTopExteriorIso` records the resulting
determinant relation. The diagram needs no numerical divisor-degree premise;
in Mukai's application the divisor has degree two.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiPencilQuotient

open CategoryTheory CategoryTheory.Limits

section KernelComposite

variable {C : Type*} [Category* C] [Abelian C]
variable {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

/-- The concrete inclusion of the first kernel in the kernel of the composite. -/
def kernelCompositeInclusion : kernel f ⟶ kernel (f ≫ g) :=
  kernel.lift (f ≫ g) (kernel.ι f) (by simp)

/-- The concrete map from the kernel of the composite to the second kernel. -/
def kernelCompositeProjection : kernel (f ≫ g) ⟶ kernel g :=
  kernel.lift g (kernel.ι (f ≫ g) ≫ f) (by simp)

@[reassoc (attr := simp)] theorem kernelCompositeInclusion_ι :
    kernelCompositeInclusion f g ≫ kernel.ι (f ≫ g) = kernel.ι f :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)] theorem kernelCompositeProjection_ι :
    kernelCompositeProjection f g ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f :=
  kernel.lift_ι _ _ _

theorem kernelComposite_zero :
    kernelCompositeInclusion f g ≫ kernelCompositeProjection f g = 0 := by
  apply (cancel_mono (kernel.ι g)).1
  simp

instance kernelCompositeInclusion_mono : Mono (kernelCompositeInclusion f g) := by
  constructor
  intro T a b hab
  apply (cancel_mono (kernel.ι f)).1
  simpa only [Category.assoc, kernelCompositeInclusion_ι] using
    congrArg (fun q => q ≫ kernel.ι (f ≫ g)) hab

def kernelCompositeSequence : ShortComplex C :=
  ShortComplex.mk (kernelCompositeInclusion f g) (kernelCompositeProjection f g)
    (kernelComposite_zero f g)

theorem kernelComposite_exact : (kernelCompositeSequence f g).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T z hz
  have hz' : (z ≫ kernel.ι (f ≫ g)) ≫ f = 0 := by
    have h := congrArg (fun q => q ≫ kernel.ι g) hz
    simpa only [kernelCompositeSequence, Category.assoc, kernelCompositeProjection_ι,
      zero_comp] using h
  refine ⟨T, 𝟙 T, inferInstance, kernel.lift f (z ≫ kernel.ι (f ≫ g)) hz', ?_⟩
  apply (cancel_mono (kernel.ι (f ≫ g))).1
  simp [kernelCompositeSequence]

instance kernelCompositeProjection_epi [Epi f] : Epi (kernelCompositeProjection f g) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T', π, hπ, x, hx⟩ := surjective_up_to_refinements_of_epi f (z ≫ kernel.ι g)
  have hx' : x ≫ (f ≫ g) = 0 := by
    rw [← Category.assoc, ← hx]
    simp
  refine ⟨T', π, hπ, kernel.lift (f ≫ g) x hx', ?_⟩
  apply (cancel_mono (kernel.ι g)).1
  simpa only [Category.assoc, kernelCompositeProjection_ι, kernel.lift_ι_assoc] using hx

theorem kernelComposite_shortExact [Epi f] :
    (kernelCompositeSequence f g).ShortExact :=
  { exact := kernelComposite_exact f g
    mono_f := by change Mono (kernelCompositeInclusion f g); infer_instance
    epi_g := by change Epi (kernelCompositeProjection f g); infer_instance }

variable (E : C)

theorem blockKernel_fst_zero :
    (kernel.ι (biprod.map f (𝟙 E)) ≫ biprod.fst) ≫ f = 0 := by
  have h := congrArg (fun q => q ≫ biprod.fst)
    (kernel.condition (biprod.map f (𝟙 E)))
  simpa only [Category.assoc, biprod.map_fst, zero_comp] using h

theorem blockKernel_snd_zero :
    kernel.ι (biprod.map f (𝟙 E)) ≫ biprod.snd = 0 := by
  have h := congrArg (fun q => q ≫ biprod.snd)
    (kernel.condition (biprod.map f (𝟙 E)))
  simpa only [Category.assoc, biprod.map_snd, Category.comp_id, zero_comp] using h

/-- The kernel of the pencil evaluation plus an identity is its original kernel. -/
def blockKernelIso : kernel (biprod.map f (𝟙 E)) ≅ kernel f where
  hom := kernel.lift f (kernel.ι (biprod.map f (𝟙 E)) ≫ biprod.fst)
    (blockKernel_fst_zero f E)
  inv := kernel.lift (biprod.map f (𝟙 E)) (kernel.ι f ≫ biprod.inl) (by simp)
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (biprod.map f (𝟙 E)))).1
    apply biprod.hom_ext
    · simp
    · simp [blockKernel_snd_zero]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι f)).1
    simp

@[reassoc (attr := simp)] theorem blockKernelIso_inv_ι :
    (blockKernelIso f E).inv ≫ kernel.ι (biprod.map f (𝟙 E)) =
      kernel.ι f ≫ biprod.inl := kernel.lift_ι _ _ _

variable (q : B ⊞ E ⟶ D)

def blockSequenceInclusion : kernel f ⟶ kernel (biprod.map f (𝟙 E) ≫ q) :=
  (blockKernelIso f E).inv ≫ kernelCompositeInclusion (biprod.map f (𝟙 E)) q

def blockSequenceProjection : kernel (biprod.map f (𝟙 E) ≫ q) ⟶ kernel q :=
  kernelCompositeProjection (biprod.map f (𝟙 E)) q

theorem blockSequence_zero : blockSequenceInclusion f E q ≫ blockSequenceProjection f E q = 0 := by
  simp [blockSequenceInclusion, blockSequenceProjection, kernelComposite_zero]

def blockKernelSequence : ShortComplex C :=
  ShortComplex.mk (blockSequenceInclusion f E q) (blockSequenceProjection f E q)
    (blockSequence_zero f E q)

/-- An exact quotient sequence constructed from the original pencil evaluation. -/
theorem blockKernelSequence_shortExact [Epi f] : (blockKernelSequence f E q).ShortExact := by
  let e : kernelCompositeSequence (biprod.map f (𝟙 E)) q ≅ blockKernelSequence f E q :=
    ShortComplex.isoMk (blockKernelIso f E) (Iso.refl _) (Iso.refl _)
      (by simp [kernelCompositeSequence, blockKernelSequence, blockSequenceInclusion])
      (by simp [kernelCompositeSequence, blockKernelSequence, blockSequenceProjection])
  exact ShortComplex.shortExact_of_iso e (kernelComposite_shortExact (biprod.map f (𝟙 E)) q)

@[reassoc (attr := simp)] theorem blockSequenceInclusion_ι :
    blockSequenceInclusion f E q ≫ kernel.ι (biprod.map f (𝟙 E) ≫ q) =
      kernel.ι f ≫ biprod.inl := by
  simp [blockSequenceInclusion]

end KernelComposite

section KernelSourceIso

variable {C : Type*} [Category* C] [Abelian C]
variable {A B D : C} (e : A ≅ B) (f : A ⟶ D) (g : B ⟶ D)
  (h : e.hom ≫ g = f)

/-- Changing the actual evaluation source transports its actual kernel. -/
def kernelSourceIso : kernel f ≅ kernel g where
  hom := kernel.lift g (kernel.ι f ≫ e.hom) (by simp [h])
  inv := kernel.lift f (kernel.ι g ≫ e.inv) (by
    rw [← h]
    simp)
  hom_inv_id := by
    apply (cancel_mono (kernel.ι f)).1
    simp
  inv_hom_id := by
    apply (cancel_mono (kernel.ι g)).1
    simp

@[reassoc (attr := simp)] theorem kernelSourceIso_hom_ι :
    (kernelSourceIso e f g h).hom ≫ kernel.ι g = kernel.ι f ≫ e.hom :=
  kernel.lift_ι _ _ _

end KernelSourceIso

section NativeEvaluation

open AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle

variable {X : Scheme.{u}}

def pencilFree (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))

def pencilEvaluation (ξ : X.Modules) (t : ULift.{u} (Fin 2) → ξ.sections) :
    pencilFree X ⟶ ξ := ξ.freeHomEquiv.symm t

theorem pencilEvaluation_freeSection (ξ : X.Modules)
    (t : ULift.{u} (Fin 2) → ξ.sections) (i : ULift.{u} (Fin 2)) :
    SheafOfModules.sectionsMap (pencilEvaluation ξ t) (SheafOfModules.freeSection i) = t i :=
  SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection t i

abbrev adaptedFree (X : Scheme.{u}) : X.Modules := pencilFree X ⊞ structureModule X

def pencilStep (ξ : X.Modules) (t : ULift.{u} (Fin 2) → ξ.sections) :
    adaptedFree X ⟶ ξ ⊞ structureModule X :=
  biprod.map (pencilEvaluation ξ t) (𝟙 (structureModule X))

def targetEvaluation {ξ β : X.Modules} (c : ξ ⟶ β) (s : β.sections) :
    ξ ⊞ structureModule X ⟶ β :=
  biprod.desc c (β.unitHomEquiv.symm s)

/-- The original net evaluation in a basis extending the pencil sections. -/
def adaptedEvaluation {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) : adaptedFree X ⟶ β :=
  pencilStep ξ t ≫ targetEvaluation c s

@[reassoc (attr := simp)] theorem adaptedEvaluation_inl {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    biprod.inl ≫ adaptedEvaluation c t s = pencilEvaluation ξ t ≫ c := by
  simp [adaptedEvaluation, pencilStep, targetEvaluation]

@[reassoc (attr := simp)] theorem adaptedEvaluation_inr {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    biprod.inr ≫ adaptedEvaluation c t s = β.unitHomEquiv.symm s := by
  simp [adaptedEvaluation, pencilStep, targetEvaluation]

def adaptedKernel {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) : X.Modules :=
  kernel (adaptedEvaluation c t s)

def quotientKernel {ξ β : X.Modules} (c : ξ ⟶ β) (s : β.sections) : X.Modules :=
  kernel (targetEvaluation c s)

def adaptedKernelInclusion {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    kernel (pencilEvaluation ξ t) ⟶ adaptedKernel c t s :=
  blockSequenceInclusion (pencilEvaluation ξ t) (structureModule X) (targetEvaluation c s)

def adaptedKernelProjection {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    adaptedKernel c t s ⟶ quotientKernel c s :=
  blockSequenceProjection (pencilEvaluation ξ t) (structureModule X) (targetEvaluation c s)

theorem adaptedKernel_zero {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    adaptedKernelInclusion c t s ≫ adaptedKernelProjection c t s = 0 :=
  blockSequence_zero (pencilEvaluation ξ t) (structureModule X) (targetEvaluation c s)

theorem adaptedKernel_shortExact {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (hgen : Epi (pencilEvaluation ξ t)) :
    (ShortComplex.mk (adaptedKernelInclusion c t s) (adaptedKernelProjection c t s)
      (adaptedKernel_zero c t s)).ShortExact := by
  let := hgen
  exact blockKernelSequence_shortExact (pencilEvaluation ξ t) (structureModule X)
    (targetEvaluation c s)

@[reassoc (attr := simp)] theorem adaptedKernelInclusion_ι {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections) :
    adaptedKernelInclusion c t s ≫ kernel.ι (adaptedEvaluation c t s) =
      kernel.ι (pencilEvaluation ξ t) ≫ biprod.inl :=
  blockSequenceInclusion_ι (pencilEvaluation ξ t) (structureModule X) (targetEvaluation c s)

theorem targetEvaluation_epi {ξ β : X.Modules} (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (hgen : Epi (adaptedEvaluation c t s)) : Epi (targetEvaluation c s) := by
  let := hgen
  constructor
  intro T a b hab
  apply (cancel_epi (adaptedEvaluation c t s)).1
  change (pencilStep ξ t ≫ targetEvaluation c s) ≫ a =
    (pencilStep ξ t ≫ targetEvaluation c s) ≫ b
  simpa only [Category.assoc] using congrArg (fun q => pencilStep ξ t ≫ q) hab

theorem pencilFree_rank (X : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (pencilFree X) 2 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv
    (ULift.{u} (Fin 2)) 2 Equiv.ulift

theorem structureModule_rank (X : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (structureModule X) 1 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (structureModule X) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  exact SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (structureModule X)

theorem biprod_structure_rank (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F ⊞ structureModule X) (r + 1) := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (biprod.inl : F ⟶ F ⊞ structureModule X) biprod.snd (by simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.Splitting.ofHasBinaryBiproduct F (structureModule X)).exact }
  exact extension_rank S hS r 1 hF (structureModule_rank X)

theorem pencilKernel_rank (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (t : ULift.{u} (Fin 2) → ξ.sections) (hgen : Epi (pencilEvaluation ξ t)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel (pencilEvaluation ξ t)) 1 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (pencilEvaluation ξ t) hgen inferInstance 1 (pencilFree_rank X)

theorem adaptedKernel_rank {ξ β : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (c : ξ ⟶ β) (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (hgen : Epi (adaptedEvaluation c t s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (adaptedKernel c t s) 2 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (adaptedEvaluation c t s) hgen inferInstance 2
      (biprod_structure_rank (pencilFree X) 2 (pencilFree_rank X))

theorem quotientKernel_rank {ξ β : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (c : ξ ⟶ β) (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (hgen : Epi (adaptedEvaluation c t s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientKernel c s) 1 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (targetEvaluation c s) (targetEvaluation_epi c t s hgen) inferInstance 1
      (biprod_structure_rank ξ 1
        (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ))

theorem adaptedDualSequence_shortExact {ξ β : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (c : ξ ⟶ β) (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (hξ : Epi (pencilEvaluation ξ t)) (hβ : Epi (adaptedEvaluation c t s)) :
    ∃ w : dualMap (adaptedKernelProjection c t s) ≫
        dualMap (adaptedKernelInclusion c t s) = 0,
      (ShortComplex.mk (dualMap (adaptedKernelProjection c t s))
        (dualMap (adaptedKernelInclusion c t s)) w).ShortExact := by
  have hS := adaptedKernel_shortExact c t s hξ
  exact exists_dualSheaf_shortExact (adaptedKernelInclusion c t s)
    (adaptedKernelProjection c t s) (adaptedKernel_zero c t s)
    hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      (pencilKernel_rank ξ t hξ).isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      (adaptedKernel_rank c t s hβ).isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      (quotientKernel_rank c t s hβ).isFiniteLocallyFree)

end NativeEvaluation

section FreeSplitting

open AlgebraicGeometry M9Native.MukaiBundle

variable (X : Scheme.{u})

/-- The literal first-two-plus-last decomposition of the free net. -/
def splitNetHom : netFree X ⟶ adaptedFree X :=
  Sigma.desc (fun j : ULift.{u} (Fin 3) =>
    Fin.lastCases (biprod.inr : structureModule X ⟶ adaptedFree X)
      (fun i : Fin 2 => SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i) ≫
        biprod.inl) j.down)

@[reassoc (attr := simp)] theorem splitNetHom_left (i : Fin 2) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i.castSucc) ≫ splitNetHom X =
      SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i) ≫ biprod.inl := by
  simp [splitNetHom, SheafOfModules.ιFree]

@[reassoc (attr := simp)] theorem splitNetHom_last :
    SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up (Fin.last 2)) ≫ splitNetHom X =
      biprod.inr := by
  simp only [splitNetHom, SheafOfModules.ιFree, Sigma.ι_comp_desc, Fin.lastCases_last]

def splitNetInv : adaptedFree X ⟶ netFree X :=
  biprod.desc (SheafOfModules.freeMap (fun i : ULift.{u} (Fin 2) => ULift.up i.down.castSucc))
    (SheafOfModules.ιFree (ULift.up (Fin.last 2)))

/-- This is an actual source isomorphism of the evaluation maps. -/
def splitNetIso : netFree X ≅ adaptedFree X where
  hom := splitNetHom X
  inv := splitNetInv X
  hom_inv_id := by
    apply Sigma.hom_ext
    intro j
    obtain ⟨j⟩ := j
    induction j using Fin.lastCases with
    | last =>
      change SheafOfModules.ιFree (ULift.up (Fin.last 2)) ≫ _ =
        SheafOfModules.ιFree (ULift.up (Fin.last 2)) ≫ _
      exact (splitNetHom_last_assoc X (splitNetInv X)).trans
        ((biprod.inr_desc _ _).trans (Category.comp_id _).symm)
    | cast i =>
      change SheafOfModules.ιFree (ULift.up i.castSucc) ≫ _ =
        SheafOfModules.ιFree (ULift.up i.castSucc) ≫ _
      exact (splitNetHom_left_assoc X i (splitNetInv X)).trans
        ((congrArg (fun q => SheafOfModules.ιFree (ULift.up i) ≫ q)
          (biprod.inl_desc
            (SheafOfModules.freeMap (fun i : ULift.{u} (Fin 2) => ULift.up i.down.castSucc))
            (SheafOfModules.ιFree (ULift.up (Fin.last 2))))).trans
          ((SheafOfModules.ιFree_freeMap
            (fun i : ULift.{u} (Fin 2) => ULift.up i.down.castSucc) (ULift.up i)).trans
              (Category.comp_id _).symm))
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [splitNetInv, biprod.inl_desc_assoc, Category.comp_id]
      apply Sigma.hom_ext
      intro i
      change SheafOfModules.ιFree i ≫ _ = SheafOfModules.ιFree i ≫ _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ splitNetHom X)
          (SheafOfModules.ιFree_freeMap
            (fun i : ULift.{u} (Fin 2) => ULift.up i.down.castSucc) i)).trans
              (splitNetHom_left X i.down))
    · simpa only [splitNetInv, biprod.inr_desc_assoc, Category.comp_id] using splitNetHom_last X

variable {X} {ξ β : X.Modules}

theorem freeEvaluation_generator {I : Type u} (L : X.Modules)
    (ns : I → L.sections) (i : I) :
    SheafOfModules.ιFree i ≫ L.freeHomEquiv.symm ns = L.unitHomEquiv.symm (ns i) := by
  exact (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
    (L.freeHomEquiv.symm ns) i).symm.trans
      (congrArg L.unitHomEquiv.symm (congrFun (L.freeHomEquiv.apply_symm_apply ns) i))

theorem splitNetHom_evaluation (c : ξ ⟶ β)
    (t : ULift.{u} (Fin 2) → ξ.sections) (s : β.sections)
    (ns : ULift.{u} (Fin 3) → β.sections)
    (hl : ∀ i : Fin 2, ns ⟨i.castSucc⟩ = SheafOfModules.sectionsMap c (t ⟨i⟩))
    (hr : ns ⟨Fin.last 2⟩ = s) :
    splitNetHom X ≫ adaptedEvaluation c t s = netEvaluation β ns := by
  apply Sigma.hom_ext
  intro j
  obtain ⟨j⟩ := j
  induction j using Fin.lastCases with
  | last =>
    change SheafOfModules.ιFree (ULift.up (Fin.last 2)) ≫ _ =
      SheafOfModules.ιFree (ULift.up (Fin.last 2)) ≫ _
    exact (splitNetHom_last_assoc X (adaptedEvaluation c t s)).trans
      ((adaptedEvaluation_inr c t s).trans
        ((congrArg β.unitHomEquiv.symm hr).symm.trans
          (freeEvaluation_generator β ns _).symm))
  | cast i =>
    change SheafOfModules.ιFree (ULift.up i.castSucc) ≫ _ =
      SheafOfModules.ιFree (ULift.up i.castSucc) ≫ _
    exact (splitNetHom_left_assoc X i (adaptedEvaluation c t s)).trans
      ((congrArg (fun q => SheafOfModules.ιFree (ULift.up i) ≫ q)
        (adaptedEvaluation_inl c t s)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ c) (freeEvaluation_generator ξ t _)).trans
              ((SheafOfModules.unitHomEquiv_symm_comp _ c).trans
                ((congrArg β.unitHomEquiv.symm (hl i)).symm.trans
                  (freeEvaluation_generator β ns _).symm)))))

end FreeSplitting

section NativeEndpointLines

open AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.CurveDivisorSections

variable {X : Scheme.{u}}

/-- Contravariant functoriality of the literal sheaf dual on an isomorphism. -/
def dualIso {F G : X.Modules} (e : F ≅ G) : dualSheaf G ≅ dualSheaf F where
  hom := dualMap e.hom
  inv := dualMap e.inv
  hom_inv_id := by rw [← dualMap_comp, e.inv_hom_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, e.hom_inv_id, dualMap_id]

/-- The line kernel of an epimorphism has its actual determinant tensor relation. -/
def kernelLineTensorIso {F L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (p : F ⟶ L) (hp : Epi p)
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel p) 1) :
    tensor (kernel p) L ≅ topExterior F 2 := by
  letI := hr
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p
      mono_f := inferInstance
      epi_g := hp }
  exact tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf (kernel p)).symm
      (Scheme.Modules.exteriorPowerOneIsoSelf L).symm ≪≫
    Scheme.Modules.exteriorPowerTensorExteriorPowerIso (kernel.ι p) p
      (kernel.condition p) hS 1 0

/-- The dual of the kernel of the genuine pencil evaluation is its line bundle. -/
def pencilKernelDualIso (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (t : ULift.{u} (Fin 2) → ξ.sections) (hp : Epi (pencilEvaluation ξ t)) :
    dualSheaf (kernel (pencilEvaluation ξ t)) ≅ ξ :=
  (tensorInverseNativeIso (kernel (pencilEvaluation ξ t)) ξ
    (kernelLineTensorIso (pencilEvaluation ξ t) hp (pencilKernel_rank ξ t hp) ≪≫
      freeTopExteriorIso 2 (pencilFree X) (Iso.refl _))).symm

/-- The determinant of the actual split rank-two source is its line summand. -/
def biprodLineTopIso (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ] :
    topExterior (ξ ⊞ structureModule X) 2 ≅ ξ := by
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  letI := structureModule_rank X
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (biprod.inl : ξ ⟶ ξ ⊞ structureModule X) biprod.snd (by simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.Splitting.ofHasBinaryBiproduct ξ (structureModule X)).exact }
  exact (Scheme.Modules.exteriorPowerTensorExteriorPowerIso S.f S.g S.zero hS 1 0).symm ≪≫
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf ξ)
      (Scheme.Modules.exteriorPowerOneIsoSelf (structureModule X)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      X.presheaf X.ringCatSheaf.2 ξ

/-- The other actual kernel is the ideal sheaf of the original Cartier divisor. -/
def quotientKernelIdealIso (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hp : Epi (adaptedEvaluation (twistDownι D β) t s)) :
    quotientKernel (twistDownι D β) s ≅ Stacks.Divisors.idealSheafOfModules D := by
  letI := twistDown_isInvertible D β
  let T := M9StacksIntegration.InvertibleHomCancellation.tensorRight β
  letI : T.IsEquivalence := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor β
  letI : T.Full := Functor.IsEquivalence.full
  letI : T.Faithful := Functor.IsEquivalence.faithful
  let e : T.obj (quotientKernel (twistDownι D β) s) ≅
      T.obj (Stacks.Divisors.idealSheafOfModules D) :=
    kernelLineTensorIso (targetEvaluation (twistDownι D β) s)
      (targetEvaluation_epi (twistDownι D β) t s hp)
      (quotientKernel_rank (twistDownι D β) t s hp) ≪≫
        biprodLineTopIso (twistDown D β)
  exact T.preimageIso e

/-- Its dual is precisely the native positive divisor sheaf. -/
def quotientKernelDivisorIso (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hp : Epi (adaptedEvaluation (twistDownι D β) t s)) :
    dualSheaf (quotientKernel (twistDownι D β) s) ≅ Stacks.Divisors.divisorSheaf D :=
  (dualIso (quotientKernelIdealIso D β t s hp)).symm

/-- The concrete injection of the positive divisor line into the adapted dual span. -/
def adaptedPencilInclusion (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hp : Epi (adaptedEvaluation (twistDownι D β) t s)) :
    Stacks.Divisors.divisorSheaf D ⟶ dualSheaf (adaptedKernel (twistDownι D β) t s) :=
  (quotientKernelDivisorIso D β t s hp).inv ≫
    dualMap (adaptedKernelProjection (twistDownι D β) t s)

/-- The concrete pencil quotient map of the adapted dual span. -/
def adaptedPencilProjection (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hp : Epi (pencilEvaluation (twistDown D β) t)) :
    dualSheaf (adaptedKernel (twistDownι D β) t s) ⟶ twistDown D β := by
  let := twistDown_isInvertible D β
  exact dualMap (adaptedKernelInclusion (twistDownι D β) t s) ≫
    (pencilKernelDualIso (twistDown D β) t hp).hom

theorem adaptedPencil_zero (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (adaptedEvaluation (twistDownι D β) t s)) :
    adaptedPencilInclusion D β t s hβ ≫ adaptedPencilProjection D β t s hξ = 0 := by
  let := twistDown_isInvertible D β
  obtain ⟨w, _hS⟩ := adaptedDualSequence_shortExact (twistDownι D β) t s hξ hβ
  simp only [adaptedPencilInclusion, adaptedPencilProjection, Category.assoc]
  rw [← Category.assoc (dualMap _) (dualMap _), w]
  simp

/-- The actual divisor-to-dual-span-to-pencil sequence in an adapted complete net. -/
def adaptedPencilSequence (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (adaptedEvaluation (twistDownι D β) t s)) : ShortComplex X.Modules :=
  ShortComplex.mk (adaptedPencilInclusion D β t s hβ)
    (adaptedPencilProjection D β t s hξ) (adaptedPencil_zero D β t s hξ hβ)

theorem adaptedPencilSequence_shortExact (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (adaptedEvaluation (twistDownι D β) t s)) :
    (adaptedPencilSequence D β t s hξ hβ).ShortExact := by
  let := twistDown_isInvertible D β
  obtain ⟨w, hS⟩ := adaptedDualSequence_shortExact (twistDownι D β) t s hξ hβ
  let e : ShortComplex.mk (dualMap (adaptedKernelProjection (twistDownι D β) t s))
      (dualMap (adaptedKernelInclusion (twistDownι D β) t s)) w ≅
      adaptedPencilSequence D β t s hξ hβ :=
    ShortComplex.isoMk (quotientKernelDivisorIso D β t s hβ) (Iso.refl _)
      (pencilKernelDualIso (twistDown D β) t hξ)
      (by simp [adaptedPencilSequence, adaptedPencilInclusion])
      (by simp [adaptedPencilSequence, adaptedPencilProjection])
  exact ShortComplex.shortExact_of_iso e hS

end NativeEndpointLines

section AdaptedBasis

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An injective map from a two-dimensional section space extends to an
actual basis of the original three-dimensional section space. -/
theorem exists_basis_extending_pair (bV : Module.Basis (Fin 2) k V)
    (bW : Module.Basis (Fin 3) k W) (L : V →ₗ[k] W) (hL : Function.Injective L) :
    ∃ b : Module.Basis (Fin 3) k W, ∀ i : Fin 2, b i.castSucc = L (bV i) := by
  classical
  let : Module.Finite k V := Module.Finite.of_basis bV
  let : Module.Finite k W := Module.Finite.of_basis bW
  have hr : Module.finrank k (LinearMap.range L) = 2 := by
    rw [LinearMap.finrank_range_of_inj hL, Module.finrank_eq_card_basis bV]
    simp
  have hW : Module.finrank k W = 3 := by rw [Module.finrank_eq_card_basis bW]; simp
  have hspan : Submodule.span k (Set.range (fun i : Fin 2 => L (bV i))) ≤ LinearMap.range L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨bV i, rfl⟩
  have hne : Submodule.span k (Set.range (fun i : Fin 2 => L (bV i))) ≠ ⊤ := by
    intro htop
    have heq : LinearMap.range L = ⊤ := by
      apply top_unique
      rw [← htop]
      exact hspan
    rw [heq, finrank_top, hW] at hr
    exact (by decide : (3 : ℕ) ≠ 2) hr
  have hex : ∃ w : W, w ∉ Submodule.span k (Set.range (fun i : Fin 2 => L (bV i))) := by
    by_contra h
    apply hne
    apply top_unique
    intro w _hw
    exact Classical.byContradiction (fun hw => h ⟨w, hw⟩)
  obtain ⟨w, hw⟩ := hex
  have hli := (bV.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)).finSnoc hw
  let b : Module.Basis (Fin 3) k W :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hW])
  refine ⟨b, ?_⟩
  intro i
  simp [b]

end AdaptedBasis

section SectionHomLinearity

open AlgebraicGeometry Opposite
open M9Native.MukaiBundle

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

abbrev nativeTopSections (L : X.Modules) : ModuleCat.{u} k :=
  (restrictScalarsOverBase k f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)

abbrev nativeTopSectionsAppTop (L : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)

/-- Identity on actual global sections, with the two native base-map spellings
proved to induce the same scalar action. -/
def topSectionsSpellingEquiv (L : X.Modules) :
    nativeTopSectionsAppTop f L ≃ₗ[k] nativeTopSections f L where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c) • a =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) • a
    rw [appLE_top_top_eq_appTop]

/-- Actual unit morphisms and actual top sections, in the exact native
`modulesLinearOverField` structure. -/
def homTopLinearEquiv (L : X.Modules) :
    letI := modulesLinearOverField k f
    (structureModule X ⟶ L) ≃ₗ[k] nativeTopSections f L := by
  letI := modulesLinearOverField k f
  exact (unitHomLinearEquivCohomologyZero k f L).trans
    ((cohomologyOverFieldZeroIsoSections k f L).toLinearEquiv.trans
      (topSectionsSpellingEquiv f L))

theorem homTopLinearEquiv_apply (L : X.Modules) (φ : structureModule X ⟶ L) :
    letI := modulesLinearOverField k f
    homTopLinearEquiv f L φ = (φ.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤)) := by
  let := modulesLinearOverField k f
  change topSectionsSpellingEquiv f L
    ((cohomologyOverFieldZeroIsoSections k f L).toLinearEquiv
      ((cohomologyOverFieldZeroIsoSections k f L).toLinearEquiv.symm
        ((φ.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem homTopLinearEquiv_symm_section (L : X.Modules) (a : nativeTopSections f L) :
    letI := modulesLinearOverField k f
    (homTopLinearEquiv f L).symm a =
      L.unitHomEquiv.symm (Stacks.PresheafOfModules.sectionOfTop L.val a) := by
  let := modulesLinearOverField k f
  apply (homTopLinearEquiv f L).injective
  rw [LinearEquiv.apply_symm_apply, homTopLinearEquiv_apply]
  change a = (L.unitHomEquiv
    (L.unitHomEquiv.symm (Stacks.PresheafOfModules.sectionOfTop L.val a))).eval (op ⊤)
  rw [Equiv.apply_symm_apply]
  exact (Stacks.PresheafOfModules.sectionOfTop_val_top L.val a).symm

/-- The actual section-to-unit-morphism assignment is linear on the original H⁰. -/
def sectionHomLinearEquiv (L : X.Modules) :
    letI := modulesLinearOverField k f
    cohomologyOverField k f L 0 ≃ₗ[k] (structureModule X ⟶ L) := by
  letI := modulesLinearOverField k f
  exact (cohomologyOverFieldZeroLinearIso k f L).toLinearEquiv.trans (homTopLinearEquiv f L).symm

theorem sectionHomLinearEquiv_apply (L : X.Modules) (a : cohomologyOverField k f L 0) :
    letI := modulesLinearOverField k f
    sectionHomLinearEquiv f L a = L.unitHomEquiv.symm
      (Stacks.PresheafOfModules.sectionOfTop L.val ((cohomologyOverFieldZeroLinearIso k f L).hom a)) := by
  let := modulesLinearOverField k f
  exact homTopLinearEquiv_symm_section f L ((cohomologyOverFieldZeroLinearIso k f L).hom a)

end SectionHomLinearity

section CompleteNetBasisChange

open AlgebraicGeometry M9Native.MukaiBundle M9Native.MukaiDualSpanSections
open M9Native.FiniteCopowerBasisChange

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (β : X.Modules)

theorem completeNetEvaluation_generator
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (i : ULift.{u} (Fin 3)) :
    letI := modulesLinearOverField k f
    SheafOfModules.ιFree i ≫ netEvaluation β (completeNetSections f β b) =
      sectionHomLinearEquiv f β (b i) := by
  let := modulesLinearOverField k f
  exact (freeEvaluation_generator β (completeNetSections f β b) i).trans
    (sectionHomLinearEquiv_apply f β (b i)).symm

/-- The actual finite free-source change between two complete bases of H⁰. -/
def completeNetSourceIso
    (bI bJ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    netFree X ≅ netFree X :=
  sheafFreeIso f (bI.equivFun.symm.trans bJ.equivFun)

theorem completeNetSourceIso_evaluation
    (bI bJ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    (completeNetSourceIso f β bI bJ).hom ≫ netEvaluation β (completeNetSections f β bJ) =
      netEvaluation β (completeNetSections f β bI) := by
  let := modulesLinearOverField k f
  change (linearEquivIso (structureModule X) (bI.equivFun.symm.trans bJ.equivFun)).hom ≫
    netEvaluation β (completeNetSections f β bJ) = _
  exact basis_evaluation_triangle_of_generators (structureModule X) β bI bJ
    (sectionHomLinearEquiv f β).toLinearMap
    (netEvaluation β (completeNetSections f β bI))
    (netEvaluation β (completeNetSections f β bJ))
    (completeNetEvaluation_generator f β bI) (completeNetEvaluation_generator f β bJ)

end CompleteNetBasisChange

section NativeSections

open AlgebraicGeometry Opposite
open M9Native.MukaiDualSpanSections M9Native.CurveDivisorSections

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable (D : X.IdealSheafData) (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]

theorem twistDown_H0_injective :
    Function.Injective (cohomologyOverFieldMap k f (twistDownι D β) 0) := by
  obtain ⟨_δ, hi, _he, _hd, _hd'⟩ :=
    exists_cohomologyOverField_longExactSequence k f (restrictionSequence_shortExact D β)
  exact hi

/-- The two original sections of the actual twisted-down pencil. -/
def completePencilSections
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0)) :
    ULift.{u} (Fin 2) → (twistDown D β).sections := fun i =>
  Stacks.PresheafOfModules.sectionOfTop (twistDown D β).val
    ((cohomologyOverFieldZeroLinearIso k f (twistDown D β)).hom (bξ i))

/-- A chosen complete net basis extending the images of the two actual pencil sections. -/
def adaptedH0Basis
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0) :=
  (Classical.choose (exists_basis_extending_pair
    (bξ.reindex Equiv.ulift) (bβ.reindex Equiv.ulift)
    (cohomologyOverFieldMap k f (twistDownι D β) 0).hom
    (twistDown_H0_injective f D β))).reindex Equiv.ulift.symm

theorem adaptedH0Basis_left
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) (i : Fin 2) :
    adaptedH0Basis f D β bξ bβ ⟨i.castSucc⟩ =
      (cohomologyOverFieldMap k f (twistDownι D β) 0) (bξ ⟨i⟩) := by
  simpa [adaptedH0Basis] using (Classical.choose_spec (exists_basis_extending_pair
    (bξ.reindex Equiv.ulift) (bβ.reindex Equiv.ulift)
    (cohomologyOverFieldMap k f (twistDownι D β) 0).hom
    (twistDown_H0_injective f D β))) i

omit [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β] in
theorem completePencilSections_eval_top
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (i : ULift.{u} (Fin 2)) :
    (completePencilSections f D β bξ i).eval (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f (twistDown D β)).hom (bξ i) :=
  Stacks.PresheafOfModules.sectionOfTop_val_top _ _

omit [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β] in
theorem completePencilSections_map_top
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (i : ULift.{u} (Fin 2)) :
    (SheafOfModules.sectionsMap (twistDownι D β) (completePencilSections f D β bξ i)).eval
        (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f β).hom
        ((cohomologyOverFieldMap k f (twistDownι D β) 0) (bξ i)) := by
  change (twistDownι D β).app ⊤
    ((completePencilSections f D β bξ i).eval (op ⊤)) = _
  exact (congrArg (fun a => (twistDownι D β).app ⊤ a)
    (completePencilSections_eval_top f D β bξ i)).trans
      (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f
        (twistDownι D β) (bξ i)).symm

/-- The adapted net uses precisely the original included pencil sections. -/
theorem adaptedSections_left
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) (i : Fin 2) :
    completeNetSections f β (adaptedH0Basis f D β bξ bβ) ⟨i.castSucc⟩ =
      SheafOfModules.sectionsMap (twistDownι D β) (completePencilSections f D β bξ ⟨i⟩) := by
  apply (bijective_sections_eval_top β).injective
  change (completeNetSections f β (adaptedH0Basis f D β bξ bβ) ⟨i.castSucc⟩).eval (op ⊤) =
    (SheafOfModules.sectionsMap (twistDownι D β) (completePencilSections f D β bξ ⟨i⟩)).eval (op ⊤)
  exact (completeNetSections_eval_top f β (adaptedH0Basis f D β bξ bβ) ⟨i.castSucc⟩).trans
    ((congrArg (fun a => (cohomologyOverFieldZeroLinearIso k f β).hom a)
      (adaptedH0Basis_left f D β bξ bβ i)).trans
        (completePencilSections_map_top f D β bξ ⟨i⟩).symm)

end NativeSections

section OriginalNetTransport

open AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.CurveDivisorSections

variable {X : Scheme.{u}} (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (ns : ULift.{u} (Fin 3) → β.sections)
    (t : ULift.{u} (Fin 2) → (twistDown D β).sections) (s : β.sections)
    (e : netFree X ≅ adaptedFree X)
    (he : e.hom ≫ adaptedEvaluation (twistDownι D β) t s = netEvaluation β ns)

/-- The original dual span and the adapted dual kernel are identified by the
actual commuting evaluation-source isomorphism. -/
def originalDualSpanIso :
    dualSheaf (adaptedKernel (twistDownι D β) t s) ≅ dualSpan β ns :=
  dualIso (kernelSourceIso e (netEvaluation β ns)
    (adaptedEvaluation (twistDownι D β) t s) he)

include e he in
omit [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β] in
theorem adaptedEvaluation_epi_of_original
    (hgen : Epi (netEvaluation β ns)) :
    Epi (adaptedEvaluation (twistDownι D β) t s) := by
  have hc : Epi (e.hom ≫ adaptedEvaluation (twistDownι D β) t s) := by
    rw [he]
    exact hgen
  exact (epi_comp_iff_of_epi e.hom _).mp hc

def pencilInclusion (hgen : Epi (netEvaluation β ns)) :
    Stacks.Divisors.divisorSheaf D ⟶ dualSpan β ns :=
  adaptedPencilInclusion D β t s
      (adaptedEvaluation_epi_of_original D β ns t s e he hgen) ≫
    (originalDualSpanIso D β ns t s e he).hom

def pencilProjection (hgen : Epi (pencilEvaluation (twistDown D β) t)) :
    dualSpan β ns ⟶ twistDown D β :=
  (originalDualSpanIso D β ns t s e he).inv ≫ adaptedPencilProjection D β t s hgen

theorem pencil_zero (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (netEvaluation β ns)) :
    pencilInclusion D β ns t s e he hβ ≫ pencilProjection D β ns t s e he hξ = 0 := by
  simp [pencilInclusion, pencilProjection, adaptedPencil_zero]

/-- The concrete divisor-to-original-dual-span-to-pencil complex. -/
def pencilSequence (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (netEvaluation β ns)) : ShortComplex X.Modules :=
  ShortComplex.mk (pencilInclusion D β ns t s e he hβ)
    (pencilProjection D β ns t s e he hξ) (pencil_zero D β ns t s e he hξ hβ)

theorem pencilSequence_shortExact (hξ : Epi (pencilEvaluation (twistDown D β) t))
    (hβ : Epi (netEvaluation β ns)) :
    (pencilSequence D β ns t s e he hξ hβ).ShortExact := by
  let hβ' := adaptedEvaluation_epi_of_original D β ns t s e he hβ
  let eS : adaptedPencilSequence D β t s hξ hβ' ≅ pencilSequence D β ns t s e he hξ hβ :=
    ShortComplex.isoMk (Iso.refl _) (originalDualSpanIso D β ns t s e he) (Iso.refl _)
      (by simp [adaptedPencilSequence, pencilSequence, pencilInclusion])
      (by simp [adaptedPencilSequence, pencilSequence, pencilProjection])
  exact ShortComplex.shortExact_of_iso eS (adaptedPencilSequence_shortExact D β t s hξ hβ')

end OriginalNetTransport

section CompletePencilQuotient

open AlgebraicGeometry M9Native.MukaiBundle M9Native.MukaiDualSpanSections
open M9Native.CurveDivisorSections M9Native.MukaiBundleDeterminant

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (β : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D β) 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))

/-- The extra section in a genuine basis extending the included pencil. -/
def adaptedExtraSection : β.sections :=
  completeNetSections f β (adaptedH0Basis f D β bξ bβ) ⟨Fin.last 2⟩

/-- An actual isomorphism from the original complete free net to the
first-two-plus-last source of the pencil diagram. -/
def completePencilSourceIso : netFree X ≅ adaptedFree X :=
  completeNetSourceIso f β bβ (adaptedH0Basis f D β bξ bβ) ≪≫ splitNetIso X

/- The source isomorphism commutes with the original evaluation map. -/
omit [Stacks.Divisors.IsEffectiveCartierDivisor D] in
theorem completePencilSourceIso_evaluation :
    (completePencilSourceIso f D β bξ bβ).hom ≫
        adaptedEvaluation (twistDownι D β) (completePencilSections f D β bξ)
          (adaptedExtraSection f D β bξ bβ) =
      netEvaluation β (completeNetSections f β bβ) := by
  change ((completeNetSourceIso f β bβ (adaptedH0Basis f D β bξ bβ)).hom ≫
    splitNetHom X) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q =>
      (completeNetSourceIso f β bβ (adaptedH0Basis f D β bξ bβ)).hom ≫ q)
        (splitNetHom_evaluation (twistDownι D β) (completePencilSections f D β bξ)
          (adaptedExtraSection f D β bξ bβ)
          (completeNetSections f β (adaptedH0Basis f D β bξ bβ))
          (adaptedSections_left f D β bξ bβ) rfl)).trans
      (completeNetSourceIso_evaluation f β bβ (adaptedH0Basis f D β bξ bβ)))

/-- The actual Mukai pencil quotient complex, with its concrete injection
and projection on the original dual span of the original complete net. -/
def completePencilSequence
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) : ShortComplex X.Modules :=
  pencilSequence D β (completeNetSections f β bβ) (completePencilSections f D β bξ)
    (adaptedExtraSection f D β bξ bβ) (completePencilSourceIso f D β bξ bβ)
    (completePencilSourceIso_evaluation f D β bξ bβ) hξ hβ

/-- Mukai's divisor-line/pencil quotient is derived from the actual
complete evaluations and the actual Cartier ideal inclusion. -/
theorem completePencilSequence_shortExact
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    (completePencilSequence f D β bξ bβ hξ hβ).ShortExact :=
  pencilSequence_shortExact D β (completeNetSections f β bβ) (completePencilSections f D β bξ)
    (adaptedExtraSection f D β bξ bβ) (completePencilSourceIso f D β bξ bβ)
    (completePencilSourceIso_evaluation f D β bξ bβ) hξ hβ

theorem completePencilSequence_X₁
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    (completePencilSequence f D β bξ bβ hξ hβ).X₁ = Stacks.Divisors.divisorSheaf D := rfl

theorem completePencilSequence_X₂
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    (completePencilSequence f D β bξ bβ hξ hβ).X₂ =
      dualSpan β (completeNetSections f β bβ) := rfl

theorem completePencilSequence_X₃
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    (completePencilSequence f D β bξ bβ hξ hβ).X₃ = twistDown D β := rfl

/-- The two explicit maps of the original complete dual span realize the
actual line-bundle extension, without an extension-class premise. -/
theorem exists_completePencil_shortExact
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    ∃ (i : Stacks.Divisors.divisorSheaf D ⟶ dualSpan β (completeNetSections f β bβ))
      (p : dualSpan β (completeNetSections f β bβ) ⟶ twistDown D β)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact :=
  ⟨(completePencilSequence f D β bξ bβ hξ hβ).f,
    (completePencilSequence f D β bξ bβ hξ hβ).g,
    (completePencilSequence f D β bξ bβ hξ hβ).zero,
    completePencilSequence_shortExact f D β bξ bβ hξ hβ⟩

/-- The actual determinant relation of this constructed extension follows
from its proved short exactness and the native exterior comparison map. -/
def completePencilTopExteriorIso
    (hξ : Epi (pencilEvaluation (twistDown D β) (completePencilSections f D β bξ)))
    (hβ : Epi (netEvaluation β (completeNetSections f β bβ))) :
    topExterior (dualSpan β (completeNetSections f β bβ)) 2 ≅
      tensor (Stacks.Divisors.divisorSheaf D) (twistDown D β) := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Divisors.divisorSheaf D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  letI := twistDown_isInvertible D β
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
    (Stacks.Divisors.divisorSheaf D)
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (twistDown D β)
  let S := completePencilSequence f D β bξ bβ hξ hβ
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ 1 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (Stacks.Divisors.divisorSheaf D) 1
    infer_instance
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistDown D β) 1
    infer_instance
  exact (Scheme.Modules.exteriorPowerTensorExteriorPowerIso S.f S.g S.zero
    (completePencilSequence_shortExact f D β bξ bβ hξ hβ) 1 0).symm ≪≫
      tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf (Stacks.Divisors.divisorSheaf D))
        (Scheme.Modules.exteriorPowerOneIsoSelf (twistDown D β))

end CompletePencilQuotient

end M9Native.MukaiPencilQuotient
