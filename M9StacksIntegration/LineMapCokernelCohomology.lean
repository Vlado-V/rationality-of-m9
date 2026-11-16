module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CokernelSupportDegree

/-!
# The actual cokernel of a nonzero map between curve line bundles

The actual morphism and its literal native cokernel are retained. Generic
rank-one linear algebra proves injectivity and zero-dimensional support;
native Euler additivity and native zero-dimensional cohomology then give
the original H0 dimension as the degree jump and kill the original H1.

The generic-stalk arguments adapt the corresponding short proofs in the
pinned StacksFrontier `Curves.RiemannHurwitzDegree` (Tags 0C1C, 0B40),
without importing that file's unrelated local Riemann--Hurwitz closure.
The package source is unchanged. No support, injectivity, cohomology
count, or degree-jump equality is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.ModuleStalk
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.LineMapCokernelCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A morphism into an actual line bundle is determined by its generic stalk. -/
theorem eq_zero_of_generic_stalk {N M : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (φ : N ⟶ M) (h : ∀ a, mapFun φ (genericPoint X) a = 0) : φ = 0 := by
  have : M.IsCoherent := isCoherent_of_isInvertible' M
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have hM := isTorsionFree_of_isInvertibleModule M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext t
  by_cases hV : Nonempty V.unop
  · have hη : genericPoint X ∈ V.unop :=
      ((genericPoint_spec X).mem_open_set_iff V.unop.isOpen).mpr (by simpa using hV)
    apply injective_generic_germ_of_isTorsionFree M hM hη
    have h1 := (mapFun_germ φ (genericPoint X) V.unop hη t).symm.trans
      (h ((N.presheaf.germ V.unop (genericPoint X) hη).hom t))
    exact h1.trans (map_zero _).symm
  · let underlying : TopCat.Sheaf Ab.{u} X.toTopCat := ⟨M.presheaf, M.isSheaf⟩
    exact TopCat.Presheaf.section_ext underlying V.unop (φ.val.app V t) 0 fun x hx =>
      False.elim (hV ⟨⟨x, hx⟩⟩)

variable {N M : X.Modules}
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]

/-- A nonzero morphism between actual line bundles is injective. -/
theorem mono_of_ne_zero (φ : N ⟶ M) (hφ : φ ≠ 0) : Mono φ := by
  refine Preadditive.mono_of_kernel_zero ?_
  have hK : genericPoint X ∉ SheafOfModules.supp (kernel φ) := by
    rintro ⟨a₀, ha⟩
    let a : TopCat.Presheaf.stalk (C := Ab.{u}) (kernel φ).presheaf (genericPoint X) := a₀
    let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have hinj : Function.Injective (mapFun (kernel.ι φ) (genericPoint X)) :=
      TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (f := (kernel.ι φ).mapPresheaf)
        (fun U => Scheme.Modules.injective_app_of_mono (kernel.ι φ) U) (genericPoint X)
    have hb : mapFun (kernel.ι φ) (genericPoint X) a ≠ 0 := fun h0 =>
      ha (hinj (h0.trans (map_zero _).symm))
    have hrank := finrank_stalk_genericPoint_eq_one_of_isInvertible N
    have hspan := (finrank_eq_one_iff_of_nonzero' _ hb).mp hrank
    apply hφ
    refine eq_zero_of_generic_stalk φ fun c => ?_
    obtain ⟨r, hr⟩ := hspan c
    rw [← hr, mapFun_smul, ← mapFun_comp, kernel.condition]
    obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq _ a
    rw [← ht, mapFun_germ]
    simp
  have : N.IsCoherent := isCoherent_of_isInvertible' N
  have : N.IsQuasicoherent := isQuasicoherent_of_isCoherent N
  have : (kernel φ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel φ
  exact (isZero_of_mono_of_genericPoint_notMem (kernel.ι φ) hK).eq_of_src _ _

omit [IsIntegral X] in
/-- The literal native cokernel is coherent. -/
theorem cokernel_isCoherent (φ : N ⟶ M) : (cokernel φ).IsCoherent := by
  have : N.IsCoherent := isCoherent_of_isInvertible' N
  have : M.IsCoherent := isCoherent_of_isInvertible' M
  have : N.IsQuasicoherent := isQuasicoherent_of_isCoherent N
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have : (cokernel φ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel φ
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent
    (inferInstance : M.IsCoherent) (cokernel.π φ)

omit [IsLocallyNoetherian X] in
/-- Actual support has dimension zero, derived from nonvanishing. -/
theorem cokernel_support_le_zero [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (φ : N ⟶ M) (hφ : φ ≠ 0) :
    topologicalKrullDim (SheafOfModules.supp (cokernel φ)) ≤ 0 := by
  have : (cokernel φ).IsCoherent := cokernel_isCoherent φ
  have hne : ∃ a, mapFun (φ ≫ 𝟙 _) (genericPoint X) a ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hφ (eq_zero_of_generic_stalk φ fun a => by simpa using hall a)
  exact topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim _
    (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ ‹_›)
    (genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp φ (𝟙 _) hne)

/-- The original map and original quotient form the actual short exact sequence. -/
theorem cokernel_shortExact (φ : N ⟶ M) (hφ : φ ≠ 0) :
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact := by
  let := mono_of_ne_zero φ hφ
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ)
    inferInstance inferInstance

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- Every positive cohomology group of the actual quotient vanishes. -/
theorem cokernel_cohomology_isZero (φ : N ⟶ M) (hφ : φ ≠ 0)
    (i : ℕ) (hi : 0 < i) :
    letI := cokernel_isCoherent φ
    IsZero (cohomologyOverField k f (cokernel φ) i) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let := cokernel_isCoherent φ
  exact isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f
    (cokernel φ) (cokernel_support_le_zero hdim φ hφ) i hi

/-- The degree jump is the actual H0 dimension, without a numerical premise. -/
theorem cokernel_h0_eq_degree_jump (φ : N ⟶ M) (hφ : φ ≠ 0) :
    letI := cokernel_isCoherent φ
    (Module.finrank k (cohomologyOverField k f (cokernel φ) 0) : ℤ) =
      invertibleCurveDegree k f hdim M - invertibleCurveDegree k f hdim N := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let := cokernel_isCoherent φ
  have : N.IsCoherent := isCoherent_of_isInvertible' N
  have : M.IsCoherent := isCoherent_of_isInvertible' M
  have hadd := eulerCharacteristic_add_of_shortExact k f (cokernel_shortExact φ hφ)
  have hN := invertibleCurveDegree_eq_eulerCharacteristic_sub k f hdim N
  have hM := invertibleCurveDegree_eq_eulerCharacteristic_sub k f hdim M
  have hQ := eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero
    k f (cokernel φ) (cokernel_support_le_zero hdim φ hφ)
  change eulerCharacteristic k f M =
    eulerCharacteristic k f N + eulerCharacteristic k f (cokernel φ) at hadd
  linarith

include k f hdim in
/-- The finite support is obtained from the original line-map geometry. -/
theorem cokernel_support_finite (φ : N ⟶ M) (hφ : φ ≠ 0) :
    (SheafOfModules.supp (cokernel φ)).Finite := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let := cokernel_isCoherent φ
  exact finite_supp_of_supp_le_zero k f (cokernel φ)
    (cokernel_support_le_zero hdim φ hφ)

end M9Native.LineMapCokernelCohomology
