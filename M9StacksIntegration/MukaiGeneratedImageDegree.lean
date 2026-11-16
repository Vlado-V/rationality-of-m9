module

public import M9StacksIntegration.MukaiGeneratedImage
public import M9StacksIntegration.MukaiCohomologyParity
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# Degree of an actual elementary generated modification

These are cohomological consequences of actual quotient maps. Support
and H0 bounds refer to the actual sheaves, never an assigned length.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiGeneratedImage

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual support can only shrink under an epimorphism. -/
theorem supp_subset_of_epi {A B : X.Modules} (q : A ⟶ B) [Epi q] :
    SheafOfModules.supp B ⊆ SheafOfModules.supp A := by
  intro x hx
  by_contra hn
  have ha := (Scheme.Modules.notMem_supp_iff_isZero_stalk A x).mp hn
  letI : Epi ((Scheme.Modules.stalkFunctor X x).map q) :=
    (Scheme.Modules.stalkFunctor X x).map_epi q
  have hb := IsZero.of_epi ((Scheme.Modules.stalkFunctor X x).map q) ha
  exact ((Scheme.Modules.notMem_supp_iff_isZero_stalk B x).mpr hb) hx

/-- The actual support can only shrink under a monomorphism. -/
theorem supp_subset_of_mono {A B : X.Modules} (q : A ⟶ B) [Mono q] :
    SheafOfModules.supp A ⊆ SheafOfModules.supp B := by
  intro x hx
  by_contra hn
  have hb := (Scheme.Modules.notMem_supp_iff_isZero_stalk B x).mp hn
  letI : Mono ((Scheme.Modules.stalkFunctor X x).map q) :=
    (Scheme.Modules.stalkFunctor X x).map_mono q
  have ha := IsZero.of_mono ((Scheme.Modules.stalkFunctor X x).map q) hb
  exact ((Scheme.Modules.notMem_supp_iff_isZero_stalk A x).mpr ha) hx

/-- Support dimension is monotone for actual subsets of a scheme. -/
theorem support_dim_le_of_subset {A B : Set X} (h : A ⊆ B) :
    topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

variable (f : X ⟶ Spec (.of k)) [IsProper f]

/-- An actual quotient of a zero-dimensional coherent sheaf has no H1,
so global sections are right exact for this epimorphism. -/
theorem cohomology_zero_surjective_of_epi {A B : X.Modules}
    (q : A ⟶ B) [Epi q]
    [A.IsCoherent] [B.IsCoherent]
    (hA : topologicalKrullDim (SheafOfModules.supp A) ≤ 0) :
    Function.Surjective (cohomologyOverFieldMap k f q 0) := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  letI : (kernel q).IsCoherent := _root_.SheafOfModules.kernel_isCoherent q
  have hk : topologicalKrullDim (SheafOfModules.supp (kernel q)) ≤ 0 :=
    (support_dim_le_of_subset (supp_subset_of_mono (kernel.ι q))).trans hA
  have hz := isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero
    k f (kernel q) hk 1 (by decide)
  letI : Subsingleton (cohomologyOverField k f (kernel q) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  intro b
  apply (MukaiCohomologyParity.cohomologyBoundary_exact_middle k f hS 0 b).mp
  exact Subsingleton.elim _ _

/-- Therefore actual H0 dimension decreases under such a quotient. -/
theorem finrank_cohomology_zero_le_of_epi {A B : X.Modules}
    (q : A ⟶ B) [Epi q]
    [A.IsCoherent] [B.IsCoherent]
    (hA : topologicalKrullDim (SheafOfModules.supp A) ≤ 0) :
    Module.finrank k (cohomologyOverField k f B 0) ≤
      Module.finrank k (cohomologyOverField k f A 0) := by
  letI := finiteDimensional_cohomologyOverField_of_isProper k f A 0
  exact LinearMap.finrank_le_finrank_of_surjective
    (cohomology_zero_surjective_of_epi f q hA)

/-- The degree increase in a genuine rank-two elementary modification
is precisely the actual dimension of the torsion quotient. -/
theorem degree_eq_add_quotient_h0 {A B T : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2]
    [A.IsCoherent] [B.IsCoherent] [T.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    {i : A ⟶ B} {q : B ⟶ T} {w : i ≫ q = 0}
    (hdim : topologicalKrullDim X ≤ 1)
    (hS : (ShortComplex.mk i q w).ShortExact)
    (hT : topologicalKrullDim (SheafOfModules.supp T) ≤ 0) :
    curveDegree k f hdim B 2 =
      curveDegree k f hdim A 2 +
        Module.finrank k (cohomologyOverField k f T 0) := by
  rw [curveDegree_eq_eulerCharacteristic_sub, curveDegree_eq_eulerCharacteristic_sub]
  have hχ := eulerCharacteristic_add_of_shortExact k f hS
  change eulerCharacteristic k f B =
    eulerCharacteristic k f A + eulerCharacteristic k f T at hχ
  rw [hχ, eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k f T hT]
  ring

/-- A genuine quotient of a finite-support sheaf bounds the degree
increase of the original elementary modification. -/
theorem degree_le_of_quotient {A B T S : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2]
    [A.IsCoherent] [B.IsCoherent] [T.IsCoherent] [S.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    {i : A ⟶ B} {q : B ⟶ T} {w : i ≫ q = 0}
    (hdim : topologicalKrullDim X ≤ 1)
    (hAB : (ShortComplex.mk i q w).ShortExact)
    (e : S ⟶ T) [Epi e]
    (hS : topologicalKrullDim (SheafOfModules.supp S) ≤ 0)
    (d : ℕ) (hbound : Module.finrank k (cohomologyOverField k f S 0) ≤ d) :
    curveDegree k f hdim B 2 ≤ curveDegree k f hdim A 2 + d := by
  have hT : topologicalKrullDim (SheafOfModules.supp T) ≤ 0 :=
    (support_dim_le_of_subset (supp_subset_of_epi e)).trans hS
  have hdeg := degree_eq_add_quotient_h0 f hdim hAB hT
  have hH := finrank_cohomology_zero_le_of_epi f e hS
  omega

end M9Native.MukaiGeneratedImage

