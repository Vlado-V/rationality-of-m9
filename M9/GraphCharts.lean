module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import M9.Basic

/-!
# Actual graph coordinates for the genus-nine construction

This file proves the linear-algebra correspondence used at the beginning of
Section 3 of the pinned manuscript.  A subspace of a product whose two
coordinate projections are injective is recovered from its two actual
images and the induced linear isomorphism.  Conversely, the range of the
graph embedding recovers all three pieces of data.

These are correspondences of linear-algebra data.  No assertion about
varieties, dense opens, birational maps, or invariant function fields is
deduced from the set-level equivalence.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.GraphCharts

universe u v w

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]
variable (W : Type w) [AddCommGroup W] [Module K W]

/-- The first coordinate map on the actual subspace. -/
def firstMap (U : Submodule K (V × W)) : U →ₗ[K] V :=
  (LinearMap.fst K V W).comp U.subtype

/-- The second coordinate map on the actual subspace. -/
def secondMap (U : Submodule K (V × W)) : U →ₗ[K] W :=
  (LinearMap.snd K V W).comp U.subtype

/-- The two-injective-projection locus, in the subspace convention. -/
def Chart := {U : Submodule K (V × W) //
  Function.Injective (firstMap K V W U) ∧ Function.Injective (secondMap K V W U)}

/-- Both projection images and an actual linear isomorphism between them. -/
structure GraphData where
  left : Submodule K V
  right : Submodule K W
  equiv : left ≃ₗ[K] right

variable {K V W}

def leftImage (U : Submodule K (V × W)) : Submodule K V :=
  LinearMap.range (firstMap K V W U)

def rightImage (U : Submodule K (V × W)) : Submodule K W :=
  LinearMap.range (secondMap K V W U)

def leftEquiv (C : Chart K V W) : C.val ≃ₗ[K] leftImage C.val :=
  LinearEquiv.ofInjective (firstMap K V W C.val) C.property.1

def rightEquiv (C : Chart K V W) : C.val ≃ₗ[K] rightImage C.val :=
  LinearEquiv.ofInjective (secondMap K V W C.val) C.property.2

/-- Extracting the graph isomorphism by passing through the original subspace. -/
def fromChart (C : Chart K V W) : GraphData K V W where
  left := leftImage C.val
  right := rightImage C.val
  equiv := (leftEquiv C).symm.trans (rightEquiv C)

/-- The genuine graph embedding into the original ambient product. -/
def graphEmbedding (A : GraphData K V W) : A.left →ₗ[K] (V × W) :=
  A.left.subtype.prod (A.right.subtype.comp A.equiv.toLinearMap)

@[simp] theorem graphEmbedding_apply (A : GraphData K V W) (s : A.left) :
    graphEmbedding A s = ((s : V), (A.equiv s : W)) := rfl

theorem graphEmbedding_injective (A : GraphData K V W) :
    Function.Injective (graphEmbedding A) := by
  intro s t h
  exact Subtype.ext (congrArg Prod.fst h)

/-- The graph is an actual linear subspace of the ambient product. -/
def graph (A : GraphData K V W) : Submodule K (V × W) :=
  LinearMap.range (graphEmbedding A)

def graphEquiv (A : GraphData K V W) : A.left ≃ₗ[K] graph A :=
  LinearEquiv.ofInjective (graphEmbedding A) (graphEmbedding_injective A)

theorem graph_first_injective (A : GraphData K V W) :
    Function.Injective (firstMap K V W (graph A)) := by
  intro x y h
  obtain ⟨s, hs⟩ := x.property
  obtain ⟨t, ht⟩ := y.property
  have hst : s = t := by
    apply Subtype.ext
    change x.val.1 = y.val.1 at h
    rw [← hs, ← ht] at h
    exact h
  apply Subtype.ext
  rw [← hs, ← ht, hst]

theorem graph_second_injective (A : GraphData K V W) :
    Function.Injective (secondMap K V W (graph A)) := by
  intro x y h
  obtain ⟨s, hs⟩ := x.property
  obtain ⟨t, ht⟩ := y.property
  have hst : s = t := by
    apply A.equiv.injective
    apply Subtype.ext
    change x.val.2 = y.val.2 at h
    rw [← hs, ← ht] at h
    exact h
  apply Subtype.ext
  rw [← hs, ← ht, hst]

def toChart (A : GraphData K V W) : Chart K V W :=
  ⟨graph A, graph_first_injective A, graph_second_injective A⟩

@[simp] theorem leftImage_graph (A : GraphData K V W) : leftImage (graph A) = A.left := by
  ext v
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := x.property
    have heq : (s : V) = v := (congrArg Prod.fst hs).trans hx
    exact heq ▸ s.property
  · intro hv
    exact ⟨⟨graphEmbedding A ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩⟩, rfl⟩

@[simp] theorem rightImage_graph (A : GraphData K V W) : rightImage (graph A) = A.right := by
  ext w
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := x.property
    have heq : (A.equiv s : W) = w := (congrArg Prod.snd hs).trans hx
    exact heq ▸ (A.equiv s).property
  · intro hw
    refine ⟨⟨graphEmbedding A (A.equiv.symm ⟨w, hw⟩), ⟨_, rfl⟩⟩, ?_⟩
    change (A.equiv (A.equiv.symm ⟨w, hw⟩) : W) = w
    simp

theorem graph_injective : Function.Injective (graph (K := K) (V := V) (W := W)) := by
  intro A B h
  have hl : A.left = B.left := by rw [← leftImage_graph A, ← leftImage_graph B, h]
  have hr : A.right = B.right := by rw [← rightImage_graph A, ← rightImage_graph B, h]
  cases A with
  | mk S T e =>
    cases B with
    | mk S' T' e' =>
      dsimp only at hl hr
      subst S'
      subst T'
      have he : e = e' := by
        apply LinearEquiv.ext
        intro s
        apply Subtype.ext
        have hs : ((s : V), (e s : W)) ∈ graph (GraphData.mk S T e) := ⟨s, rfl⟩
        rw [h] at hs
        obtain ⟨t, ht⟩ := hs
        have hts : t = s := Subtype.ext (congrArg Prod.fst ht)
        subst t
        exact (congrArg Prod.snd ht).symm
      subst e'
      rfl

theorem graphEmbedding_fromChart (C : Chart K V W) (s : (fromChart C).left) :
    graphEmbedding (fromChart C) s = ((leftEquiv C).symm s).val := by
  apply Prod.ext
  · exact (LinearEquiv.ofInjective_symm_apply (firstMap K V W C.val) s).symm
  · rfl

/-- The original subspace is recovered from its actual projection images. -/
@[simp] theorem graph_fromChart (C : Chart K V W) : graph (fromChart C) = C.val := by
  ext z
  constructor
  · rintro ⟨s, hs⟩
    rw [graphEmbedding_fromChart] at hs
    exact hs ▸ ((leftEquiv C).symm s).property
  · intro hz
    refine ⟨leftEquiv C ⟨z, hz⟩, ?_⟩
    rw [graphEmbedding_fromChart, LinearEquiv.symm_apply_apply]

@[simp] theorem toChart_fromChart (C : Chart K V W) : toChart (fromChart C) = C :=
  Subtype.ext (graph_fromChart C)

@[simp] theorem fromChart_toChart (A : GraphData K V W) : fromChart (toChart A) = A :=
  graph_injective (graph_fromChart (toChart A))

/-- The mutually inverse graph constructions, as an actual equivalence of data. -/
def chartEquiv : Chart K V W ≃ GraphData K V W where
  toFun := fromChart
  invFun := toChart
  left_inv := toChart_fromChart
  right_inv := fromChart_toChart

/-- The isomorphism extracted from a chart has the original dimension. -/
theorem fromChart_finrank_left (C : Chart K V W) :
    Module.finrank K (fromChart C).left = Module.finrank K C.val :=
  (leftEquiv C).finrank_eq.symm

theorem fromChart_finrank_right (C : Chart K V W) :
    Module.finrank K (fromChart C).right = Module.finrank K C.val :=
  (rightEquiv C).finrank_eq.symm

theorem finrank_graph (A : GraphData K V W) :
    Module.finrank K (graph A) = Module.finrank K A.left :=
  (graphEquiv A).finrank_eq.symm

/-- Rank-`r` subspaces in the two-injective-projection locus. -/
def RankChart (r : ℕ) := {C : Chart K V W // Module.finrank K C.val = r}

/-- The two actual projection images are both of rank `r`. -/
def RankGraphData (r : ℕ) := {A : GraphData K V W //
  Module.finrank K A.left = r ∧ Module.finrank K A.right = r}

/-- The graph correspondence preserves the subspace-rank convention. -/
def rankChartEquiv (r : ℕ) : RankChart (K := K) (V := V) (W := W) r ≃
    RankGraphData (K := K) (V := V) (W := W) r :=
  Equiv.subtypeEquiv chartEquiv (fun C => by
    change Module.finrank K C.val = r ↔
      Module.finrank K (fromChart C).left = r ∧ Module.finrank K (fromChart C).right = r
    rw [fromChart_finrank_left, fromChart_finrank_right]
    exact ⟨fun h => ⟨h, h⟩, And.left⟩)

/-- Exchange acts on the actual graph isomorphism by inversion. -/
def swapData (A : GraphData K V W) : GraphData K W V :=
  ⟨A.right, A.left, A.equiv.symm⟩

@[simp] theorem swapData_swapData (A : GraphData K V W) : swapData (swapData A) = A := rfl

theorem graph_swap (A : GraphData K V W) :
    (graph A).map (LinearEquiv.prodComm K V W).toLinearMap = graph (swapData A) := by
  ext z
  constructor
  · rintro ⟨x, ⟨s, hs⟩, hx⟩
    refine ⟨A.equiv s, ?_⟩
    rw [← hx, ← hs]
    simp [graphEmbedding, swapData]
  · rintro ⟨t, ht⟩
    refine ⟨graphEmbedding A (A.equiv.symm t), ⟨_, rfl⟩, ?_⟩
    rw [← ht]
    simp [graphEmbedding, swapData]

def swapChart (C : Chart K V W) : Chart K W V := toChart (swapData (fromChart C))

theorem swapChart_subspace (C : Chart K V W) :
    (swapChart C).val = C.val.map (LinearEquiv.prodComm K V W).toLinearMap := by
  change graph (swapData (fromChart C)) = _
  rw [← graph_swap, graph_fromChart]

@[simp] theorem fromChart_swapChart (C : Chart K V W) :
    fromChart (swapChart C) = swapData (fromChart C) := fromChart_toChart _

section Pairing

variable (P : V →ₗ[K] W →ₗ[K] K)

/-- The standard alternating form attached to a pairing of the two summands. -/
def symplecticForm : LinearMap.BilinForm K (V × W) :=
  let B := P.compl₁₂ (LinearMap.fst K V W) (LinearMap.snd K V W)
  B - B.flip

@[simp] theorem symplecticForm_apply (x y : V × W) :
    symplecticForm P x y = P x.1 y.2 - P y.1 x.2 := rfl

theorem symplecticForm_isAlt : (symplecticForm P).IsAlt := fun _x => sub_self _

/-- `β(u,v)=P(u,x(v))` on the actual left projection image. -/
def graphPairing (A : GraphData K V W) : LinearMap.BilinForm K A.left :=
  P.compl₁₂ A.left.subtype (A.right.subtype.comp A.equiv.toLinearMap)

/-- Pulling the ambient form back by the actual graph embedding. -/
def graphForm (A : GraphData K V W) : LinearMap.BilinForm K A.left :=
  (symplecticForm P).compl₁₂ (graphEmbedding A) (graphEmbedding A)

theorem graphForm_eq (A : GraphData K V W) :
    graphForm P A = graphPairing P A - (graphPairing P A).flip := by
  ext s t
  rfl

@[simp] theorem graphForm_apply (A : GraphData K V W) (s t : A.left) :
    graphForm P A s t = P (s : V) (A.equiv t : W) - P (t : V) (A.equiv s : W) := rfl

/-- Nondegeneracy on the actual graph agrees with nondegeneracy of its
pulled-back form on the projection image. -/
theorem graph_restrict_nondegenerate_iff (A : GraphData K V W) :
    ((symplecticForm P).restrict (graph A)).Nondegenerate ↔ (graphForm P A).Nondegenerate := by
  have he : LinearMap.BilinForm.congr (graphEquiv A).symm
      ((symplecticForm P).restrict (graph A)) = graphForm P A := by
    ext s t
    rfl
  rw [← he, LinearMap.BilinForm.nondegenerate_congr_iff]

/-- For alternating `β`, the graph restriction is literally `2β`. -/
theorem graphForm_eq_two_smul (A : GraphData K V W)
    (hβ : (graphPairing P A).IsAlt) :
    graphForm P A = (2 : K) • graphPairing P A := by
  ext s t
  change graphPairing P A s t - graphPairing P A t s = (2 : K) * graphPairing P A s t
  rw [← hβ.neg_eq s t, sub_neg_eq_add, two_mul]

/-- A nonsingular alternating `β` gives a nondegenerate actual graph when
two is invertible, as used in Section 3. -/
theorem graph_nondegenerate_of_alternating (A : GraphData K V W) (h2 : (2 : K) ≠ 0)
    (hβ : (graphPairing P A).IsAlt) (hn : (graphPairing P A).Nondegenerate) :
    ((symplecticForm P).restrict (graph A)).Nondegenerate := by
  rw [graph_restrict_nondegenerate_iff, graphForm_eq_two_smul P A hβ]
  constructor
  · intro s hs
    apply hn.1 s
    intro t
    have h := hs t
    change (2 : K) * graphPairing P A s t = 0 at h
    exact (mul_eq_zero.mp h).resolve_left h2
  · intro t ht
    apply hn.2 t
    intro s
    have h := ht s
    change (2 : K) * graphPairing P A s t = 0 at h
    exact (mul_eq_zero.mp h).resolve_left h2

end Pairing

section SymmetricThree

variable (K : Type*) [Field K]

/-- The actual symmetric ternary-matrix space and its actual algebraic dual. -/
abbrev Q := ↥(M9.Symmetric3 K)
abbrev Qdual := Module.Dual K (Q K)

/-- The rank-four graph chart of Section 3. -/
abbrev SymmetricRankFourChart := RankChart (K := K) (V := Q K) (W := Qdual K) 4

abbrev SymmetricRankFourData := RankGraphData (K := K) (V := Q K) (W := Qdual K) 4

/-- Concrete rank-four specialization of the genuine graph correspondence. -/
def symmetricRankFourGraphEquiv : SymmetricRankFourChart K ≃ SymmetricRankFourData K :=
  rankChartEquiv 4

theorem symmetric_ambient_dimensions :
    Module.finrank K (Q K) = 6 ∧ Module.finrank K (Qdual K) = 6 := by
  constructor
  · exact M9.finrank_symmetric3 K
  · change Module.finrank K (Module.Dual K (Q K)) = 6
    rw [Subspace.dual_finrank_eq]
    exact M9.finrank_symmetric3 K

/-- Evaluation realizes the canonical `Q × Q∨` alternating form. -/
def evaluationPairing : Q K →ₗ[K] Qdual K →ₗ[K] K := Module.Dual.eval K (Q K)

@[simp] theorem symmetric_symplectic_apply (x y : Q K × Qdual K) :
    symplecticForm (evaluationPairing K) x y = y.2 x.1 - x.2 y.1 := rfl

end SymmetricThree

end M9.GraphCharts
