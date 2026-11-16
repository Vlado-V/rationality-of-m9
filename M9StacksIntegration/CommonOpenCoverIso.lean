module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Gluing actual open charts over a common ambient scheme

Two schemes with monomorphic ambient maps are isomorphic when they have
the same actual chart domains, both chart families are open covers, and
the actual chart maps agree in the ambient scheme. Both inverse maps are
constructed by native scheme gluing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace M9Native.CommonOpenCoverIso

variable {ι : Type v} {Z Q S : Scheme.{u}} (A : ι → Scheme.{u})
  (a : ∀ i, A i ⟶ Z) (b : ∀ i, A i ⟶ Q)
  [∀ i, IsOpenImmersion (a i)] [∀ i, IsOpenImmersion (b i)]
  (ha : ∀ z : Z, ∃ i, z ∈ Set.range (a i))
  (hb : ∀ q : Q, ∃ i, q ∈ Set.range (b i))
  (z : Z ⟶ S) (q : Q ⟶ S) [Mono z] [Mono q]
  (h : ∀ i, a i ≫ z = b i ≫ q)

def sourceCover : Z.OpenCover :=
  Scheme.Cover.mkOfCovers ι A a (fun x => by
    obtain ⟨i,y,hy⟩ := ha x
    exact ⟨i,y,hy⟩)

def targetCover : Q.OpenCover :=
  Scheme.Cover.mkOfCovers ι A b (fun x => by
    obtain ⟨i,y,hy⟩ := hb x
    exact ⟨i,y,hy⟩)

include z h in
theorem forward_compatible (i j : ι) :
    pullback.fst (a i) (a j) ≫ b i = pullback.snd (a i) (a j) ≫ b j := by
  apply (cancel_mono q).1
  simp only [Category.assoc, ← h]
  simpa only [Category.assoc] using congrArg
    (fun r : pullback (a i) (a j) ⟶ Z => r ≫ z)
    (pullback.condition (f := a i) (g := a j))

include q h in
theorem backward_compatible (i j : ι) :
    pullback.fst (b i) (b j) ≫ a i = pullback.snd (b i) (b j) ≫ a j := by
  apply (cancel_mono z).1
  simp only [Category.assoc, h]
  simpa only [Category.assoc] using congrArg
    (fun r : pullback (b i) (b j) ⟶ Q => r ≫ q)
    (pullback.condition (f := b i) (g := b j))

def forward : Z ⟶ Q :=
  (sourceCover A a ha).glueMorphisms b (forward_compatible A a b z q h)

def backward : Q ⟶ Z :=
  (targetCover A b hb).glueMorphisms a (backward_compatible A a b z q h)

theorem source_forward (i : ι) : a i ≫ forward A a b ha z q h = b i :=
  (sourceCover A a ha).ι_glueMorphisms b (forward_compatible A a b z q h) i

theorem target_backward (i : ι) : b i ≫ backward A a b hb z q h = a i :=
  (targetCover A b hb).ι_glueMorphisms a (backward_compatible A a b z q h) i

theorem forward_backward : forward A a b ha z q h ≫ backward A a b hb z q h = 𝟙 Z := by
  apply (sourceCover A a ha).hom_ext
  intro i
  change a i ≫ (forward A a b ha z q h ≫ backward A a b hb z q h) = a i ≫ 𝟙 Z
  rw [← Category.assoc, source_forward, target_backward, Category.comp_id]

theorem backward_forward : backward A a b hb z q h ≫ forward A a b ha z q h = 𝟙 Q := by
  apply (targetCover A b hb).hom_ext
  intro i
  change b i ≫ (backward A a b hb z q h ≫ forward A a b ha z q h) = b i ≫ 𝟙 Q
  rw [← Category.assoc, target_backward, source_forward, Category.comp_id]

/-- The actual isomorphism, with the actual glued inverse. -/
def iso : Z ≅ Q :=
  ⟨forward A a b ha z q h, backward A a b hb z q h,
    forward_backward A a b ha hb z q h, backward_forward A a b ha hb z q h⟩

theorem iso_hom_ambient : (iso A a b ha hb z q h).hom ≫ q = z := by
  apply (sourceCover A a ha).hom_ext
  intro i
  change a i ≫ (forward A a b ha z q h ≫ q) = a i ≫ z
  rw [← Category.assoc, source_forward]
  exact (h i).symm

end M9Native.CommonOpenCoverIso
