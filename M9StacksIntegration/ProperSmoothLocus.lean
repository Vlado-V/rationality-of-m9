module

public import M9StacksIntegration.ProperGenericSmoothness

/-! The actual largest base open above which a proper morphism is smooth.
Its membership condition tests the original morphism at every point of the
original fibre, and it retains smoothness of arbitrary actual base changes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace M9Native.ProperSmoothLocus
open M9Native.ProperGenericSmoothness
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]

def goodOpen : Y.Opens :=
  ⟨(f '' ((f.smoothLocus : Set X)ᶜ))ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_goodOpen_iff (y : Y) : y ∈ goodOpen f ↔ ∀ x : X,f x=y → x ∈ f.smoothLocus := by
  constructor
  · intro hy x hxy
    by_contra hbad
    exact hy ⟨x,hbad,hxy⟩
  · intro h ⟨x,hbad,hxy⟩
    exact hbad (h x hxy)

theorem preimage_subset_smoothLocus :
    ((f ⁻¹ᵁ goodOpen f : X.Opens) : Set X) ⊆ (f.smoothLocus : Set X) := by
  intro x hx
  exact (mem_goodOpen_iff f (f x)).mp hx x rfl

instance preimage_comp_smooth : Smooth ((f ⁻¹ᵁ goodOpen f).ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff,← Scheme.Hom.preimage_smoothLocus_eq,eq_top_iff]
  exact fun x _ => preimage_subset_smoothLocus f x.2

instance restrict_smooth : Smooth (f ∣_ goodOpen f) :=
  MorphismProperty.of_postcomp (@Smooth) (W':=MorphismProperty.monomorphisms Scheme)
    (f ∣_ goodOpen f) (goodOpen f).ι inferInstance (by rw [morphismRestrict_ι];infer_instance)

instance restrict_proper : IsProper (f ∣_ goodOpen f) := inferInstance

/-- Every actual cartesian base change landing in the good open is smooth. -/
theorem smooth_of_isPullback {T F : Scheme.{u}} (p : T ⟶ Y)
    (hp : ∀ t : T,p t ∈ goodOpen f) (c : F ⟶ X) (h : F ⟶ T)
    (sq : IsPullback c h f p) : Smooth h := by
  have hrange : Set.range c ⊆ Set.range (f ⁻¹ᵁ goodOpen f).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x,rfl⟩
    change f (c x) ∈ goodOpen f
    rw [← Scheme.Hom.comp_apply,sq.w,Scheme.Hom.comp_apply]
    exact hp _
  have hbig := (IsOpenImmersion.isPullback_lift_id c (f ⁻¹ᵁ goodOpen f).ι hrange).paste_vert sq
  rw [Category.id_comp] at hbig
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hbig (preimage_comp_smooth f)

/-- Perfection of the actual generic field and regularity of the total source
make this explicit canonical good open nonempty. -/
theorem goodOpen_nonempty [IsIntegral Y] (hX : IsRegular X)
    [PerfectField (Y.residueField (genericPoint Y))] : (goodOpen f : Set Y).Nonempty := by
  refine ⟨genericPoint Y,(mem_goodOpen_iff f _).mpr fun x hx => ?_⟩
  exact generic_preimage_subset_smoothLocus f hX (by simpa only [Set.mem_preimage,
    Set.mem_singleton_iff] using hx)

end M9Native.ProperSmoothLocus
end
