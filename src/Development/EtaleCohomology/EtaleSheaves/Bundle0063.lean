module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0055
public import Development.EtaleCohomology.EtaleSheaves.Bundle0057
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044
public import Development.EtaleCohomology.EtaleSheaves.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ImageInPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.ImageInPf

theorem vanishing_le_ker {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range γ)) ≤ γ.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  show s ∈ RingHom.ker (γ.app U).hom
  rw [RingHom.mem_ker]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro x hx
  exfalso
  have hx' : γ x ∈ Y.basicOpen s := hx
  have hU : γ x ∈ U.1 := Y.basicOpen_le s hx'
  obtain ⟨y, hy⟩ : γ x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hU
  have h1 := hs y (by
    show U.2.fromSpec y ∈ closure (Set.range γ)
    rw [hy]; exact subset_closure ⟨x, rfl⟩)
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    show U.2.fromSpec y ∈ Y.basicOpen s
    rwa [hy]
  rw [U.2.fromSpec_preimage_basicOpen] at h2
  exact h2 h1

theorem ker_apply_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (U : Y.affineOpens) :
    γ.ker.ideal U = RingHom.ker (γ.app U).hom := by
  refine le_antisymm (γ.ideal_ker_le U) fun s hs => vanishing_le_ker γ U ?_
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro y hy
  by_contra h
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact h
  have hy' : U.2.fromSpec y ∈ closure (Set.range γ) := hy
  obtain ⟨_, hz, x, rfl⟩ := mem_closure_iff.mp hy' _ (Y.basicOpen s).2 h2
  have h3 : x ∈ γ ⁻¹ᵁ Y.basicOpen s := hz
  rw [Scheme.preimage_basicOpen, RingHom.mem_ker.mp hs, Scheme.basicOpen_zero] at h3
  exact h3

theorem ker_restrict_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (U : O.toScheme.affineOpens) :
    (γ ∣_ O).ker.ideal U = γ.ker.ideal ⟨O.ι ''ᵁ U, U.2.image_of_isOpenImmersion _⟩ := by
  rw [ker_apply_red, ker_apply_red]
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (V.presheaf.map (eqToHom (image_morphismRestrict_preimage γ O U)).op)).1

theorem image_in_red {V Y Z : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (t : Z ⟶ O.toScheme)
    (a : (γ ⁻¹ᵁ O).toScheme ⟶ Z) [IsClosedImmersion t] (h : a ≫ t = γ ∣_ O) :
    ∃ b : (γ.imageι ⁻¹ᵁ O).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ O := by
  have H : t.ker ≤ (γ.imageι ∣_ O).ker := by
    refine (a.le_ker_comp t).trans ?_
    rw [h]
    intro U
    rw [ker_restrict_red, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_rfl
  exact ⟨_, IsClosedImmersion.lift_fac t _ H⟩

theorem range_imageι_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Set.range γ.imageι ⊆ closure (Set.range γ) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι]
  have := Scheme.IdealSheafData.support_antitone (vanishing_le_ker γ)
  intro y hy
  have h2 := this hy
  exact h2

theorem covered_red {S X₁ : Scheme.{0}} [IsReduced X₁] (p₁ : X₁ ⟶ S)
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j)
    (hcov : ∀ x : X₁, ∃ j, x ∈ U j) (hsep : ∀ j, IsSeparated (qj j))
    (hc : ∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) (hπ : ∀ j, π j ≫ qj j = q)
    (V : X₁.Opens) (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q)
    (hγ1 : γ ≫ pullback.fst p₁ q = V.ι)
    (hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) :
      Set.range (γ.imageι ≫ pullback.snd p₁ q) ⊆ ⋃ j, ((π j ⁻¹ᵁ W j : P.Opens) : Set P) := by
  rintro _ ⟨y, rfl⟩
  have hz : γ.imageι y ∈ closure (Set.range γ) := range_imageι_red γ ⟨y, rfl⟩
  obtain ⟨j, hj⟩ := hcov (pullback.fst p₁ q (γ.imageι y))
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  set z := γ.imageι y
  let O : (pullback p₁ q).Opens := pullback.fst p₁ q ⁻¹ᵁ U j
  have hcomm : ((pullback.fst p₁ q ∣_ U j) ≫ e j ≫ (W j).ι) ≫ qj j = (O.ι ≫ pullback.snd p₁ q ≫ π j) ≫ qj j := by
    simp only [Category.assoc, hc j, hπ j, morphismRestrict_ι_assoc, pullback.condition]
    rfl
  let f : O.toScheme ⟶ pullback (qj j) (qj j) := pullback.lift _ _ hcomm
  have hD : IsClosed (Set.range (pullback.diagonal (qj j))) :=
    (pullback.diagonal (qj j)).isClosedEmbedding.isClosed_range
  have hrange : Set.range γ ⊆ Set.range O.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    show pullback.fst p₁ q (γ v) ∈ U j
    rw [← Scheme.Hom.comp_apply, hγ1]
    exact hV j v.2
  let γO : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι γ hrange
  have hγO : γO ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have hfac : γO ≫ f = (X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) ≫ pullback.diagonal (qj j) := by
    apply pullback.hom_ext
    · simp only [f, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      have h1 : γO ≫ (pullback.fst p₁ q ∣_ U j) = X₁.homOfLE (hV j) := by
        rw [← cancel_mono (U j).ι, Category.assoc, morphismRestrict_ι, reassoc_of% hγO, hγ1,
          Scheme.homOfLE_ι]
      rw [reassoc_of% h1]
    · simp only [f, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [← hγ2 j, ← hγO, Category.assoc]
  obtain ⟨zO, hzO⟩ : z ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hj
  have hcl : zO ∈ closure (O.ι ⁻¹' Set.range γ) := by
    rw [← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]
    show O.ι zO ∈ closure (Set.range γ)
    rw [hzO]; exact hz
  have hsub : O.ι ⁻¹' Set.range γ ⊆ f ⁻¹' Set.range (pullback.diagonal (qj j)) := by
    rintro w ⟨v, hv⟩
    have hw : w = γO v := O.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hγO, hv])
    refine ⟨(X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) v, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]
  obtain ⟨p, hp⟩ := closure_minimal hsub (hD.preimage f.continuous) hcl
  have e1 : (f ≫ pullback.fst _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
  have e2 : (f ≫ pullback.snd _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
  simp only [f, pullback.lift_fst, pullback.lift_snd] at e1 e2
  show π j (pullback.snd p₁ q z) ∈ W j
  have : π j (pullback.snd p₁ q z) = p := by
    rw [← e2, ← hzO]; simp only [Scheme.Hom.comp_apply]
  rw [this, ← e1]
  simp only [Scheme.Hom.comp_apply]
  have hmem : ∀ a : (W j).toScheme, (W j).ι a ∈ W j := fun a => by
    exact (Scheme.Opens.range_ι (W j)).le ⟨a, rfl⟩
  exact hmem _

def GraphT : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j,
      ∃ (Z : Scheme.{0}) (t : Z ⟶ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).toScheme) (a : (γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z),
        IsClosedImmersion t ∧ IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ∧
        a ≫ t = γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))

theorem GraphT_of : GraphT := by
  intro S X₁ p₁ _ n U Pj qj W e P q π _ _ he hc hπ V _ hV γ h1 h2 j
  have := he j
  let z1 := pullback.fst (π j ∣_ W j) (e j)
  let z2 := pullback.snd (π j ∣_ W j) (e j)
  have hz : z1 ≫ (π j ∣_ W j) = z2 ≫ e j := pullback.condition
  have hw : (z2 ≫ (U j).ι) ≫ p₁ = (z1 ≫ (π j ⁻¹ᵁ W j).ι) ≫ q := by
    rw [Category.assoc, ← hc j, ← reassoc_of% hz, morphismRestrict_ι_assoc, hπ j, Category.assoc]
  let t0 := pullback.lift _ _ hw
  have hP := isPullback_morphismRestrict (pullback.snd p₁ q) (π j ⁻¹ᵁ W j)
  have ht0 : z1 ≫ (π j ⁻¹ᵁ W j).ι = t0 ≫ pullback.snd p₁ q := (pullback.lift_snd _ _ _).symm
  have ht0' : t0 ≫ pullback.fst p₁ q = z2 ≫ (U j).ι := pullback.lift_fst _ _ _
  let t := hP.lift z1 t0 ht0
  have e1 : t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j) = z1 := hP.lift_fst _ _ _
  have e2 : t ≫ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).ι = t0 := hP.lift_snd _ _ _
  have hcl : IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) := by rw [e1]; infer_instance
  have ha : (γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ≫ (π j ∣_ W j) =
      ((γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).ι ≫ X₁.homOfLE (hV j)) ≫ e j := by
    rw [← cancel_mono (W j).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, h2 j]
  let a := pullback.lift _ _ ha
  have a1 : a ≫ z1 = _ := pullback.lift_fst _ _ _
  have a2 : a ≫ z2 = _ := pullback.lift_snd _ _ _
  refine ⟨_, t, a, IsClosedImmersion.of_comp t (pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)), hcl, ?_⟩
  apply hP.hom_ext
  · rw [Category.assoc, e1, a1]
  · rw [Category.assoc, e2, morphismRestrict_ι]
    apply pullback.hom_ext
    · rw [Category.assoc, ht0', reassoc_of% a2, Scheme.homOfLE_ι, Category.assoc, h1]
    · rw [Category.assoc, ← ht0, reassoc_of% a1, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc]

theorem Core_of : LateralTheory.E.ChowGraphCut.Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  obtain ⟨x₀⟩ : Nonempty X₁ := inferInstance
  obtain ⟨j₀, -⟩ := hUc x₀
  let V₀ : X₁.Opens := Finset.univ.inf U
  have hV₀ : ∀ j, V₀ ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  obtain ⟨x, hx⟩ := LateralTheory.E.CorePf.inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨V', hVa, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens (U := V₀) hx
  obtain ⟨V, rfl⟩ : ∃ V : X₁.Opens, V = V' := ⟨V', rfl⟩
  replace hVa : IsAffineOpen V := hVa
  have hV : ∀ j, (V : X₁.Opens) ≤ U j := fun j => hVle.trans (hV₀ j)
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP ((V : X₁.Opens).ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : (V : X₁.Opens).toScheme ⟶ pullback p₁ q := pullback.lift (V : X₁.Opens).ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = (V : X₁.Opens).ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    LateralTheory.E.CorePf2.isClosedImmersion_of_cover _ (fun j => π j ⁻¹ᵁ W j) (LateralTheory.E.CorePf2.range_closed p₁ q γ)
      (covered_red p₁ n U Pj qj W e P q π hUc hsep hc hπ V hV γ hγ1 hγ2)
      (fun j => ?_), ⟨x, hxV⟩, ?_⟩
  · obtain ⟨Z, t, a, ht, hts, hat⟩ := GraphT_of p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2 j
    obtain ⟨b, hb⟩ := image_in_red γ _ t a hat
    rw [morphismRestrict_comp, ← hb, Category.assoc]
    have : IsClosedImmersion (b ≫ t) := by rw [hb]; infer_instance
    have : IsClosedImmersion b := IsClosedImmersion.of_comp_isClosedImmersion b t
    exact @IsClosedImmersion.comp _ _ _ b _ this hts
  · rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.ImageInPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafIntClosureAlgPf
section
noncomputable section
open Polynomial

namespace LateralTheory.E.LeafIntClosureAlgPf
open LateralTheory.E.LeafNormalModelPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L]

theorem isAlgebraic_of_mem_adjoin (u x : L) (hx : x ∈ IntermediateField.adjoin Ω {u}) :
    IsAlgebraic (Algebra.adjoin Ω {u}) x := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := Ω) (α := u) x).1 hx
  set R := Algebra.adjoin Ω {u}
  have hr : aeval u r ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨r, rfl⟩
  have hs : aeval u s ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨s, rfl⟩
  by_cases h0 : aeval u s = 0
  · rw [h0, div_zero]; exact isAlgebraic_zero
  refine ⟨C (⟨aeval u s, hs⟩ : R) * X - C ⟨aeval u r, hr⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, if_false,
      sub_zero, coeff_zero] at this
    exact h0 (congrArg Subtype.val this)
  · simp only [map_sub, map_mul, aeval_C, aeval_X]
    change aeval u s * (aeval u r / aeval u s) - aeval u r = 0
    rw [mul_div_cancel₀ _ h0, sub_self]

variable (Ω) in
theorem isAlgebraic_adjoin (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    Algebra.IsAlgebraic (Algebra.adjoin Ω {u}) L := by
  constructor
  intro z
  set K := IntermediateField.adjoin Ω {u}
  have h1 : IsAlgebraic K z := Algebra.IsAlgebraic.isAlgebraic z
  have h2 : IsAlgebraic K.toSubalgebra z := h1
  have h3 : IsAlgebraic (Algebra.adjoin Ω (K : Set L)) z :=
    h2.tower_top_of_subalgebra_le (fun y hy => Algebra.subset_adjoin hy)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (fun y hy => ?_) h3
  exact isAlgebraic_of_mem_adjoin u y hy.1

variable (Ω) in
theorem isFractionRing_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsFractionRing (integralClosure (Algebra.adjoin Ω {u}) L) L := by
  have := isAlgebraic_adjoin Ω u
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨y, hy, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin Ω {u}) z).exists_integral_multiple
  have hy' : (y : L) ≠ 0 := fun h => hy (Subtype.ext h)
  refine ⟨⟨y • z, hint⟩, ⟨(y : L), isIntegral_algebraMap (R := Algebra.adjoin Ω {u}) (x := y)⟩, ?_⟩
  change z = y • z / (y : L)
  rw [Algebra.smul_def]
  change z = (y : L) * z / (y : L)
  field_simp

variable (Ω) in
theorem isIntegrallyClosed_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsIntegrallyClosed (integralClosure (Algebra.adjoin Ω {u}) L) := by
  have := isFractionRing_intClosure Ω u
  rw [isIntegrallyClosed_iff L]
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨⟨x, isIntegral_trans (A := integralClosure (Algebra.adjoin Ω {u}) L) x hx⟩, rfl⟩

theorem ringKrullDim_intClosure (u : L) (hu : Transcendental Ω u) :
    ringKrullDim (integralClosure (Algebra.adjoin Ω {u}) L) = 1 := by
  have h1 := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := Algebra.adjoin Ω {u})
    (B := integralClosure (Algebra.adjoin Ω {u}) L) (fun a b h => Subtype.ext (congrArg (Subtype.val : integralClosure (Algebra.adjoin Ω {u}) L → L) h))
  have h2 := ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental Ω u hu).toRingEquiv
  rw [h1, ← h2]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField Ω)

def LeafIntClFinite : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)

theorem finiteType_intCl (u : L) (h : Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)) :
    Algebra.FiniteType Ω (intCl Ω u) := by
  have h1 : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨{u}, by rw [Finset.coe_singleton]⟩
  have h2 : Algebra.FiniteType (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L) := inferInstance
  have h3 : Algebra.FiniteType Ω (integralClosure (Algebra.adjoin Ω {u}) L) :=
    Algebra.FiniteType.trans (S := Algebra.adjoin Ω {u}) h1 h2
  exact h3

theorem LeafIntClosureAlg_of (h : LeafIntClFinite) : LeafIntClosureAlg := by
  intro Ω L _ _ _ u hu hfd
  refine ⟨finiteType_intCl u (h Ω L u hu hfd), ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_intClosure Ω u
  · exact ringKrullDim_intClosure u hu
  · exact isFractionRing_intClosure Ω u

end LateralTheory.E.LeafIntClosureAlgPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.QuasiFiniteDescent

def QFChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (R : Subalgebra k Ω)
    {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) : Prop :=
  IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
  IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧
  γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafQFOmega : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) ∧ LocallyQuasiFinite γ1 ∧ LocallyQuasiFinite γ2

def LeafDescendPreMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 ∧ v0 ≫ f = e

def LeafSpreadQF : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) → LocallyQuasiFinite γ1 → LocallyQuasiFinite γ2 →
    ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 → v0 ≫ f = e →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (f' : E0 ⟶ X) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2)
      (hf' : f' ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
      QFChain p R' c0 γ1 γ2 e q' e1 e2 f' w0 w1 w2 hf'

def LeafReducedSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), SmoothOfRelativeDimension 1 q → AlgebraicGeometry.IsReduced D

theorem integral_of (hI : LeafIrred) (hR : LeafReducedSmooth) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k Ω) (hFG : R.FG) {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D)
    (hc : IsCurve c) (hs : SmoothOfRelativeDimension 1 q) (hp : IsPullback v c q (toR R)) : IsIntegral D := by
  have := hI k Ω R hFG c q v hc hs hp
  have := hR k Ω R hFG q hs
  exact isIntegral_of_irreducibleSpace_of_isReduced D

theorem goal_of (hQ : LeafQFOmega) (hP : LeafDescendPreMap) (hS : LeafSpreadQF) (hI : LeafIrred)
    (hR : LeafReducedSmooth) (hD : LeafDimBound) : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨q0, q1, q2⟩ := hQ k p Ω hdim c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hFG, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, hpre, hve⟩ :=
    hP k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', hc⟩ :=
    hS k p Ω R hFG c0 γ1 γ2 e he hc0 h1 h2 q0 q1 q2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, l0, l1, l2, P0, P1, P2, m1, m2, m3⟩ := hc
  exact ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', a1, a2, a3, b1, b2, b3, c1, c2, c3,
    integral_of hI hR R' hFG' c0 q' w0 hc0 a3 P0, integral_of hI hR R' hFG' (γ1 ≫ c0) (e1 ≫ q') w1 h1 b3 P1,
    integral_of hI hR R' hFG' (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') w2 h2 c3 P2, l0, l1, l2,
    hD k Ω R' hFG' q' a3, P0, P1, P2, m1, m2, m3⟩

end LateralTheory.E.QuasiFiniteDescent

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafRelDimOnePf

theorem exists_ne_generic {C : Scheme.{0}} [IsIntegral C] (hd : topologicalKrullDim C = 1) :
    ∃ x : C, x ≠ genericPoint C := by
  by_contra h
  push Not at h
  have : Subsingleton C := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology C := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hd] at this
  exact absurd this (by decide)

theorem isField_top (Ω : Type) [Field Ω] : IsField Γ(Sp Ω, ⊤) :=
  MulEquiv.isField (Field.toIsField Ω)
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv

theorem chart (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [IsIntegral C]
    (hd : topologicalKrullDim C = 1) (U : (Sp Ω).Opens) (V : C.Opens) (hV : IsAffineOpen V)
    (x : C) (hx : x ∈ V) (hxη : x ≠ genericPoint C) (e : V ≤ c ⁻¹ᵁ U)
    (hs : (c.appLE U V e).hom.IsStandardSmooth) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE U V e).hom := by
  have hU : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c x := Subsingleton.elim _ _
    subst this
    exact e hx
  subst hU
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let : Field Γ(Sp Ω, ⊤) := (isField_top Ω).toField
  let : Algebra Γ(Sp Ω, ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 := GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V))
    (d := P.dimension)
  have hle : ringKrullDim Γ(C, V) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim Γ(C, V) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 Γ(C, V) := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))
    let := hF.toField
    have hη : genericPoint C ∈ V :=
      ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩
    have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    have hη' : genericPoint C ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hη
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, hb⟩ := hη'
    apply hxη
    rw [← hb]
    have key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥ := by
      intro p
      have hp := p.isPrime
      exact Ideal.eq_bot_of_prime _
    congr 1
    exact PrimeSpectrum.ext ((key a).trans (key b).symm)
  rw [h1] at hle hne
  have h2 : P.dimension ≤ 1 := by exact_mod_cast hle
  have h3 : P.dimension ≠ 0 := by exact_mod_cast hne
  exact P.isStandardSmoothOfRelativeDimension (by omega)

theorem LeafRelDimOne_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := by
  intro Ω _ C c hC hs hd
  obtain ⟨x₀, hx₀⟩ := exists_ne_generic hd
  constructor
  intro y
  by_cases hy : y = genericPoint C
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c x₀
    have hyV : y ∈ V := hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩
    exact ⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c y
    exact ⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩

end LateralTheory.E.LeafRelDimOnePf
end
end

