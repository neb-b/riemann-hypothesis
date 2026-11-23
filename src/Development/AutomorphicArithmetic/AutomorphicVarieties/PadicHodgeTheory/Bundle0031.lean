module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open Topology Pointwise

private theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

private def ballSub (l : ℕ) [Fact l.Prime] (ε : ℝ) (hε : 0 < ε) : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l)‖ = 1 ∧ ‖(x : Qbar l) - 1‖ < ε}
  one_mem' := by simpa using hε
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have e : ((x * y : (Qbar l)ˣ) : Qbar l) - 1 = x * (y - 1) + (x - 1) := by push_cast; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx')
    rwa [norm_mul, hx, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have e : ((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((x : Qbar l)⁻¹ * (x - 1)) := by
      have := x.ne_zero
      push_cast; field_simp; ring
    rwa [e, norm_neg, norm_mul, norm_inv, hx, inv_one, one_mul]

private theorem exists_compact {l : ℕ} [Fact l.Prime] (u : (Qbar l)ˣ) (hu : ‖(u : Qbar l)‖ = 1) :
    ∃ C : Subgroup (Qbar l)ˣ, IsCompact (C : Set (Qbar l)ˣ) ∧ u ∈ C ∧ ∀ x ∈ C, ‖(x : Qbar l)‖ = 1 := by
  let L : IntermediateField ℚ_[l] (Qbar l) := IntermediateField.adjoin ℚ_[l] {(u : Qbar l)}
  haveI : FiniteDimensional ℚ_[l] L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  let C : Subgroup (Qbar l)ˣ :=
    { carrier := {x | (x : Qbar l) ∈ L ∧ ‖(x : Qbar l)‖ = 1}
      one_mem' := ⟨by simpa using L.one_mem, by simp⟩
      mul_mem' := fun hx hy => ⟨L.mul_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      inv_mem' := fun hx => ⟨by simpa using L.inv_mem hx.1, by simp [hx.2]⟩ }
  refine ⟨C, ?_, ⟨IntermediateField.mem_adjoin_simple_self _ _, hu⟩, fun x hx => hx.2⟩
  rw [Units.isEmbedding_val₀.isCompact_iff]
  haveI : FiniteDimensional ℚ_[l] L.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[l] L)
  haveI : ProperSpace L.toSubmodule := FiniteDimensional.proper ℚ_[l] _
  convert (isCompact_sphere (0 : L.toSubmodule) 1).image continuous_subtype_val using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1⟩, by simpa using hy.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖(y : Qbar l)‖ = 1 := by simpa using hy
    have h0 : (y : Qbar l) ≠ 0 := fun h => by simp [h] at hy'
    exact ⟨Units.mk0 _ h0, ⟨y.2, hy'⟩, rfl⟩

theorem UpperTheory.V.Loc.laExists :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ, Continuous ξ → (∀ x, ‖(ξ x : Qbar l)‖ = 1) → ∃! κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = ξ (a σ) := by
  intro _ F Ω _ _ _ _ _ l _ A w h a ha ξ hξ hn
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI := compactSpace_Ine (E := F) A
  let χ := ξ.comp a
  have hI : Continuous fun τ : Ine (F := F) A => χ (ineIncl h τ) := hξ.comp ha.cont
  obtain ⟨C, hC, huC, hC1⟩ := exists_compact (χ (frob h)) (hn _)
  refine ext_dense (Subgroup.inclusion (Weil_le_Dec h)) ?_ χ
    ((C : Set (Qbar l)ˣ) * Set.range fun τ : Ine (F := F) A => χ (ineIncl h τ))
    (hC.mul (isCompact_range hI)) (fun σ => ?_) fun V hV => ?_
  · have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := F) A).subgroupOf (Dec (F := F) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := F) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  · obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    refine ⟨χ (frob h) ^ deg σ, C.zpow_mem huC _, _, ⟨τ, rfl⟩, ?_⟩
    conv_rhs => rw [hτ, map_mul, map_zpow]
  · rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨V', hV', hVV⟩ := hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV'
    let H := ballSub l ε hε
    have hH : ∀ x ∈ H, x ∈ V := fun x hx => hVV (hεV (by simpa [dist_eq_norm] using hx.2))
    have hop : IsOpen {x : (Qbar l)ˣ | ‖(x : Qbar l) - 1‖ < ε} :=
      isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
    haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have hHC : IsOpen ((H.subgroupOf C : Subgroup C) : Set C) := by
      convert hop.preimage (continuous_subtype_val (p := (· ∈ C))) using 1
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hC1 _ x.2, hx⟩⟩
    haveI := (H.subgroupOf C).quotient_finite_of_isOpen hHC
    obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf C)) ⟨_, huC⟩
    have hNH' : χ (frob h) ^ N ∈ H := hNH
    have hM := (hop.preimage hI).mem_nhds (x := 1) (by simpa using hε)
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
    obtain ⟨U, hU, hUM⟩ := hM
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    have hEo : IsOpen (E.fixingSubgroup : Set (G F Ω)) := E.fixingSubgroup_isOpen
    haveI := E.fixingSubgroup.quotient_finite_of_isOpen hEo
    obtain ⟨m, hm, -, hmE⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) (frob h : G F Ω)
    obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg F Ω A w h (m * N) (Nat.mul_pos hm hN)
    have hζo : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω)) := stabilizer_isOpen_of_isIntegral ζ
    refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hEo.inter hζo).mem_nhds ⟨E.fixingSubgroup.one_mem, (MulAction.stabilizer (G F Ω) ζ).one_mem⟩), fun σ hσ => hH _ ?_⟩
    obtain ⟨k, hk⟩ := hζ σ hσ.2
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    have h1 : ((frob h ^ deg σ : Weil h) : G F Ω) ∈ E.fixingSubgroup := by
      rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
      exact E.fixingSubgroup.zpow_mem hmE _
    have h2 : (τ : G F Ω) ∈ E.fixingSubgroup := by
      have h3 : (σ : G F Ω) ∈ E.fixingSubgroup := hσ.1
      rw [hτ, Subgroup.coe_mul] at h3
      exact (E.fixingSubgroup.mul_mem_cancel_left h1).1 h3
    rw [hτ, map_mul, map_zpow]
    refine H.mul_mem ?_ ⟨hn _, hUM (hEU h2)⟩
    rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
    exact H.zpow_mem hNH' _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaUnique
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  classical
  let φ : Emb l w → (F →+* Qbar l) := fun j =>
    (j.1).comp (algebraMap F (HeightOneSpectrum.adicCompletion F w))
  refine Finite.of_injective φ ?_
  intro i j hij
  apply Subtype.ext
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := F) w
  have hfun : (i.1 : HeightOneSpectrum.adicCompletion F w → Qbar l) = j.1 :=
    hd.equalizer i.2 j.2 (funext fun x => DFunLike.congr_fun hij x)
  exact DFunLike.coe_injective hfun

private theorem lin_term {ι L : Type} [Fintype ι] [Field L] [CharZero L] (c : ι → L) (p q : ι → ℕ)
    (H : ∀ n : ℕ, ∏ i, (1 + c i * n) ^ p i = ∏ i, (1 + c i * n) ^ q i) :
    ∑ i, (p i : L) * c i = ∑ i, (q i : L) * c i := by
  classical
  open Polynomial in
  have hmul : ∀ f g : L[X], (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
    intro f g
    rw [coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [add_comm]
  have hlin : ∀ (a : L) (m : ℕ), ((1 + C a * X) ^ m).coeff 0 = 1 ∧ ((1 + C a * X) ^ m).coeff 1 = (m : L) * a := by
    intro a m
    induction m with
    | zero => simp [coeff_one]
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ, mul_coeff_zero, ih.1]
        simp
      · rw [pow_succ, hmul, ih.1, ih.2]
        simp [coeff_one, coeff_C_mul_X]
        push_cast
        ring
  have hprod : ∀ (m : ι → ℕ) (s : Finset ι), (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 0 = 1 ∧
      (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 1 = ∑ i ∈ s, (m i : L) * c i := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp [coeff_one]
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine ⟨?_, ?_⟩
      · rw [mul_coeff_zero, ih.1, (hlin (c j) (m j)).1, one_mul]
      · rw [hmul, ih.1, ih.2, (hlin (c j) (m j)).1, (hlin (c j) (m j)).2]
        ring
  have heq : (∏ i, (1 + C (c i) * X) ^ p i) = ∏ i, (1 + C (c i) * X) ^ q i := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : L)))
    · rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, eval_prod, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X]
      exact H n
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have h1 := congrArg (fun P : L[X] => P.coeff 1) heq
  rw [(hprod p Finset.univ).2, (hprod q Finset.univ).2] at h1
  exact h1

private theorem indep {ι k L Γ : Type} [Fintype ι] [Field k] [Field L] [CharZero L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) (π : k) (h0 : π ≠ 0) (h1 : v π < 1)
    (τ : ι → k →+* L) (hτ : Function.Injective τ) (e : ι → ℤ)
    (H : ∀ u : k, v u = 1 → ∏ i, τ i u ^ e i = 1) : e = 0 := by
  classical
  have hnat : ∀ n : ℕ, v (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (v.map_add _ _) (max_le ih (by simp))
  have hS : ∀ y : k, v y < 1 → ∑ i, (e i : L) * τ i y = 0 := by
    intro y hy
    have key : ∀ n : ℕ, ∏ i, (1 + τ i y * n) ^ (e i).toNat = ∏ i, (1 + τ i y * n) ^ (-e i).toNat := by
      intro n
      have hlt : v ((n : k) * y) < 1 := by
        rw [v.map_mul]
        calc v (n : k) * v y ≤ 1 * v y := by gcongr; exact hnat n
          _ = v y := one_mul _
          _ < 1 := hy
      have hu : v (1 + (n : k) * y) = 1 := v.map_one_add_of_lt hlt
      have hu0 : (1 + (n : k) * y) ≠ 0 := by
        intro h0
        rw [h0, v.map_zero] at hu
        exact zero_ne_one hu
      have hx : ∀ i, τ i (1 + (n : k) * y) = 1 + τ i y * n := by
        intro i
        simp [map_add (f := _), map_mul, map_natCast, mul_comm]
      have hne : ∀ i, τ i (1 + (n : k) * y) ≠ 0 := fun i => (map_ne_zero (τ i)).2 hu0
      have h := H _ hu
      have hsplit : ∀ i, τ i (1 + (n : k) * y) ^ e i =
          τ i (1 + (n : k) * y) ^ (e i).toNat / τ i (1 + (n : k) * y) ^ (-e i).toNat := by
        intro i
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hne i), Int.toNat_sub_toNat_neg]
      simp only [hsplit] at h
      rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i))] at h
      simpa only [hx] using h
    have h2 := lin_term (fun i => τ i y) (fun i => (e i).toNat) (fun i => (-e i).toNat) key
    have hcast : ∀ i, (e i : L) = ((e i).toNat : L) - ((-e i).toNat : L) := by
      intro i
      have := congrArg (fun z : ℤ => (z : L)) (Int.toNat_sub_toNat_neg (e i))
      push_cast at this
      exact this.symm
    simp only [hcast, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h2
  let R := v.integer
  let ρ : ι → (R →* L) := fun i => (τ i).toMonoidHom.comp R.subtype.toMonoidHom
  have hinj : Function.Injective ρ := by
    intro i j hij
    apply hτ
    ext x
    rcases le_or_gt (v x) 1 with hx | hx
    · have := DFunLike.congr_fun hij ⟨x, hx⟩
      simpa [ρ] using this
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hxi : v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hx).le
      have := DFunLike.congr_fun hij ⟨x⁻¹, hxi⟩
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply] at this
      simpa [map_inv₀] using this
  have hli := (linearIndependent_monoidHom R L).comp ρ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun i => (e i : L) * τ i π) (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    have ha : v (π * (a : k)) < 1 := by
      rw [v.map_mul]
      calc v π * v (a : k) ≤ v π * 1 := by gcongr; exact a.2
        _ = v π := mul_one _
        _ < 1 := h1
    have := hS _ ha
    simp only [map_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ρ, mul_assoc])
  funext i
  have hi := hz i
  have hπ : τ i π ≠ 0 := (map_ne_zero (τ i)).2 h0
  have : (e i : L) = 0 := by
    rcases mul_eq_zero.1 hi with h | h
    · exact h
    · exact absurd h hπ
  simpa using this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laUnique :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∃ a, IsLocalArtin h a) → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ), IsLocAlg h κ wt → IsLocAlg h κ wt' → wt = wt' := by
  intro F Ω _ _ _ _ _ l _ A w h ha0 κ wt wt' hw hw'
  classical
  obtain ⟨a, ha⟩ := ha0
  obtain ⟨ph, hph⟩ := hw
  obtain ⟨ph', hph'⟩ := hw'
  haveI : Finite (Emb l w) := finite_emb l w
  letI : Fintype (Emb l w) := Fintype.ofFinite _
  let K : Subgroup ↥(Ine (F := F) A) := ph.ker ⊓ ph'.ker
  haveI : CompactSpace ↥(Ine (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Ine (F := F) A).isCompact
  have hKo : IsOpen (K : Set ↥(Ine (F := F) A)) := hph.1.inter hph'.1
  haveI : Finite (↥(Ine (F := F) A) ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  haveI : K.Normal := Subgroup.normal_inf_normal _ _
  have hm0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : ∀ σ : ↥(Ine (F := F) A), ∏ τ : Emb l w,
      (τ.1 (a (ineIncl h σ) : HeightOneSpectrum.adicCompletion F w)) ^ ((K.index : ℤ) * (wt' τ - wt τ)) = 1 := by
    intro σ
    have hmem := K.pow_index_mem σ
    have hk1 : ph (σ ^ K.index) = 1 := hmem.1
    have hk2 : ph' (σ ^ K.index) = 1 := hmem.2
    have e1 := hph.2 a ha (σ ^ K.index)
    have e2 := hph'.2 a ha (σ ^ K.index)
    rw [hk1, mul_one] at e1
    rw [hk2, mul_one] at e2
    have e := e1.symm.trans e2
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype] at e
    simp only [map_pow, Units.val_pow_eq_pow_val] at e
    have hy : ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 := Units.ne_zero _
    have hne : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 :=
      fun τ => (map_ne_zero τ.1).2 hy
    have hsp : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ ((K.index : ℤ) * (wt' τ - wt τ)) =
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt τ) /
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt' τ) := by
      intro τ
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_sub₀ (hne τ)]
      congr 1
      ring
    simp only [hsp]
    rw [Finset.prod_div_distrib, e, div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (hne τ)))]
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := HeightOneSpectrum.adicCompletion F w)
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective γ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact hγ0.ne hπ
  have he := indep (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion F w)) π hπ0 (hπ ▸ hγ1)
    (fun τ : Emb l w => τ.1) Subtype.val_injective (fun τ => (K.index : ℤ) * (wt' τ - wt τ)) (by
      intro u hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact zero_ne_one hu
      have hord : GlobalTheory.SmGL.ord _ (Units.mk0 u hu0) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.2 (by simpa using hu)
      obtain ⟨ρ, hρ⟩ := ha.surj (Units.mk0 u hu0)
      have hdeg : deg ρ = 0 := by
        have := ha.ord_eq ρ
        rw [hρ, hord] at this
        omega
      have hI : (ρ : G F Ω) ∈ Ine (F := F) A :=
        actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simp [hdeg]))
      have hr : ineIncl h ⟨(ρ : G F Ω), hI⟩ = ρ := Subtype.ext rfl
      have := hrel ⟨(ρ : G F Ω), hI⟩
      rw [hr, hρ] at this
      simpa using this)
  funext τ
  have hτ := congrFun he τ
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hτ
  rcases hτ with hτ | hτ
  · exact absurd hτ hm0
  · exact (sub_eq_zero.1 hτ).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

def UpperTheory.V.Loc.HasLT {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ)
    (wt : Emb l w → ℤ) (a : Weil h →* (w.adicCompletion F)ˣ) : Prop :=
  ∃ (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* ℂˣ), Continuous μ ∧ IsSmooth ξ ∧
    GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 μ) ∧
    (∀ σ, (ξ σ : ℂ) = ι ((μ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) *
      ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ)) ∧
    ∀ σ, (ξ σ : ℂ) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 μ)).eig σ
end

