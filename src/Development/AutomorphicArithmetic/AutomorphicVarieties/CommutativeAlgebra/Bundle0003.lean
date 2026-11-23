module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_fin_min {σ : Type} [Fintype σ] (P : (σ →₀ ℕ) → Prop) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m ∈ T, P m) ∧ ∀ n, P n → ∃ m ∈ T, m ≤ n := by
  classical
  have hfin : {m : σ →₀ ℕ | Minimal P m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, ?_⟩
  intro n hn
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | P x}).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

private theorem exists_decomp {O σ X : Type} [CommRing O] [Fintype σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) :
    ∃ (T : Finset (σ →₀ ℕ)) (g : (σ →₀ ℕ) → MvPowerSeries σ O), (∀ m ∈ T, g m ∈ wtPart O wt 0) ∧
      f = ∑ m ∈ T, monomial m (1 : O) * g m := by
  classical
  obtain ⟨T, hTP, hT⟩ := exists_fin_min (fun n => coeff n f ≠ 0)
  choose! c hcT hcle using hT
  obtain ⟨g, hg⟩ : ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, ∀ m k,
      coeff k (g m) = if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0 :=
    ⟨fun m k => if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
  have hwt : ∀ n, coeff n f ≠ 0 → Finsupp.weight wt n = j := by
    intro n hn
    by_contra h
    exact hn (hf n h)
  refine ⟨T, g, ?_, ?_⟩
  · intro m hmT k hk
    rw [hg, if_neg]
    rintro ⟨h1, h2⟩
    apply hk
    have hm : Finsupp.weight wt m = j := hwt m (hTP m hmT)
    have hkm := hwt _ h1
    rw [map_add (f := _), hm] at hkm
    simpa using hkm
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl
      (g := fun m => if c n = m then (if coeff n f ≠ 0 then coeff n f else 0) else 0),
      Finset.sum_ite_eq]
    · by_cases hn : coeff n f ≠ 0
      · rw [if_pos (hcT n hn), if_pos hn]
      · push_neg at hn
        rw [hn]
        simp
    · intro m _
      rw [MvPowerSeries.coeff_monomial_mul, one_mul]
      by_cases hmn : m ≤ n
      · rw [if_pos hmn, hg, tsub_add_cancel_of_le hmn]
        by_cases h1 : coeff n f ≠ 0 <;> by_cases h2 : c n = m <;> simp [h1, h2]
      · rw [if_neg hmn]
        by_cases h1 : coeff n f ≠ 0
        · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
          simp [h3]
        · push_neg at h1
          simp [h1]

private theorem monomial_eq_prod {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  have key : ∀ s : Finset σ, ∏ i ∈ s, (MvPowerSeries.X i : MvPowerSeries σ O) ^ (m i) =
      monomial (∑ i ∈ s, Finsupp.single i (m i)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MvPowerSeries.monomial_zero_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

theorem UpperTheory.V.Alg.gr_gen :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R), Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) = ⊤ := by
  intro O R _ _ _ X _ _ _ W
  classical
  haveI := W.fin
  rw [Algebra.eq_top_iff]
  rintro ⟨x, hx⟩
  refine Submodule.iSup_induction' (p := W.part)
    (motive := fun x h => (⟨x, h⟩ : W.A) ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA))
    ?_ ?_ ?_ hx
  · intro j y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨T, g, hg, hfe⟩ := exists_decomp W.wt j f hf
    have hg' : ∀ m, (if m ∈ T then g m else 0) ∈ wtPart O W.wt 0 := by
      intro m
      split_ifs with h
      · exact hg m h
      · exact zero_mem _
    let e : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (if m ∈ T then g m else 0), W.part_le_A (Submodule.mem_map_of_mem (hg' m))⟩
    have he : ∀ m, e m ∈ W.gr 0 := fun m => Submodule.mem_map_of_mem (hg' m)
    have hmem : (∑ m ∈ T, (∏ i, W.zA i ^ m i) * e m) ∈
        Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
      · refine Subalgebra.prod_mem _ fun i _ => pow_mem ?_ _
        exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (he m))
    convert hmem using 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, e, WPres.zA, WPres.z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.toLinearMap_apply, hfe, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm, map_mul, monomial_eq_prod, map_prod]
    simp only [map_pow]
  · exact Subalgebra.zero_mem _
  · intro x y _ _ ihx ihy
    exact Subalgebra.add_mem _ ihx ihy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrInternal
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_internal :
    ∀ (O X R : Type) [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R), DirectSum.IsInternal W.gr := by
  intro O X R _ _ _ _ _ W
  have hhom := W.homog
  unfold IsHomog at hhom
  have hK : ∀ (j : X) (f g : MvPowerSeries W.σ O), W.π f = W.π g →
      W.π (wcomp O W.wt j f) = W.π (wcomp O W.wt j g) := by
    intro j f g hfg
    have hker : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker]
      simp [hfg]
    have h2 := hhom (f - g) hker j
    rw [RingHom.mem_ker] at h2
    simp only [map_sub] at h2
    exact sub_eq_zero.mp (by simpa using h2)
  have hself : ∀ (j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt j →
      wcomp O W.wt j f = f := by
    intro j f hf
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  have hoff : ∀ (i j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt i → i ≠ j →
      wcomp O W.wt j f = 0 := by
    intro i j f hf hij
    ext n
    rw [coeff_wcomp, map_zero]
    split_ifs with h
    · exact hf n (fun h' => hij (h'.symm.trans h))
    · rfl
  have hgr : ∀ (i : X) (y : W.A), y ∈ W.gr i ↔ y.1 ∈ W.part i := fun i y => Iff.rfl
  have hpart : ∀ (i : X) (x : R), x ∈ W.part i ↔ ∃ f ∈ wtPart O W.wt i, W.π f = x := by
    intro i x
    exact Submodule.mem_map
  let T : X → Submodule O W.A := fun j =>
    { carrier := {y | ∀ f, W.π f = y.1 → W.π (wcomp O W.wt j f) = 0}
      add_mem' := by
        intro a b ha hb f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        obtain ⟨fb, hfb⟩ := W.surj b.1
        have e : W.π f = W.π (fa + fb) := by
          rw [hf, map_add (f := _), hfa, hfb]
          rfl
        rw [hK j f (fa + fb) e, map_add (f := _), map_add (f := _), ha fa hfa, hb fb hfb, add_zero]
      zero_mem' := by
        intro f hf
        have e : W.π f = W.π 0 := by
          rw [hf, map_zero]
          rfl
        rw [hK j f 0 e, map_zero, map_zero]
      smul_mem' := by
        intro c a ha f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        have e : W.π f = W.π (c • fa) := by
          rw [hf, map_smul, hfa]
          rfl
        rw [hK j f (c • fa) e, map_smul, map_smul, ha fa hfa, smul_zero] }
  have hT : ∀ (i j : X), i ≠ j → W.gr i ≤ T j := by
    intro i j hij y hy f hf
    obtain ⟨g, hg, hgy⟩ := (hpart i y.1).mp ((hgr i y).mp hy)
    rw [hK j f g (hf.trans hgy.symm), hoff i j g hg hij, map_zero]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ i, ⨆ (_ : i ≠ j), W.gr i) ≤ T j := iSup₂_le fun i hij => hT i j hij
    have hxT := hle hx'
    obtain ⟨g, hg, hgx⟩ := (hpart j x.1).mp ((hgr j x).mp hx)
    have h0 := hxT g hgx
    rw [hself j g hg, hgx] at h0
    exact Subtype.ext h0
  · rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    have hle : ∀ i, W.part i ≤ LinearMap.range W.A.val.toLinearMap := by
      intro i x hx
      exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    have hmap : Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) = ⨆ i, W.part i := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun i => Submodule.map_comap_eq_self (hle i)
    have hmem : a ∈ Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) := by
      rw [hmap]
      exact ha
    obtain ⟨b, hb, hba⟩ := hmem
    have : b = ⟨a, ha⟩ := Subtype.ext hba
    rw [← this]
    exact hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

theorem UpperTheory.V.Alg.homog_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] (W : WPres O X R) (κ : Type) [Finite κ] (g : κ → W.A) (c : κ → X), (∀ i, g i ∈ W.gr (c i)) →
      IsHomog O W.wt ((Ideal.span (Set.range fun i => (g i : R))).comap W.π) ∧
      ∀ x : W.A, (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) ↔ x ∈ Ideal.span (Set.range g) := by
  intro O R _ _ _ X _ W κ _ g c hg
  classical
  cases nonempty_fintype κ
  have hback : ∀ x : W.A, x ∈ Ideal.span (Set.range g) →
      (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => (a i : R), ?_⟩
    rw [← ha]
    simp
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = (g i : R) := fun i => hg i
  choose e he heg using hg'
  have key : ∀ f, W.π f ∈ Ideal.span (Set.range fun i => (g i : R)) → ∀ j,
      ∃ y ∈ Ideal.span (Set.range g), (y : R) = W.π (wcomp O W.wt j f) := by
    intro f hf j
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
    choose G hG using fun i => W.surj (a i)
    have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sub, ← ha, map_sum]
      simp [hG, heg]
    have h2 := W.homog _ h1 j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    have hm : ∀ i, W.π (wcomp O W.wt (j - c i) (G i)) ∈ W.A := fun i =>
      W.part_le_A (j := j - c i) ⟨_, wcomp_mem O W.wt _ _, rfl⟩
    refine ⟨∑ i, ⟨_, hm i⟩ * g i, Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨_, hm i⟩, rfl⟩, ?_⟩
    rw [h2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
    rfl
  refine ⟨fun f hf j => ?_, fun x => ⟨fun hx => ?_, hback x⟩⟩
  · obtain ⟨y, hy, hy'⟩ := key f hf j
    rw [Ideal.mem_comap, ← hy']
    exact hback y hy
  · have hx' : (x : R) ∈ ⨆ j, W.part j := x.2
    have hl : ∃ f, W.π f = (x : R) ∧ ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
      refine Submodule.iSup_induction W.part
        (motive := fun z : R => ∃ f, W.π f = z ∧
          ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
      · rintro i _ ⟨f, hf, rfl⟩
        exact ⟨f, rfl, {i}, fun n hn => hf n (by simpa using hn)⟩
      · exact ⟨0, map_zero _, ∅, fun n _ => map_zero _⟩
      · rintro a b ⟨f, hf, s, hs⟩ ⟨f', hf', s', hs'⟩
        refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun n hn => ?_⟩
        rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
    obtain ⟨f, hf, s, hs⟩ := hl
    have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
      ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [coeff_wcomp]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hs n h
    choose y hy hy' using key f (hf ▸ hx)
    have : x = ∑ j ∈ s, y j := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ← hf]
      conv_lhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hy' j).symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => hy j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
section
noncomputable section

open IsLocalRing MvPowerSeries

namespace UpperTheory.V.Alg

structure IsNVal (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (v : K → ℝ) : Prop where
  mul : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  base : ∀ c : O, c ≠ 0 → v (algebraMap O K c) = ((IsDiscreteValuationRing.addVal O c).toNat : ℝ)

abbrev tz {K : Type} [CommRing K] (t : Kˣ) : Multiplicative ℤ →* Kˣ := zpowersHom Kˣ t

section Data

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

structure IsWRing [IsLocalRing O] (x : A →ₐ[O] O) : Prop where
  co : IsCO O (𝒜 0)
  gen : ∃ s : Finset A, (∀ z ∈ s, z ∈ 𝒜 (-2) ∨ z ∈ 𝒜 (-1) ∨ z ∈ 𝒜 1 ∨ z ∈ 𝒜 2) ∧
    Algebra.adjoin O ((𝒜 0 : Set A) ∪ s) = ⊤
  fixed : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0

variable {K : Type} [Field K] [Algebra O K]

def OnS (I : Ideal A) (ξ : A →ₐ[O] K) : Prop := ∀ f ∈ I, ξ f = 0

def NegZero (ξ : A →ₐ[O] K) : Prop := ∀ j < 0, ∀ f ∈ 𝒜 j, ξ f = 0

def PosZero (ξ : A →ₐ[O] K) : Prop := ∀ j > 0, ∀ f ∈ 𝒜 j, ξ f = 0

def TwoSigned (ξ : A →ₐ[O] K) : Prop := ¬ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ

def Same0 (ξ ξ' : A →ₐ[O] K) : Prop := ∀ b ∈ 𝒜 0, ξ b = ξ' b

def SameOrbit (ξ ξ' : A →ₐ[O] K) : Prop := ∃ t : Kˣ, ξ' = act 𝒜 (tz t) ξ

def M2 (I : Ideal A) : Prop := ((𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap).FG


variable (K)

def M3 (x : A →ₐ[O] O) (I : Ideal A) : Prop :=
  ∀ x₁ : A →ₐ[O] K, OnS I x₁ → NegZero 𝒜 x₁ → PosZero 𝒜 x₁ → x₁ ≠ (Algebra.ofId O K).comp x →
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁) ∨
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ PosZero 𝒜 ξ ∧ ¬ NegZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁)


def M4 (I : Ideal A) : Prop :=
  ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ∀ D ∈ PtDer ξ K, ∀ D' ∈ PtDer ξ K, (∀ f ∈ I, D f = 0) →
    (∀ f ∈ I, D' f = 0) → ∃ c c' : K, (c ≠ 0 ∨ c' ≠ 0) ∧ c • D + c' • D' = 0



def M5 (x : A →ₐ[O] O) (I : Ideal A) (a : A) : Prop :=
  a ∈ 𝒜 0 ∧ x a = 0 ∧ ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ξ a ≠ 0

variable {K}

def Covers (I : Ideal A) (T : Finset (A →ₐ[O] K)) : Prop :=
  (∀ ξ ∈ T, OnS I ξ ∧ TwoSigned 𝒜 ξ) ∧ ∀ ξ, OnS I ξ → TwoSigned 𝒜 ξ → ∃ ξ' ∈ T, SameOrbit 𝒜 ξ' ξ

end Data

structure IsChart {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Prop where
  graded : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : A, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) → f ∈ satSq x

def SmoothPt {O A X : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (n : X → ℕ) : Prop :=
  ∃ (τ : Type) (_ : Fintype τ) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsChart 𝒜 x wt φ ∧ ∀ j, Nat.card {i // wt i = j} = n j

structure Eqns {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O)
    (r s r' s' m : ℕ) where
  F : Fin (r + 1) → A
  G : Fin s → A
  E : Fin r' → A
  E' : Fin s' → A
  Z : Fin m → A
  hF : ∀ i, F i ∈ 𝒜 (-1)
  hG : ∀ i, G i ∈ 𝒜 (-2)
  hE : ∀ i, E i ∈ 𝒜 1
  hE' : ∀ i, E' i ∈ 𝒜 2
  hZ : ∀ i, Z i ∈ 𝒜 0 ∧ x (Z i) = 0

def Eqns.ideal {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Ideal A :=
  Ideal.span (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z)

def mDims (r s r' s' m : ℕ) (j : ℤ) : ℕ :=
  if j = -1 then r else if j = -2 then s else if j = 1 then r' + 1 else if j = 2 then s' + 1 else
    if j = 0 then m else 0

def M1 {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Prop :=
  1 ≤ r ∧ SmoothPt 𝒜 x (mDims r s r' s' m) ∧ SpansCot x 𝒜 (-1) Q.F ∧ SpansCot x 𝒜 (-2) Q.G ∧ SpansCot x 𝒜 0 Q.Z

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
  ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O), IsWRing 𝒜 x →
  ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m) (a : A),
    M1 Q → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal → M5 𝒜 K x Q.ideal a →
    (∃ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T) ∧ cotLen x 𝒜 (-1) Q.F ≠ ⊤ ∧
    ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T → ((cotLen x 𝒜 (-1) Q.F).toNat : ℝ) ≤ 2 * ∑ ξ ∈ T, v (ξ a)

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (A X : Type) [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (j : X), (∀ f ∈ 𝒜 j, x f = 0) →
  ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j) →
  ∀ (c : O), c ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M] (D : M →+ (A →ₗ[O] O ⧸ Ideal.span {c})),
    Function.Injective D → (∀ μ i, D μ (F i) = 0) →
    (∀ μ, ∃ D' ∈ PtDer x O, HasWt 𝒜 j D' ∧ ∀ f, D μ f = Ideal.Quotient.mk _ (D' f)) →
    Module.length O M ≤ cotLen x 𝒜 j F

end UpperTheory.V.Alg
end
end

