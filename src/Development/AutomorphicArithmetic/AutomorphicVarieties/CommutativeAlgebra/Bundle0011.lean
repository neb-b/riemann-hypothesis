module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {X : Type} [AddCommGroup X]

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma π_monomial (W : WPres O X R) (m : W.σ →₀ ℕ) :
    W.π (monomial m 1) = m.prod fun i k => W.z i ^ k := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
  simp [WPres.z]

private lemma exists_order (W : WPres O X R) (h : W.HasOrigin) (n : ℕ) :
    ∀ x ∈ RingHom.ker (W.origin h) ^ n, ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order := by
  induction n with
  | zero =>
    intro x _
    obtain ⟨f, hf⟩ := W.surj x
    exact ⟨f, hf, by simp⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · obtain ⟨f, rfl, hf⟩ := ih a ha
      obtain ⟨g, rfl⟩ := W.surj b
      rw [RingHom.mem_ker, W.origin_π] at hb
      refine ⟨f * g, map_mul _ _ _, le_trans ?_ (le_order_mul)⟩
      push_cast
      exact add_le_add hf (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
      exact ⟨f + g, map_add _ _ _, le_trans (le_min hf hg) (min_order_le_add)⟩

private lemma z_mem_ker (W : WPres O X R) (h : W.HasOrigin) (i : W.σ) : W.z i ∈ RingHom.ker (W.origin h) := by
  rw [RingHom.mem_ker, WPres.z, W.origin_π]
  simp

private lemma monomial_mem {σ : Type} (wt : σ → X) (m : σ →₀ ℕ) (c : O) :
    monomial m c ∈ wtPart O wt (Finsupp.weight wt m) := fun k hk => by
  classical
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hk rfl

private lemma A_fin (W : WPres O X R) (x : R) (hx : x ∈ W.A) :
    ∃ (T : Finset X) (f : MvPowerSeries W.σ O), W.π f = x ∧
      ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0 := by
  classical
  have hx' : x ∈ ⨆ j, W.part j := hx
  refine Submodule.iSup_induction W.part (motive := fun x => ∃ (T : Finset X) (f : MvPowerSeries W.σ O),
    W.π f = x ∧ ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0) hx' ?_ ?_ ?_
  · rintro j _ ⟨f, hf, rfl⟩
    exact ⟨{j}, f, rfl, fun m hm => hf m (by simpa using hm)⟩
  · exact ⟨∅, 0, map_zero _, fun _ _ => map_zero _⟩
  · rintro _ _ ⟨T, f, rfl, hf⟩ ⟨U, g, rfl, hg⟩
    refine ⟨T ∪ U, f + g, map_add _ _ _, fun m hm => ?_⟩
    rw [Finset.mem_union, not_or] at hm
    rw [map_add (f := _), hf m hm.1, hg m hm.2, add_zero]

private lemma A_sum (W : WPres O X R) (g : MvPowerSeries W.σ O) (hx : W.π g ∈ W.A) :
    ∃ T : Finset X, W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) := by
  classical
  obtain ⟨T, f, hf, hT⟩ := A_fin W _ hx
  refine ⟨T, ?_⟩
  have h1 : f = ∑ j ∈ T, wcomp O W.wt j f := by
    ext m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · exact hT m hm
  have h2 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hf, sub_self]
  rw [← hf]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [h1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := W.homog _ h2 j
  rwa [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at this

end

theorem UpperTheory.V.Alg.ker_pow :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (n : ℕ),
      (RingHom.ker (W.origin h) ^ n).comap W.A.val = RingHom.ker (W.originA h) ^ n ∧ ∀ x : R, ∃ y : W.A, x - y ∈ RingHom.ker (W.origin h) ^ n := by
  intro O R _ _ _ X _ _ _ _ W h n
  classical
  refine ⟨le_antisymm (fun x hx => ?_) ?_, fun x => ?_⟩
  · obtain ⟨g, hg, hgn⟩ := exists_order W h n _ hx
    have hg' : W.π g = (x : R) := hg
    obtain ⟨T, hT⟩ := A_sum W g (hg' ▸ x.2)
    have hx' : x = ∑ j ∈ T, (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) := by
      apply Subtype.ext
      rw [← hg', hT]
      simp
    rw [hx']
    refine Ideal.sum_mem _ fun j _ => ?_
    obtain ⟨μ, hμ, hs⟩ := part_span O R X W {m | Finsupp.weight W.wt m = j ∧ n ≤ m.degree} j (fun _ hm => hm.1)
    obtain ⟨b, hb, hbs⟩ := hs (wcomp O W.wt j g) (fun m hm => by
      rw [coeff_wcomp]
      split_ifs with h1
      · refine coeff_of_lt_order (lt_of_lt_of_le ?_ hgn)
        have : ¬ n ≤ m.degree := fun h2 => hm ⟨h1, h2⟩
        exact_mod_cast not_le.1 this
      · rfl)
    have h3 : (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) =
        ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k := by
      apply Subtype.ext
      show W.π (wcomp O W.wt j g) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hbs, map_sum]
      simp [π_monomial, Finsupp.prod, WPres.zA]
    rw [h3]
    exact Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _
      (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)
  · exact Ideal.le_comap_pow (K := RingHom.ker (W.origin h)) W.A.val n
  · obtain ⟨f, rfl⟩ := W.surj x
    have hfin : {m : W.σ →₀ ℕ | m.degree < n}.Finite :=
      (Finsupp.finite_of_degree_le n).subset fun m (hm : m.degree < n) => hm.le
    set t : MvPowerSeries W.σ O := ∑ m ∈ hfin.toFinset, monomial m (coeff m f) with ht
    have htA : W.π t ∈ W.A := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ht, map_sum]
      exact Subalgebra.sum_mem _ fun m _ => W.part_le_A ⟨_, monomial_mem W.wt m _, rfl⟩
    refine ⟨⟨_, htA⟩, ?_⟩
    have key : ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ {m : W.σ →₀ ℕ | n ≤ m.degree} ∧
        ∀ f : MvPowerSeries W.σ O, (∀ m, m ∉ {m : W.σ →₀ ℕ | n ≤ m.degree} → coeff m f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O (fun _ : W.σ => (0 : X)) 0) ∧
          f = ∑ m ∈ μ, b m * monomial m 1 :=
      part_span O (MvPowerSeries W.σ O) X (WPres.free O fun _ : W.σ => (0 : X))
        {m : W.σ →₀ ℕ | n ≤ m.degree} 0 (fun (m : W.σ →₀ ℕ) _ => by
          show Finsupp.weight (fun _ : W.σ => (0 : X)) m = 0
          simp [Finsupp.weight_apply, Finsupp.sum])
    obtain ⟨μ, hμ, hs⟩ := key
    obtain ⟨b, -, hbs'⟩ := hs (f - t) (fun m hm => by
      have hm0 : m.degree < n := not_le.1 hm
      have hm' : m ∈ hfin.toFinset := hfin.mem_toFinset.2 hm0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, ht, map_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq, if_pos hm', sub_self])
    show W.π f - W.π t ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sub, hbs', map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, π_monomial]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ (fun i => z_mem_ker W h i) m (hμ hm))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.monomial_mem_weight_zero {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (m : σ →₀ ℕ) (hm : Finsupp.weight wt m = 0) : (monomial m (1 : O) : MvPowerSeries σ O) ∈ wtPart O wt 0 := by
  classical
  intro n hn
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hm

theorem UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO O (W.gr 0)], (∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R) ∧
      ∃ u : Finset (W.gr 0), (∀ b ∈ u, ∃ n : W.σ →₀ ℕ, n ≠ 0 ∧ Finsupp.weight W.wt n = 0 ∧ ((b : W.A) : R) = n.prod fun s k => W.z s ^ k) ∧
        maximalIdeal (W.gr 0) = (maximalIdeal O).map (algebraMap O (W.gr 0)) ⊔ Ideal.span (u : Set (W.gr 0)) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz _
  classical
  let φ : W.gr 0 →ₐ[O] R :=
    { toFun := fun b => ((b : W.A) : R)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hφ : ∀ b : W.gr 0, φ b = ((b : W.A) : R) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
  have h1 : ∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R := fun b => by
    rw [← hφ, ← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
  refine ⟨h1, ?_⟩
  let mk : ∀ f : MvPowerSeries W.σ O, f ∈ wtPart O W.wt 0 → W.gr 0 := fun f hf =>
    ⟨⟨W.π f, W.part_le_A (j := 0) ⟨f, hf, rfl⟩⟩, ⟨f, hf, rfl⟩⟩
  have hmk : ∀ f hf, φ (mk f hf) = W.π f := fun _ _ => rfl
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W {n | n ≠ 0 ∧ Finsupp.weight W.wt n = 0} 0
    (fun n hn => hn.2)
  let U : μ → W.gr 0 := fun m => mk (monomial m.1 1) (UpperTheory.V.Alg.monomial_mem_weight_zero W.wt m.1 (hμ m.2).2)
  have hU : ∀ m : μ, φ (U m) = m.1.prod fun s k => W.z s ^ k := fun m => by
    show W.π (monomial m.1 1) = _
    rw [monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
    simp only [map_pow, WPres.z]
  have hUm : ∀ m : μ, U m ∈ maximalIdeal (W.gr 0) := fun m => by
    rw [h1, ← hφ, hU]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 (hμ m.2).1
    exact Ideal.prod_mem _ hs (Ideal.pow_mem_of_mem _ (hz s) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs)))
  have hle : Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) ≤ maximalIdeal (W.gr 0) := by
    rw [Ideal.span_le]
    intro b hb
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hUm m
  refine ⟨Finset.univ.image U, fun b hb => ?_, le_antisymm (fun b hb => ?_) (sup_le ?_ hle)⟩
  · obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨m.1, (hμ m.2).1, (hμ m.2).2, hU m⟩
  · obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
    obtain ⟨c, hc, hsum⟩ := hspan (f - C (constantCoeff f)) (fun n hn => by
      rw [map_sub, coeff_C]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg h0, sub_zero]
        exact hf n fun h => hn ⟨h0, h⟩)
    have hb' : b - algebraMap O (W.gr 0) (constantCoeff f) = ∑ m : μ, mk (c m.1) (hc m.1) * U m := by
      apply hinj
      have h2 := congrArg W.π hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, ← Finset.sum_coe_sort] at h2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, AlgHom.commutes, hφ, ← hfb, ← W.π.commutes]
      simp only [map_mul] at h2 ⊢
      exact h2
    have hs : b - algebraMap O (W.gr 0) (constantCoeff f) ∈
        Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) := by
      rw [hb']
      exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem U (Finset.mem_univ m))))
    have h3 : algebraMap O (W.gr 0) (constantCoeff f) ∈ maximalIdeal (W.gr 0) := by
      simpa using Ideal.sub_mem _ hb (hle hs)
    have h4 : constantCoeff f ∈ maximalIdeal O := fun h => h3 (h.map _)
    rw [← add_sub_cancel (algebraMap O (W.gr 0) (constantCoeff f)) b]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h4) hs
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha h
    exact ha (IsLocalHom.map_nonunit a h)
end

