module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Carver
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem between_fin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b)
    (A B : Set ℝ) (hA : A.Finite) (hB : B.Finite) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x ∈ D, (∀ a ∈ A, a < x) ∧ ∀ b ∈ B, x < b := by
  obtain ⟨a0, h1, h2⟩ : ∃ a0 : ℝ, (∀ a ∈ A, a ≤ a0) ∧ ∀ b ∈ B, a0 < b := by
    rcases A.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨m, hm⟩ := hB.bddBelow
      exact ⟨m - 1, by simp, fun b hb => by linarith [hm hb]⟩
    · obtain ⟨a0, ha0, hmax⟩ := Set.exists_max_image A id hA hne
      exact ⟨a0, hmax, h a0 ha0⟩
  obtain ⟨b0, h3, h4⟩ : ∃ b0 : ℝ, a0 < b0 ∧ ∀ b ∈ B, b0 ≤ b := by
    rcases B.eq_empty_or_nonempty with rfl | hne
    · exact ⟨a0 + 1, by linarith, by simp⟩
    · obtain ⟨b0, hb0, hmin⟩ := Set.exists_min_image B id hB hne
      exact ⟨b0, h2 b0 hb0, hmin⟩
  obtain ⟨x, hx, h5, h6⟩ := hD a0 b0 h3
  exact ⟨x, hx, fun a ha => lt_of_le_of_lt (h1 a ha) h5, fun b hb => lt_of_lt_of_le h6 (h4 b hb)⟩

private theorem zsmul_mem_pos {M : Type} [AddCommGroup M] (H : Set M)
    (hH : ∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) (v : M) (hv : v ∈ H) (k : ℤ) (hk : 0 < k) : k • v ∈ H := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  clear hk
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have : (((n + 1 : ℕ) : ℤ) + 1) • v = ((n : ℤ) + 1) • v + v := by
      push_cast; rw [add_smul ((n : ℤ) + 1) 1 v, one_smul]
    rw [this]; exact hH _ ih _ hv

private theorem fourier_motzkin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b) :
    ∀ (d : ℕ) (F H : Set ((Fin d → ℤ) × ℝ)), F.Finite → F ⊆ H → (∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) →
      (∀ v ∈ H, v.1 = 0 → v.2 < 0) →
      ∃ φ : Fin d → ℝ, (∀ i, φ i ∈ D) ∧ ∀ v ∈ F, ∑ i, (v.1 i : ℝ) * φ i + v.2 < 0 := by
  intro d
  induction d with
  | zero =>
    intro F H _ hFH _ h0
    refine ⟨Fin.elim0, fun i => i.elim0, fun v hv => ?_⟩
    simpa using h0 v (hFH hv) (Subsingleton.elim _ _)
  | succ d ih =>
    intro F H hF hFH hadd h0
    let π : (Fin (d + 1) → ℤ) × ℝ → (Fin d → ℤ) × ℝ := fun v => (fun i => v.1 i.succ, v.2)
    let cmb : ((Fin (d + 1) → ℤ) × ℝ) × ((Fin (d + 1) → ℤ) × ℝ) → (Fin (d + 1) → ℤ) × ℝ :=
      fun p => (-p.2.1 0) • p.1 + (p.1.1 0) • p.2
    let G : Set ((Fin (d + 1) → ℤ) × ℝ) :=
      {v ∈ F | v.1 0 = 0} ∪ cmb '' ({v ∈ F | 0 < v.1 0} ×ˢ {v ∈ F | v.1 0 < 0})
    have hG : G.Finite :=
      (hF.subset (Set.sep_subset _ _)).union
        (((hF.subset (Set.sep_subset _ _)).prod (hF.subset (Set.sep_subset _ _))).image _)
    have hGH : G ⊆ {v ∈ H | v.1 0 = 0} := by
      rintro v (⟨hv, hv0⟩ | ⟨⟨s, t⟩, ⟨⟨hs, hs0⟩, ht, ht0⟩, rfl⟩)
      · exact ⟨hFH hv, hv0⟩
      · refine ⟨hadd _ (zsmul_mem_pos H hadd _ (hFH hs) _ (neg_pos.2 ht0)) _
          (zsmul_mem_pos H hadd _ (hFH ht) _ hs0), ?_⟩
        simp only [cmb, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    obtain ⟨φ, hφD, hφ⟩ := ih (π '' G) (π '' {v ∈ H | v.1 0 = 0}) (hG.image _)
      (Set.image_mono hGH)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ _ ⟨v, ⟨hv, hv0⟩, rfl⟩
        exact ⟨u + v, ⟨hadd u hu v hv, by simp [hu0, hv0]⟩, rfl⟩)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ h
        refine h0 u hu (funext fun i => ?_)
        refine Fin.cases hu0 (fun j => ?_) i
        exact congrFun h j)
    let r : (Fin (d + 1) → ℤ) × ℝ → ℝ := fun v => ∑ i : Fin d, (v.1 i.succ : ℝ) * φ i + v.2
    have hr : ∀ v ∈ G, r v < 0 := fun v hv => hφ (π v) ⟨v, hv, rfl⟩
    have hrc : ∀ s t, r (cmb (s, t)) = (-(t.1 0 : ℝ)) * r s + (s.1 0 : ℝ) * r t := by
      intro s t
      simp only [r, cmb, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
      simp only [zsmul_eq_mul]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
      ring
    obtain ⟨x, hxD, hlo, hhi⟩ := between_fin D hD
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | v.1 0 < 0})
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | 0 < v.1 0})
      ((hF.subset (Set.sep_subset _ _)).image _) ((hF.subset (Set.sep_subset _ _)).image _)
      (by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
        have h1 := hr _ (Or.inr ⟨(s, t), ⟨hs, ht⟩, rfl⟩)
        rw [hrc] at h1
        have hs0 : (0 : ℝ) < s.1 0 := by exact_mod_cast hs.2
        have ht0 : (t.1 0 : ℝ) < 0 := by exact_mod_cast ht.2
        show -r t / (t.1 0 : ℝ) < -r s / (s.1 0 : ℝ)
        rw [← neg_div_neg_eq, div_lt_div_iff₀ (neg_pos.2 ht0) hs0]
        linarith)
    refine ⟨Fin.cons x φ, fun i => Fin.cases hxD hφD i, fun v hv => ?_⟩
    have hsum : ∑ i, (v.1 i : ℝ) * (Fin.cons x φ : Fin (d + 1) → ℝ) i + v.2 = (v.1 0 : ℝ) * x + r v := by
      simp only [r, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
    rw [hsum]
    rcases lt_trichotomy (v.1 0) 0 with h | h | h
    · have h1 := hlo _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (v.1 0 : ℝ) < 0 := by exact_mod_cast h
      rw [div_lt_iff_of_neg h2] at h1
      linarith
    · have h1 := hr v (Or.inl ⟨hv, h⟩)
      rw [h]; simpa using h1
    · have h1 := hhi _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (0 : ℝ) < v.1 0 := by exact_mod_cast h
      rw [lt_div_iff₀ h2] at h1
      linarith

private theorem log_norm_dense (K : Type) [NormedField K] [IsAlgClosed K] (p : K) (hp : p ≠ 0)
    (hp1 : ‖p‖ ≠ 1) (a b : ℝ) (hab : a < b) :
    ∃ x ∈ Set.range (fun u : Kˣ => Real.log ‖(u : K)‖), a < x ∧ x < b := by
  have hL : Real.log ‖p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 hp) hp1
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ, a < q * Real.log ‖p‖ ∧ q * Real.log ‖p‖ < b := by
    rcases lt_or_gt_of_ne hL with h | h
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn ((div_lt_div_right_of_neg h).2 hab)
      rw [div_lt_iff_of_neg h] at h1
      rw [lt_div_iff_of_neg h] at h2
      exact ⟨q, h2, h1⟩
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (div_lt_div_of_pos_right hab h)
      rw [div_lt_iff₀ h] at h1
      rw [lt_div_iff₀ h] at h2
      exact ⟨q, h1, h2⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq p q.den_pos
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_nz] at hr
    exact hp hr.symm
  refine ⟨_, ⟨Units.mk0 r hr0 ^ q.num, ?_⟩, hq1, hq2⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Real.log_zpow]
  rw [← hr, norm_pow, Real.log_pow, Rat.cast_def]
  field_simp

theorem UpperTheory.V.Alg.carver :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (K : Type) [NormedField K] [IsAlgClosed K] (z : σ → K), (∃ p : K, p ≠ 0 ∧ ‖p‖ ≠ 1) →
      (∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → ‖n.prod fun s k => z s ^ k‖ < 1) →
      ∃ t : Multiplicative X →* Kˣ, ∀ s, ‖(t (Multiplicative.ofAdd (wt s)) : K) * z s‖ < 1 := by
  intro σ _ X _ _ _ wt K _ _ z ⟨p, hp, hp1⟩ hz
  let e := (Module.finBasis ℤ X).equivFun
  let g : (σ →₀ ℕ) → K := fun n => n.prod fun s k => z s ^ k
  have hg : ∀ m n, g (m + n) = g m * g n := fun m n =>
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  have hg1 : ∀ s, g (Finsupp.single s 1) = z s := fun s => by
    simp [g, Finsupp.prod_single_index]
  obtain ⟨φ, hφD, hφ⟩ := fourier_motzkin _ (log_norm_dense K p hp hp1) (Module.finrank ℤ X)
    ((fun s => (e (wt s), Real.log ‖z s‖)) '' {s | z s ≠ 0})
    ((fun n => (e (Finsupp.weight wt n), Real.log ‖g n‖)) '' {n | n ≠ 0 ∧ g n ≠ 0})
    ((Set.toFinite _).image _)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨Finsupp.single s 1, ⟨by simp, by rw [hg1]; exact hs⟩, ?_⟩
      simp [hg1, Finsupp.weight_single])
    (by
      rintro _ ⟨m, ⟨hm, hm'⟩, rfl⟩ _ ⟨n, ⟨hn, hn'⟩, rfl⟩
      refine ⟨m + n, ⟨fun h => hm (add_eq_zero.1 h).1, by rw [hg]; exact mul_ne_zero hm' hn'⟩, ?_⟩
      simp only [hg, map_add (f := _), norm_mul, Prod.mk_add_mk,
        Real.log_mul (norm_ne_zero_iff.2 hm') (norm_ne_zero_iff.2 hn')])
    (by
      rintro _ ⟨n, ⟨hn, hn'⟩, rfl⟩ h
      exact Real.log_neg (norm_pos_iff.2 hn') (hz n hn (e.map_eq_zero_iff.1 h)))
  choose u hu using hφD
  let t : Multiplicative X →* Kˣ :=
    { toFun := fun x => ∏ i, u i ^ (e x.toAdd i)
      map_one' := by simp
      map_mul' := fun x y => by simp [zpow_add, Finset.prod_mul_distrib] }
  refine ⟨t, fun s => ?_⟩
  by_cases hs : z s = 0
  · simp [hs]
  have h1 := hφ _ ⟨s, hs, rfl⟩
  have h2 : Real.log ‖(t (Multiplicative.ofAdd (wt s)) : K)‖ = ∑ i, (e (wt s) i : ℝ) * φ i := by
    show Real.log ‖((∏ i, u i ^ (e (wt s) i) : Kˣ) : K)‖ = _
    rw [Units.coe_prod, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.2 (Units.ne_zero _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, ← hu i]
  rw [← Real.log_neg_iff (norm_pos_iff.2 (mul_ne_zero (Units.ne_zero _) hs)), norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 hs), h2]
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mvPowerSeries_mem_span_X_of_constantCoeff_zero {σ R : Type} [Finite σ] [CommRing R] (h : MvPowerSeries σ R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  classical
  have := Fintype.ofFinite σ
  have hex : ∀ d : σ →₀ ℕ, ∃ o : Option σ, d ≠ 0 → ∃ s, o = some s ∧ d s ≠ 0 := by
    intro d
    by_cases hd : d = 0
    · exact ⟨none, fun h => (h hd).elim⟩
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra H
        push_neg at H
        exact hd (Finsupp.ext H)
      exact ⟨some s, fun _ => ⟨s, rfl, hs⟩⟩
  choose sel hsel using hex
  let g : σ → MvPowerSeries σ R := fun s e =>
    if sel (e + Finsupp.single s 1) = some s then MvPowerSeries.coeff (e + Finsupp.single s 1) h
    else 0
  have key : h = ∑ s, MvPowerSeries.X s * g s := by
    ext d
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      rw [if_neg]
      simp [Finsupp.single_le_iff]
    · obtain ⟨s0, hs0, hds0⟩ := hsel d hd
      have hle0 : Finsupp.single s0 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hds0)
      rw [Finset.sum_eq_single s0]
      · rw [if_pos hle0]
        show _ = (if sel (d - Finsupp.single s0 1 + Finsupp.single s0 1) = some s0 then
          MvPowerSeries.coeff (d - Finsupp.single s0 1 + Finsupp.single s0 1) h else 0)
        rw [tsub_add_cancel_of_le hle0, if_pos hs0]
      · intro s _ hs
        split_ifs with hle
        · show (if sel (d - Finsupp.single s 1 + Finsupp.single s 1) = some s then
            MvPowerSeries.coeff (d - Finsupp.single s 1 + Finsupp.single s 1) h else 0) = 0
          rw [tsub_add_cancel_of_le hle, hs0, if_neg]
          intro h'
          exact hs (Option.some_injective _ h').symm
        · rfl
      · simp
  rw [key]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

private theorem mvPowerSeries_exists_polynomial_sub_mem_span_X_pow {σ R : Type} [Finite σ] [CommRing R] (n : ℕ) (g : MvPowerSeries σ R) :
    ∃ p : MvPolynomial σ R, g - (p : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  classical
  have := Fintype.ofFinite σ
  induction n generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have h1 : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
      mvPowerSeries_mem_span_X_of_constantCoeff_zero _ (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries σ R)).mp h1
    choose p hp using fun s => ih (c s)
    refine ⟨MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s, ?_⟩
    have hsum : ((∑ s, p s * MvPolynomial.X s : MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (p s : MvPowerSeries σ R) * MvPowerSeries.X s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    have e : g - ((MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s :
        MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (c s - (p s : MvPowerSeries σ R)) * MvPowerSeries.X s := by
      rw [MvPolynomial.coe_add, hsum, MvPolynomial.coe_C, ← sub_sub, ← hc]
      simp [sub_mul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [e, pow_succ]
    exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_mul (hp s) (Ideal.subset_span ⟨s, rfl⟩)

theorem UpperTheory.V.Alg.co_ev :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (σ : Type) [Finite σ] (f : R →ₐ[O] R') (a : σ → R'), (∀ s, a s ∈ maximalIdeal R') →
      ∃! F : MvPowerSeries σ R →ₐ[O] R', (∀ x, F (C x) = f x) ∧ ∀ s, F (X s) = a s := by
  intro O _ _ R _ _ _ R' _ _ _ σ _ f a ha
  classical
  letI : WithIdeal R' := ⟨maximalIdeal R'⟩
  have hcs : CompleteSpace R' ∧ T2Space R' :=
    (IsAdic.isAdicComplete_iff (R := R') (I := maximalIdeal R') rfl).mp (IsCO.complete (O := O))
  haveI := hcs.1
  haveI := hcs.2
  have hE : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by simp [Filter.cofinite_eq_bot]⟩
  let E : MvPowerSeries σ R →+* R' :=
    (MvPowerSeries.aeval hE).toRingHom.comp (MvPowerSeries.map f.toRingHom)
  have hEC : ∀ x, E (C x) = f x := by
    intro x
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_C, MvPowerSeries.map_C]
  have hEX : ∀ s, E (X s) = a s := by
    intro s
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X, MvPowerSeries.map_X]
  let F : MvPowerSeries σ R →ₐ[O] R' :=
    { E with
      commutes' := fun r => by
        change E (algebraMap O (MvPowerSeries σ R) r) = _
        rw [MvPowerSeries.algebraMap_apply, hEC]
        simp }
  refine ⟨F, ⟨hEC, hEX⟩, ?_⟩
  rintro G ⟨hGC, hGX⟩
  have hpoly : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ x, H (C x) = f x) → (∀ s, H (X s) = a s) →
      ∀ p : MvPolynomial σ R, H (p : MvPowerSeries σ R) = MvPolynomial.eval₂ f.toRingHom a p := by
    intro H hC hX p
    induction p using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.coe_C, hC]
    | add p q hp hq => simp [MvPolynomial.coe_add, hp, hq]
    | mul_X p s hp => simp [MvPolynomial.coe_mul, MvPolynomial.coe_X, hp, hX]
  have hJ : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ s, H (X s) = a s) → ∀ n,
      ∀ y ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ^ n, H y ∈ maximalIdeal R' ^ n := by
    intro H hX n y hy
    have h1 : Ideal.map H (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤ maximalIdeal R' := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [hX]
      exact ha s
    have h2 := Ideal.mem_map_of_mem H hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  have hH : IsHausdorff (maximalIdeal R') R' := (IsCO.complete (O := O)).toIsHausdorff
  ext g
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨p, hp⟩ := mvPowerSeries_exists_polynomial_sub_mem_span_X_pow n g
  have e1 : G g - F g = G (g - p) - F (g - p) := by
    rw [map_sub, map_sub, hpoly G hGC hGX, hpoly F (fun x => hEC x) (fun s => hEX s)]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e1]
  exact Ideal.sub_mem _ (hJ G hGX n _ hp) (hJ F (fun s => hEX s) n _ hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoExt
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_ext_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

theorem UpperTheory.V.Alg.co_ext :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R' : Type) [CommRing R'] [Algebra O R'] (I : Ideal R') [IsHausdorff I R'] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R → maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∀ f f' : R →ₐ[O] R', (∃ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x ∈ I ∧ f' x ∈ I) → f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f' := by
  intro O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs
  have hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R := by
    rintro t (ht | ⟨b, hb, rfl⟩)
    · exact ⟨hs t ht, hS ht⟩
    · refine ⟨DFunLike.congr_fun hi b, ?_⟩
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hb
  have hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2 := by
    rw [Ideal.span_union]
    exact hm
  have key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) →
      ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k := by
    intro g hg k x hx
    rw [pow_mul] at hx
    have hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R') :=
      le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)
    exact hle hx
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  obtain ⟨a, ha, h⟩ := co_ext_approx (maximalIdeal R) (AlgHom.equalizer f f') _
    (IsCO.res_surj (O := O)) hT hm' (n * k) x
  have ha' : f a = f' a := ha
  have : f x - f' x = f (x - a) - f' (x - a) := by rw [map_sub, map_sub, ha']; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, this]
  exact sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem prec_of_surj {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : Function.Surjective p) (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete (I.map p) R' := ⟨fun f hf => by
  have hd : ∀ n, ∃ d ∈ I ^ n, p d = f (n + 1) - f n := fun n => by
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at h
    exact (Ideal.mem_map_iff_of_surjective p hp).1 h
  choose d hdI hd using hd
  obtain ⟨x, hx⟩ := hp (f 0)
  have hg : ∀ n, p (x + ∑ i ∈ Finset.range n, d i) = f n := fun n => by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hd]; ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => x + ∑ i ∈ Finset.range n, d i) (fun {m n} hmn => by
    apply SModEq.symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, add_sub_add_left_eq_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun i hi => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hdI i))
  refine ⟨p L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← hg n, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem p h⟩

theorem UpperTheory.V.Alg.co_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Nontrivial R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ p hp
  have hp' : Function.Surjective (p : R →+* R') := hp
  haveI hL : IsLocalRing R' := IsLocalRing.of_surjective' (p : R →+* R') hp'
  haveI hN : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hp'
  haveI hH : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp'
  have hm : (maximalIdeal R).map (p : R →+* R') = maximalIdeal R' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hP : IsPrecomplete (maximalIdeal R') R' := hm ▸ prec_of_surj (p : R →+* R') hp' (maximalIdeal R)
  refine { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
           isLocalHom := ⟨fun a ha => ?_⟩
           res_surj := fun y => ?_ }
  · rw [← p.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (IsLocalHom.map_nonunit (f := (p : R →+* R')) _ ha)
  · obtain ⟨x, rfl⟩ := hp y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← p.commutes, ← map_sub, ← hm]
    exact Ideal.mem_map_of_mem _ ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem complete_of_sq {R : Type} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0 := by
    intro x hx
    rw [Ideal.smul_eq_mul, Ideal.mul_top, h] at hx
    exact (Submodule.mem_bot R).mp hx
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx2 := hx 2
    rw [SModEq.sub_mem, sub_zero] at hx2
    exact h0 x hx2
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt 2 n with hn | hn
    · have hfn := hf hn
      rw [SModEq.sub_mem] at hfn
      have e : f 2 = f n := sub_eq_zero.mp (h0 _ hfn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _
    · exact hf hn.le

theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [pow_two]
      refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
      rw [hm] at hr hs
      refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
end

