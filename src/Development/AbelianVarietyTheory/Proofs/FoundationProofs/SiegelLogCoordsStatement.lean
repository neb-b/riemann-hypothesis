module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelLogCoords
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_logCoords_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (L : ℕ) (ψ : O0 p →+* Ωl) (io : KT X (p ^ L) →+* Ωl), 1 ≤ L → IsReb T L ψ → IsIo X A T j L ψ io → ∀ ι : On p L →ₐ[O0 p] Ωl, IsEmb T L ι →
  ∀ (N c : ℕ) (A₁ a₂ g : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∀ y : KT X (p ^ L), (y : X.K) = sgN X c N (N * p ^ L) (A₁, a₂) →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = io y ∧ Ev ψ (fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0) z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro Ω _ _ _ ε X hj p _ hp2 A hpA Ωl _ _ hclo T j hcusp L ψ io hL hreb hio ι hemb N c A₁ a₂ g ha₂ hNa hN hNp hc hc6 hNA y hy
  have supp_fin : ∀ {R : Type} [Ring R] (θ : ℤ → ℤ) (f : ℤ → R),
      (∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k = 0) →
      (Function.support (fun k : ℤ => (θ k : R) * f k)).Finite := by
    intro R _ θ f h
    obtain ⟨B, hB⟩ := h
    refine (Set.finite_Icc (-(B : ℤ)) B).subset fun k hk => ?_
    by_contra hc
    apply hk
    have : (B : ℤ) < |k| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
      rcases hc with hc | hc
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_pos (by omega)]; omega
    simp [hB k this]
  obtain ⟨θ, hB, hr0, hcong, hexp, hder, hsm, hunit⟩ := _root_.GlobalTheory.SiegTwo.sgN_two_variable ε X hj p hp2 L N c A₁ a₂ g hL ha₂ hNa hN hNp hc hc6 hNA
  rw [← hy] at hexp hder hunit
  have hζ : j (zt ε p L) = T.ζ L := hcusp.root L
  have hzA : zt ε p L ∈ A := (hcusp.int _).2 (by rw [hζ]; exact GlobalTheory.KumDlog.int_zeta T L)
  have hzA' : (zt ε p L)⁻¹ ∈ A := (hcusp.int _).2 (by rw [map_inv₀, hζ]; exact GlobalTheory.KumDlog.int_zeta_inv T L)
  have hzpow : ∀ m : ℤ, zt ε p L ^ m ∈ A := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hzA m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem hzA' _
  have hpL : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hcoef : ∀ s : ℚ, (X.exp (y : X.K)).coeff s ∈ A ∧
      (X.exp (y : X.K)).coeff s ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω) := by
    intro s
    by_cases hs : (X.exp (y : X.K)).coeff s = 0
    · rw [hs]; exact ⟨zero_mem _, zero_mem _⟩
    have hden := ((KTExp.mem_KT_iff ε X (p ^ L) hpL (y : X.K)).1 y.2) s hs
    have hsr : s = (((s * ((p ^ L : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ L := by
      have e := Rat.intCast_num_of_den_eq_one hden
      have hp0 : (p : ℚ) ^ L ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      rw [e, Nat.cast_pow, mul_div_assoc, div_self hp0, mul_one]
    rw [hsr, hexp]
    constructor
    · refine finsum_induction (· ∈ A) (zero_mem _) (fun _ _ => add_mem) fun k => ?_
      exact mul_mem (intCast_mem _ _) (hzpow _)
    · refine finsum_induction (· ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω)) (zero_mem _)
        (fun _ _ => add_mem) fun k => ?_
      refine mul_mem (intCast_mem _ _) (zpow_mem (IntermediateField.subset_adjoin _ _ ?_) _)
      simp
  obtain ⟨x', hEv⟩ := hio.ev y {zt ε p L} hcoef
  obtain ⟨r0, hr0'⟩ := hr0
  set cU : ℤ → Ωl := fun r => j ((X.exp (y : X.K)).coeff ((r : ℚ) / (p : ℚ) ^ L)) with hcU
  set cE : ℤ → Ωl := fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0 with hcE
  have hjexp : ∀ r, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k) := by
    intro r
    simp only [hcU, hexp r]
    rw [map_finsum j (supp_fin (fun k => θ k r) (fun k => zt ε p L ^ (g * k)) (hB r))]
    simp only [map_mul, map_intCast, map_zpow₀, hζ]
  have hcE0 : ∀ r : ℤ, r < 0 → cE r = 0 := by
    intro r hr
    simp [hcE, not_le.2 hr]
  have hcEmem : ∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L} := by
    intro r
    simp only [hcE]
    split_ifs
    · have h1 : j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) ∈ (Subring.closure {zt ε p L}).map j := Subring.mem_map.2 ⟨_, hsm r.toNat, rfl⟩
      rwa [RingHom.map_closure, Set.image_singleton, hζ] at h1
    · exact zero_mem _
  have hjder : ∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := by
    intro r
    have hfin : (Function.support (fun i : ℤ => (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (y : X.K)).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L))).Finite := by
      refine (Set.finite_Icc 0 (r - r0)).subset fun i hi => ?_
      rw [Function.mem_support] at hi
      constructor
      · by_contra h0
        apply hi
        rw [ite_eq_right h0, zero_mul]
      · by_contra h1
        apply hi
        have h2 : ∀ k, θ k (r - i) = 0 := fun k => hr0' k _ (by omega)
        rw [hexp (r - i)]
        simp [h2]
    have hB' : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → k * θ k r = 0 := by
      obtain ⟨B, hb⟩ := hB r
      exact ⟨B, fun k hk => by rw [hb k hk, mul_zero]⟩
    have h := congrArg j (hder r)
    rw [map_neg, map_finsum j (supp_fin (fun k => k * θ k r) (fun k => zt ε p L ^ (g * k)) hB'), map_finsum j hfin] at h
    simp only [map_mul, map_intCast, map_zpow₀, hζ] at h
    rw [h]
    congr 1
    refine finsum_congr fun i => ?_
    simp only [hcE, hcU]
    split_ifs <;> simp
  have hzi : ∀ m : ℤ, IsInt (p := p) ((T.ζ L) ^ m) := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta T L) m
    · rw [zpow_negSucc, ← inv_pow]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta_inv T L) _
  obtain ⟨r, m, hrm⟩ := hunit
  have hcu : cU r ≠ 0 ∧ IsInt (p := p) (cU r)⁻¹ := by
    have hz0 : (T.ζ L) ^ m ≠ 0 := zpow_ne_zero _ (GlobalTheory.KumDlog.zeta_ne T L)
    rcases hrm with hrm | hrm
    · simp only [hcU, hrm, map_zpow₀, hζ]
      exact ⟨hz0, by rw [← zpow_neg]; exact hzi _⟩
    · simp only [hcU, hrm, map_neg, map_zpow₀, hζ]
      exact ⟨neg_ne_zero.2 hz0, by rw [inv_neg, ← zpow_neg]; exact GlobalTheory.KumDlog.int_neg (hzi _)⟩
  obtain ⟨hx0, hxi⟩ := (GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ωl hclo T L ψ hreb 0 cU (io y) x' hEv).2 ⟨r, hcu.1, hcu.2⟩
  have logCoords : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
    ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
    (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
    (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
    Ev ψ cU x x' → x ≠ 0 → IsInt (p := p) x⁻¹ →
    ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
      Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
      Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
    intro p hp Ω _ _ hc T L ψ ι hL hψ hι A₁ g θ cU cE x x' hB ⟨r0, h0⟩ hdiv hU hE hE0 hEm hx hx0 hxi
    have cong_sum : ∀ {L : ℕ} (S : Finset ℤ) (v : ℤ → ℤ) (e : ℤ → Ω) (he : ∀ k, IsInt (p := p) (e k)) (hv : ∀ k, (p : ℤ) ^ L ∣ v k),
        Cong (p := p) L (∑ k ∈ S, (v k : Ω) * e k) 0 := by
      intro L S v e he hv
      choose c hc using hv
      refine ⟨∑ k ∈ S, (c k : Ω) * e k, IsIntegral.sum _ fun k _ => IsIntegral.mul (Basic.isInt_intCast _) (he k), ?_⟩
      rw [sub_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hc k]
      push_cast
      ring

    have cong_val : ∀ (hc : IsClo p Ω) {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g A : ℤ)
        (θ v : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ) (cU cE : ℤ → Ω) (x x' z z' y y' : Ω)
        (hv : ∀ k r, θ k r ≠ 0 → (p : ℤ) ^ L ∣ v k r - A * k)
        (hE : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i))
        (hx : Ev ψ cU x x') (hz : Ev ψ cE z z')
        (hy : Ev ψ (fun r => ∑ k ∈ S r, (v k r : Ω) * (θ k r : Ω) * T.ζ L ^ (g * k)) y y'),
        Cong (p := p) L (y + A * (z * x)) 0 := by
      intro hc T L ψ hψ g A θ v S cU cE x x' z z' y y' hv hE hx hz hy
      have hN : 0 < p ^ L := pow_pos hp.out.pos L
      have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
      obtain ⟨R1, R2⟩ := GlobalTheory.Glue.EvRing.ev_ring p Ω hc T L ψ hψ
      obtain ⟨U, rfl⟩ := (R2 _ _ _ hx).2.2.1
      obtain ⟨E, rfl⟩ := (R2 _ _ _ hz).2.2.1
      obtain ⟨Y, hY⟩ := (R2 _ _ _ hy).2.2.1
      have h1 := (R2 _ _ _ (R1 E U _ _ _ _ hz hx).1).2.2.2.2.1 (A : Ω) (Basic.isInt_intCast _) (GlobalTheory.Glue.SiegLoc.isAlgZp_int _)
      obtain ⟨V, hV⟩ := (R2 _ _ _ h1).2.2.1
      rw [← hV] at h1
      rw [← hY] at hy
      refine ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T L ψ hψ L _ _ _ (R1 Y V _ _ _ _ hy h1).2.1).1).2 fun r => ?_
      have e : (Y + V).coeff r = ∑ k ∈ S r, (((v k r - A * k) * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) := by
        rw [HahnSeries.coeff_add, hY, hV]
        simp only
        rw [GlobalTheory.Glue.SiegLoc.coeff_mul_finsum, ← neg_eq_iff_eq_neg.2 (hE r), mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [e]
      refine cong_sum _ (fun k => (v k r - A * k) * θ k r) _ (fun k => ?_) fun k => ?_
      · rw [GlobalTheory.Glue.SiegLoc.zpow_emod hN hζ]
        exact IsIntegral.pow (GlobalTheory.Glue.EvTwist.isInt_of_pow hN hζ) _
      · by_cases h : θ k r = 0
        · simp [h]
        · exact Dvd.dvd.mul_right (hv k r h) _
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    choose B hB using hB
    let S : ℤ → Finset ℤ := fun r => Finset.Icc (-(B r : ℤ)) (B r)
    have hS : ∀ (r : ℤ) (f : ℤ → Ω), (∀ k, θ k r = 0 → f k = 0) → ∑ᶠ k, f k = ∑ k ∈ S r, f k := fun r f hf =>
      finsum_eq_sum_of_support_subset _ fun k hk => by
        rw [Finset.mem_coe, Finset.mem_Icc, ← abs_le]
        exact not_lt.1 fun h => hk (hf k (hB r k h))
    have hE' : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ (m + 1) ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := fun r => by
      rw [← hE r, hS r _ fun k hk => by simp [hk]]
    obtain ⟨z, z', hz⟩ := GlobalTheory.Glue.SiegLoc.ev_cyc T (m + 1) ψ cE hE0 hEm
    obtain ⟨a, ha⟩ := GlobalTheory.Glue.SiegLoc.rep hψ g θ S r0 h0
    obtain ⟨y0, e0⟩ := ha fun _ _ => 1
    obtain ⟨y1, e1⟩ := ha fun _ j => j
    obtain ⟨y2, e2⟩ := ha fun i _ => i
    have hN : (0 : ℤ) < ((p ^ (m + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos _
    have hmod : ∀ r : ℤ, (p : ℤ) ^ (m + 1) ∣ ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ) - r := fun r => by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg r hN.ne')]
      have := Int.emod_add_mul_ediv r ((p ^ (m + 1) : ℕ) : ℤ)
      push_cast at this ⊢
      exact ⟨-(r / (p : ℤ) ^ (m + 1)), by linarith⟩
    obtain ⟨c1, hc1, k1⟩ := cong_val hc hψ g A₁ θ (fun _ r => ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
      (fun k r h => by simpa using dvd_add (hmod r) (hdiv k r h)) hE' hx hz e1
    obtain ⟨c2, hc2, k2⟩ := cong_val hc hψ g g θ (fun k _ => ((g * k % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
      (fun k r _ => hmod _) hE' hx hz e2
    have hcU : cU = fun r => ∑ k ∈ S r, ((1 : ℤ) : Ω) * (θ k r : Ω) * T.ζ (m + 1) ^ (g * k) := funext fun r => by
      rw [hU r, hS r _ fun k hk => by simp [hk]]
      simp
    rw [← hcU] at e0
    have hxe := (GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients p Ω hc T (m + 1) ψ hψ _ _ _ _ _ hx e0).1
    set w0 : On p (m + 1) := ∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
      algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) with hw0
    have hw : ι w0 = x := by
      rw [hxe, hw0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hι.1, hι.2, Int.cast_one, one_mul]
    obtain ⟨w, hwu⟩ := GlobalTheory.Glue.SiegLoc.isUnit_of_inv ι (_root_.GlobalTheory.K5.LevEmb.emb_inj_range p Ω hc T (m + 1) hL ι hι).1 w0 (hw ▸ hx0) (hw ▸ hxi)
    obtain ⟨α, β, hd⟩ := GlobalTheory.K5.exists_isDlog p (m + 1) w
    obtain ⟨d1, d2⟩ := GlobalTheory.Glue.SiegLoc.coef m a w α β (hwu.trans hw0) hd
    obtain ⟨f1, d1⟩ := Ideal.mem_span_singleton'.1 d1
    obtain ⟨f2, d2⟩ := Ideal.mem_span_singleton'.1 d2
    replace d1 := congrArg ι d1
    replace d2 := congrArg ι d2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_sub, map_natCast, map_one, AlgHom.commutes, hι.1, hι.2, hwu, hw, GlobalTheory.Glue.SiegLoc.zeta_one] at d1 d2
    simp only [Int.cast_natCast] at k1 k2
    have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    refine ⟨w, α, β, z, z', hd, hwu ▸ hw, hz, ⟨(ι f1 + c1) * x⁻¹,
      IsIntegral.mul (IsIntegral.add (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hc1) hxi, ?_⟩, ?_⟩
    · linear_combination x⁻¹ * k1 - x⁻¹ * d1 - (ι α + A₁ * z) * hinv
    · have hζ1 : T.ζ 1 - 1 ≠ 0 := sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using hp.out.one_lt))
      have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (pow_pos hp.out.pos _))
      rw [pow_one, div_eq_mul_inv] at hpd
      have hinv2 : (T.ζ 1 - 1) * (T.ζ 1 - 1)⁻¹ = 1 := mul_inv_cancel₀ hζ1
      have hpi : IsInt (p := p) (p : Ω) := by simpa using Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
      refine ⟨(ι f2 * ((p : Ω) * (T.ζ 1 - 1)⁻¹) + p * c2) * x⁻¹,
        IsIntegral.mul (IsIntegral.add (IsIntegral.mul (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hpd) (IsIntegral.mul hpi hc2)) hxi, ?_⟩
      generalize (∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
        ((i : ℕ) : Ω) * algebraMap (O0 p) Ω (a i j) * T.ζ (m + 1) ^ (i : ℕ) * T.qq (m + 1) ^ (j : ℕ)) = Y at k2 d2
      linear_combination (p * x⁻¹) * k2 - (p * x⁻¹ * (T.ζ 1 - 1)⁻¹) * d2 - (p * x⁻¹ * (x * ι β - Y)) * hinv2
        - (p * (ι β + g * z)) * hinv
  exact logCoords p Ωl hclo T L ψ ι hL hreb hemb A₁ g θ cU cE (io y) x' hB ⟨r0, hr0'⟩ hcong hjexp hjder hcE0 hcEmem hEv hx0 hxi
