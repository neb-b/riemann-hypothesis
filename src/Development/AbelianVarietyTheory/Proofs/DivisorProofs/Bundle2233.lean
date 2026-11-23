module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefAway

theorem vLa_nat_eq_zero {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ}
    (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) : vLa la (N : K) = 0 := by
  rw [vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]
  simp

theorem vLa_nat_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0)
    (hN : ((N : ℕ) : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (N : K) := by
  have h1 : la.valuation K (N : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) N]
    exact (la.valuation_lt_one_iff_mem _).2 hN
  have h2 : la.valuation K (N : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast h0
  have h3 := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  unfold vLa
  omega

theorem isUnit_nat {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h3 := ho.2 (N : K)
  rw [vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem nat_not_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p N : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime p N) : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))

theorem vV_nat_eq {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) (p : ℕ) :
    vV S.V (p : S.Fr) = (e : ℤ) * vLa la (p : K) := by
  rw [← ho.2, map_natCast]

theorem le_nval_place {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) {p : ℕ} (hp : 0 < vLa la (p : K)) (A : ℕ) (x : S.Fr)
    (h : ((A : ℝ) : EReal) ≤ nval S.V (vV S.V (p : S.Fr)).toNat x) :
    (((vLa la (p : K) * A : ℤ) : ℝ) : EReal) ≤ nval S.V e x := by
  by_cases hx : x = 0
  · rw [hx, nval_zero]; exact le_top
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ) := by
    have h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K) := by
      rw [Int.toNat_of_nonneg, vV_nat_eq ho]
      rw [vV_nat_eq ho]; positivity
    exact_mod_cast h2
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp' : (0 : ℝ) < (vLa la (p : K) : ℝ) := by exact_mod_cast hp
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  rw [h1, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he']
  push_cast
  linarith

theorem coprime_type (D : D7) : Nat.Coprime (D.host.g 0 * D.host.g 1) (D.host.QS * D.host.q * D.host.d) := by
  have h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    have hc := D.ntypes.g_cond k
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
    exact h1
  exact Nat.Coprime.mul_left (h 0) (h 1)

theorem err_le (R N ρ u Dg φ c r v g₀ g₁ : ℝ) (hR : 0 ≤ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hu : 0 ≤ u) (hr : 0 < r)
    (hv : 0 < v) (hg₀ : 0 < g₀) (hg₁ : 1 ≤ g₁) (hφ : 0 ≤ φ) (hc : R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ ≤ c) :
    Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v) ≤ c * φ / v := by
  have hN : 0 ≤ N := hρ0.trans hρ
  calc Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v)
      ≤ Dg ^ 2 * (R * N ^ 3 * (r * φ)) / (g₀ * 1) / (r * v) := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ / v := by field_simp
    _ ≤ R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ * φ / v := by
      gcongr
      nlinarith [sq_nonneg Dg]
    _ ≤ _ := by gcongr

theorem refExp_le_of_oscLe : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  intro D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO
  letI := T.Q.H.starRing
  have hqp : q.Prime := hq'.out
  refine (refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1
  obtain ⟨A, hA⟩ := hO la
  obtain ⟨P₁, hP₁, hPB⟩ := GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA
  obtain ⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  have ho' := hov la.1 e ho
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T hL EX
  obtain ⟨π, π', hsplit⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hL EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  have hcop : Nat.Coprime q T.Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0))
      ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V) := isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ n := by omega
  have hρN : ρ ≤ 2 * D.R.f * D.R.m := by
    refine hρ.trans ?_
    rw [GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hρN
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ T.Q.l.M := hM ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by exact_mod_cast hle
  have hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ) := by
    refine lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')
    gcongr

  have hε : 0 < vLa la.1 (q : T.Q.c.F) := vLa_nat_pos la.1 hqp.ne_zero la.2
  have hv0 : 0 < vV S.V (q : S.Fr) := by
    rw [vV_nat_eq ho]
    exact mul_pos (by exact_mod_cast ho.1) hε
  obtain ⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v := ⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩
  have hvpos : 0 < v := by omega
  have hv' : (vV S'.V (q : S'.Fr)).toNat = r * v := by
    rw [hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]
  have hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F) := by
    rw [← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos

  have hup := GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB
    α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁
  have hloc := (hPB S' io' _ ho' y' hy' C T.Q.l.M).2
  rw [hv'] at hloc
  have hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤
      cst * φ / v := by
    rw [hM, Nat.cast_mul, Nat.cast_mul]
    refine err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith)
      hφ.nonneg (hJ 0).2.2
    · unfold rr0; positivity
    · positivity
  have hinf := hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))

  obtain ⟨m, hm, hmlow, -⟩ := GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit
    (coprime_type D) a n
  have hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤
      ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f),
        nval S'.V (r * v) (evI y' f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n := ⟨x, P₁, hP₁, hx⟩
    have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2
      a n hD hLP f hf
    have hlow := GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp
      (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx
    obtain ⟨s, hs0, hsv, g, hg, hgs⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n)
      ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by
        rintro _ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩
        exact le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))
    have h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f) := by
      refine (iInf₂_le g hg).trans (le_of_eq ?_)
      show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _
      rw [hv, Int.toNat_natCast, hgs, evI_smul]
    have h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]
      congr 1
      have h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ) := by exact_mod_cast hrv
      have h4 : ((r * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'
      rw [div_eq_iff h4, h3]
      push_cast
      ring
    rw [← hsc nab hnab a n v s f hf, nval_mul, h2] at h1
    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
    rw [add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  have hfin := hdep.trans hinf
  rw [hv, Int.cast_natCast]
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    ← EReal.coe_sub] at hfin
  rw [← EReal.coe_add]
  exact hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.RefAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovMult

open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum

section Places

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
    | prime p hp => exact fun _ h => ⟨p, hp, h⟩
    | mul a b ha hb =>
      intro h hm
      rw [Nat.cast_mul] at hm
      exact (la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  exact key _ h0 (Ideal.absNorm_mem _)

theorem vLa_nat_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

theorem vLa_pos {la : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ≠ 0) (h : (q : 𝓞 K) ∈ la.asIdeal) :
    0 < vLa la (q : K) := by
  have h1 : la.valuation K (q : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h
    simpa using this
  have h0 : la.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  unfold vLa
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem exists_spread {S : Finset ℕ} {a : ℕ → ℝ} {s : ℝ} (h : PrimeSum S a s) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ) : ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t ≤ cost e t + s ∧
      ∀ (la : HeightOneSpectrum (𝓞 K)) (q : ℕ), e la + (vLa la (q : K) : ℝ) * a q ≤ e' la := by
  classical
  obtain ⟨hp, h0, hS, hs⟩ := h
  have one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b := by
    intro q hq b e
    have hf := fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b
    refine ⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩
    have h1 := sum_vAdd_nat (K := K) hq
    have h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) /
        (Module.finrank ℚ K : ℝ) = b * Real.log q := by
      rw [← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]
      · refine Finset.sum_congr rfl fun la _ => ?_
        simp only [Finsupp.ofSupportFinite_coe, lw]; ring
      · intro la hla
        simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
        intro h
        apply hla
        simp only
        rw [← mul_assoc, mul_comm b, h, zero_mul]
    rw [cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]
    ring
  have all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨e, by simp, by simp⟩
    | insert q T hq ih =>
      intro hT
      obtain ⟨e₁, h1, h2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      obtain ⟨e₂, h3, h4⟩ := one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁
      exact ⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩
  obtain ⟨e', h1, h2⟩ := all S fun q hq => (hp q hq).ne_zero
  have hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q := fun la q hq =>
    mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)
  refine ⟨e', by linarith, fun la q => ?_⟩
  rw [h2]
  by_cases hq : q ∈ S
  · exact add_le_add_right (Finset.single_le_sum (hn la) hq) _
  · rw [hS q hq, mul_zero]
    exact add_le_add_right (Finset.sum_nonneg (hn la)) _

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem depthOn_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {cst a : ℝ} {G : WTZ E} {q : ℕ} (hq : q ≠ 0)
    (ha : refExp_vp U cst G q ≤ (a : EReal)) {la : HeightOneSpectrum (𝓞 c.F)} (hla : (q : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {y : IntFr Xo c T io} (hy : y.IsAlg)
    {φ : ℝ} (hφ : HasPhi y φ) {Z : Comp Xo c} (hZ : letI := io.toAlgebra; LiesOn Z y.1) :
    depthOn U Z G (fun f => nval T.V e (evI y f)) ≤ (((vLa la (q : c.F) : ℝ) * a + cst * φ / e : ℝ) : EReal) := by
  letI := io.toAlgebra
  have hb := (refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ
  rw [← EReal.coe_add] at hb
  have hm := vLa_pos hq hla
  have hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F) := by rw [← ho.2, map_natCast]
  have hm' : (0 : ℝ) < vLa la (q : c.F) := by exact_mod_cast hm
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F) := by
    have : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F) := by
      rw [← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]
    exact_mod_cast this
  refine le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb' not_lt_bot
  | top => exact le_top
  | coe b =>
    have hb1 := EReal.coe_lt_coe_iff.1 hb'
    have hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal) := by
      refine hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
      rw [lt_div_iff₀ hm', hv]
      refine lt_of_eq_of_lt ?_ hb1
      push_cast; field_simp
    unfold depthAt_vp depth_vw at hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hwl, hw⟩ := iInf_lt_iff.1 hw
    have hne : evI y (w : Rul Xo c) ≠ 0 := fun h0 => by
      simp only [h0, nval_zero] at hw
      exact not_top_lt hw
    obtain ⟨g, hg, hgl⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w
    have hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c) := hg T.Fr y.1 hZ
    refine (iInf₂_le g (hgl hwl)).trans ?_
    simp only [nval_of_ne hne] at hw
    beta_reduce
    rw [hev, nval_of_ne hne, EReal.coe_le_coe_iff]
    have h2 := EReal.coe_lt_coe_iff.1 hw
    rw [hn, ← div_div, div_lt_div_iff_of_pos_right hm'] at h2
    exact h2.le

theorem exists_bound (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {a : ℕ → ℝ} {G : WTZ E}
    (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (a q : EReal)) {Z : Comp Xo c} {θ : Rul Xo c} {w : Ix Dw → ℤ}
    (hθ : θ ∈ secZ Xo c w) {e e' : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (he : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (q : ℕ), e la + (vLa la (q : c.F) : ℝ) * a q ≤ e' la)
    (hk : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
      ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
        ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {G' : WTZ E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z G') (hf0 : v f ≠ ⊤) :
    ∃ B : ℝ, depthOn U Z G v ≤ (B : EReal) ∧ ((8 * B - 8 * e' la : ℝ) : EReal) ≤ v θ := by
  obtain ⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  obtain ⟨q, hq, hla⟩ := exists_prime_mem la
  have hf1 : evI y' f ≠ 0 := fun h => hf0 (by
    show nval T.V e₀ (evI y f) = ⊤
    rw [← (hv f hf.1.1.1).2, h, nval_zero])
  letI := (i.comp io).toAlgebra
  have hZ : LiesOn Z y'.1 := by
    by_contra h
    exact hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))
  refine ⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩
  · exact iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)
    have := he la q
    have e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁) := by ring
    linarith

theorem mult_of (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {u u' : AllWt.Weight Dw} {S : Finset ℕ} {a : ℕ → ℝ} {s cc : ℝ}
    (hS : PrimeSum S a s) (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) (wtOf Dw u 0) q ≤ (a q : EReal)) {Z : Comp Xo c}
    (hZ : ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u u' θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc) :
    Mult U x V dict Z u u' (cc + s) := by
  obtain ⟨θ, e, t, hC, hk, hI, hco⟩ := hZ
  obtain ⟨e', he', he⟩ := exists_spread hS e t
  have key := fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0
  refine ⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩
  · obtain ⟨B, hB, -⟩ := key la v hv G' f hf hf0
    by_contra hn
    push Not at hn
    exact EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))
  · obtain ⟨B, hB, hB'⟩ := key la v hv _ w w.2 hw
    calc _ ≤ ((8 : ℕ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le 8)
      _ = ((8 * B - 8 * e' la : ℝ) : EReal) + ((((8 : ℕ) : ℝ) * e' la : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add_left hB' _

theorem budget_add {T a b C₁ C₂ u : ℝ} (h₁ : T * b ≤ C₁ * u) (h₂ : T * a ≤ C₂ * u) : T * (a + b) ≤ (C₁ + C₂) * u := by
  linarith

end GlobalTheory.CovMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  first | exact @GlobalTheory.QDivSum.sum_eq | exact GlobalTheory.QDivSum.sum_eq | (intros; apply GlobalTheory.QDivSum.sum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairing
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem cartier_primePow_pairing (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r :=
  convPow_primePow_apply_pow p R h G n r χ a

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryAStatement
section
alias GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub :=
  GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary
end

