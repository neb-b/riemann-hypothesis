module

public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.ResidueCharacters.FiniteRoots
public import Formalism.LocalRingCardinality.DataParams

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.CyclotomicWeightExponentLe
section
namespace UpperTheory.N.Num

variable {l N h : ℕ} {y : ℝ}

theorem one_le_sN (l N : ℕ) : 1 ≤ sN l N := le_max_left _ _

theorem lamN_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) :
    (lamN l N h : ℝ) ≤ 3 * lam l (sN l N) y := by
  have h1 := natLog_le_lam hl (one_le_sN l N) hy (n := 2 * h) (by push_cast; linarith)
  have h2 := natLog_le_lam hl (one_le_sN l N) hy hN
  have h3 := s_le_lam (s := sN l N) hl hy
  unfold lamN
  push_cast
  linarith

theorem eL_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) :
    (eL l N h : ℝ) ≤ 1000 * y * sN l N := by
  have h1 := lamN_le hl hy hh hN
  have h2 := lam_le hl (one_le_sN l N) hy
  have hs : (1 : ℝ) ≤ sN l N := by exact_mod_cast one_le_sN l N
  have h3 : (h : ℝ) * sN l N ≤ 4 * y * sN l N := mul_le_mul_of_nonneg_right hh (by linarith)
  have h4 : 1 ≤ y * sN l N := by nlinarith
  unfold eL
  push_cast
  nlinarith

theorem cyclotomicWeightExponent_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) {n : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hn : (n : ℝ) ≤ 8 * a) : (c0L l N h n : ℝ) ≤ 1000 * a * lam l (sN l N) y := by
  have hs := one_le_sN l N
  have h2 := lamN_le hl hy hh hN
  have hl1 := one_le_lam (s := sN l N) hl hy
  unfold c0L
  push_cast
  have hn1 : (n : ℝ) + 1 ≤ 9 * a := by linarith
  have hL0 : (0 : ℝ) ≤ lamN l N h := by positivity
  calc 20 * ((n : ℝ) + 1) * (lamN l N h : ℝ)
      ≤ 20 * (9 * a) * (3 * lam l (sN l N) y) := by
        apply mul_le_mul (by linarith) h2 hL0 (by linarith)
    _ ≤ 1000 * a * lam l (sN l N) y := by nlinarith

theorem cBL_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) {n t : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hn : (n : ℝ) ≤ 2 * a) (ht : 1 ≤ t) :
    (cBL l N h n t : ℝ) ≤ 1000 * t * a * lam l (sN l N) y := by
  have h1 := lamN_le hl hy hh hN
  have hΛ := one_le_lam (s := sN l N) hl hy
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  unfold cBL
  push_cast
  calc (40 : ℝ) * (t + 1) * (n + 1) * lamN l N h ≤ 40 * (2 * t) * (3 * a) * (3 * lam l (sN l N) y) := by
        gcongr <;> linarith
    _ = 720 * (t * a * lam l (sN l N) y) := by ring
    _ ≤ 1000 * (t * a * lam l (sN l N) y) := by gcongr; norm_num
    _ = _ := by ring

end UpperTheory.N.Num
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.LocNum
section
open Formalism Formalism.MainNotions

namespace UpperTheory.N.LocNum

theorem mN_le (l s h : ℕ) (hl : l.Prime) : LocalSituation.mN l s (h + h) ≤ 2 * s + Nat.log l (2 * h) + 2 := by
  have hn0 : LocalSituation.n0 l (h + h) ≤ Nat.log l (2 * h) + 1 := by
    refine Nat.sInf_le ?_
    have h1 := Nat.lt_pow_succ_log_self hl.one_lt (2 * h)
    have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
    show h + h ≤ l ^ (Nat.log l (2 * h) + 1) * (l - 1)
    calc h + h = 2 * h := by ring
      _ ≤ l ^ (Nat.log l (2 * h) + 1) := h1.le
      _ ≤ _ := Nat.le_mul_of_pos_right _ h2
  unfold LocalSituation.mN; omega

theorem rI_le (l m h n : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (i : ℤ) (hi : 0 ≤ i) (hi' : i ≤ h) :
    LocalSituation.rI l m U' i ≤ n * (m + Nat.log l (2 * h)) := by
  classical
  have hfin : U'.Finite := (U.finite_toSet).subset hU
  unfold LocalSituation.rI
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : hfin.toFinset ⊆ U := by
    intro x hx
    exact hU ((Set.Finite.mem_toFinset hfin).1 hx)
  have hcard : hfin.toFinset.card ≤ n := (Finset.card_le_card hsub).trans hn
  have hterm : ∀ u ∈ hfin.toFinset, (∑ᶠ (_ : u ≠ i), (m + LocalSituation.vZ l (u - i))) ≤ m + Nat.log l (2 * h) := by
    intro u hu
    rw [finsum_eq_if]
    split_ifs with hui
    · have huU := hsub hu
      obtain ⟨hb1, hb2⟩ := hb u huU
      have hz : (u - i).natAbs ≤ 2 * h := by omega
      have hv : LocalSituation.vZ l (u - i) ≤ Nat.log l (2 * h) := by
        unfold LocalSituation.vZ padicValInt
        exact (padicValNat_le_nat_log _).trans (Nat.log_mono_right hz)
      omega
    · exact Nat.zero_le _
  calc ∑ u ∈ hfin.toFinset, (∑ᶠ (_ : u ≠ i), (m + LocalSituation.vZ l (u - i)))
      ≤ hfin.toFinset.card • (m + Nat.log l (2 * h)) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = hfin.toFinset.card * (m + Nat.log l (2 * h)) := by rw [smul_eq_mul]
    _ ≤ n * (m + Nat.log l (2 * h)) := Nat.mul_le_mul_right _ hcard

theorem cLL_le (l N h n k vd : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (hk : k ≤ h + 1) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h)) :
    LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 (k : ℤ) ≤ 2 * lamN l N h + k * (3 * (n + 1) * lamN l N h) := by
  set M := LocalSituation.mN l (sN l N) (h + h) with hM
  have hMle : M ≤ 2 * sN l N + Nat.log l (2 * h) + 2 := mN_le l (sN l N) h hl
  have hs : 1 ≤ sN l N := le_max_left _ _
  have hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1 := rfl
  have hterm : ∀ i ∈ Finset.Ico (0 : ℤ) (k : ℤ), 2 + max 1 (LocalSituation.rI l M U' i) ≤ 3 * (n + 1) * lamN l N h := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hr := rI_le l M h n hl U U' hU hn hb i hi.1 (by omega)
    have hr2 : n * (M + Nat.log l (2 * h)) ≤ n * (2 * lamN l N h) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmax : max 1 (LocalSituation.rI l M U' i) ≤ 1 + LocalSituation.rI l M U' i := max_le (by omega) (by omega)
    have hL1 : 1 ≤ lamN l N h := by omega
    nlinarith
  unfold LocalSituation.cLL
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Int.card_Ico, smul_eq_mul] at hsum
  simp only [sub_zero, Int.toNat_natCast] at hsum
  have hvd2 : vd ≤ 2 * lamN l N h := by omega
  omega

theorem latticeExponent_one_le_invariantsKillingExponent (l N h n vd : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h)) :
    LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 1 ≤ c0L l N h n := by
  have h3 := cLL_le l N h n 1 vd hl U U' hU hn hb (by omega) hvd
  simp only [Nat.cast_one, one_mul] at h3
  unfold c0L
  have hL1 : 1 ≤ lamN l N h := by unfold lamN; omega
  nlinarith

theorem cTB_le (l N h n t e vd g : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (he : e < t) (ht : t ≤ h) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h))
    (hg : g ≤ Nat.log l N + 1) :
    LocalSituation.cTB l (sN l N) e 0 (LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 ((e : ℤ) + 1)) + g ≤ cBL l N h n t := by
  have h3 := cLL_le l N h n (e + 1) vd hl U U' hU hn hb (by omega) hvd
  push_cast at h3
  have hs : 1 ≤ sN l N := le_max_left _ _
  have hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1 := rfl
  have hv1 : padicValNat l e ≤ e := by
    rw [Nat.padicValNat_def]
    exact (multiplicity_le_nat_log e).trans (Nat.log_le_self _ _)
  have hv2 : padicValNat l (e + 1) ≤ e + 1 := by
    rw [Nat.padicValNat_def]
    exact (multiplicity_le_nat_log _).trans (Nat.log_le_self _ _)
  have hd : e / (l - 1) ≤ e := Nat.div_le_self _ _
  unfold LocalSituation.cTB cBL
  set L := lamN l N h
  set c := LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 ((e : ℤ) + 1)
  have hL1 : 1 ≤ L := by omega
  have hsL : sN l N ≤ L := by omega
  have hgL : g ≤ L := by omega
  have hm1 : (e + 1) * (3 * (n + 1) * L) ≤ t * (3 * (n + 1) * L) := Nat.mul_le_mul_right _ (by omega)
  have hm2 : (e + 2) * sN l N ≤ (t + 1) * L := Nat.mul_le_mul (by omega) hsL
  have hX : (t + 1) * L ≤ (t + 1) * (n + 1) * L := by
    calc (t + 1) * L = 1 * ((t + 1) * L) := by ring
      _ ≤ (n + 1) * ((t + 1) * L) := Nat.mul_le_mul_right _ (by omega)
      _ = (t + 1) * (n + 1) * L := by ring
  have hY : t + 1 ≤ (t + 1) * L := by
    calc t + 1 = (t + 1) * 1 := by ring
      _ ≤ (t + 1) * L := Nat.mul_le_mul_left _ hL1
  have hV : L ≤ (t + 1) * L := by
    calc L = 1 * L := by ring
      _ ≤ (t + 1) * L := Nat.mul_le_mul_right _ (by omega)
  have hZ : t * (3 * (n + 1) * L) ≤ 3 * ((t + 1) * (n + 1) * L) := by
    have : t * (3 * (n + 1) * L) = 3 * (t * (n + 1) * L) := by ring
    rw [this]
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_right _ (by omega)
  have hW : 40 * (t + 1) * (n + 1) * L = 40 * ((t + 1) * (n + 1) * L) := by ring
  rw [hW]
  omega


open Formalism.BasicNotions Formalism.BasicNotions.Loc in
theorem exists_up {l : ℕ} [Fact l.Prime] {N : ℕ} {K LL : FinExt l} (hC : Cyc N K LL) :
    ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ Good K' (sN l N) LL ∧ Ks K' (sN l N) = K'.1 ∧ (GK K').Normal ∧
      padicValNat l (Module.finrank ℚ_[l] ↥K'.1 / Module.finrank ℚ_[l] ↥K.1) ≤ Nat.log l N + 1 :=
  ⟨Cyc.Kc l (Nat.lcm l N) (Cyc.lcm_pos hC.pos), hC.le, Cyc.good_lcm' hC.pos hC.lvl LL hC.coef, Cyc.Ks_lcm hC.pos,
    Cyc.GK_normal _, Cyc.val_index_le hC.pos _⟩

end UpperTheory.N.LocNum
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
section
noncomputable section

open NumberField Formalism Formalism.BasicNotions

namespace UpperTheory.N.Num

variable {D : D7}

theorem ranks (D : D7) : (1 : ℝ) ≤ D.R.m ∧ (D.R.m : ℝ) ≤ D.R.f ∧ (D.R.f : ℝ) ≤ D.R.k ∧ (D.R.k : ℝ) ≤ D.R.r ∧
    (D.R.r : ℝ) ≤ D.R.t ∧ (D.R.t : ℝ) ≤ D.R.nV ∧ (D.R.nV : ℝ) ≤ 2 * D.R.t := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 := D.R.f_le_k
  have h4 := D.R.rank_add_five_le
  have e1 : D.R.f = 2 * D.R.ord := rfl
  have e2 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e3 : D.R.nV = D.R.r + D.R.t := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_cast <;> omega

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b := Real.one_le_exp (by linarith [one_le_L L])

theorem condN_le (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.host.condN : ℝ) ≤ L.sc.b := by
  have hc := P.condE_le
  have hb := one_le_b L
  obtain ⟨r1, r2, r3, r4, r5, -, -⟩ := ranks D
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ (by linarith)
  have h1 : L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b := by
    conv_rhs => rw [← Real.rpow_one L.sc.b]
    exact Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
  have e : (LevelStarExponents.condE D : ℝ) = D.host.condN := rfl
  rw [e] at hc
  have h2 : (D.host.condN : ℝ) ≤ (D.host.condN : ℝ) ^ 36 := by exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h3 : (D.host.condN : ℝ) ^ 36 ≤ (D.host.condN : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem sizes_le_b (L : SizeData₂ D) (P : ParameterChoice' D L) :
    L.Sc ≤ L.sc.b ∧ L.etaSz ≤ L.sc.b ∧ (D.R.t : ℝ) ≤ L.sc.b := by
  have hb := one_le_b L
  have hL := one_le_L L
  obtain ⟨r1, r2, r3, r4, r5, -, -⟩ := ranks D
  have hη : L.etaSz ≤ L.sc.b := by
    refine P.eta_le.trans (div_le_self (by linarith) ?_)
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 (by linarith)) h2
  refine ⟨?_, hη, P.t_le_eta.trans hη⟩
  have hS := L.Sc_pos
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hden : (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have h1 : (0 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (by linarith)
    have h3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)) :=
      le_mul_of_one_le_right (by linarith) h2
    rw [← mul_assoc] at h3
    linarith
  have hle : LevelStarExponents.lStar L ≤ L.sc.b := by
    unfold LevelStarExponents.lStar
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < LevelStarExponents.lStar L := by
    unfold LevelStarExponents.lStar
    exact div_pos (by nlinarith) (by linarith)
  have h1 := P.lstar1
  have hb' : 0 < L.sc.b' := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have h2 : 0 ≤ L.sc.b / LevelStarExponents.lStar L := by positivity
  have h3 := L.etaSz_pos
  linarith

theorem factorization_condN (H : D7) {l : ℕ} (hs : l ∈ H.host.small) :
    H.host.condN.factorization l = H.host.QS.factorization l := by
  have h := Nat.mem_primeFactors.1 hs
  have e : H.host.condN = H.host.QS * (H.host.q * H.host.d) := mul_assoc _ _ _
  rw [e, Nat.factorization_eq_of_coprime_left H.host.QS_coprime (Nat.mem_primeFactorsList'.2 h)]

theorem s0_eq (i : D.nd.Loc) (hs : D.nd.l i ∈ D.host.small) (h2 : D.nd.l i ≠ 2) :
    D.nd.s0 i = max 1 (D.host.condN.factorization (D.nd.l i)) := by
  rw [D.nd.restNLevelExponent_of_odd i h2, factorization_condN D hs]

end UpperTheory.N.Num

end
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.ThreeHost
section
open NumberField Formalism Formalism.BasicNotions

namespace UpperTheory.N

theorem three_ne_q (D : D7) : 3 ≠ D.host.q ∧ 3 ≠ D.host.d := by
  obtain ⟨_, _, _, hd, _⟩ := D.host.hyp
  refine ⟨fun h => D.host.q_ne_three h.symm, fun h => ?_⟩
  omega

theorem three_ne_g (D : D7) (k : Fin 2) : 3 ≠ D.host.g k := by
  intro h
  have hc := D.ntypes.g_cond k
  rw [← h] at hc
  obtain ⟨_, _, hq, hd, _⟩ := D.host.hyp
  have hq3 := D.host.q_ne_three
  have hS : 1 ≤ D.host.QS := D.host.QS_pos
  have h1 : 11 ≤ D.host.q := by omega
  have h2 : 1 ≤ D.host.d := by omega
  have hM : 3 < D.host.QS * D.host.q * D.host.d :=
    calc 3 < 1 * 11 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hS h1) h2
  rw [Nat.mod_eq_of_lt hM] at hc
  omega

end UpperTheory.N
end

