module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeDefectLeOfDividedWeight
section
open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem vdm_cast_eq_range {ι : Type} [Fintype ι] {N : ℕ} (la : ι → Fin N → ℤ) (v : ι → ℕ → ℝ)
    (hv : ∀ τ (i : Fin N), v τ i = la τ i) :
    ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l) := by
  rw [show ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = _ from GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) la]
  unfold GlobalTheory.CompHt.vdm
  refine Finset.prod_congr rfl fun τ _ => ?_
  have lhs : ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ((Int.castRingHom ℝ) (la τ i) - (Int.castRingHom ℝ) (la τ l))
      = ∏ i ∈ Finset.range N, ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)) N]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun l => if (i : ℕ) < l then v τ i - v τ l else 1) N, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext l; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]) fun l _ => ?_
    rw [hv, hv]
    rfl
  have rhs : ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l)
      = ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    have := Finset.mem_range.1 hl
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [lhs, rhs, Finset.prod_comm]

theorem rho_div_le : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv →
    (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H →
    24 * (N : ℝ) * W.T ≤ H →
    (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) →
    GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤
      3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  intro ι _ N W H hW hd hanti hw hH1 hH2 hbar
  have hk := hW.kc_pos
  have hkp := hW.kc_lt
  have hpN := hW.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast hW.weightConst_nonneg
  have hT1 : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast hW.h1
  have hD : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by linarith
  have hMT : M ≤ 5 / 4 * W.T := by linarith
  have hNT : 0 < (N : ℝ) * W.T := mul_pos hN0 hT0
  have hHpos : 0 < H := by linarith
  obtain ⟨g1, hg1⟩ : ∃ g1 : ℝ, g1 = H / (2 * M) := ⟨_, rfl⟩
  have hg : 3 * (N : ℝ) < g1 := by
    rw [hg1, lt_div_iff₀ (by positivity)]
    have : (N : ℝ) * M ≤ N * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hMT hN0.le
    nlinarith
  obtain ⟨U, hU⟩ : ∃ U : ι → ℕ → ℝ, ∀ τ (i : Fin N), U τ i = W.u1 τ i :=
    ⟨fun τ n => if h : n < N then (W.u1 τ ⟨n, h⟩ : ℝ) else 0, fun τ i => by simp [i.2]⟩
  have hU' : ∀ τ (i : Fin N), (if (i : ℕ) < W.p then U τ i else U τ i + 3 * N) = ((W.u' τ i : ℤ) : ℝ) := by
    intro τ i
    rw [hU]
    unfold Wts.u'
    split_ifs <;> push_cast <;> ring

  obtain ⟨a, ha⟩ : ∃ a : Fin N, (a : ℕ) = W.p - 1 := ⟨⟨W.p - 1, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N, (b : ℕ) = W.p := ⟨⟨W.p, hpN⟩, rfl⟩
  have hab : (b : ℕ) = a + 1 := by omega
  have hbarGap : ∀ τ, g1 ≤ (W.u1 τ a : ℝ) - W.u1 τ b := by
    intro τ
    have e := (hd τ).2 a b hab
    rw [if_pos hb] at e
    have hG := hbar τ a b hab hb
    have hMi : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    have h3 := Int.emod_lt_of_pos (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) hMi
    have h4 := Int.mul_ediv_add_emod (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) ((W.T : ℤ) + W.Dd + 1)
    rw [← e] at h4
    have h5 : W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2)) - ((W.T : ℤ) + W.Dd + 1) <
        ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) := by linarith
    have h6 : ((W.u τ a - W.u τ b : ℤ) : ℝ) - W.c0 - 2 * N + 2 - M < M * ((W.u1 τ a : ℝ) - W.u1 τ b) := by
      rw [hM]
      have := (Int.cast_lt (R := ℝ)).2 h5
      push_cast at this ⊢
      linarith
    rw [hg1, div_le_iff₀ (by positivity)]
    have h7 : H ≤ 2 * (M * ((W.u1 τ a : ℝ) - W.u1 τ b)) := by linarith
    linarith
  have hdec : ∀ τ i l, i < l → l < N → U τ l < U τ i := by
    intro τ i l h1 h2
    have := hU τ ⟨i, by omega⟩
    have := hU τ ⟨l, h2⟩
    simp only at *
    have h := hanti τ (show (⟨i, by omega⟩ : Fin N) < ⟨l, h2⟩ from h1)
    have h' : (W.u1 τ ⟨l, h2⟩ : ℝ) < W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast h
    linarith
  have hgap : ∀ τ i l, i < W.p → W.p ≤ l → l < N → g1 ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have m1 : W.u1 τ a ≤ W.u1 τ ⟨i, by omega⟩ := (hanti τ).antitone (show (⟨i, by omega⟩ : Fin N) ≤ a by
      rw [Fin.le_def]; simp only; omega)
    have m2 : W.u1 τ ⟨l, h3⟩ ≤ W.u1 τ b := (hanti τ).antitone (show b ≤ (⟨l, h3⟩ : Fin N) by
      rw [Fin.le_def]; simp only; omega)
    have m1' : (W.u1 τ a : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast m1
    have m2' : (W.u1 τ ⟨l, h3⟩ : ℝ) ≤ W.u1 τ b := by exact_mod_cast m2
    linarith [hbarGap τ]
  have hcl : ∀ τ i l, i < W.kc → W.p ≤ l → l < N → W.w τ / (2 * W.T) ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have c1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hd τ ⟨i, by omega⟩).2.2 h1
    have c1' : (0 : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast c1
    have c2 := ((GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hd τ).1 ⟨l, h3⟩ (by simp only; omega)).1
    linarith
  have L := GlobalTheory.degree_ratio_shift_bound ι N W.p W.kc U (fun _ => g1) W.w (W.T : ℝ) hkp.le hpN.le hT0 hw
    (fun _ => hg) hdec hgap hcl
  dsimp only at L
  obtain ⟨-, -, L3⟩ := L
  unfold GlobalTheory.CompHt.rhoOf
  rw [vdm_cast_eq_range W.u' (fun τ i => if i < W.p then U τ i else U τ i + 3 * N) (fun τ i => hU' τ i),
    vdm_cast_eq_range W.u1 U hU]
  refine L3.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity))
  have hwt := hw τ
  have e : ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) / g1 = ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) * (2 * M) / H := by
    rw [hg1]; field_simp
  rw [e]
  have i1 : ((W.p - W.kc : ℕ) : ℝ) ≤ N := by exact_mod_cast (show W.p - W.kc ≤ N by omega)
  have i2 : ((N - W.p : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - W.p ≤ N by omega)
  have i3 : (W.kc : ℝ) ≤ N := by exact_mod_cast (show W.kc ≤ N by omega)
  gcongr

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.SecWt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb Coeff Level)

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := fun τ τ' h => by
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conjEmb (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

theorem conj_cmHostRoot_ne_self : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro e
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 e
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end

theorem tauE_inj (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_inj {E : Type} [Field E] : Function.Injective (conjEmb (E := E)) := fun a b h => by
  ext x
  exact star_injective (RingHom.congr_fun h x)

theorem wtA_pos {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (tauE D s, n) = ext0 (w.aP s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl, if_neg (hne s s)]; rfl
  · intro t _ ht
    rw [if_neg (fun h => ht (tauE_inj D h).symm), if_neg (hne s t), add_zero]
  · simp

theorem wtA_neg {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (conjEmb (tauE D s), n) = ext0 (w.aM s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_neg (fun h => hne s s (Eq.symm h)), if_pos rfl, zero_add]
  · intro t _ ht
    rw [if_neg (fun h => hne t s (Eq.symm h)), if_neg (fun h => ht (tauE_inj D (conjEmb_inj h)).symm), add_zero]
  · simp

theorem aPl_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n < p) :
    (aPl D i p τ n : ℚ) =
      Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (p - 1 - n) n (by simp only [Ranks.r]; omega)
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) (n + (p - 1 - n)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have hc : ((p - 1 - n : ℕ) : ℚ) = (p : ℚ) - (n + 1) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hl, hc] at h3
  have g := (D.hc τ).gap_be i
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 =
      ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ z1 + z2 - (p - (n + 1)) - (s + 1) := by
    have : (0 : ℚ) ≤ ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aPl
  rw [if_pos hn, hz, Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem aMi_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p q c : ℕ) (hp : p = D.R.k + i) (hq : q = D.R.m - (i + 1))
    (hc : c < q) :
    (aMi D i p q τ (q - 1 - c) : ℚ) =
      -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) c p (by simp only [Ranks.r]; omega)
  have hm : (i : ℕ) + 1 < D.R.m := by omega
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) p = -(D.hc τ).b ⟨i + 1, hm⟩ := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  rw [hl] at h3
  have g := (D.hc τ).gap_eb i hm
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (p + c)
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) =
      ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ -(z2 + z1 + (c + 1) + s) := by
    have : (0 : ℚ) ≤ ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aMi
  rw [if_pos (by omega), show q - (q - 1 - c) = c + 1 by omega, show p + (c + 1) - 1 = p + c by omega, Nat.cast_succ, hz,
    Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem laU_eq_wtCol : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  intro D T _ κ hl ha hκ i σ hσ e he k ρ τ hτ c
  have hlab := (GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ).1 hσ
  have he' := he ρ
  generalize lab σ ρ = s at hlab he' ⊢
  have hrt : ∀ t, tauE D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hl.pins.1.2.2.2
  have hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t) := fun s t h => by
    have h1 := RingHom.congr_fun h (T.Q.H.rt : D.host.E)
    change _ = starRingEnd ℂ (tauE D t _) at h1
    rw [hrt, hrt] at h1
    exact conj_cmHostRoot_ne_self h1.symm
  have hrel : relab T.Q.c (res T σ) (tauE D s) = τ.1 := by
    rw [hτ, ← hlab]
    ext x
    show σ (algebraMap T.Q.c.F D.what₂.LL (embF T.Q.c (tauE D s) x)) = σ (labLL D s x)
    congr 1
    apply D.what₂.embLL.injective
    have h1 := RingHom.congr_fun (res_embLL T ha hl.pins.2.2.1) (embF T.Q.c (tauE D s) x)
    have h2 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau s).1 : D.host.E →+* D.host.E) x)
    exact h1.trans h2.symm
  have hi1 : Function.invFun (relab T.Q.c (res T σ)) τ.1 = tauE D s := by
    rw [← hrel]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hi2 : Function.invFun (relab T.Q.c (res T σ)) (conjEmb τ.1) = conjEmb (tauE D s) := by
    rw [← hrel, ← relab_conjEmb]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hp0 : ((T.U ((i : ℕ) + 1) (res T σ)).X k).p0 = (D.R.sigW ((i : ℕ) + 1)).2 :=
    ((hl.unf _ (inR i) _ hσ).2.1 k).1.trans (hl.pins.2.2.2 _ (inR i)).2.1
  have hs : (Wc D i).sig (tauE D s) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨hP, hM, hn⟩ := hκ i s
  rw [hs] at hP hM
  have hi := i.2
  have hc := c.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hq : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  have hr : D.R.r = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 := by
    rw [hp, hq]; simp only [Ranks.r]; omega
  obtain ⟨N, hN⟩ := (κ i).n_even
  have hN2 : (κ i).n / 2 = N := by omega
  have hNq : (N : ℚ) + N = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
    have : N + N = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
      rw [← hN, hn, ← hr]; rfl
    exact_mod_cast this
  unfold laU wtCol
  rw [hi1, hi2, hp0, hN2, wtA_pos hne, wtA_neg hne, ← sub_eq_iff_eq_add, eq_comm, Int.floor_eq_iff]
  by_cases h : (c : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2
  · have h1 : (D.R.sigW ((i : ℕ) + 1)).2 - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 := by omega
    have h2 := aMi_cast D i s _ _ c hp hq h
    rw [if_pos h, if_neg (not_le.2 h), ext0, dite_eq_left h1, hM]
    push_cast
    rw [h2, he']
    constructor <;> linarith
  · have h1 : (c : ℕ) - (D.R.sigW ((i : ℕ) + 1)).2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
    have h2 := aPl_cast D i s _ _ hp h1
    rw [if_neg h, if_pos (not_lt.1 h), ext0, dite_eq_left h1, hP]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [h2, he']
    constructor <;> linarith

end GlobalTheory.HolRead.SecWt
end
end

