module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfPlace
section
namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

theorem thr_plus3 (c0 Cc R X N A : ℝ) (hc : max (4 * c0) 0 ≤ Cc) (hR : 0 ≤ R) (hX : 1 ≤ X) (hN : 0 ≤ N)
    (hA : Cc * R * (N * X ^ 2 + X ^ 3) ≤ A) : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ A := by
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hY : 0 ≤ N * X ^ 2 + X ^ 3 := by positivity
  have hle : (N + 3) * X ^ 2 + X ^ 3 ≤ 4 * (N * X ^ 2 + X ^ 3) := by nlinarith
  have hY' : 0 ≤ (N + 3) * X ^ 2 + X ^ 3 := by positivity
  have h0 : 0 ≤ Cc := le_trans (le_max_right _ _) hc
  have h4 : 4 * c0 ≤ Cc := le_trans (le_max_left _ _) hc
  refine le_trans ?_ hA
  rcases le_or_gt c0 0 with hc0 | hc0
  · have : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0 hR) hY'
    exact le_trans this (by positivity)
  · calc c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ c0 * R * (4 * (N * X ^ 2 + X ^ 3)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * c0) * R * (N * X ^ 2 + X ^ 3) := by ring
      _ ≤ Cc * R * (N * X ^ 2 + X ^ 3) := by gcongr

theorem bound_absorb (K C M y a b : ℝ) (_hM : 0 ≤ M) (hy : 0 ≤ y) (_hb : 0 ≤ b) (hK : 0 ≤ K)
    (ha : a ≤ C * y) (hyM : y ≤ M * b) : K * a ≤ (K * |C| * M) * b := by
  have h1 : C * y ≤ |C| * (M * b) := le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hy)
    (mul_le_mul_of_nonneg_left hyM (abs_nonneg C))
  calc K * a ≤ K * (|C| * (M * b)) := mul_le_mul_of_nonneg_left (le_trans ha h1) hK
    _ = (K * |C| * M) * b := by ring

def DecayUnifOfPlace : Prop :=
  P5.ThmPActualCpt → KB.RadHead → KB.HeadTop → Formalism.FourierDecayAlt.P.PBO.DecayUnif → Formalism.FourierDecayAlt.P.PBASM.DecayUnif

theorem decayUnif_of_place (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop)
    (hD : Formalism.FourierDecayAlt.P.PBO.DecayUnif) : Formalism.FourierDecayAlt.P.PBASM.DecayUnif := by
  have hPS : PStdC := pStdC_of hP hRH hHT
  intro Cb
  obtain ⟨c0, hc0⟩ := hD hP Cb
  obtain ⟨c1, hc1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨max (max (4 * c0) 0) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB v ε hε i hi1 hir a ha h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz'
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hCI : KB.CutInside S := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨w, rfl⟩ := ha
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := cutWord_of_adm S hGo hCI w v
  have hlen : (w.1 v).length ≤ S.Ntop := le_trans (Formalism.FourierDecayAlt.P.PBB.len_le_cnt S w v) w.2.2
  have hR : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 4 := by positivity
  have hX : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
    linarith
  have hNn : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _

  have hcpt : ∀ n, KB.CptCoef (p v).T.base (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n v ε) := by
    intro n
    refine ((hc1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop Formalism.FourierDecayAlt.P.PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) (by positivity)
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hloc.1
    have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hloc.2
    have hroom : 10 * ((S.Ntop : ℝ) + 3 * (2 * (S.G.r : ℝ) + 1) + 1) ≤ S.cutHi v - S.cutLo v := by
      have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
        unfold C.HidaSetting.Ntop C.Kst; push_cast; ring
      have h6 := (hGo v).1
      have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have hN20 : (20 : ℝ) ≤ S.Ntop := by rw [hN]; linarith
      have hsq : (400 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 := by nlinarith
      have hN3 : (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 3 := by
        calc (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 2 * S.Ntop := mul_le_mul_of_nonneg_right hsq hNn
          _ = (S.Ntop : ℝ) ^ 3 := by ring
      nlinarith
    obtain ⟨C, hC⟩ := hc0 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop
      Formalism.FourierDecayAlt.P.PBASM.cutN (S.cutLo v) (S.cutHi v) (by rw [hl0]; exact hInD) hcut hε hCk hCC
      (by
        have := thr_plus3 c0 (max (max (4 * c0) 0) c1) (((S.G.r : ℝ) + 1) ^ 4) (2 * (S.G.r : ℝ) + S.G.k + 1)
          S.Ntop A₀ (le_max_left _ _) hR hX hNn (by simpa [mul_assoc] using hA)
        push_cast
        linarith [this])
      (fun n g => rfl) (fun Y h1 h2 => by rw [hl0]; exact hCI v Y ⟨h1, h2⟩) (by push_cast; linarith [hroom])
      j hj (w.1 v) (by rw [hl0]; exact hw) hlen (stdS S h) (stdS S h') hH hH'
    set lam := lamS S j with hlam
    have hlam_pos : 0 < lam := lamS_pos S hgpos j
    set tw : ℝ := 2 * Real.pi / ((S.g : ℝ) * lam) with htw
    have htw_pos : 0 < tw := by rw [htw]; positivity
    have hsW : ∀ l : ℂ, ‖sW S j l‖ = tw * ‖l‖ := by
      intro l
      unfold sW
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg htw_pos.le, one_mul]
    set K1 : ℝ := |Kg S j h h'| with hK1
    set K2 : ℝ := abs (Kg S j h h' * |(lamS S j ^ 2)⁻¹|) with hK2
    refine ⟨K1 * |C| * (max 1 lam⁻¹) ^ 3 + K2 * |C| * (max 1 tw⁻¹) ^ 3, fun n => ⟨fun c hc => ?_, fun l => ?_⟩⟩
    · have hb : 0 ≤ ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hb1 := (hC n).1 _ hlc
      rw [gramLoc_setC_app hB _ v ε j hj (w.1 v) h h' hsz hsz' c hc, mul_assoc, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hnl : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnl] at hb1
      have := bound_absorb K1 C ((max 1 lam⁻¹) ^ 3) (((1 + lam * ‖c‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale lam ‖c‖ hlam_pos (norm_nonneg _))
      have h2 : 0 ≤ K2 * |C| * (max 1 tw⁻¹) ^ 3 * ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      calc K1 * _ ≤ (K1 * |C| * (max 1 lam⁻¹) ^ 3) * ((1 + ‖c‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
    · have hb : 0 ≤ ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      have hb1 := (hC n).2 (sW S j l)
      rw [hsW l] at hb1
      rw [int_gramLoc_setC hPS hB _ v ε (hcpt n) j hj (w.1 v) hw l h h' hloc.1 hloc.2, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have := bound_absorb K2 C ((max 1 tw⁻¹) ^ 3) (((1 + tw * ‖l‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale tw ‖l‖ htw_pos (norm_nonneg _))
      have h2 : 0 ≤ K1 * |C| * (max 1 lam⁻¹) ^ 3 * ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      calc K2 * _ ≤ (K2 * |C| * (max 1 tw⁻¹) ^ 3) * ((1 + ‖l‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
  · have hz : ∀ (n : ℕ) (c : ℂ), (setC S p (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro n c
      rw [gramLoc_setC hB, rr_zero_of_not, mul_zero]
      unfold stdS
      rw [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
      rintro ⟨h1, h2⟩
      exact hloc ⟨⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hsz⟩,
        ⟨fun b hb => h2.1 b (List.mem_append_left _ hb), hsz'⟩⟩
    refine ⟨0, fun n => ⟨fun c _ => ?_, fun l => ?_⟩⟩
    · rw [hz n c]; simp
    · simp [hz n]

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_place : Formalism.FourierDecayAlt.P.StandardPairingDecay.DecayUnifOfPlace :=
  fun hP hRH hHT hD => Formalism.FourierDecayAlt.P.StandardPairingDecay.decayUnif_of_place hP hRH hHT hD
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffFormOf
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def OnOldBound : Prop :=
  ∀ (k ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (ys : List ℝ) (A : ℝ)
      (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (KB.onOld (PBO.mDiff Bs σ w) ys x e) (K * ‖σ‖ ^ 3 * c)

theorem plusW_length (ys : List ℝ) (w : List C.Letter) : (KB.plusW ys w).length = ys.length + w.length := by
  rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]
  simp

theorem waveDiffForm_of (hO : OnOldBound) : PBO.WaveDiffForm := by
  intro _hP Cb
  obtain ⟨Cs, hCs0, hSQ⟩ := Formalism.FourierDecayAlt.P.PBE.sliceQ
  refine ⟨2 * Cs + 2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut _hInD hχ hε hf hfA hA hcut j hj w hw hwN h hh ys hys hcw
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N₂ : ℕ := 2 * N + 6 with hN₂
  set R : ℝ := ((P.r : ℝ) + 1) ^ 4 with hRdef
  have hR1 : 1 ≤ R := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  set n0 : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn0
  have hn01 : 1 ≤ n0 := by
    have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    rw [hn0]; linarith
  set X : ℝ := ((N + 3 : ℕ) : ℝ) * n0 ^ 2 + n0 ^ 3 with hXdef
  have hX1 : 1 ≤ X := by
    have h1 : 1 ≤ n0 ^ 3 := one_le_pow₀ hn01
    have : 0 ≤ ((N + 3 : ℕ) : ℝ) * n0 ^ 2 := by positivity
    rw [hXdef]; linarith
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * ((N₂ : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - 1 := by
    have hX2 : (N₂ : ℝ) * n0 ^ 2 + n0 ^ 3 ≤ 2 * X := by
      rw [hXdef, hN₂]
      push_cast
      have : 0 ≤ n0 ^ 3 := by positivity
      nlinarith
    have hRX : 1 ≤ R * X := by nlinarith
    have h0 : (2 * Cs + 2) * R * X ≤ A := hA
    calc Cs * R * ((N₂ : ℝ) * n0 ^ 2 + n0 ^ 3) ≤ Cs * R * (2 * X) :=
          mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ = (2 * Cs + 2) * R * X - 2 * (R * X) := by ring
      _ ≤ A - 1 := by linarith
  set MM := 3 * (11 * (N₂ * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hMM
  obtain ⟨bf, hbf⟩ := hfA MM
  have hbf0 : 0 ≤ bf := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) MM f bf := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) MM
  have hψ : ∀ n : ℕ, B.CCle (A - 1) MM (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g)
      (Kp * bf / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, Formalism.FourierDecayAlt.P.PBE.cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) MM (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hbf' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add hf (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  set w' := KB.plusW ys w with hw'
  have hw'len : w'.length ≤ N + 3 := by rw [hw', plusW_length]; omega
  have hN₂w : w'.length ≤ N₂ := by omega
  have hc : P.r - j = P.r - D.ptSize h := by rw [hh.2]
  have hQ := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N₂ P rfl rfl hk2 hχ hA' ε hε j hj w' hN₂w h hc hh e
  choose εa Ka hεa hKa hQ1 _hQ2 using hQ
  set KK : ℝ := ∑ e, Ka e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := fun e =>
    Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun e _ => hKa e
  set cs : ℝ := KK * (bf + Kp * bf) with hcs
  have hcs0 : 0 ≤ cs := by positivity
  have hsl : ∀ n e, B.CCle (P5.Auser P N₂ + 1) (P5.mmUser P N₂) (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs := by
    intro n e
    obtain ⟨-, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
    exact Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKa' e) (by positivity))
  have hxs : ∀ n, KB.slv p.T (D.cutF p.T.base χ (hn n) ε) j hj w' h hh.2 =
      Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) := fun n => rfl
  set mo : ℕ := 5 + (2 * (P.r - j) + P.k + 1) * w'.length with hmo
  obtain ⟨K3, hK30, hK3⟩ := hO P.k (P.r - j) Wp Wq (p.T.bs j) w mo
  set Af : ℝ := P5.Auser P w'.length + 1 with hAf
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' Af le_rfl
  have hq : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) ≤ n0 := by
    rw [hn0]
    have : P.r - j ≤ P.r := Nat.sub_le _ _
    have : ((P.r - j : ℕ) : ℝ) ≤ P.r := by exact_mod_cast this
    push_cast
    linarith
  have hL : (w'.length : ℝ) ≤ (N : ℝ) + 3 := by exact_mod_cast hw'len
  have hdec : Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ) ≤ P5.Auser P N₂ + 1 := by
    have hmo' : ((mo + 1 : ℕ) : ℝ) = 6 + ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) := by
      rw [hmo]; push_cast; ring
    have hnV : ((P5.nV P : ℕ) : ℝ) = n0 := by rw [hn0]; unfold P5.nV; push_cast; ring
    have hR3 : 1 ≤ ((P.r : ℝ) + 1) ^ 3 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
    have hdiff : P5.Auser P N₂ - P5.Auser P w'.length =
        127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by
      unfold P5.Auser; rw [hnV]; ring
    have hgap : (N : ℝ) + 3 ≤ (N₂ : ℝ) - w'.length := by rw [hN₂]; push_cast; linarith
    have hN3 : (3 : ℝ) ≤ (N : ℝ) + 3 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    have h1 : 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ P5.Auser P N₂ - P5.Auser P w'.length := by
      rw [hdiff]
      have hb : n0 ^ 2 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      have hpos : 0 ≤ n0 ^ 2 * ((N : ℝ) + 3) := by positivity
      have hY : 0 ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) := le_trans hpos hb
      have hR : n0 ^ 2 * ((N₂ : ℝ) - w'.length) ≤ ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) :=
        le_mul_of_one_le_left hY hR3
      calc 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ 127 * (((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length))) := by
            linarith
        _ = 127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by ring
    have h2 : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) ≤ n0 * ((N : ℝ) + 3) :=
      mul_le_mul hq hL (Nat.cast_nonneg _) (by linarith)
    have ha3 : 3 ≤ n0 * ((N : ℝ) + 3) := by
      calc (3 : ℝ) ≤ (N : ℝ) + 3 := hN3
        _ = 1 * ((N : ℝ) + 3) := by ring
        _ ≤ n0 * ((N : ℝ) + 3) := mul_le_mul_of_nonneg_right hn01 (by linarith)
    have hb2 : n0 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N : ℝ) + 3) := by
      have e : n0 ^ 2 * ((N : ℝ) + 3) = n0 * (n0 * ((N : ℝ) + 3)) := by ring
      rw [e]
      exact le_mul_of_one_le_left (by linarith) hn01
    have h3 : 3 * (n0 * ((N : ℝ) + 3)) + 17 ≤ 127 * (n0 ^ 2 * ((N : ℝ) + 3)) := by linarith
    rw [hAf, hmo']
    linarith
  have hord : mo ≤ P5.mmUser P N₂ := by
    have h1 : 2 * (P.r - j) + P.k + 1 ≤ P5.nV P := by unfold P5.nV; omega
    have h2 : w'.length ≤ 3 * (P.r + 1) * (N₂ + 2) := by
      have : N + 3 ≤ 3 * (P.r + 1) * (N₂ + 2) := by
        have : 1 ≤ 3 * (P.r + 1) := by omega
        nlinarith
      omega
    have h3 : (2 * (P.r - j) + P.k + 1) * w'.length ≤ P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) :=
      Nat.mul_le_mul h1 h2
    have e : P5.mmUser P N₂ = 5 + 3 * (P.r + 1) * (N₂ + 2) * P5.nV P + N₂ * P.r := rfl
    have e2 : P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) = 3 * (P.r + 1) * (N₂ + 2) * P5.nV P := by ring
    rw [e, hmo]
    rw [e2] at h3
    exact le_trans (Nat.add_le_add_left h3 5) (Nat.le_add_right _ _)
  refine ⟨Cf * (K3 * cs) * (K3 * cs), fun n σ hσ => ?_⟩
  rw [hFn n, hxs n]
  have hx : ∀ e, B.CCle (Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ)) mo (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs :=
    fun e => Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hdec (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hord (hsl n e))
  have hu := hK3 σ hσ ys (Af - 1) _ cs hx
  have hv : ∀ e, B.CCle (Af - 1 - 2 * (w'.length : ℝ)) 5
      (KB.onOld (PBO.mDiff (p.T.bs j) σ w) ys (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n)) e)
      (K3 * ‖σ‖ ^ 3 * cs) := fun e =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ w'.length := Nat.cast_nonneg _; linarith)
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by rw [hmo]; omega) (hu e))
  have hb := hCf _ _ _ _ hu hv
  show ‖D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' _ _‖ ≤ _
  refine hb.trans (le_of_eq ?_)
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLSubOneCcle
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem waveL_sub_one_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (((PBO.waveL Bs σ w - 1) x) e) (K * ‖σ‖ * c) := by
  have uInv_ccle (A : ℝ) (m : ℕ) (σ : ℂ) (hσ : ‖σ‖ ≤ 2) :
      ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
        (∀ e, B.CCle A m (x e) c) → ∀ e,
        B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) := by
    intro w
    induction w with
    | nil =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
      simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
      exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
    | cons l w ih =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      have ih0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have ih1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have hs : ‖(if l.1 then σ else (starRingEnd ℂ) σ)‖ = ‖σ‖ := (by cases l.1 <;> simp)
      have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
      have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
      have hlen : (l :: w).length = w.length + 1 := rfl
      have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
      have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
      simp only [KB.uInv]
      by_cases he : e 0 = 0
      · rw [if_pos he]
        have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he]
        refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
        rw [hxe]
        exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
      · rw [if_neg he]
        have he1 : e 0 = 1 := by
          rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
          · exact absurd h he
          · exact h
        have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he1]
        refine ⟨?_, ?_⟩
        · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
            (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
            (by rw [hp]; nlinarith [mul_nonneg h3 hc])
        · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          rw [hxe]
          have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
              (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
              fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
                x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
                (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
            funext g
            simp only [Pi.add_apply, Pi.smul_apply]
            abel
          rw [hf]
          exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])
  obtain ⟨K1, hK1, hmul⟩ := mult_phase (E := Wq →L[ℂ] Wp) m
    (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0))
  refine ⟨(K1 + 1) * 3 ^ w.length, by positivity, ?_⟩
  intro σ hσ A x c hx e
  have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
  have hu := uInv_ccle (A + ((m + 1 : ℕ) : ℝ)) m σ hσ w x c hx e
  have h1 := hmul σ hσ A (KB.uInv σ w x e) (3 ^ w.length * c) hu.1
  have h2 : B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) :=
    BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hu.2
  have h3 := BetaSesquilinearity.CCle_add h1 h2
  have hf : ((PBO.waveL Bs σ w - 1) x) e = fun g =>
      (Complex.exp (PBFV.phaseL σ (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0)) g) - 1) •
        KB.uInv σ w x e g + (KB.uInv σ w x e g - x e g) := by
    funext g
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, PBO.waveL, LinearMap.coe_mk,
      AddHom.coe_mk, KB.waveG]
    rw [PBFV.fsv_dmin_one σ Bs.z Bs.z' g (by omega), sub_smul, one_smul]
    abel
  rw [hf]
  refine JCx2.pd_ccle_mono_c h3 (le_of_eq ?_)
  ring

theorem mDiff_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m ((PBO.mDiff Bs σ w x) e) (K * ‖σ‖ ^ 3 * c) := by
  obtain ⟨K, hK, h1⟩ := waveL_sub_one_ccle Bs w m
  refine ⟨K ^ 3, by positivity, ?_⟩
  intro σ hσ A x c hx
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM
  have hx' : ∀ e, B.CCle ((A + M + M) + M) m (x e) c := fun e => by
    have : (A + M + M) + M = A + 3 * M := by ring
    rw [this]; exact hx e
  have s1 := h1 σ hσ (A + M + M) x c hx'
  have s2 := h1 σ hσ (A + M) _ _ s1
  have s3 := h1 σ hσ A _ _ s2
  intro e
  have he : PBO.mDiff Bs σ w x = (PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) x)) := by
    simp only [PBO.mDiff, pow_succ, pow_zero, one_mul]
    rfl
  rw [he]
  refine JCx2.pd_ccle_mono_c (s3 e) (le_of_eq ?_)
  ring

end one

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

