module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0036

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)


set_option maxHeartbeats 1000000 in
theorem heights (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hLAM : d.HtLAM)
    (hSup : d.HtSup) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl (d.htOf hd h) := by
  obtain ⟨⟨x, hx⟩, ⟨ta', hta'⟩⟩ := d.exists_generic hd h
  choose F hF _hF0 using fun c => d.componentForm_poly hd h c
  have hUP := d.sum_logHeight_upper_bound hd h hLAM F hF
  have hb1 := d.HeightMinMaxFormula hd h hI2be x hx F hF
  obtain ⟨haL, hade0, hade, haG10, haG1, haF0, haF, haG20, haG2⟩ := d.h_six hd h hF1d x hx ta' hta'
  have h7 :
      let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
      let HL := d.Hgt h d.wL (d.wx x)
      let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
      let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
      let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
      let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
      let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
      HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
        d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
          d.D * d.aG h d.G2 d.ta2 * lr := by
    dsimp only
    have hf : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
    have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
    have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
    have hn1pos : (0 : ℝ) < d.n1 := by rw [hn1]; positivity
    have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
    have hla := d.la_part hd h hH1 (d.wx x) hf
    have hsg := d.sg_part hd h hI2be (d.wx x) hf
    have h0 := d.logHeight_section_bound hd h hF1d (d.wx x) hf
    obtain ⟨-, -, hind3, hind4⟩ := d.h_ind hd h hI2be
    have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 :=
      fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
    have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
    have hbdd1 := fun sg => hd.bdd sg _ d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    have hbdd2 := fun sg => hd.bdd sg _ d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    have hint1 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 ((2 : ℕ) • d.G1) (d.ta1 c) (by simp)
      (hd.firstSectionMem c) (hd.firstSectionNeZero c)
    have hint2 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 d.G2 (d.ta2 c) (by simp)
      (hd.secondSectionMem c) (hd.secondSectionNeZero c)
    have h41 := (d.h_four hd h _ d.ta1 hta1 hd.ordDoubleFirstSection_nonneg hbdd1 hint1).1
    have h42 := (d.h_four hd h _ d.ta2 hta2 hd.ordSecondSectionNonneg hbdd2 hint2).1
    obtain ⟨-, -, hsup1, hsup2⟩ := hSup
    have m1 := mul_le_mul_of_nonneg_left hsup1 hdel
    have m2 := mul_le_mul_of_nonneg_left hsup2 hdel
    refine ⟨?_, ?_, ?_⟩
    · have e1 : d.Hgt h d.wL (d.wx x) = (∑ᶠ la, d.NlaG h d.wL (d.wx x) la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.Nsg d.wL (d.wx x)) + d.h0f h d.wL (d.wx x) := rfl
      have e2 : d.HgtMM h (d.wx x) = (∑ᶠ la, d.NlaMM h (d.wx x) la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM (d.wx x)) + d.mahlerMeasureHeight h (d.wx x) := rfl
      have e3 : d.Hgt h (d.n1 • d.wde) d.et = (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.Nsg (d.n1 • d.wde) d.et) + d.h0f h (d.n1 • d.wde) d.et := rfl
      have hla' := div_le_div_of_nonneg_right hla hK.le
      rw [add_div, add_div, mul_div_assoc, mul_div_assoc] at hla'
      have eH : d.cc * d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1) =
          d.cc / d.i * d.Hgt h (d.n1 • d.wde) d.et := by
        rw [hn1]; field_simp
      have eA : d.D * d.cc * d.g0 * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
          (Real.log (d.N + 1 : ℕ) + 1 / 2) =
          d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
        rw [hn1]; field_simp
      rw [e1, e2, eH, eA, e3]
      nlinarith [hla', hsg, h0]
    · have hd3 := hind3 x hx
      have eq : d.Hgt h (d.n1 • d.wde) d.et / d.n1 =
          d.Hgt h d.wL (d.wx x) - d.Hgt h ((2 : ℕ) • d.G1) d.ta1 / 2 := by
        rw [div_eq_iff hn1pos.ne']
        linarith
      rw [eq]
      linarith [h41, m1]
    · have hd4 := hind4 x ta' hx hta'
      linarith [h42, m2]
  have hdi :
      let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
      (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
      (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
      2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
        d.del * Real.log d.del +
          2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
          2 * d.D * d.aG h d.wF ta' * lr + 2 * d.Hgt h d.wF ta' ∧
      (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite ∧
      ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
        d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) * lr) +
          d.del * d.Pet := by
    intro lr
    obtain ⟨h1, h2, h3, h4⟩ := d.disc_one hd h hI2et hI2be ta' hta'
    obtain ⟨h5, h6⟩ := d.nl_nonneg_fin hd h
    exact ⟨h1, h2, h3, h4, h5, h6, d.disc_two hd h hI2et hI2be⟩
  dsimp only at h7 hdi
  obtain ⟨h7a, h7b, h7c⟩ := h7
  obtain ⟨hplf, hIla, hIf, hdi1, hN0, hNf, hdn⟩ := hdi
  obtain ⟨hPN, hPQ, hPP0, hPP0', hPd, hGc, hPI4, hPet, hP14, hP16, hPrw, hPO⟩ := hd.P_ge
  have hn1 : (0 : ℝ) < d.n1 := by
    have h1 := hd.i_ge; have h2 := hd.g_zero_ge_ask_sum
    have : 0 < d.n1 := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hL := hd.size_L
  have hlog0 : 0 ≤ Real.log ((d.N + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos _)
  have hrw := hd.rw_le
  have hlr : Real.log ((d.N + 1 : ℕ) : ℝ) + 1 / 2 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hlw1 : Real.log ((d.N + 1 : ℕ) : ℝ) + 1 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hharm : (harmonic d.N : ℝ) ≤ Real.log ((d.N + 1 : ℕ) : ℝ) + 1 := by
    have h1 := harmonic_le_one_add_log d.N
    rcases Nat.eq_zero_or_pos d.N with h0 | hpos
    · simp [h0]
    · have : Real.log (d.N : ℝ) ≤ Real.log ((d.N + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by push_cast; linarith)
      linarith
  have hhN : (harmonic d.N : ℝ) / 2 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hnu := hH1.2.2.1
  have hlaW := hSup.1
  have arith := heights_arith (d.D : ℝ) (d.del : ℝ) (d.wsize d.wL)
    (Real.log ((d.N + 1 : ℕ) : ℝ) + 1 / 2) (Real.log ((d.N + 1 : ℕ) : ℝ) + 1) (harmonic d.N : ℝ)
    (∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c)) (meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j)))
    ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ)) d.cc (d.g0 : ℝ) (d.i : ℝ) d.DF
    d.PP0' d.PN d.tableLineDegreeFive d.tableLineDegreeTwo d.PI4 d.Prw d.Gc d.Pet
    (d.aG h d.wL (d.wx x) : ℝ) ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1)
    ((d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2) (d.aG h d.wF ta' : ℝ) (d.aG h d.G2 d.ta2 : ℝ)
    (d.HgtMM h (d.wx x)) (d.Hgt h d.wL (d.wx x)) (d.Hgt h (d.n1 • d.wde) d.et / d.n1)
    (d.Hgt h d.wF ta')
    ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ))
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ))
    (∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))))
    (d.del * Real.log d.del)
    (by exact_mod_cast hd.D_ge) (Nat.cast_nonneg _) hL hd.cc_nonneg hd.cc_le hd.ccg0 (Nat.cast_nonneg _)
    (by exact_mod_cast hd.i_ge) ⟨hPP0', hPN, hP14, hP16, hPI4, hPrw, hGc, hPet⟩
    (by linarith) hlr hlw1 hhN hd.DF_le hlaW hnu
    (by simpa [add_assoc] using hUP) hb1
    haL (div_nonneg (by exact_mod_cast hade0) hn1.le) (by rw [div_le_iff₀ hn1]; have := (Int.cast_le (R := ℝ)).mpr hade; push_cast at this; linarith) (div_nonneg (by exact_mod_cast haG10) (by norm_num))
    (by rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; have := (Int.cast_le (R := ℝ)).mpr haG1; push_cast at this; linarith) (by exact_mod_cast haF0)
    (by exact_mod_cast haF) (by exact_mod_cast haG20) (by exact_mod_cast haG2)
    h7a h7b h7c hdi1 hdn
  obtain ⟨ar1, ar2⟩ := arith
  have hsI : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la).Finite :=
    hIf.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have hsN : (Function.support fun la => d.Nl h la * logNorm la).Finite :=
    hNf.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have eI : (fun la => (((d.htOf hd h).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN (d.htOf hd h).K la) =
      fun la => d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ := by
    funext la
    show d.IL h hd.sel hd.a4.choose la * (logNorm la / (Module.finrank ℚ K : ℝ)) = _
    rw [div_eq_mul_inv, ← mul_assoc]
    rfl
  have eN : ∀ la, (d.htOf hd h).Net la = d.Nl h la := by
    intro la
    haveI : ∀ c, Fintype {w // w ∈ d.PlOver la c} := fun c => (hplf la c).fintype
    show (∑ᶠ ζ : (Σ c, {w // w ∈ d.PlOver la c}), ((1 : ℕ) : ℝ) * (d.fze h ζ.1 ζ.2.1 : ℝ) *
      (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)) = _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma]
    unfold Data.Nl
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    simp
  have eNf : (fun la => (d.htOf hd h).Net la * Formalism.MainNotions.Gaps.HeightData.lN (d.htOf hd h).K la) =
      fun la => d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ := by
    funext la
    rw [eN la]
    show d.Nl h la * (logNorm la / (Module.finrank ℚ K : ℝ)) = _
    rw [div_eq_mul_inv, ← mul_assoc]
    rfl
  have hsI' : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la *
      (Module.finrank ℚ K : ℝ)⁻¹).Finite := hsI.subset (Function.support_mul_subset_left _ _)
  have hsN' : (Function.support fun la => d.Nl h la * logNorm la *
      (Module.finrank ℚ K : ℝ)⁻¹).Finite := hsN.subset (Function.support_mul_subset_left _ _)
  have e1 : ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ =
      (∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) * (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [tsum_eq_finsum hsI', ← finsum_mul' _ _ hsI]
  have e2 : ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ =
      (∑ᶠ la, d.Nl h la * logNorm la) * (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [tsum_eq_finsum hsN', ← finsum_mul' _ _ hsN]
  refine ⟨hIla, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [eI]; classical
    exact summable_of_ne_finset_zero (s := hsI'.toFinset) (by intro a ha; by_contra hn; apply ha; exact hsI'.mem_toFinset.mpr hn)
  · rw [eI]
    show 2 * ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ ≤
      (d.del : ℝ) * Real.log (d.del : ℝ) +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        8 / 3 * (d.D : ℝ) * ((d.D : ℝ) + 4) * (d.del : ℝ) * d.Prw * d.wsize d.wL +
        2 * ((d.D : ℝ) + 4) * ((d.D : ℝ) + 1) * (d.del : ℝ) * (2 * d.Gc + 6 * d.PHc) * d.wsize d.wL
    rw [e1]
    have := ar1
    unfold Data.PHc Data.PH
    rw [← div_eq_mul_inv]
    linarith
  · rw [eNf]; classical
    exact summable_of_ne_finset_zero (s := hsN'.toFinset) (by intro a ha; by_contra hn; apply ha; exact hsN'.mem_toFinset.mpr hn)
  · rw [eNf]
    show (∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹) / (d.i : ℝ) ≤
      (d.g0 : ℝ) * (((d.D : ℝ) + 1) * (d.del : ℝ) * (2 * d.Gc + 6 * d.PHc) * d.wsize d.wL +
        4 / 3 * (d.D : ℝ) * (d.del : ℝ) * d.Prw * d.wsize d.wL) + (d.del : ℝ) * d.Pet
    rw [e2]
    have := ar2
    unfold Data.PHc Data.PH
    rw [← div_eq_mul_inv]
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
