module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0175
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowth
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem petInt_mp (γ : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have h := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  convert h using 1
  ext z
  simp

theorem petInt_emb (γ : SL(2, ℤ)) : MeasurableEmbedding (fun z : ℍ => γ • z) := by
  have h := measurableEmbedding_const_smul (α := ℍ) ((γ : GL (Fin 2) ℝ))
  convert h using 1
  ext z
  simp

theorem petInt_fd_meas : MeasurableSet ModularGroup.fd := by
  unfold ModularGroup.fd
  apply IsClosed.measurableSet
  change IsClosed ({z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} ∩ {z : ℍ | |z.re| ≤ 1 / 2})
  apply IsClosed.inter
  · exact isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  · exact isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const

theorem petInt_im_bd (γ : SL(2, ℤ)) (σ : ℍ) (hσ : σ ∈ ModularGroup.fd) :
    (γ • σ).im ≤ 2 * σ.im ∧
      ((γ • σ).im)⁻¹ ≤ (3 * ((γ 1 0 : ℤ) : ℝ) ^ 2 + 8 * ((γ 1 1 : ℤ) : ℝ) ^ 2) * σ.im := by
  have hy : 3 ≤ 4 * σ.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
  have hx : |σ.re| ≤ 1 / 2 := hσ.2
  have hyp : 0 < σ.im := σ.im_pos
  have hx2 : σ.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg σ.re, sq_abs σ.re]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hcd : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 ∨ (((γ 1 0 : ℤ) : ℝ) = 0 ∧ ((γ 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
    by_cases h0 : (γ 1 0 : ℤ) = 0
    · right
      rw [h0, mul_zero, sub_zero, mul_comm] at hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;>
        simp [h0, h]
    · left
      have h1 : (1 : ℤ) ≤ (γ 1 0 : ℤ) ^ 2 := by
        rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
      exact_mod_cast h1
  have hN : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) σ) =
      (((γ 1 0 : ℤ) : ℝ) * σ.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 + (((γ 1 0 : ℤ) : ℝ) * σ.im) ^ 2 := by
    rw [ModularGroup.denom_apply]
    simp [Complex.normSq_apply]
    ring
  rw [ModularGroup.im_smul_eq_div_normSq, hN]
  generalize ((γ 1 0 : ℤ) : ℝ) = c at *
  generalize ((γ 1 1 : ℤ) : ℝ) = d at *
  have hhalf : 1 / 2 ≤ (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by
    rcases hcd with h | ⟨hc, hd⟩
    · nlinarith [sq_nonneg (c * σ.re + d), mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ c ^ 2)]
    · subst hc
      nlinarith
  have hNpos : 0 < (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by linarith
  constructor
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [inv_div, div_le_iff₀ hyp]
    nlinarith [sq_nonneg (c * σ.re - d), mul_le_mul_of_nonneg_left hx2 (sq_nonneg c),
      mul_le_mul_of_nonneg_left hy (sq_nonneg c), mul_le_mul_of_nonneg_left hy (sq_nonneg d)]

theorem petInt_real (k A : ℕ) (r q f t y C C' K δ : ℝ) (hr1 : r ≤ 1) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (ht : 0 < t) (ht1 : t ≤ 2 * y) (ht2 : t⁻¹ ≤ K * y)
    (hdec : q ^ 2 * t ^ k ≤ C * Real.exp (-δ * y)) (hF : f ≤ C' * (t ^ A + (t ^ A)⁻¹)) :
    r * (q * f * t ^ k) ≤ C / 2 * (y ^ 0 * Real.exp (-(δ / 2) * y)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (y ^ (2 * A + k) * Real.exp (-(δ / 2) * y)) := by
  have hy : 0 < y := by linarith
  have hKy : 0 < K * y := lt_of_lt_of_le (inv_pos.mpr ht) ht2
  set E := Real.exp (-(δ / 2) * y) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-δ * y) = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have htk : 0 < t ^ k := pow_pos ht k
  have hS : t ^ A + (t ^ A)⁻¹ ≤ (2 ^ A + K ^ A) * y ^ A := by
    have h1 : t ^ A ≤ (2 * y) ^ A := pow_le_pow_left₀ ht.le ht1 A
    have h2 : (t ^ A)⁻¹ ≤ (K * y) ^ A := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ht2 A
    rw [mul_pow] at h1 h2
    linarith
  have hSpos : 0 ≤ t ^ A + (t ^ A)⁻¹ := by positivity
  have hf' : f ≤ |C'| * ((2 ^ A + K ^ A) * y ^ A) :=
    le_trans hF (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C') hSpos)
      (mul_le_mul_of_nonneg_left hS (abs_nonneg _)))
  have hf2 : f ^ 2 ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
    calc f ^ 2 ≤ (|C'| * ((2 ^ A + K ^ A) * y ^ A)) ^ 2 := pow_le_pow_left₀ hf hf' 2
      _ = (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
        rw [mul_comm 2 A, pow_mul]
        ring
  have htk2 : t ^ k ≤ 2 ^ k * y ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le ht1 k
  have key : 2 * (q * f * t ^ k) * E ≤ (C * E + f ^ 2 * t ^ k * E) * E := by
    rw [hE2] at hdec
    nlinarith [mul_nonneg (sq_nonneg (q - f * E)) htk.le]
  have key2 : 2 * (q * f * t ^ k) ≤ C * E + f ^ 2 * t ^ k * E := le_of_mul_le_mul_right key hEpos
  have hft : f ^ 2 * t ^ k ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) * (2 ^ k * y ^ k) :=
    mul_le_mul hf2 htk2 htk.le (by positivity)
  have hP : 0 ≤ q * f * t ^ k := by positivity
  refine le_trans (mul_le_of_le_one_left hP hr1) ?_
  rw [pow_zero, one_mul, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hft hEpos.le]

theorem integrable_pet_integrand : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  intro k L L' N ε a ρ F hk hL' hN hW hCF hFm hMod
  set g : ℍ → ℂ := fun τ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k) with hg
  have hρ1 : ∀ τ, ρ τ ≤ 1 := by
    intro τ
    have h := le_hasSum (hW.sum τ) 1 (fun j _ => hW.nonneg _)
    simpa using h
  have hqc : Continuous (qs a) := (qs_summable_continuous a hCF.1.1).2
  have hgm : AEStronglyMeasurable g volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hW.meas).aestronglyMeasurable
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hFm) ?_
      · exact (Complex.continuous_conj.comp hqc).aestronglyMeasurable
      · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow k).aestronglyMeasurable
  obtain ⟨S, hS⟩ := hW.supp
  obtain ⟨C', A, hC'⟩ := hMod
  have hsupp : Function.support g ⊆ ⋃ γ ∈ S, {τ : ℍ | γ • τ ∈ ModularGroup.fd} := by
    intro τ hτ
    have hρ : ρ τ ≠ 0 := by
      intro h0
      apply hτ
      simp [hg, h0]
    obtain ⟨γ, hγS, hγ⟩ := hS τ hρ
    exact Set.mem_biUnion hγS hγ
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, integrableOn_finset_iUnion]
  intro γ hγS
  have hpre : (fun σ : ℍ => γ⁻¹ • σ) ⁻¹' {τ : ℍ | γ • τ ∈ ModularGroup.fd} = ModularGroup.fd := by
    ext σ
    simp
  rw [← (petInt_mp γ⁻¹).integrableOn_comp_preimage (petInt_emb γ⁻¹), hpre]
  obtain ⟨C, δ, hδ, hdec⟩ := _root_.GlobalTheory.EisM.cusp_decay k L' N ε a γ⁻¹ hk hL' hN hCF
  set K : ℝ := 3 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 + 8 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℝ) ^ 2 with hK
  refine Integrable.mono' (g := fun σ : ℍ => C / 2 * (σ.im ^ 0 * Real.exp (-(δ / 2) * σ.im)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (σ.im ^ (2 * A + k) * Real.exp (-(δ / 2) * σ.im))) ?_ ?_ ?_
  · exact ((integrableOn_fd_im_pow_mul_exp (δ / 2) 0 (by positivity)).const_mul _).add
      ((integrableOn_fd_im_pow_mul_exp (δ / 2) (2 * A + k) (by positivity)).const_mul _)
  · exact (hgm.comp_measurePreserving (petInt_mp γ⁻¹)).restrict
  · refine (ae_restrict_iff' petInt_fd_meas).mpr (Filter.Eventually.of_forall fun σ hσ => ?_)
    have hy : 1 / 2 ≤ σ.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
      nlinarith [σ.im_pos]
    obtain ⟨hb1, hb2⟩ := petInt_im_bd γ⁻¹ σ hσ
    have ht := (γ⁻¹ • σ).im_pos
    have hn : ‖g (γ⁻¹ • σ)‖ = ρ (γ⁻¹ • σ) * (‖qs a (γ⁻¹ • σ)‖ * ‖F (γ⁻¹ • σ)‖ * (γ⁻¹ • σ).im ^ k) := by
      simp only [hg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
        abs_of_nonneg (hW.nonneg _), abs_of_pos ht]
    rw [Function.comp_apply, hn]
    exact petInt_real k A _ _ _ _ σ.im C C' K δ (hρ1 _) (norm_nonneg _) (norm_nonneg _) ht hb1 hb2
      (hdec σ hy) (hC' _)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAdmissibleSmoothingFactorDividedIndices
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, _root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [_root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simpa only [Finset.prod_apply, sgC] using
    GlobalTheory.SiegDist.sg_distribution c m x (UpperHalfPlane.ofComplex z) hA hm hcm

end GlobalTheory.KZDist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterULevelValStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma ch_periodic_of_dvd {N L : ℕ} (ε : DirichletCharacter ℂ N) (h : N ∣ L) (d : ℤ) :
    ch ε (d + L) = ch ε d := by
  unfold ch
  have : ((L : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff L N).2 h
  rw [Int.cast_add, this, add_zero]

theorem iterU_level_val_stable : ∀ (k N l m : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c a : ℕ → ℂ),
    1 ≤ k → l.Prime → α ≠ 0 → MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) ∧
      (EigF k N l ε t α B c → ∀ r, m ≤ r → val B c l α r a = val B c l α m a) := by
  intro k N l m ε t α B c a hk hl hα ha
  have lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) := by
    intro m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a) := by
        refine _root_.GlobalTheory.Uo_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_
        · exact Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N
        · exact ch_periodic_of_dvd ε (Dvd.intro _ rfl)
        · simpa [pow_succ, mul_assoc] using ha
      rw [Function.iterate_succ_apply]
      exact ih _ hU
  have hb := lev m a ha
  refine ⟨hb, fun hE r hr => ?_⟩
  have per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d := ch_periodic_of_dvd ε (Dvd.intro _ rfl)
  have mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a)) := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (_root_.GlobalTheory.depletion_mf k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1
  have lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]
      ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold val
  rw [add_comm m j, Function.iterate_add_apply, lamj, pow_add]
  have hj : α ^ j ≠ 0 := pow_ne_zero _ hα
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamExtendByZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory


open Classical in
theorem lam_extend_by_zero : ∀ (k L N : ℕ) (χ₀ : DirichletCharacter ℂ N) (B : ℕ) (c : ℕ → ℂ), 0 < L → N ∣ L →
    ∃ (B' : ℕ) (c' : ℕ → ℂ), (∀ a, MF k L (ch χ₀) a → lam B' c' a = lam B c a) ∧
      ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ₀ → MF k L (ch ε) a → lam B' c' a = 0 := by
  intro k L N χ₀ B c hL hN
  have lin := _root_.GlobalTheory.EisM.mf_linear k L
  let Fam : (DirichletCharacter ℂ N → ℕ → ℂ) → Prop := fun a => ∀ ε, MF k L (ch ε) (a ε)
  have uniq : ∀ a b, Fam a → Fam b → (∑ ε, a ε) = ∑ ε, b ε → a = b := by
    intro a b ha hb hab
    have hd : Fam (fun ε => a ε + (-1 : ℂ) • b ε) := fun ε =>
      ((lin (ch ε)).2.1 _ _ (ha ε) ((lin (ch ε)).2.2.1 (-1) _ (hb ε)).1).1
    have h0 := _root_.GlobalTheory.EisM.Indep.forms_of_characters_independent k L N (fun ε => a ε + (-1 : ℂ) • b ε) hL hN hd (by
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hab, neg_one_smul, add_neg_cancel])
    funext ε
    have h1 : a ε + (-1 : ℂ) • b ε = 0 := h0 ε
    rw [neg_one_smul, ← sub_eq_add_neg] at h1
    exact sub_eq_zero.mp h1
  obtain ⟨B₀, hB₀⟩ := _root_.GlobalTheory.EisM.sturm_sum_coef_zero k L N hL hN
  let S : Set (ℕ → ℂ) := {s | ∃ a, Fam a ∧ s = ∑ ε, a ε}
  let rep : (ℕ → ℂ) → DirichletCharacter ℂ N → ℕ → ℂ := fun s => if h : s ∈ S then Classical.choose h else 0
  have rep_spec : ∀ a, Fam a → rep (∑ ε, a ε) = a := by
    intro a ha
    have hs : (∑ ε, a ε) ∈ S := ⟨a, ha, rfl⟩
    simp only [rep, dif_pos hs]
    have h := Classical.choose_spec hs
    exact uniq _ _ h.1 ha h.2.symm
  let φ : (ℕ → ℂ) → ℂ := fun s => lam B c (rep s χ₀)
  have lam_add : ∀ x y : ℕ → ℂ, lam B c (x + y) = lam B c x + lam B c y := by
    intro x y; simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have lam_smul : ∀ (t : ℂ) (x : ℕ → ℂ), lam B c (t • x) = t * lam B c x := by
    intro t x; simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.func_eq_lam S B₀ φ
    ⟨0, fun ε => (lin (ch ε)).1, by simp⟩
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : Fam (a + b) := fun ε => ((lin (ch ε)).2.1 _ _ (ha ε) (hb ε)).1
      have e : (∑ ε, a ε) + ∑ ε, b ε = ∑ ε, (a + b) ε := by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      refine ⟨⟨a + b, hab, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = lam B c (rep _ χ₀) + lam B c (rep _ χ₀)
      rw [e, rep_spec _ hab, rep_spec _ ha, rep_spec _ hb]
      exact lam_add _ _)
    (by
      rintro t _ ⟨a, ha, rfl⟩
      have hta : Fam (t • a) := fun ε => ((lin (ch ε)).2.2.1 t _ (ha ε)).1
      have e : t • ∑ ε, a ε = ∑ ε, (t • a) ε := by
        simp only [Pi.smul_apply, Finset.smul_sum]
      refine ⟨⟨t • a, hta, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = t * lam B c (rep _ χ₀)
      rw [e, rep_spec _ hta, rep_spec _ ha]
      exact lam_smul _ _)
    (by
      rintro _ ⟨a, ha, rfl⟩ h
      exact hB₀ a ha h)
  have single : ∀ (ε₀ : DirichletCharacter ℂ N) (a : ℕ → ℂ), MF k L (ch ε₀) a →
      lam B₀ c' a = lam B c (if ε₀ = χ₀ then a else 0) := by
    intro ε₀ a ha
    let fa : DirichletCharacter ℂ N → ℕ → ℂ := fun ε => if ε = ε₀ then a else 0
    have hfa : Fam fa := by
      intro ε
      by_cases h : ε = ε₀
      · subst h; simp only [fa, if_pos rfl]; exact ha
      · simp only [fa, if_neg h]; exact (lin (ch ε)).1
    have hs : ∑ ε, fa ε = a := by simp [fa]
    have h := hc' _ ⟨fa, hfa, rfl⟩
    simp only [φ] at h
    rw [rep_spec _ hfa, hs] at h
    rw [← h]
    by_cases h' : ε₀ = χ₀
    · subst h'; simp [fa]
    · simp [fa, h', Ne.symm h']
  refine ⟨B₀, c', fun a ha => by simpa using single χ₀ a ha, fun ε a hε ha => ?_⟩
  rw [single ε a ha, if_neg hε]
  simp [lam]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZero
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem siegel_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → siegel T c x ≠ 0 := by
  intro Ω _ _ _ ε T c x hx h0
  have han := _root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c x hx
  rw [h0, map_zero] at han
  have hev : (fun z => sgC c x z) =ᶠ[Filter.codiscreteWithin Hs] (fun _ => (0 : ℂ)) :=
    (Filter.Germ.coe_eq.1 han.symm)
  have hne : ∀ᶠ z in Filter.codiscreteWithin Hs, sgC c x z ≠ 0 := by
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    have hz' : 0 < z.im := hz
    simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact sg_ne_zero c x _ hx
  haveI := codiscreteWithin_Hs_neBot
  obtain ⟨z, h1, h2⟩ := (hev.and hne).exists
  exact h2 h1

end GlobalTheory.KZ
end

