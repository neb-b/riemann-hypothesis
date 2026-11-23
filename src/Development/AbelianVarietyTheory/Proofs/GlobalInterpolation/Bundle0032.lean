module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0027
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
section
noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne

variable {q : ℕ} [Fact q.Prime]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem momInt_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z * G z) := by
  classical
  have cF := (_root_.GlobalTheory.MomCrit.momInt_iff_norm_mahler_le q ι V κ v F hF).1 mF
  have cG := (_root_.GlobalTheory.MomCrit.momInt_iff_norm_mahler_le q ι V κ v G hG).1 mG
  refine (_root_.GlobalTheory.MomCrit.momInt_iff_norm_mahler_le q ι V κ v _ (hF.mul hG)).2 fun n => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V κ v F G hF hG n, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_one₀ (cF k) (norm_nonneg _) (cG _)

theorem momInt_add (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z + G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mF
  obtain ⟨ν, hν, eν⟩ := mG
  refine ⟨μ + ν, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using μ.le_of_opNorm_le hμ f
    · simpa using ν.le_of_opNorm_le hν f
  · have h : iteratedFDeriv ℂ k (fun z => F z + G z) 0 =
        iteratedFDeriv ℂ k F 0 + iteratedFDeriv ℂ k G 0 :=
      iteratedFDeriv_add_apply (hF.contDiffAt.of_le (by exact_mod_cast le_top))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h, ContinuousMultilinearMap.add_apply, map_add (f := _), eμ k j f hf, eν k j f hf,
      ContinuousLinearMap.add_apply]

theorem momInt_const_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : MomInt ι v G) :
    MomInt ι v (fun z => c * G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mG
  refine ⟨ι c • μ, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.smul_apply, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (μ.le_of_opNorm_le hμ f |>.trans (by simp))
  · have h : iteratedFDeriv ℂ k (fun z => c * G z) 0 = c • iteratedFDeriv ℂ k G 0 := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (a := c) (f := G) (i := k) (x := (0 : V))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
      simpa [Pi.smul_def, smul_eq_mul] using this
    rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul, map_mul, eμ k j f hf,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem latInt_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z * G z) :=
  fun κ _ v hv => momInt_mul ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_add (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z + G z) :=
  fun κ _ v hv => momInt_add ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_const_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => c * G z) :=
  fun κ _ v hv => momInt_const_mul ι _ hG hc (mG κ v hv)

theorem latInt_prod_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ω : ℂ_[q]) (Λ : AddSubgroup V),
    (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∏ j, G j z) ∧
    ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) →
      (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  intro q _ ι V _ _ ω Λ
  classical
  refine ⟨fun m _ G hd hl => ?_, fun m s c G hd hc hl => ?_⟩
  · have key : ∀ s : Finset m, ContDiff ℂ ⊤ (fun z => ∏ j ∈ s, G j z) ∧
        LatInt ι ω Λ (fun z => ∏ j ∈ s, G j z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using ⟨contDiff_const, latInt_one ι ω Λ⟩
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ⟨(hd a).mul ih.1, latInt_mul ι ω Λ (hd a) ih.1 (hl a) ih.2⟩
    exact (key Finset.univ).2
  · have key : ∀ t : Finset m, t ⊆ s → ContDiff ℂ ⊤ (fun z => ∑ j ∈ t, c j * G j z) ∧
        LatInt ι ω Λ (fun z => ∑ j ∈ t, c j * G j z) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        simpa using ⟨contDiff_const, latInt_zero ι ω Λ⟩
      | insert a t ha ih =>
        intro hts
        have hat : a ∈ s := hts (by simp)
        obtain ⟨h1, h2⟩ := ih fun x hx => hts (by simp [hx])
        simp only [Finset.sum_insert ha]
        have h3 : ContDiff ℂ ⊤ (fun z => c a * G a z) := contDiff_const.mul (hd a hat)
        exact ⟨h3.add h1, latInt_add ι ω Λ h3 h1
          (latInt_const_mul ι ω Λ (hd a hat) (hc a hat) (hl a hat)) h2⟩
    exact (key s subset_rfl).2

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
section
open GlobalTheory.MomN

namespace GlobalTheory

theorem mahler_mul_of_disjoint_support :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
      (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T →
      (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) →
      (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) →
      (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧
      (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) →
        GlobalTheory.MomN.mahler u (fun z => F z * H z) N =
          GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
            GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  intro V _ _ ι' _ _ u F H hF hH S T hST hFS hHT
  constructor
  · intro N ⟨p, hp, hNp⟩
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    apply Finset.sum_eq_zero
    intro k _
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_right _ h)
    by_cases hk : k p = 0
    · rw [hHT _ ⟨p, hpT, by simp [hk, hNp]⟩, mul_zero]
    · rw [hFS _ ⟨p, hpS, hk⟩, zero_mul]
  · intro N hN
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    rw [Finset.sum_eq_single (fun p => if p ∈ S then N p else 0)]
    · have hfun : (fun i => N i - (fun p => if p ∈ S then N p else 0) i) =
          (fun p => if p ∈ T then N p else 0) := by
        funext p
        by_cases hS : p ∈ S
        · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
          simp only [hS, hT, if_true, if_false, Nat.sub_self]
        · by_cases hT : p ∈ T
          · simp only [hS, hT, if_true, if_false, Nat.sub_zero]
          · have h0 : N p = 0 := hN p (by simp [hS, hT])
            simp only [hS, hT, if_false, h0, Nat.sub_zero]
      exact congrArg (fun g => GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
        GlobalTheory.MomN.mahler u H g) hfun
    · intro k hk hne
      by_contra hprod
      have h1 : GlobalTheory.MomN.mahler u F k ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : GlobalTheory.MomN.mahler u H (fun i => N i - k i) ≠ 0 := right_ne_zero_of_mul hprod
      apply hne
      funext p
      rw [Fintype.mem_piFinset] at hk
      have hkp : k p ≤ N p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hk p))
      by_cases hS : p ∈ S
      · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
        have : N p - k p = 0 := by
          by_contra h
          exact h2 (hHT _ ⟨p, hT, h⟩)
        simp only [hS, if_true]
        omega
      · simp only [hS, if_false]
        by_contra h
        exact h1 (hFS _ ⟨p, hS, h⟩)
    · intro h
      exfalso
      apply h
      rw [Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range]
      split_ifs <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugeSectionMulBlockCompareStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadricPointGauge_section_mul_block_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptGauge e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptGauge e y + gauge g ≤ t * gauge (a * j g) ∧ gauge (a * j g) ≤ t * (ptGauge e y + gauge g) := by
  first | exact @GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | exact GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | (intros; apply GlobalTheory.SectionGaugeCompare.gauge_section_mul_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivity
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumLamIdealLe
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LamRay

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_nonneg (I : Ideal (𝓞 K)) : 0 ≤ lamIdeal I := by
  unfold lamIdeal
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

theorem pow_prime_norm (hK : Module.finrank ℚ K = 2) {P : Ideal (𝓞 K)} {k : ℕ} (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hk : 1 ≤ k) : IsPrimePow (Ideal.absNorm (P ^ k)) ∧
      P ∣ Ideal.span {((Ideal.absNorm (P ^ k)).minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm P := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, h0⟩
  obtain ⟨p, hp, hm⟩ := GlobalTheory.Mem.FewPrimes.exists_prime_mem v
  have hd : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm P ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact absurd he h1.ne'
  have hik : i * k ≠ 0 := mul_ne_zero hi (by omega)
  rw [map_pow, he, ← pow_mul, hp.pow_minFac hik]
  exact ⟨(isPrimePow_nat_iff _).2 ⟨p, i * k, hp, Nat.pos_of_ne_zero hik, rfl⟩, hd, he ▸ h1⟩

theorem sum_lamIdeal_le (hK : Module.finrank ℚ K = 2) (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ 2 * Λ n := by
  set T := S.filter (fun I => ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) with hT
  have e : ∑ I ∈ S, lamIdeal I = ∑ I ∈ T, Real.log (Ideal.absNorm I.radical) := by
    rw [hT, Finset.sum_filter]
    rfl
  rw [e]
  rcases T.eq_empty_or_nonempty with h | ⟨I₀, hI₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg zero_le_two vonMangoldt_nonneg
  have key : ∀ I ∈ T, IsPrimePow n ∧ I.radical.IsPrime ∧ I.radical ≠ ⊥ ∧
      I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm I.radical ∧ ∃ k, I = I.radical ^ k := by
    intro I hI
    obtain ⟨hIS, P, k, hP, h0, hk, rfl⟩ := Finset.mem_filter.1 hI
    have h := pow_prime_norm hK hP h0 hk
    rw [hS _ hIS] at h
    rw [Ideal.radical_pow _ (by omega), hP.radical]
    exact ⟨h.1, hP, h0, h.2.1, h.2.2, k, rfl⟩
  have hn := (key I₀ hI₀).1
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  have hdvd : ∏ I ∈ T, I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun I hI J hJ hIJ => ?_) (fun I hI => (key I hI).2.2.2.1)
    obtain ⟨-, a1, a2, -, a3, k, a4⟩ := key I hI
    obtain ⟨-, b1, b2, -, -, l, b4⟩ := key J hJ
    refine Ideal.isCoprime_iff_sup_eq.2 ((a1.isMaximal a2).coprime_of_ne (b1.isMaximal b2) fun h => hIJ ?_)
    have c1 := hS I (Finset.mem_filter.1 hI).1
    have c2 := hS J (Finset.mem_filter.1 hJ).1
    rw [a4, map_pow] at c1
    rw [b4, map_pow, ← h] at c2
    have := Nat.pow_right_injective a3 (c1.trans c2.symm)
    rw [a4, b4, ← h, this]
  have h2 : ∏ I ∈ T, Ideal.absNorm I.radical ∣ n.minFac ^ 2 := by
    have := map_dvd Ideal.absNorm hdvd
    rwa [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at this
  have h3 : ((∏ I ∈ T, Ideal.absNorm I.radical : ℕ) : ℝ) ≤ (n.minFac ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.le_of_dvd (pow_pos hp.pos 2) h2)
  have hpos : ∀ I ∈ T, (0 : ℝ) < Ideal.absNorm I.radical := fun I hI =>
    Nat.cast_pos.2 (lt_trans one_pos (key I hI).2.2.2.2.1)
  push_cast at h3
  rw [← Real.log_prod (fun I hI => (hpos I hI).ne'), vonMangoldt_apply, if_pos hn]
  have h4 := Real.log_le_log (Finset.prod_pos hpos) h3
  rw [Real.log_pow] at h4
  exact_mod_cast h4


open QuadraticZeta in
theorem exists_gen {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) : ∃ ω : 𝓞 K, (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  have hsq : Squarefree d := hp.squarefree
  have hD := discr_eq_neg_of_sq_eq h2 hsq hd hr
  obtain ⟨w, bar, hw, -, hgen, hσ, σ, hσr⟩ :=
    ringOfIntegers_sqrt_neg_three_mod_four d hsq hd K h2 r hr
  refine ⟨w, hgen, fun a b => ?_⟩
  have h1 := norm_eq_sq h2 hD σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
  rw [← Algebra.coe_norm_int] at h1
  have h3 : σ (w : K) = (1 + Complex.I * √d) / 2 := by
    have := congrArg σ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hσr] at this
    linear_combination this / 2
  have h4 : σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
      = ((a + b / 2 : ℝ) : ℂ) + ((b * √d / 2 : ℝ) : ℂ) * Complex.I := by
    have h7 : (((a : 𝓞 K) + b * w : 𝓞 K) : K) = a + b * (w : K) := by simp
    rw [h7, map_add (f := _), map_mul, map_intCast, map_intCast, h3]
    push_cast
    ring
  rw [h4, Complex.sq_norm, Complex.normSq_add_mul_I] at h1
  have h5 : √(d : ℝ) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have h6 : ((Algebra.norm ℤ ((a : 𝓞 K) + b * w) : ℤ) : ℝ) * 4
      = (2 * a + b) ^ 2 + d * b ^ 2 := by
    push_cast at h1
    rw [h1]
    linear_combination (b : ℝ) ^ 2 * h5
  exact_mod_cast h6

theorem normOne_span {d M : ℕ} {ω : 𝓞 K} (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    GlobalTheory.Mem.An.NormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * ω := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  have h0 : 0 ≤ Algebra.norm ℤ π := by
    have : 0 ≤ (2 * (1 + (M : ℤ) * a) + M * b) ^ 2 + d * ((M : ℤ) * b) ^ 2 := by positivity
    linarith
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, Dvd.intro _ rfl, ⟨a, by ring⟩⟩
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg h0]
  linarith

theorem finite_idealsIn {M : ℕ} (D : RayData K M) (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

theorem lamRay_props : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, (∀ g n, 0 ≤ lamRay D g n) ∧ (∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) ∧ ∀ p : ℕ, p.Prime → lamRay D 1 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro K _ _ d M x hp hd _ hx hK _ D
  refine ⟨fun g n => ?_, fun n => ?_, fun p _ h => ?_⟩
  · exact finsum_nonneg fun I => finsum_nonneg fun _ => lamIdeal_nonneg I
  · have e : ∀ g, lamRay D g n = ∑ I ∈ (finite_idealsIn D g n).toFinset, lamIdeal I := fun g =>
      finsum_mem_eq_finite_toFinset_sum _ _
    simp only [e]
    rw [← Finset.sum_biUnion]
    · refine sum_lamIdeal_le hK n _ fun I hI => ?_
      obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hI
      exact ((Set.Finite.mem_toFinset _).1 hg).2.2.1
    · intro g _ g' _ hgg
      refine Finset.disjoint_left.2 fun I h1 h2 => hgg ?_
      exact ((Set.Finite.mem_toFinset _).1 h1).2.2.2.symm.trans ((Set.Finite.mem_toFinset _).1 h2).2.2.2
  · have hne : (idealsIn D 1 p).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      apply h
      unfold lamRay
      rw [h0, finsum_mem_empty]
    obtain ⟨I, h0, hc, hN, hcl⟩ := hne
    obtain ⟨a, b, ha, -, ha1, hb1, hab⟩ := (D.cls_eq_one_iff hc h0).1 hcl
    have hb : b ∈ Ideal.span {a} := by
      have : Ideal.span {b} ≤ Ideal.span {a} := hab ▸ Ideal.mul_le_left
      exact this (Ideal.mem_span_singleton_self b)
    obtain ⟨π, rfl⟩ := Ideal.mem_span_singleton.1 hb
    rw [← Ideal.span_singleton_mul_span_singleton] at hab
    have hI : I = Ideal.span {π} :=
      mul_left_cancel₀ (by simpa [Ideal.span_singleton_eq_bot] using ha) hab
    have hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have : π - 1 = (a * π - 1) - π * (a - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ hb1 (Ideal.mul_mem_left _ _ ha1)
    obtain ⟨ω, hgen, hnorm⟩ := exists_gen hp hd hx hK
    rw [← hN, hI]
    exact normOne_span hgen hnorm hπ

end GlobalTheory.Hk.LamRay
end

