module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0021

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecayHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem flow_coefficient_decay_holds (h1 : UnipotentVectorGroup (E := E)) (h2 : UnipotentLatticeLift (E := E))
    (h3 : FourierCoefficientProperties (E := E)) (h3d : FourierCoefficientSupport (E := E)) (h4 : HolomorphicPeriodicityExtension (E := E)) :
    FlowCoefficientDecay (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS χ z hz hf
  obtain ⟨hH, hxL, hxξ, hxx, hne, hxp0, hua⟩ := hS
  obtain ⟨-, hSS, hξ, -, -, -, -, hw, hχ, hz0, -⟩ := hH
  set u : Fin 2 → Fin r → E := ![ξ, (X.NC : E) • x] with hu
  set e := X.uvec u a with he
  set Q := X.fj la ξ ν P with hQ
  set S1 := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la Q y} with hS1
  have hpair := FlowIsotropicPairs.isIsoPair_of X hξ hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hξ hxL
  obtain ⟨hiso, heξ, hHe, hce⟩ :=
    FlowIsotropicPairs.e_facts X.toData hξ.2.1 hξ.2.2 hxξ hxx hz0.1 e hxp0 hua
  obtain ⟨httv, hTD1⟩ := FlowIsotropicPairs.flow_facts X.toData hz0 e hiso heξ hHe hce hz hf
  have hTdom : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := hTD1.1

  obtain ⟨CP, hCP⟩ := hSS.1.2
  have hQb : ∀ y ∈ X.dom, X.pnorm la Q y ≤ CP := fun y hy =>
    FlowCoefficientBounds.fj_bound X.toData la P CP hCP hξ ν hy
  have hCP0 : 0 ≤ CP :=
    le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz la).le) (hQb z hz)
  have hhat : ∀ y ∈ X.dom, X.hatN la Q y ≤ CP := fun y _ =>
    Real.sSup_le (by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy') hCP0
  have hle_hat : ∀ y ∈ X.dom, X.pnorm la Q y ≤ X.hatN la Q y := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy'⟩ ⟨y, hy, fun τ => rfl, rfl⟩
  have hle_S1 : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la Q y ≤ S1 := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', rfl⟩; exact hhat y' hy'.1⟩ ⟨y, hy, rfl⟩
  have hS10 : 0 ≤ S1 := le_trans (le_trans (mul_nonneg (norm_nonneg _)
    (FlowCoefficientBounds.nfac_pos X.toData hz0.1 la).le) (hle_hat z0 hz0.1)) (hle_S1 z0 hz0)

  obtain ⟨-, hL1⟩ := h1 r X.toData u hpair
  have hT1 : X.pnorm la (X.fz u X.g χ Q) (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    have hb : ∀ b, IsHermFam b → ‖Q (X.Zb u b (X.flowV e (fun _ => -(I / 2)) z))‖ *
        X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
      intro b hb
      obtain ⟨-, -, -, -, -, hnfZ, -, hD1Z, -, -⟩ := hL1 b hb
      have hZ : X.Zb u b (X.flowV e (fun _ => -(I / 2)) z) ∈ X.FramesOverBasis ξ := hD1Z _ hTD1
      rw [← hnfZ la _ hTdom]
      exact (hle_hat _ hZ.1).trans (hle_S1 _ hZ)
    have hpos := FlowCoefficientBounds.nfac_pos X.toData hTdom la
    change ‖X.fz u X.g χ Q (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1
    unfold Data.fz
    split_ifs with h1 h2
    · rw [← le_div_iff₀ hpos]
      have hpt : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ,
          ‖Q (X.Zb u (∑ j, (t j : ℂ) • h2.choose j) (X.flowV e (fun _ => -(I / 2)) z)) *
          cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ ≤
          S1 / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) := by
        intro t
        have hherm : IsHermFam (∑ j, (t j : ℂ) • h2.choose j) := by
          intro τ i k
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
          refine Finset.sum_congr rfl fun j _ => ?_
          obtain ⟨β, hβ, -, he⟩ := h2.choose_spec.1 j
          rw [he]
          simp only [Data.embH]
          rw [← hβ i k, cc, NumberField.IsCMField.complexEmbedding_complexConj]
        have hexp : ‖cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h2.choose j))‖ = 1 := by
          rw [Complex.norm_exp, Real.exp_eq_one_iff]
          simp [Complex.mul_re, Complex.mul_im]
        rw [norm_mul, hexp, mul_one, le_div_iff₀ hpos]
        exact hb _ hherm
      have hvol : MeasureTheory.volume (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1) = 1 := by
        rw [MeasureTheory.volume_pi_pi]
        simp [Real.volume_Icc]
      haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict
          (Set.pi Set.univ fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1)) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
      refine (MeasureTheory.norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans ?_
      rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ, hvol]
      simp
    · simp [hS10]
    · simp [hS10]
  have hRHS : 0 ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hS10

  have hL3d : ∀ y ∈ X.dom, X.fz u X.g χ Q y =
      if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P y else 0 := fun y hy =>
    h3d r X u hpair hmem la P hSS.1.1 hχ ν χ y hy
  by_cases hc : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · have h0 : X.fz u X.g χ Q z = 0 := by rw [hL3d z hz, if_neg hc]
    show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
    rw [h0, norm_zero, zero_mul]
    exact hRHS
  have hGP : ∀ y ∈ X.dom, X.fz u X.g χ Q y = X.fz u X.g χ P y := fun y hy => by
    rw [hL3d y hy, if_pos hc]

  have hper := (h2 r X u hpair hmem).2.1 la P hSS.1.1 hχ
  obtain ⟨⟨hdiff, -, hcov⟩, -, -⟩ :=
    h3 r X.toData u X.g hpair X.g_pos la P hSS.1.1.1 hSS.1.1.2.1 hper χ

  obtain ⟨-, -, -, -, -, -, -, -, -, hRF⟩ := hL1 0 (fun τ i k => by simp)
  have hreal : ∀ s : X.Ψ → ℝ, X.fz u X.g χ P (X.flowV e (fun τ => (s τ : ℂ)) z) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * X.fz u X.g χ P z := by
    intro s
    have hb : IsHermFam (fun τ (i k : Fin 2) => (s τ : ℂ) * a τ i * conj (a τ k)) := by
      intro τ i k
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hRF' : X.flowV e (fun τ => (s τ : ℂ)) z =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) z := hRF a s z
    have hpr : X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) =
        ∑ τ, (X.chiAt χ a τ).re * s τ := by
      unfold Data.pairR Data.chiAt
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have : ∑ i, ∑ k, χ τ i k * ((s τ : ℂ) * a τ i * conj (a τ k)) =
          (s τ : ℂ) * ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [this, Complex.re_ofReal_mul, mul_comm]
    rw [hRF', hcov _ hb z hz, hpr, Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  have hL4 := h4 r X.toData e hiso (X.fz u X.g χ P) hdiff
    (fun τ => ((X.chiAt χ a τ).re : ℂ)) z hz hreal (fun _ => -(I / 2)) hTdom
  have hexp : 4 * (Real.pi : ℂ) * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * -(I / 2) =
      ((2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re : ℝ) : ℂ) := by
    rw [← Finset.sum_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ τ, ((X.chiAt χ a τ).re : ℂ)) * Complex.I_sq
  rw [hexp] at hL4
  have hnorm : ‖X.fz u X.g χ P z‖ = Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
      ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ := by
    rw [hL4, norm_mul, Complex.norm_exp_ofReal, ← mul_assoc, ← Real.exp_add,
      show -Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re) + 2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re = 0 by
        ring, Real.exp_zero, one_mul]

  have hq := m3bNorm_holds r X.toData e hiso la z hz (fun _ => -(I / 2)) hTdom
  have hq2 : X.nfac la z / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤
      ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) := by
    refine hq.2.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => ?_))
    simp only [httv τ]
    norm_num [max_def]
  have hprod : ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) ≤ 2 ^ (w / 2) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← Finset.sum_div]
    linarith
  have hnT := FlowCoefficientBounds.nfac_pos X.toData hTdom la
  have hnf : X.nfac la z ≤ 2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) := by
    rw [div_le_iff₀ hnT] at hq2
    exact hq2.trans (mul_le_mul_of_nonneg_right hprod hnT.le)

  have hT1' : ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
      X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    rw [← hGP _ hTdom]
    exact hT1
  show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
  rw [hGP z hz, hnorm]
  calc Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la z
      ≤ Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          (2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by gcongr
    _ = 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        (‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by ring
    _ ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 := by gcongr

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HCSumRight
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem hC_sum_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, Finset.sum_apply, map_sum, Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ i ∈ s, u a * τ (G a b) * conj (f i b))
      = ∑ a, ∑ i ∈ s, ∑ b, u a * τ (G a b) * conj (f i b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, u a * τ (G a b) * conj (f i b) := Finset.sum_comm

private theorem hermC_add_left_eq_add (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' w : Fin r → ℂ) :
    hermC τ G (u + u') w = hermC τ G u w + hermC τ G u' w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_smul_left_eq_smul_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hermC_finset_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * hermC τ G (v k) w := by
  classical
  induction s using Finset.induction_on
  · simp [hermC]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left_eq_add, hermC_smul_left_eq_smul_mul, ih]

theorem comb_col {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  rw [hermC_finset_sum_smul_left]
  have hab : ∀ a, hermC τ.1 X.Gm (col (mat x0 τ) a) (col (mat x0 τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have h := congrFun (congrFun (ho τ) a) b
    rw [Matrix.diagonal_apply] at h
    exact h
  simp [hab, mul_ite]

private theorem hermC_smul_right_eq_conj_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem comb_comb {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  rw [hC_sum_right']
  simp only [hermC_smul_right_eq_conj_mul, comb_col X ho τ c]
  exact Finset.sum_congr rfl fun a _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def mjip {n : ℕ} (p q : Fin n → ℂ) : ℂ := ∑ i, p i * conj (q i)

lemma mjip_self {n : ℕ} (p : Fin n → ℂ) : mjip p p = ((nsq p : ℝ) : ℂ) := by
  simp only [mjip, nsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

lemma mjip_norm_le {n : ℕ} (p q : Fin n → ℂ) :
    ‖mjip p q‖ ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) := by
  unfold mjip nsq
  calc ‖∑ i, p i * conj (q i)‖ ≤ ∑ i, ‖p i * conj (q i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖p i‖ * ‖q i‖ := by simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma mjip_single {n : ℕ} (p : Fin n → ℂ) (d : Fin n) : mjip p (Pi.single d 1) = p d := by
  unfold mjip
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

lemma mjip_zero_right {n : ℕ} (p : Fin n → ℂ) : mjip p 0 = 0 := by
  simp [mjip]

lemma mjnsq_sub_smul {n : ℕ} (p q : Fin n → ℂ) (t : ℝ) :
    nsq (p - (t : ℂ) • q) = nsq p - 2 * t * (mjip p q).re + t ^ 2 * nsq q := by
  unfold nsq mjip
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def mjpa (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)

def mjpb (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)

lemma nsq_zero' {n : ℕ} : nsq (0 : Fin n → ℂ) = 0 := by
  simp [nsq]

private lemma hermC_fin_sum_smul_left {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (p : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) v = ∑ i, p i * hermC τ G (f i) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

private lemma hermC_fin_sum_smul_right_mul_conj {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (u : Fin r → ℂ)
    (q : Fin n → ℂ) (f : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ j, q j • f j) = ∑ j, hermC τ G u (f j) * conj (q j) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

lemma hermC_bilin (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) (∑ j, q j • f j) =
      ∑ i, ∑ j, p i * hermC τ G (f i) (f j) * conj (q j) := by
  rw [hermC_fin_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_fin_sum_smul_right_mul_conj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma sum_fin_eq_sum_castLE_add_sum_shift {M : Type} [AddCommMonoid M] {p0 n : ℕ} (h : p0 ≤ n) (f : Fin n → M) :
    ∑ i, f i = ∑ a : Fin p0, f (Fin.castLE h a) +
      ∑ m : Fin (n - p0), f ⟨p0 + m, by have := m.isLt; omega⟩ := by
  let e : Fin p0 ⊕ Fin (n - p0) ≃ Fin n := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))
  rw [← e.sum_comp f, Fintype.sum_sum_type]
  congr 1
  all_goals exact Finset.sum_congr rfl fun i _ => congrArg f (Fin.ext (by simp [e]))

lemma hermC_orthonormal_coordinates {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (p q : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ p) (mat x τ *ᵥ q) =
      mjip (mjpa X p) (mjpa X q) - mjip (mjpb X p) (mjpb X q) := by
  have hM : ∀ u : Fin r → ℂ, mat x τ *ᵥ u = ∑ c, u c • col (mat x τ) c := by
    intro u
    ext k
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hij : ∀ i j, hermC τ.1 X.Gm (col (mat x τ) i) (col (mat x τ) j) =
      if i = j then ((sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun (ho τ) i) j
    simpa [gram, Matrix.diagonal_apply] using this
  rw [hM p, hM q, hermC_bilin]
  simp only [hij, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_fin_eq_sum_castLE_add_sum_shift X.p0_le]
  simp only [mjip, mjpa, mjpb, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [sgn, mjpa, a.isLt]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp [sgn, mjpb, nI]

lemma mj_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (c : Fin X.p0) :
    X.colP (X.xZ x Z) τ c = mat x τ *ᵥ col (X.lowBlock Z τ) (Fin.castLE X.p0_le c) := by
  funext k
  rfl

def mjg (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : Fin r → ℂ :=
  ∑ c, δ c • col (X.lowBlock Z τ) (Fin.castLE X.p0_le c)

lemma mjg_pa (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : mjpa X (mjg X Z τ δ) = δ := by
  funext a
  have ha : ¬ (X.p0 ≤ (a : ℕ)) := not_le.2 a.isLt
  simp [mjpa, mjg, Finset.sum_apply, col, Data.lowBlock, ha, Fin.castLE_inj]

lemma mjg_pb (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    mjpb X (mjg X Z τ δ) = Matrix.of (Z τ) *ᵥ δ := by
  funext m
  simp only [mjpb, mjg, nI, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Data.lowBlock, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ¬ ((⟨X.p0 + (m : ℕ), by have := m.isLt; have := X.p0_le; omega⟩ : Fin r) =
      Fin.castLE X.p0_le c) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlt : X.p0 ≤ X.p0 + (m : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := ⟨by omega, by simp⟩
  rw [if_neg hne, dite_eq_left hlt, zero_add, mul_comm]
  congr 2 <;> ext <;> simp

lemma mj_sum_colP (x : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    ∑ c, δ c • X.colP (X.xZ x Z) τ c = mat x τ *ᵥ mjg X Z τ δ := by
  simp only [mj_colP, mjg, Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma mj_coord {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (hy : X.xZ x Z ∈ X.dom)
    (τ : X.Ψ) (w : Fin r → ℂ) : ∃ γ : Fin X.p0 → ℂ,
      X.maj (X.xZ x Z) τ (mat x τ *ᵥ w) =
        2 * (nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) ∧
      ∀ δ, mjip (mjpa X w) δ - mjip (mjpb X w) (Matrix.of (Z τ) *ᵥ δ) =
        mjip γ δ - mjip (Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
  have hG := X.gramPos_posDef hy τ
  have hdet : IsUnit (X.gramPos (X.xZ x Z) τ).det := by open scoped ComplexOrder in exact hG.det_pos.ne'.isUnit
  have hGi : (X.gramPos (X.xZ x Z) τ)⁻¹.IsHermitian := (X.gramPos_isHermitian (X.xZ x Z) τ).inv
  have hconj : ∀ a b, conj ((X.gramPos (X.xZ x Z) τ)⁻¹ b a) = (X.gramPos (X.xZ x Z) τ)⁻¹ a b :=
    fun a b => hGi.apply a b
  obtain ⟨β, hβ⟩ : ∃ β : Fin X.p0 → ℂ, ∀ b, β b =
      hermC τ.1 X.Gm (mat x τ *ᵥ w) (col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le b)) :=
    ⟨_, fun _ => rfl⟩
  have hβ' : ∀ b, β b = hermC τ.1 X.Gm (mat x τ *ᵥ w) (X.colP (X.xZ x Z) τ b) := hβ
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin X.p0 → ℂ, ∀ a, γ a = ∑ b, β b * (X.gramPos (X.xZ x Z) τ)⁻¹ b a :=
    ⟨_, fun _ => rfl⟩
  have K : ∀ c, hermC τ.1 X.Gm (∑ a, γ a • X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c) = β c := by
    intro c
    rw [hermC_fin_sum_smul_left]
    calc ∑ a, γ a * hermC τ.1 X.Gm (X.colP (X.xZ x Z) τ a) (X.colP (X.xZ x Z) τ c)
        = ∑ b, β b * ((X.gramPos (X.xZ x Z) τ)⁻¹ * X.gramPos (X.xZ x Z) τ) b c := by
          simp only [← X.gramPos_apply, hγ, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
      _ = β c := by
          rw [Matrix.nonsing_inv_mul _ hdet, Finset.sum_eq_single c]
          · simp
          · intro b _ hb
            simp [Matrix.one_apply_ne hb]
          · simp
  have P : X.posPart (X.xZ x Z) τ (mat x τ *ᵥ w) = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
    have e3 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ γ)
    simp only [mjg_pa, mjg_pb, mjip_self] at e3
    rw [← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj] at e3
    simp only [K] at e3
    have hre : (∑ c, β c * conj (γ c)).re = nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ) := by
      rw [e3]
      simp
    rw [← hre, Data.posPart]
    congr 1
    simp only [← hβ]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hγ a, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, hconj]
    ring
  refine ⟨γ, ?_, ?_⟩
  · rw [Data.maj, P, hermC_orthonormal_coordinates X ho τ w w, mjip_self, mjip_self]
    simp
  · intro δ
    have e1 := hermC_orthonormal_coordinates X ho τ w (mjg X Z τ δ)
    have e2 := hermC_orthonormal_coordinates X ho τ (mjg X Z τ γ) (mjg X Z τ δ)
    simp only [mjg_pa, mjg_pb] at e1 e2
    rw [← e1, ← e2, ← mj_sum_colP X x Z τ δ, ← mj_sum_colP X x Z τ γ, hermC_fin_sum_smul_right_mul_conj, hermC_fin_sum_smul_right_mul_conj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [K c, hβ']

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem unipotent_lattice_lift : UnipotentLatticeLift (E := E) := by
  intro r X u hu hmem
  exact ⟨fun b hb => X.exists_gamma u hu hmem b hb,
    fun la P hP hχ b hb x hx => X.LZ_periodic u hu hmem la P hP hχ b hb x hx,
    fun χ hχ hf => X.freq_to_beta χ hχ hf⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

