module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
section
noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ApproxUnit

theorem avg_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (u : α → ℂ) (c : ℂ)
    (ε : ℝ) (hb0 : ∀ w, 0 ≤ b w) (hb1 : ∫ w, b w ∂μ = 1) (hum : AEStronglyMeasurable u μ)
    (h : ∀ w, b w ≠ 0 → ‖u w - c‖ ≤ ε) :
    ‖∫ w, u w * (b w : ℂ) ∂μ - c‖ ≤ ε := by
  have hbi : Integrable b μ := by
    by_contra hn
    rw [integral_undef hn] at hb1
    exact zero_ne_one hb1
  have hbc : Integrable (fun w => (b w : ℂ)) μ := hbi.ofReal
  have hpt : ∀ w, ‖(u w - c) * (b w : ℂ)‖ ≤ ε * b w := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 w)]
    by_cases hw : b w = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_right (h w hw) (hb0 w)
  have hd : Integrable (fun w => (u w - c) * (b w : ℂ)) μ :=
    Integrable.mono' (hbi.const_mul ε)
      ((hum.sub aestronglyMeasurable_const).mul hbc.aestronglyMeasurable)
      (Filter.Eventually.of_forall hpt)
  have hc : ∫ w, (b w : ℂ) ∂μ = 1 := by
    rw [integral_complex_ofReal, hb1]
    simp
  have hu : Integrable (fun w => u w * (b w : ℂ)) μ := by
    have := hd.add (hbc.const_mul c)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]
    ring
  have e : ∫ w, u w * (b w : ℂ) ∂μ - c = ∫ w, (u w - c) * (b w : ℂ) ∂μ := by
    have h1 : (fun w => (u w - c) * (b w : ℂ)) = fun w => u w * (b w : ℂ) - c * (b w : ℂ) := by
      ext w
      ring
    rw [h1, integral_sub hu (hbc.const_mul c), integral_const_mul, hc, mul_one]
  rw [e]
  calc ‖∫ w, (u w - c) * (b w : ℂ) ∂μ‖ ≤ ∫ w, ε * b w ∂μ :=
        norm_integral_le_of_norm_le (hbi.const_mul ε) (Filter.Eventually.of_forall hpt)
    _ = ε := by rw [integral_const_mul, hb1, mul_one]

theorem cv_eq_avg (X : Ctx) (φ ψ : X.G → ℂ) (hψ : IsBump X ψ) (g : X.G) :
    cv X.μ φ ψ g = ∫ w, φ (g * w) * ((‖ψ w⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  rw [← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mul_inv_rev, inv_mul_cancel_right]
  rw [← hψ.2.1]

theorem cv_adj_eq_avg (X : Ctx) (f ψ : X.G → ℂ) (hψ : IsBump X ψ) (y : X.G) :
    cv X.μ (adj ψ) f y = ∫ z, f (z⁻¹ * y) * ((‖ψ z⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h : adj ψ z = ((‖ψ z⁻¹‖ : ℝ) : ℂ) := by
    unfold adj
    rw [hψ.2.1 z⁻¹]
    simp
  simp only [h]
  ring

theorem approxU : CvTest → TwoUnif → ApproxU := by
  intro hcv htu X φ ε hφ hε
  letI : Inv (Set X.G) := Set.inv
  obtain ⟨W₀, hW₀, hW⟩ := htu X φ ε hφ hε
  refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
  intro ψ hb hsub y
  have hsupp : ∀ w, ‖ψ w⁻¹‖ ≠ 0 → w ∈ W₀ ∧ w⁻¹ ∈ W₀ := by
    intro w hw
    have h1 : w⁻¹ ∈ tsupport ψ := subset_tsupport _ (norm_ne_zero_iff.1 hw)
    have h2 := hsub h1
    exact ⟨by simpa using h2.2, h2.1⟩
  have hb0 : ∀ w, 0 ≤ ‖ψ w⁻¹‖ := fun w => norm_nonneg _
  have key : ∀ z ∈ W₀, ‖cv X.μ φ ψ (z * y) - φ y‖ ≤ ε := by
    intro z hz
    rw [cv_eq_avg X φ ψ hb]
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun w => φ (z * y * w)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hφ.1.comp (by fun_prop))) ?_
    intro w hw
    exact hW z hz w (hsupp w hw).1 y
  refine ⟨?_, ?_⟩
  · simpa using key 1 (mem_of_mem_nhds hW₀)
  · rw [cv_adj_eq_avg X _ ψ hb]
    have hc : Continuous (cv X.μ φ ψ) := (hcv X φ ψ hφ hb.1).1.1
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun z => cv X.μ φ ψ (z⁻¹ * y)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hc.comp (by fun_prop))) ?_
    intro z hz
    exact key z⁻¹ (hsupp z hz).2

end GlobalTheory.CompanionTheory.ApproxUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DichMod

variable {S : Type} [CommRing S]

theorem isUnit_one_sub_mul {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (w : S) :
    IsUnit (1 - w * ϖ) := by
  have h := Ideal.mem_jacobson_bot.mp hJ (-w)
  have e : ϖ * -w + 1 = 1 - w * ϖ := by ring
  rwa [e] at h

theorem dvd_or_dvd {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) (f : S) :
    ϖ ∣ f ∨ f ∣ ϖ := by
  rcases hc f ϖ with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    exact ⟨c + d * ϖ, by rw [← e]; ring⟩
  · right
    obtain ⟨c, w, e⟩ := Ideal.mem_span_pair.mp h
    have hu := isUnit_one_sub_mul hJ w
    have key : (1 - w * ϖ) * ϖ = c * f := by
      have : c * f = ϖ - w * ϖ ^ 2 := by linear_combination e
      rw [this]; ring
    exact hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)

theorem comparable {ϖ : S}
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) {f g : S}
    (hf : f ∣ ϖ) (hg : g ∣ ϖ) : g ∣ f ∨ f ∣ g := by
  rcases hc f g with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)
  · right
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)

theorem dvd_of_high {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) {f g a b : S} {N : ℕ}
    (e : a * f + b * g = ϖ ^ N) (h : ϖ ^ (N + 1) ∣ f) : g ∣ f := by
  obtain ⟨t, ht⟩ := h
  have hu := isUnit_one_sub_mul hJ (a * t)
  have key : (1 - a * t * ϖ) * ϖ ^ N = b * g := by
    have : b * g = ϖ ^ N - a * f := by linear_combination e
    rw [this, ht]; ring
  have hg : g ∣ ϖ ^ N := hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)
  exact hg.trans ⟨ϖ * t, by rw [ht]; ring⟩

theorem dvd_of_lt {ϖ f g f' g' : S} {i j : ℕ} (hf : f = ϖ ^ i * f') (hg : g = ϖ ^ j * g')
    (hf' : f' ∣ ϖ) (hij : i < j) : f ∣ g := by
  have h1 : f ∣ ϖ ^ (i + 1) := by
    rw [hf, pow_succ]
    exact mul_dvd_mul_left _ hf'
  have h2 : ϖ ^ (i + 1) ∣ g := by
    rw [hg]
    exact (pow_dvd_pow ϖ hij).mul_right g'
  exact h1.trans h2

theorem dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  intro S _ ϖ hJ hc f g hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.mp hN
  have hd := dvd_or_dvd hJ hc
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩
  · exact Or.inl (dvd_of_high hJ e hf)
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩
  · exact Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr (dvd_of_lt hf hg hf' hij)
  · subst hij
    rw [hf, hg]
    rcases comparable hc hf' hg' with h | h
    · exact Or.inl (mul_dvd_mul_left _ h)
    · exact Or.inr (mul_dvd_mul_left _ h)
  · exact Or.inl (dvd_of_lt hg hf hg' hij)

end GlobalTheory.CompanionTheory.DichMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem exists_dividedPowers_map_quotient {S : Type} [CommRing S] (hS : TF (S := S)) (I J : Ideal S)
    (hI : PdI I)
    (hJ : ∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) :
    ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  obtain ⟨δ₀, -, hδ₀⟩ := exists_dividedPowers hS I hI
  have hsub : DividedPowers.IsSubDPIdeal δ₀ (J ⊓ I) :=
    { isSubideal := inf_le_right
      dpow_mem := fun n hn j hj =>
        ⟨hJ j hj.2 hj.1 n hn _ (δ₀.factorial_mul_dpow_eq_pow hj.2),
          δ₀.dpow_mem hn hj.2⟩ }
  refine ⟨DividedPowers.Quotient.dividedPowers δ₀ hsub, rfl, fun k x y hx e => ?_⟩
  rw [DividedPowers.Quotient.dpow_apply δ₀ hsub hx]
  exact congrArg _ (hδ₀ k x y hx e)

end GlobalTheory.CompanionTheory.PdTF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantComponentsOfGerm
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.ComplexSets

variable {σ : Type} [Fintype σ]

theorem exists_equation_not_vanishing {Y Z : Set (σ → ℂ)} {w : σ → ℂ} (hZ : IsAnalyticNear Z w)
    (hYZ : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) :
    ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (∀ᶠ z in 𝓝 w, z ∈ Z → φ z = 0) ∧
      ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 := by
  obtain ⟨N, k, f, hN, hwN, hf, hZN⟩ := hZ
  by_contra hcon
  push_neg at hcon
  apply hYZ
  have hall : ∀ i, ∀ᶠ z in 𝓝 w, z ∈ Y → f i z = 0 := by
    intro i
    apply hcon (f i) (hf i w hwN)
    filter_upwards [hN.mem_nhds hwN] with z hzN hzZ
    have hz : z ∈ Z ∩ N := ⟨hzZ, hzN⟩
    rw [hZN] at hz
    exact hz.2 i
  have hall' : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y → f i z = 0 := Filter.eventually_all.mpr hall
  filter_upwards [hall', hN.mem_nhds hwN] with z hz hzN hzY
  have hz' : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
  rw [← hZN] at hz'
  exact hz'.1

theorem not_eventually_prod_eq_zero {ι : Type} {Y : Set (σ → ℂ)} {w : σ → ℂ}
    (hY : GermIrreducibleAt Y w) (φ : ι → (σ → ℂ) → ℂ) (s : Finset ι)
    (hφ : ∀ j ∈ s, AnalyticAt ℂ (φ j) w)
    (hne : ∀ j ∈ s, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ j z = 0) :
    ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → ∏ j ∈ s, φ j z = 0 := by
  classical
  obtain ⟨hwY, hirr⟩ := hY
  revert hφ hne
  refine Finset.induction_on s ?_ ?_
  · intro _ _ h
    have h0 := h.self_of_nhds hwY
    simp at h0
  · intro a s has ih hφ hne h
    simp_rw [Finset.prod_insert has] at h
    rcases hirr (φ a) (fun z => ∏ j ∈ s, φ j z) (hφ a (Finset.mem_insert_self a s))
        (by simpa only [Finset.prod_fn] using
          Finset.analyticAt_prod s fun j hj => hφ j (Finset.mem_insert_of_mem hj)) h with h1 | h1
    · exact hne a (Finset.mem_insert_self a s) h1
    · exact ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h1

theorem exists_subfamily_no_containment {ι : Type} [Finite ι] (Y : ι → Set (σ → ℂ)) (w : σ → ℂ) :
    ∃ T : Finset ι, (∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let P : Finset ι → Prop := fun T => ∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i
  have hP : P Finset.univ := Filter.Eventually.of_forall fun z => by simp
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩⟩
  rw [Finset.mem_filter] at hT
  refine ⟨T, hT.2, ?_⟩
  intro i hi j hj hij hsub
  have hP' : P (T.erase i) := by
    filter_upwards [hT.2, hsub] with z hz hzs
    rw [hz]
    constructor
    · rintro ⟨m, hm, hzm⟩
      by_cases hmi : m = i
      · rw [hmi] at hzm
        exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hzs hzm⟩
      · exact ⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hzm⟩
    · rintro ⟨m, hm, hzm⟩
      exact ⟨m, Finset.mem_of_mem_erase hm, hzm⟩
  have hle := hmin (T.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
  have hlt := Finset.card_erase_lt_of_mem hi
  omega

theorem dominant_of_open {ι : Type} [Fintype ι] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    {S W : Set (σ → ℂ)} {w : σ → ℂ} (Y : ι → Set (σ → ℂ))
    (hopen : ∀ x ∈ S, ∀ V ∈ 𝓝 x, A '' (S ∩ V) ∈ 𝓝 (A x))
    (hYan : ∀ i, IsAnalyticNear (Y i) w) (hYirr : ∀ i, GermIrreducibleAt (Y i) w)
    (hno : ∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j)
    (hW : W ∈ 𝓝 w) (hS : S ∩ W = (⋃ i, Y i) ∩ W) (i : ι)
    (h : (Fin d → ℂ) → ℂ) (hh : AnalyticAt ℂ h (A w))
    (hv : ∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) :
    ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  classical
  have hsep : ∀ j, ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (j ≠ i →
      (∀ᶠ z in 𝓝 w, z ∈ Y j → φ z = 0) ∧ ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → φ z = 0) := by
    intro j
    by_cases hj : j = i
    · exact ⟨fun _ => 1, analyticAt_const, fun h' => absurd hj h'⟩
    · obtain ⟨φ, h1, h2, h3⟩ := exists_equation_not_vanishing (hYan j) (hno i j (Ne.symm hj))
      exact ⟨φ, h1, fun _ => ⟨h2, h3⟩⟩
  choose φ hφan hφ using hsep
  have hΦan : AnalyticAt ℂ (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) w :=
    by simpa only [Finset.prod_fn] using Finset.analyticAt_prod (Finset.univ.erase i) fun j _ => hφan j
  have hΦne : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → ∏ j ∈ Finset.univ.erase i, φ j z = 0 :=
    not_eventually_prod_eq_zero (hYirr i) φ _ (fun j _ => hφan j)
      (fun j hj => (hφ j (Finset.ne_of_mem_erase hj)).2)
  have hΦY : ∀ᶠ z in 𝓝 w, ∀ j, j ≠ i → z ∈ Y j → ∏ j ∈ Finset.univ.erase i, φ j z = 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun z h' => absurd hj h'
    · filter_upwards [(hφ j hj).1] with z hz _ hzj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hz hzj)
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  have hcont : ∀ᶠ z in 𝓝 w, ContinuousAt (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) z :=
    hΦan.eventually_analyticAt.mono fun z hz => hz.continuousAt
  have hAball : ∀ᶠ z in 𝓝 w, A z ∈ Metric.ball (A w) ε :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hgood := hcont.and (hΦY.and (hv.and (hAball.and (show ∀ᶠ z in 𝓝 w, z ∈ W from hW))))
  have hfreq := Filter.not_eventually.mp hΦne
  obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually hgood.eventually_nhds).exists
  push_neg at hx1
  obtain ⟨hxY, hxΦ⟩ := hx1
  obtain ⟨hxc, -, -, hxA, hxW⟩ := hx2.self_of_nhds
  have hxS : x ∈ S := by
    have hx' : x ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.mpr ⟨i, hxY⟩, hxW⟩
    rw [← hS] at hx'
    exact hx'.1
  have hV := hx2.and (hxc.eventually_ne hxΦ)
  have himg := hopen x hxS _ hV
  have hzero : ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    filter_upwards [himg] with y hy
    obtain ⟨z, ⟨hzS, ⟨⟨-, hzY, hzh, -, hzW⟩, hzΦ⟩⟩, rfl⟩ := hy
    have hz' : z ∈ (⋃ j, Y j) ∩ W := by rw [← hS]; exact ⟨hzS, hzW⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz'.1
    by_cases hji : j = i
    · rw [hji] at hzj
      exact hzh hzj
    · exact absurd (hzY j hji hzj) hzΦ
  have hEq := hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hxA hzero
  filter_upwards [Metric.ball_mem_nhds (A w) hε] with y hy
  exact hEq hy

theorem openProjectionDominantComponents_of_analyticGermComponents :
    AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  intro hAGC
  unfold AnalyticGermComponents.Statement at hAGC
  unfold OpenProjectionDominantComponents.Statement
  intro σ _ X B k f d A hB hf hXB hopen w hw
  have hAN : IsAnalyticNear (X ∩ B) w := by
    unfold IsAnalyticNear
    exact ⟨B, k, f, hB, hw.2, hf, by rw [Set.inter_assoc, Set.inter_self, hXB]⟩
  obtain ⟨n₀, Y₀, hY₀, W, hW, hXW⟩ := hAGC σ (X ∩ B) w hAN hw
  obtain ⟨T, hT, hTno⟩ := exists_subfamily_no_containment Y₀ w
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hno : ∀ i j : Fin T.card, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y₀ (e i) → z ∈ Y₀ (e j) := by
    intro i j hij
    exact hTno _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  have hW' : W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i} ∈ 𝓝 w := Filter.inter_mem hW hT
  have hS : X ∩ B ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) =
      (⋃ i, Y₀ (e i)) ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) := by
    ext z
    constructor
    · rintro ⟨hzXB, hzW, hzT⟩
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := by rw [← hXW]; exact ⟨hzXB, hzW⟩
      obtain ⟨i, hiT, hzi⟩ := hzT.mp h1.1
      refine ⟨Set.mem_iUnion.mpr ⟨e.symm ⟨i, hiT⟩, ?_⟩, hzW, hzT⟩
      simpa using hzi
    · rintro ⟨hzU, hzW, hzT⟩
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := ⟨Set.mem_iUnion.mpr ⟨_, hzi⟩, hzW⟩
      rw [← hXW] at h1
      exact ⟨h1.1, hzW, hzT⟩
  refine ⟨T.card, fun i => Y₀ (e i), fun i => ⟨(hY₀ _).1, (hY₀ _).2, fun h hh hv => ?_⟩, hno,
    _, hW', hS⟩
  exact dominant_of_open A (fun j => Y₀ (e j)) hopen (fun j => (hY₀ _).1) (fun j => (hY₀ _).2)
    hno hW' hS i h hh hv

end GlobalTheory.CompanionTheory.ComplexSets
end

