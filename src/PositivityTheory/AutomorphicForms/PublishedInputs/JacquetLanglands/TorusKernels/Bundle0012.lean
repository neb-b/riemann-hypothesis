module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFhyp
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HyperbolicTermsContribution

open UpperTheory.Esk

theorem vecMul_ne {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) (δ : GL (Fin 2) F) : s ᵥ* δ.val ≠ 0 := by
  intro h
  apply hs
  have h2 := congrArg (fun v => v ᵥ* (δ⁻¹ : GL (Fin 2) F).val) h
  simpa [Matrix.vecMul_vecMul] using h2

theorem isEll_conj {F : Type} [Field F]
    (hfix : ∀ (s : Fin 2 → F) (γ δ : GL (Fin 2) F), Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔
      ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val)) (g γ : PG F) :
    IsEll (g * γ * g⁻¹) ↔ IsEll γ := by
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective γ
  have h1 : ∀ s : Fin 2 → F, Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
    intro s
    have := hfix s γ 1
    simpa using this
  constructor
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (h1 s).1 hf
    have hs' : s ᵥ* (δ⁻¹ : GL (Fin 2) F).val ≠ 0 := vecMul_ne s hs _
    apply h _ hs'
    rw [hfix]
    refine ⟨c, ?_⟩
    have e : (s ᵥ* (δ⁻¹ : GL (Fin 2) F).val) ᵥ* δ.val = s := by
      rw [Matrix.vecMul_vecMul]; simp
    rw [e, hc]
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (hfix s γ δ).1 hf
    exact h _ (vecMul_ne s hs δ) ((h1 _).2 ⟨c, hc⟩)

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

open scoped Classical in
open Classical in
def uT (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) : ℂ :=
  if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y

theorem enorm_uT_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖uT D k a T γ y‖ₑ ≤ ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ := by
  unfold uT
  split_ifs <;> simp

theorem enorm_ind_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ ≤ ‖D.kk k a γ y‖ₑ := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

open scoped Classical in
open Classical in
theorem fhyp (hC4 : C4) (hE0a : E0a) (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hE2 : E2) (hE3 : E3) (hEcut : Ecut)
    (hFsum : Fsum) (hF5 : F5) (hF6 : F6) (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a)
    (b : D.Y → ℝ) (hb : IsCut (PG F) b)
    (hint : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY) :
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY = 0 := by
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -, -, -, -, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hkkc, hkkm, -, -, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨-, -, -, -, -, -, -, hLamF, hev, -, hfix⟩ := hE0d F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨-, hcut⟩ := hEcut F I Gf D hax
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have hF6' := hF6 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt
  have : Countable D.Cj := hcnt
  have : Countable D.Om := hax.cO

  have hbI : Integrable b D.μY := by
    refine ⟨hb.meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hb3
    refine lintegral_congr fun y => ?_
    exact Real.enorm_eq_ofReal (hb.nonneg y)

  have hum : ∀ T γ, Measurable (uT D k a T γ) := by
    intro T γ
    by_cases h : IsEll γ
    · unfold uT; simp only [h, if_true]; exact measurable_const
    · unfold uT; simp only [h, if_false]; exact (hkkm γ).indicator (hLamF T γ).1

  have hsumle : ∀ T : ℝ, 1 < T → ∀ y, y ∉ D.abelian₂ T → ∑' γ, ‖uT D k a T γ y‖ₑ ≤ C := by
    intro T hT y hy
    exact le_trans (ENNReal.tsum_le_tsum fun γ => enorm_uT_le D k a T γ y) ((hC T hT y).2 hy)
  have hon : ∀ T : ℝ, 1 < T → ∀ y, y ∈ D.abelian₂ T → ∀ γ, uT D k a T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    intro T hT y hy γ
    unfold uT
    split_ifs
    · rfl
    · exact Set.indicator_of_mem ((hC T hT y).1 hy γ) _

  have hinv : ∀ T (g γ : PG F) (y : D.Y), uT D k a T (g * γ * g⁻¹) (g • y) = uT D k a T γ y := by
    intro T g γ y
    unfold uT
    rw [isEll_conj hfix g γ]
    split_ifs
    · rfl
    · rw [Set.indicator_apply, Set.indicator_apply, hkkc]
      simp only [(hLamF T γ).2 g y]

  have step1 : ∀ T : ℝ, 1 < T → Integrable (fun y => b y • ∑' γ, uT D k a T γ y) D.μY ∧
      ∫ y, b y • ∑' γ, uT D k a T γ y ∂D.μY = 0 := by
    intro T hT
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY < ⊤ := by
      have hle : ∀ y, ∑' γ, ‖uT D k a T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        intro y
        by_cases hy : y ∈ D.abelian₂ T
        · refine le_trans ?_ le_self_add
          refine le_trans (ENNReal.tsum_le_tsum fun γ => ?_) (hCT y hy)
          exact (enorm_uT_le D k a T γ y).trans (enorm_ind_le D k a T γ y)
        · exact (hsumle T hT y hy).trans le_add_self
      calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY
          ≤ ∫⁻ y, ENNReal.ofReal (b y) * ((CT : ℝ≥0∞) + C) ∂D.μY :=
            lintegral_mono fun y => by gcongr; exact hle y
        _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * ((CT : ℝ≥0∞) + C) :=
            lintegral_mul_const' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top hb3 (by simp)
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT D k a T) (hum T) hfin
    refine ⟨hiY, ?_⟩
    rw [heq]

    let R : Set (D.Cj × D.Om) := Set.range (fun q : MulAction.orbitRel.Quotient (PG F) (D.Cj × D.Om) => q.out)
    have hR : ∀ ω : D.Cj × D.Om, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit (PG F) ω := by
      intro ω
      refine ⟨(Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · exact (MulAction.orbitRel_apply).1 (Quotient.mk_out ω)
      · rintro r ⟨⟨q, rfl⟩, hq⟩
        have e1 : q = Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω := by
          rw [← Quotient.out_eq q]
          exact Quotient.sound ((MulAction.orbitRel_apply).2 hq)
        rw [e1]
    have hβ : ∀ r : D.Cj × D.Om, ∃ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) r) β := by
      intro r
      refine hcut r.2 _ ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      have := congrArg Prod.snd hg
      simpa using this
    choose β hβ using hβ
    have hinv' : ∀ (g : PG F) (p : (D.Cj × D.Om) × D.Xs),
        uT D k a T (D.el (g • p).1.1) ((g • p).1.2, (g • p).2) = uT D k a T (D.el p.1.1) (p.1.2, p.2) := by
      intro g p
      have e : ((g • p).1.2, (g • p).2) = g • ((p.1.2, p.2) : D.Y) := rfl
      rw [e, show D.el (g • p).1.1 = g * D.el p.1.1 * g⁻¹ from D.smulC g p.1.1, hinv]
    obtain ⟨hI, hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' R hR β (fun r _ => hβ r)
    have hz : ∀ r : R, ∫ x, β r x • uT D k a T (D.el r.1.1) (r.1.2, x) = 0 := by
      intro r
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · have hI' := hI r.1 r.2
        simp only [uT, he, if_false] at hI' ⊢
        exact hF6' T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) hI'
    have hS' := hS
    simp only [hz] at hS'
    exact (hS'.unique hasSum_zero)

  have hT2 : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) + 2 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖b y • ∑' γ : PG F, (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _)) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
      by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
      · rw [tsum_congr (hon _ hT y hy)]
        exact le_add_of_nonneg_right C.2
      · have h1 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ₑ ≤ C :=
          enorm_tsum_le_tsum_enorm.trans (hsumle _ hT y hy)
        have h2 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ ≤ C := by
          have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
          simpa using this
        exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨T₀, hT₀⟩ := hev y
      obtain ⟨N, hN⟩ := exists_nat_ge T₀
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      have hy : y ∈ D.abelian₂ ((n : ℝ) + 2) := hT₀ _ (by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      dsimp only
      rw [tsum_congr (hon _ hT y hy)]
  have h0 : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact ((step1 _ (hT2 n)).2).symm
  exact tendsto_nhds_unique hlim h0

end UpperTheory.Esk.HyperbolicTermsContribution

theorem UpperTheory.Esk.pf_Fhyp : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E2 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F5 → UpperTheory.Esk.F6 → UpperTheory.Esk.Fhyp := by
  intro hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  exact UpperTheory.Esk.HyperbolicTermsContribution.fhyp hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 D k a hyp b hb hint
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapInt
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk

theorem lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, ENNReal.ofReal (f v x) ≤ C v) :
    ∫⁻ w : I → P, ENNReal.ofReal (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∀ v, Integrable (f v) := by
    intro v
    refine ⟨(hm v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]
    exact lt_of_le_of_lt (hC v) ENNReal.coe_lt_top
  have hnn : ∀ w : I → P, 0 ≤ ∏ v, f v (w v) :=
    fun w => Finset.prod_nonneg fun v _ => hf0 v (w v)
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ hnn),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_le_prod' fun v _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]
  exact hC v

theorem har1 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) :
    kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
  unfold B1c at hB
  obtain ⟨h1, -, h3, -⟩ := hB
  have hzw := (h1 z w).1
  have hzw' := (h1 z w').1
  have key : kap z w ≤ 8 * kap z w' := by
    nlinarith [h3 z w w', mul_le_mul_of_nonneg_left h hzw]
  calc kap z w ^ e ≤ (8 * kap z w') ^ e := Real.rpow_le_rpow hzw key he
    _ = (8 : ℝ) ^ e * kap z w' ^ e := Real.mul_rpow (by norm_num) hzw'

theorem har2 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') :
    (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
  unfold B1c at hB
  obtain ⟨-, -, -, h4, -⟩ := hB
  have hw : 0 < |w.1.im| := abs_pos.mpr w.2
  have hw' : 0 < |w'.1.im| := abs_pos.mpr w'.2
  have hz : 0 ≤ |z.1.im| := abs_nonneg _
  have hww : |w'.1.im| ≤ 8 * |w.1.im| := by
    nlinarith [h4 w w', mul_le_mul_of_nonneg_right h hw'.le]
  have key : |z.1.im| / |w.1.im| ≤ 8 * (|z.1.im| / |w'.1.im|) := by
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left hww hz]
  calc (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 * (|z.1.im| / |w'.1.im|)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hz hw.le) key (by norm_num)
    _ = (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (div_nonneg hz hw'.le)

theorem meas_abs_im : Measurable fun x : P => |x.1.im| := by
  exact (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable

end UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk.KappaIntegralLemmas in
theorem UpperTheory.Esk.pf_KapInt : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B6 → UpperTheory.Esk.KapInt := by
  intro hA _ hB h6
  unfold KapInt
  intro I _ k hk
  have hσ : SigmaFinite (volume : Measure P) := by
    unfold B1a at hA
    exact hA.1
  haveI := hσ
  have hB' := hB
  unfold B1c at hB'
  obtain ⟨h1, -, -, -, h5, -⟩ := hB'
  unfold B6 at h6
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have ha : ∀ v, 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := fun v => by positivity
  have hA' : ((∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ)
      = ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]
    exact Finset.prod_congr rfl fun v _ => Real.coe_toNNReal _ (ha v)
  refine ⟨∏ v, Cv v, ∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm : ∀ v, Measurable (fun t : P => kap (z v) t) := fun v =>
    h5.measurable.comp (measurable_const.prodMk measurable_id)
  have hsplit : ∀ w : X I, Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
      = ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    rfl
  refine ⟨?_, ?_, ?_, fun w w' hn => ⟨?_, ?_⟩⟩
  · unfold Kap
    exact Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _
  · unfold Kap
    exact lint_prod (fun v t => kap (z v) t ^ ((k v : ℝ) / 2))
      (fun v t => Real.rpow_nonneg (h1 _ _).1 _) (fun v => (hkm v).pow_const _) Cv
      (fun v => (hCv v (z v)).1)
  · simp only [hsplit]
    exact lint_prod
      (fun v t => kap (z v) t ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |t.1.im|) ^ ((1 : ℝ) / 2))
      (fun v t => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
        (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
      (fun v => ((hkm v).pow_const _).mul ((measurable_const.div meas_abs_im).pow_const _)) Cv
      (fun v => (hCv v (z v)).2)
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    unfold Kap
    rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (h1 _ _).1 _) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2)
        ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := e1
      _ ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
      (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 hB (z v) (w v) (w' v) (hn' v)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
        ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2)) *
            ((8 : ℝ) ^ ((1 : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul e1 e2 (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _))
      _ = ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) *
            (kap (z v) (w' v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) := by
        ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfMult
section
noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Esk.ExponentialSlopeDerivatives

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def A (δ : ℝ) (y : D.Y) : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}

theorem near_smul (hB : B1b) (δ : ℝ) (g : PG F) (z w : D.Xs) :
    Near δ (g • z : D.Xs) (g • w : D.Xs) ↔ Near δ z w := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [Dat.mk_smulX D γ z, Dat.mk_smulX D γ w]
    simp only [Near, Dat.act, hB.2.2.2.1]

theorem mem_conj (hB : B1b) (δ : ℝ) (g γ : PG F) (y : D.Y) :
    g * γ * g⁻¹ ∈ A D δ (g • y) ↔ γ ∈ A D δ y := by
  simp only [A, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, mul_smul, inv_smul_smul,
    smul_left_cancel_iff, near_smul D hB]

theorem A_conj (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    A D δ (g • y) = (fun γ => g * γ * g⁻¹) '' A D δ y := by
  ext γ'
  constructor
  · intro h
    refine ⟨g⁻¹ * γ' * g, (mem_conj D hB δ g _ y).1 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]
    · show g * (g⁻¹ * γ' * g) * g⁻¹ = γ'
      group
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_conj D hB δ g γ y).2 hγ

theorem conj_inj (g : PG F) : Function.Injective (fun γ : PG F => g * γ * g⁻¹) := by
  intro a b h
  simpa using h

theorem fin_card (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    ((A D δ (g • y)).Finite ↔ (A D δ y).Finite) ∧ (A D δ (g • y)).ncard = (A D δ y).ncard := by
  rw [A_conj D hB δ g y]
  exact ⟨Set.finite_image_iff (conj_inj g).injOn, Set.ncard_image_of_injective _ (conj_inj g)⟩

theorem e01 : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Ht01 [Fintype I] (z : X I) (x : Gf) : D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

end UpperTheory.Esk.ExponentialSlopeDerivatives

open UpperTheory.Esk UpperTheory.Esk.ExponentialSlopeDerivatives

theorem UpperTheory.Esk.pf_Mult : UpperTheory.Esk.B1b → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult := by
  intro hB hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have hcnt : ∀ x' : Gf, ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
      (A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).Finite ∧
      ((A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|) :=
    fun x' => hD.count ((x' : Gf ⧸ D.H)) δ C c hδ hc
  choose C' hC' using hcnt
  have hapos : ∀ x : Gf, 0 < D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H))) := fun x => hD.pos _ e01 _
  have final : ∀ (N Cx P a H K : ℝ), N ≤ Cx * (1 + P) → 0 ≤ P → P * a = H → 0 < a → 0 ≤ H →
      max Cx 0 * (1 + 1 / a) ≤ K → N ≤ K * (1 + H) := by
    intro N Cx P a H K hN hP hPa ha hH hK
    have hP' : P = H / a := eq_div_of_mul_eq ha.ne' hPa
    have h1 : N ≤ max Cx 0 * (1 + P) :=
      hN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h2 : 1 + P ≤ (1 + 1 / a) * (1 + H) := by
      rw [hP']
      have h0 : 0 ≤ 1 / a := by positivity
      have he : (1 + 1 / a) * (1 + H) - (1 + H / a) = H + 1 / a := by ring
      linarith
    have hM : 0 ≤ max Cx 0 := le_max_right _ _
    calc N ≤ max Cx 0 * (1 + P) := h1
      _ ≤ max Cx 0 * ((1 + 1 / a) * (1 + H)) := mul_le_mul_of_nonneg_left h2 hM
      _ = (max Cx 0 * (1 + 1 / a)) * (1 + H) := by ring
      _ ≤ K * (1 + H) := mul_le_mul_of_nonneg_right hK (by linarith)
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))), ?_⟩
  intro y s hs hy
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by
    rw [h2 _ e01 γ₀ y, hγ₀]
  have hn : c₀ ≤ D.Ht ![0, 1] ((γ₀ : PG F) • y).2 (D.rep ((γ₀ : PG F) • y).1) := by
    rw [← e1] at hy
    exact hy
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ hn
  have hb11 : b.val 1 1 ≠ 0 := by
    intro h0
    apply b.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hsm : ∀ ω : D.Om, (b : PG F) • ω = (((D.j b * D.rep ω : Gf) : Gf ⧸ D.H) : D.Om) := by
    intro ω
    conv_lhs => rw [← QuotientGroup.out_eq' ω]
    rfl
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) =
      (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    show (b : PG F) • ((γ₀ : PG F) • y).1 = _
    rw [hsm, hbx]
    exact QuotientGroup.eq.2 (by simpa using hh)
  obtain ⟨f1, c1⟩ := fin_card D hB δ (γ₀ : PG F) y
  obtain ⟨f2, c2⟩ := fin_card D hB δ (b : PG F) ((γ₀ : PG F) • y)
  rw [hy''] at f2 c2
  obtain ⟨hfin, hle⟩ := hC' x' _ hsg
  refine ⟨f1.1 (f2.1 hfin), ?_⟩
  have hHt : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) = D.HtY s y := by
    rw [← hy'', h2 _ e01 b _, hvb, h3 _ e01 _ hb11, e1]
  have hP : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs)
      = (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep ((x' : Gf ⧸ D.H))) :=
    Ht01 D (D.act b ((γ₀ : PG F) • y).2) (D.rep ((x' : Gf ⧸ D.H)))
  have hH : 0 ≤ D.HtY s y := by linarith
  show ((A D δ y).ncard : ℝ) ≤ _
  rw [← c1, ← c2]
  exact final _ _ _ _ _ _ hle (Finset.prod_nonneg fun v _ => abs_nonneg _) (hP.symm.trans hHt) (hapos x') hH
    (Finset.single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))))
      (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (one_div_nonneg.2 (hapos x).le))) hx'S)
end
end

