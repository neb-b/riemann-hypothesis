module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.LintegralOfRealToReal
section
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
  [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private theorem lintegral_swap_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i) {a b Ψ : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hΨ : Measurable Ψ) (hinv : ∀ t x, Ψ (i t * x) = Ψ x) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1)
    (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) :
    ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, Ψ x * b x ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm μ ν i hi ha hb hΨ hinv hA hB

private theorem ae_lt_top_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    (i : T →* X) (hi : Continuous i) {a : X → ℝ≥0∞} (ha : Measurable a) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) :
    ∀ᵐ x ∂μ, a x < ⊤ := by
  have him : Measurable i := hi.measurable
  have hS : MeasurableSet (a ⁻¹' {⊤}) := ha (measurableSet_singleton _)
  set c : X → ℝ≥0∞ := (a ⁻¹' {⊤}).indicator 1 with hc
  have hcm : Measurable c := measurable_one.indicator hS
  have hm : Measurable (fun p : X × T => i p.2 * p.1) := (him.comp measurable_snd).mul measurable_fst
  have hu : Measurable (Function.uncurry fun (x : X) (t : T) => c (i t * x)) := hcm.comp hm
  have h0 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = 0 := by
    have : ∀ x, ∫⁻ t, c (i t * x) ∂ν = 0 := by
      intro x
      have hf : ∀ᵐ t ∂ν, a (i t * x) < ⊤ :=
        ae_lt_top (ha.comp (him.mul_const x)) (by rw [hA x]; exact ENNReal.one_ne_top)
      have hcx : Measurable (fun t => c (i t * x)) := hcm.comp (him.mul_const x)
      rw [lintegral_eq_zero_iff hcx]
      filter_upwards [hf] with t ht
      simp [hc, ht.ne]
    simp [this]
  have h1 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = μ (a ⁻¹' {⊤}) * ν Set.univ := by
    rw [lintegral_lintegral_swap hu.aemeasurable]
    have : ∀ t, ∫⁻ x, c (i t * x) ∂μ = μ (a ⁻¹' {⊤}) := by
      intro t
      rw [lintegral_mul_left_eq_self c (i t), hc, lintegral_indicator_one hS]
    simp [this]
  rw [h1] at h0
  have hν : ν Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne ν)).ne'
  have hμ : μ (a ⁻¹' {⊤}) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hν
  have : ∀ᵐ x ∂μ, x ∉ a ⁻¹' {⊤} := measure_eq_zero_iff_ae_notMem.mp hμ
  filter_upwards [this] with x hx
  exact lt_top_iff_ne_top.mpr hx

private theorem lintegral_ofReal_toReal (μ : Measure X) {a : X → ℝ≥0∞} (hfin : ∀ᵐ x ∂μ, a x < ⊤) (c : X → ℝ) :
    ∫⁻ x, ENNReal.ofReal (c x * (a x).toReal) ∂μ = ∫⁻ x, ENNReal.ofReal (c x) * a x ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with x hx
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

private theorem real_eq (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X) (hi : Continuous i) {a b : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) {g : X → ℝ} (hg : Measurable g)
    (hinv : ∀ t x, g (i t * x) = g x) (h1 : Integrable (fun x => g x * (a x).toReal) μ)
    (h2 : Integrable (fun x => g x * (b x).toReal) μ) :
    ∫ x, g x * (a x).toReal ∂μ = ∫ x, g x * (b x).toReal ∂μ := by
  have fa := ae_lt_top_norm μ ν i hi ha hA
  have fb := ae_lt_top_norm μ ν i hi hb hB
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
  simp only [← neg_mul]
  rw [lintegral_ofReal_toReal μ fa g, lintegral_ofReal_toReal μ fa (fun x => - g x),
    lintegral_ofReal_toReal μ fb g, lintegral_ofReal_toReal μ fb (fun x => - g x),
    lintegral_swap_norm μ ν i hi ha hb hg.ennreal_ofReal (fun t x => by rw [hinv]) hA hB,
    lintegral_swap_norm μ ν i hi ha hb (Ψ := fun x => ENNReal.ofReal (- g x)) hg.neg.ennreal_ofReal
      (fun t x => by rw [hinv]) hA hB]

private theorem integrable_mul_toReal (μ : Measure X) {Φ : X → ℂ} {a : X → ℝ≥0∞} (hΦ : Measurable Φ)
    (ha : Measurable a) (hf : ∫⁻ x, ‖Φ x‖ₑ * a x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((a x).toReal : ℂ)) μ := by
  refine ⟨(hΦ.mul (Complex.measurable_ofReal.comp ha.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
  rw [enorm_mul]
  gcongr
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.isUnit_last_join :
    Q1 := by
  intro X G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ u i hu hi Φ ρ hΦ hinv hn hfin
  have hex : ∃ ρ, IsNormAlong u (fun t => u (i t)) ν ρ := ⟨ρ, hn⟩
  unfold quotInt
  rw [dite_eq_left hex]
  have h0 := hex.choose_spec
  set ρ₀ := hex.choose
  have ha : Measurable (fun x => ρ (u x)) := hn.1.comp hu
  have hb : Measurable (fun x => ρ₀ (u x)) := h0.1.comp hu
  have hA : ∀ x, ∫⁻ t, ρ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using hn.2 x
  have hB : ∀ x, ∫⁻ t, ρ₀ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using h0.2 x
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ₀ (u x) ∂μ < ⊤ := by
    rw [← lintegral_swap_norm μ ν i hi ha hb hΦ.enorm (fun t x => by rw [hinv]) hA hB]
    exact hfin
  have h1 := integrable_mul_toReal μ hΦ ha hfin
  have h2 := integrable_mul_toReal μ hΦ hb hfin'
  have hre : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ :=
    fun f hf => (Complex.reCLM.integral_comp_comm hf).symm
  have him : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ :=
    fun f hf => (Complex.imCLM.integral_comp_comm hf).symm
  apply Complex.ext
  · rw [hre _ h1, hre _ h2]
    simp only [Complex.re_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_re.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.re_mul_ofReal] using h2.re
    · simpa [Complex.re_mul_ofReal] using h1.re
  · rw [him _ h1, him _ h2]
    simp only [Complex.im_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_im.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.im_mul_ofReal] using h2.im
    · simpa [Complex.im_mul_ofReal] using h1.im
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.OrbitalIntegralAbsoluteConvergence
section
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

private theorem finite_fiber_integral {X T : Type} [Group X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [Group T]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (i : T →* X) (Φ : X → ℂ) (ρ : X → NNReal) (hΦ : Continuous Φ)
    (hρ : Continuous ρ) (hC : ∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y)
    (h : ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧ ∀ t, ∀ x ∈ C, ρ (i t * x) ≠ 0 → i t * x ∈ C') :
    ∫⁻ x, ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) ∂μ < ⊤ := by
  obtain ⟨C, hC, hs⟩ := hC
  obtain ⟨C', hC', hs'⟩ := h C hC
  have hc : Continuous fun x => Φ x * ((ρ x : ℝ) : ℂ) :=
    hΦ.mul (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hρ))
  have hk : HasCompactSupport fun x => Φ x * ((ρ x : ℝ) : ℂ) := by
    refine HasCompactSupport.intro hC' fun x hx => ?_
    by_contra hne
    have h1 : Φ x ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ρ x ≠ 0 := by
      intro h0
      exact hne (by simp [h0])
    obtain ⟨t, y, hy, rfl⟩ := hs x h1
    exact hx (hs' t y hy h2)
  have hi := (hc.integrable_of_hasCompactSupport (μ := μ) hk).2
  unfold HasFiniteIntegral at hi
  convert hi using 3 with x
  rw [enorm_mul]
  congr 1
  simp [eNorm_eq_nnNorm]

private theorem prod_isInvInvariant {T T' : Type} [Group T] [MeasurableSpace T] [MeasurableInv T] [Group T'] [MeasurableSpace T']
    [MeasurableInv T'] (ν : Measure T) (ν' : Measure T') [SFinite ν] [SFinite ν'] [ν.IsInvInvariant] [ν'.IsInvInvariant] :
    (ν.prod ν').IsInvInvariant := by
  constructor
  exact ((Measure.measurePreserving_inv ν).prod (Measure.measurePreserving_inv ν')).map_eq

theorem UpperTheory.ConvolutionTheory.G.orbitalIntegral_absolute_convergence :
    Q1 → Q2 → Q3 := by
  intro h1 h2 X T X' T' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ μ' _ ν' _ _ _ _ _
    i i' hi hi' Φ Φ' hΦ hΦ' hinv hinv' hC hC'
  obtain ⟨ρ, hρ, hn, hs⟩ := h2 X T ν i hi
  obtain ⟨ρ', hρ', hn', hs'⟩ := h2 X' T' ν' i' hi'
  have f1 := finite_fiber_integral μ i Φ ρ hΦ hρ hC hs
  have f2 := finite_fiber_integral μ' i' Φ' ρ' hΦ' hρ' hC' hs'
  have e1 := h1 X X T μ ν (MonoidHom.id X) i measurable_id hi.continuous Φ _ hΦ.measurable hinv hn f1
  have e2 := h1 X' X' T' μ' ν' (MonoidHom.id X') i' measurable_id hi'.continuous Φ' _ hΦ'.measurable hinv' hn' f2
  haveI := prod_isInvInvariant ν ν'
  have hn3 : IsNormAlong id (fun t : T × T' => (i t.1, i' t.2)) (ν.prod ν')
      (fun x : X × X' => (ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) := by
    refine ⟨(hn.1.comp measurable_fst).mul (hn'.1.comp measurable_snd), fun x => ?_⟩
    have a1 : Measurable fun t => (ρ (i t * x.1) : ℝ≥0∞) :=
      hn.1.comp (hi.continuous.mul continuous_const).measurable
    have a2 : Measurable fun t => (ρ' (i' t * x.2) : ℝ≥0∞) :=
      hn'.1.comp (hi'.continuous.mul continuous_const).measurable
    have := lintegral_prod_mul (μ := ν) (ν := ν') a1.aemeasurable a2.aemeasurable
    have b1 := hn.2 x.1
    have b2 := hn'.2 x.2
    simp only [id] at b1 b2
    rw [b1, b2, mul_one] at this
    exact this
  have f3 : ∫⁻ x : X × X', ‖Φ x.1 * Φ' x.2‖ₑ * ((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) ∂(μ.prod μ') < ⊤ := by
    have a1 : Measurable fun x => ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) := hΦ.measurable.enorm.mul hn.1
    have a2 : Measurable fun x => ‖Φ' x‖ₑ * (ρ' x : ℝ≥0∞) := hΦ'.measurable.enorm.mul hn'.1
    have := lintegral_prod_mul (μ := μ) (ν := μ') a1.aemeasurable a2.aemeasurable
    refine lt_of_eq_of_lt ?_ (this ▸ ENNReal.mul_lt_top f1 f2)
    refine lintegral_congr fun x => ?_
    rw [enorm_mul]
    ring
  have e3 := h1 (X × X') (X × X') (T × T') (μ.prod μ') (ν.prod ν') (MonoidHom.id _) (i.prodMap i') measurable_id
    (hi.continuous.prodMap hi'.continuous) (fun x => Φ x.1 * Φ' x.2) _
    ((hΦ.measurable.comp measurable_fst).mul (hΦ'.measurable.comp measurable_snd))
    (fun t x => by
      show Φ (i t.1 * x.1) * Φ' (i' t.2 * x.2) = _
      rw [hinv, hinv']) hn3 f3
  refine e3.trans (Eq.trans ?_ (congrArg₂ (· * ·) e1 e2).symm)
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [MonoidHom.id_apply, ENNReal.toReal_mul, Complex.ofReal_mul]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G
open scoped ENNReal NumberField.AdeleRing

namespace UpperTheory.ConvolutionTheory.T4

section

abbrev Pl (K : Type) [Field K] : Type := HeightOneSpectrum (𝓞 K)

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev GA : Type := AdelicGLn.AdelicGL K n

abbrev pI : GA K n →* GL (Fin n) (InfiniteAdeleRing K) := mapGL n (RingHom.fst _ _)

def pF (v : Pl K) : GA K n →* GL (Fin n) (v.adicCompletion K) where
  toFun := finAt v
  map_one' := Units.ext (by ext a b; simp only [finAt_apply, Units.val_one, Matrix.one_apply]; split_ifs <;> rfl)
  map_mul' := finAt_mul v

theorem pF_apply (v : Pl K) (g : GA K n) : pF K n v g = finAt v g := rfl

abbrev KF (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) := GLnLocal.integralGL (v.adicCompletion K) n

abbrev zA (s : ℝ) : GA K n := centralSection K n ⟨Real.exp s, Real.exp_pos s⟩

variable {K n}

abbrev TA (γ : GL (Fin n) K) : Subgroup (GA K n) := Subgroup.centralizer {AdelicGLn.diagonal K n γ}

abbrev TI (γ : GL (Fin n) K) : Subgroup (GL (Fin n) (InfiniteAdeleRing K)) :=
  Subgroup.centralizer {pI K n (AdelicGLn.diagonal K n γ)}

abbrev TF (γ : GL (Fin n) K) (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) :=
  Subgroup.centralizer {pF K n v (AdelicGLn.diagonal K n γ)}

abbrev EulT [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing K))] [∀ v : Pl K, MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    (γ : GL (Fin n) K) (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl K, Measure (TF γ v)) (b : NNReal)
    (S : Finset (Pl K)) : Prop :=
  Eul (cen (pI K n) (AdelicGLn.diagonal K n γ)) (fun v => cen (pF K n v) (AdelicGLn.diagonal K n γ))
    (fun v => (KF K n v).comap (TF γ v).subtype) ν νi nv b S

def FF (γ : GL (Fin n) K) (Φ : GA K n → ℂ) (x : GA K n) : ℂ :=
  ∫ s : ℝ, Φ (zA K n s * (x⁻¹ * AdelicGLn.diagonal K n γ * x))

end

section

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E] (n : ℕ)


variable (F) in
abbrev infMap : InfiniteAdeleRing F →+* InfiniteAdeleRing E :=
  GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)

abbrev pE (v : Pl F) : GA E n →* GL (Fin n) (CompletionsOver E v) := mapGL n (atFin v)

def KE (v : Pl F) : Subgroup (GL (Fin n) (CompletionsOver E v)) where
  carrier := unitSet E n v
  one_mem' w := by rw [map_one]; exact one_mem _
  mul_mem' {a b} ha hb w := by rw [map_mul]; exact mul_mem (ha w) (hb w)
  inv_mem' {a} ha w := by rw [map_inv]; exact inv_mem (ha w)

variable {E n}

def FE (σ : E ≃ₐ[F] E) (δ : GL (Fin n) E) (Φ : GA E n → ℂ) (x : GA E n) : ℂ :=
  ∫ s : ℝ, Φ (zA E n s * (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x))

end

def QSub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (H : Subgroup G), IsClosed (H : Set G) → ∀ (μ : Measure H) (j : T →* H) (ν : Measure T), Pair μ j ν →
    ∀ Φ : H → ℂ, Measurable Φ → (∀ t g, Φ (j t * g) = Φ g) →
      quotInt μ (fun x : H => (x : G)) (fun t => (j t : G)) ν Φ = qI μ j ν Φ

def RPF : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), RP (pI K n) (pF K n) (KF K n)

def RPE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    RP (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v)

def Compat : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    (∀ g, pI E n (mapGL n (galAd σ) g) = mapGL n (galInf σ) (pI E n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (galAd σ) g) = mapGL n (galFin σ v) (pE E n v g)) ∧
    (∀ g, pI E n (mapGL n (adeleMap F E) g) = mapGL n (infMap F E) (pI F n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (adeleMap F E) g) = mapGL n (incFin E v) (pF F n v g)) ∧
    (∀ g, mapGL n (galAd σ) (mapGL n (adeleMap F E) g) = mapGL n (adeleMap F E) g) ∧
    (∀ g, mapGL n (galInf σ) (mapGL n (infMap F E) g) = mapGL n (infMap F E) g) ∧
    (∀ δ, mapGL n (galAd σ) (AdelicGLn.diagonal E n δ) = AdelicGLn.diagonal E n (sigmaGL σ δ)) ∧
    ∀ γ, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n γ) = AdelicGLn.diagonal E n (incl γ)

def GalCont : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    Continuous (mapGL n (galAd σ)) ∧ Continuous (mapGL n (galInf σ)) ∧ ∀ v : Pl F, Continuous (mapGL n (galFin σ v))

def LocEmb : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    IsClosedEmbedding (mapGL n (infMap F E)) ∧ ∀ v : Pl F, IsClosedEmbedding (mapGL n (incFin E v))

def UnitIff : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (t : GL (Fin n) (v.adicCompletion F)),
    mapGL n (incFin E v) t ∈ unitSet E n v ↔ t ∈ KF F n v

def CentLoc : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}),
    (∃ r : (InfiniteAdeleRing K)ˣ, ∀ g : GL (Fin n) (InfiniteAdeleRing K),
      ((pI K n (centralSection K n s) * g : GL (Fin n) (InfiniteAdeleRing K)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
        (r : InfiniteAdeleRing K) • (g : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))) ∧
    (∀ g, pI K n (centralSection K n s) * g = g * pI K n (centralSection K n s)) ∧
    (∀ v : Pl K, pF K n v (centralSection K n s) = 1) ∧
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F K] (v : Pl F), pE K n v (centralSection K n s) = 1

def CentBC : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (s : {r : ℝ // 0 < r}),
    mapGL n (adeleMap F E) (centralSection F n s) = centralSection E n (s ^ Module.finrank F E)

def ZNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (s : ℝ) (δ : GL (Fin n) (InfiniteAdeleRing E)),
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (zA E n s) * δ) =
        mapGL n (infMap F E) (pI F n (zA F n s)) * twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ

def LocNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F), normGL σ δ = incl γ →
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (AdelicGLn.diagonal E n δ)) =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ)) ∧
      ∀ v : Pl F, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) (pE E n v (AdelicGLn.diagonal E n δ)) =
        mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ))

def SepLoc : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable ∧
    (∀ s : ℝ, (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable) ∧
    ∀ v : Pl F, (finAt v (AdelicGLn.diagonal F n γ)).val.charpoly.Separable

def TComm : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (∀ s t : TA γ, s * t = t * s) ∧ (∀ s t : TI γ, s * t = t * s) ∧ (∀ v : Pl F, ∀ s t : TF γ v, s * t = t * s) ∧
    ∀ γ₁ : G1 F n, (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → ∀ s t : Subgroup.centralizer {γ₁}, s * t = t * s

def Triv : Prop := ∀ (F : Type) [Field F] [NumberField F],
    galInf (1 : F ≃ₐ[F] F) = RingHom.id _ ∧ infMap F F = RingHom.id _ ∧
    ∀ v : Pl F, galFin (1 : F ≃ₐ[F] F) v = RingHom.id _ ∧ Function.Bijective (incFin F v)

def BoundE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) (InfiniteAdeleRing E)) (D : Set (GL (Fin n) (InfiniteAdeleRing E))), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x) ∈ D → s ∈ B

def InfF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) (InfiniteAdeleRing F),
    (∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI F n (zA F n s) * (x⁻¹ * γ * x) ∈ D → s ∈ B) ∧
    (γ.val.charpoly.Separable → ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ C, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y)

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
    ∀ᶠ v : Pl F in cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y

def Spl : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    (∃ e : G1 E n × {r : ℝ // 0 < r} ≃ₜ* GA E n, ∀ x, e x = (x.1 : GA E n) * mapGL n (adeleMap F E) (centralSection F n x.2)) ∧
    ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ →
      (∃ e : Subgroup.centralizer {γ₁} × {r : ℝ // 0 < r} ≃ₜ* TA γ,
        ∀ x, (e x : GA F n) = ((x.1 : G1 F n) : GA F n) * centralSection F n x.2) ∧
      ∃ j : Subgroup.centralizer {γ₁} →* G1 E n, IsClosedEmbedding j ∧
        ∀ t, (j t : GA E n) = mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)

def Glob : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (G1 E n)) (μF : Measure (G1 F n)), μE.IsHaarMeasure → μF.IsHaarMeasure →
    ∃ (μE' : Measure (GA E n)) (μF' : Measure (GA F n)), Uni μE' ∧ Uni μF' ∧
      ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → IsRegSemisimple γ →
      ∀ ν : Measure (Subgroup.centralizer {γ₁}), ν.IsHaarMeasure → ∃ ν' : Measure (TA γ), ν'.IsHaarMeasure ∧
        (∀ Φ : GA F n → ℂ, Measurable (FF γ Φ) →
          quotInt μF id (fun t : Subgroup.centralizer {γ₁} => (t : G1 F n)) ν (fun x => avg Φ (x⁻¹ * γ₁ * x)) =
            qI μF' (TA γ).subtype ν' (FF γ Φ)) ∧
        ∀ δ : GL (Fin n) E, normGL σ δ = incl γ → ∀ Φ : GA E n → ℂ, Measurable (FE σ δ Φ) →
          quotInt μE (fun x : G1 E n => (x : GA E n))
            (fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)) ν
            (fun x => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n))) =
            qI μE' ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν' (FE σ δ Φ)

def SideF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (μ : Measure (GA F n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing F))) (m : ∀ v : Pl F, Measure (GL (Fin n) (v.adicCompletion F))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI F n) (pF F n) (KF F n) μ μi m a S →
      ∀ (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ) (f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ),
      Continuous fi → HasCompactSupport fi → (∀ v, Continuous (f v)) →
      (∀ v ∉ S, f v = (KF F n v : Set _).indicator 1 ∧ ∀ x : GL (Fin n) (v.adicCompletion F),
        x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
        ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y) →
      Measurable (FF γ (tensF fi f)) ∧ qI μ (TA γ).subtype ν (FF γ (tensF fi f)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi (TI γ).subtype νi fun x => fi (x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x)) *
          ∏ v ∈ S, qI (m v) (TF γ v).subtype (nv v) fun x => f v (x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x)

def SideE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [∀ v : Pl F, BorelSpace (GL (Fin n) (CompletionsOver E v))]
      (μ : Measure (GA E n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing E))) (m : ∀ v : Pl F, Measure (GL (Fin n) (CompletionsOver E v))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ δ : GL (Fin n) E, normGL σ δ = incl γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v) μ μi m a S →
      ∀ (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
      Continuous φi → HasCompactSupport φi → (∀ v, Continuous (φ v)) →
      (∀ v ∉ S, φ v = (unitSet E n v).indicator 1 ∧ ∀ x : GL (Fin n) (CompletionsOver E v),
        x⁻¹ * mapGL n (atFin v) (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x ∈ unitSet E n v ↔
        ∃ t : GL (Fin n) (v.adicCompletion F), t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
          ∃ y ∈ unitSet E n v, x = mapGL n (incFin E v) t * y) →
      Measurable (FE σ δ (tensE φi φ)) ∧ qI μ ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν (FE σ δ (tensE φi φ)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi ((mapGL n (infMap F E)).comp (TI γ).subtype) νi fun x =>
            φi (x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x)) *
          ∏ v ∈ S, qI (m v) ((mapGL n (incFin E v)).comp (TF γ v).subtype) (nv v) fun x =>
            φ v (x⁻¹ * pE E n v (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x)

end UpperTheory.ConvolutionTheory.T4
end
end

