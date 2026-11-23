module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulQuot
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCellInv

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

theorem mk_inv_mul' {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [QuotientGroup.eq]
  simpa using hp

theorem mk_inv_rp' {P : Subgroup G} (q : G ⧸ P) : (QuotientGroup.mk (rp q)⁻¹ : G ⧸ P) = q := by
  simp [rp]

theorem rp_mk_inv {P : Subgroup G} (g : G) :
    ∃ p ∈ P, rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = p * g := by
  have hmem : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * g⁻¹ ∈ P := by
    have := mk_inv_rp' (QuotientGroup.mk g⁻¹ : G ⧸ P)
    rw [QuotientGroup.eq] at this
    simpa using this
  exact ⟨_, hmem, by simp⟩

theorem mk_inv_rp_mul {P : Subgroup G} (q : G ⧸ P) (x : G) :
    (QuotientGroup.mk (rp q * x)⁻¹ : G ⧸ P) = x⁻¹ • q := by
  conv_rhs => rw [← mk_inv_rp' q]
  rw [mul_inv_rev]
  rfl

theorem density_rp {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x g : G) :
    h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * x) / h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      h (g * x) / h g := by
  obtain ⟨p, hp, e⟩ := rp_mk_inv (P := P) g
  rw [e]
  have h1 := (S.pos (p * g)).ne'
  have h2 := (S.pos g).ne'
  rw [div_eq_div_iff h1 h2]
  have := S.law p hp g (g * x)
  rw [mul_assoc]
  linarith

theorem sec_translate {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [ContinuousMul G] (S : Setup P h mu)
    {f : G → ℂ} (hf : Sec P h f) (x : G) : Sec P h (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), fun p hp g => ?_⟩
  have h1 := hf.2 p hp (g * x)
  have h2 : ((h (p * g) : ℂ)) * h (g * x) = h g * h (p * (g * x)) := by
    exact_mod_cast S.law p hp g (g * x)
  have h3 : (h (g * x) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
  apply mul_right_cancel₀ h3
  show f (p * g * x) * (h g : ℂ) * (h (g * x) : ℂ) = f (g * x) * (h (p * g) : ℂ) * (h (g * x) : ℂ)
  rw [mul_assoc p g x]
  linear_combination (h g : ℂ) * h1 - f (g * x) * h2

variable [IsTopologicalGroup G]

theorem sec_of_real {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℝ} (hF : Continuous F) :
    Sec P h (fun g => ((F (QuotientGroup.mk g⁻¹) : ℝ) : ℂ) * (h g : ℂ)) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · have : Continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
      QuotientGroup.continuous_mk.comp continuous_inv
    exact (Complex.continuous_ofReal.comp (hF.comp this)).mul (Complex.continuous_ofReal.comp hc)
  · simp only [mk_inv_mul' hp]
    ring

theorem continuous_density {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x : G) :
    Continuous fun q : G ⧸ P => h (rp q * x) / h (rp q) := by
  have hq : IsQuotientMap fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.comp (Homeomorph.inv G).isQuotientMap
  rw [hq.continuous_iff]
  have : ((fun q : G ⧸ P => h (rp q * x) / h (rp q)) ∘ fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      fun g => h (g * x) / h g := by
    funext g
    exact density_rp S x g
  rw [this]
  exact (S.cont.comp (continuous_mul_const x)).div S.cont fun g => (S.pos g).ne'

theorem continuous_smul_quot {P : Subgroup G} (x : G) : Continuous fun q : G ⧸ P => x • q := by
  rw [(QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_const_mul x)

theorem compact_quot' {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have hK : IsCompact ((fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) '' C) :=
    hC.image (QuotientGroup.continuous_mk.comp continuous_inv)
  refine ⟨?_⟩
  convert hK using 1
  symm
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq, c, hc, hqc⟩ := hcov y⁻¹
  refine ⟨c, hc, ?_⟩
  have : y = (q * c)⁻¹ := by rw [← hqc, inv_inv]
  rw [this, QuotientGroup.eq]
  simpa using hq

theorem integral_translate {P : Subgroup G} [MeasurableSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (S : Setup P h mu) {ν : Measure (G ⧸ P)} (hR : Repr P h mu ν) {x : G} (hx : Inv P h mu x)
    {F : G ⧸ P → ℝ} (hF : Continuous F) :
    ∫ q, h (rp q * x) / h (rp q) * F (x⁻¹ • q) ∂ν = ∫ q, F q ∂ν := by
  have hs := sec_of_real (P := P) S.cont hF
  have h1 := (hR.2 _ hs).2
  have h2 := (hR.2 _ (sec_translate S hs x)).2
  have h3 := hx _ hs
  rw [h1, h2] at h3
  have e1 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q)⁻¹) : ℝ) : ℂ) * (h (rp q) : ℂ)) / (h (rp q) : ℂ) =
      ((F q : ℝ) : ℂ) := fun q => by
    have : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
    rw [mk_inv_rp', mul_div_cancel_right₀ _ this]
  have e2 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q * x)⁻¹) : ℝ) : ℂ) * (h (rp q * x) : ℂ)) / (h (rp q) : ℂ) =
      ((h (rp q * x) / h (rp q) * F (x⁻¹ • q) : ℝ) : ℂ) := fun q => by
    rw [mk_inv_rp_mul]
    push_cast
    ring
  simp only [e1, e2] at h3
  rw [integral_complex_ofReal, integral_complex_ofReal] at h3
  exact_mod_cast h3

theorem inv_measure [T2Space G] [SecondCountableTopology G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)]
    [BorelSpace (G ⧸ P)] (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) (ν : Measure (G ⧸ P))
    (hR : Repr P h mu ν) (x : G) (hx : Inv P h mu x) :
    (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q) = ν := by
  have : IsClosed (P : Set G) := S.closed
  have : CompactSpace (G ⧸ P) := compact_quot' S.cocpt
  have : IsFiniteMeasure ν := hR.1
  have hj := continuous_density S x
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp hj.measurable
  have hjnn : ∀ q : G ⧸ P, 0 ≤ h (rp q * x) / h (rp q) := fun q => (div_pos (S.pos _) (S.pos _)).le
  have hfin : IsFiniteMeasure (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))) :=
    isFiniteMeasure_withDensity_ofReal
      (hj.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).2
  have hfin' : IsFiniteMeasure
      ((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q)) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hsm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hjm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have := integral_translate S hR hx f.continuous
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [ENNReal.toReal_ofReal (hjnn q), smul_eq_mul]

theorem invM : InvM := by
  intro G _ _ _ _ _ _ P _ _ h mu S ν hR x hx
  refine ⟨continuous_density S x, fun F hF => ?_⟩
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp (continuous_density S x).measurable
  have key : ∫⁻ q, F q ∂((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map
      (fun q => x⁻¹ • q)) = ∫⁻ q, F q ∂ν := by rw [inv_measure P h mu S ν hR x hx]
  rw [lintegral_map hF hsm.measurable,
    lintegral_withDensity_eq_lintegral_mul ν hjm
      (show Measurable fun a => F (x⁻¹ • a) from hF.comp hsm.measurable)] at key
  rw [← key]
  refine lintegral_congr fun q => ?_
  simp only [Pi.mul_apply, mul_comm]

end GlobalTheory.CompanionTheory.RswCellInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAffLine
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def aff (α β γ : ℝ) (l : ℂ × ℂ) : ℂ := (α : ℂ) * l.1 + (β : ℂ) * l.2 + (γ : ℂ)

def affR (α β γ : ℝ) (x : ℝ × ℝ) : ℝ := α * x.1 + β * x.2 + γ

def chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (l : ℂ × ℂ) : ℂ × ℂ := (aff α₁ β₁ γ₁ l, aff α₂ β₂ γ₂ l)

def chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (affR α₁ β₁ γ₁ x, affR α₂ β₂ γ₂ x)

lemma aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]

lemma aff_line (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by
  unfold aff; fun_prop

lemma continuous_affR (α β γ : ℝ) : Continuous (affR α β γ) := by
  unfold affR; fun_prop

lemma continuous_chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chg α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_aff _ _ _).prodMk (continuous_aff _ _ _)

lemma continuous_chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)

lemma differentiable_aff_line (α β γ : ℝ) (p v : ℂ × ℂ) :
    Differentiable ℂ fun τ : ℂ => aff α β γ (p + τ • v) := by
  simp only [aff_line]
  fun_prop

lemma mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by
  simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]

lemma chg_line (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl

section Good

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma lineHol_chg {F : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hF : LineHol F (tube Ω))
    (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    LineHol (fun l => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l)) (tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω)) := by
  intro p v
  have h := hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p)
    ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)
  simp only [mem_tube_chg, chg_line]
  exact h

theorem TubeGood_chg {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]

lemma TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ

structure Fac (A : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol A (tube Ω)
  cont : ContinuousOn A (tube Ω)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C, ‖A l‖ ≤ M

lemma exists_bounds {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : C.Nonempty) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : ∃ x ∈ C, ∃ y ∈ C, ∀ u ∈ C, f x ≤ f u ∧ f u ≤ f y := by
  obtain ⟨x, hx, hx'⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨y, hy, hy'⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩

theorem Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by
  have hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a := fun l hl => by
    rw [aff_re]; exact h _ hl
  refine ⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩
  · refine hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_
    intro τ hτ
    exact hre _ hτ
  · exact hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, hy, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_smul {f : ℂ × ℂ → ℂ} {A : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hA : Fac A Ω) :
    Fac (fun l => f l • A l) Ω := by
  refine ⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem Fac_mul {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'

theorem TubeGood_smul {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Good

section Comp

variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

theorem Fac_comp {A : ℂ × ℂ → E₂ →L[ℂ] E₃} {B : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)}
    (hA : Fac A Ω) (hB : Fac B Ω) : Fac (fun l => (A l).comp (B l)) Ω := by
  refine ⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont,
    fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hA.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hB.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Comp

end GlobalTheory.CompanionTheory.RgEisGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerIdealTorsionFree
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DivPow

theorem exists_gamma {S : Type} [CommRing S] (I : Ideal S) (z : S)
    (h : ∀ k : ℕ, k ≠ 0 → ∃ y ∈ I, (k.factorial : S) * y = z ^ k) :
    ∃ γ : ℕ → S, (∀ i, i ≠ 0 → γ i ∈ I) ∧ ∀ i, (i.factorial : S) * γ i = z ^ i := by
  classical
  refine ⟨fun i => if hi : i = 0 then 1 else (h i hi).choose, ?_, ?_⟩
  · intro i hi
    simpa [hi] using (h i hi).choose_spec.1
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · simpa [hi] using (h i hi).choose_spec.2

theorem pdI_span : ∀ {S : Type} [CommRing S], TF (S := S) → ∀ s : Set S,
    (∀ x ∈ s, ∀ k : ℕ, k ≠ 0 → ∃ y ∈ Ideal.span s, (k.factorial : S) * y = x ^ k) →
    PdI (Ideal.span s) := by
  intro S _ _ s h x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    intro k hk
    exact ⟨0, Ideal.zero_mem _, by simp [zero_pow hk]⟩
  | smul a x _ ih =>
    intro k hk
    obtain ⟨y, hy, e⟩ := ih k hk
    refine ⟨a ^ k * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    rw [smul_eq_mul, mul_pow, ← e]
    ring
  | add x x' _ _ ih ih' =>
    intro k hk
    obtain ⟨γ, hγ, e⟩ := exists_gamma _ x ih
    obtain ⟨γ', hγ', e'⟩ := exists_gamma _ x' ih'
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, γ p.1 * γ' p.2, ?_, ?_⟩
    · refine Ideal.sum_mem _ ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by
          rintro rfl
          exact hk (by omega)
        exact Ideal.mul_mem_left _ _ (hγ' j hj)
      · exact Ideal.mul_mem_right _ _ (hγ i hi)
    · rw [Finset.mul_sum, (Commute.all x x').add_pow']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      subst hij
      rw [← e i, ← e' j, nsmul_eq_mul, Nat.choose_symm_add, ← Nat.add_choose_mul_factorial_mul_factorial i j]
      push_cast
      ring

end GlobalTheory.CompanionTheory.DivPow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerMorphismCompatible
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdMor

theorem isDPMorphism_of_isPd : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  intro S _ S' E E' _ _ _ π π' I I' J J' δ δ' F₀ F hπ hI hP hP' hF₀ hF
  have hmem : ∀ a ∈ J, ∃ x ∈ I, π x = a := fun a ha => by
    rw [hP.1] at ha
    exact (Ideal.mem_map_iff_of_surjective π hπ).mp ha
  have hdp : ∀ (k : ℕ) (x : S), x ∈ I → ∃ y : S, (k.factorial : S) * y = x ^ k := by
    intro k x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by simp⟩
    · obtain ⟨y, -, hy⟩ := hI x hx k hk.ne'
      exact ⟨y, hy⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    rw [Ideal.mem_comap, hF, hP'.1]
    exact Ideal.mem_map_of_mem π' (hF₀ x hx)
  · intro n a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    obtain ⟨y, hy⟩ := hdp n x hx
    rw [hP.2 n x y hx hy, hF, hF,
      hP'.2 n (F₀ x) (F₀ y) (hF₀ x hx) (by rw [← map_pow, ← hy, map_mul, map_natCast])]

end GlobalTheory.CompanionTheory.PdMor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityChainPowerFactorization
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NormalForm

theorem normal_form_of_dichotomy :
    ∀ {S : Type} [CommRing S] (ϖ : S), (∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) →
      ∀ (f : S) (M : ℕ), ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  intro S _ ϖ hd f M
  induction M generalizing f with
  | zero => exact Or.inl (by simp)
  | succ M ih =>
    rcases hd f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', hg, hf'⟩
      · left
        rw [pow_succ']
        exact mul_dvd_mul_left ϖ hg
      · right
        refine ⟨j + 1, f', ?_, hf'⟩
        rw [hg, pow_succ', mul_assoc]
    · exact Or.inr ⟨0, f, by simp, hf⟩

end GlobalTheory.CompanionTheory.NormalForm
end

