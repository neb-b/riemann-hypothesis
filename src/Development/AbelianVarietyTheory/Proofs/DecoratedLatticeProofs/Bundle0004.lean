module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
section
open scoped ComplexConjugate

namespace GlobalTheory

theorem hermitian_adjoint_exists_unique :
    ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
      (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ),
      (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) →
      ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  intro A C _ _ _ _ _ ipA ip _hsym hpos io u

  let g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ) :=
    { toFun := fun x => ip.flip x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        ext y
        have h1 : (r • x : C) = (r : ℂ) • x := rfl
        have h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x := by
          show ((r : ℂ) • ip.flip x) y = _
          simp
        simp only [RingHom.id_apply]
        rw [h2, h1, LinearMap.map_smulₛₗ]
        simp [Complex.conj_ofReal] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have h0 : ip x x = 0 := by
      have := LinearMap.congr_fun hx x
      simpa [g] using this
    have := hpos x hne
    rw [h0] at this
    simp at this
  have hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hs : Function.Surjective g := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg
  obtain ⟨x, hx⟩ := hs ((ipA.flip u).comp io)
  refine ⟨x, fun y => ?_, fun x' hx' => ?_⟩
  · have := LinearMap.congr_fun hx y
    simpa [g] using this
  · apply hg
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢
    rw [hx' y, hy]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexComapEqOfCosetsHit
section
namespace GlobalTheory.IndexComapCosets

theorem index_comap_eq_of_cosets_hit {A B : Type} [Group A] [Group B] (f : A →* B)
    (H : Subgroup B) (h : ∀ b : B, ∃ a : A, (f a)⁻¹ * b ∈ H) :
    (H.comap f).index = H.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  let φ : A ⧸ H.comap f → B ⧸ H :=
    Quotient.map' f (fun a a' hr => by
      rw [QuotientGroup.leftRel_apply] at hr ⊢
      simpa using hr)
  have hφ : ∀ a : A, φ (a : A ⧸ H.comap f) = (f a : B ⧸ H) := fun a => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hφ, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [hφ, QuotientGroup.eq]; exact ha⟩
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)

end GlobalTheory.IndexComapCosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicator
section
open MeasureTheory Classical

namespace GlobalTheory.BlockFubini

theorem integral_block_indicator (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ ¬ Q i) (hQ : ∀ i, Q i → P i) (s : Set k) (hs : MeasurableSet s) (_hν : ν s ≠ ⊤) (G : (I → k) → ℂ) (hG : ∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) : ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  let σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i} :=
    { toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩)
      invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩
      left_inv := by
        rintro (a | a)
        · simp [a.2]
        · simp [((hR _).1 a.2).2]
      right_inv := by
        intro a
        by_cases h : Q a.1 <;> simp [h] }
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)
  have h3 := h1.comp h2
  rw [← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]
  have key : ∀ z : ({i // Q i} → k) × ({i // R i} → k),
      G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0)
      = (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) z.1 * G (fun i => if h : R i then z.2 ⟨i, h⟩ else 0) := by
    intro z
    set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE
    have e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a := by
      intro a
      rw [hE]
      simp only [Function.comp_apply]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      cases a <;> rfl
    have e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩ := fun i h => e0 (Sum.inl ⟨i, h⟩)
    have e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩ := fun i h => e0 (Sum.inr ⟨i, h⟩)
    rw [hG]
    congr 1
    · rw [Set.indicator_apply]
      congr 1
      apply propext
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h a
        have := h a.1 a.2
        rwa [dif_pos (hQ _ a.2), e1 _ a.2] at this
      · intro h i hi
        rw [dif_pos (hQ _ hi), e1 _ hi]
        exact h _
    · congr 1
      funext i
      by_cases hq : Q i
      · have : ¬ R i := fun h => ((hR i).1 h).2 hq
        simp [hq, this]
      · by_cases hp : P i
        · have : R i := (hR i).2 ⟨hp, hq⟩
          simp only [hq, if_false, dif_pos hp, dif_pos this]
          exact e2 i this
        · have : ¬ R i := fun h => hp ((hR i).1 h).1
          simp [hq, hp, this]
  simp_rw [key]
  rw [integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]
  congr 1
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]
  simp [Measure.real, Measure.pi_pi]

end GlobalTheory.BlockFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormula
section
open MeasureTheory

namespace GlobalTheory.FoldIntegral

theorem integral_integral_eq_pos_sub_neg {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by
  have hN : Measurable fun y => ∫⁻ s, ‖h (y, s)‖ₑ ∂m := hh.enorm.lintegral_prod_right'
  have hp : Measurable fun y => ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m :=
    hh.ennreal_ofReal.lintegral_prod_right'
  have hn : Measurable fun y => ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m :=
    hh.neg.ennreal_ofReal.lintegral_prod_right'
  have bp : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => Real.ofReal_le_enorm _) hfin
  have bn : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s =>
      (Real.ofReal_le_enorm _).trans (enorm_neg _).le) hfin
  rw [← integral_toReal hp.aemeasurable (ae_lt_top hp bp.ne),
    ← integral_toReal hn.aemeasurable (ae_lt_top hn bn.ne),
    ← integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable bp.ne)
      (integrable_toReal_of_lintegral_ne_top hn.aemeasurable bn.ne)]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨(hh.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩

theorem clm_integral_integral {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by
  have hN : Measurable fun y => ∫⁻ s, ‖H (y, s)‖ₑ ∂m := hH.enorm.lintegral_prod_right'
  have hI : Integrable (fun y => ∫ s, H (y, s) ∂m) ν :=
    ⟨hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
      lt_of_le_of_lt (lintegral_mono fun y => enorm_integral_le_lintegral_enorm _) hfin⟩
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact (L.integral_comp_comm
    ⟨(hH.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩).symm

theorem fold : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  intro α Y Z _ _ _ μ Fs ν m S hS Φ hΦ c hc P hQ G hG hP hfin
  haveI : IsFiniteMeasure (m.restrict S) := ⟨by simpa using hS⟩
  have hint : IntegrableOn G Fs μ := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hQ _ hG.enorm (hP (fun z => ‖z‖ₑ) (by simp))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hint, ?_⟩
  have hH : Measurable fun p : Y × Z => G (Φ p.1 p.2) := hG.comp hΦ
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ z, ‖L z‖ ≤ ‖z‖) →
      L (∫ x in Fs, G x ∂μ) = c * L (∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν) := by
    intro L hL
    have hLm : Measurable L := L.continuous.measurable
    have h1 := clm_integral_integral ν (m.restrict S) _ hH hfin L
    have h2 := integral_integral_eq_pos_sub_neg ν (m.restrict S)
      (fun p : Y × Z => L (G (Φ p.1 p.2))) (hLm.comp hH)
      (lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hL _)) hfin)
    have h3 := hQ (fun x => ENNReal.ofReal (L (G x))) (hLm.comp hG).ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (L z)) (by simp))
    have h4 := hQ (fun x => ENNReal.ofReal (-L (G x))) (hLm.comp hG).neg.ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (-L z)) (by simp))
    simp only at h1 h2
    rw [h1, h2, ← L.integral_comp_comm hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hint), h3, h4,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, mul_sub]
  apply Complex.ext
  · have := key Complex.reCLM (fun z => by simpa using Complex.abs_re_le_norm z)
    simpa using this
  · have := key Complex.imCLM (fun z => by simpa using Complex.abs_im_le_norm z)
    simpa using this

end GlobalTheory.FoldIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralKernelLiftsFubiniSigmaFinite
section
open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace GlobalTheory.AbsFubini

variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]

lemma lintegral_mul_le_sqrt (ν : Measure Y) {a₁ a₂ : Y → ℝ≥0∞} (h₁ : Measurable a₁) (h₂ : Measurable a₂) :
    ∫⁻ y, a₁ y * a₂ y ∂ν ≤
      (∫⁻ y, a₁ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a₂ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two h₁.aemeasurable
    h₂.aemeasurable
  simpa only [Pi.mul_apply] using h

lemma sqrt_le_of_sq_le {I N : ℝ≥0∞} (h : I ≤ N ^ 2) : I ^ (1 / (2:ℝ)) ≤ N := by
  calc I ^ (1 / (2:ℝ)) ≤ (N ^ 2) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = N := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma lintegral_prod_split {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂)) (y : Y) :
    (∫⁻ x₁, a₁ x₁ y ∂μ₁) * (∫⁻ x₂, a₂ x₂ y ∂μ₂) = ∫⁻ p : X₁ × X₂, a₁ p.1 y * a₂ p.2 y ∂μ₁.prod μ₂ := by
  have m₁ : Measurable fun x => a₁ x y := ha₁.comp (measurable_id.prodMk measurable_const)
  have m₂ : Measurable fun x => a₂ x y := ha₂.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_prod_mul (f := fun x => a₁ x y) (g := fun x => a₂ x y) m₁.aemeasurable
    m₂.aemeasurable).symm

lemma core {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞} {b₁ : X₁ → ℝ≥0∞} {b₂ : X₂ → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) {N₁ : X₁ → ℝ≥0∞} {N₂ : X₂ → ℝ≥0∞}
    (hN₁ : ∀ x, ∫⁻ y, a₁ x y ^ 2 ∂ν ≤ N₁ x ^ 2) (hN₂ : ∀ x, ∫⁻ y, a₂ x y ^ 2 ∂ν ≤ N₂ x ^ 2) :
    ∫⁻ y, (∫⁻ x₁, a₁ x₁ y * b₁ x₁ ∂μ₁) * (∫⁻ x₂, a₂ x₂ y * b₂ x₂ ∂μ₂) ∂ν ≤
      (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) := by
  have hA₁ : Measurable (Function.uncurry fun x y => a₁ x y * b₁ x) :=
    ha₁.mul (hb₁.comp measurable_fst)
  have hA₂ : Measurable (Function.uncurry fun x y => a₂ x y * b₂ x) :=
    ha₂.mul (hb₂.comp measurable_fst)

  set n₁ : X₁ → ℝ≥0∞ := fun x => (∫⁻ y, a₁ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₁
  set n₂ : X₂ → ℝ≥0∞ := fun x => (∫⁻ y, a₂ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₂
  have mn₁ : Measurable n₁ :=
    ((ha₁.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have mn₂ : Measurable n₂ :=
    ((ha₂.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have nN₁ : ∀ x, n₁ x ≤ N₁ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₁ x)
  have nN₂ : ∀ x, n₂ x ≤ N₂ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₂ x)
  have hsplit := lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁ hA₂
  simp only [hsplit]
  have hG : Measurable (Function.uncurry fun (y : Y) (p : X₁ × X₂) =>
      a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2)) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => a₁ z.2.1 z.1 * b₁ z.2.1 :=
      hA₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => a₂ z.2.2 z.1 * b₂ z.2.2 :=
      hA₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact e₁.mul e₂
  rw [lintegral_lintegral_swap hG.aemeasurable]
  calc ∫⁻ p : X₁ × X₂, ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν ∂μ₁.prod μ₂
      ≤ ∫⁻ p : X₁ × X₂, (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) ∂μ₁.prod μ₂ := by
        refine lintegral_mono fun p => ?_
        have m₁ : Measurable fun y => a₁ p.1 y := ha₁.comp (measurable_const.prodMk measurable_id)
        have m₂ : Measurable fun y => a₂ p.2 y := ha₂.comp (measurable_const.prodMk measurable_id)
        calc ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν
            = ∫⁻ y, (b₁ p.1 * b₂ p.2) * (a₁ p.1 y * a₂ p.2 y) ∂ν := by
              congr 1; funext y; ring
          _ = (b₁ p.1 * b₂ p.2) * ∫⁻ y, a₁ p.1 y * a₂ p.2 y ∂ν := lintegral_const_mul _ (m₁.mul m₂)
          _ ≤ (b₁ p.1 * b₂ p.2) * (n₁ p.1 * n₂ p.2) :=
              by gcongr; exact lintegral_mul_le_sqrt ν m₁ m₂
          _ = (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) := by ring
    _ = (∫⁻ x, n₁ x * b₁ x ∂μ₁) * (∫⁻ x, n₂ x * b₂ x ∂μ₂) :=
        lintegral_prod_mul (f := fun x => n₁ x * b₁ x) (g := fun x => n₂ x * b₂ x)
          (mn₁.mul hb₁).aemeasurable (mn₂.mul hb₂).aemeasurable
    _ ≤ (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) :=
        by
          gcongr with x x
          · exact nN₁ x
          · exact nN₂ x

lemma memLp_lift {k : X₁ → Y → ℂ} {u : X₁ → ℂ} (hk : Measurable (Function.uncurry k))
    (hu : Measurable u) {N : X₁ → ℝ≥0∞} (hN : ∀ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂ν ≤ N x ^ 2)
    (hfin : ∫⁻ x, N x * ‖u x‖ₑ ∂μ₁ ≠ ⊤) :
    MemLp (fun y => ∫ x, k x y * u x ∂μ₁) 2 ν := by
  have hF : Measurable fun q : Y × X₁ => k q.2 q.1 * u q.2 :=
    (hk.comp (measurable_snd.prodMk measurable_fst)).mul (hu.comp measurable_snd)
  have hsm : StronglyMeasurable fun y => ∫ x, k x y * u x ∂μ₁ :=
    hF.stronglyMeasurable.integral_prod_right'
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
    hsm.aestronglyMeasurable]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hA : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hb : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₁) (ν := ν) hA hA hb hb hN hN
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin hfin) (le_trans ?_ hc)
  refine lintegral_mono fun y => ?_
  have h1 : ‖∫ x, k x y * u x ∂μ₁‖ₑ ≤ ∫⁻ x, ‖k x y‖ₑ * ‖u x‖ₑ ∂μ₁ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (μ := μ₁) (fun x => k x y * u x)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two]
  exact mul_le_mul' h1 h1

theorem abstract_fubini_two_lifts : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by
  intro X₁ X₂ Y _ _ _ μ₁ μ₂ ν _ _ _ k₁ k₂ u₁ u₂ hk₁ hk₂ hu₁ hu₂ N₁ N₂ hN₁ hN₂ hf₁ hf₂ _ _
  refine ⟨memLp_lift hk₁ hu₁ hN₁ hf₁, memLp_lift hk₂ hu₂ hN₂ hf₂, ?_⟩
  set F : Y → X₁ × X₂ → ℂ := fun y p => k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => k₁ z.2.1 z.1 * u₁ z.2.1 :=
      (hk₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₁.comp (measurable_fst.comp measurable_snd))
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => k₂ z.2.2 z.1 * u₂ z.2.2 :=
      (hk₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₂.comp (measurable_snd.comp measurable_snd))
    exact e₁.mul (Complex.continuous_conj.measurable.comp e₂)
  have hA₁ : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ) := hk₁.enorm
  have hA₂ : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ) := hk₂.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₂) (ν := ν) hA₁ hA₂ hu₁.enorm hu₂.enorm hN₁ hN₂
  have hFi : Integrable (Function.uncurry F) (ν.prod (μ₁.prod μ₂)) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hc
      (ENNReal.mul_lt_top hf₁.lt_top hf₂.lt_top))
    refine lintegral_congr fun y => ?_
    have hA₁' : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ * ‖u₁ x‖ₑ) :=
      hA₁.mul (hu₁.enorm.comp measurable_fst)
    have hA₂' : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ * ‖u₂ x‖ₑ) :=
      hA₂.mul (hu₂.enorm.comp measurable_fst)
    rw [lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁' hA₂' y]
    refine lintegral_congr fun p => ?_
    simp only [Function.uncurry_apply_pair, hFdef, enorm_mul, RCLike.enorm_conj]
  have hpt : ∀ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) =
      ∫ p, F y p ∂μ₁.prod μ₂ := by
    intro y
    rw [← integral_conj]
    exact (integral_prod_mul (fun x => k₁ x y * u₁ x) (fun x => conj (k₂ x y * u₂ x))).symm
  simp_rw [hpt]
  rw [integral_integral_swap hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hFdef]
  have : ∀ y, k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) =
      k₁ p.1 y * conj (k₂ p.2 y) * (u₁ p.1 * conj (u₂ p.2)) := by
    intro y; simp only [map_mul]; ring
  simp_rw [this]
  rw [integral_mul_const]
  ring

end GlobalTheory.AbsFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompact
section
open MeasureTheory

namespace GlobalTheory.ChainOnto

theorem map_restrict_isHaar : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  intro G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK
  have hpm : Measurable p := hp.measurable
  have hAm : MeasurableSet (A : Set G) := hA.measurableSet
  have happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A) := by
    intro S hS
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]

  have hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1}) := by
    intro S
    ext g
    constructor
    · rintro ⟨hgS, hgA⟩
      refine ⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩
      · exact A.mul_mem (A.inv_mem (hiA _)) hgA
      · simp [hpi]
    · rintro ⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩
      refine ⟨?_, A.mul_mem (hiA s) hyA⟩
      simp [hpi, hy1, hs]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro C hC
    rw [happ C hC.isClosed.measurableSet, hpre C]
    exact ((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top
  · intro b
    ext S hS
    rw [Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]
    have : p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, A.mul_mem (hiA b) h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := A.mul_mem (A.inv_mem (hiA b)) h2
        simpa using this
    rw [this, measure_preimage_mul]
  · intro U hU hne
    rw [happ U hU.measurableSet]
    obtain ⟨u, hu⟩ := hne
    exact (hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormPowSubPowLtOne
section
namespace GlobalTheory.UltrametricPowerDifference

theorem norm_pow_sub_pow_lt_one {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K)
    (ha : ‖a‖ ≤ (1 : ℝ)) (hb : ‖b‖ ≤ (1 : ℝ)) (hab : ‖a - b‖ < (1 : ℝ)) (n : ℕ) :
    ‖a ^ n - b ^ n‖ < (1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) ih
    · rw [norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)) hab

end GlobalTheory.UltrametricPowerDifference
end

