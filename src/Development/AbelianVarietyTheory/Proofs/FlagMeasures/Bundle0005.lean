module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMapMulRightEqSmul
section
open MeasureTheory

namespace GlobalTheory.IwasawaShape

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem lintegral_mul_left_of_map {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by
  have e := lintegral_map (μ := ρ) hf (measurable_const_mul p)
  rw [h] at e
  exact e.symm

theorem exists_map_mul_right_eq_smul (P : Subgroup G) (hP : MeasurableSet (P : Set G)) (ρ : Measure G)
    [SigmaFinite ρ] (h0 : ρ (P : Set G)ᶜ = 0) (hinv : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) (l : G) (hl : l ∈ P) :
    ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * l) = D • ρ := by
  classical
  have e : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hP
  have : MeasurableMul₂ P := ⟨e.measurable_comp_iff.1
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))⟩
  have : MeasurableInv P := ⟨e.measurable_comp_iff.1 measurable_subtype_coe.inv⟩
  set ρ' : Measure P := ρ.comap Subtype.val with hρ'
  have hmap : ρ'.map Subtype.val = ρ := by
    rw [hρ', e.map_comap, Subtype.range_coe_subtype, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 h0
  have inj : ∀ α β : Measure P, α.map Subtype.val = β.map Subtype.val → α = β := fun α β h => by
    rw [← e.comap_map α, ← e.comap_map β, h]
  have : SigmaFinite ρ' :=
    SigmaFinite.of_map ρ' measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  have : ρ'.IsMulLeftInvariant := ⟨fun s => inj _ _ (by
    rw [Measure.map_map measurable_subtype_coe (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : P => s * x) = (fun g : G => (s : G) * g) ∘ Subtype.val := rfl
    rw [hc, ← Measure.map_map (measurable_const_mul _) measurable_subtype_coe, hmap, hinv s s.2])⟩
  let l' : P := ⟨l, hl⟩
  set ν' : Measure P := ρ'.map (fun x => x * l') with hν'
  have : ν'.IsMulLeftInvariant := ⟨fun s => by
    rw [hν', Measure.map_map (measurable_const_mul s) (measurable_mul_const l')]
    have hc : ((fun x : P => s * x) ∘ fun x => x * l') = (fun x => x * l') ∘ (fun x => s * x) := by
      funext x; simp [Function.comp, mul_assoc]
    rw [hc, ← Measure.map_map (measurable_mul_const l') (measurable_const_mul s), map_mul_left_eq_self]⟩
  have : SigmaFinite ν' := SigmaFinite.of_map ν' (measurable_mul_const l'⁻¹).aemeasurable (by
    rw [hν', Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have hc : ((fun x : P => x * l'⁻¹) ∘ fun x => x * l') = id := by funext x; simp
    rw [hc, Measure.map_id]; infer_instance)
  have hρT' : ρ' (Subtype.val ⁻¹' T) = ρ T := by
    rw [hρ', e.comap_apply, Set.image_preimage_eq_inter_range]
    exact measure_inter_conull (by rw [Subtype.range_coe_subtype]; exact h0)
  have hEq := measure_eq_div_smul ν' ρ' (s := Subtype.val ⁻¹' T) (by rw [hρT']; exact hT0)
    (by rw [hρT']; exact hT1)
  set D := ν' (Subtype.val ⁻¹' T) / ρ' (Subtype.val ⁻¹' T) with hD
  have hmapD : ρ.map (fun g => g * l) = D • ρ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_map (measurable_mul_const l) measurable_subtype_coe]
    have hc : ((fun g : G => g * l) ∘ Subtype.val) = Subtype.val ∘ (fun x : P => x * l') := rfl
    rw [hc, ← Measure.map_map measurable_subtype_coe (measurable_mul_const l'), ← hν', hEq,
      Measure.map_smul D e.measurable.aemeasurable, hmap]
  have huniv : (ρ.map fun g => g * l) Set.univ ≠ 0 := by
    rw [Measure.map_apply (measurable_mul_const l) MeasurableSet.univ, Set.preimage_univ]
    exact fun h => hT0 (measure_mono_null (Set.subset_univ _) h)
  have hD0 : D ≠ 0 := by
    intro h
    apply huniv
    rw [hmapD, h, zero_smul, Measure.coe_zero, Pi.zero_apply]
  have hD1 : D ≠ ⊤ := by
    intro h
    have : SigmaFinite (ρ.map fun g => g * l) :=
      SigmaFinite.of_map _ (measurable_mul_const l⁻¹).aemeasurable (by
        rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
        have hc : ((fun g : G => g * l⁻¹) ∘ fun g => g * l) = id := by funext x; simp
        rw [hc, Measure.map_id]; infer_instance)
    obtain ⟨n, hn⟩ : ∃ n, (ρ.map fun g => g * l) (spanningSets (ρ.map fun g => g * l) n) ≠ 0 := by
      by_contra hne
      push Not at hne
      apply huniv
      rw [← iUnion_spanningSets (ρ.map fun g => g * l)]
      exact measure_iUnion_null hne
    have hlt := measure_spanningSets_lt_top (ρ.map fun g => g * l) n
    set Sn := spanningSets (ρ.map fun g => g * l) n
    rw [hmapD, Measure.smul_apply, smul_eq_mul, h] at hn hlt
    rcases eq_or_ne (ρ Sn) 0 with h' | h'
    · exact hn (by rw [h', mul_zero])
    · rw [ENNReal.top_mul h'] at hlt
      exact lt_irrefl _ hlt
  exact ⟨D, hD0, hD1, hmapD⟩

theorem exists_lintegral_eq_mul (μ ρ κ : Measure G) [SigmaFinite μ] [SFinite ρ] [IsProbabilityMeasure κ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) (P K : Set G)
    (hKl : ∀ k ∈ K, κ.map (fun g => k * g) = κ) (hPl : ∀ p ∈ P, ρ.map (fun g => p * g) = ρ)
    (hPr : ∀ p ∈ P, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * p) = D • ρ)
    (hdec : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (T : Set G) (hT : MeasurableSet T)
    (hTK : ∀ k ∈ K, ∀ g, k⁻¹ * g ∈ T ↔ g ∈ T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
  classical
  have hind : Measurable (T.indicator (1 : G → ENNReal)) := measurable_one.indicator hT
  have ind_ne_top : ∀ x, T.indicator (1 : G → ENNReal) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hLm : ∀ φ : G → ENNReal, Measurable φ →
      Measurable fun h => T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ :=
    fun φ hφ => (hind.comp measurable_inv).mul
      ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.2 * y.1.1 * y.2)).lintegral_prod_right').lintegral_prod_right'

  have key : ∀ h : G, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ = D * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
    intro h
    obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec h
    obtain ⟨D, hD0, hDt, hD⟩ := hPr p0 hp0
    refine ⟨D, hD0, hDt, fun φ hφ => ?_⟩
    have hF : Measurable fun x => ∫⁻ k, φ (x * k) ∂κ := (hφ.comp measurable_mul).lintegral_prod_right'
    have e1 : ∀ q, ∫⁻ k, φ (q * (p0 * k0) * k) ∂κ = ∫⁻ k, φ (q * p0 * k) ∂κ := by
      intro q
      have := lintegral_mul_left_of_map (hKl k0 hk0) (fun k => φ (q * p0 * k))
        (hφ.comp (measurable_const_mul _))
      simpa only [mul_assoc] using this
    simp_rw [e1]
    have := lintegral_map (μ := ρ) hF (measurable_mul_const p0)
    rw [hD, lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm

  have mix : ∀ φ : G → ENNReal, Measurable φ →
      ρ T * ∫⁻ g, φ g ∂μ = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
    intro φ hφ
    have s1 : ∫⁻ g, φ g ∂μ = ∫⁻ g, ∫⁻ k, φ (g * k) ∂κ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g k => φ (g * k)) (by exact (hφ.comp measurable_mul).aemeasurable)]
      simp_rw [lintegral_mul_right_eq_self]
      rw [lintegral_const, measure_univ, mul_one]
    have s2 : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) ∂ρ = ρ T := by
      intro g
      obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec g
      have e : ∀ q, T.indicator (1 : G → ENNReal) ((p0 * k0)⁻¹ * q) = T.indicator 1 (p0⁻¹ * q) := by
        intro q
        have hm : (p0 * k0)⁻¹ * q ∈ T ↔ p0⁻¹ * q ∈ T := by
          rw [mul_inv_rev, mul_assoc]; exact hTK k0 hk0 _
        simp only [Set.indicator_apply, hm, Pi.one_apply]
      simp_rw [e]
      have := lintegral_mul_left_of_map (hPl p0 hp0) (fun x => T.indicator (1 : G → ENNReal) (p0⁻¹ * x))
        (hind.comp (measurable_const_mul _))
      simp only [inv_mul_cancel_left] at this
      rw [← this, lintegral_indicator_one hT]
    have hW1 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ρ T * ∫⁻ g, φ g ∂μ := by
      have e : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ
          = ρ T * ∫⁻ k, φ (g * k) ∂κ := by
        intro g
        exact (lintegral_mul_const _ (hind.comp (measurable_const_mul g⁻¹))).trans (congrArg (· * _) (s2 g))
      simp_rw [e]
      rw [lintegral_const_mul' _ _ hT1, ← s1]
    have hmF : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) (x.1⁻¹ * x.2) * ∫⁻ k, φ (x.1 * k) ∂κ :=
      (hind.comp (measurable_fst.inv.mul measurable_snd)).mul
        (((hφ.comp measurable_mul).lintegral_prod_right').comp measurable_fst)
    have hmG : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) x.2⁻¹ * ∫⁻ k, φ (x.1 * x.2 * k) ∂κ :=
      (hind.comp measurable_snd.inv).mul
        ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.1 * y.1.2 * y.2)).lintegral_prod_right')
    have hW2 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g q => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
        ∫⁻ k, φ (g * k) ∂κ) (by exact hmF.aemeasurable)]
      have e : ∀ q, ∫⁻ g, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂μ
          = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ k, φ (q * h * k) ∂κ ∂μ := by
        intro q
        refine (lintegral_mul_left_eq_self (μ := μ) (fun g => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
          ∫⁻ k, φ (g * k) ∂κ) q).symm.trans ?_
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      simp_rw [e]
      rw [lintegral_lintegral_swap (f := fun q h => T.indicator (1 : G → ENNReal) h⁻¹ *
        ∫⁻ k, φ (q * h * k) ∂κ) (by exact hmG.aemeasurable)]
      exact lintegral_congr fun h => lintegral_const_mul' _ _ (ind_ne_top _)
    rw [← hW1, hW2]

  obtain ⟨S, hS, hS0, hS1⟩ : ∃ S, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply hμ
    have hz : ∀ n, μ (spanningSets μ n) = 0 := fun n => by
      by_contra hn
      exact (measure_spanningSets_lt_top μ n).ne (hne _ (measurableSet_spanningSets μ n) hn)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
    exact measure_iUnion_null hz
  have hφ0 : Measurable (S.indicator (1 : G → ENNReal)) := measurable_one.indicator hS
  have hμS : ∫⁻ g, S.indicator (1 : G → ENNReal) g ∂μ = μ S := lintegral_indicator_one hS
  have mix0 := mix _ hφ0
  rw [hμS] at mix0
  have hL0 : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ 0 := by
    intro h0
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ = 0 := by
      refine (lintegral_congr fun h => ?_).trans lintegral_zero
      obtain ⟨D, -, -, hD⟩ := key h
      rw [hD _ hφ0, h0, mul_zero, mul_zero]
    rw [this] at mix0
    exact mul_ne_zero hT0 hS0 mix0
  have hLt : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ ⊤ := by
    intro ht
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ
        = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤ := by
      rw [← (lintegral_mul_const ⊤ (hind.comp measurable_inv) : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ⊤ ∂μ = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤)]
      refine lintegral_congr fun h => ?_
      obtain ⟨D, hD0, -, hD⟩ := key h
      rw [hD _ hφ0, ht, ENNReal.mul_top hD0]
    rw [this] at mix0
    rcases eq_or_ne (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) 0 with hz | hz
    · rw [hz, zero_mul] at mix0
      exact mul_ne_zero hT0 hS0 mix0
    · rw [ENNReal.mul_top hz] at mix0
      exact ENNReal.mul_ne_top hT1 hS1 mix0
  refine ⟨μ S / ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ,
    (ENNReal.div_pos_iff.2 ⟨hS0, hLt⟩).ne', ENNReal.div_ne_top hS1 hL0, fun φ hφ => ?_⟩
  have E : ρ T * ((∫⁻ g, φ g ∂μ) * ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ)
      = ρ T * (μ S * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ) := by
    rw [← mul_assoc]
    rw [mix _ hφ]
    rw [← lintegral_mul_const _ (hLm _ hφ)]
    rw [← mul_assoc]
    rw [mix0]
    rw [← lintegral_mul_const _ (hLm _ hφ0)]
    refine lintegral_congr fun h => ?_
    obtain ⟨D, -, -, hD⟩ := key h
    rw [hD _ hφ, hD _ hφ0]
    ring
  have E' := (ENNReal.mul_right_inj hT0 hT1).1 E
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  exact (ENNReal.eq_div_iff hL0 hLt).2 (by rw [mul_comm]; exact E')

end GlobalTheory.IwasawaShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableFundamentalDomain
section
namespace GlobalTheory.MeasurableFundamentalDomain

open Set Topology

theorem exists_small_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : Subgroup G)
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a * b⁻¹ = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hfin : ((K ∩ (↑Γ : Set G)) \ {1}).Finite := (hΓ K hK).subset sdiff_subset
  have hcl : IsClosed ((K ∩ (↑Γ : Set G)) \ {1}) := hfin.isClosed
  have h1 : ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) :=
    hcl.isOpen_compl.mem_nhds (by simp)
  have hW : K ∩ ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) := Filter.inter_mem hK1 h1
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv hW
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro a ha b hb hab
  have h := hVW a (interior_subset ha) b (interior_subset hb)
  rw [div_eq_mul_inv] at h
  by_contra hne
  exact h.2 ⟨⟨h.1, hab⟩, hne⟩

theorem exists_measurable_fundamental_domain {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by
  classical
  obtain ⟨V, hVo, hV1, hV⟩ := exists_small_open Γ hΓ
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq G
  let U : ℕ → Set G := fun n => {y | y * (g n)⁻¹ ∈ V}
  let S : ℕ → Set G := fun n => ⋃ γ ∈ Γ, {y | γ * y ∈ U n}
  have hUo : ∀ n, IsOpen (U n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_biUnion fun γ _ => (hUo n).preimage (continuous_const.mul continuous_id)
  have hS : ∀ n y, y ∈ S n ↔ ∃ γ ∈ Γ, γ * y ∈ U n := by
    intro n y
    simp [S]
  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ y, γ * y ∈ S n → y ∈ S n := by
    intro n γ hγ y hy
    obtain ⟨δ, hδ, h⟩ := (hS _ _).1 hy
    exact (hS _ _).2 ⟨δ * γ, Γ.mul_mem hδ hγ, by rwa [mul_assoc]⟩
  refine ⟨⋃ n, (U n \ ⋃ m ∈ Set.Iio n, S m), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (hUo n).measurableSet.diff (isOpen_biUnion fun m _ => hSo m).measurableSet
  · intro y
    have hex : ∃ n, y ∈ S n := by
      have ho : IsOpen {x : G | y * x⁻¹ ∈ V} :=
        hVo.preimage (continuous_const.mul continuous_inv)
      obtain ⟨n, hn⟩ := hg.exists_mem_open ho ⟨y, by simpa using hV1⟩
      exact ⟨n, (hS _ _).2 ⟨1, Γ.one_mem, by rw [one_mul]; exact hn⟩⟩
    obtain ⟨γ, hγ, h⟩ := (hS _ _).1 (Nat.find_spec hex)
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, h, ?_⟩⟩
    intro hm
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hm
    exact Nat.find_min hex hm (hSinv m γ hγ y hy)
  · intro γ hγ y hy hγy
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hγy
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact absurd (mem_iUnion₂.2 ⟨n, h, (hS _ _).2
          ⟨γ⁻¹, Γ.inv_mem hγ, by rwa [inv_mul_cancel_left]⟩⟩) hm'
      · exact h
      · exact absurd (mem_iUnion₂.2 ⟨m, h, (hS _ _).2 ⟨γ, hγ, hm⟩⟩) hn'
    subst hnm
    have e : (γ * y * (g n)⁻¹) * (y * (g n)⁻¹)⁻¹ = γ := by group
    have := hV _ hm _ hn (by rw [e]; exact hγ)
    rwa [e] at this

end GlobalTheory.MeasurableFundamentalDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
section
open MeasureTheory

namespace GlobalTheory


open MeasureTheory in
open scoped ENNReal in
open scoped Pointwise in
theorem _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  let K := CompactExhaustion.choice G
  set a : ℕ → ℝ≥0∞ := fun n => ν (j ⁻¹' (K n * (K n)⁻¹)) with ha_def
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    (hj.isCompact_preimage ((K.isCompact n).mul (K.isCompact n).inv)).measure_lt_top.ne
  set c : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n / (a n + 1) with hc_def
  have hc_pos : ∀ n, c n ≠ 0 := fun n =>
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp [ha n])).ne'
  have hc_le : ∀ n, c n ≤ 2⁻¹ ^ n := fun n =>
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' le_add_self)
  have hca : ∀ n, c n * a n ≤ 2⁻¹ ^ n := fun n => by
    calc c n * a n ≤ c n * (a n + 1) := by gcongr; exact le_self_add
      _ = 2⁻¹ ^ n := ENNReal.div_mul_cancel (by simp) (by simp [ha n])
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (K.isCompact n).isClosed.measurableSet
  set f : G → ℝ≥0∞ := fun y => ∑' n, (K n).indicator (fun _ => c n) y with hf_def
  have hf : Measurable f := Measurable.tsum fun n => measurable_const.indicator (hKm n)
  have hf_pos : ∀ y, f y ≠ 0 := by
    intro y
    obtain ⟨n, hn⟩ := K.exists_mem y
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hc_pos n)) ?_)
    calc c n = (K n).indicator (fun _ => c n) y := (Set.indicator_of_mem hn (fun _ => c n)).symm
      _ ≤ f y := by
        change (K n).indicator (fun _ => c n) y ≤ ∑' i, (K i).indicator (fun _ => c i) y
        exact le_tsum (fun i => (K i).indicator (fun _ => c i) y) n
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  have hmeas : ∀ g, Measurable fun h => f (j h * g) := fun g => hf.comp (hjg g)
  set F : G → ℝ≥0∞ := fun g => ∫⁻ h, f (j h * g) ∂ν with hF_def
  have hF : Measurable F :=
    Measurable.lintegral_prod_right' (ν := ν) (f := fun p : G × H => f (j p.2 * p.1))
      (hf.comp ((hj.continuous.measurable.comp measurable_snd).mul measurable_fst))
  have hF_inv : ∀ h' g, F (j h' * g) = F g := by
    intro h' g
    have e : ∀ h, f (j h * (j h' * g)) = (fun k => f (j k * g)) (h * h') := by
      intro h; simp only [map_mul, mul_assoc]
    calc F (j h' * g) = ∫⁻ h, (fun k => f (j k * g)) (h * h') ∂ν := lintegral_congr e
      _ = F g := lintegral_mul_right_eq_self (μ := ν) (fun k => f (j k * g)) h'
  have hF0 : ∀ g, F g ≠ 0 := by
    intro g h0
    rw [hF_def, lintegral_eq_zero_iff (hmeas g), Filter.EventuallyEq, ae_iff] at h0
    have : ν Set.univ = 0 := by simpa [hf_pos] using h0
    exact NeZero.ne ν (Measure.measure_univ_eq_zero.1 this)
  have hFtop : ∀ g, F g ≠ ∞ := by
    intro g
    obtain ⟨m, hm⟩ := K.exists_mem g
    have hterm : ∀ n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
        ≤ (1 + a m) * 2⁻¹ ^ n := by
      intro n
      have hsub : (fun h => j h * g) ⁻¹' K n ⊆ j ⁻¹' (K (max n m) * (K (max n m))⁻¹) := by
        intro h hh
        have h1 : j h * g ∈ K (max n m) := K.subset (le_max_left n m) hh
        have h2 : g ∈ K (max n m) := K.subset (le_max_right n m) hm
        have e : j h = (j h * g) * g⁻¹ := by group
        rw [Set.mem_preimage, e]
        exact Set.mul_mem_mul h1 (Set.inv_mem_inv.2 h2)
      have hle : ν ((fun h => j h * g) ⁻¹' K n) ≤ a n + a m := by
        refine (measure_mono hsub).trans ?_
        rcases le_total n m with hnm | hnm
        · rw [max_eq_right hnm]; exact le_add_self
        · rw [max_eq_left hnm]; exact le_self_add
      calc ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
          = ∫⁻ h, ((fun h => j h * g) ⁻¹' K n).indicator (fun _ => c n) h ∂ν := rfl
        _ = c n * ν ((fun h => j h * g) ⁻¹' K n) :=
            lintegral_indicator_const (hjg g (hKm n)) _
        _ ≤ c n * (a n + a m) := by gcongr
        _ = c n * a n + c n * a m := mul_add _ _ _
        _ ≤ 2⁻¹ ^ n + 2⁻¹ ^ n * a m := by gcongr; exacts [hca n, hc_le n]
        _ = (1 + a m) * 2⁻¹ ^ n := by ring
    have hF_eq : F g = ∑' n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν :=
      lintegral_tsum fun n =>
        ((measurable_const.indicator (hKm n)).comp (hjg g)).aemeasurable
    rw [hF_eq]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by simp [ha m]) (by simp)
  refine ⟨fun g => f g * (F g)⁻¹, hf.mul hF.inv, fun g => ?_⟩
  simp only [hF_inv]
  rw [lintegral_mul_const _ (hmeas g)]
  exact ENNReal.mul_inv_cancel (hF0 g) (hFtop g)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
end

