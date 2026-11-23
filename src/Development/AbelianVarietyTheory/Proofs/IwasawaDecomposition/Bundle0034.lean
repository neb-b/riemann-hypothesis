module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanes
section
open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneExt

theorem norm_le_of_off_hyperplane {n : ℕ} {U V : Set (Fin n → ℂ)} {k : Fin n} {F : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContinuousOn F U)
    (hb : ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖F z‖ ≤ M) : ∀ z ∈ V, z ∈ U → ‖F z‖ ≤ M := by
  intro z hzV hzU
  by_cases hz : z k = 0
  · have hc : ContinuousAt F z := hF.continuousAt (hU.mem_nhds hzU)
    have hupd : Continuous (fun ε : ℂ => Function.update z k ε) := continuous_const.update k continuous_id
    have h0 : Function.update z k 0 = z := by rw [← hz]; exact Function.update_eq_self k z
    have ht : Tendsto (fun ε : ℂ => Function.update z k ε) (𝓝[≠] (0 : ℂ)) (𝓝 z) := by
      have := hupd.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hT : Tendsto (fun ε : ℂ => F (Function.update z k ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (F z)) :=
      hc.tendsto.comp ht
    refine le_of_tendsto hT.norm ?_
    have hm : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), Function.update z k ε ∈ V ∩ U :=
      ht (inter_mem (hV.mem_nhds hzV) (hU.mem_nhds hzU))
    filter_upwards [hm, self_mem_nhdsWithin] with ε hε hne
    exact hb _ hε.1 hε.2 (by simpa using hne)
  · exact hb z hzV hzU hz

theorem extend_finset (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by
  intro n s
  induction s using Finset.induction_on with
  | empty =>
    intro W Φ _ hd _
    refine ⟨Φ, ?_, fun _ _ _ => rfl⟩
    simpa using hd
  | insert j t _ ih =>
    intro W Φ hW hd hb
    have hUeq : {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} = W ∩ ⋂ k ∈ t, {z | z k ≠ 0} := by
      ext z; simp
    have hU : IsOpen {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} := by
      rw [hUeq]
      exact hW.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)
    have hd1 : DifferentiableOn ℂ Φ {z | z ∈ {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} ∧ z j ≠ 0} := by
      refine hd.mono fun z hz => ⟨hz.1.1, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz.2
      · exact hz.1.2 k hk
    obtain ⟨F1, hF1d, hF1e⟩ := hR n _ j Φ hU hd1 (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀.1
      refine ⟨V, hV, M, fun z hzV hzU hzj => hM z hzV hzU.1 ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzj
      · exact hzU.2 k hk)
    have hall : ∀ z : Fin n → ℂ, (∀ k ∈ insert j t, z k ≠ 0) ↔ z j ≠ 0 ∧ ∀ k ∈ t, z k ≠ 0 := by
      intro z; simp
    obtain ⟨F, hFd, hFe⟩ := ih W F1 hW hF1d (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
      refine ⟨interior V, interior_mem_nhds.mpr hV, M, ?_⟩
      intro z hzV hzW ht
      refine norm_le_of_off_hyperplane (k := j) hU isOpen_interior hF1d.continuousOn
        (fun w hwV hwU hwj => ?_) z hzV ⟨hzW, ht⟩
      rw [hF1e w hwU hwj]
      exact hM w (interior_subset hwV) hwU.1 ((hall w).2 ⟨hwj, hwU.2⟩))
    refine ⟨F, hFd, fun z hz hk => ?_⟩
    have hk' := (hall z).1 hk
    rw [hFe z hz hk'.2, hF1e z ⟨hz, hk'.2⟩ hk'.1]

theorem extension_of_parts
    (h1 : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) (h2 : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M) (h3 : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  intro n a ρ Φ m hρ hd hb
  have hset : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0} := by
    ext z; simp
  have hmem : ∀ z : Fin n → ℂ, (∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0) ↔
      ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
    intro z; simp
  obtain ⟨F, hFd, hFe⟩ := extend_finset h3 n (Finset.univ.filter (fun k : Fin n => (k : ℕ) < a))
    (Metric.ball 0 ρ) Φ isOpen_ball (hset ▸ hd) (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := h2 h1 n a ρ Φ m hρ hd hb z₀ hz₀
      exact ⟨V, hV, M, fun z hzV hz hk => hM z hzV hz ((hmem z).1 hk)⟩)
  exact ⟨F, hFd, fun z hz hk => hFe z hz ((hmem z).2 hk)⟩

theorem extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z :=
  extension_of_parts _root_.GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound _root_.GlobalTheory.HyperplaneLocBound.locally_bounded _root_.GlobalTheory.riemann_extension_coordinate_hyperplane

end GlobalTheory.HyperplaneExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  have := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one, one_mul]

end GlobalTheory.LevelChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubsingletonJacquetIff
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

theorem blk_two_stdSum {r t N : ℕ} (h : r + t = N) (a : Fin N) :
    blk (two (stdSum h)) a = decide (r ≤ (a : ℕ)) := by
  obtain ⟨a, rfl⟩ := (stdSum h).surjective a
  rcases a with a | a
  · rw [← two_false, blk_apply, two_false]
    simp [stdSum]
  · rw [← two_true, blk_apply, two_true]
    simp [stdSum]

theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries
end

