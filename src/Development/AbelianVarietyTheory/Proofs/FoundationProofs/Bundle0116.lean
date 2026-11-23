module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.H3.UnRoot

lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected

lemma eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) {τ : ℂ} (hτ : τ ∈ Hs) :
    ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  have h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z := Filter.Germ.coe_eq.mp h
  rw [Filter.eventually_iff, mem_codiscreteWithin] at h'
  have hd := Filter.disjoint_principal_right.mp (h' τ hτ)
  have hH : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [hH, hd] with z hz1 hz2
  by_contra hne
  exact hz2 ⟨hz1, hne⟩

lemma eq_nhds_of_punctured {F G : ℂ → ℂ} {τ : ℂ} (hF : ContinuousAt F τ) (hG : ContinuousAt G τ)
    (h : ∀ᶠ z in 𝓝[≠] τ, F z = G z) : F =ᶠ[𝓝 τ] G := by
  have hτ : F τ = G τ :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))
  have h2 := eventually_nhdsWithin_iff.mp h
  filter_upwards [h2] with z hz
  by_cases hz' : z = τ
  · subst hz'; exact hτ
  · exact hz hz'

lemma order_ne_top {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) ≠ 0) {τ : ℂ} (hτ : τ ∈ Hs) :
    analyticOrderAt a τ ≠ ⊤ := by
  intro htop
  apply h0
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ
    (analyticOrderAt_eq_top.mp htop)
  have : ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z :=
    Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'
  rw [← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr this

lemma germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma num_ne_zero (X : Tower Ω ε) (f : X.Kˣ) {a b : ℂ → ℂ} (hb : (b : Mero) ≠ 0)
    (hf : X.an (f : X.K) * (b : Mero) = (a : Mero)) : (a : Mero) ≠ 0 := by
  intro h
  apply hb
  have e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc (b : Mero) = X.an ((f⁻¹ : X.Kˣ) : X.K) * (X.an (f : X.K) * b) := by rw [← mul_assoc, e, one_mul]
    _ = 0 := by rw [hf, h, mul_zero]

end GlobalTheory.KZ.H3.UnRoot

namespace GlobalTheory.KZ.H3.UnRoot

theorem exists_isRoot_of_mem_Un : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), JHol X →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  intro Ω _ _ ε X hj m hm f hf
  obtain ⟨a0, b0, ha0, hb0, hb0ne, hf0⟩ := X.an_mero (f : X.K)
  have ha0ne : (a0 : Mero) ≠ 0 := num_ne_zero X f hb0ne hf0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ :=
    fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ
  have hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞) := by
    intro τ hτ
    obtain ⟨W, hW, hWmem⟩ := _root_.GlobalTheory.KZ.H3.exists_place_at_point Ω ε X hj τ hτ
    obtain ⟨g, hg⟩ := hf W hW
    set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu
    have hgm : (g : X.K) ^ (m' + 1) ≠ 0 := pow_ne_zero _ g.ne_zero
    have hune : u ≠ 0 := div_ne_zero f.ne_zero hgm
    have huW : u ∈ W := (W.valuation_le_one_iff u).mp hg.le
    have huW' : u⁻¹ ∈ W := (W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])
    obtain ⟨φ, hφ, hφa⟩ := (hWmem u).mp huW
    obtain ⟨ψ, hψ, hψa⟩ := (hWmem u⁻¹).mp huW'

    have hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]
    have hφτ : φ τ ≠ 0 := by
      have e : φ τ * ψ τ = 1 := (eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const
        (eventually_of_germ_eq hφψ hτ)).self_of_nhds
      intro h0
      rw [h0, zero_mul] at e
      exact zero_ne_one e

    obtain ⟨a1, b1, ha1, hb1, hb1ne, hg1⟩ := X.an_mero (g : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := num_ne_zero X g hb1ne hg1
    have hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1) := by
      rw [← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]
    have hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero) := by
      simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
      rw [← hf0, ← hg1, hfu, hφ]
      ring
    have hev := eq_nhds_of_punctured
      ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _))
      ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt)
      (eventually_of_germ_eq hgerm hτ)
    have hcong := analyticOrderAt_congr hev
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ),
      analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ),
      analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ),
      hφa.analyticOrderAt_eq_zero.mpr hφτ] at hcong
    obtain ⟨oA0, orbitMap_conj_smul_zero⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)
    obtain ⟨oB0, eB0⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)
    obtain ⟨oA1, orbitMap_conj_smul_one⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)
    obtain ⟨oB1, eB1⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)
    rw [← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1] at hcong
    have heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0 := by
      simp only [nsmul_eq_mul, zero_add] at hcong
      exact_mod_cast hcong
    have hdvd : (m' + 1) ∣ oA0 + m' * oB0 :=
      Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        push_cast at this ⊢
        linear_combination this⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ),
      ← orbitMap_conj_smul_zero, ← eB0, ← hk]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨r, hr, hrm⟩ := _root_.GlobalTheory.KZ.H3.uhp_root (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord
  refine ⟨r, b0, hr, hb0, hb0ne, ?_⟩
  have e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero) :=
    germ_eq_of_eqOn fun z hz => by simpa using hrm z hz
  simp only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢
  rw [e1, ← hf0]
  ring

end GlobalTheory.KZ.H3.UnRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRoot
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_natCast (m k : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ZMod m).val : ℕ) : ℂ) / (m : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_natCast]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk : 2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((k % m : ℕ) : ℂ) / (m : ℂ) + ((k / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    push_cast
    field_simp
  rw [hk, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_of_isRoot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f →
    IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ n x f a b hx hr
  obtain ⟨G1, -, G3, -, G5⟩ := _root_.GlobalTheory.KZ.Germ.main
  obtain ⟨M1, -, -, M4, -, -⟩ := _root_.GlobalTheory.KZ.mob_laws
  obtain ⟨ha, hb, hb0, hab0⟩ := hr
  have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  obtain ⟨M, hM, hlev⟩ := X.level (f : X.K)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (f : X.K)) (fun φ => ⟨φ, rfl⟩)
  have hab : (φ : Mero) * (b : Mero) ^ (l ^ n) = (a : Mero) ^ (l ^ n) := by rw [← hφ]; exact hab0
  have key : ∀ δ ∈ CongruenceSubgroup.Gamma M, ∃ k : ℕ, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) * (a z * b (mob (ofSL δ) z)) := by
    intro δ hδ
    have hφg : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = (φ : Mero) := by
      rw [← X.an_sl (ofSL δ) (f : X.K) φ hφ, hlev δ hδ, hφ]
    have dag : DifferentiableOn ℂ (fun z => a (mob (ofSL δ) z)) Hs :=
      ha.comp (M4 _) (fun z hz => M1 _ z hz)
    have dbg : DifferentiableOn ℂ (fun z => b (mob (ofSL δ) z)) Hs :=
      hb.comp (M4 _) (fun z hz => M1 _ z hz)
    have h1 : ((φ * b ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab
    have h2 : (((fun z => φ (mob (ofSL δ) z)) * (fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((fun z => a (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := G3 (ofSL δ) _ _ h1
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, hφg] at h2
    have h3 : ((((fun z => a (mob (ofSL δ) z)) * b) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((a * fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Filter.Germ.coe_mul, Filter.Germ.coe_mul]
      linear_combination (-(b : Mero) ^ (l ^ n)) * h2 +
        ((fun z => b (mob (ofSL δ) z) : ℂ → ℂ) : Mero) ^ (l ^ n) * hab
    have h4 := (G1 _ _ ((dag.mul hb).pow _) ((ha.mul dbg).pow _)).1 h3
    obtain ⟨k, hk⟩ := G5 (l ^ n) ((fun z => a (mob (ofSL δ) z)) * b) (a * fun z => b (mob (ofSL δ) z)) hm
      (dag.mul hb) (ha.mul dbg) h4
    exact ⟨k, hk⟩
  classical
  let χ : SL(2, ℤ) → ZMod (l ^ n) := fun δ =>
    if h : δ ∈ CongruenceSubgroup.Gamma M then ((key δ h).choose : ZMod (l ^ n)) else 0
  refine ⟨χ, f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab0⟩, fun δ hδ z hz => ?_⟩
  have hc : ((l : ℂ) ^ n) = ((l ^ n : ℕ) : ℂ) := by push_cast; rfl
  simp only [χ, dif_pos hδ]
  rw [hc, exp_val_natCast (l ^ n) _ hm]
  exact (key δ hδ).choose_spec z hz

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMeromorphicRootOfMemModularFunctionTowerUn
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ.MeroRoot

theorem valAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ,
      X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point X τ hτ

theorem repAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ)
    (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := GlobalTheory.T.an_meromorphicAt_upperHalfPlane X x φ hφ τ hτ

theorem rootHs (h : ℂ → ℂ) (m : ℕ) (hm : 0 < m) (hh : DifferentiableOn ℂ h Hs)
    (hdiv : ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := _root_.GlobalTheory.RootHs.rootHs h m hm hh hdiv

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_codisc {F G : ℂ → ℂ} (hFG : F =ᶠ[codiscreteWithin Hs] G) {τ : ℂ} (hτ : τ ∈ Hs) :
    F =ᶠ[𝓝[≠] τ] G := by
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hFG) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := nhdsWithin_le_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem germ_rep (x : Mero) : ∃ φ : ℂ → ℂ, x = (φ : Mero) := by
  induction x using Filter.Germ.inductionOn with
  | h φ => exact ⟨φ, rfl⟩

theorem wt_dvd {m : ℕ} (hm : 0 < m) {k : ℤ} {u v : WithTop ℤ}
    (hk : (k : WithTop ℤ) = (m : WithTop ℤ) * u + (m : WithTop ℤ) * v) : (m : ℤ) ∣ k := by
  have hm0 : (m : WithTop ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  cases u with
  | top => rw [WithTop.mul_top hm0, WithTop.top_add] at hk; exact absurd hk (WithTop.coe_ne_top)
  | coe p =>
    cases v with
    | top => rw [WithTop.mul_top hm0, WithTop.add_top] at hk; exact absurd hk (WithTop.coe_ne_top)
    | coe q =>
      have : k = (m : ℤ) * p + (m : ℤ) * q := by exact_mod_cast hk
      exact ⟨p + q, by rw [this]; ring⟩

theorem orders_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (f : X.Kˣ) (hf : f ∈ X.Un m) (a b : ℂ → ℂ) (hb : DifferentiableOn ℂ b Hs)
    (hab : X.an (f : X.K) * (b : Mero) = (a : Mero)) :
    ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt (fun z => a z * b z ^ (m - 1)) τ = (k : WithTop ℤ) → (m : ℤ) ∣ k := by
  intro τ hτ k hk
  obtain ⟨W, hW, hWv⟩ := valAt X τ hτ
  obtain ⟨g, hg⟩ := hf W hW
  obtain ⟨φf, hφf⟩ := germ_rep (X.an (f : X.K))
  obtain ⟨φg, hφg⟩ := germ_rep (X.an (g : X.K))
  obtain ⟨ψ, hψ⟩ := germ_rep (X.an ((f : X.K) / (g : X.K) ^ m))
  have hψ0 : meromorphicOrderAt ψ τ = 0 := hWv _ hg ψ hψ
  have hfm := (repAt X _ φf hφf τ hτ).1
  have hgm := (repAt X _ φg hφg τ hτ).1
  have hψm := (repAt X _ ψ hψ τ hτ).1
  have hbm : MeromorphicAt b τ :=
    ((hb.analyticOnNhd isOpen_Hs) τ hτ).meromorphicAt

  have e1 : (φf : Mero) = ((fun z => ψ z * φg z ^ m : ℂ → ℂ) : Mero) := by
    have : (f : X.K) = ((f : X.K) / (g : X.K) ^ m) * (g : X.K) ^ m := by
      rw [div_mul_cancel₀]; exact pow_ne_zero _ g.ne_zero
    rw [← hφf, this, map_mul, map_pow, hψ, hφg]; rfl
  have e1' : φf =ᶠ[𝓝[≠] τ] (fun z => ψ z * φg z ^ m) := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e1) hτ
  have e2 : ((fun z => a z * b z ^ (m - 1) : ℂ → ℂ) : Mero) = ((fun z => φf z * b z ^ m : ℂ → ℂ) : Mero) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show ((a * b ^ n : ℂ → ℂ) : Mero) = ((φf * b ^ (n + 1) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, ← hab, hφf, pow_succ]
    ring
  have e2' := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e2) hτ
  have o1 : meromorphicOrderAt φf τ = (m : WithTop ℤ) * meromorphicOrderAt φg τ := by
    rw [meromorphicOrderAt_congr e1']
    rw [show (fun z => ψ z * φg z ^ m) = ψ * φg ^ m from rfl, meromorphicOrderAt_mul hψm (hgm.pow m),
      meromorphicOrderAt_pow hgm, hψ0, zero_add]
  rw [meromorphicOrderAt_congr e2', show (fun z => φf z * b z ^ m) = φf * b ^ m from rfl,
    meromorphicOrderAt_mul hfm (hbm.pow m), meromorphicOrderAt_pow hbm, o1] at hk
  exact wt_dvd hm hk.symm

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem exists_mero_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧
      (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f hf
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero (f : X.K)
  obtain ⟨g, hg, hgm⟩ := rootHs (fun z => a z * b z ^ (m - 1)) m hm (ha.mul (hb.pow _))
    (orders_dvd X m hm f hf a b hb hab)
  refine ⟨g, b, hg, hb, hb0, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : ((fun z => a z * b z ^ n : ℂ → ℂ) : Mero) = ((fun z => g z ^ (n + 1) : ℂ → ℂ) : Mero) := by
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simpa using (hgm z hz).symm
  rw [pow_succ, mul_comm ((b : Mero) ^ n), ← mul_assoc, hab, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow,
    ← Filter.Germ.coe_mul]
  exact e

end GlobalTheory.KZ.MeroRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsShiftedLtClassMin
section
noncomputable section

namespace GlobalTheory.ClassMin

open QuadraticMap Module
open scoped Pointwise

section Class

variable {X : Type*} [AddCommGroup X]

variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

theorem shifted_zsmul (hN : N ≠ 0) (ν : X →+ ℝ) (μ : X) :
    Q (N • μ) / N + ν (N • μ) = N * (Q μ + ν μ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [QuadraticMap.map_smul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  field_simp

theorem shifted_zsmul_nonneg (hN : 0 < N) {ν : X →+ ℝ} (h : ∀ μ, 0 ≤ Q μ + ν μ) (μ : X) :
    0 ≤ Q (N • μ) / N + ν (N • μ) := by
  rw [shifted_zsmul hN.ne']
  exact mul_nonneg (by exact_mod_cast hN.le) (h μ)

theorem shifted_lt_add_zsmul {c : ℝ} (hc : 0 ≤ c) (hN : 1 + 2 * c < N) {ν : X →+ ℝ} {e μ : X}
    (hμ : 0 < Q μ) (hF : 0 ≤ Q μ / N + ν μ) (h : |polar Q e μ| ≤ c * polar Q μ μ) :
    Q e / N + ν e < Q (e + N • μ) / N + ν (e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : Q (e + N • μ) / N + ν (e + N • μ) = Q e / N + ν e +
      (polar Q e μ + (N - 1) * Q μ + N * (Q μ / N + ν μ)) := by
    rw [map_add_zsmul, map_add (f := _), map_zsmul, zsmul_eq_mul]
    field_simp
    ring
  rw [polar_self, two_smul, abs_le] at h
  have h1 := mul_pos (sub_pos.2 hN) hμ
  have h2 := mul_nonneg hN0.le hF
  rw [e1]
  nlinarith [h.1]

theorem exists_basis_neg {ι : Type*} (e : Basis ι ℤ X) {ν : X →+ ℝ} (hν : ν ≠ 0) :
    ∃ i, ν (e i) < 0 ∨ ν (-e i) < 0 := by
  by_contra h
  push Not at h
  refine hν (AddMonoidHom.toIntLinearMap_injective (e.ext fun i => ?_))
  have h2 := (h i).2
  rw [map_neg] at h2
  simpa using le_antisymm (by linarith) (h i).1

theorem realExtension_eq_realExt (Q : QuadraticMap ℤ X ℝ) : realExtension Q = realExt Q :=
  eq_realExt Q _ (realExtension_one_tmul Q)

end Class

section Main

variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ} {N : ℤ} {d : ℕ}

theorem exists_shifted_lt (hd : finrank ℤ X = d) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * d * (2 : ℝ) ^ ((d : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  have hP := posDef_of_posDef_realExt hQ
  have hc : (0 : ℝ) ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  rw [mul_assoc] at hN
  have hN1 : (1 : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have : (1 : ℤ) < N := by exact_mod_cast hN1
    omega
  have hN0 : (0 : ℝ) < N := by linarith
  suffices H : ∃ α : X, (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N by
    obtain ⟨α, h1, h2⟩ := H
    refine ⟨α, ?_, h1, h2⟩
    rintro w rfl
    have h3 := h2 (-w)
    rw [smul_neg, add_neg_cancel, map_zero, zero_div] at h3
    exact h3.not_ge (shifted_zsmul_nonneg (by omega) h w)
  obtain ⟨a, ha⟩ := exists_global_min (realExtension_eq_realExt Q ▸ hQ) ν hN0
  by_cases hX : ∃ u, a = N • u
  · obtain ⟨u, rfl⟩ := hX
    have hF : ∀ x, 0 ≤ Q x / N + ν x := fun x => (shifted_zsmul_nonneg (by omega) h u).trans (ha x)
    obtain ⟨e, he, -⟩ := exists_reduced_basis_pairing_coord hd Q hQ
    obtain ⟨v, hv, hvp⟩ : ∃ v, ν v < 0 ∧
        ∀ μ, |polar Q v μ| ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) * polar Q μ μ := by
      obtain ⟨i, hi | hi⟩ := exists_basis_neg e hν
      · exact ⟨_, hi, he i⟩
      · exact ⟨_, hi, fun μ => by rw [polar_neg_left, abs_neg]; exact he i μ⟩
    refine ⟨v, fun w hw => shifted_lt_add_zsmul hc hN (hP w hw) (hF w) (hvp w), fun w => ?_⟩
    refine (add_lt_of_neg_right _ hv).trans_le (div_le_div_of_nonneg_right ?_ hN0.le)
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (lt_add_smul_of_abs_polar_le Q hc (by linarith) (hP w hw) (hvp w)).1.le
  · refine ⟨a, fun w => lt_of_global_min hP ν hN2 ha, fun w => ?_⟩
    have h0 := ha 0
    rw [map_zero, map_zero, zero_div, add_zero] at h0
    refine h0.trans_lt (div_pos (hP _ fun hw => hX ⟨-w, ?_⟩) hN0)
    rw [smul_neg, eq_neg_iff_add_eq_zero, hw]

theorem exists_shifted_lt_of_le {g : ℕ} (hg : finrank ℤ X ≤ g) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * g * (2 : ℝ) ^ ((g : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  refine exists_shifted_lt rfl hQ (lt_of_le_of_lt ?_ hN) hν h
  have := pairing_const_mono hg
  rw [mul_assoc, mul_assoc]
  linarith

end Main

section Matrix

open ReciprocityTheory.ReducedBases (SameClass IsMinInClass IsUniqueMinInClass)

end Matrix

end GlobalTheory.ClassMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobiusStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧ ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.HermFN.hermite | exact GlobalTheory.HermFN.hermite | (intros; apply GlobalTheory.HermFN.hermite <;> assumption)
end

