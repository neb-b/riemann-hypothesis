module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import GroundTheory.LocalFields.Bundle0006
public import GroundTheory.LocalFields.UnramifiedGalois

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LiftExp

variable {l : ℕ} [hl : Fact l.Prime]

theorem one_add_pow_expand (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring

theorem norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt

theorem zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h

theorem norm_pow_sub_one_of (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)

theorem norm_pow_coprime (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this

theorem norm_pow_prime (j : ℕ) (hj : Lev l j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ l - 1‖ = (l : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
  have hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ)) := by simp
  have hj1 := hj.1
  push_cast
  by_cases h2 : l = 2
  · have := hj.2 h2
    exact norm_pow_sub_one_of j hj.1 u hu l 1 0 hn
      (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      (by omega) (by omega)
  · have h3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
    obtain ⟨m, hm⟩ := hl.out.dvd_choose_self (k := 2) two_ne_zero h3
    refine norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)
    rw [hm, Nat.cast_mul, norm_mul, hn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih

theorem norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hl.out.ne_zero) hm0,
    Nat.multiplicity_prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp

theorem norm_zpow_sub_one : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← Nat.padicValNat_def, ← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp

end GlobalTheory.Cyc.LiftExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSu
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TildeTest

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ
  set T : A.K → A.K → ℂ := fun c u => A.tilde μK ψ φ' c u with hTdef
  have hslice : ∀ c, IsTest (fun u => T c u) := by
    intro c
    have hnd := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1
    have h := (_root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 μK hμ
      (fun b => φ' (b, c)) (GlobalTheory.TestFn.slice_test φ' hφ c)
    have heq : (fun u => T c u) = fourB μK (fun x y => ψ ((Algebra.traceForm F A.K) x y)) (fun b => φ' (b, c)) := by
      funext u
      simp [hTdef, Et.tilde, fourB, Et.psiK, Algebra.traceForm_apply, mul_comm]
    rw [heq]
    exact h
  obtain ⟨V, hV, hVf⟩ := GlobalTheory.TestFn.unif_const (A.K × A.K) φ' hφ
  set V₂ : Set A.K := {v | ((0 : A.K), v) ∈ V} with hV₂def
  have hV₂ : V₂ ∈ 𝓝 (0 : A.K) := by
    have hc : Continuous (fun v : A.K => ((0 : A.K), v)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by rw [show ((0 : A.K), (0 : A.K)) = (0 : A.K × A.K) from rfl]; exact hV)
  have hshift : ∀ c c', c' - c ∈ V₂ → ∀ u, T c' u = T c u := by
    intro c c' hcc u
    simp only [hTdef, Et.tilde]
    congr 1; funext b
    have := hVf (b, c) (0, c' - c) hcc
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
    rw [this]
  have hnbhd : ∀ c : A.K, {c' | c' - c ∈ V₂} ∈ 𝓝 c := by
    intro c
    have hc : Continuous (fun c' : A.K => c' - c) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  have hlc : IsLocallyConstant (fun p : A.K × A.K => T p.1 p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c₀, u₀⟩
    have hu : {u | T c₀ u = T c₀ u₀} ∈ 𝓝 u₀ := ((hslice c₀).1.isOpen_fiber _).mem_nhds rfl
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (hnbhd c₀) hu] with p hp
    rw [hshift c₀ p.1 hp.1 p.2]; exact hp.2
  refine ⟨hlc, ?_⟩
  have hC₂ : IsCompact (Prod.snd '' tsupport φ') := hφ.2.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hC₂.elim_nhds_subcover (fun c => {c' | c' - c ∈ V₂}) (fun c _ => hnbhd c)
  have hK : IsCompact ((Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u)) :=
    hC₂.prod (t.isCompact_biUnion fun c _ => (hslice c).2)
  have hzero : ∀ c ∉ Prod.snd '' tsupport φ', ∀ u, T c u = 0 := by
    intro c hc u
    have h0 : ∀ b, φ' (b, c) = 0 := fun b => image_eq_zero_of_notMem_tsupport (fun h => hc ⟨(b, c), h, rfl⟩)
    simp [hTdef, Et.tilde, h0]
  have hsupp : Function.support (fun p : A.K × A.K => T p.1 p.2) ⊆
      (Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u) := by
    rintro ⟨c, u⟩ hp
    have hc : c ∈ Prod.snd '' tsupport φ' := by
      by_contra hc; exact hp (hzero c hc u)
    refine ⟨hc, ?_⟩
    obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hc)
    refine Set.mem_iUnion₂.mpr ⟨c', hc't, subset_tsupport _ ?_⟩
    show T c' u ≠ 0
    rw [← hshift c' c hcc' u]; exact hp
  have hclosed : IsClosed (Function.support (fun p : A.K × A.K => T p.1 p.2)) := by
    have := (hlc.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext p; simp [Function.mem_support]
  have hts : tsupport (fun p : A.K × A.K => T p.1 p.2) = Function.support (fun p : A.K × A.K => T p.1 p.2) :=
    hclosed.closure_eq
  unfold HasCompactSupport
  rw [hts]
  exact hK.of_isClosed_subset hclosed hsupp

end GlobalTheory.JR.TildeTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctions
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp.PtTest

theorem hasCompactSupport_of_loc {X : Type} [TopologicalSpace X] (g : X → ℂ) (hg : IsLocallyConstant g)
    (C : Set X) (hC : IsCompact C) (hz : ∀ x ∉ C, g x = 0) : HasCompactSupport g := by
  have hcl : IsClosed (Function.support g) := by
    have := (hg.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext; simp [Function.mem_support]
  show IsCompact (closure (Function.support g))
  rw [hcl.closure_eq]
  exact hC.of_isClosed_subset hcl fun x hx => by
    by_contra h
    exact hx (hz x h)

theorem slice_eventually {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : ∀ᶠ a' in 𝓝 a, (fun b => Φ (a', b)) = fun b => Φ (a, b) := by
  have hC : IsCompact (Prod.snd '' tsupport Φ) := hΦ.2.isCompact.image continuous_snd
  have h := hC.eventually_forall_of_forall_eventually (x₀ := a) (P := fun a' b => Φ (a', b) = Φ (a, b))
    fun y _ => by
      have h1 : ∀ᶠ z in 𝓝 (a, y), Φ z = Φ (a, y) := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y)
      have hc : Continuous fun z : X × Y => (a, z.2) := continuous_const.prodMk continuous_snd
      have h2 : ∀ᶠ z in 𝓝 (a, y), Φ (a, z.2) = Φ (a, y) :=
        (hc.tendsto (a, y)).eventually ((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y))
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
  filter_upwards [h] with a' ha'
  funext b
  by_cases hb : b ∈ Prod.snd '' tsupport Φ
  · exact ha' b hb
  · have h0 : ∀ c, Φ (c, b) = 0 := fun c => by
      by_contra hne
      exact hb ⟨(c, b), subset_tsupport _ hne, rfl⟩
    rw [h0, h0]

theorem slice_isTest {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : IsTest fun b => Φ (a, b) := by
  have hl : IsLocallyConstant fun b => Φ (a, b) :=
    hΦ.1.comp_continuous (continuous_const.prodMk continuous_id)
  refine ⟨hl, hasCompactSupport_of_loc _ hl _ (hΦ.2.isCompact.image continuous_snd) fun b hb => ?_⟩
  by_contra hne
  exact hb ⟨(a, b), subset_tsupport _ hne, rfl⟩

end GlobalTheory.JR.Hyp.PtTest


open GlobalTheory.JR.Hyp.PtTest in
theorem GlobalTheory.JR.Hyp.pt_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν Φ hΦ

  let β : LinearMap.BilinForm F A.K := LinearMap.comp (Algebra.traceForm F A.K) (LinearMap.mulLeft F (x : A.K))
  have hβapp : ∀ u b, β u b = Algebra.trace F A.K ((x : A.K) * u * b) := fun u b => by simp [β, Algebra.traceForm_apply, mul_assoc]
  have hsymm : β.IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    ring_nf
  have htr := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1
  have hsepL : ∀ u : A.K, (∀ b, β u b = 0) → u = 0 := fun u hu => by
    have h1 : (x : A.K) * u = 0 := htr.1 _ fun b => by simpa [hβapp] using hu b
    simpa using congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h1
  have hnd : β.Nondegenerate := ⟨hsepL, fun b hb => hsepL b fun u => by
    have := hb u
    rw [hβapp] at this
    rw [hβapp, mul_right_comm]; exact this⟩
  have hF : ∀ f : A.K → ℂ, IsTest f → IsTest (fourB ν (kx A ψ (x : A.K)) f) := fun f hf =>
    (_root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.K β hsymm hnd).2 ν hν f hf
  have hG : ∀ p, Hyp.pt A ν ψ x Φ p = fourB ν (kx A ψ (x : A.K)) (fun b => Φ (p.1, b)) p.2 := fun p => rfl
  have hloc : IsLocallyConstant (Hyp.pt A ν ψ x Φ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a, u⟩
    have h1 := slice_eventually Φ hΦ a
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hF _ (slice_isTest Φ hΦ a)).1 u
    rw [nhds_prod_eq]
    filter_upwards [h1.prod_mk h2] with q hq
    rw [hG, hG, hq.1]
    exact hq.2
  refine ⟨hloc, ?_⟩
  have hC1 : IsCompact (Prod.fst '' tsupport Φ) := hΦ.2.isCompact.image continuous_fst
  obtain ⟨t, -, ht⟩ := hC1.elim_nhds_subcover (fun a => {a' | (fun b => Φ (a', b)) = fun b => Φ (a, b)})
    fun a _ => slice_eventually Φ hΦ a
  refine hasCompactSupport_of_loc _ hloc
    ((Prod.fst '' tsupport Φ) ×ˢ ⋃ i ∈ t, tsupport (fourB ν (kx A ψ (x : A.K)) fun b => Φ (i, b)))
    (hC1.prod (t.isCompact_biUnion fun i _ => (hF _ (slice_isTest Φ hΦ i)).2.isCompact)) ?_
  rintro ⟨a, u⟩ hq
  by_contra hne
  apply hq
  have ha : a ∈ Prod.fst '' tsupport Φ := by
    by_contra ha
    apply hne
    have h0 : ∀ b, Φ (a, b) = 0 := fun b => by
      by_contra hb
      exact ha ⟨(a, b), subset_tsupport _ hb, rfl⟩
    simp [hG, fourB, h0]
  refine ⟨ha, ?_⟩
  obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (ht ha)
  refine Set.mem_iUnion₂.2 ⟨i, hi, subset_tsupport _ ?_⟩
  rw [hG] at hne
  simp only [Set.mem_setOf_eq] at hai
  rw [Function.mem_support]
  rwa [hai] at hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
section
open GlobalTheory.NL

namespace GlobalTheory.NL.Twist

variable {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]

theorem conv_mem_of_forall (w : PowerSeries L) (g : ℤ → M) (S : Submodule L M) (j : ℤ)
    (h : ∀ i : ℕ, g (j - i) ∈ S) : conv w g j ∈ S := by
  unfold conv
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem)
    (fun i => S.smul_mem _ (h i))

theorem conv_eq_sum (w : PowerSeries L) (g : ℤ → M) (m : ℤ) (hg : ∀ j < m, g j = 0) (k : ℤ) :
    conv w g k = ∑ i ∈ Finset.range ((k - m).toNat + 1), PowerSeries.coeff i w • g (k - i) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  apply hi
  have : g (k - i) = 0 := hg _ (by omega)
  simp [this]

theorem tri (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hSub : Monotone Sub) (y : ℕ)
    (f : ℤ → M) (hf : ∃ m : ℤ, ∀ j < m, f j = 0) (hfS : ∀ j, f j ∈ Sub j) (k : ℤ)
    (hk : ∀ j < k, f j ∈ Sub (j - y)) :
    (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧
    (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧
    (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧
    conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  obtain ⟨m, hm⟩ := hf
  have hg : ∀ j < m, (fun m => u ^ m • f m) j = 0 := fun j hj => by simp [hm j hj]
  refine ⟨⟨m, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · refine (Submodule.mem_bot L).1 (conv_mem_of_forall w _ ⊥ j (fun i => ?_))
    rw [hm _ (by omega), smul_zero]
    exact Submodule.zero_mem _
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) ≤ j) (hfS _)))
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) - y ≤ j - y) (hk _ (by omega))))
  · rw [conv_eq_sum w _ m hg k, Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 w • (u ^ (k - ((0 : ℕ) : ℤ)) • f (k - ((0 : ℕ) : ℤ))) -
        (PowerSeries.constantCoeff w * u ^ k) • f k = 0 := by
      simp [mul_smul]
    rw [add_sub_assoc, h0, add_zero]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
    exact hSub (by omega : k - ((i + 1 : ℕ) : ℤ) - y ≤ k - y) (hk _ (by omega))

end GlobalTheory.NL.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmul
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem fOp_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y,
      fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y =
        ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  intro F E _ _ _ _ U A ψ x μ ω hH s φ _ y
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (MeasScale.unitL A s) = distribHaarChar A.K s ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [MeasScale.unitL, A.star_K, pow_two]
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hinv : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : ∀ y', φ ((s : A.K) • y') * A.kerL ψ x y' y =
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)) (MeasScale.unitL A s • y') := by
    intro y'
    simp only [MeasScale.unitL_smul, Et.kerL]
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]
    congr 4
    linear_combination (star y' * y) * hinv.symm
  simp only [fOp, fourB]
  rw [integral_congr_ae (Eventually.of_forall key),
    MeasScale.integral_units_smul μ (MeasScale.unitL A s)
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)), hN, EtMeas.absK_unit]
  push_cast
  rfl

end GlobalTheory.JR.WeilQuad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTop
section
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IntermediateField

theorem ramificationIndex_eq_one_of_adjoin_range_eq_top (F E K L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L]
    [FiniteDimensional F E] [FiniteDimensional K L] :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 →
      Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
        (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  intro he hadj
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  set m := Nat.card 𝓀[E] - 1 with hm_def
  have hmE : (m : 𝓀[E]) ≠ 0 := natCast_card_residueField_sub_one_ne_zero E
  have hmF : (m : 𝓀[F]) ≠ 0 := fun h0 ↦ hmE (by rw [← map_natCast (algebraMap 𝓀[F] 𝓀[E]), h0, map_zero])
  have hmK : (m : 𝓀[K]) ≠ 0 := fun h0 ↦ hmF ((algebraMap 𝓀[F] 𝓀[K]).injective (by rw [map_natCast, h0, map_zero]))
  have hζ' : IsPrimitiveRoot (algebraMap E L ζ) m := hζ.map_of_injective (algebraMap E L).injective
  have hE : Set.range (algebraMap E L) ⊆ Algebra.adjoin K {algebraMap E L ζ} := by
    rintro _ ⟨e, rfl⟩
    have he' : e ∈ Algebra.adjoin F {ζ} := by
      rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial
    have h1 : algebraMap E L e ∈ (Algebra.adjoin F {ζ}).map (IsScalarTower.toAlgHom F E L) :=
      ⟨e, he', rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin F {(IsScalarTower.toAlgHom F E L) ζ} ≤
        (Algebra.adjoin K {algebraMap E L ζ}).restrictScalars F :=
      Algebra.adjoin_le (by simpa using Algebra.subset_adjoin (R := K) (s := {algebraMap E L ζ}))
    exact h2 h1
  have hadjK : Algebra.adjoin K {algebraMap E L ζ} = ⊤ := by
    rw [eq_top_iff, ← hadj]
    exact Algebra.adjoin_le hE
  have htopK : K⟮algebraMap E L ζ⟯ = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mpr hadjK
  exact ramificationIndex_eq_one_of_adjoin_eq_top hζ' hmK htopK

end GlobalTheory
end

