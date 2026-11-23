module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffWittTiltRelation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ResidueUnitCoeff

theorem neZero_of_piSys {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) : NeZero e := by
  refine ⟨fun he => ?_⟩
  subst he
  have h := ϖ.seq_zero
  rw [pow_zero, eq_neg_iff_add_eq_zero, add_comm] at h
  exact Nat.cast_add_one_ne_zero l h

theorem exists_bound {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ c : O, ‖algebraMap O K c‖ < 1 → ‖algebraMap O K c‖ ≤ ρ := by
  have : IsNoetherianRing O := isNoetherian_of_tower ℤ_[l] inferInstance
  let m : Ideal O :=
    { carrier := {c | ‖algebraMap O K c‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans_lt hx }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian m : m.FG)
  refine ⟨(s.sup fun g => ‖algebraMap O K g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun c hc => ?_⟩
  · have : s.sup (fun g => ‖algebraMap O K g‖₊) < 1 := by
      refine (Finset.sup_lt_iff zero_lt_one).2 fun g hg => ?_
      have : g ∈ m := hs ▸ Ideal.subset_span hg
      exact (by exact_mod_cast this : ‖algebraMap O K g‖ < 1)
    exact_mod_cast this
  · have key : ∀ c ∈ Submodule.span O (s : Set O),
        ‖algebraMap O K c‖ ≤ (s.sup fun g => ‖algebraMap O K g‖₊ : NNReal) := by
      intro c hc'
      induction hc' using Submodule.span_induction with
      | mem x hx =>
        exact_mod_cast Finset.le_sup (f := fun g => ‖algebraMap O K g‖₊) hx
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans hx
    exact key c (by rw [hs]; exact hc)

end GlobalTheory.ResidueUnitCoeff

namespace GlobalTheory.ResidueUnitCoeff

theorem norm_coeff_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {f : K⟦X⟧} {ρ : ℝ}
    (h0 : 0 ≤ ρ) (hf : ∀ n, ‖coeff n f‖ ≤ ρ) (m n : ℕ) : ‖coeff n (f ^ m)‖ ≤ ρ ^ m := by
  induction m generalizing n with
  | zero => rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (pow_nonneg h0 m) h0 (f := f ^ m) (g := f) (by simpa using ih) (by simpa using hf) n

theorem exists_norm_coeff_eq_one : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  intro l _ a _ e O K _ _ _ _ _ _ _ _ _ t ϖ S _ y c h τ
  have := neZero_of_piSys ϖ
  by_contra hne
  push_neg at hne
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_bound (l := l) (O := O) (K := K)
  have hco : ∀ s k, ‖coeff k (y s τ : K⟦X⟧)‖ ≤ ρ := fun s k => by
    obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 (mem_A.1 (y s τ).2 k)
    have h1 : ‖coeff k (y s τ : K⟦X⟧)‖ < 1 := lt_of_le_of_ne (mem_A.1 (y s τ).2 k) (hne s k)
    rw [← ho] at h1 ⊢
    exact hρ o h1
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl0
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hlpos hρ1
  set N := N0 + 1 with hN
  have hρN : ρ ^ N ≤ ‖(l : K)‖ :=
    (pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ N0)).trans hN0.le
  have hzmem : ∀ s, C (l : K)⁻¹ * (y s τ : K⟦X⟧) ^ N ∈ A O K := fun s n => by
    rw [coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hlpos, mul_one]
    exact (norm_coeff_pow_le hρ0 (hco s) N n).trans hρN
  let z : S → A O K := fun s => ⟨_, hzmem s⟩
  have hz : ∀ s, y s τ ^ N = (l : A O K) * z s := fun s => Subtype.ext (by
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast, z]
    rw [← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_mul])
  let ε : ZMod a → A O K := Pi.single τ 1
  have hpow : ∀ s, (ε * y s) ^ N = (l : ZMod a → A O K) * Pi.single τ (z s) := fun s => by
    funext σ
    rcases eq_or_ne σ τ with rfl | hσ
    · simp [ε, hz]
    · simp [ε, hσ, hN]
  obtain ⟨Φ, hΦi, hΦ⟩ : ∃ Φ : (ZMod a → A O K) →ₐ[O] OW l O, Function.Injective Φ ∧
      ∀ s, inclO l O (ϖ.iTot t K (y s)) = Φ (y s) :=
    ⟨(inclO l O).comp (ϖ.iTot t K), inclO_injective.comp (ϖ.iTot_injective t K), fun _ => rfl⟩
  simp only [hΦ] at h
  have hidem : IsIdempotentElem (Φ ε) := by
    show Φ ε * Φ ε = Φ ε
    rw [← map_mul]
    congr 1
    simp only [ε, ← Pi.single_mul, one_mul]
  have hne0 : Φ ε ≠ 0 := fun h0 => by
    have h1 := congrFun (hΦi (h0.trans (map_zero Φ).symm)) τ
    simp [ε] at h1
  let I : Ideal (OW l O) := Ideal.span {((l : ℕ) : OW l O)}
  have hnil : ∀ s, IsNilpotent (Ideal.Quotient.mk I (Φ ε * Φ (y s))) := fun s => by
    refine ⟨N, ?_⟩
    rw [← map_pow, ← map_mul, ← map_pow, hpow, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hsum : Φ ε = ∑ s, c s * (Φ ε * Φ (y s)) := by
    calc Φ ε = Φ ε * ∑ s, c s * Φ (y s) := by rw [h, mul_one]
      _ = ∑ s, c s * (Φ ε * Φ (y s)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  have hmk : Ideal.Quotient.mk I (Φ ε) = 0 := by
    refine IsIdempotentElem.eq_zero_of_isNilpotent ?_ ?_
    · show _ * _ = _
      rw [← map_mul, hidem.eq]
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
      refine isNilpotent_sum fun s _ => ?_
      rw [map_mul]
      exact (Commute.all _ _).isNilpotent_mul_left (hnil s)
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  have hdvd : ∀ n, Φ ε ∈ Ideal.span {((l : ℕ) : OW l O) ^ n} := fun n => by
    rw [Ideal.mem_span_singleton]
    cases n with
    | zero => exact one_dvd _
    | succ n =>
      rw [← hidem.pow_succ_eq n, ← hx, mul_pow]
      exact dvd_mul_left _ _
  have hcpl := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) ((l : ℕ) : WCb l)
  have e1 : (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) = ((l : ℕ) : OW l O) :=
    map_natCast (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O) l
  rw [e1] at hcpl
  exact hne0 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus ((l : ℕ) : OW l O) (Φ ε) hdvd)

end GlobalTheory.ResidueUnitCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacter
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section
namespace GlobalTheory.UnramZl
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem modEq_of_pow_modEq {l d : ℕ} (hl : 1 < l) (hd : 0 < d) {a b : ℕ}
    (h : l ^ a ≡ l ^ b [MOD l ^ d - 1]) : a ≡ b [MOD d] := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : l ^ d - 1 ∣ l ^ (a + c) - l ^ a :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hl.le hab)).1 h
  rw [pow_add, ← Nat.mul_sub_one] at h1
  have hcop : (l ^ d - 1).Coprime (l ^ a) := by
    apply Nat.Coprime.pow_right
    have h2 : (l ^ d - 1).Coprime (l ^ d) := by
      have : l ^ d = (l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
      conv_rhs => rw [this]
      simp
    exact h2.coprime_dvd_right (dvd_pow_self l hd.ne')
  have h3 := Nat.gcd_eq_left (hcop.dvd_of_dvd_mul_left h1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : l ^ d.gcd c = l ^ d := by
    have := Nat.one_le_pow (d.gcd c) l (by omega)
    have := Nat.one_le_pow d l (by omega)
    omega
  have h5 : d ∣ c := (Nat.pow_right_injective hl h4) ▸ Nat.gcd_dvd_right d c
  exact (Nat.modEq_iff_dvd' hab).2 (by simpa using h5)

variable {l : ℕ} [hl : Fact l.Prime]

theorem lev_pos (n : ℕ) : 0 < l ^ (l ^ n) - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow (pow_pos hl.out.pos n).ne' hl.out.one_lt)

theorem not_dvd_lev (n : ℕ) : ¬ l ∣ l ^ (l ^ n) - 1 := fun h => by
  have h1 : l ∣ l ^ (l ^ n) := dvd_pow_self l (pow_pos hl.out.pos n).ne'
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.out.pos)] at h2
  exact hl.out.not_dvd_one h2

def Acts (g : GQ l) (n a : ℕ) : Prop :=
  ∀ ζ : Om l, ζ ^ (l ^ (l ^ n) - 1) = 1 → g ζ = ζ ^ (l ^ a)

theorem exists_prim (n : ℕ) : ∃ ξ : Om l, IsPrimitiveRoot ξ (l ^ (l ^ n) - 1) := by
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) _

theorem Acts.uniq {g : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts g n b) :
    a ≡ b [MOD l ^ n] := by
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  have h := (ha ξ hξ.pow_eq_one).symm.trans (hb ξ hξ.pow_eq_one)
  rw [(hξ.isOfFinOrder (lev_pos n).ne').pow_eq_pow_iff_modEq, ← hξ.eq_orderOf] at h
  exact modEq_of_pow_modEq hl.out.one_lt (pow_pos hl.out.pos n) h

theorem Acts.down {g : GQ l} {n a : ℕ} (ha : Acts g (n + 1) a) : Acts g n a := fun ζ hζ => by
  obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one l (pow_dvd_pow l (Nat.le_succ n))
  exact ha ζ (by rw [hc, pow_mul, hζ, one_pow])

theorem Acts.mul {g h : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts h n b) :
    Acts (g * h) n (a + b) := fun ζ hζ => by
  rw [AlgEquiv.mul_apply, hb ζ hζ, map_pow, ha ζ hζ, ← pow_mul, pow_add]

theorem exists_acts (g : GQ l) (n : ℕ) : ∃ a, Acts g n a :=
  gal_root g (lev_pos n) (not_dvd_lev n)

theorem exists_deg (g : GQ l) :
    ∃ x : ℤ_[l], ∀ n a, Acts g n a → PadicInt.toZModPow n x = (a : ZMod (l ^ n)) := by
  choose a ha using exists_acts g
  have hdv : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - a i := fun i => by
    have := ((ha i).uniq (ha (i + 1)).down).dvd
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv), fun n b hb => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv n, Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 ((ha n).uniq hb)

def deg (g : GQ l) : ℤ_[l] := (exists_deg g).choose

theorem deg_spec {g : GQ l} {n a : ℕ} (h : Acts g n a) :
    PadicInt.toZModPow n (deg g) = (a : ZMod (l ^ n)) := (exists_deg g).choose_spec n a h

theorem deg_mul (g h : GQ l) : deg (g * h) = deg g + deg h := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  obtain ⟨a, ha⟩ := exists_acts g n
  obtain ⟨b, hb⟩ := exists_acts h n
  rw [map_add (f := _), deg_spec ha, deg_spec hb, deg_spec (ha.mul hb), Nat.cast_add]

theorem deg_eq_nat {g : GQ l} {a : ℕ} (h : ∀ n, Acts g n a) : deg g = a := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [deg_spec (h n), map_natCast]

theorem deg_one : deg (1 : GQ l) = 0 := by
  simpa using deg_eq_nat (g := (1 : GQ l)) (a := 0) fun n ζ _ => by simp

theorem deg_pow (g : GQ l) (N : ℕ) : deg (g ^ N) = N * deg g := by
  induction N with
  | zero => simp [deg_one]
  | succ N ih => rw [pow_succ, deg_mul, ih]; push_cast; ring

theorem continuous_deg : Continuous (deg : GQ l → ℤ_[l]) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt l hε
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) ξ).preimage (continuous_const_mul g⁻¹)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ MulAction.stabilizer (GQ l) ξ by simp)] with h hh
  have h1 : (g⁻¹ * h) ξ = ξ := hh
  have h2 : h ξ = g ξ := by
    conv_rhs => rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := exists_acts g n
  have hb : Acts h n a := fun ζ hζ => by
    rw [← ha ζ hζ]
    obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, map_pow, h2]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    deg_spec ha, deg_spec hb, sub_self]

theorem deg_inertia {g : GQ l} (h : ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) : deg g = 0 := by
  simpa using deg_eq_nat (g := g) (a := 0) fun n ζ hζ => by
    let a : OO l := ⟨ζ, (norm_root (lev_pos n) hζ).le⟩
    have ha : a ^ (l ^ (l ^ n) - 1) = 1 := Subtype.ext hζ
    have := res_inj (lev_pos n) (not_dvd_lev n) (a := galO g a) (b := a)
      (by rw [← map_pow, ha, map_one]) ha ((res_eq_iff _ _).2 (h ζ a.2))
    rw [pow_zero, pow_one]
    exact congrArg Subtype.val this

theorem exists_deg_eq_one : ∃ g : GQ l, deg g = 1 := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  simpa using deg_eq_nat (g := g) (a := 1) fun n ζ hζ => by
    let c : ↥(MaximalUnramifiedExtension l) :=
      ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨_, lev_pos n, not_dvd_lev n, hζ⟩⟩
    have := hσ c _ (lev_pos n) (not_dvd_lev n) (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this, pow_one]; rfl

theorem exists_unramified_character : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    ∃ δ : ↥(GK K) → ℚ_[l], Continuous δ ∧ (∀ g h, δ (g * h) = δ g + δ h) ∧
      (∀ g ∈ IK K, δ g = 0) ∧ ∃ g, δ g ≠ 0 := by
  intro l _ K
  refine ⟨fun g => (deg (g : GQ l) : ℚ_[l]),
    continuous_subtype_val.comp (continuous_deg.comp continuous_subtype_val),
    fun g h => by simp [deg_mul], fun g hg => ?_, ?_⟩
  · have : deg (g : GQ l) = 0 := by
      unfold IK at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => exact deg_inertia hx
      | one => exact deg_one
      | mul x y _ _ hx hy => rw [Subgroup.coe_mul, deg_mul, hx, hy, add_zero]
      | inv x _ hx =>
        have := deg_mul ((x⁻¹ : ↥(GK K)) : GQ l) x
        rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, deg_one, hx, add_zero] at this
        exact this.symm
    simp [this]
  · obtain ⟨φ, hφ⟩ := exists_deg_eq_one (l := l)
    haveI := K.2
    haveI : Finite (GQ l ⧸ GK K) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K.1)
    obtain ⟨N, hN, -, hm⟩ := (GK K).exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite φ
    refine ⟨⟨φ ^ N, hm⟩, ?_⟩
    simp [deg_pow, hφ, hN.ne']

end GlobalTheory.UnramZl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorTraceOneFiniteLevel
section
namespace GlobalTheory.UnramifiedCrys

theorem exists_witt_trace_one : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  intro p hp G _ R _ _ _ _ ρ m hm hfin
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  obtain ⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by
    by_contra hc
    push Not at hc
    have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      funext θ
      simp only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]
      exact hc θ) (QuotientGroup.mk 1)
    exact one_ne_zero this
  have hθm : (θ : R) ^ p ^ m = θ := θ.2
  have hsum : ∀ (f : G → WittVector p R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  set t := ∑ x : G ⧸ N, ρ x.out θ with ht
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  have hθN : ∀ n ∈ N, WittVector.map (ρ n).toRingHom (WittVector.teichmuller p (θ : R)) =
      WittVector.teichmuller p (θ : R) := fun n hn => by
    rw [WittVector.map_teichmuller]
    congr 1
    exact hn θ hθm
  set T := ∑ x : G ⧸ N, WittVector.map (ρ x.out).toRingHom (WittVector.teichmuller p (θ : R))
    with hT
  have hTg : ∀ g, WittVector.map (ρ g).toRingHom T = T := fun g => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum, ← hsum (fun g => WittVector.map (ρ g).toRingHom
      (WittVector.teichmuller p (θ : R))) (fun g n hn => by
        simp only [wittMap_mul, hθN n hn]) g]
    simp only [wittMap_mul]
  have hT0 : WittVector.constantCoeff T = t := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum, ht]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WittVector.map_teichmuller, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    rfl
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have hmem : T * WittVector.teichmuller p (t ^ (p ^ m - 2)) - 1 ∈
      Ideal.span {(p : WittVector p R)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      map_mul, map_one, hT0, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      mul_comm, hu, sub_self]
  have hunit : IsUnit T := by
    have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hmem) 1
    rw [mul_one, sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨S, hS⟩ := hunit.exists_left_inv
  have hSg : ∀ g, WittVector.map (ρ g).toRingHom S = S := fun g => by
    have h2 := congrArg (WittVector.map (ρ g).toRingHom) hS
    rw [map_mul, hTg, map_one] at h2
    exact hunit.mul_right_cancel (h2.trans hS.symm)
  refine ⟨S * WittVector.teichmuller p (θ : R), fun g hg => ?_, ?_⟩
  · rw [map_mul, hSg, hθN g hg]
  · rw [finsum_eq_sum_of_fintype]
    simp only [map_mul, hSg]
    rw [← Finset.mul_sum, ← hT, hS]

end GlobalTheory.UnramifiedCrys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCrystalCoordCoeffMem
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CrysInteg

theorem mem_of_semiBC {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (g : N →+ Q) (H : AddSubgroup Q) (hg : ∀ (r : B) (x : M), g (r • u x) ∈ H) (y : N) : g y ∈ H := by
  have hspan : y ∈ Submodule.span B (Set.range u) := by
    have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have key : ∀ z ∈ Submodule.span B (Set.range u), ∀ r : B, g (r • z) ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact fun r => hg r x
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact H.zero_mem
    | add z w _ _ hz hw =>
      intro r
      rw [smul_add, map_add (f := _)]
      exact add_mem (hz r) (hw r)
    | smul s z _ hz =>
      intro r
      rw [smul_smul]
      exact hz _
  have := key y hspan 1
  rwa [one_smul] at this

def divSub {R σ ι : Type} [CommRing R] (S : Subring R) (τ : σ) (i : ι) (k : ℕ) :
    AddSubgroup (σ → ι → R⟦X⟧) where
  carrier := {v | (k.factorial : R) * coeff k (v τ i) ∈ S}
  add_mem' {v w} hv hw := by
    change (k.factorial : R) * coeff k (v τ i + w τ i) ∈ S
    rw [map_add (f := _), mul_add]
    exact add_mem hv hw
  zero_mem' := by
    change (k.factorial : R) * coeff k (0 : R⟦X⟧) ∈ S
    rw [map_zero, mul_zero]
    exact zero_mem _
  neg_mem' {v} hv := by
    change (k.factorial : R) * coeff k (-(v τ i)) ∈ S
    rw [map_neg, mul_neg]
    exact neg_mem hv

theorem factorial_mul_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hc PP p J hJ lam hsm htr y τ i k
  refine mem_of_semiBC (EE.tr_bc p) lam (divSub (S O K e).toSubring τ i k) (fun r x => ?_) y
  change (k.factorial : K⟦X⟧) * coeff k (lam (r • EE.tr p x) τ i) ∈ S O K e
  rw [hsm, htr, PowerSeries.coeff_mul_C, ← mul_assoc]
  exact mul_mem (hJ τ r k) (A_le_S l e (frob_mem_A l (mem_tot.1 (hc x) (τ - 1) i)))

end GlobalTheory.BKGal.CrysInteg
end
end

