module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLattice
section
noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice

theorem integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Integral D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  obtain ⟨-, hfil, hcomp⟩ := _root_.GlobalTheory.IntegralityComp.integralityComputation O K l e a ι η H D hηH hl
  intro w hw
  obtain ⟨⟨y, hyM, rfl⟩, hinv⟩ := (D.desc.mem_Z).1 hw
  obtain ⟨p, hp, f, hf, hEq⟩ := hcomp y hyM
  have hfM := hfil f hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  have hsplit : D.EN y = Ezpow K l e (-(2 * H : ℤ)) • p + Ezpow K l e (-(2 * H : ℤ)) • f := by
    rw [← smul_add, ← hEq, smul_smul, mul_comm, h1, one_smul]
  have hENy : D.EN y ∈ divE l e η D.Man := D.EN_mem_divE (D.M_le_Man hyM)
  have hy' : Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM η := by
    have hA : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM (2 * H) := by
      show E K l e ^ (2 * H) • E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.M
      rw [smul_comm (E K l e ^ (2 * H)) (E K l e ^ η), smul_smul (E K l e ^ (2 * H)), h1, one_smul]
      exact D.upper p hp
    have hB : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.Man := by
      have : Ezpow K l e (-(2 * H : ℤ)) • p = D.EN y - Ezpow K l e (-(2 * H : ℤ)) • f := by
        rw [hsplit, add_sub_cancel_right]
      rw [this, smul_sub]
      exact sub_mem hENy (D.smul_mem_Man (pow_mem (E_mem l e _) η) hfM)
    exact D.mem_M_of_mem_Man hA hB
  refine (D.desc.mem_Z).2 ⟨⟨_, hy', ?_⟩, fun g => ?_⟩
  · rw [BKDat.Lc_cls, hsplit, map_add (f := _), add_eq_left.2 ((D.cls_eq_zero_iff).2 hfM)]
  · rw [D.actPol_Lc, hinv g]

end GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasis
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem zeta_Y'_fine_bound : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hηH hl y hy
  obtain ⟨y₀, ⟨hy₀, -⟩, rfl⟩ := hy
  have hy₀' : E K l e ^ η • y₀ ∈ D.M := hy₀
  show ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta ((X : K⟦X⟧) ^ e • y₀) = _
  obtain ⟨r, hr, hT⟩ := _root_.GlobalTheory.zeta_add_lphi_conn_mem O K l e a ι η H D y₀ hη hηH hl hy₀'
  obtain ⟨w₁, hw₁, hB⟩ := _root_.GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem O K l e a ι η H D y₀ hη hy₀' 0
  obtain ⟨s, hs, f, hf, hD⟩ := GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule O K l e a ι D.toPhiMod (10 * H) (by omega) w₁ hw₁
  have hIC := _root_.GlobalTheory.IntegralityComp.integralityComputation O K l e a ι η H D hηH (by omega)
  obtain ⟨p₁, hp₁, f₁, hf₁, rfl⟩ := hIC.1 s hs
  obtain ⟨p₂, hp₂, f₂, hf₂, rfl⟩ := hIC.1 r hr
  have hsm : ∀ {R : Type} [Semiring R] [Module R (Vec K a ι)] (W : Submodule R (Vec K a ι)) (k : ℕ)
      {v : Vec K a ι}, v ∈ W → (l : K) ^ k • v ∈ W := fun W k v hv => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv _
  refine ⟨p₂ - (l : K) ^ (3 * H - 2 * η) • p₁, sub_mem hp₂ (hsm _ _ hp₁),
    (l : K) ^ (l - 11 * H) • f₂ - (l : K) ^ (2 * H - 2 * η) • ((l : K) ^ (l - 10 * H) • f₁ + f),
    sub_mem (hsm _ _ hf₂) (hsm _ _ (add_mem (hsm _ _ hf₁) hf)), ?_⟩
  simp only [zero_add, pow_one, zero_mul, add_zero, one_mul] at hB
  rw [hD] at hB
  have hl0 : (l : K) ≠ 0 := l_ne_zero l
  have e1 : l - 10 * H = (l - 14 * H) + (3 * H - 2 * η) + (H + 2 * η) := by omega
  have e2 : l - 11 * H = (l - 14 * H) + (2 * H - 2 * η) + (H + 2 * η) := by omega
  have e3 : (l : K) ^ (3 * H) = (l : K) ^ (2 * H - 2 * η) * (l : K) ^ (H + 2 * η) := by
    rw [← pow_add]; congr 1; omega
  rw [e1] at hB
  rw [e1, e2, e3]
  have hz := eq_sub_of_add_eq hT
  rw [hz]
  generalize l - 14 * H = A at *
  generalize 3 * H - 2 * η = B at *
  generalize 2 * H - 2 * η = Dd at *
  generalize H + 2 * η = Cc at *
  generalize (l : K) = x at *
  have hL : D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (x ^ Cc)⁻¹ • (x ^ (A + B + Cc) • (p₁ + f₁) + f) := by
    rw [← hB, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  rw [hL]
  match_scalars <;> field_simp <;> ring

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLe
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.PolarBound

theorem card_le_sum {k V ι : Type} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] {s : ℕ}
    (c : ι → Fin s → V) (N : ι → Submodule k V) (d : ι → ℕ)
    (hd : ∀ i, Module.finrank k (↥(LinearMap.range (Fintype.linearCombination k (c i))) ⧸
      (N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))) ≤ d i)
    (hinj : ∀ t : Fin s → k, (∀ i, ∑ a, t a • c i a ∈ N i) → t = 0) : s ≤ ∑ i, d i := by
  let f := LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ
    (Fintype.linearCombination k (c i)).rangeRestrict
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    refine hinj t fun i => ?_
    have h1 : f t i = 0 := congrFun ht i
    exact (Submodule.Quotient.mk_eq_zero ((N i).submoduleOf
      (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h2
  exact h2.trans (Finset.sum_le_sum fun i _ => hd i)

variable {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem cob_mem (D : ModPG R n (Vc k m)) (y : ZMod n → Vc k m) :
    ((fun i => D.φ i (y (i - 1)) - y i, fun i => D.γ i (y i) - y i) :
      (ZMod n → Vc k m) × (ZMod n → Vc k m)) ∈ herrB D := ⟨y, rfl⟩

theorem gauge_one (D : ModPG R n (Vc k m)) (Dt : TopData n m) (N : Lats k n m)
    (hI : ∀ i, (Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i)
    (hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i) (hN : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i (a : ℕ), a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0)
    (z : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : InZZ D Dt N z.1 z.2) :
    ∃ (z' : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (c : ZMod n → Vc k m), z - z' ∈ herrB D ∧
      ∀ i, D.γ i (z'.1 i) - z'.1 i = D.φ i (z'.2 (i - 1)) - z'.2 i ∧ z'.2 i ∈ sh (Dt.sg l i + 3) (N i) ∧
        c i - z'.1 i ∈ N i ∧
        (Dt.ty i = LType.G → c i ∈ sh (-Dt.w i) (N i) ∧ D.γ i (c i) - c i ∈ sh 1 (N i)) ∧
        (Dt.ty i = LType.Bd → c i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
          D.γ i (c i) - c i ∈ sh (Dt.wst i + 2) (N i)) := by
  obtain ⟨b, g⟩ := z
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  obtain ⟨y, hy, hy'⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
    (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g
    (fun i => (hz i).1) (fun i => (hz i).2.1)).1
  have hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧
      (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i)) := by
    intro i
    cases h : Dt.ty i with
    | G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩
    | Bd =>
      obtain ⟨x, hx, hx'⟩ := ((hz i).2.2.2 h).2
      exact ⟨x, hx, fun h => (by cases h), fun _ => hx'⟩
  choose x hx hxG hxB using hx
  refine ⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)),
    fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩
  · convert cob_mem D y using 1
    ext i : 2 <;> simp
  have h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i := (hz i).1
  have hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hy _, rfl⟩
  have hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i) := by
    have h1 := Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3)
      (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))
    refine sh_le_sh_of_le ?_ _ h1
    have := hI i
    unfold TopData.wst
    push_cast; nlinarith
  have hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) =
      D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i)) := by
    simp only [map_sub, map_add (f := _), D.comm]
    linear_combination (norm := module) h0
  have hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    simpa [sh_zero_eq] using sh_le_sh_of_le (a := 0) (b := -a) (by omega) P
  refine ⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp only [map_sub, D.comm]
    linear_combination (norm := module) h0
  · convert (N i).sub_mem (hx i) (hy i) using 1
    simp only []
    abel
  · exact Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))
  · beta_reduce
    rw [hc, hxG i h]
    refine Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))
    · have := (hw i).2; omega
    · omega
  · refine Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_
    have := sh_le_sh (-Dt.wst i) (hAB i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
  · beta_reduce
    rw [hc]
    exact Submodule.sub_mem _ hdeep (hxB i h)


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem span_prop {s : ℕ} (c : Fin s → Vc k m) (g : Vc k m →ₗ[k] Vc k m) (P Q : Submodule k⟦X⟧ (Vc k m))
    (h : ∀ a, c a ∈ P ∧ g (c a) - c a ∈ Q) :
    ∀ x ∈ LinearMap.range (Fintype.linearCombination k c), x ∈ P ∧ g x - x ∈ Q := by
  rintro _ ⟨t, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]
  refine ⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1,
    Submodule.sum_mem _ fun a _ => ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ _ (h a).2

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli
  have hW := _root_.GlobalTheory.WindowArith.windows (k := k) Dt T1 T2 T3
  have hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i := fun i => by
    have h1 := Dt.one_le_letterBlockLength
    have := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
    unfold TopData.wst
    omega
  choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl5 : 5 ≤ l := by have := T1 0; omega
  obtain ⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩ := hΨ.modPG l k hl5 R ι hι
  choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i
  refine card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)
  · cases h : Dt.ty i with
    | G =>
      have e : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (hw i).1
      have := _root_.GlobalTheory.PhiGam.PolarKernel.main R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by
          have := span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx
          rw [e]
          refine ⟨this.1, ?_⟩
          have h2 := mem_sh_iff_smul_mem.1 this.2
          rwa [zpow_neg_one] at h2)
      rw [e, (hs i).2.1 h] at this
      exact this
    | Bd =>
      have e : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (hw i).2
      obtain ⟨-, -, w1, w2⟩ := (hW i).2.2.2 h
      have h1 := Dt.one_le_letterBlockLength
      have h2 := T1 i
      have h3 := (hW i).1
      obtain ⟨s1, s2⟩ := (hs i).2.2 h
      have := _root_.GlobalTheory.PhiGam.PolarCount.main R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2
        (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat
        (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [e]; exact (hAB i).2)
        (hAB i).1 (by rw [e]; unfold TopData.wst; nlinarith) (hs _).1
        (fun y hy hy0 => by
          rw [e] at hy ⊢
          have h4 := (hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)
          have h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1) :=
            ⟨by rwa [neg_add_eq_sub], hy0⟩
          rw [← h4] at h5
          obtain ⟨x, ⟨hx, hx0⟩, hxy⟩ := h5
          exact ⟨x, hx, hx0, hxy⟩)
        (by rw [e]; exact _root_.GlobalTheory.GenKernelFit.nab_mem_of_ePoly D i (N i) _ (hC i) s2)
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by
          rw [e]; exact span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))
      rw [Module.finrank_fin_fun] at this
      omega
  · have hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i) := fun i => by
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1
    obtain ⟨y, -, hy⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
      (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1)
      (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
          map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        exact Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])
      (fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by
        have h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1
        have h2 : ∑ a, t a • c a i ∈ N i := ht i
        convert (N i).sub_mem h2 h1 using 1
        simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib,
          ← smul_sub, sub_sub_cancel])
    have h1 : ∑ a, t a • z' a ∈ herrB D := by
      convert cob_mem D y using 1
      exact Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)
    have h2 : ∑ a, t a • (z a - z' a) ∈ herrB D :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)
    have h3 : ∑ a, t a • z a ∈ herrB D := by
      convert (herrB D).add_mem h1 h2 using 1
      simp only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]
    funext a
    refine Fintype.linearIndependent_iff.1 hli t ?_ a
    have h4 : (herrB D).mkQ (∑ a, t a • z a) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h3
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul] using h4

end GlobalTheory.Models.PolarBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterModelExponentsSignsSenWeight
section
noncomputable section
namespace GlobalTheory.Models.CharSign
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem exists_unit_zpow {c : k⸨X⸩} (hc : c ≠ 0) :
    ∃ (a : ℤ) (u : (k⟦X⟧)ˣ), c = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a := by
  obtain ⟨a, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := k⟦X⟧) (K := k⸨X⸩) PowerSeries.X_irreducible hc
  refine ⟨a, u, ?_⟩
  rw [h, Units.smul_def, Algebra.smul_def, vv_eq_coe_X]
  rfl

theorem coe_smul (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := algebraMap_smul k⸨X⸩ a x

theorem le_of_sh_le_sh {N : Submodule k⟦X⟧ V} (hN : N.FG) (h0 : N ≠ ⊥) {a b : ℤ} (h : sh a N ≤ sh b N) :
    b ≤ a := by
  by_contra hab
  have h1 : N ≤ sh 1 N := by
    have h2 := sh_le_sh (-a) h
    rw [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq] at h2
    exact h2.trans (sh_le_sh_of_le (by omega) N)
  apply h0
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(PowerSeries.X : k⟦X⟧)}) N hN ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 (h1 hx)
    rw [zpow_one, vv_eq_coe_X, coe_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PowerSeries.maximalIdeal_eq_span_X]

theorem span_unit_zpow (a : ℤ) (u : (k⟦X⟧)ˣ) (y : V) :
    Submodule.span k⟦X⟧ {(((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a) • y} = sh a (Submodule.span k⟦X⟧ {y}) := by
  rw [sh, Submodule.map_span, Set.image_singleton, mul_smul, coe_smul,
    Submodule.span_singleton_smul_eq u.isUnit]
  rfl

theorem φ_zpow {l : ℕ} (R : RingPG k l) (a : ℤ) :
    ∃ u : (k⟦X⟧)ˣ, R.φ (vv k ^ a) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l * a) := by
  obtain ⟨u, hu⟩ := R.φ_v
  refine ⟨u ^ a, ?_⟩
  rw [map_zpow₀, hu, mul_zpow, zpow_mul, zpow_natCast]
  congr 1
  have := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ →+* k⸨X⸩).toMonoidHom) u a
  have h2 := congrArg Units.val this
  rw [Units.val_zpow_eq_zpow_val] at h2
  exact h2.symm

variable [Module k V]

theorem pull_sh_le {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) ≤ sh (l * a) (pull f N) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := φ_zpow R a
  rw [hf, hu, mul_smul, coe_smul]
  exact Submodule.smul_mem _ _ (mem_sh_iff_exists.2 ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩)

theorem pull_sh {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) = sh (l * a) (pull f N) := by
  refine le_antisymm (pull_sh_le R hf a N) ?_
  have h := sh_le_sh (l * a) (pull_sh_le R hf (-a) (sh a N))
  rwa [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq, mul_neg, add_neg_cancel, sh_zero_eq] at h

end

section
variable {k : Type} [Field k]

theorem exists_smul_eq {y : Vc k 1} (hy : y ≠ 0) (x : Vc k 1) : ∃ c : k⸨X⸩, x = c • y := by
  have h0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
  refine ⟨x 0 / y 0, funext fun j => ?_⟩
  rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]

theorem span_eq_sh {x y : Vc k 1} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : ℤ, Submodule.span k⟦X⟧ {x} = sh a (Submodule.span k⟦X⟧ {y}) := by
  obtain ⟨c, rfl⟩ := exists_smul_eq hy x
  obtain ⟨a, u, rfl⟩ := exists_unit_zpow (c := c) (by rintro rfl; exact hx (zero_smul _ _))
  exact ⟨a, span_unit_zpow a u y⟩

theorem span_total (x y : Vc k 1) : Submodule.span k⟦X⟧ {x} ≤ Submodule.span k⟦X⟧ {y} ∨
    Submodule.span k⟦X⟧ {y} ≤ Submodule.span k⟦X⟧ {x} := by
  by_cases hx : x = 0
  · left; simp [hx]
  by_cases hy : y = 0
  · right; simp [hy]
  obtain ⟨a, h⟩ := span_eq_sh hx hy
  rw [h]
  rcases le_total 0 a with ha | ha
  · left; exact (sh_le_sh_of_le ha _).trans (sh_zero_eq _).le
  · right; exact (sh_zero_eq _).ge.trans (sh_le_sh_of_le ha _)

theorem exists_gen {N : Submodule k⟦X⟧ (Vc k 1)} (hN : N.FG) : ∃ x, N = Submodule.span k⟦X⟧ {x} := by
  classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨x, hx⟩ := ih
    rw [Finset.coe_insert, Submodule.span_insert, hx]
    rcases span_total a x with h | h
    · exact ⟨x, sup_eq_right.2 h⟩
    · exact ⟨a, sup_eq_left.2 h⟩

theorem ne_bot_of_isLat {N : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) : N ≠ ⊥ := by
  rintro rfl
  have h := hN.2
  simp at h

theorem exists_eq_sh {N N' : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) (hN' : IsLat N') : ∃ a : ℤ, N = sh a N' := by
  obtain ⟨x, rfl⟩ := exists_gen hN.1
  obtain ⟨y, rfl⟩ := exists_gen hN'.1
  refine span_eq_sh ?_ ?_
  · rintro rfl; exact ne_bot_of_isLat hN (by simp)
  · rintro rfl; exact ne_bot_of_isLat hN' (by simp)

end

theorem model_char_sign : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 _ _ e he0 het N hN
  obtain ⟨-, hL, hAB, -⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M (chr (M.ω ^ (-e))) N hN
  obtain ⟨-, hL0, hAB0, -⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M (chr (M.ω ^ (-e))) (M.Nχ e) (M.χ_model e he0 het)
  have hχ := M.χ_lat e (by omega) het
  choose κ hκ using fun i => exists_eq_sh (hL i) (hL0 i)
  have key : ∀ i {a b : ℤ}, sh a (M.Nχ e i) ≤ sh b (M.Nχ e i) → b ≤ a :=
    fun i a b h => le_of_sh_le_sh (hL0 i).1 (ne_bot_of_isLat (hL0 i)) h
  have habs : ∀ i, |κ i| ≤ Dt.sg l i := by
    intro i
    have a1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w N (M.Nχ e) hL hL0 hAB hAB0 i
    have a2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w (M.Nχ e) N hL0 hL hAB0 hAB i
    rw [hκ i, sh_sh_eq] at a1
    rw [hκ i] at a2
    have b1 := key i (a1.trans (sh_zero_eq _).ge)
    have b2 := key i a2
    unfold TopData.sg
    rw [abs_le]
    constructor <;> omega
  have hJ : ∀ i, -Dt.w i + κ i ≤ l * κ (i - 1) + e ∧ l * κ (i - 1) + e ≤ Dt.wst i + κ i := by
    intro i
    obtain ⟨a1, a2⟩ := hAB i
    have hp : pull ((F.D (chr (M.ω ^ (-e)))).φ i) (N (i - 1)) = sh (l * κ (i - 1) + e) (M.Nχ e i) := by
      rw [hκ (i - 1), pull_sh R ((F.D (chr (M.ω ^ (-e)))).φ_semi i), (hχ i).2.2.1, sh_sh_eq]
    rw [hp, hκ i, sh_sh_eq] at a1 a2
    exact ⟨key i a1, key i a2⟩
  refine ⟨κ, fun i => ⟨hκ i, habs i, fun hi => ?_, fun hi => ?_, fun x => ?_⟩⟩
  · by_contra hneg
    have c1 := (Dt.lowG i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).2
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).1
    have c5 : (l : ℤ) * κ (i - 1) ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · by_contra hneg
    have c1 := (Dt.lowBd i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).1
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).2
    unfold TopData.wst at c4
    have c5 : (l : ℤ) * 1 ≤ l * κ (i - 1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · rw [hκ i, GlobalTheory.PhiGam.SenShift.sen_sh R _ ((F.D (chr (M.ω ^ (-e)))).γ_semi i) _ (hχ i).1 (hχ i).2.1,
      (hχ i).2.2.2]
    unfold resCount
    have : (((e - 0 : ℤ) : k) = x + (κ i : k)) ↔ (((e - κ i - 0 : ℤ) : k) = x) := by
      push_cast
      rw [sub_zero, sub_zero, sub_eq_iff_eq_add]
    classical
    simp only [Multiset.filter_singleton, this]
    split_ifs <;> simp

end GlobalTheory.Models.CharSign
end
end

