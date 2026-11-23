module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormDiscriminantSuperlatticeOddIndexEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnit
section
noncomputable section

namespace GlobalTheory.MomDelta

section Scale

open GlobalTheory.MomOne

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, LinearIndependent.pair_iff.2 fun s t h => by
    have h' : s • L.ω₁ + t • L.ω₂ = 0 := by
      apply mul_left_cancel₀ hc
      simp only [Complex.real_smul] at h ⊢
      linear_combination h
    exact LinearIndependent.pair_iff.1 L.indep s t h'⟩

theorem mem_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, mul_left_cancel₀ hc ?_⟩
    simp only [scalePair] at h
    linear_combination h
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [scalePair]; ring⟩

theorem G_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    L.G k = c ^ k * (scalePair L c hc).G k := by
  let e : (L.lattice : Set ℂ) ≃ ((scalePair L c hc).lattice : Set ℂ) :=
    (Equiv.mulLeft₀ c hc).subtypeEquiv fun w => by
      simpa using (mem_scalePair L c hc w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : ((scalePair L c hc).lattice : Set ℂ)) : ℂ) = c * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]

theorem g₂_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₂ = L.g₂ / c ^ 4 := by
  simp only [PeriodPair.g₂, G_scale L c hc 4]
  field_simp

theorem g₃_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₃, G_scale L c hc 6]
  field_simp

variable {q : ℕ} [Fact q.Prime]

theorem ok_scale (M : Mdl q) (hM : M.Ok) (c : ℂ) (hc : c ≠ 0) :
    (Mdl.mk M.ι (scalePair M.L c hc) (M.c / c) M.W).Ok := by
  obtain ⟨h0, h1, h2, h3, h4, h6, hΔ, hg2, hg3⟩ := hM
  refine ⟨div_ne_zero h0 hc, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : (scalePair M.L c hc).g₂ / (M.c / c) ^ 4 = M.L.g₂ / M.c ^ 4 := by
      rw [g₂_scale]; field_simp
    show M.W.c₄ / 12 = M.ι _
    rw [this]; exact hg2
  · have : (scalePair M.L c hc).g₃ / (M.c / c) ^ 6 = M.L.g₃ / M.c ^ 6 := by
      rw [g₃_scale]; field_simp
    show M.W.c₆ / 216 = M.ι _
    rw [this]; exact hg3

theorem norm_disc_ring (ι : ℂ ≃+* ℂ_[q]) {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (L' : PeriodPair) (N : ℕ)
    (hq : q ≠ 2) (hN : Nat.Coprime N (2 * q)) (hN0 : N ≠ 0)
    (h1 : ∀ z, InOK d z → (N : ℂ) * z ∈ L'.lattice) (h2 : ∀ x ∈ L'.lattice, InOK d x) :
    ‖ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖ι (discr d)‖ := by
  have hc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hL := Basic.isOK_okPair d hd.pos
  obtain ⟨M, hMι, hML, hOk, -⟩ := exists_model d q ι _ hd h16 hL
  have hIs : IsOK d M.L := hML ▸ hL
  subst hMι
  have hk := _root_.GlobalTheory.MomDisc.norm_disc_eq q (Mdl.mk M.ι (scalePair M.L N hc) (M.c / N) M.W) L' N hq (ok_scale M hOk N hc) hN
    (fun z hz => by
      have e : z = (N : ℂ) * (z / N) := by field_simp
      have hz' : (N : ℂ) * (z / N) ∈ (scalePair M.L N hc).lattice := by rw [← e]; exact hz
      rw [e]
      exact h1 _ ((hIs _).1 ((mem_scalePair M.L N hc _).1 hz')))
    (fun x hx => (mem_scalePair M.L N hc x).2 ((hIs x).2 (h2 x hx)))
  have e : (scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2
      = (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) / (N : ℂ) ^ 12 := by
    rw [g₂_scale, g₃_scale]; field_simp
  have hnorm : ‖M.ι (N : ℂ)‖ = 1 := by
    rw [map_natCast]
    exact Basic.norm_nat_eq_one (Nat.Coprime.symm (Nat.coprime_mul_iff_right.1 hN).2)
  refine hk.trans ?_
  show ‖M.ι ((scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2)‖ = _
  rw [e, map_div₀, norm_div, map_pow, norm_pow, hnorm, one_pow, div_one, (Basic.discr_eq hIs).1]

end Scale

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem delta_ratio : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q →
    δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  intro D cc δ δ₀ hcc hδ hδ₀ q _ hq hNq
  obtain ⟨hdp, h16, hOK, -, hlam⟩ := _root_.GlobalTheory.MomDict.main D
  obtain ⟨hne, hcop⟩ := hcc
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
  have hN2 : Nat.Coprime (Ideal.absNorm cc) (2 * q) :=
    Nat.coprime_mul_iff_right.2 ⟨(Nat.coprime_mul_iff_right.1 hcop).1, hNq⟩
  obtain ⟨L', hL'⟩ := Formalism.L2.PairingIndexBounds.Rec.exists_pp D cc hne
  have hmem : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  have hΔ : Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D cc 1) = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by
    have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 2 (by norm_num)
    have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 3 (by norm_num)
    unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [h4, h6]
    simp [PeriodPair.g₂, PeriodPair.g₃]
  have h1 : ∀ z, GlobalTheory.MomOne.InOK D.host.d z → ((Ideal.absNorm cc : ℕ) : ℂ) * z ∈ L'.lattice := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hOK z).1 hz
    refine (hL' _).1 ((hlam cc 1 hne).2 _ |>.2 ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) * x, cc.mul_mem_right x hmem, ?_⟩)
    simp
  have h2 : ∀ x ∈ L'.lattice, GlobalTheory.MomOne.InOK D.host.d x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := ((hlam cc 1 hne).2 x).1 ((hL' x).2 hx)
    exact (hOK _).2 ⟨c, by simp⟩
  have hne₀ : GlobalTheory.MomOne.discr D.host.d ≠ 0 :=
    (GlobalTheory.MomOne.Basic.discr_eq (GlobalTheory.MomOne.Basic.isOK_okPair _ hdp.pos)).2
  have hδ₀0 : δ₀ ≠ 0 := by
    rintro rfl
    exact hne₀ (by rw [← hδ₀]; simp)
  have key : ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
    intro ι
    have h := norm_disc_ring ι hdp h16 L' _ hq hN2 hN0 h1 h2
    have hδ' : δ ^ 12 = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by rw [← hΔ]; exact hδ
    rw [← hδ', ← hδ₀, map_pow, map_pow, norm_pow, norm_pow] at h
    have hι₀ : ‖ι δ₀‖ ≠ 0 := by simpa using hδ₀0
    have h12 : ‖ι (δ / δ₀)‖ ^ 12 = 1 := by
      rw [map_div₀, norm_div, div_pow, h, div_self (pow_ne_zero _ hι₀)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  obtain ⟨ι⟩ := GlobalTheory.MomOne.Basic.nonempty_iso q
  exact ⟨GlobalTheory.MomOne.mem_algebraicClosure_of_norm_le q ι _ 1 fun ι' _ => (key ι').le, key⟩

end GlobalTheory.MomDelta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.TamePow

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem locK_eq_one_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

theorem exists_pow_sub_one_mem (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal)ˣ, Nat.card_pos, fun r hr => ?_⟩
  let _ := Ideal.Quotient.field v.asIdeal
  have h0 : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 _ h0))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h1

theorem exists_pow_locK (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, H⟩ := exists_pow_sub_one_mem v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hs1 : v.valuation L (algebraMap (𝓞 L) L s) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem (H r hr) (H s hs)
    rwa [sub_sub_sub_cancel_right] at this
  have hle : v.valuation L (algebraMap (𝓞 L) L (r ^ m - s ^ m)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    simpa using (v.intValuation_le_pow_iff_mem (r ^ m - s ^ m) 1).2 (by simpa using hmem)
  rw [← map_pow]
  refine locK_eq_one_of_tame χ h _ (by simp [hu]) ?_
  have e : algebraMap (𝓞 L) L (r ^ m - s ^ m) = (algebraMap (𝓞 L) L s) ^ m * (((u ^ m : Lˣ) : L) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]; ring
  rwa [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle

theorem exists_gen (P : HeightOneSpectrum (𝓞 L)) : ∃ (h : ℕ) (a : Lˣ), 0 < h ∧
    P.valuation L (a : L) = WithZero.exp (-(h : ℤ)) ∧
    ∀ Q : HeightOneSpectrum (𝓞 L), Q ≠ P → Q.valuation L (a : L) = 1 := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have h1 : ClassGroup.mk0 (⟨P.asIdeal, hP⟩ ^ Nat.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (pow_mem hP _)).1 h1
  have ha' : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) = Ideal.span {a} := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ P.ne_bot (by simpa using ha')
  refine ⟨Nat.card (ClassGroup (𝓞 L)), Units.mk0 (algebraMap (𝓞 L) L a) (by simpa using ha0), Nat.card_pos, ?_, ?_⟩
  · rw [Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap, P.intValuation_if_neg ha0, ← ha',
      Associates.mk_pow, Associates.count_pow (by simpa using P.ne_bot) P.associates_irreducible,
      Associates.count_self P.associates_irreducible, mul_one]
  · intro Q hQ
    rw [Units.val_mk0, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hm
    have h2 : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) ≤ Q.asIdeal := by
      rw [ha', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := Q.isPrime.le_of_pow_le h2
    exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h3).symm)

theorem exists_pow_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), χ.ProductRule → (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.TameAt v) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hpr hunr htame P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := exists_gen P
  choose m hm hmu using fun v => exists_pow_locK χ (htame v)
  set M' := ∏ v ∈ insert P S, m v with hM'
  have hkill : ∀ v ∈ insert P S, ∀ u : Eˣ, v.valuation E (u : E) = 1 → χ.locK v (u ^ M') = 1 := by
    intro v hv u hu
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hv
    rw [map_pow, hM', hc, pow_mul, hmu v u hu, one_pow]
  have hk0 : P.valuation E (k : E) ≠ 0 := by simp
  set z0 : Eˣ := a ^ ordF P k with hz0
  have hz0P : P.valuation E (z0 : E) = P.valuation E (k : E) ^ h := by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haP, ← WithZero.exp_log hk0, ← WithZero.exp_zsmul,
      ← WithZero.exp_nsmul, ordF]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have hz0Q : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z0 : E) = 1 := fun Q hQ => by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  have hzQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E ((z0 ^ M' : Eˣ) : E) = 1 := fun Q hQ => by
    rw [Units.val_pow_eq_pow_val, map_pow, hz0Q Q hQ, one_pow]
  refine ⟨h * M', z0 ^ M', Nat.mul_pos hh (Finset.prod_pos fun v _ => hm v), ?_, hzQ, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hz0P, pow_mul]
  · have H := hpr (insert P S) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (z0 ^ M')
    have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P S), χ.val v ^ ordF v (z0 ^ M')) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      by_cases hv : v ∈ insert P S
      · rw [finprod_eq_if, if_neg (not_not.2 hv)]
      rw [finprod_eq_if, if_pos hv]
      have : v ≠ P := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      rw [ordF, hzQ v this, WithZero.log_one, neg_zero, zpow_zero]
    have e2 : ∏ v ∈ insert P S, χ.locK v (z0 ^ M') = χ.locK P (z0 ^ M') :=
      Finset.prod_eq_single P (fun v hv hne => hkill v hv z0 (hz0Q v hne))
        (fun h => absurd (Finset.mem_insert_self _ _) h)
    have e3 : χ.locK P (z0 ^ M') = χ.locK P k ^ (h * M') := by
      have := hkill P (Finset.mem_insert_self _ _) (z0 / k ^ h) (by
        rw [Units.val_div_eq_div_val, map_div₀, hz0P, Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hk0)])
      rwa [div_pow, map_div, div_eq_one, ← pow_mul, map_pow (χ.locK P) k] at this
    rw [e1, e2, e3, mul_one, mul_comm] at H
    exact H

end GlobalTheory.TamePow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.NormOneIdeal

theorem star_integer_smul {E : Type} [Field E] [NumberField E] [StarRing E] (a : 𝓞 E) :
    ∃ b : 𝓞 E, (b : E) = star (a : E) := by
  refine ⟨⟨star (a : E), ?_⟩, rfl⟩
  have h : IsIntegral ℤ (a : E) := a.isIntegral_coe
  exact h.map (starRingEnd E).toIntAlgHom

theorem star_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E]
    {A B C D : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (h2 : ∀ x ∈ B, star x ∈ D) :
    ∀ x ∈ A * B, star x ∈ C * D := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [star_mul']
    exact Submodule.mul_mem_mul (h1 m hm) (h2 n hn)
  · intro a b ha hb
    rw [star_add]
    exact add_mem ha hb

theorem star_mem_span {E : Type} [Field E] [NumberField E] [StarRing E] (z x : E)
    (hx : x ∈ Submodule.span (𝓞 E) {z}) : star x ∈ Submodule.span (𝓞 E) {star z} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, hb⟩ := star_integer_smul a
  refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  exact congrArg (· * star z) hb

theorem star_mem_pow {E : Type} [Field E] [NumberField E] [StarRing E]
    {A C : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (n : ℕ) :
    ∀ x ∈ A ^ n, star x ∈ C ^ n := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_span] at hx ⊢
    simpa using star_mem_span 1 x hx
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact star_mem_mul ih h1

theorem exists_pow_principal {E : Type} [Field E] [NumberField E]
    (I : (Submodule (𝓞 E) E)ˣ) :
    ∃ (h : ℕ) (z : E), 0 < h ∧ (I : Submodule (𝓞 E) E) ^ h = Submodule.span (𝓞 E) {z} := by
  let e := FractionalIdeal.unitsMulEquivSubmodule (S := nonZeroDivisors (𝓞 E)) (P := E)
  let F := e.symm I
  have hF : ClassGroup.mk E (F ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨z, hz⟩ := ClassGroup.mk_eq_one_iff.1 hF
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), z, Fintype.card_pos, ?_⟩
  rw [← hz]
  have : e (F ^ Fintype.card (ClassGroup (𝓞 E))) = I ^ Fintype.card (ClassGroup (𝓞 E)) := by
    rw [map_pow, MulEquiv.apply_symm_apply]
  rw [← Units.val_pow_eq_pow_val, ← this]
  rfl

theorem pow_eq_span_norm_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (I J : Submodule (𝓞 E) E), (∀ x, x ∈ J ↔ star x ∈ I) → I * J = 1 → (∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n) ∧ ∃ (h : ℕ) (y : E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 E) {y} = I ^ h := by
  intro E _ _ _ I J hJ hIJ
  have h1 : ∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n := by
    intro n x
    refine ⟨star_mem_pow (fun x hx => (hJ x).1 hx) n x, fun hx => ?_⟩
    have := star_mem_pow (A := I) (C := J) (fun x hx => (hJ _).2 (by rwa [star_star])) n _ hx
    rwa [star_star] at this
  refine ⟨h1, ?_⟩
  obtain ⟨h, z, hh, hz⟩ := exists_pow_principal (E := E) ⟨I, J, hIJ, by rw [mul_comm, hIJ]⟩
  change I ^ h = _ at hz
  have hJh : J ^ h = Submodule.span (𝓞 E) {star z} := by
    ext x
    rw [h1, hz]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa using star_mem_span _ _ hx
    · simpa using star_mem_span _ _ hx
  have hm : I ^ h * J ^ h = 1 := by rw [← mul_pow, hIJ, one_pow]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [hz] at hm
    simp only [Submodule.span_zero_singleton, Submodule.bot_mul] at hm
    have : (1 : E) ∈ (⊥ : Submodule (𝓞 E) E) := by
      rw [hm, Submodule.one_eq_span]
      exact Submodule.mem_span_singleton_self _
    simp at this
  have hs0 : star z ≠ 0 := star_ne_zero.2 hz0
  have hinv : Submodule.span (𝓞 E) {(star z)⁻¹} = I ^ h := by
    calc Submodule.span (𝓞 E) {(star z)⁻¹}
        = I ^ h * J ^ h * Submodule.span (𝓞 E) {(star z)⁻¹} := by rw [hm, one_mul]
      _ = I ^ h := by
        rw [mul_assoc, hJh, Submodule.span_mul_span, Set.singleton_mul_singleton,
          mul_inv_cancel₀ hs0, ← Submodule.one_eq_span, mul_one]
  refine ⟨h + h, z * (star z)⁻¹, by omega, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_star]
    field_simp
  · rw [pow_add]
    nth_rewrite 1 [hz]
    rw [← hinv, Submodule.span_mul_span, Set.singleton_mul_singleton]

end GlobalTheory.NormOneIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory

theorem exists_reps_sup_of_finite_quot (E : Type) [Field E] (H : Type) [AddCommGroup H]
    [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H)
    (hfin : Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)) :
    ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧
      (∀ x ∈ R, ∀ y ∈ R, x - y ∈ Z₀.toAddSubgroup ⊔ C → x = y) ∧
      ∀ y ∈ Z₁, ∃ x ∈ R, y - x ∈ Z₀.toAddSubgroup ⊔ C := by
  classical
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  set Z : AddSubgroup H := Z₀.toAddSubgroup ⊔ C with hZ
  let s : (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → ↥Z₁ :=
    Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
  have hs : ∀ z, Submodule.Quotient.mk (s z) = z := fun z =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype)) z
  let T : Finset (H ⧸ Z) := Finset.univ.image fun z => QuotientAddGroup.mk (s z : H)
  have hsurj : (Z₁ : Set H).SurjOn (QuotientAddGroup.mk : H → H ⧸ Z) T := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact ⟨s z, (s z).2, rfl⟩
  obtain ⟨R, hR, hinj, him⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  refine ⟨R, fun x hx => hR hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (QuotientAddGroup.eq_iff_sub_mem.2 hxy)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥Z₁) - s (Submodule.Quotient.mk ⟨y, hy⟩) ∈ Z₀.comap Z₁.subtype :=
      (Submodule.Quotient.eq _).1 (hs _).symm
    have h2 : y - (s (Submodule.Quotient.mk ⟨y, hy⟩) : H) ∈ Z :=
      AddSubgroup.mem_sup_left (by simpa using h1)
    have h3 : (QuotientAddGroup.mk y : H ⧸ Z) ∈ T :=
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, (QuotientAddGroup.eq_iff_sub_mem.2 h2).symm⟩
    rw [← him] at h3
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h3
    exact ⟨x, hx, QuotientAddGroup.eq_iff_sub_mem.1 hxy.symm⟩

theorem latSum_eq_sum_sum_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (H : Type) [AddCommGroup H] [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H) (J : Finset H), Z₀ ≤ Z₁ → C ≤ Z₁.toAddSubgroup → Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → IsReps Z₀.toAddSubgroup C J → ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧ ∀ (M : Type) [AddCommMonoid M] (f : H → M), (∀ x ∈ Z₁, ∀ y ∈ Z₀, f (x + y) = f x) → latSum Z₁ Z₀ f = ∑ x ∈ R, ∑ j ∈ J, f (x + j) := by
  intro E _ _ _ H _ _ Z₁ Z₀ C J h01 hC hfin hJ
  classical
  obtain ⟨R, hR, hRinj, hRsurj⟩ := exists_reps_sup_of_finite_quot E H Z₁ Z₀ C hfin
  obtain ⟨hJC, hJinj, hJsurj⟩ := hJ
  refine ⟨R, hR, ?_⟩
  intro M _ f hf
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  have hmem : ∀ p ∈ R ×ˢ J, p.1 + p.2 ∈ Z₁ := fun p hp =>
    Z₁.add_mem (hR _ (Finset.mem_product.1 hp).1) (hC (hJC _ (Finset.mem_product.1 hp).2))
  unfold latSum
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p hp => (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, j⟩ hp ⟨x', j'⟩ hp' h
    obtain ⟨hx, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', hj'⟩ := Finset.mem_product.1 hp'
    have h1 : x + j - (x' + j') ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h
    have h2 : x = x' := by
      refine hRinj x hx x' hx' ?_
      have : x - x' = (x + j - (x' + j')) + (j' - j) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup h1 (C.sub_mem (hJC _ hj') (hJC _ hj))
    subst h2
    have h3 : j = j' := by
      refine hJinj j hj j' hj' ?_
      have : j - j' = x + j - (x + j') := by abel
      rw [this]
      exact h1
    rw [h3]
  · intro z _
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx, hyx⟩ := hRsurj y hy
    obtain ⟨a, ha, c, hc, hac⟩ := AddSubgroup.mem_sup.1 hyx
    obtain ⟨j, hj, hcj⟩ := hJsurj c hc
    refine ⟨(x, j), Finset.mem_product.2 ⟨hx, hj⟩, (Submodule.Quotient.eq _).2 ?_⟩
    have h1 : x + j - y = -(a + (c - j)) := by
      have : y = x + (a + c) := by rw [hac]; abel
      rw [this]; abel
    have h2 : x + j - y ∈ Z₀ := by
      rw [h1]
      exact Z₀.neg_mem (Z₀.add_mem ha hcj)
    simpa using h2
  · intro p hp
    set w := Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
      (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩) with hw
    have h0 : Submodule.Quotient.mk w =
        (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype) :=
      Function.surjInv_eq _ _
    have h1 : (w : H) - (p.1 + p.2) ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h0
    have h2 := hf _ (hmem p hp) _ h1
    rw [← h2]
    congr 1
    abel

end GlobalTheory
end

