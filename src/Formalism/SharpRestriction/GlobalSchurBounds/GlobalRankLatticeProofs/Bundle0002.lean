module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

private theorem eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf {G : Type*} [AddCommGroup G] (a : G) (k : ℤ)
    (hk : k • a = 0) (hlt : |k| < (addOrderOf a : ℤ)) : k = 0 :=
  Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk) hlt

private theorem sub_zsmul_eq_of_two_eqs {G : Type*} [AddCommGroup G] (a h t u₀ : G) (i j : ℤ) (s s' : ℕ)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) :
    (j - i) • h = ((s' : ℤ) - s) • a := by
  rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  calc j • h - i • h = (t + j • h) - (t + i • h) := by abel
    _ = (s' • a + u₀) - (s • a + u₀) := by rw [e, e']
    _ = s' • a - s • a := by abel

private theorem false_of_three_distinct_in_window {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hR : Formalism.FrobeniusOrbits.NoRel T L)
    (hh : 4 * L < addOrderOf h) (i₀ i1 i2 i3 : ℤ) (s1 s2 s3 : ℕ)
    (a1 : i₀ ≤ i1) (b1 : i1 < i₀ + L) (a2 : i₀ ≤ i2) (b2 : i2 < i₀ + L)
    (a3 : i₀ ≤ i3) (b3 : i3 < i₀ + L)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) (hs1 : s1 ∈ T) (hs2 : s2 ∈ T) (hs3 : s3 ∈ T)
    (e1 : t + i1 • h = s1 • a + u₀) (e2 : t + i2 • h = s2 • a + u₀)
    (e3 : t + i3 • h = s3 • a + u₀) : False := by
  have hL : (4 * L : ℤ) < addOrderOf h := by exact_mod_cast hh
  have hdist : ∀ (i j : ℤ) (s s' : ℕ), i₀ ≤ i → i < i₀ + L → i₀ ≤ j → j < i₀ + L → i ≠ j →
      (j - i) • h = ((s' : ℤ) - s) • a → s ≠ s' := by
    intro i j s s' hi hi' hj hj' hij e hss
    subst hss
    rw [sub_self, zero_zsmul] at e
    have h0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf h (j - i) e (by rw [abs_lt]; constructor <;> omega)
    omega
  have k2 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i2 s1 s2 e1 e2
  have k3 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i3 s1 s3 e1 e3
  have k23 := sub_zsmul_eq_of_two_eqs a h t u₀ i2 i3 s2 s3 e2 e3
  have n12 := hdist i1 i2 s1 s2 a1 b1 a2 b2 h12 k2
  have n13 := hdist i1 i3 s1 s3 a1 b1 a3 b3 h13 k3
  have n23 := hdist i2 i3 s2 s3 a2 b2 a3 b3 h23 k23
  have hD : ((i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)) • a = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, ← smul_smul, ← smul_smul, ← k2, ← k3, smul_smul, smul_smul,
      mul_comm (i3 - i1), sub_self]
  have hN : ∀ s ∈ T, 4 * (L : ℤ) * s < addOrderOf a := fun s hs => by exact_mod_cast hT s hs
  have hb1 := hN s1 hs1
  have hb2 := hN s2 hs2
  have hb3 := hN s3 hs3
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hs1n : (0 : ℤ) ≤ s1 := by positivity
  have hs2n : (0 : ℤ) ≤ s2 := by positivity
  have hs3n : (0 : ℤ) ≤ s3 := by positivity
  have hy2 : 4 * (L : ℤ) * |(s2 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s2 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs2n]
  have hy3 : 4 * (L : ℤ) * |(s3 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s3 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs3n]
  have hx : |i3 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hu : |i2 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hxy : 4 * |(i3 - i1) * ((s2 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg ((s2 : ℤ) - s1))]
  have huv : 4 * |(i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg ((s3 : ℤ) - s1))]
  have hDb : |(i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_lt]
    constructor <;>
      linarith [le_abs_self ((i3 - i1) * ((s2 : ℤ) - s1)), neg_abs_le ((i3 - i1) * ((s2 : ℤ) - s1)),
        le_abs_self ((i2 - i1) * ((s3 : ℤ) - s1)), neg_abs_le ((i2 - i1) * ((s3 : ℤ) - s1)),
        abs_nonneg ((i3 - i1) * ((s2 : ℤ) - s1)), abs_nonneg ((i2 - i1) * ((s3 : ℤ) - s1))]
  have hD0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hD hDb
  exact hR s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 (i2 - i1) (i3 - i1)
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h12))) hu
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h13))) hx
    (fun hc => h23 (by omega)) (sub_eq_zero.mp hD0)

private theorem eq_of_zsmul_eqs_of_small_orders {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hpos : 0 < addOrderOf h)
    (hh : addOrderOf h ≤ 4 * L) (i j : ℤ) (s s' : ℕ) (hs : s ∈ T) (hs' : s' ∈ T)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) : s = s' := by
  have k := sub_zsmul_eq_of_two_eqs a h t u₀ i j s s' e e'
  have hm : ((addOrderOf h : ℤ) * ((s' : ℤ) - s)) • a = 0 := by
    rw [← smul_smul, ← k, smul_smul, mul_comm, ← smul_smul, natCast_zsmul,
      addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hm0 : (0 : ℤ) ≤ (addOrderOf h : ℤ) := by positivity
  have hmL : (addOrderOf h : ℤ) ≤ 4 * L := by exact_mod_cast hh
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hsn : (0 : ℤ) ≤ s := by positivity
  have hsn' : (0 : ℤ) ≤ s' := by positivity
  have hb := (show 4 * (L : ℤ) * s < addOrderOf a by exact_mod_cast hT s hs)
  have hb' := (show 4 * (L : ℤ) * s' < addOrderOf a by exact_mod_cast hT s' hs')
  have hy : 4 * (L : ℤ) * |(s' : ℤ) - s| < addOrderOf a := by
    rcases abs_cases ((s' : ℤ) - s) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hsn, mul_nonneg hLn hsn']
  have hz := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hm (by
    rw [abs_mul, abs_of_nonneg hm0]
    nlinarith [mul_le_mul_of_nonneg_right hmL (abs_nonneg ((s' : ℤ) - s))])
  rcases mul_eq_zero.mp hz with h0 | h0 <;> omega

theorem dropping_proposition_holds : ∃ C : ℝ, ∀ D : D7, Conclusion5 D C := by
  obtain ⟨C, -, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨C, fun D Lw hLw => ?_⟩
  obtain ⟨T, hTs, hTR, hTc⟩ := hT D.R.n0 Lw hLw
  refine ⟨T, ?_, hTc, hTR, ?_⟩
  · intro s hs
    have h1 : ((4 * Lw * s : ℕ) : ℝ) < (D.R.n0 : ℝ) := by exact_mod_cast hTs s hs
    have hL : (2 : ℝ) ≤ Lw := by exact_mod_cast hLw
    rw [lt_div_iff₀ (by linarith)]
    push_cast at h1
    linarith
  · intro u₀ t h
    refine ⟨fun hh i₀ => ?_, fun hh => ?_⟩
    · by_contra hc
      push_neg at hc
      obtain ⟨i1, hi1, i2, hi2, i3, hi3, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
      simp only [Finset.mem_filter, Finset.mem_Ico, transl, Set.mem_setOf_eq] at hi1 hi2 hi3
      obtain ⟨⟨a1, b1⟩, s1, hs1, e1⟩ := hi1
      obtain ⟨⟨a2, b2⟩, s2, hs2, e2⟩ := hi2
      obtain ⟨⟨a3, b3⟩, s3, hs3, e3⟩ := hi3
      exact false_of_three_distinct_in_window _ t h u₀ T Lw hTs hTR hh i₀ i1 i2 i3 s1 s2 s3 a1 b1 a2 b2 a3 b3
        h12 h13 h23 hs1 hs2 hs3 e1 e2 e3
    · haveI hfin : Finite (HH D) := by
        show Finite (Fin _)
        infer_instance
      have hpos : 0 < addOrderOf h := addOrderOf_pos h
      have hsub : (coset t h ∩ transl T u₀).Subsingleton := by
        rintro x ⟨⟨i, rfl⟩, s, hs, ex⟩ y ⟨⟨j, rfl⟩, s', hs', ey⟩
        have hss := eq_of_zsmul_eqs_of_small_orders _ t h u₀ T Lw hTs hpos hh i j s s' hs hs' ex ey
        subst hss
        rw [ex, ey]
      rcases hsub.eq_empty_or_singleton with hE | ⟨x, hx⟩
      · rw [hE, Set.ncard_empty]
        omega
      · rw [hx, Set.ncard_singleton]

end Formalism.MainNotions.UnusedSlot33

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal IntermediateField
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace CMIdealEquivalence

theorem mult_ring {M : Type} [Field M] [NumberField M]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) (hI : I ≠ 0) (x : M) :
    (∀ y ∈ I, x * y ∈ I) ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    have hi : IsIntegral (𝓞 M) x :=
      isIntegral_of_smul_mem_submodule (I : Submodule (𝓞 M) M)
        (fun h0 => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h0))
        (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) x (fun n hn => h n hn)
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro hx y hy
    have : (⟨x, hx⟩ : 𝓞 M) • y ∈ (I : Submodule (𝓞 M) M) :=
      Submodule.smul_mem (I : Submodule (𝓞 M) M) _ hy
    exact this

private theorem mem_one_iff'' {M : Type} [Field M] [NumberField M] (t : M) :
    t ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨x', rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe x'
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem integ_iff' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M) (t : M) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

private theorem smul_ne_bot' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h2 : σ⁻¹ • (σ • B) = σ⁻¹ • (⊥ : Ideal (𝓞 M)) := by rw [h]
  rwa [inv_smul_smul, Ideal.pointwise_smul_def, Ideal.map_bot] at h2

private theorem mem_inv_smul' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) (y : M) :
    σ y ∈ ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 M)) M))⁻¹ := by
  have hc : ∀ b : 𝓞 M, algebraMap (𝓞 M) M (σ • b) = σ (algebraMap (𝓞 M) M b) := fun b => rfl
  have h1 : ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (smul_ne_bot' σ B hB)
  have h2 : ((B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have := h (σ (algebraMap (𝓞 M) M b)) ((FractionalIdeal.mem_coeIdeal _).2
      ⟨σ • b, Ideal.smul_mem_pointwise_smul σ b B hb, hc b⟩)
    rw [mem_one_iff'', ← map_mul, integ_iff'] at this
    rw [mem_one_iff'']
    exact this
  · intro h z hz
    obtain ⟨c, hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have hb : σ⁻¹ • c ∈ B := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
    rw [mem_one_iff''] at this ⊢
    have e : algebraMap (𝓞 M) M c = σ (algebraMap (𝓞 M) M (σ⁻¹ • c)) := by
      rw [← hc, smul_inv_smul]
    rw [e, ← map_mul, integ_iff']
    exact this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  show (D.host.conj * D.host.conj) x = x
  rw [show D.host.conj * D.host.conj = 1 by
    simp only [Formalism.HC.HostRaw.conj, ← map_mul, Formalism.HC.Frame.cc_mul_cc, map_one]]
  rfl

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.pointwise_smul_def, Ideal.map_bot, bot_sup_eq] at h2
  exact bot_ne_top h2

theorem ordinary (D : D7) : ∀ p : ℕ, p.Prime →
    (primesOver (span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 →
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(p : ℤ)}) →
        ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, τ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P →
          (D.host.galE (σ * τ) ∈ D.R.Psi ↔
            D.host.galE σ ∈ D.R.Psi) := by
  intro p hp hK P hP hl σ τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hl
  exact (D.host.der.ordinary p P).2 hK σ τ hτ

end CMIdealEquivalence

open CMIdealEquivalence

def PolPart (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    ∃ ξ : D.host.E, ξ ∈ D.host.K ∧ D.host.conj ξ = -ξ ∧ (∀ φ ∈ PhiEmb D, 0 < (φ ξ).im) ∧
      ∀ y : D.host.E,
        y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ↔
        ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0,
          Algebra.trace ℚ D.host.E (ξ * D.host.conj x * y) ∈ (algebraMap ℤ ℚ).range

theorem lemma_one_eight_of_polarisation (D : D7) (hPol : PolPart D) : Conclusion8 D := by
  have hb := b_ne_bot D
  have hσb : D.host.conj • D.host.𝔟 ≠ ⊥ := smul_ne_bot' D.host.conj _ hb
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨D.host.AA0, ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹, ?_, ?_, ?_, ordinary D⟩
  · intro x
    have hσσ : D.host.conj • D.host.conj • D.host.𝔟 = D.host.𝔟 := by
      rw [smul_smul, show D.host.conj * D.host.conj = 1 from AlgEquiv.ext (conj_conj D), one_smul]
    have h := mem_inv_smul' D.host.conj (D.host.conj • D.host.𝔟) hσb x
    rw [hσσ] at h
    exact h.symm
  · rw [D.host.𝔟_spec.1, FractionalIdeal.coeIdeal_mul, mul_inv]
    try rfl
  · intro cc hcc
    have hm : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hcc
    have hne : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hm) (inv_ne_zero hb0)
    exact ⟨fun x => mult_ring _ hne x, hPol cc hcc⟩

end Formalism.MainNotions.UnusedSlot33

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

section P3
open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem signature_counts_ge_one (D : D7) : 1 ≤ pY D ∧ 1 ≤ qY D := by
  unfold pY qY
  simp only [Formalism.BasicNotions.Ranks.sigY0]
  have := D.R.m_add_three_le_k
  constructor <;> omega

end P3

theorem explicit_gap_le_general_gap (D : D7) (C ep0 : ℝ) (hC : 8192 ≤ C) : spectralGapLowerBound D ep0 ≤ gap3 D C ep0 := by
  unfold spectralGapLowerBound gap3
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log D.R.r := Real.log_nonneg hr1
  have hX : 0 ≤ (↑(min (pY D) (qY D)) : ℝ) * (↑(pY D) * ↑(qY D)) ^ 3 := by positivity
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg ep0)
  have h1 : (8192 : ℝ) ≤ C * D.R.r := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hX hlog)]

theorem weighted_log_sum_lower_bound (D : D7) (w : ℕ → D.what₂.Tau → ℝ) (w0 : ℝ) (hw0 : 0 < w0) (hpi : Real.pi ≤ D.host.v)
    (hw : ∀ ρ j, j < D.R.m → w0 ≤ w j ρ) :
    (D.R.m : ℝ) * Real.log w0 ≤
      ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv : 1 ≤ D.host.v / Real.pi := (one_le_div Real.pi_pos).2 hpi
  have hterm : ∀ j, j < D.R.m → (Fintype.card D.what₂.Tau : ℝ) * Real.log w0 ≤
      ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    intro j hj
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ρ _
    apply Real.log_le_log hw0
    rw [mul_div_assoc]
    calc w0 = w0 * 1 := (mul_one _).symm
      _ ≤ w j ρ * (D.host.v / Real.pi) :=
        mul_le_mul (hw ρ j hj) hv zero_le_one (by linarith [hw ρ j hj])
  rw [D.what₂.card_Tau] at hterm
  calc (D.R.m : ℝ) * Real.log w0 =
        ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ((D.R.f : ℝ) * Real.log w0) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, inv_mul_cancel_left₀ hf.ne']
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hterm j (Finset.mem_range.1 hj)) (by positivity)

theorem weights_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ w j ρ := by
  obtain ⟨-, -, -, -, -, -, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hx := sc.one_lt_alt
  have hbase : 1 ≤ bN D ρ 0 := by
    have h := (hb0 ρ).1
    rw [le_div_iff₀ (by linarith)] at h
    have h4 : (1 : ℝ) ≤ D.R.k * (4 * Δ) := by nlinarith
    have h5 : (D.R.k : ℝ) * (4 * Δ) ≤ D.R.k * (4 * Δ) * sc.x :=
      le_mul_of_one_le_right (by positivity) hx.le
    linarith
  have hmono : ∀ i, i < D.R.m → bN D ρ 0 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hwb ρ i hi
      linarith
  linarith [(hw ρ j hj).2.1, hmono j hj]

theorem eight_L_le_log_g (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w) (i : Fin 2) :
    8 * sc.L ≤ Real.log (D.host.g i : ℝ) := by
  obtain ⟨-, -, -, -, -, hg, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb : 0 < sc.b := Real.exp_pos _
  have h1 := (hg i).1
  have hpos : 0 < ((D.R.k : ℝ) * sc.b) ^ 8 := by positivity
  calc 8 * sc.L = Real.log (sc.b ^ 8) := by
        rw [Real.log_pow, Formalism.BasicNotions.Scale.b, Real.log_exp]
        norm_num
    _ ≤ Real.log (((D.R.k : ℝ) * sc.b) ^ 8) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hb.le (by nlinarith) 8)
    _ ≤ Real.log (D.host.g i : ℝ) := Real.log_le_log hpos h1

theorem corollary_five_four_of_explicit (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) : VandermondeCountExplicit D sc C0 CY := by
  intro Δ w hA Γ hΓ u hT2 hf2 hT1 hT3
  have hB := hA.1
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hD := dual_degree_pos D hg
  have hd := dual_degree_word_pos D hg (massI_pos D D.R.k) u
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := le_trans one_le_two (le_trans D.R.two_le_m D.R.m_le_f)
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hX : Real.exp (logXuD D u) ^ (D.R.f * D.R.k) = DstarD D / duStarU D u := by
    have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
    have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    rw [← Real.exp_nat_mul]
    unfold logXuD logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (DstarD D / duStarU D u)) =
      Real.log (DstarD D / duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
  obtain ⟨c1, c2, c3, c4⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ) (Real.exp (logXuD D u)) Γ
    (DstarD D) (duStarU D u) _ (logXuD D u) (logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ hD hd hX
    hT1 hT3 rfl (by rw [Real.log_exp]) (by rw [Real.log_exp])
  have hL := scale_one_le_L sc
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hΓ0 : 0 < Γ := by linarith
  have eΓ : Γ ^ (-(2 : ℝ)) = (Γ⁻¹) ^ 2 := by
    rw [Real.rpow_neg hΓ0.le, Real.rpow_two, inv_pow]
  have l1 := (h5 Δ w hA u).1
  refine ⟨⟨by rw [eΓ]; exact c1, by rw [eΓ]; exact c2⟩, by linarith, by linarith, fun hG => ⟨c4, by linarith, ?_⟩⟩
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hA.2.2.2.1
  have s1 := weighted_log_sum_lower_bound D w 1 one_pos hB.1 (fun ρ j hj => weights_ge_one_section_B D sc C0 Δ w hB ρ j hj)
  rw [Real.log_one, mul_zero] at s1
  have s2 : 16 * sc.L ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
    rw [Fin.sum_univ_two]
    have := eight_L_le_log_g D sc C0 Δ w hB 0
    have := eight_L_le_log_g D sc C0 Δ w hB 1
    linarith
  unfold lowS at l1
  have s3 : (D.R.m : ℝ) * (16 * sc.L) ≤ (D.R.m : ℝ) * ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
    mul_le_mul_of_nonneg_left s2 (by linarith)
  nlinarith

theorem part_five_explicit_of_propositions (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) (hv : VandermondeVariationExplicitBound D sc C0 CY) :
    VandermondeCountBound D sc C0 CY := ⟨h5, corollary_five_six_of_explicit D sc C0 CY h5, corollary_five_four_of_explicit D sc C0 CY h5, hv⟩

end Formalism.MainNotions.StandardLattice
end
end

