module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModRepsCardLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem lattice_mod_reps_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E),
    T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  intro E _ _ _ r M Λ hM hfg
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  have hLfg : L.FG := hfg.restrictScalars
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hLfg
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b := Module.Free.chooseBasis ℤ L
  have hli : LinearIndependent ℤ (fun i => (b i : Fin r → E)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliQ : LinearIndependent ℚ (fun i => (b i : Fin r → E)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hcard : Fintype.card ι ≤ Module.finrank ℚ (Fin r → E) := hliQ.fintype_card_le_finrank
  have hfr : Module.finrank ℚ (Fin r → E) = r * Module.finrank ℚ E := by
    simp [Module.finrank_pi_fintype]
  have heven : Module.finrank ℚ E = 2 * fdeg E := by
    rw [fdeg, IsTotallyComplex.finrank E]; omega
  have hn : Fintype.card ι ≤ 2 * fdeg E * r := by
    rw [hfr, heven] at hcard; linarith [Nat.mul_comm r (2 * fdeg E)]
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  let f : (ι → Fin M) → (Fin r → E) := fun c => ((∑ i, ((c i : ℕ) : ℤ) • b i : L) : Fin r → E)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (ι → Fin M)).card :=
          Finset.card_image_le
      _ = M ^ Fintype.card ι := by simp
      _ ≤ M ^ (2 * fdeg E * r) := Nat.pow_le_pow_right hM hn
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ht
    exact (∑ i, ((c i : ℕ) : ℤ) • b i : L).2
  · intro x hx
    let xl : L := ⟨x, hx⟩
    let k := b.repr xl
    let c : ι → Fin M := fun i => ⟨(k i % M).toNat, by
      have := Int.emod_nonneg (k i) hMpos.ne'
      have := Int.emod_lt_of_pos (k i) hMpos
      omega⟩
    refine ⟨f c, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ((∑ i, (k i / M) • b i : L) : Fin r → E), (∑ i, (k i / M) • b i : L).2, ?_⟩
    have hsum : xl = ∑ i, ((c i : ℕ) : ℤ) • b i + (M : ℤ) • ∑ i, (k i / M) • b i := by
      conv_lhs => rw [← b.sum_repr xl]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      show k i = ((k i % M).toNat : ℤ) + M * (k i / M)
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')]
      linarith [Int.mul_ediv_add_emod (k i) (M : ℤ)]
    have h2 := congrArg Subtype.val hsum
    calc x = (xl : Fin r → E) := rfl
      _ = _ := h2
      _ = f c + M • ((∑ i, (k i / M) • b i : L) : Fin r → E) := by
        rw [Submodule.coe_add, Submodule.coe_smul, natCast_zsmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumEqConeSum
section
open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latM_ne_zero (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by
  rw [latM_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero

theorem nrm_pos (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  unfold nrm
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem eisTerm_eq [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by
  have hprod : ∏ τ, latPt z (a, b) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ (Module.finrank ℚ F) *
      ∏ τ : F →+* ℝ, (((τ b : ℝ) : ℂ) * z τ + ((τ a : ℝ) : ℂ)) := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [latPt]; ring
  unfold eisTerm lhsTerm
  rw [hprod]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_neg, zpow_natCast]
  ring

theorem rhsTerm_eq [IsTotallyReal F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (ν b : F) :
    rhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z (ν, b) := by
  have hN : ∏ τ : F →+* ℝ, τ ν = ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    have h := prod_emb ν
    rw [← Complex.ofReal_prod] at h
    exact_mod_cast h
  have hpos := nrm_pos 𝔞
  have hreal : |((Algebra.norm ℚ ν : ℚ) : ℝ)| ^ (k - 1) =
      nrm 𝔞 ^ (k - 1) * (|((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hpos.ne')]
  have hsum : ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * (((τ b : ℝ) : ℂ) * z τ) =
      ∑ τ : F →+* ℝ, ((τ (ν * b) : ℝ) : ℂ) * z τ := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, Complex.ofReal_mul, mul_assoc]
  unfold rhsTerm qTerm qPow
  rw [hN, hsum, hreal, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

end GlobalTheory.EisPerB


open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent in
theorem GlobalTheory.EisPerB.lattice_sum_eq_cone_sum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
    ∀ (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k → ∀ (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
      Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) ∧
      HasSum (fun a : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F) => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k 0 z ((a : F), b))
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) *
          ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) := by
  intro F _ _ _ hLip 𝔞 k hk2 hke b hb z hz
  have hz'im : ∀ τ, ((fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) τ).im ≠ 0 := by
    intro τ
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  obtain ⟨hL, hR, hEq⟩ := hLip F (latM 𝔞) (GlobalTheory.EisPerB.latM_ne_zero 𝔞) k hk2 hke _ hz'im
  let e : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ≃ GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b :=
    Equiv.subtypeEquivRight (fun ν => _root_.GlobalTheory.Div.LipschitzCone.cone_iff F 𝔞 b hb z hz ν)
  have hN : (nrm 𝔞 : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (GlobalTheory.EisPerB.nrm_pos 𝔞).ne')
  have hRq : ∀ ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z ((e ν).1, b) :=
    fun ν => GlobalTheory.EisPerB.rhsTerm_eq 𝔞 k z ν.1 b
  have hsumQ : Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b)) := by
    have h1 : Summable (fun ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) =>
        qTerm 𝔞 k z ((e ν).1, b)) := by
      refine (hR.mul_left ((nrm 𝔞 : ℂ) ^ (k - 1))⁻¹).congr fun ν => ?_
      rw [hRq, inv_mul_cancel_left₀ hN]
    exact e.summable_iff.1 h1
  have htsum : ∑' ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν =
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) := by
    rw [tsum_congr hRq, tsum_mul_left]
    congr 1
    exact e.tsum_eq (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b))
  refine ⟨hsumQ, ?_⟩
  have hE : (fun a : (latM 𝔞 : Set F) => eisTerm k 0 z ((a : F), b)) = fun a : (latM 𝔞 : Set F) =>
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
        lhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) a :=
    funext fun a => GlobalTheory.EisPerB.eisTerm_eq k z a b
  rw [hE]
  have h := hL.hasSum.mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹
  rw [hEq, htsum] at h
  rw [← _root_.GlobalTheory.LipEisConst.lip_const_eis F 𝔞 k (by omega)]
  have hv : ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * lipConst k (latM 𝔞) *
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      (lipConst k (latM 𝔞) * ((nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b))) := by
    ring
  rw [hv]
  exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlatStatement
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenSublattice_iff_eval_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  first | exact @GlobalTheory.lie_eigenSub_iff_flat | exact GlobalTheory.lie_eigenSub_iff_flat | (intros; apply GlobalTheory.lie_eigenSub_iff_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegReg
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem liftL_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l →
    (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) →
    deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftL, deg]
  | cons p L ih =>
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2 := fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')
    obtain ⟨ihd, ihm⟩ := ih hL'
    obtain ⟨hp0, hpd, hpr⟩ := hL p List.mem_cons_self
    obtain ⟨c, hc⟩ := hpd
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have hdiv : p.1 / l = c := by rw [hc]; exact Nat.mul_div_cancel_left c hl
    have hcons : liftL q l (p :: L) = (List.range l).map (fun i => (p.1 / l, p.2 * q ^ i)) ++ liftL q l L := by
      simp [liftL, List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · rw [hcons]
      simp only [deg, List.map_append, List.sum_append, List.map_map] at ihd ⊢
      rw [ihd]
      simp [Function.comp_def, List.sum_replicate, hdiv, hc, Nat.mul_div_cancel_left c hl]
    · intro p' hp'
      rw [hcons, List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp'
        refine ⟨by simpa [hdiv] using hc0, ?_⟩
        simp only [hdiv]
        rw [hc] at hpr
        exact (GlobalTheory.Shin.reg_step_of_dvd q l c p.2 hq hl hc0 hpr).1 i
      · exact ihm p' hp'

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleModelDegree
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem flat_one_tmul_eq_zero_mem_map (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P) :
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  intro hI y hy
  subst hI
  set K := RingHom.ker (algebraMap P T)
  let f : (P ⧸ K) →ₗ[P] T := (Ideal.Quotient.liftₐ K (Algebra.ofId P T) (fun a ha => RingHom.mem_ker.mp ha)).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [f] using hab
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f hf
  have h0 : (1 : P ⧸ K) ⊗ₜ[P] y = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, map_zero]
    simpa [f] using hy
  have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L K) h0
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
section
open IsLocalRing

namespace GlobalTheory

namespace LocIndEtale

open Polynomial

lemma isIntegrallyClosed_of_forall_monic_root (T : Type) [CommRing T] [IsDomain T]
    (h : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  rintro x ⟨p, hpm, hp⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : p = 1 := hpm.natDegree_eq_zero.mp hn
      subst this
      simp at hp
    · obtain ⟨r, hr⟩ := h p hpm (hn ▸ hpos)
      have hroot : IsRoot p r := hr
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
      set q := p /ₘ (X - C r) with hq
      have hqm : q.Monic := by
        refine Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) ?_
        rw [hfac]; exact hpm
      have hqdeg : q.natDegree < n := by
        rw [hq, Polynomial.natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
        omega
      rw [← hfac, eval₂_mul] at hp
      rcases mul_eq_zero.mp hp with h1 | h1
      · refine ⟨r, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.mp h1).symm
      · exact ih _ hqdeg q hqm h1 rfl

end LocIndEtale

theorem locIndEtale_isDomain_isIntegrallyClosed :
    ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ∧ IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := by
  intro T O _ _ _ _ _ _ _ _ _ n hT _ _ hind
  haveI : IsIntegrallyClosed T := LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hT.2
  obtain ⟨hdom, hic⟩ := indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind

  have hinj : Function.Injective (algebraMap T O) := by
    obtain ⟨ι, _, _, _, Si, -, -, hloc⟩ := hind
    obtain ⟨A, _, _, _, P, _, ⟨e⟩⟩ := hloc (Classical.arbitrary ι)
    haveI : Module.Flat (Polynomial T) (Localization.AtPrime P) := inferInstance
    have hL : Function.Injective (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro f hf
      by_contra hne
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := Localization.AtPrime P) (mem_nonZeroDivisors_of_ne_zero hne)
      have h1 : f • (1 : Localization.AtPrime P) = f • 0 := by
        rw [Algebra.smul_def, hf, zero_mul, smul_zero]
      exact one_ne_zero (hreg h1)
    have hS : Function.Injective (algebraMap (Polynomial T) O) := by
      have : (algebraMap (Polynomial T) O) =
          (Si (Classical.arbitrary ι)).val.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial T) (Localization.AtPrime P))) := by
        ext f
        · simp
        · simp
      rw [this]
      exact Subtype.val_injective.comp (e.injective.comp hL)
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
    exact hS.comp Polynomial.C_injective
  have hle : Algebra.algebraMapSubmonoid O (nonZeroDivisors T) ≤ nonZeroDivisors O := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ht (hinj ?_)
    rw [h, map_zero]
  exact ⟨IsLocalization.isDomain_localization hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
section
open ValuativeRel
open scoped Matrix Topology

noncomputable section
namespace GlobalTheory.CondRescale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by
  by_contra hz
  push_neg at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have h1 := h n
  have h2 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖z ^ n‖ = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_pow, norm_one] at h2
  linarith

theorem exists_ball_trivial (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ0 t = 1 := by
  have hc : Continuous fun t : k => ‖ψ0 t - 1‖ := (hψ.sub continuous_const).norm
  have h0 : ‖ψ0 0 - 1‖ < 1 := by simp
  have hU : {t : k | ‖ψ0 t - 1‖ < 1} ∈ nhds (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hp : ∀ s : k, valuation k s < γ → ∀ n : ℕ, ‖ψ0 s ^ n - 1‖ < 1 := by
    intro s hs n
    have h1 : n • s ∈ {t : k | ‖ψ0 t - 1‖ < 1} :=
      hsub (lt_of_le_of_lt (GlobalTheory.CharDualMat.valuation_nsmul_le s n) hs)
    rw [Set.mem_setOf_eq, AddChar.map_nsmul_eq_pow] at h1
    exact h1
  have hneg : valuation k (-t) < γ := by rwa [Valuation.map_neg]
  have a1 := norm_le_one_of_pow_near _ (hp t ht)
  have a2 := norm_le_one_of_pow_near _ (hp (-t) hneg)
  have hm : ψ0 (-t) * ψ0 t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 t‖ = 1 := by
    have := congrArg norm hm
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg (ψ0 t), norm_nonneg (ψ0 (-t))]
  exact GlobalTheory.IrredSB.eq_one_of_forall_pow hn (hp t ht)

theorem exists_rescale_conductor_integers [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (hne : ψ0 ≠ 1) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (c * (x * y)) = 1) ↔ x ∈ 𝒪[k] := by
  classical
  let P : k → Prop := fun a => ∀ y ∈ 𝒪[k], ψ0 (a * y) = 1
  obtain ⟨t, ht⟩ : ∃ t : k, ψ0 t ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (AddChar.ext _ _ fun s => by simpa using hall s)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one _)
  have hbd : ∀ a, P a → a ≠ 0 → valuation k a < valuation k t := by
    intro a ha ha0
    by_contra hle
    push_neg at hle
    apply ht
    have hmem : t / a ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    have := ha _ hmem
    rwa [mul_div_cancel₀ _ ha0] at this
  obtain ⟨γ, hγ, hball⟩ := exists_ball_trivial ψ0 hψ
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  have hPr : P (r ^ m) := by
    intro y hy
    apply hball
    rw [map_mul, map_pow]
    calc valuation k r ^ m * valuation k y ≤ valuation k r ^ m * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 hy)
      _ < γ := by simpa using hm
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hex : ∀ a : k, a ≠ 0 → ∃ n : ℤ, e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro a ha
    have h1 : e (valuation k a) ≠ 0 := by
      intro h
      apply ha
      have : valuation k a = 0 := by
        have h2 : e (valuation k a) = e 0 := by rw [h, map_zero]
        exact e.injective h2
      simpa using this
    obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h1
    exact ⟨Multiplicative.toAdd u, by simpa using hu.symm⟩
  let Q : ℤ → Prop := fun n => ∃ a, P a ∧ a ≠ 0 ∧
    e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨N, hN⟩ := hex t ht0
  have hr0' : r ^ m ≠ 0 := pow_ne_zero _ hr0
  obtain ⟨n1, hn1⟩ := hex _ hr0'
  obtain ⟨n0, ⟨a0, ha0P, ha0, hn0⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := Q)
    ⟨N, fun n ⟨a, ha, ha0, hn⟩ => by
      have h1 : e (valuation k a) < e (valuation k t) := e.strictMono (hbd a ha ha0)
      rw [hn, hN, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt] at h1
      exact h1.le⟩ ⟨n1, r ^ m, hPr, hr0', hn1⟩
  have hdown : ∀ b, P b → b ≠ 0 → valuation k b ≤ valuation k a0 := by
    intro b hb hb0
    obtain ⟨n, hn⟩ := hex b hb0
    have h1 := hmax n ⟨b, hb, hb0, hn⟩
    have h2 : e (valuation k b) ≤ e (valuation k a0) := by
      rw [hn, hn0, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      exact h1
    exact (map_le_map_iff e).1 h2
  have hv0 : valuation k a0 ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  refine ⟨a0, ha0, fun x => ⟨fun hx => ?_, fun hx y hy => ha0P _ (mul_mem hx hy)⟩⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem _
  have hP : P (a0 * x) := fun y hy => by
    rw [mul_assoc]
    exact hx y hy
  have h1 := hdown _ hP (mul_ne_zero ha0 hx0)
  rw [Valuation.mem_integer_iff]
  have h2 : valuation k x = valuation k (a0 * x) / valuation k a0 := by
    rw [map_mul, mul_div_cancel_left₀ _ hv0]
  rw [h2]
  exact (div_le_one₀ (zero_lt_iff.2 hv0)).2 h1

end GlobalTheory.CondRescale
end
end

