module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionMod
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_redGL_eq {N : ℕ} (g : GL (Fin 2) (ZMod N))
    (hg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1) : ∃ γ : SL(2, ℤ), redGL N γ = g := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) N ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod N)), hg⟩
  refine ⟨γ, Units.ext ?_⟩
  show ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [hγ]; rfl

theorem dg_conj_lift : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  intro N _ u
  have hdet : ∀ γ : SL(2, ℤ), Matrix.det ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro γ
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).2
  have hconj : ∀ (a g : GL (Fin 2) (ZMod N)), Matrix.det ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) = 1 →
      Matrix.det (((a⁻¹ * g * a : GL (Fin 2) (ZMod N))) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro a g hg
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hg, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine ⟨fun γ => ?_, fun γ' => ?_⟩
  · obtain ⟨γ', h⟩ := exists_redGL_eq _ (hconj (dg u) (redGL N γ) (hdet γ))
    refine ⟨γ', ?_⟩
    rw [h]; group
  · obtain ⟨γ, h⟩ := exists_redGL_eq _ (hconj (dg u)⁻¹ (redGL N γ') (hdet γ'))
    refine ⟨γ, ?_⟩
    rw [h]; group

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChange
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ

theorem pot_triv_lin : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  intro R _ w Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [← hp z hz, ← hq z hz]; abel
  · refine ⟨fun z => MvPolynomial.isHomogeneous_zero _ _ _, fun γ _ => ⟨0, fun z _ => ?_⟩⟩
    simp
  · rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => ?_, fun γ hγ => ?_⟩
    · simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (hF z)
    · obtain ⟨p, hp⟩ := hF' γ hγ
      refine ⟨c • p, fun z hz => ?_⟩
      simp only [Pi.smul_apply, map_smul]
      rw [← hp z hz, smul_sub]
  · rintro F G ⟨ψ, p, hψ, hp⟩ ⟨ψ', p', hψ', hp'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.add_apply, map_add (f := _), hψ γ hγ z hz, hψ' γ hγ z hz]
    · simp only [Pi.add_apply, hp z hz, hp' z hz]; abel
  · rintro c F ⟨ψ, p, hψ, hp⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.smul_apply, map_smul, hψ γ hγ z hz]
    · simp only [Pi.smul_apply, hp z hz, smul_add]
  · rintro S _ f F ⟨hF, hF'⟩
    refine ⟨fun z => (hF z).map f, fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨MvPolynomial.map f p, fun z hz => ?_⟩
    rw [← (polySlash_laws R).2.2.2.2.1 S f, ← map_sub, hp z hz]
  · rintro S _ f F ⟨ψ, p, hψ, hp⟩
    refine ⟨fun z => MvPolynomial.map f (ψ z), MvPolynomial.map f p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only
      rw [← (polySlash_laws R).2.2.2.2.1 S f, hψ γ hγ z hz]
    · simp only [hp z hz, map_add (f := _)]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosure
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgPowerSeries

theorem mem_range_map_iff {L : Type} [CommRing L] (B : Subring L) (f : PowerSeries L) :
    f ∈ (PowerSeries.map B.subtype).range ↔ ∀ k, PowerSeries.coeff k f ∈ B := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k g).2
  · intro h
    refine ⟨PowerSeries.mk fun k => ⟨PowerSeries.coeff k f, h k⟩, ?_⟩
    ext k; simp [PowerSeries.coeff_map]

theorem exists_finset_coeff_mem_closure :
    ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L)
      (Q : Polynomial (PowerSeries L)), Q ≠ 0 →
      (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 →
      ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  classical
  intro L _ _ A b Q hQ hA hb
  obtain ⟨RA, hRAdef⟩ : ∃ RA : Subring (PowerSeries L), RA = (PowerSeries.map A.subtype).range :=
    ⟨_, rfl⟩
  have hex : ∃ d, ∃ R : Polynomial (PowerSeries L), R ≠ 0 ∧ (∀ i, R.coeff i ∈ RA) ∧
      R.eval b = 0 ∧ R.natDegree = d :=
    ⟨Q.natDegree, Q, hQ, fun i => hRAdef ▸ (mem_range_map_iff A _).2 (hA i), hb, rfl⟩
  obtain ⟨R, hR0, hRA', hRb, hRd⟩ := Nat.find_spec hex
  have hmin : ∀ R' : Polynomial (PowerSeries L), R' ≠ 0 → (∀ i, R'.coeff i ∈ RA) →
      R'.natDegree < R.natDegree → R'.eval b ≠ 0 := by
    intro R' h0 hc hlt he
    exact Nat.find_min hex (by omega) ⟨R', h0, hc, he, rfl⟩
  have hdeg : R.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C] at hRb
    apply hR0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hRb, map_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Polynomial.derivative R := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    haveI : HasUniqueDiv (PowerSeries L) := IsAddTorsionFree.of_isTorsionFree L _
    intro h; rw [hD] at h; exact hdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h)
  have hDc : ∀ i, D.coeff i ∈ RA := by
    intro i; rw [hD, Polynomial.coeff_derivative]
    exact RA.mul_mem (hRA' _) (RA.add_mem (natCast_mem RA _) RA.one_mem)
  have hDb : D.eval b ≠ 0 :=
    hmin D hD0 hDc (hD ▸ Polynomial.natDegree_derivative_lt hdeg)
  obtain ⟨F, hF⟩ : ∃ F, F = D.eval b := ⟨_, rfl⟩
  have hex2 : ∃ m, PowerSeries.coeff m F ≠ 0 := by
    by_contra h; push_neg at h; exact hDb (hF ▸ PowerSeries.ext fun k => by simpa using h k)
  obtain ⟨m, hc, hlow⟩ : ∃ m, PowerSeries.coeff m F ≠ 0 ∧ ∀ i < m, PowerSeries.coeff i F = 0 :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun i hi => not_not.mp (Nat.find_min hex2 hi)⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = PowerSeries.coeff m F := ⟨_, rfl⟩
  rw [← hcdef] at hc
  refine ⟨insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b), ?_⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = Subring.closure ((A : Set L) ∪
      ↑(insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b))) := ⟨_, rfl⟩
  rw [← hBdef]
  have hAB : ∀ x ∈ A, x ∈ B := fun x hx => hBdef ▸ Subring.subset_closure (Or.inl hx)
  have hcB : c⁻¹ ∈ B := hBdef ▸ Subring.subset_closure (Or.inr (by simp))
  have hbB : ∀ i ≤ m, PowerSeries.coeff i b ∈ B := fun i hi =>
    hBdef ▸ Subring.subset_closure (Or.inr (by simp; exact Or.inr ⟨i, by omega, rfl⟩))
  obtain ⟨RB, hRBdef⟩ : ∃ RB : Subring (PowerSeries L), RB = (PowerSeries.map B.subtype).range :=
    ⟨_, rfl⟩
  have hRARB : ∀ f ∈ RA, f ∈ RB := fun f hf => by
    rw [hRBdef]; rw [hRAdef] at hf
    exact (mem_range_map_iff B f).2 fun k => hAB _ ((mem_range_map_iff A f).1 hf k)
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases le_or_gt n m with hnm | hmn
  · exact hbB n hnm
  obtain ⟨u, hu⟩ : ∃ u : PowerSeries L,
      u = PowerSeries.mk fun k => if k < n then PowerSeries.coeff k b else 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : PowerSeries L,
      v = PowerSeries.mk fun k => PowerSeries.coeff (n + k) b := ⟨_, rfl⟩
  have hbuv : b = u + PowerSeries.X ^ n * v := by
    ext k
    rw [map_add (f := _), PowerSeries.coeff_X_pow_mul', hu, hv]
    simp only [PowerSeries.coeff_mk]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · rw [if_neg h1, if_pos (by omega), zero_add, show n + (k - n) = k by omega]
  have huB : u ∈ RB := by
    rw [hRBdef]
    refine (mem_range_map_iff B u).2 fun k => ?_
    rw [hu, PowerSeries.coeff_mk]; split_ifs with h
    · exact ih k h
    · exact B.zero_mem
  have hRu : R.eval u ∈ RB := by
    rw [Polynomial.eval_eq_sum_range]
    exact RB.sum_mem fun i _ => RB.mul_mem (hRARB _ (hRA' i)) (RB.pow_mem huB _)
  have hdvd : PowerSeries.X ^ n ∣ F - D.eval u := by
    have h1 := Polynomial.sub_dvd_eval_sub b u D
    have h2 : b - u = PowerSeries.X ^ n * v := by rw [hbuv]; ring
    rw [h2, ← hF] at h1
    exact (dvd_mul_right _ _).trans h1
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨k, hk⟩ := R.binomExpansion u (PowerSeries.X ^ n * v)
  rw [← hbuv, hRb, ← hD] at hk
  have hDu : D.eval u = F - PowerSeries.X ^ n * w := by rw [← hw]; ring
  rw [hDu] at hk
  have key : 0 = R.eval u + PowerSeries.X ^ n * (F * v) +
      PowerSeries.X ^ (n + n) * (k * v ^ 2 - w * v) := by
    rw [hk]; ring
  have hc2 := congrArg (PowerSeries.coeff (n + m)) key
  rw [map_zero, map_add (f := _), map_add (f := _), PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), if_neg (by omega), add_zero, Nat.add_sub_cancel_left] at hc2
  have hFv : PowerSeries.coeff m (F * v) = c * PowerSeries.coeff n b := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
    · rw [← hcdef, hv, PowerSeries.coeff_mk, add_zero]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = m := by simpa using hij
      have him : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exfalso; apply hne; simp only [Prod.mk.injEq]; omega
      rw [hlow i him, zero_mul]
    · intro h; exfalso; exact h (by simp)
  have hcn : c * PowerSeries.coeff n b ∈ B := by
    have e : c * PowerSeries.coeff n b = - PowerSeries.coeff (n + m) (R.eval u) := by
      linear_combination -hc2 - hFv
    rw [e]
    rw [hRBdef] at hRu
    exact B.neg_mem ((mem_range_map_iff B _).1 hRu _)
  have e2 : PowerSeries.coeff n b = c⁻¹ * (c * PowerSeries.coeff n b) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e2]; exact B.mul_mem hcB hcn

end GlobalTheory.AlgPowerSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZero
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gamma_le_gamma_of_dvd {K M : ℕ} (h : K ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma K := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h2
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h3
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h4

theorem mem_gam_of_mem_gamma {N l : ℕ} {δ : SL(2, ℤ)} (hN : δ ∈ CongruenceSubgroup.Gamma N)
    (hl : δ ∈ CongruenceSubgroup.Gamma l) : δ ∈ Gam N l := by
  rw [CongruenceSubgroup.Gamma_mem] at hN hl
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem N δ).2 ⟨hN.1, hN.2.2.2, hN.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 hl.2.2.1

theorem cls_pow_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : X.Kˣ) : X.cls l n (g ^ (l ^ n)) = 0 := by
  unfold Tower.cls
  rw [Submodule.Quotient.mk_eq_zero]
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul (g ^ (l ^ n)) : X.Kl l) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul g : X.Kl l) := by
    rw [ofMul_pow, TensorProduct.tmul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

theorem eq_zero_of_btZ_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  intro Ω _ _ _ ε X hε hj N l hl hN b hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, ⟨f, a, c, M₁, hM₁, hev, ⟨ha, hc, hc0, hroot⟩, hinv⟩, M₂, hM₂, hχ⟩ := hb n u
  have hlpos : 0 < l := hl.out.pos
  obtain ⟨g, hg⟩ := kummer_root_mem ε X hε hj (l ^ n) (pow_pos hlpos n) f a c (M₁ * M₂ * N * l)
    (by positivity) ha hc hc0 hroot (by
      intro γ hγ
      have h1 : γ ∈ CongruenceSubgroup.Gamma M₁ := gamma_le_gamma_of_dvd ⟨M₂ * N * l, by ring⟩ hγ
      have h2 : γ ∈ CongruenceSubgroup.Gamma M₂ := gamma_le_gamma_of_dvd ⟨M₁ * N * l, by ring⟩ hγ
      have h3 : γ ∈ CongruenceSubgroup.Gamma N := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * l, by ring⟩ hγ
      have h4 : γ ∈ CongruenceSubgroup.Gamma l := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * N, by ring⟩ hγ
      have h0 : χ γ = 0 := by
        have := hχ ⟨γ, mem_gam_of_mem_gamma h3 h4⟩ h2
        simpa using this.symm
      refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz => ?_)
      have := hinv γ h1 z hz
      rw [h0] at this
      simpa using this)
  have : AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
    rw [hev, hg, cls_pow_eq_zero]
  exact this

end GlobalTheory.KZ.BettiB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvNormOpEqNrm
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem ev_normOp_eq_nrm (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (h : PowerSeries R) :
    ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  obtain ⟨b, hb⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hR
  letI iA : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI iM : Module (PowerSeries R) (PowerSeries R) := @Algebra.toModule _ _ _ _ iA
  letI iS : SMul (PowerSeries R) (PowerSeries R) := iM.toSMul
  have F1 : ∀ x : PowerSeries R, ∑ i, phi (R := R) p hp.out.pos (b.repr x i) * (1 + X) ^ (i : ℕ) = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]; rfl
  have F3 : ∀ (d : Fin p → PowerSeries R) (i : Fin p),
      b.repr (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) i = d i := by
    intro d i
    have h1 : (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = b.equivFun.symm d := by
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j]; rfl
    rw [h1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have F2 : ∀ (a x : PowerSeries R) (i : Fin p),
      b.repr (phi (R := R) p hp.out.pos a * x) i = a * b.repr x i := by
    intro a x i
    have : phi (R := R) p hp.out.pos a * x = a • x := rfl
    rw [this, LinearEquiv.map_smul]; rfl

  letI iU : Algebra (lev R p m) (lev R p (m + 1)) := (up (R := R) p m hm).toAlgebra
  have hup : ∀ a : PowerSeries R, up (R := R) p m hm (ev R p m a) = ev R p (m + 1) (phi (R := R) p hp.out.pos a) :=
    fun a => rfl
  have hsm : ∀ (a : PowerSeries R) (y : PowerSeries R),
      ev R p (m + 1) (phi (R := R) p hp.out.pos a * y) = (ev R p m a) • ev R p (m + 1) y := by
    intro a y
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hup, map_mul]
  let v : Fin p → lev R p (m + 1) := fun i => ev R p (m + 1) ((1 + X) ^ (i : ℕ))
  have hli : LinearIndependent (lev R p m) v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    choose d hd using fun i => Ideal.Quotient.mk_surjective (g i)
    have hx : ev R p (m + 1) (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hg, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsm, ← hd j]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rw [← phi_cyc (R := R) p m hm, mul_comm] at ha
    have := F3 d i
    rw [← ha, F2] at this
    rw [← hd i, ← this, map_mul]
    have h0 : ev R p m (cyc R p m) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [h0, zero_mul]
  have hsp : ⊤ ≤ Submodule.span (lev R p m) (Set.range v) := by
    intro z _
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    show ev R p (m + 1) y ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← F1 y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin p) (lev R p m) (lev R p (m + 1)) := Module.Basis.mk hli hsp
  have G : ∀ (y : PowerSeries R) (i : Fin p), b'.repr (ev R p (m + 1) y) i = ev R p m (b.repr y i) := by
    intro y i
    have e1 : ev R p (m + 1) y = b'.equivFun.symm (fun i => ev R p m (b.repr y i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← F1 y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.mk_apply, hsm]
    rw [e1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  unfold nrm normOp
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.mk_apply, ← map_mul, G, hb]

end GlobalTheory.Col
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureAutomorphismRestrictingLocal
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_extend_of_embedding :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  intro Ω _ ε s
  letI : Algebra Ω ℂ := ε.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis Ω ℂ
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let e := hB.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv B s).trans hB.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : ∀ y : Ω,
      algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.C y)) = ε y := fun y => by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  conv_lhs => rw [← h1 x]
  rw [IsAlgClosure.equivOfEquiv_algebraMap, ← h1 (s x)]
  congr 1
  simp [e]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePointStatement
section
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariantStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponents_integral_of_translation_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K), X.sl (ofSL ModularGroup.T) h = h → ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ m : ℤ, r = m := by
  first | exact @GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | exact GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | (intros; apply GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant <;> assumption)
end

