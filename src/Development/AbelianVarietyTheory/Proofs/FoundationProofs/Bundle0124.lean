module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePowStatement
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
      IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) →
      ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e →
      ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨v, hv, _, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hclo
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoeffwiseConjugateOfIntegralQuotient
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

theorem conjEx_hasQ_zero (N : ℕ) : HasQ N (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ => by
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem conjEx_conv_coeff (a b : ℕ → ℂ) (n : ℕ) :
    conv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [conv, PowerSeries.coeff_mul]

theorem conjEx_conv_map (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) :
    (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) := by
  funext n; simp [conv, map_sum, map_mul]

theorem conjEx_conv_cancel (a b d : ℕ → ℂ) (hd : d ≠ 0) (h : conv a d = conv b d) : a = b := by
  have hmk : PowerSeries.mk d ≠ 0 := by
    intro h0; apply hd; funext n
    have := congrArg (PowerSeries.coeff n) h0
    simpa using this
  have hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d := by
    ext n
    have := congrFun h n
    rwa [conjEx_conv_coeff, conjEx_conv_coeff] at this
  have := mul_right_cancel₀ hmk hm
  funext n
  have := congrArg (PowerSeries.coeff n) this
  simpa using this

theorem conj_exists : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  intro g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol
  obtain ⟨uc, uf⟩ := GlobalTheory.QFam.hasQ_unique_both
  have hz := conjEx_hasQ_zero N
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (uf N D (fun _ => 0) _ hd hz)
  have hgd0 : (fun n => g (d n)) ≠ 0 := by
    intro h0; apply hd0; funext k
    have := congrFun h0 k
    simpa using this
  have hD' : D' ≠ 0 := by
    rintro rfl
    exact hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)
  obtain ⟨_, hadd, _, hmul, hpow, hsumprod⟩ := GlobalTheory.QFam.qConj_ring g N hN
  have hA : QConj g N A A' := ⟨e, he, he'⟩
  have hDD : QConj g N D D' := ⟨d, hd, hd'⟩
  have hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) := by
    refine hadd _ _ _ _ (hpow _ _ n hA) ?_
    refine (hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1
    intro j _
    exact hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)
  have hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0 := by
    funext τ
    have hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) =
        D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ)) := by
      rw [mul_add, Finset.mul_sum, ← hfA τ, mul_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
        ring
    rw [hx, hpol τ, mul_zero]
  have hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0 := by
    obtain ⟨c, hc, hc'⟩ := hP
    rw [hP0] at hc
    have hc0 : c = fun _ => 0 := uc N _ _ _ hN hc hz
    subst hc0
    simp only [map_zero] at hc'
    have := uf N _ _ _ hc' hz
    exact fun τ => congrFun this τ
  obtain ⟨h, b, hb, hAh⟩ := _root_.GlobalTheory.FN.hasQ_of_integral_quot N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩
    (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0
  have hfD : HasQ N A (conv a d) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd
    have hAe : (fun τ => f τ * D τ) = A := funext hfA
    rwa [hAe] at this
  have he1 : e = conv a d := uc N A _ _ hN he hfD
  have hhD : HasQ N A' (conv b fun n => g (d n)) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'
    have hAe : (fun τ => h τ * D' τ) = A' := funext fun τ => (hAh τ).symm
    rwa [hAe] at this
  have he2 : (fun n => g (e n)) = conv b fun n => g (d n) := uc N A' _ _ hN he' hhD
  rw [he1, conjEx_conv_map] at he2
  have hba : b = fun n => g (a n) := (conjEx_conv_cancel _ _ _ hgd0 he2).symm
  refine ⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem inR_algebraMap {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (c : O0 p) :
    ∃ c' : O0 p, ψ c' = algebraMap (O0 p) Ω c := by
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  exact hmem

theorem inR_pow {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) (k : ℕ) : InR ψ (x ^ k) := by
  induction k with
  | zero => simpa using inR_psi ψ 1
  | succ k ih => rw [pow_succ]; exact inR_mul ih hx

theorem exists_inR_mul_eq_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 →
    ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  intro p _ Ω _ _ hc T n ψ h N hN hN0
  obtain ⟨f, hfm, hf⟩ : IsIntegral (O0 p) N := hN.isInt h
  have key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 →
      ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro f hk hfm hf
      by_cases h0 : f.coeff 0 = 0
      · obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.2 h0
        have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm
        have hgdeg : g.natDegree < k := by
          rw [← hk, Polynomial.natDegree_X_mul hgm.ne_zero]; omega
        refine ih _ hgdeg g rfl hgm ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hf
        exact (mul_eq_zero.1 hf).resolve_left hN0
      · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)
        obtain ⟨D, hD⟩ := inR_algebraMap h (-f.coeff 0)
        refine ⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩
        · rw [Polynomial.eval₂_eq_sum_range]
          refine inR_sum _ _ fun i _ => ?_
          obtain ⟨c', hc'⟩ := inR_algebraMap h (g.coeff i)
          rw [← hc']
          exact inR_mul (inR_psi ψ c') (inR_pow hN i)
        · rintro rfl
          rw [map_zero, map_neg] at hD
          apply h0
          apply hc.inj
          rw [map_zero (algebraMap (O0 p) Ω)]
          exact neg_eq_zero.mp hD.symm
        · have hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0) := by
            rw [← hg]; ring
          rw [hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
          rw [hD, map_neg]
          linear_combination hf
  exact key _ f rfl hfm hf

end GlobalTheory.GeoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_level_one : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) →
    ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  intro g w N F hN hinv ⟨a, ha⟩
  have hmf : IsMF (w : ℤ) F := GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha
  obtain ⟨s, c, hwt, hF⟩ := GlobalTheory.QFam.isMF_eq_sum_monomials w F hmf
  refine ⟨fun τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2), ?_, ?_⟩
  ·
    let act : Unit → SL(2, ℤ) → Unit := fun i _ => i
    have hfam : IsFam act (w : ℤ)
        (fun _ τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) := by
      refine IsFam.sum_fun s (f := fun p _ τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
      intro p hp
      have h4 := (isFam_const_E4 Unit act).pow_fun p.1
      have h6 := (isFam_const_E6 Unit act).pow_fun p.2
      have hm := (h4.mul_fun h6).const_mul_fun (g (c p))
      have e : ((p.1 : ℕ) : ℤ) * 4 + ((p.2 : ℕ) : ℤ) * 6 = (w : ℤ) := by
        rw [← hwt p hp]; push_cast; ring
      rw [e] at hm
      exact hm
    intro γ
    exact hfam () γ
  · have hFe : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
    rw [hFe]
    refine QConj.sum s (f := fun p τ => c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2))
      (f' := fun p τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
    intro p _
    have h4 : QConj g N ⇑E₄ ⇑E₄ := eis_qConj N hN _ (Or.inl rfl) g
    have h6 : QConj g N ⇑E₆ ⇑E₆ := eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
    exact QConj.mul hN (QConj.const g N (c p))
      (QConj.mul hN (QConj.pow hN p.1 h4) (QConj.pow hN p.2 h6))

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExpD

theorem hasQ_DD_int : HasQ 1 DD fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : ℂ) := by
  rw [hasQ_iff]
  intro τ
  have := ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ
  rw [← ReciprocityTheory.ChartRestriction.L1.dC_eq] at this
  simpa [ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map] using this

theorem expD : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧
    h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  have hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω) := by
    simpa only [map_intCast] using hasQ_DD_int
  obtain ⟨h, hexp, hk, hz⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε 1 DD
    (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD
  have h1 : h.coeff 1 = 1 := by
    have := hk 1
    simpa [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one] using this
  have hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0 := by
    intro r hr
    by_cases hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr'
      have hk1 : (k : ℚ) < 1 := by simpa using hr
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast hk1
        omega
      subst hk0
      rw [hk 0]
      simp [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]
    · push_neg at hr'
      exact hz r hr'
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)
  have hord : h.order = 1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_
    by_contra hlt
    push_neg at hlt
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)
  refine ⟨h, hexp, hne, ?_, ?_⟩
  · rw [HahnSeries.leadingCoeff_eq, hord, h1]
  · intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr
      exact ⟨_, hk k⟩
    · push_neg at hr
      exact ⟨0, by simpa using hz r hr⟩

end GlobalTheory.FNExpD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.CycDec

theorem exists_unit_infinite_order (l : ℕ) [Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ∀ n : ℤ, n ≠ 0 → u ^ n ≠ 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun n hn h => ?_⟩
  have h1 : u ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with e | e
    · rw [← zpow_natCast, ← e, h]
    · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h
      exact h
  have h2 : (((1 + l) ^ n.natAbs : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  rw [pow_eq_one_iff] at h3
  rcases h3 with h3 | h3
  · exact hl.ne_zero (by omega)
  · exact hn (Int.natAbs_eq_zero.1 h3)

theorem exists_mem_Dec_cycZ_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 →
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ v A hl hA n hn
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  refine ⟨g, hD, ?_⟩
  rw [hc, map_pow, hσu, ← zpow_natCast, ← zpow_mul]
  exact hu _ (mul_ne_zero (by exact_mod_cast hN.ne') hn)

end GlobalTheory.CycDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenbergStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_representation_heisenberg : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, e ≠ 0 → Fixes W A e → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ Om g e = normOp lam W A (A.map (ρ g)) e := by
  first | exact @GlobalTheory.FinWeil.exists_weil_rep | exact GlobalTheory.FinWeil.exists_weil_rep | (intros; apply GlobalTheory.FinWeil.exists_weil_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  first | exact @GlobalTheory.KZ.H3.kum_smul | exact GlobalTheory.KZ.H3.kum_smul | (intros; apply GlobalTheory.KZ.H3.kum_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarModStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jTranslates_level_and_scalar_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ m : ℕ, 0 < m → (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), Lev X m (X.sl (toGQ g) X.jK)) ∧ ∀ γ : SL(2, ℤ), (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (ofSL γ) (X.sl (toGQ g) X.jK) = X.sl (toGQ g) X.jK) → (en γ 0 1 : ZMod m) = 0 ∧ (en γ 1 0 : ZMod m) = 0 ∧ (en γ 0 0 : ZMod m) = en γ 1 1 := by
  first | exact @GlobalTheory.KZ.ES.Scal.lev_and_scalar | exact GlobalTheory.KZ.ES.Scal.lev_and_scalar | (intros; apply GlobalTheory.KZ.ES.Scal.lev_and_scalar <;> assumption)
end

