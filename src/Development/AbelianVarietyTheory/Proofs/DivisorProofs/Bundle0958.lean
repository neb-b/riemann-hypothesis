module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertClassFieldLatticeTransport
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn coordIn_div)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.TransportProof
theorem exists_sq_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := _root_.GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg

theorem nrm_eq_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := _root_.GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := _root_.GlobalTheory.CMVal.ModFRat.modF_rat

theorem modF_upIdele : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := GlobalTheory.T.modF_finiteIdeleUpToExtension

theorem card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := _root_.GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType

theorem norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := _root_.GlobalTheory.CMVal.norm_conj_finPart

theorem algebraic_coordIn_toric : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := _root_.GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := _root_.GlobalTheory.ConjCoordToric.conj_coordIn_toric

theorem equidistributed_of_j : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := _root_.GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ

theorem isTotallyComplex_of_discr_neg {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (h : discr K < 0) : IsTotallyComplex K := by
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hs
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h2] at hr
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    rcases Nat.even_or_odd (InfinitePlace.nrComplexPlaces K) with he | ho
    · rw [he.neg_one_pow] at hs; norm_num at hs
    · obtain ⟨k, hk⟩ := ho; omega
  exact nrRealPlaces_eq_zero_iff.1 (by omega)

theorem disc_j_of_torsTransport {K : Type} [Field K] [NumberField K] {ι : K →+* ℂ} {g : ℂ ≃+* ℂ} {t : (Af K)ˣ}
    {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    Ω₁ ^ 12 = latDisc Λ₁ ∧ jLat Λ₁ = g (jLat Λ₀) := by
  obtain ⟨h0, h1, -, -, -, ha, hb, -⟩ := hT
  have e0 : (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 - 27 * (Λ₀.g₃ / Ω₀ ^ 6) ^ 2 = 1 := by
    have : latDisc Λ₀ / Ω₀ ^ 12 = 1 := by rw [← hΩ, div_self (pow_ne_zero _ h0)]
    rw [← this, latDisc]; field_simp
  have e1 : (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 - 27 * (Λ₁.g₃ / Ω₁ ^ 6) ^ 2 = 1 := by
    rw [← ha, ← hb]
    have := congrArg g e0
    simpa [map_sub, map_pow, map_mul, map_ofNat] using this
  have hD : Ω₁ ^ 12 = latDisc Λ₁ := by
    rw [latDisc]; field_simp at e1; linear_combination -e1
  refine ⟨hD, ?_⟩
  have j0 : jLat Λ₀ = 1728 * (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 := by
    rw [jLat, ← hΩ]; field_simp
  have j1 : jLat Λ₁ = 1728 * (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 := by
    rw [jLat, ← hD]; field_simp
  rw [j0, j1, map_mul, map_pow, ha, map_ofNat]

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ := by
  unfold condQ
  rw [← Ideal.zero_eq_bot]
  refine mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem norm_lamF_conj_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (h2 : Module.finrank ℚ K = 2) (φ : I → E →+* ℂ) (hE : UnramFin E)
    (hφ : IsCMType φ) (s : ℕ) (κ κ' : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (χ χ' : HChar E) (hχ : IsValChar φ s κ 𝔣 Q χ)
    (σ : ℂ ≃+* ℂ) (hc : IsConjChar φ s κ' σ χ χ') (t : (Af K)ˣ) :
    ‖lamF s χ' (upIdele K E t)‖ = modF t ^ (s * Fintype.card I) := by
  have hu := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have h1 := norm_conj_finPart φ hφ s κ (condQ 𝔣 Q) (condQ_ne_bot h𝔣 Q) χ hχ.2.2.1 hu σ (upIdele K E t)
  obtain ⟨q, hq⟩ := modF_rat (upIdele K E t)
  have hpos := GlobalTheory.CMVal.IdeleModule.modF_pos (upIdele K E t)
  rw [hc.1, lamF, map_mul, norm_mul, h1, one_mul]
  have e : (((modF (upIdele K E t)) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) := by rw [hq]; push_cast; rfl
  rw [e, map_ratCast, ← e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), modF_upIdele, ← card_eq_finrank φ hφ h2,
    ← pow_mul, mul_comm]

theorem beta_eq_coordIn_pow (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (Ω T : ℂ) (Λ : PeriodPair) (h : Ω ^ 12 = latDisc Λ) : beta E d s κ Λ T = coordIn E d s κ Ω T ^ 12 := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem transportFor_of (hA : LatAlg) (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (hd : 0 < d)
    (δ : K) (hδ : δ ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair)
    (hΛ : IsLatOf φK 1 ΛK) (Ω₀ : ℂ) (hΩ₀ : Ω₀ ^ 12 = latDisc ΛK) (hΩ₀0 : Ω₀ ≠ 0)
    (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (Ω : (ℂ ≃+* ℂ) → ℂ)
    (hT : ∀ σ, Fixes φK σ →
      TorsTransport φK σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) ∧ IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K))
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (hE : UnramFin E)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = φK)
    (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (hs : 1 ≤ s) (h𝔣 : IsBaseCond 𝔣) :
    TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣 := by
  have hC0 : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  have conj : ∀ σ, Fixes φK σ → ∀ κ', IsConjWt φ σ κ κ' → ∀ Q χ T χ' T', IsValSum φ s κ 𝔣 Q χ T →
      IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
      σ (coordIn E d s κ Ω₀ T) = coordIn E d s κ (Ω σ) ((((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
        (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
    intro σ hσ κ' hκ' Q χ T χ' T' hV hV'
    rw [nrm_eq_modF _ _ (hT σ hσ).2]
    exact conj_coordIn_toric hC d δ φK h2 hd hδ σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) hΩ₀ (hT σ hσ).1 φ hE hφ hφK s hs
      κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  refine ⟨fun Q χ T hV => ⟨?_, fun σ hσ κ' hκ' χ' T' hV' => ?_⟩,
    fun Q₁ Q₂ χ₁ χ₂ T₁ T₂ hV₁ hV₂ hT₂ => ⟨?_, fun σ hσ κ' hκ' χ₁' χ₂' T₁' T₂' hV₁' hV₂' => ?_⟩⟩
  · rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV).pow 12
  · have hD := (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).1
    set N := nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) with hN
    have hN0 : N ≠ 0 := nrm_ne_zero _
    have hNpos : 0 < N := lt_of_le_of_ne (by rw [hN, nrm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _) hN0.symm
    have e : σ (beta E d s κ ΛK T) = beta E d s κ (Λ σ)
        ((((N : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
      rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀, map_pow, conj σ hσ κ' hκ' Q χ T χ' T' hV hV',
        beta_eq_coordIn_pow E d s κ (Ω σ) _ (Λ σ) hD]
    have hl := norm_lamF_conj_up h2 φ hE hφ s κ κ' 𝔣 h𝔣 Q hV.1 χ χ' hV.2.1 σ hV'.1 (t σ)
    rw [← nrm_eq_modF _ _ (hT σ hσ).2, ← hN] at hl
    refine ⟨by rw [e, beta_eq]; ring, ?_⟩
    rw [e, beta_eq, norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hl, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos,
      abs_of_pos (cmValueConst_pos E hd (by omega) κ)]
    have hDn : ‖latDisc (Λ σ)‖ ≠ 0 := norm_ne_zero_iff.2 (latDisc_ne_zero _)
    field_simp
    ring
  · rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, div_eq_mul_inv]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₁ χ₁ T₁ hV₁).mul
      (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₂ χ₂ T₂ hV₂).inv
  · have hΩσ : Ω σ ≠ 0 := (hT σ hσ).1.2.1
    set m : ℂ := (((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (∑ i, κ i)) with hm
    have hm0 : m ≠ 0 := pow_ne_zero _ (by exact_mod_cast nrm_ne_zero _)
    have c1 := conj σ hσ κ' hκ' Q₁ χ₁ T₁ χ₁' T₁' hV₁ hV₁'
    have c2 := conj σ hσ κ' hκ' Q₂ χ₂ T₂ χ₂' T₂' hV₂ hV₂'
    have hc2 : coordIn E d s κ Ω₀ T₂ ≠ 0 := by
      rw [coordIn]; exact div_ne_zero (mul_ne_zero hC0 hT₂) (pow_ne_zero _ hΩ₀0)
    have hT2' : T₂' ≠ 0 := by
      rintro rfl
      have := (map_ne_zero σ).2 hc2
      rw [c2, mul_zero, coordIn, mul_zero, zero_div] at this
      exact this rfl
    refine ⟨hT2', ?_⟩
    rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, map_div₀, c1, c2, coordIn_div E hd hs κ hΩσ, mul_assoc, mul_assoc,
      mul_div_mul_left _ _ (inv_ne_zero hm0)]

theorem transport_of (hH : GlobalTheory.Published.HilbertClassFieldJ) (hA : LatAlg) (hC : LatConj) : Transport := by
  intro K _ _ d hd h2 hdisc φK ΛK hΛ
  have hTC : IsTotallyComplex K := isTotallyComplex_of_discr_neg h2 (by rw [hdisc]; omega)
  obtain ⟨δ, hδ⟩ := exists_sq_eq_neg K d h2 hdisc
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc ΛK) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by rintro rfl; exact latDisc_ne_zero ΛK (by rw [← hΩ₀]; norm_num)
  have key : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ (t : (Af K)ˣ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair) (Ω : ℂ),
      TorsTransport φK σ t ΛK Λ Ω₀ Ω ∧ IsInvIdealOf t (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
        IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λ := by
    intro σ hσ
    letI : Algebra K ℂ := φK.toAlgebra
    obtain ⟨X, hX, ξ, hξ, hTr⟩ := GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport h2 φK ΛK Ω₀ hΛ hΩ₀0
    haveI := hX
    let σK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := σ) hσ
    obtain ⟨t, ht⟩ := GlobalTheory.EllipticCM.exists_transports h2 σK one_ne_zero hξ
    obtain ⟨Λ₁, Ω₁, h1⟩ := hTr σK t ht
    obtain ⟨𝔞, h𝔞t, h𝔞Λ⟩ := h1.2.2.2.2.1
    have h𝔞0 : 𝔞 ≠ 0 := by
      rintro rfl
      have hm : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := PeriodPair.ω₁_mem_lattice Λ₁
      rw [h𝔞Λ] at hm
      obtain ⟨x, hx, hx'⟩ := hm
      have hx0 : x = 0 := by simpa using hx
      rw [hx0, map_zero] at hx'
      exact (by simpa using Λ₁.indep.ne_zero 0 : Λ₁.ω₁ ≠ 0) hx'.symm
    exact ⟨t, Units.mk0 𝔞 h𝔞0, Λ₁, Ω₁, h1, h𝔞t, h𝔞Λ⟩
  haveI : Nonempty PeriodPair := ⟨ΛK⟩
  choose! t 𝔞 Λ Ω hT using key
  refine ⟨t, 𝔞, Λ, fun σ hσ => ⟨(hT σ hσ).2.1, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩,
    equidistributed_of_j hH h2 φK ΛK hΛ 𝔞
      (fun σ hσ => ⟨Λ σ, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩), ?_⟩
  intro E _ _ _ _ _ hE I _ φ hcard hφ hφK s κ 𝔣 hs hκ h𝔣
  exact transportFor_of hA hC d (by omega) δ hδ h2 φK ΛK hΛ Ω₀ hΩ₀ hΩ₀0 t 𝔞 Λ Ω
    (fun σ hσ => ⟨(hT σ hσ).1, (hT σ hσ).2.1⟩) E hE I φ hφ hφK s κ 𝔣 hs h𝔣

end GlobalTheory.TransportProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open Formalism.L2.NTheta in
theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n = R.r) :
    StrictAnti fun a : Fin n => lamAt h a := by
  intro a b hab
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have h3 := lamAt_add_add_le h (b - a) a (by omega)
  rw [show (a : ℕ) + (b - a) = b by omega] at h3
  have h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith


open Formalism.L2.NTheta in
theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := by rw [hpq, hn]; exact odd_r R
  ext x
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact ⟨⟨a, by have := a.2; omega⟩, by simp⟩
    · exact ⟨⟨p + a, by have := a.2; omega⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩
      simp [ha, show p + ((a : ℕ) - p) = a by omega]


open Formalism.L2.NTheta in
theorem isEnum_holPar_kapW {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n)
    {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q (kapW h p q)) lam ε) (a : Fin n) :
    lam a = (lamAt h a : ℝ) ∧ ε a = decide ((a : ℕ) < p) := by
  obtain ⟨hs, f, hf, hS⟩ := he
  rw [holPar_kapW_eq h hn hpq] at hS
  have hg := lamAt_strictAnti h hn
  have hfs : StrictAnti f := fun a b hab => by
    have := hs hab
    rw [hf, hf] at this
    exact_mod_cast this
  have m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a) := fun a => by
    have : (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p)) := fun a => by
    have : (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a) := by
      rw [← hS]; exact Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have e : f = fun a : Fin n => lamAt h a := by
    refine (StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m1 a
      exact ⟨b, congrArg Prod.fst hb⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m2 a
      exact ⟨b, congrArg Prod.fst hb⟩
  subst e
  refine ⟨hf a, ?_⟩
  obtain ⟨b, hb⟩ := m1 a
  obtain rfl : b = a := hg.injective (congrArg Prod.fst hb)
  exact (congrArg Prod.snd hb).symm

theorem holShape_of_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)] at he
    rw [← hs ρ]
    exact isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  refine ⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩
  · rw [nNeg_shape (by omega) fun a => (key ρ a).2]
    omega
  · choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a
    exact ⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.CompHt

theorem finrank_quotPiece_coneIdeal_eq_finrank_map {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) (n : ℕ) :
    Module.finrank K (quotPiece (coneIdeal K y) n) =
      Module.finrank K ((homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap) := by
  have e1 := finrank_quotPiece_add (coneIdeal K y) n
  have e2 := GradedHilbert.finrank_map_add_finrank_inf_ker
    (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)
  have e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _)
      = homogeneousSubmodule (Fin N) K n ⊓
        LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
    ext g
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule,
      LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩
  rw [e3] at e1
  omega

theorem aeval_mem_map_homogeneousSubmodule {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) {j : Fin N} (hj : y j = 1) (g : MvPolynomial (Fin N) K) {n : ℕ}
    (hn : g.totalDegree ≤ n) :
    aeval y g ∈ (homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent g, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := by
    have := Finset.mem_range.1 hi
    omega
  refine ⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩
  have := (homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))
  rw [one_mul, Nat.add_sub_cancel' hi'] at this
  exact this

theorem idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin (K : Type) [Field K] (N : ℕ)
    (y : Fin N → AlgebraicClosure K) (j : Fin N) (hj : y j = 1) :
    GlobalTheory.idealHilbertPoly (coneIdeal K y) =
      Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  have halg : ∀ x ∈ Set.range y, IsAlgebraic K x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  set S : Submodule K (AlgebraicClosure K) :=
    Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS
  have hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x := by
    intro x
    rw [hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hfin : Module.Finite K S := ‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap := by
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (hs ▸ Submodule.subset_span hx)
    filter_upwards [eventually_ge_atTop g.totalDegree] with n hn
    exact aeval_mem_map_homogeneousSubmodule y hj g hn
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev]
    with n h1 h2
  have hW : (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S := by
    apply le_antisymm
    · rintro _ ⟨g, -, rfl⟩
      exact (hmem _).2 ⟨g, rfl⟩
    · rw [← hs, Submodule.span_le]
      exact fun x hx => h2 x hx
  rw [← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]
  rfl

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacesIffGoodPrimesFixedByConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrderCentralizerStable
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_order_centralizer_stable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ), (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c → IsIntV G v 1 → (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) → (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) → (∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y) → ∀ θ θ' h : Qv v ⊗[ℚ] G.C, θ * g = g * θ → θ' * g = g * θ' → h * g = g * h → IsIntV G v θ → IsIntV G v θ' → IsIntV G v h → (θ - (starT G.star (Qv v) θ).unop) * θ' = 1 → 2 * h = 1 → ∀ s : (Qv v ⊗[ℚ] G.C)ˣ, s * g = g * s → IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) → (starT G.star (Qv v) s).unop = s → ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧ (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  first | (exact @GlobalTheory.OrbFinAf.normStep_exists) | (exact GlobalTheory.OrbFinAf.normStep_exists) | (intros; apply GlobalTheory.OrbFinAf.normStep_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_IntV) | (exact GlobalTheory.OrbFinAf.isCompact_IntV) | (intros; apply GlobalTheory.OrbFinAf.isCompact_IntV  <;> assumption)
end

