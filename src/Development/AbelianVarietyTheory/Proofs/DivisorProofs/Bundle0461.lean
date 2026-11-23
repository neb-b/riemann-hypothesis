module

public import Mathlib
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorTimesSplitPrimesExponents
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.CondExp

theorem dvd_prod_primes_iff {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ q ∈ Q, q.asIdeal ↔ v ∈ Q := by
  constructor
  · intro h
    have hex : ∃ q ∈ Q, v.asIdeal ∣ q.asIdeal :=
      (v.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum R => q.asIdeal)).1 h
    obtain ⟨q, hq, hd⟩ := hex
    have : q.asIdeal = v.asIdeal :=
      q.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)
    rwa [← HeightOneSpectrum.ext this]
  · intro h
    exact Finset.dvd_prod_of_mem _ h

theorem prod_primes_ne_zero {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) : ∏ q ∈ Q, q.asIdeal ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot

theorem multiplicity_prod_primes_of_mem {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) (hv : v ∈ Q) :
    multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) = 1 := by
  classical
  have h0 := prod_primes_ne_zero Q
  rw [← Finset.mul_prod_erase Q _ hv] at h0 ⊢
  rw [multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0),
    multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.ne_bot),
    multiplicity_eq_zero_of_not_dvd (by rw [dvd_prod_primes_iff]; simp)]

theorem condQ_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  intro E _ _ 𝔣 Q hb ha
  have h0 : condQ 𝔣 Q ≠ 0 := mul_ne_zero hb.1 (prod_primes_ne_zero Q)
  have hm : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v =
      expIn 𝔣 v + multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) := fun v =>
    multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0)
  have hd : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q := by
    intro v hv
    by_contra h
    exact hv (multiplicity_eq_zero_of_not_dvd h)
  refine ⟨h0, ?_, hd, ?_, ?_, (Ideal.finite_factors h0).subset hd⟩
  · intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact (hb.2.2 v h).1
    · exact (ha v ((dvd_prod_primes_iff Q v).1 h)).1
  · intro v hv
    have h1 : expIn 𝔣 v = 0 := multiplicity_eq_zero_of_not_dvd (ha v hv).2
    rw [hm, h1, multiplicity_prod_primes_of_mem Q v hv]
  · intro v hv
    rw [hm, multiplicity_eq_zero_of_not_dvd (fun h => hv ((dvd_prod_primes_iff Q v).1 h)), add_zero]

end GlobalTheory.CMVal.CondExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateIntoAdjoinedAlgebra
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_into_adjoined_algebra : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (exact GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (intros; apply GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountWordWithLetterMultiplicities
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem count_word_eq (I : Type) [Fintype I] [DecidableEq I] (κ : I → ℕ) (i : I) :
    (word κ).count i = κ i := by
  unfold word
  rw [List.count_flatMap]
  simp [List.count_replicate, Function.comp_def]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRuleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossProductTwisted_leibniz_rule : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ} (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k') (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m), δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  first | (exact @GlobalTheory.PBFc.crossT_leibniz) | (exact GlobalTheory.PBFc.crossT_leibniz) | (intros; apply GlobalTheory.PBFc.crossT_leibniz  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), (∀ s, Injective (I.X s)) → (∀ s, Injective (J.X s)) → ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) I n a = 0 → cpull ((chains R).map g) J m b = 0 → μ.cup E hk a b = 0 := by
  first | (exact @GlobalTheory.EtC.cup_supp) | (exact GlobalTheory.EtC.cup_supp) | (intros; apply GlobalTheory.EtC.cup_supp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransport
section
noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def omegaDualCongr {G H : PDivGroup p O} (f : G ≅ H) : G.dual.omega ≃ₗ[O] H.dual.omega :=
  LinearEquiv.ofLinearMap (omegaDualMap G H f.hom) (omegaDualMap H G f.inv)
    (by rw [← omegaDualMap_comp, f.inv_hom_id, omegaDualMap_id])
    (by rw [← omegaDualMap_comp, f.hom_inv_id, omegaDualMap_id])

def lieCongr {G H : PDivGroup p O} (f : G ≅ H) : G.Lie ≃ₗ[O] H.Lie :=
  LinearEquiv.ofLinearMap (lieMap G H f.hom) (lieMap H G f.inv)
    (by rw [← lieMap_comp, f.inv_hom_id, lieMap_id])
    (by rw [← lieMap_comp, f.hom_inv_id, lieMap_id])

theorem datum_transport [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {h : ℕ}
    {G H : PDivGroup p O} (f : G ≅ H) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie)
    (h1 : ∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O))
    (h2 : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)) :
    ∃ (e' : H.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
      (fil' : H.dual.omega ≃ₗ[O] D.Fil) (lie' : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] H.Lie),
      (∀ t, D.al (toO e' t) = (fil' (hodgeTate H t) : Fin h → O)) ∧
        ∀ (x : H.Lie) (χ : H.dual.Tate), pairingO hε e' (bQuot D (lie'.symm x)) χ = x (dlog H χ) := by
  refine ⟨(tateCongr O f).symm ≪≫ₗ e, (omegaDualCongr f).symm ≪≫ₗ fil, lie ≪≫ₗ lieCongr f,
    fun s => ?_, fun x χ => ?_⟩
  · have := h1 (tateMap H G O f.inv s)
    change D.al (toO e (tateMap H G O f.inv s)) =
      (fil (omegaDualMap H G f.inv (hodgeTate H s)) : Fin h → O)
    rw [this, ← hodgeTate_tateMap]
  · set χ' := tateMap _ _ O (dualHom G H f.hom) χ
    have hp : ∀ y, pairingO hε ((tateCongr O f).symm ≪≫ₗ e) y χ = pairingO hε e y χ' := by
      intro y
      simp only [pairingO, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      simp only [epsPairing, tateCongr_apply, pairing_tateMap, χ']
    have hl : (lie ≪≫ₗ lieCongr f).symm x = lie.symm (lieMap H G f.inv x) := rfl
    rw [hp, hl, h2, lieMap_apply, dlog_tateMap, ← LinearMap.comp_apply (omegaMap H G f.inv),
      ← omegaMap_comp, f.inv_hom_id, omegaMap_id, LinearMap.id_apply]

theorem hasDatum_of_iso : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G H : PDivGroup p O,
      Nonempty (G ≅ H) → HasDatum hε G → HasDatum hε H := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H ⟨f⟩ hG
  haveI : IsIntegrallyClosedIn O C :=
    isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun hx => hv.exists_of_le_one
      (hv.isIntegral_iff_v_le_one.1 hx)⟩
  have hh : G.height = H.height := by
    rw [← PDivGroup.finrank_tate G C, ← PDivGroup.finrank_tate H C]
    exact (tateCongr O f).finrank_eq
  obtain ⟨D, e, fil, lie, h1, h2⟩ := hG
  unfold HasDatum
  rw [← hh]
  obtain ⟨e', fil', lie', h1', h2'⟩ := datum_transport hε f D e fil lie h1 h2
  exact ⟨D, e', fil', lie', h1', h2'⟩

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum.Bound

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defCoord_lower (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) {r : ℝ} (hz : ‖z i‖ ≤ r) :
    (1 - r) * ‖φ i x‖ ≤ ‖defCoord φ z x i‖ := by
  have h1 : ‖z i * starRingEnd ℂ (φ i x)‖ = ‖z i‖ * ‖φ i x‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 := norm_sub_norm_le (φ i x) (-(z i * starRingEnd ℂ (φ i x)))
  rw [norm_neg, h1, sub_neg_eq_add] at h2
  unfold defCoord
  nlinarith [norm_nonneg (φ i x)]

theorem factor_le (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) (hx : x ≠ 0) (i : I) {r : ℝ} (hr : r < 1)
    (hz : ‖z i‖ ≤ r) :
    ‖((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
        (defCoord φ z x i)⁻¹ ^ (k + m i)‖ ≤
      ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (k + m i) * (‖φ i x‖⁻¹) ^ k := by
  have hp : 0 < ‖φ i x‖ := by simpa using hx
  have hr' : 0 < 1 - r := by linarith
  have hl := defCoord_lower φ z x i hz
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  have hinv : ‖defCoord φ z x i‖⁻¹ ≤ (1 - r)⁻¹ * ‖φ i x‖⁻¹ := by
    rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv]
  rw [mul_assoc, mul_assoc]
  gcongr ‖_‖ * ?_
  calc ‖φ i x‖ ^ m i * ‖defCoord φ z x i‖⁻¹ ^ (k + m i)
      ≤ ‖φ i x‖ ^ m i * ((1 - r)⁻¹ * ‖φ i x‖⁻¹) ^ (k + m i) := by gcongr
    _ = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k := by
      rw [mul_pow, pow_add ‖φ i x‖⁻¹]
      have : ‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]
      calc ‖φ i x‖ ^ m i * ((1 - r)⁻¹ ^ (k + m i) * (‖φ i x‖⁻¹ ^ k * ‖φ i x‖⁻¹ ^ m i))
          = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k * (‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i) := by ring
        _ = _ := by rw [this, mul_one]

theorem dTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 →
      ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  intro E _ _ _ I _ φ hφ s m r hr
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (((2 * s : ℕ) : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (2 * s + m i)),
    fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) = ∏ i, (‖φ i x‖⁻¹) ^ (2 * s) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.rpow_neg (Finset.prod_nonneg fun i _ => by positivity), Real.rpow_natCast,
      ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, inv_pow, inv_pow]
  rw [hN, ← Finset.prod_mul_distrib, dTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  exact factor_le φ (2 * s) m z x hx i hr (hz i)

end GlobalTheory.DeformedSum.Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeZeroSectionClass_properties : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  first | exact @GlobalTheory.EtC.secClass_props | exact GlobalTheory.EtC.secClass_props | (intros; apply GlobalTheory.EtC.secClass_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivFormulaOfSeries
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DerivAtOrigin

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := by
  intro i; simp

theorem count_cons_eq {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [List.count_cons]
  · simp [List.count_cons, Pi.single_apply, h, Ne.symm h]

theorem risingFactor_ne_zero {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by
  unfold risingFactor
  rw [Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have : ((k : ℂ) + j) = ((k + j : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by omega : k + j ≠ 0)

theorem term_origin {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by
  unfold term
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem derivFormula_of_series : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (L : Set E), 4 ≤ k → (∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits L => dTerm φ k m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) (∑' q : modUnits L, dTerm φ k (m + Pi.single i 1) z q.1.out) z (Pi.single i 1)) → DerivFormula φ k L := by
  intro E _ _ I _ _ φ k L hk H
  set T : (I → ℕ) → (I → ℂ) → ℂ := fun m w => ∑' q : modUnits L, dTerm φ k m w q.1.out with hT
  have hT0 : ∀ z ∈ polydisc I, HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) (T 0 z) := by
    intro z hz
    have e : (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) = fun q : modUnits L => dTerm φ k 0 z q.1.out :=
      funext fun q => (dTerm_zero φ k z q.1.out).symm
    rw [e]
    exact (H 0 z hz).1.hasSum

  have hagree : ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, g z = (cWt E k : ℂ) * T 0 z := by
    intro g hg z hz
    obtain ⟨G, hG, hgz⟩ := hg z hz
    rw [hgz, (hG.1 (by omega)).unique (hT0 z hz)]

  have hiter : ∀ g, IsDefSum φ k L g → ∀ l : List I, ∀ z ∈ polydisc I,
      iterD l g z = (cWt E k : ℂ) * T (fun j => l.count j) z := by
    intro g hg l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      exact hagree g hg z hz
    | cons i l ih =>
      intro z hz
      have hev : iterD l g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T (fun j => l.count j) w := by
        filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using ih w hw
      have hd : HasLineDerivAt ℂ (fun w => (cWt E k : ℂ) * T (fun j => l.count j) w)
          ((cWt E k : ℂ) * T ((fun j => l.count j) + Pi.single i 1) z) z (Pi.single i 1) := by
        have h1 := (H (fun j => l.count j) z hz).2.2 i
        unfold HasLineDerivAt at h1 ⊢
        exact h1.const_mul _
      have h2 : iterD (i :: l) g z = lineDeriv ℂ (iterD l g) z (Pi.single i 1) := rfl
      rw [h2, hev.lineDeriv_eq, hd.lineDeriv, count_cons_eq]
  refine ⟨⟨fun z => (cWt E k : ℂ) * T 0 z, fun z hz => ⟨T 0 z, ⟨fun _ => hT0 z hz, fun h => by omega⟩, rfl⟩⟩, ?_⟩
  intro g hg
  refine ⟨?_, ?_⟩
  · intro z hz
    have hev : g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T 0 w := by
      filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using hagree g hg w hw
    have hda : DifferentiableAt ℂ (fun w => (cWt E k : ℂ) * T 0 w) z :=
      ((H 0 z hz).2.1).const_mul _
    exact (hda.congr_of_eventuallyEq hev).differentiableWithinAt
  · intro κ l hl
    have hκ : (fun j => l.count j) = κ := funext hl
    have h0 : iterD l g 0 = (cWt E k : ℂ) * T κ 0 := by
      rw [hiter g hg l 0 (zero_mem_polydisc I), hκ]
    have hTκ : T κ 0 = risingFactor k κ *
        ∑' q : modUnits L, ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i) := by
      simp only [hT, dTerm_origin]
      exact tsum_mul_left
    refine ⟨?_, ?_⟩
    · intro S hS
      have hS0 := hS.2 0 (by
        have : (4 : ℝ) ≤ k := by exact_mod_cast hk
        simp; linarith)
      simp only [term_origin] at hS0
      rw [h0, hTκ, hS0.tsum_eq]; ring
    · intro _
      have hsum : Summable (fun q : modUnits L =>
          ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) := by
        have h := (H κ 0 (zero_mem_polydisc I)).1
        simp only [dTerm_origin] at h
        exact (summable_mul_left_iff (risingFactor_ne_zero k (by omega) κ)).1 h
      refine ⟨_, hsum.hasSum, ?_⟩
      rw [h0, hTκ]; ring

end GlobalTheory.DerivAtOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscr
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.GalDiff

open scoped Pointwise

variable (E : Type) [Field E] [NumberField E]

theorem mem_differentIdeal_iff_one (x : 𝓞 E) :
    x ∈ differentIdeal ℤ (𝓞 E) ↔
      ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E), (x : E) * y ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E),
    IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, h⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 E) E h
    exact this ▸ hy

theorem galois_smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  have hone : ∀ (τ : E ≃ₐ[ℚ] E) (a : E), a ∈ (1 : Submodule (𝓞 E) E) →
      τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro τ a ha
    rw [Submodule.mem_one] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨τ • b, rfl⟩
  rw [mem_differentIdeal_iff_one] at hx ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have := hy (σ a) (hone σ a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]
    exact this
  have := hone σ _ (hx _ hy')
  rw [map_mul, AlgEquiv.apply_symm_apply] at this
  exact this

theorem differentIdeal_pow_finrank_eq_span_discr :
    ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F],
      differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  intro E _ _ _
  classical
  have hmap : Ideal.span {((discr E : ℤ) : 𝓞 E)} = (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [hmap]
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hN : Ideal.absNorm D = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hrel : Ideal.relNorm ℤ D = Ideal.span {discr E} := by
    rw [Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  have hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E := by
    rw [← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E
    rw [h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.prod_const]
    exact Ideal.prod_mem_prod fun σ _ => galois_smul_mem_differentIdeal E σ hx
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have h2 := congrArg Ideal.absNorm hL
  rw [Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank,
    Ideal.absNorm_span_singleton, Algebra.norm_self] at h2
  have h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))
  have h3 : Ideal.absNorm L = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    exact h2.symm
  rw [hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]

end GlobalTheory.GalDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyBaseChangeCoprodBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  first | (exact @GlobalTheory.EtC.BcCoprod.main) | (exact GlobalTheory.EtC.BcCoprod.main) | (intros; apply GlobalTheory.EtC.BcCoprod.main  <;> assumption)
end

