module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory

theorem exists_ideal_character_of_unitary_hchar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  let S : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset
  have hS : ∀ P, P ∈ S ↔ ¬ χ.UnrAt P := fun P => by simp [S]
  let m : Ideal (𝓞 K) := ∏ P ∈ S, P.asIdeal ^ (n P + 1)
  have hdvd : ∀ P ∈ S, P.asIdeal ^ (n P + 1) ∣ m := fun P hP =>
    Finset.dvd_prod_of_mem (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal ^ (n P + 1)) hP
  have hm : ∀ P : HeightOneSpectrum (𝓞 K), m ≤ P.asIdeal ↔ P ∈ S := by
    intro P
    constructor
    · intro h
      have hprod : ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
          P.asIdeal ∣ ∏ Q ∈ T, Q.asIdeal ^ (n Q + 1) →
          ∃ Q ∈ T, P.asIdeal ∣ Q.asIdeal ^ (n Q + 1) := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          simp only [Finset.prod_empty]
          intro hd
          exact (P.prime.not_dvd_one hd).elim
        | @insert Q T hQT ih =>
          simp only [Finset.prod_insert hQT]
          intro hd
          rcases P.prime.dvd_or_dvd hd with hd | hd
          · exact ⟨Q, Finset.mem_insert_self _ _, hd⟩
          · obtain ⟨R, hR, hd⟩ := ih hd
            exact ⟨R, Finset.mem_insert_of_mem hR, hd⟩
      obtain ⟨Q, hQ, hQP⟩ := hprod S (Ideal.dvd_iff_le.2 h)
      have h1 : Q.asIdeal ≤ P.asIdeal := Ideal.le_of_dvd (P.prime.dvd_of_dvd_pow hQP)
      have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
      exact h2 ▸ hQ
    · intro h
      exact Ideal.le_of_dvd ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (hdvd P h))
  have hm0 : m ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun P _ => pow_ne_zero _ P.ne_bot
  obtain ⟨X, h0, h1, hmul, hnorm, hz, hP⟩ := GlobalTheory.exists_multiplicative_ideal_extension K m
    (fun P => ((χ.val P : ℂˣ) : ℂ)) (fun P _ => hχ _)
  refine ⟨m, X, hm0, h0, h1, hmul, hnorm, hz, ?_, ?_⟩
  · intro P
    split_ifs with h
    · exact hP P fun h' => (hS P).1 ((hm P).1 h') h
    · apply hz
      rw [sup_eq_left.2 ((hm P).2 ((hS P).2 h))]
      exact P.isPrime.ne_top
  · intro β k hk hβ1
    have hβ : β ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    have hne : (Ideal.span {β} : Ideal (𝓞 K)) ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hβ
    have hval : ∀ (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K),
        Valued.v (algebraMap K (P.adicCompletion K) (r : K)) = P.intValuation r := by
      intro P r
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (r : K)
    have hnot : ∀ P ∈ S, β ∉ P.asIdeal := by
      intro P hPS h
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.asIdeal.sub_mem h ((hm P).2 hPS hβ1)
      simpa using this
    have hloc : ∀ P ∈ S, χ.locK P k = 1 := by
      intro P hPS
      have e : ((Formalism.L2.Host.atFin P k : (P.adicCompletion K)ˣ) : P.adicCompletion K)
          = algebraMap K (P.adicCompletion K) (β : K) := by
        rw [← hk]; rfl
      refine hn P _ ?_ ?_
      · unfold Formalism.L2.Host.IsUnitAt
        rw [e, hval]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 (hnot P hPS)
      · have e2 : algebraMap K (P.adicCompletion K) (β : K) - 1
            = algebraMap K (P.adicCompletion K) ((β - 1 : 𝓞 K) : K) := by simp
        rw [e, e2, hval, HeightOneSpectrum.intValuation_le_pow_iff_mem]
        exact Ideal.le_of_dvd ((pow_dvd_pow _ (Nat.le_succ _)).trans (hdvd P hPS)) hβ1
    have hpr := GlobalTheory.HeckeProduct.hchar_productRule K χ S
      (fun v hv => not_not.1 fun h => hv ((hS v).2 h)) k
    rw [Finset.prod_eq_one hloc, mul_one] at hpr
    let φ : Ideal (𝓞 K) →* ℂ :=
      { toFun := X, map_one' := by rw [Ideal.one_eq_top, h1], map_mul' := hmul }
    have hφ : ∀ I, φ I = X I := fun _ => rfl
    have hord : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.L2.Host.ordF v k =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors : ℕ) := by
      intro v
      unfold Formalism.L2.Host.ordF
      rw [hk]
      have : v.valuation K (β : K) = v.intValuation β := HeightOneSpectrum.valuation_of_algebraMap v β
      rw [this, HeightOneSpectrum.intValuation_if_neg _ hβ, WithZero.log_exp, neg_neg]
    have hfs : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        ∏ᶠ (_ : v ∉ S), χ.val v ^ Formalism.L2.Host.ordF v k).Finite := by
      refine (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h => hv ?_
      simp only [h, zpow_zero, finprod_one]
    have key : X (Ideal.span {β}) = ((∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S),
        χ.val v ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) := by
      have e1 := (Units.coeHom ℂ).map_finprod hfs
      rw [Units.coeHom_apply] at e1
      rw [e1, ← hφ, ← Ideal.finprod_heightOneSpectrum_factorization hne,
        φ.map_finprod (Ideal.hasFiniteMulSupport hne)]
      refine finprod_congr fun v => ?_
      rw [HeightOneSpectrum.maxPowDividing, map_pow, hφ, hord, Units.coeHom_apply]
      by_cases hv : v ∈ S
      · have hc : (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors = 0 := by
          by_contra hc
          have := (Associates.count_ne_zero_iff_dvd hne v.irreducible).1 hc
          exact hnot v hv (Ideal.dvd_span_singleton.1 this)
        simp [hc]
      · rw [hP v fun h => hv ((hm v).1 h)]
        simp [hv]
    rw [key, ← Units.val_inv_eq_inv_val, (inv_eq_of_mul_eq_one_right hpr)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNumberFieldValuesInEtaCharHalfTwist
section
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.EtaValsNumberField

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def embSum : R.Psi ⊕ R.Psi → (H.E →+* ℂ) :=
  Sum.elim (embPsi H) fun g => (starRingEnd ℂ).comp (embPsi H g)

theorem embSum_injective : Function.Injective (embSum H) := by
  rintro (i | i) (j | j) hij
  · exact congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H hij)
  · exact absurd hij (GlobalTheory.HalfIntChars.embPsi_ne_conj H i j)
  · exact absurd hij.symm (GlobalTheory.HalfIntChars.embPsi_ne_conj H j i)
  · refine congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H (RingHom.ext fun x => ?_))
    have := congrArg (fun f : H.E →+* ℂ => starRingEnd ℂ (f x)) hij
    simpa [embSum] using this

theorem card_sum : Fintype.card (R.Psi ⊕ R.Psi) = Fintype.card (H.E →+* ℂ) := by
  rw [Fintype.card_sum, NumberField.Embeddings.card, H.finrank_cmField,
    ← Nat.card_eq_fintype_card, Formalism.HC.Frame.natCard_Psi]
  ring

def embEquiv : R.Psi ⊕ R.Psi ≃ (H.E →+* ℂ) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨embSum_injective H, card_sum H⟩)

theorem algType_eta : ∃ m : (H.E →+* ℂ) → ℤ, ∀ k : H.Eˣ,
    (∏ g, (embPsi H g (k : H.E) / ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) *
      ∏ φ : H.E →+* ℂ, ((‖φ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ∏ φ : H.E →+* ℂ, φ (k : H.E) ^ m φ := by
  set bij := embEquiv H
  let g : R.Psi ⊕ R.Psi → ℤ := fun x => Sum.elim (fun _ => 1) (fun _ => 0) x
  refine ⟨fun ψ => g (bij.symm ψ), fun k => ?_⟩
  have hR : ∏ ψ : H.E →+* ℂ, ψ (k : H.E) ^ g (bij.symm ψ) = ∏ x : R.Psi ⊕ R.Psi, (bij x) (k : H.E) ^ g x :=
    (Fintype.prod_equiv bij _ _ fun x => by rw [Equiv.symm_apply_apply]).symm
  have hL : ∏ ψ : H.E →+* ℂ, ((‖ψ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) =
      ∏ x : R.Psi ⊕ R.Psi, ((‖bij x (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) :=
    (Fintype.prod_equiv bij _ _ fun x => rfl).symm
  rw [hR, hL, Fintype.prod_sum_type, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  set z := embPsi H τ (k : H.E) with hzdef
  have hz : z ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hn : (((‖z‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  show (z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ) * ((((‖z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ) *
    (((‖starRingEnd ℂ z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ)) = z ^ (1 : ℤ) * (starRingEnd ℂ z) ^ (0 : ℤ)
  rw [Complex.norm_conj, ← Complex.cpow_add _ _ hn]
  norm_num
  rw [div_mul_cancel₀ _ hn]

theorem etaVals : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  intro R H χ hχ
  obtain ⟨m, hm⟩ := algType_eta H
  obtain ⟨C, hC, hv⟩ := PI.AlgValsFin.W.algValsFin_main H.E χ (1 / 2) m (fun k => by rw [hχ.inf k]; exact hm k)
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simp
  let e : C ≃+ M :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hM : FiniteDimensional ℚ M := LinearEquiv.finiteDimensional
    { e.toAddMonoidHom.toRatLinearMap with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  refine ⟨M, hM, fun v hv' => ?_⟩
  obtain ⟨y, hy⟩ := hv v hv'
  exact ⟨e y, hy⟩

end GlobalTheory.EtaValsNumberField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNorms
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.LineBound

theorem relIndex_span_singleton {K : Type} [Field K] [NumberField K] (𝔪 𝔟 : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = 𝔪 * 𝔟) :
    (Ideal.span {a}).toAddSubgroup.relIndex 𝔟.toAddSubgroup = Ideal.absNorm 𝔪 := by
  have hle : Ideal.span {a} ≤ 𝔟 := by rw [h, mul_comm]; exact Ideal.mul_le_left
  have h1 := AddSubgroup.relIndex_mul_index
    (show (Ideal.span {a}).toAddSubgroup ≤ 𝔟.toAddSubgroup from hle)
  have h2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm 𝔪 * Ideal.absNorm 𝔟 := by
    rw [← map_mul, ← h, Ideal.absNorm_apply]; rfl
  have h3 : 𝔟.toAddSubgroup.index = Ideal.absNorm 𝔟 := by rw [Ideal.absNorm_apply]; rfl
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hb0 : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [h2, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb0) h1

theorem ht_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ ht b X L := by
  unfold ht
  have hc : 0 ≤ Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    unfold Formalism.F.covol
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)) hc

theorem size_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ size b X L :=
  Real.rpow_nonneg (ht_nonneg b X L) _

end GlobalTheory.LineBound

namespace GlobalTheory.LineBound

theorem least_pow_mul_sqrt_absNorm_le_prod : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ →
    ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤
      ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  intro I x 𝔪 h𝔪 w hw hw0
  obtain ⟨hTC, hf, -, hbij, hX0⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  haveI := hTC
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hX0 v).1
  obtain ⟨a, ha𝔪, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  obtain ⟨𝔟, h𝔟⟩ := (Ideal.dvd_span_singleton).2 ha𝔪
  have haE : (a : I.E) ≠ 0 := by exact_mod_cast ha0
  set u : Fin I.n → I.E := (a : I.E)⁻¹ • w with hu
  set ℓ : 𝓞 I.E →ₗ[𝓞 I.E] (Fin I.n → I.E) := LinearMap.toSpanSingleton (𝓞 I.E) _ u with hℓ
  have hℓapp : ∀ c : 𝓞 I.E, ℓ c = (c : I.E) • u := fun c => by
    rw [hℓ, LinearMap.toSpanSingleton_apply]
    exact (algebraMap_smul I.E c u).symm
  have hℓa : ℓ a = w := by rw [hℓapp, hu, smul_smul, mul_inv_cancel₀ haE, one_smul]
  have hu0 : u ≠ 0 := by
    rw [hu]; exact smul_ne_zero (inv_ne_zero haE) hw0
  have hinj : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hℓapp] at hc
    have : (c : I.E) = 0 := (smul_eq_zero.1 hc).resolve_right hu0
    exact_mod_cast this
  set R : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.map ℓ 𝔟 with hR
  have hab : a ∈ 𝔟 := by
    have : Ideal.span {a} ≤ 𝔟 := by rw [h𝔟, mul_comm]; exact Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self a)
  have hwR : w ∈ R := ⟨a, hab, hℓa⟩

  have hRle : R ≤ lamX I x := by
    have key : ∀ y ∈ 𝔪 • lamX I x, ∀ c ∈ 𝔟, ((c : I.E) * (a : I.E)⁻¹) • y ∈ lamX I x := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro m hm l hl c hc
        have hmc : m * c ∈ Ideal.span {a} := by rw [h𝔟]; exact Ideal.mul_mem_mul hm hc
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hmc
        have hdE : (d : I.E) = (c : I.E) * (a : I.E)⁻¹ * (m : I.E) := by
          have : (d : I.E) * (a : I.E) = (m : I.E) * (c : I.E) := by exact_mod_cast hd
          field_simp
          linear_combination this
        have : ((c : I.E) * (a : I.E)⁻¹) • (m • l) = d • l := by
          rw [← algebraMap_smul I.E m l, smul_smul, ← algebraMap_smul I.E d l]
          congr 1
          exact hdE.symm
        rw [this]
        exact (lamX I x).smul_mem d hl
      · intro y z hy hz c hc
        rw [smul_add]
        exact add_mem (hy c hc) (hz c hc)
    rintro y ⟨c, hc, rfl⟩
    rw [hℓapp, hu, smul_smul]
    exact key w hw c hc
  have hRfg : R.FG := (IsNoetherian.noetherian 𝔟).map ℓ
  have hR0 : R ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot _).1 (h ▸ hwR))
  have hrange : Set.range (fun _ : Fin 1 => w) = {w} := Set.range_const
  have hli : LinearIndependent I.E (fun _ : Fin 1 => w) := LinearIndependent.of_subsingleton 0 hw0
  have hspanw : Submodule.span (𝓞 I.E) {w} = Submodule.map ℓ (Ideal.span {a}) := by
    rw [Ideal.span, Submodule.map_span, Set.image_singleton, hℓa]
  have hwle : Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w) ≤ R := by
    rw [hrange, Submodule.span_le, Set.singleton_subset_iff]; exact hwR
  have hrk : rkK R = 1 := by
    unfold rkK
    have : Submodule.span I.E (R : Set (Fin I.n → I.E)) = Submodule.span I.E {w} := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro y ⟨c, -, rfl⟩
        rw [hℓapp, hu, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span hwR
    rw [this, finrank_span_singleton hw0]
  have hidx : (Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w)).toAddSubgroup.relIndex
      R.toAddSubgroup = Ideal.absNorm 𝔪 := by
    rw [hrange, hspanw, hR, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact relIndex_span_singleton 𝔪 𝔟 a ha0 h𝔟
  obtain ⟨hG1, hG2⟩ := htGram I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hX 1 (fun _ => w) hli
  have hht := hG2 R hRfg hwle (by rw [hrk])
  rw [hidx, hG1] at hht

  set g : InfinitePlace I.F → ℝ := fun v =>
    ∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2 with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Finset.sum_nonneg fun i _ => by positivity
  have hdet : ∀ w' : InfinitePlace I.E,
      (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re = g (w'.comap (algebraMap I.F I.E)) := by
    intro w'
    rw [GlobalTheory.FlagMeas.SizeMove.norm_det_gram, Matrix.det_fin_one, Matrix.of_apply]
    have hU : uMat (x.1 (w'.comap (algebraMap I.F I.E)))⁻¹ = (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ := by
      simp [uMat]
    rw [hg]
    simp only [hU, GlobalTheory.FlagMeas.SizeMove.crd]
    set z := (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
      ((I.P (w'.comap (algebraMap I.F I.E)))⁻¹ *ᵥ fun l => I.φ (w'.comap (algebraMap I.F I.E)) (w l))
    have : star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have hprod : ∏ w' : InfinitePlace I.E, (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re =
      ∏ v, g v := by
    simp only [hdet]
    exact Fintype.prod_bijective _ hbij _ _ (fun _ => rfl)
  rw [hprod] at hht

  have hbdd : BddBelow {t | ∃ S : Submodule (𝓞 I.E) (Fin I.n → I.E), S ≤ lamX I x ∧ S ≠ ⊥ ∧
      size (bas I) (frm I x) S = t} := ⟨0, by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _⟩
  have hle : least I x ≤ size (bas I) (frm I x) R := csInf_le hbdd ⟨R, hRle, hR0, rfl⟩
  have h0 : 0 ≤ least I x := le_csInf ⟨_, ⟨R, hRle, hR0, rfl⟩⟩ (by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _)
  have hfpos : 0 < nPl I.E := Fintype.card_pos
  have hsz : size (bas I) (frm I x) R ^ (2 * I.f) = ht (bas I) (frm I x) R := by
    unfold size
    rw [hrk, ← Real.rpow_natCast, ← Real.rpow_mul (ht_nonneg _ _ _), ← hf]
    have : (1 : ℝ) / (2 * (nPl I.E : ℝ) * ((1 : ℕ) : ℝ)) * ((2 * nPl I.E : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hN0 : (0 : ℝ) ≤ Ideal.absNorm 𝔪 := Nat.cast_nonneg _
  have hsq : (least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪)) ^ 2 ≤
      (∏ v, Real.sqrt (g v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0, ← Finset.prod_pow]
    simp only [fun v => Real.sq_sqrt (hg0 v)]
    rw [← hht, ← pow_mul, mul_comm I.f 2, ← hsz]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle _) hN0
  exact (pow_le_pow_iff_left₀ (by positivity) (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)
    two_ne_zero).1 hsq

end GlobalTheory.LineBound
end
end

