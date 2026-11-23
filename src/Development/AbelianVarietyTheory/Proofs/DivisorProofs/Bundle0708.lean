module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)


section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)


variable {O}

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)


end GlobalTheory.ThetaInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_enlarge_good_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_good) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_good) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_good  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicLogLe
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLoss

theorem sum_padic_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.padicValNat_def]
  · have hd : ∏ p ∈ P, p ^ padicValNat p n ∣ n := by
      refine Finset.prod_dvd_of_isRelPrime ?_ fun p _ => (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
      intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.1
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq))
    have h1 : ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) =
        Real.log (∏ p ∈ P, (p : ℝ) ^ padicValNat p n) := by
      rw [Real.log_prod]
      · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]
      · intro p hp
        have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        positivity
    rw [h1]
    apply Real.log_le_log
    · refine Finset.prod_pos fun p hp => ?_
      have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      positivity
    · exact_mod_cast Nat.le_of_dvd hn hd

theorem sum_primes_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (X a A W : ℝ) (hX : 0 ≤ X) (hXa : X ≤ a)
    (ha : 1 ≤ a) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    ∑ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log n + X * (A * Real.log a) + 2 * (W * Real.log a) := by
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : ∀ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log p * (padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.log a + 2 * (W * Real.log a) * ((p : ℝ) ^ 2)⁻¹ else 0) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hl : 0 < Real.log p := Real.log_pos (by linarith)
    have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    split_ifs with h
    · have hb : 0 ≤ Real.logb p a := Real.logb_nonneg (by linarith) ha
      rw [abs_of_nonneg (by positivity), mul_add, mul_add]
      have e1 : Real.log p * (A * Real.logb p a) = A * Real.log a := by
        unfold Real.logb; field_simp
      have e2 : Real.log p ≤ Real.log a := Real.log_le_log (by linarith) (h.trans hXa)
      have e3 : W / ((p : ℝ) ^ 2 - 1) ≤ 2 * W * ((p : ℝ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hq (by positivity)]
        have : 0 ≤ (p : ℝ) ^ 2 - 2 := by nlinarith
        nlinarith [mul_nonneg hW this]
      have e4 := mul_le_mul e2 e3 (by positivity) hla
      rw [e1]
      nlinarith
    · rw [add_zero, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, add_assoc]
  refine add_le_add (sum_padic_log_le P hP n) ?_
  have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ X) ⊆ Finset.Ioo 1 (⌊X⌋₊ + 1) := by
    intro p hp
    obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_Ioo.2 ⟨(hP p a1).one_lt, Nat.lt_succ_of_le (Nat.le_floor a2)⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  have c1 : ((Finset.Ioo 1 (⌊X⌋₊ + 1)).card : ℝ) ≤ X := by
    refine le_trans ?_ (Nat.floor_le hX)
    rw [Nat.card_Ioo]
    exact_mod_cast (by omega : ⌊X⌋₊ + 1 - 1 - 1 ≤ ⌊X⌋₊)
  have c2 : ∑ p ∈ Finset.Ioo 1 (⌊X⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 1 (⌊X⌋₊ + 1)
    norm_num at this ⊢
    exact this
  exact add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity))
    (mul_le_of_le_one_right (by positivity) c2)

end GlobalTheory.ConjLoss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_shear : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {g : ℕ} (h : (I → ℂ) × (Fin g → ℂ) → ℂ) (τ : (I → ℂ) → Fin g → ℂ) (w : Fin g → ℂ), AnalyticAt ℂ τ 0 → AnalyticAt ℂ h (0, w + τ 0) → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (z, w + τ z)) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun a ↦ GlobalTheory.PeriodFamily.taylor N t (fun z ↦ τ z a) - algebraMap ℂ D (τ 0 a)) (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) := by
  intro I _ _ D _ _ N t ht g h τ w hτ hh
  have hτa : ∀ a, AnalyticAt ℂ (fun z ↦ τ z a) 0 := fun a ↦ analyticAt_pi_iff.1 hτ a
  have hco : ∀ {J : Type} [Fintype J] (j : J) (x : J → ℂ), AnalyticAt ℂ (fun z : J → ℂ ↦ z j) x :=
    fun j x ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).analyticAt x
  have hΦ : AnalyticAt ℂ (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 := by
    refine analyticAt_pi_iff.2 ?_
    rintro (i | a)
    · exact hco i 0
    · exact (hτa a).sub analyticAt_const
  have hΦ0 : (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 = 0 := by
    funext k
    rcases k with i | a <;> simp
  have hH : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) 0 := by
    have hin : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
        ((fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)) : (I → ℂ) × (Fin g → ℂ))) 0 := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ hco _ 0) ?_
      refine analyticAt_pi_iff.2 fun a ↦ ?_
      exact (analyticAt_const (v := (w + τ 0) a)).add (hco (Sum.inr a) 0)
    refine AnalyticAt.comp_of_eq hh hin ?_
    ext <;> simp
  have key := _root_.GlobalTheory.PeriodFamily.taylor_comp_chain N t ht _ _ hΦ hΦ0 hH
  obtain ⟨hadd, -, hconst, -⟩ := _root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t
  have e1 : (fun z : I → ℂ ↦ h (z, w + τ z)) = fun z : I → ℂ ↦
      (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)))
        (Sum.elim z (fun a ↦ τ z a - τ 0 a)) := by
    funext z
    congr 1
    ext <;> simp
  rw [e1, key]
  congr 1
  funext k
  rcases k with i | a
  · exact (_root_.GlobalTheory.PeriodFamily.taylor_coord_and_eval N t ht).1 i
  · have := hadd (fun z ↦ τ z a) (fun _ ↦ - τ 0 a) (hτa a) analyticAt_const
    rw [hconst, map_neg] at this
    simpa [sub_eq_add_neg] using this

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIntegerRingAlmostAllPlaces
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.OneCoh

theorem dies_on_etale_with_point (q : ℕ) [NeZero q] (B : Type) [CommRing B] (hq : IsUnit (q : B))
    (P : Ideal B) [P.IsMaximal] (hsep : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (m i : ℤ) (hm : 0 < m) (y : Ht q (sp B) m i) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D),
      Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧
      pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  obtain ⟨O, _, _, hSH, hInd, hO⟩ := GlobalTheory.T.exists_strictHenselization_at_maximal B P hsep
  have hsub : Subsingleton (Ht q (sp O) m i) := GlobalTheory.EtC.b2 (ZMod q) O hSH (tw q i) m hm
  have h0 : pull _ (spMap (algebraMap B O)) _ _ y = 0 := Subsingleton.elim _ _
  obtain ⟨D, _, _, _, φ, hD⟩ := GlobalTheory.T.vanishes_on_etale_neighbourhood q B O hq hInd m i y h0
  obtain ⟨hH, -⟩ := hSH
  haveI : IsLocalRing O := hH.toIsLocalRing
  obtain ⟨hP, hres⟩ := hO (IsLocalRing.maximalIdeal O) inferInstance
  refine ⟨D, inferInstance, inferInstance, inferInstance, (IsLocalRing.maximalIdeal O).comap φ, ?_, ?_, ?_, hD⟩
  · exact Ideal.comap_isPrime _ _
  · rw [← hP]
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  · intro d
    obtain ⟨b, hb⟩ := hres (φ d)
    refine ⟨b, ?_⟩
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes]
    exact hb

end GlobalTheory.EtC.OneCoh

theorem GlobalTheory.EtC.oneCoh_main : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 :=
  fun q _ B _ hq P _ hsep m i hm y => GlobalTheory.EtC.OneCoh.dies_on_etale_with_point q B hq P hsep m i hm y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateEtalePartManifold
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.twisted_estimate_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → 300 ≤ T → IsCut T θ → (∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω) → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∃ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F ∧ ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu ≤ 30 * ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ _ ι La _ A E L s hs hsq δ hδ hlev Λ τ z β hdat Ω h T θ hhd hT hθ hΩcov hfin
  obtain ⟨hτ, hpos, hz, hβ, _hdense, C, hC0, hC⟩ := hdat
  obtain ⟨hΩ, hh, hh0⟩ := hhd
  obtain ⟨X, hXz, hXe⟩ := _root_.GlobalTheory.nzEtaleStein n Y ι La A Λ τ z hτ hpos hz
  have hU : IsOpen (nz A τ) := hz.isOpen
  have hpt := GlobalTheory.OTY.TwEst.nz_facts A L Λ s τ C hC0 hsq hC
  obtain ⟨hsmφ, hsmψ, hlevi⟩ := _root_.GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg n Y ι La A E L s hs δ hlev (nz A τ) z β hz hβ
    (fun y hy => (hpt y hy).1)
  obtain ⟨hqd, hqm, hq⟩ := _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable n Y ι La A (A.kap + E) (nz A τ) Ω β h hU hΩ hβ hh hh0
  have hψm : Measurable (psi A L s) :=
    (_root_.GlobalTheory.OTY.measurable_nsq_extend_and_psi n Y ι La A (A.kap + E) Ω h hΩ hh hh0).2 L s hs
  have htr := _root_.GlobalTheory.OTY.TwEst.lintegral_frame_transfer n Y ι La A E (nz A τ) z β hz hβ
  have hGholo : ∀ e : OpenPartialHomeomorph (nz A τ) (V n), IsChart n X.z e →
      DifferentiableOn ℂ ((fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) := by
    rw [hXz]
    exact (_root_.GlobalTheory.OTY.holo_etale_iff_holo_chart n Y ι La A (nz A τ) z hz Ω (GlobalTheory.OTY.TwEst.quot A h β) hΩ).2 hqd
  have hGm : Measurable (fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) := by
    have h1 := hqm.comp (measurable_subtype_coe : Measurable (Subtype.val : nz A τ → Y))
    convert h1 using 1
    ext y
    exact (GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe (nz A τ)
      (fun x => GlobalTheory.OTY.TwEst.quot A h β x) y).symm
  have hθc : Continuous θ := hθ.1.continuous
  have hθb : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1 := hθ.2.2.2.1
  have hwint := _root_.GlobalTheory.OTY.TwEst.cutoff_quot_wint_le n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ θ hθc hθb
  obtain ⟨F0, hF0, hest⟩ := _root_.GlobalTheory.LogGrowth.twisted_extension_logGrowth n (nz A τ) X
    (fun y => GlobalTheory.OTY.TwEst.wt A E β z y) (fun y => psi A L s y)
    (fun y => GlobalTheory.OTY.TwEst.quot A h β y) (Subtype.val ⁻¹' Ω) δ T θ
    (by rw [hXz]; exact hsmφ) (by rw [hXz]; exact hsmψ) (fun x => (hpt x x.2).2.1) hδ hT hθ
    (by rw [hXz]; exact hlevi) (hΩ.preimage continuous_subtype_val) hGm hGholo
    (fun x hx => hΩcov x (hpt x x.2).1 hx)
    ⟨n, n * Real.log C, fun x => by rw [hXe]; exact (hpt x x.2).2.2⟩
    (by rw [hXz]; exact lt_of_le_of_lt hwint hfin)
  rw [hXz] at hF0 hest
  obtain ⟨hFsec, hFm⟩ := _root_.GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable n Y ι La A (A.kap + E) (nz A τ) z β F0 hz hβ hF0
  refine ⟨fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 (nz A τ) F0 y, hFsec, ?_⟩
  exact (_root_.GlobalTheory.OTY.TwEst.lhs_transfer n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T θ F0 hθc hFm).trans_le
    (hest.trans (mul_le_mul_of_nonneg_left
      (_root_.GlobalTheory.OTY.TwEst.rhs_le_manifold n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T) (by norm_num)))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonal
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_apply_sum (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    yF X w τ a b = ∑ k, nmat X w τ a k * gsB X w τ k b := by
  simp [yF, yM, Matrix.mul_apply, mat]

theorem gsB_differentiableAt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w => gsB X w τ a b) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hs : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) (fun w hw => hball w hw)
  exact ((_root_.GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn X hx τ a b).contDiffAt hs).differentiableAt (by simp)

theorem nmat_differentiableAt (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ a b) 0 :=
  ((PoinPf.diff_nmat X τ a b).restrictScalars ℝ) 0

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    nmat X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  have h := congrFun (congrFun (PoinPf.nmat_zero X τ) a) b
  simpa [mat] using h

theorem gsB_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    gsB X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  rw [gsB_zero]

theorem dY_lower (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ)
    (a b : Fin r) (hba : b < a) : dY X z τ a b = nmat X z τ a b := by
  have hS := (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx).hasFDerivAt
  have h1 := hasFDerivAt_pi'.1 hS τ
  have h2 := hasFDerivAt_pi'.1 h1 a
  have h3 := hasFDerivAt_pi'.1 h2 b
  have hT : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) 0 :=
    HasFDerivAt.fun_sum (fun k _ =>
      (nmat_differentiableAt X τ a k).hasFDerivAt.mul (gsB_differentiableAt X hx τ k b).hasFDerivAt)
  have h3' : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      ((ContinuousLinearMap.proj b).comp ((ContinuousLinearMap.proj a).comp
        ((ContinuousLinearMap.proj τ).comp (dY X)))) 0 := by
    have : (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b) = fun w => yF X w τ a b := by
      funext w; rw [yF_apply_sum]
    rw [this]; exact h3
  have hU := congrArg (fun L => L z) (h3'.unique hT)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hU
  rw [hU]
  have hB0 : (fun w : V (nd X) => gsB X w τ a b) = fun _ => 0 := by
    funext w; exact gsB_lower X w τ hba
  set e := (Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), hba⟩⟩
  have hN : (fun w : V (nd X) => nmat X w τ a b) =
      ⇑((EuclideanSpace.proj e : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext w; simp [nmat, hba, e]; rfl
  have hsum : (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) =
      fderiv ℝ (fun w => gsB X w τ a b) 0 + fderiv ℝ (fun w => nmat X w τ a b) 0 := by
    simp only [nmat_zero_apply, gsB_zero_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, ContinuousLinearMap.add_apply]
  rw [hB0, hN, fderiv_const_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.zero_apply, zero_add]
  simp [nmat, hba, e] <;> rfl

end GlobalTheory.SUChartSection
end

