module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClass
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

theorem pull_lam_av {A : AbVar K} (c : Pic A.X.left) {Y Z : Over (Sp K)} (u : Z ⟶ Y) (x y : Y ⟶ A.X) :
    CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) := by
  simp only [AbVar.lam, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem pull_one_eq_zero {A : AbVar K} (c : Pic A.X.left) (Y : Over (Sp K)) :
    CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
  exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
    have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc

theorem exists_phi : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A',
    AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧
      (IsAmpleCls c → IsIsogeny φ) := by
  intro K _ A A' P hP hdim c
  set β : Pic (A.X ⊗ A.X).left := AbVar.lam c (fst A.X A.X) (snd A.X A.X) with hβ
  have hpull : ∀ {Y : Over (Sp K)} (x y : Y ⟶ A.X),
      CechPic.pull (lift x y).left β = AbVar.lam c x y := fun x y => by
    rw [hβ, pull_lam_av, lift_fst, lift_snd]
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ A.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β := by
    intro Y a a' t
    rw [hpull, hpull, hpull]
    exact _root_.GlobalTheory.AV.AbVar.lam_mul_left_of_cube K A c Y a a' t
  have hnorm : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left β = 0 := by
    rw [hpull, AbVar.lam, _root_.mul_one, pull_one_eq_zero, sub_self, sub_zero]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' A P hP β hadd hnorm
  refine ⟨ψ, hψ, fun hc => ?_⟩
  have hfin : IsFinite ψ.hom.left := by
    refine (_root_.GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A A' ψ).2 ?_
    have hF := GlobalTheory.T.finite_mumfordClass_eq_zero_ample K A c hc
    refine Finite.of_injective (β := {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K)))
      (snd A.X _ ≫ x) = 0}) (fun x => ⟨x.1, ?_⟩) ?_
    · have hx : x.1 ≫ ψ.hom = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, ptMap_apply] at this
        exact this
      rw [← hpull, hψ, AbDual.pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hx, MonObj.comp_one]
      exact AbDual.evc_one_right hP.isLB hP.zero _
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  exact ⟨hfin, _root_.GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq K A A' ψ hdim.symm hfin⟩

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

open IsDedekindDomain
namespace GlobalTheory.CompatLim

theorem norm_sub_le_of_dvd (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x y : ℤ) (h : ((ℓ ^ k : ℕ) : ℤ) ∣ x - y) :
    ‖((x : ℤ_[ℓ]) - (y : ℤ_[ℓ]))‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this
  rw [← this]

theorem exists_padicInt_lim (p ℓ : ℕ) [Fact ℓ.Prime] (hp : p.Prime) (hne : ℓ ≠ p) (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ L : ℤ_[ℓ], ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : ℤ_[ℓ], L = (a n : ℤ_[ℓ]) + (n : ℤ_[ℓ]) * b := by
  have hℓ : ℓ.Prime := Fact.out
  have hcop : ∀ k, (ℓ ^ k).Coprime p := fun k => Nat.Coprime.pow_left k ((Nat.coprime_primes hℓ hp).2 hne)
  have hpos : ∀ k, 0 < ℓ ^ k := fun k => pow_pos hℓ.pos k

  have key : ∀ k m, k ≤ m → ((ℓ ^ k : ℕ) : ℤ) ∣ a (ℓ ^ m) - a (ℓ ^ k) := by
    intro k m hkm
    have h := ha (ℓ ^ k) (ℓ ^ (m - k)) (hpos k) (hpos _) (by rw [← pow_add, Nat.add_sub_cancel' hkm]; exact hcop m)
    rwa [← pow_add, Nat.add_sub_cancel' hkm] at h
  set s : ℕ → ℤ_[ℓ] := fun k => (a (ℓ ^ k) : ℤ_[ℓ]) with hs
  have hdist : ∀ k m, k ≤ m → dist (s m) (s k) ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    rw [dist_eq_norm]
    exact norm_sub_le_of_dvd ℓ k _ _ (key k m hkm)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hcs : CauchySeq s := by
    refine cauchySeq_of_le_geometric ((ℓ : ℝ)⁻¹) 1 (inv_lt_one_of_one_lt₀ hℓ1) fun k => ?_
    rw [dist_comm, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdist k (k + 1) (Nat.le_succ k)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLk : ∀ k, ‖L - s k‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have hmem : L ∈ Metric.closedBall (s k) ((ℓ : ℝ) ^ (-(k : ℤ))) :=
      Metric.isClosed_closedBall.mem_of_tendsto hL
        (Filter.eventually_atTop.2 ⟨k, fun m hm => Metric.mem_closedBall.2 (hdist k m hm)⟩)
    rwa [Metric.mem_closedBall, dist_eq_norm] at hmem
  refine ⟨L, fun n hn hnp => ?_⟩
  set e := n.factorization ℓ
  set m := n / ℓ ^ e
  have hnm : ℓ ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hm : ℓ.Coprime m := Nat.coprime_ordCompl hℓ hn.ne'
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hnm; omega

  have h1 : L - s e ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hLk e)

  have h2 := ha (ℓ ^ e) m (hpos e) hmpos (by rw [hnm]; exact hnp)
  rw [hnm] at h2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h1
  obtain ⟨d, hd⟩ := h2
  have hu : IsUnit (m : ℤ_[ℓ]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)
  obtain ⟨u, hu⟩ := hu
  refine ⟨(u⁻¹ : ℤ_[ℓ]ˣ) * (c - (d : ℤ_[ℓ])), ?_⟩
  have hd' : (a n : ℤ_[ℓ]) - s e = (ℓ : ℤ_[ℓ]) ^ e * d := by
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hd
    push_cast at this
    simpa [hs] using this
  have hn' : (n : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ e * u := by
    rw [hu, ← hnm]; push_cast; ring
  rw [hn']
  have : (ℓ : ℤ_[ℓ]) ^ e * (u : ℤ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) * (c - d)) = (ℓ : ℤ_[ℓ]) ^ e * (c - d) := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc (u : ℤ_[ℓ]), Units.mul_inv, _root_.one_mul]
  rw [this]
  linear_combination hc - hd'

open Rat.HeightOneSpectrum in
theorem natGenerator_ne (p : ℕ) (v : AwayP p) : (primesEquiv v.1 : ℕ) ≠ p := by
  obtain ⟨w, hw⟩ := v
  intro h
  apply hw
  have hs := span_natGenerator (R := ℤ) w
  change natGenerator w = p at h
  rw [h] at hs
  rw [hs]
  ext x
  rw [Ideal.mem_map_of_equiv]
  simp [eq_intCast]


open Rat.HeightOneSpectrum in
theorem exists_integer_lim (p : ℕ) [hp : Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) (v : AwayP p) :
    ∃ x : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ b : v.1.adicCompletionIntegers ℚ, x = (a n : v.1.adicCompletionIntegers ℚ) + (n : v.1.adicCompletionIntegers ℚ) * b := by
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨L, hL⟩ := exists_padicInt_lim p (primesEquiv v.1 : ℕ) hp.out (natGenerator_ne p v) a ha
  let e := (RingEquivClass.toRingEquiv (adicCompletionIntegers.padicIntEquiv (R := ℤ) v.1)).symm
  refine ⟨e L, fun n hn hnp => ?_⟩
  obtain ⟨b, hb⟩ := hL n hn hnp
  refine ⟨e b, ?_⟩
  rw [hb, map_add (f := _), map_mul, map_intCast, map_natCast]

theorem exists_lim : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  intro p _ a ha
  choose x hx using exists_integer_lim p a ha
  let α : AfP p := RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)
  refine ⟨α, fun v => (x v).2, fun n hn hnp => ?_⟩
  choose b hb using fun v => hx v n hn hnp
  let β : AfP p := RestrictedProduct.mk (fun v => (b v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (b v).2)
  refine ⟨β, fun v => (b v).2, ?_⟩
  apply RestrictedProduct.ext
  intro v
  have h1 : AfP.eval v α = x v := rfl
  have h2 : AfP.eval v β = b v := rfl
  have h3 : AfP.eval v ((a n : AfP p) + n • β) = (a n : v.1.adicCompletion ℚ) + (n : v.1.adicCompletion ℚ) * b v := by
    rw [map_add (f := _), map_intCast, map_nsmul, h2, nsmul_eq_mul]
  change AfP.eval v α = AfP.eval v ((a n : AfP p) + n • β)
  rw [h3, h1, hb v]
  push_cast
  rfl

end GlobalTheory.CompatLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruences
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AfUnit

variable {p : ℕ} [Fact p.Prime]

theorem exists_nat_mem (v : AwayP p) : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
  have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
  obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
  have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
  refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
  · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
  · rcases Int.natAbs_eq x with h1 | h1
    · rw [← h1]; exact hx
    · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx

theorem val_natCast (v : AwayP p) (m : ℕ) :
    Valued.v ((m : ℕ) : v.1.adicCompletion ℚ) = v.1.valuation ℚ (algebraMap ℤ ℚ (m : ℤ)) := by
  have e : ((m : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (m : ℤ) := by simp
  rw [e, IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _

theorem val_eval_eq_one (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β)
    (v : AwayP p) : Valued.v (AfP.eval v c) = 1 := by
  obtain ⟨l, hl0, hlp, hlv⟩ := exists_nat_mem v
  obtain ⟨hcop, β, hβ, e⟩ := h l hl0 hlp
  have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
    rw [val_natCast, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlv
  have hu : Valued.v ((u l : ℕ) : v.1.adicCompletion ℚ) = 1 := by
    rw [val_natCast]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun hlt' => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hlt'
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ a hlt') (Ideal.mul_mem_left _ b hlv)))
  have hsmall : Valued.v (AfP.eval v (l • β)) < 1 := by
    rw [map_nsmul, nsmul_eq_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hβ v)) hlt
  rw [e, map_add (f := _), map_natCast]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hu]; exact hsmall), hu]

theorem exists_mul_eq_one : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ),
    (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) →
    ∃ c' : AfP p, c * c' = 1 := by
  intro p _ c u h
  have hv := val_eval_eq_one c u h
  have hint : ∀ v : AwayP p, (AfP.eval v c)⁻¹ ∈ v.1.adicCompletionIntegers ℚ := fun v => by
    show Valued.v (AfP.eval v c)⁻¹ ≤ 1
    rw [map_inv₀, hv v, inv_one]
  let c' : AfP p := ⟨fun v => (AfP.eval v c)⁻¹, Filter.Eventually.of_forall hint⟩
  refine ⟨c', Subtype.ext (funext fun v => ?_)⟩
  have hne : AfP.eval v c ≠ 0 := fun h0 => by simpa [h0] using hv v
  exact mul_inv_cancel₀ hne

end GlobalTheory.AfUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibre
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.AmpleCut

theorem le_of_succ_le_add_one {x : WithBot ℕ∞} {d : ℕ} (h : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ x + 1) :
    (d : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have : d + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d ≤ n)

theorem exists_irreducible_diff_NV : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime →
    IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e →
    f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  intro k _ X _ p D hX P hA ℓ d e C f hℓ hCi hCc hCf hdim he hf
  by_cases h0 : C ∩ NV P e 0 f = ∅
  · refine ⟨C, hCi, hCc, fun x hx => ⟨hx, fun hx' => ?_⟩, ?_⟩
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) x ⟨hx, hx'⟩
    · exact le_trans (by exact_mod_cast Nat.le_succ d) hdim
  obtain ⟨u, hu⟩ := (_root_.GlobalTheory.HSAmp.pow_sec_dict k X p P e).2 f hf
  have hisP : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have hne : (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)).Nonempty := by
    rw [← hu]; exact Set.nonempty_iff_ne_empty.2 h0
  by_cases hsub : C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)
  · exfalso
    have haff := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
    have h1 := _root_.GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) ℓ _ C hℓ haff hCi hCc hCf hsub
    have h2 := hdim.trans h1
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h2
    have := WithBot.coe_le_coe.1 this
    norm_cast at this
  · obtain ⟨C', h1, h2, h3, h4⟩ :=
      _root_.GlobalTheory.KrullZero.exists_irreducible_zero k X p D hX (lbPow P.L.B e) u C (isLB_lbPow hA.isLB e) hCi hCc hne hsub
    refine ⟨C', h1, h2, ?_, le_of_succ_le_add_one (hdim.trans h4)⟩
    rw [hu]; exact h3

end GlobalTheory.AmpleCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponentStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  first | exact @GlobalTheory.KeyPowTw.exists_twSec_keyPow | exact GlobalTheory.KeyPowTw.exists_twSec_keyPow | (intros; apply GlobalTheory.KeyPowTw.exists_twSec_keyPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDvd

variable {p : ℕ} [Fact p.Prime]

def adBasis {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem adBasis_repr_inAf {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (z : D.La) (i : J) :
    (adBasis b).repr (inAf D z) i = algebraMap ℚ (AfP p) ((b.repr z i : ℤ) : ℚ) := by
  simp only [adBasis, inAf, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

theorem isIntAf_adBasis_repr {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {w : AfP p ⊗[ℚ] VQ D}
    (hw : w ∈ LaHat D) : IsIntAf ((adBasis b).repr w i) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (adBasis b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [adBasis, Algebra.smul_def]
    rw [e]
    intro v
    rw [map_mul, map_intCast]
    exact mul_mem (intCast_mem _ _) (hc v)
  | zero =>
    intro v
    rw [map_zero, Finsupp.zero_apply, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro v
    rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem exists_eq_nsmul_of_inAf (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ) (_hn : 0 < n) (_hc : n.Coprime p)
    (h : ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c)
    (z : D.La) (hz : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u := by
  obtain ⟨w, hw, e⟩ := hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.repr z i := by
    intro i
    refine h _ _ (isIntAf_adBasis_repr b i hw) ?_
    rw [← adBasis_repr_inAf, e, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  choose d hd using hd
  refine ⟨∑ i, d i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.LKGeo.LatDvd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedGeneratorOfFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_twistedGenerator_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  first | exact @GlobalTheory.TwNorm.exists_gen_fac | exact GlobalTheory.TwNorm.exists_gen_fac | (intros; apply GlobalTheory.TwNorm.exists_gen_fac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (n : ℕ), 0 < n → (n : κ) ≠ 0 → ∀ y y' : Over.mk x ⟶ B, y ^ n = 1 → y' ^ n = 1 → ∃ e : (Γ((Over.mk x).left, ⊤))ˣ, Out.WeilIs B M n y y' e := by
  first | (exact @GlobalTheory.WeilGeomPt.exists_weilIs_geomPt) | (exact GlobalTheory.WeilGeomPt.exists_weilIs_geomPt) | (intros; apply GlobalTheory.WeilGeomPt.exists_weilIs_geomPt  <;> assumption)
end

