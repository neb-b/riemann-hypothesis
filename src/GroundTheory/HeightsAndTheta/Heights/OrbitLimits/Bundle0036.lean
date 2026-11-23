module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeLength
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsMultiHomogIdeal divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat segreChartIdeal segreChartComponents
  mem_segreChartComponents)

namespace ChartConeLength

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem aeval_algebraMap_X (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X q)) f =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
      MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp => rw [map_mul, map_mul, hp, aeval_X]

theorem coneRatio_eq_unit_mul (i : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : ReciprocityTheory.AnForm.R.IsMultiHomog f a) :
    ∃ c : (ConeRing i)ˣ, coneRatio i f = c * algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) f := by
  refine ⟨∏ k, (isUnit_coneX i k).unit⁻¹ ^ a k, ?_⟩
  have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hf
    (fun k => (((isUnit_coneX i k).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i))
    (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X q))
  rw [aeval_algebraMap_X] at h
  rw [coneRatio, h]
  push_cast
  rfl

theorem map_algebraMap_eq_map_ratioMap (i : (k : K) → ι k) {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q) :
    (Q.map (MvPolynomial.map (Int.castRingHom ℂ))).map (algebraMap _ (ConeRing i)) =
      ((Q.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have key : ∀ f ∈ S, ∃ c : (ConeRing i)ˣ,
      ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f)) =
        c * algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    rw [ratioMap_dehom]
    exact coneRatio_eq_unit_mul i (a := a) fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k
  rw [Ideal.map_span, Ideal.map_span, Ideal.map_span, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := key f hf
    have h : algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f) =
        ((c⁻¹ : (ConeRing i)ˣ) : ConeRing i) * ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
      rw [hc, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := key f hf
    rw [hc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨f, hf, rfl⟩, rfl⟩)


omit [∀ k, Fintype (ι k)] in
theorem comap_ratioMap_map (i : (k : K) → ι k) (Y : Ideal (DehomRing i)) :
    (Y.map (ratioMap i)).comap (ratioMap i) = Y := by
  refine le_antisymm (fun g hg => ?_) Ideal.le_comap_map
  have h := Ideal.mem_map_of_mem (evalOne i) (Ideal.mem_comap.1 hg)
  rwa [Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_ratioMap] at h


omit [∀ k, Fintype (ι k)] in
theorem isRadical_map_dehom (i : (k : K) → ι k) {P' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hrad : P'.IsRadical)
    (heq : P'.map (algebraMap _ (ConeRing i)) = (P'.map (dehom i)).map (ratioMap i)) :
    (P'.map (dehom i)).IsRadical := by
  rintro g ⟨n, hn⟩
  have h1 : ratioMap i g ∈ (P'.map (algebraMap _ (ConeRing i))).radical :=
    ⟨n, by rw [← map_pow, heq]; exact Ideal.mem_map_of_mem _ hn⟩
  rw [← IsLocalization.map_radical (Submonoid.powers (coneUnit i)) (ConeRing i), hrad.radical, heq] at h1
  rw [← comap_ratioMap_map i (P'.map (dehom i))]
  exact h1


omit [Fintype K] in
theorem isMultiHomogIdeal_sup_span {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {s : MRing ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S ∪ {s}, ?_, by rw [Ideal.span_union]⟩
  rintro f (hf | hf)
  · exact hS f hf
  · rw [Set.mem_singleton_iff.1 hf]
    exact ⟨a, hs⟩

end ChartConeLength


open ChartConeLength in
theorem ChartConeLength.proof (hT : ConeRingLaurent.Statement) (hN : ChartDehomIdeal.Statement) :
    ChartConeLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle
  classical
  have hρ : Function.Surjective (segreDehom σ i) := segreDehom_surjective σ i
  obtain ⟨hTf, hTp⟩ := hT K ι i
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have hPm : IsMultiHomogIdeal P := hP.2.1.2.1
  have hWm : IsMultiHomogIdeal W := hWa.2.1.2.1
  obtain ⟨a, -, hsa, -⟩ := hs
  have hJm : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := isMultiHomogIdeal_sup_span hPm hsa
  have hPrad : ((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).IsRadical :=
    isRadical_map_dehom i (HilbertSamuel.PrimeComplexRadical.proof _ P hP.2.1.1) (map_algebraMap_eq_map_ratioMap i hPm)
  have hIP := hN K ι P m σ i hPm
  rw [hPrad.radical] at hIP
  have hIW := hN K ι W m σ i hWm

  have hker : ∀ J : Ideal (DehomRing i), RingHom.ker (segreDehom σ i) ≤ J.comap (segreDehom σ i) := fun J =>
    Ideal.comap_mono bot_le
  have hLHS : segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s} =
      (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).comap (segreDehom σ i) := by
    have hJy : ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) =
        (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).map (segreDehom σ i) := by
      rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_sup, hIP, Ideal.map_comap_of_surjective _ hρ, Ideal.map_span,
        Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, Set.image_singleton,
        chartSection_eq_chartSubst, segreDehom_chartSubst]
    rw [hJy, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]
    exact le_sup_of_le_left (hIP ▸ hker _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.map (segreDehom σ i) := ⟨_, rfl⟩
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hW'min.1.1
  have hkerW' : RingHom.ker (segreDehom σ i) ≤ W' := le_trans (hIW ▸ hker _) hW'min.1.2
  have hW'Q : W' = Q.comap (segreDehom σ i) := by
    rw [hQ, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]
    exact hkerW'
  have hQp : Q.IsPrime := hQ ▸ Ideal.map_isPrime_of_surjective hρ hkerW'
  have hQmin : Q ∈ ((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).minimalPrimes := by
    have hWyQ : (W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) ≤ Q := by
      rw [hQ]
      intro g hg
      obtain ⟨f, rfl⟩ := hρ g
      apply Ideal.mem_map_of_mem
      apply hW'min.1.2
      rw [hIW]
      exact Ideal.le_radical hg
    refine ⟨⟨hQp, hWyQ⟩, fun q hq hqQ => ?_⟩
    have : q.IsPrime := hq.1
    have hc : W' ≤ q.comap (segreDehom σ i) := hW'min.2
      ⟨Ideal.comap_isPrime _ _, by rw [hIW]; exact Ideal.comap_mono ((Ideal.IsPrime.radical_le_iff hq.1).2 hq.2)⟩
      (by rw [hW'Q]; exact Ideal.comap_mono hqQ)
    rw [hQ]
    exact (Ideal.map_mono hc).trans Ideal.map_comap_le
  have hL : localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
      localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q := by
    rw [hLHS, hW'Q]
    exact LocalMultComap.proof _ _ (segreDehom σ i : MvPolynomial (Fin m) ℂ →+* DehomRing i) _ Q hρ hQp

  have : W''.IsPrime := hW''.1.1
  have hu : coneUnit i ∉ W'' := by
    intro hu
    have h1 : segreDehom σ i (chartSubst σ i (coneUnit i)) ∈ Q := by
      rw [hQ]
      exact Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+*
        MvPolynomial (Fin m) ℂ) hu))
    rw [segreDehom_chartSubst, dehom_coneUnit] at h1
    exact hQp.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hdisj : Disjoint (Submonoid.powers (coneUnit i) : Set (MvPolynomial (Σ k, ι k) ℂ)) W'' :=
    (Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).2 hu
  have h𝔓p : (W''.map (algebraMap _ (ConeRing i))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) W'' ‹_› hdisj
  have h𝔓u : (W''.map (algebraMap _ (ConeRing i))).under _ = W'' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) ‹_› hdisj
  have h𝔓min : W''.map (algebraMap _ (ConeRing i)) ∈
      (((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i)).minimalPrimes := by
    rw [← map_algebraMap_eq_map_ratioMap i hWm,
      IsLocalization.minimalPrimes_map (Submonoid.powers (coneUnit i)) (ConeRing i), Set.mem_preimage, h𝔓u]
    exact hW''
  have : ((W''.map (algebraMap _ (ConeRing i))).comap (ratioMap i)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q₀, hq₀min, hq₀le⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.1 h𝔓min.1.2)
  have hq₀p : q₀.IsPrime := hq₀min.1.1
  have hq₀e : W''.map (algebraMap _ (ConeRing i)) = q₀.map (ratioMap i) :=
    le_antisymm (h𝔓min.2 ⟨hTp q₀ hq₀p, Ideal.map_mono hq₀min.1.2⟩ (Ideal.map_le_iff_le_comap.2 hq₀le))
      (Ideal.map_le_iff_le_comap.2 hq₀le)
  have hq₀ : q₀ = W''.map (dehom i) := by
    have h := congrArg (Ideal.map (evalOne i)) hq₀e
    rw [Ideal.map_map, Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_comp_algebraMap] at h
    exact h.symm
  have hq₀Q : q₀ = Q := by
    have hle' : q₀ ≤ Q := by
      rw [hq₀, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, ← segreDehom_chartSubst σ i f, hQ]
      exact Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+*
        MvPolynomial (Fin m) ℂ) hf))
    exact le_antisymm hle' (hQmin.2 ⟨hq₀p, hq₀min.1.2⟩ hle')

  have hflat1 : localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map
      (algebraMap _ (ConeRing i))) (W''.map (algebraMap _ (ConeRing i))) =
      localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W'' := by
    have : (W''.map (algebraMap _ (ConeRing i))).LiesOver W'' := ⟨h𝔓u.symm⟩
    have : Module.Flat (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) :=
      IsLocalization.flat _ (Submonoid.powers (coneUnit i))
    exact localMult_map_of_flat _ W'' _ (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)
  have hflat2 : localMult ((((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map
      (dehom i)).map (ratioMap i)) (Q.map (ratioMap i)) =
      localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q := by
    let := (ratioMap i).toAlgebra
    have : Module.Flat (DehomRing i) (ConeRing i) := hTf
    have := hTp Q hQp
    have : (Q.map (algebraMap (DehomRing i) (ConeRing i))).LiesOver Q := ⟨(comap_ratioMap_map i Q).symm⟩
    exact localMult_map_of_flat _ Q (Q.map (algebraMap (DehomRing i) (ConeRing i)))
      (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)
  rw [hL, ← hflat2, ← hq₀Q, ← hq₀e, ← map_algebraMap_eq_map_ratioMap i hJm, hflat1]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomIdeal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)

theorem ChartDehomIdeal.proof : ChartDehomIdeal.Statement := by
  intro K _ _ ι _ P m σ i hP
  classical
  set Q : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hQ
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := Q ⊔ dehomIdeal i with hJ
  set G : Fin m → MvPolynomial (Σ k, ι k) ℂ := fun a => ∏ k, X ⟨k, σ a k⟩ with hG

  have hseg : ∀ f, segreDehom σ i f = dehom i (aeval G f) := by
    intro f
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl

  have hcomap : ((Q.map (dehom i)).radical).comap (dehom i) = J.radical := by
    have hd : (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) = Ideal.Quotient.mk (dehomIdeal i) := rfl
    rw [← Ideal.comap_coe (dehom i), ← Ideal.map_coe (dehom i), Ideal.comap_radical, hd,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hval : ∀ (y : (Σ k, ι k) → ℂ) (f : MvPolynomial (Fin m) ℂ),
      aeval (R := ℂ) y (aeval G f) = aeval (R := ℂ) (fun a => segre y (σ a)) f := by
    intro y f
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext a
    simp [hG, segre]

  have hzero : ∀ y : (Σ k, ι k) → ℂ, y ∈ zeroLocus ℂ J ↔ y ∈ mcPts P ∧ ∀ k, y ⟨k, i k⟩ = 1 := by
    intro y
    constructor
    · intro hy
      have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
        have := hy _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
        simpa [sub_eq_zero] using this
      refine ⟨⟨fun k => ⟨i k, by simp [h1 k]⟩, fun f hf => ?_⟩, h1⟩
      have := hy _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
      exact this
    · rintro ⟨hy, h1⟩
      have hle : J ≤ RingHom.ker (aeval (R := ℂ) y : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
        refine sup_le ?_ ?_
        · rw [hQ, Ideal.map_le_iff_le_comap]
          intro f hf
          exact hy.2 f hf
        · rw [dehomIdeal, Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          simp [RingHom.mem_ker, h1 k]
      exact fun p hp => hle hp
  ext f
  rw [Ideal.mem_comap, hseg, ← Ideal.mem_comap, hcomap, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    segreChartIdeal, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
  constructor
  · intro hf y hy
    rw [hval]
    obtain ⟨hym, h1⟩ := (hzero y).1 hy
    refine hf _ ⟨y, hym, ?_, rfl⟩
    simp [segre, h1]
  · rintro hf x ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have h := Finset.prod_eq_zero (f := fun k => z ⟨k, i k⟩) (Finset.mem_univ k) h0
      exact one_ne_zero ((show segre z i = 1 from hzi).symm.trans h)
    set y := chartLift σ i (fun a => segre z (σ a)) with hy
    have hyz : y = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
      funext p
      rw [hy, chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
    have hym : y ∈ mcPts P := by
      rw [hyz]
      exact SegreChartZeroSet.scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz
    have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
      rw [hyz]
      exact inv_mul_cancel₀ (hne k)
    have := hf y ((hzero y).2 ⟨hym, h1⟩)
    rwa [hval, hy, segre_chartLift σ i z hzi] at this

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeRingLaurent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace ConeRingLaurent

theorem map_C_isPrime {D σ : Type*} [CommRing D] (𝔮 : Ideal D) [𝔮.IsPrime] :
    (𝔮.map (C : D →+* MvPolynomial σ D)).IsPrime := by
  rw [← Ideal.mk_ker (I := 𝔮), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)

def tProd : MvPolynomial K (DehomRing i) := ∏ k, X k

abbrev Laurent := Localization.Away (tProd i)

def laurentToConeRing : MvPolynomial K (DehomRing i) →+* ConeRing i :=
  eval₂Hom (ratioMap i) fun k => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)

theorem laurentToConeRing_tProd : laurentToConeRing i (tProd i) = algebraMap _ (ConeRing i) (coneUnit i) := by
  simp [laurentToConeRing, tProd, coneUnit, map_prod]

def toCone : Laurent i →+* ConeRing i :=
  IsLocalization.Away.lift (tProd i) (g := laurentToConeRing i) (by
    rw [laurentToConeRing_tProd]; exact IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneToLaurentPolynomial : MvPolynomial (Σ k, ι k) ℂ →+* Laurent i :=
  eval₂Hom ((algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C.comp (algebraMap ℂ (DehomRing i))))
    fun p => algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (C (dehom i (X p)) * X p.1)

theorem coneToLaurent_X_self (k : K) :
    coneToLaurentPolynomial i (X ⟨k, i k⟩) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X k) := by
  simp [coneToLaurentPolynomial, dehom_X_self]

theorem coneToLaurent_coneUnit :
    coneToLaurentPolynomial i (coneUnit i) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (tProd i) := by
  rw [coneUnit, map_prod]
  exact (Finset.prod_congr rfl fun k _ => coneToLaurent_X_self i k).trans (map_prod _ _ _).symm

def fromCone : ConeRing i →+* Laurent i :=
  IsLocalization.Away.lift (coneUnit i) (g := coneToLaurentPolynomial i) (by
    rw [coneToLaurent_coneUnit]; exact IsLocalization.Away.algebraMap_isUnit (tProd i))

theorem ratioMap_algebraMap (c : ℂ) :
    ratioMap i (algebraMap ℂ (DehomRing i) c) = algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
  rw [← AlgHom.commutes (dehom i) c, ratioMap_dehom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq]

theorem toCone_comp_fromCone : (toCone i).comp (fromCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneUnit i))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_C, toCone, laurentToConeRing]
    exact ratioMap_algebraMap i c
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_X', toCone, map_mul, laurentToConeRing, eval₂Hom_C]
    rw [ratioMap_dehom, coneRatio, aeval_X, mul_right_comm, (isUnit_coneX i p.1).val_inv_mul, one_mul]

theorem fromCone_algebraMap (f : MvPolynomial (Σ k, ι k) ℂ) :
    fromCone i (algebraMap _ (ConeRing i) f) = coneToLaurentPolynomial i f :=
  IsLocalization.Away.lift_eq _ _ _

theorem fromCone_comp_ratioMap :
    (fromCone i).comp (ratioMap i) =
      (algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C : DehomRing i →+* MvPolynomial K (DehomRing i)) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio, aeval_C,
      IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq,
      fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_C]
    rfl
  · intro p
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_X', map_mul, ← mul_assoc]
    have hu : fromCone i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) =
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) := by
      rw [IsUnit.unit_spec, fromCone_algebraMap, coneToLaurent_X_self]
    have hinv : fromCone i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    rw [mul_comm _ (algebraMap _ _ (C _)), mul_assoc, hinv, mul_one]

theorem fromCone_comp_toCone : (fromCone i).comp (toCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tProd i))
  apply MvPolynomial.ringHom_ext
  · intro y
    have h := RingHom.congr_fun (fromCone_comp_ratioMap i) y
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing,
      eval₂Hom_C] at h ⊢
    exact h
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing, eval₂Hom_X']
    rw [fromCone_algebraMap, coneToLaurent_X_self]

def laurentEquiv : Laurent i ≃+* ConeRing i :=
  RingEquiv.ofRingHom (toCone i) (fromCone i) (toCone_comp_fromCone i) (fromCone_comp_toCone i)

theorem toCone_comp_algebraMap : (toCone i).comp (algebraMap (DehomRing i) (Laurent i)) = ratioMap i := by
  refine RingHom.ext fun y => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i),
    toCone, IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, laurentToConeRing, eval₂Hom_C]

theorem map_laurent_isPrime (𝔮 : Ideal (DehomRing i)) [𝔮.IsPrime] :
    (𝔮.map (algebraMap (DehomRing i) (Laurent i))).IsPrime := by
  rw [IsScalarTower.algebraMap_eq (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i), ← Ideal.map_map,
    MvPolynomial.algebraMap_eq]
  apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (tProd i)) (Laurent i) _ (map_C_isPrime 𝔮)
  rw [Set.disjoint_left]
  intro x hx hmem
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  have hle : 𝔮.map (C : DehomRing i →+* MvPolynomial K (DehomRing i)) ≤
      RingHom.ker (eval₂Hom (Ideal.Quotient.mk 𝔮) fun _ : K => (1 : DehomRing i ⧸ 𝔮)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hy]
  have h0 := hle hmem
  rw [RingHom.mem_ker] at h0
  simp [tProd] at h0
  rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq_zero_iff_mem] at h0
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h0)

end ConeRingLaurent

theorem ConeRingLaurent.proof : ConeRingLaurent.Statement := by
  intro K _ ι i
  have hcomp : ratioMap i = (ConeRingLaurent.laurentEquiv i : ConeRingLaurent.Laurent i →+* ConeRing i).comp
      (algebraMap (DehomRing i) (ConeRingLaurent.Laurent i)) :=
    (ConeRingLaurent.toCone_comp_algebraMap i).symm
  constructor
  · rw [hcomp]
    refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ConeRingLaurent.laurentEquiv i).bijective)
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · intro 𝔮 h𝔮
    rw [hcomp, ← Ideal.map_map]
    have := ConeRingLaurent.map_laurent_isPrime i 𝔮
    exact Ideal.map_isPrime_of_equiv (ConeRingLaurent.laurentEquiv i)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartLatFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ChartLatFull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [NumberField Ω]
    (y : (Σ k, ι k) → Ω), Birational y →
    ∀ (a : K → ℤ) (τ : ℕ) (s : Ω), ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ chartLat y a τ

end GroundTheory.Heights₂.Heights.Targets
end

