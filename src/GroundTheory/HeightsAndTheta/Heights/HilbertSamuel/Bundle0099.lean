module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenLocal
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem homog_unique {p : MRingOver S ι} {a b : K → ℕ} (ha : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a) (hb : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p b)
    (h0 : p ≠ 0) : a = b := by
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp h0)
  funext k
  exact (ha μ hμ k).symm.trans (hb μ hμ k)

theorem chartMon_ne_zero [Nontrivial S] (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ≠ 0 := by
  have h : chartMon (S := S) c e = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (e k)) 1 := by
    rw [MvPolynomial.monomial_sum_one, chartMon]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  rw [h, Ne, MvPolynomial.monomial_eq_zero]
  exact one_ne_zero

theorem chartMon_one_pow (c : ∀ k, ι k) (n : ℕ) :
    chartMon (S := S) c (fun _ => 1) ^ n = chartMon c (fun _ => n) := by
  simp only [chartMon, pow_one, ← Finset.prod_pow]

theorem smul_mk_cancel' {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) {s : MRingOver S ι} (hs : s ∈ T) :
    (w * s) • LocalizedModule.mk y (⟨s, hs⟩ : T) = LocalizedModule.mk (w • y) 1 :=
  smul_mk_cancel w y ⟨s, hs⟩

theorem exists_kill_of_res_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c c' : ∀ k, ι k)
    (w : LocalizedModule (KH.cellMon S (chart c').1) M)
    (hw : KH.cellRes S M (chart c').1 (fun k => ({c k, c' k} : Finset (ι k))) w = 0) :
    ∃ e : ℕ, chartMon (S := S) c (fun _ => e) • w = 0 := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hsub : ∀ k, (chart c').1 k ⊆ ({c k, c' k} : Finset (ι k)) := fun k => by simp [chart]
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono hsub)] at hw
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp
      (hw.trans (LocalizedModule.zero_mk (1 : KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k))))).symm)
    simp only [one_smul, smul_zero] at hv
    obtain ⟨e, w', hw'⟩ := dvd_of_mem_pair v.2
    have hz : (chartMon (S := S) c (fun _ => e) * chartMon c' (fun _ => e)) • m = 0 := by
      rw [hw', mul_comm, mul_smul, ← Submonoid.smul_def, hv, smul_zero]
    refine ⟨e, ?_⟩
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨chartMon c' (fun _ => e), chartMon_mem c' _⟩, ?_⟩
    show chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • chartMon (S := S) c (fun _ => e) • m =
      chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • (0 : M)
    rw [smul_zero, smul_zero, smul_comm (chartMon c' (fun _ => e)) (s : MRingOver S ι),
      smul_smul (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)) m,
      mul_comm (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)), hz, smul_zero]

theorem genNear_of_chart [Nontrivial S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {d : K → ℤ} (h𝓜 : KH.IsMGraded S ι 𝓜)
    (c : ∀ k, ι k) {f₀ : MRingOver S ι} {δ₀ : K → ℕ} (hf₀ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f₀ δ₀)
    (hloc : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a ∧ (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c)) :
    GenNear S ι 𝓜 d (f₀ * chartMon c (fun _ => 1)) (δ₀ + fun _ => 1) := by
  intro J
  obtain ⟨c', rfl⟩ : ∃ c', J = chart c' := ⟨_, eq_chart J⟩
  intro x hx
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx

  have hy : LocalizedModule.mk m (⟨chartMon c a, chartMon_mem c a⟩ : KH.cellMon S (chart c).1) ∈
      KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d :=
    GenSESStep.mk_mem_locPart _ _ a (isMultiHomog_chartMon c a) hm
  obtain ⟨t₁, a₁, r, p, z, ht₁T, ht₁, hp, hz, he⟩ := hloc _ hy
  obtain ⟨α₁, rfl⟩ := exists_chartMon ht₁T
  obtain rfl : a₁ = α₁ := homog_unique ht₁ (isMultiHomog_chartMon c α₁) (chartMon_ne_zero c α₁)

  set U : ∀ k, Finset (ι k) := fun k => {c k, c' k} with hU
  have hsub : ∀ k, (chart c).1 k ⊆ U k := fun k => by simp [chart, hU]
  have hsub' : ∀ k, (chart c').1 k ⊆ U k := fun k => by simp [chart, hU]
  have hle := GenTwistGenerated.cellMon_mono (S := S) hsub
  have hle' := GenTwistGenerated.cellMon_mono (S := S) hsub'
  have hagree : ∀ j, KH.cellRes S M (chart c').1 U (z j (chart c')) =
      KH.cellRes S M (chart c).1 U (z j (chart c)) := fun j =>
    (res_agree (z j) (LinearMap.mem_ker.mp (hz j).2) c c' U (fun k => by simp [hU])
      (fun k => by simp [hU])).symm
  have hD : KH.cellRes S M (chart c').1 U ((f₀ * chartMon c a₁ * (t : MRingOver S ι)) • LocalizedModule.mk m t -
      ∑ j, (chartMon c a * p j) • z j (chart c')) = 0 := by
    have h2 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
        LocalizedModule.mk ((f₀ * chartMon c a₁) • m) 1 := by
      have e1 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
          chartMon (S := S) c a • KH.cellRes S M (chart c).1 U (∑ j, p j • z j (chart c)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hagree j, map_smul, mul_smul]
      rw [e1, ← he, map_smul, GenTwistGenerated.cellRes_mk hle, smul_smul,
        mul_comm (chartMon (S := S) c a) (f₀ * chartMon c a₁)]
      exact smul_mk_cancel' _ _ _
    rw [map_sub, h2, map_smul, GenTwistGenerated.cellRes_mk hle', sub_eq_zero]
    exact smul_mk_cancel' _ _ _
  obtain ⟨e, he0⟩ := exists_kill_of_res_eq_zero c c' _ hD
  rw [smul_sub, sub_eq_zero] at he0

  set E : ℕ := ∑ k, a₁ k with hE
  have haE : ∀ k, a₁ k ≤ E := fun k =>
    Finset.single_le_sum (f := a₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hexp : (fun _ : K => e + E + 1) = (fun _ => 1) + (fun k => E - a₁ k) + (fun _ => e) + a₁ := by
    funext k
    simp only [Pi.add_apply]
    have := haE k
    omega
  have hring : (f₀ * chartMon c (fun _ => 1)) ^ (e + E + 1) * (t : MRingOver S ι) =
      (f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k)) *
        (chartMon c (fun _ => e) * (f₀ * chartMon c a₁ * (t : MRingOver S ι))) := by
    rw [mul_pow, chartMon_one_pow, hexp, chartMon_add, chartMon_add, chartMon_add]
    ring
  refine ⟨e + E + 1, t, a, r, fun j => f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k) *
    chartMon c (fun _ => e) * chartMon c a * p j, z, t.2, ht, fun j => ?_, hz, ?_⟩
  · have h := GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (isMultiHomog_pow hf₀ (e + E))
        (isMultiHomog_chartMon c (fun _ => 1))) (isMultiHomog_chartMon c (fun k => E - a₁ k)))
        (isMultiHomog_chartMon c (fun _ => e))) (isMultiHomog_chartMon c a)) (hp j)
    convert h using 1
    funext k
    simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, Pi.one_apply, nsmul_eq_mul]
    have := haE k
    zify [this] at *
    ring
  · rw [hring, mul_smul, mul_smul (chartMon (S := S) c (fun _ => e)), he0, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp only [smul_smul]
    congr 1
    ring

end ChartNakayamaGen

theorem ChartNakayamaGen.proof : ChartNakayamaGen.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d hS hM h𝓜 hP _ I hI hgen
  obtain ⟨c, rfl⟩ : ∃ c, I = ChartNakayamaGen.chart c := ⟨_, ChartNakayamaGen.eq_chart I⟩
  have h1 : (1 : S) ≠ 0 := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by
    have e : (1 : MRingOver S ι) = 0 := by rw [← C_1, h, C_0]
    rw [e]
    exact P.zero_mem))
  have : Nontrivial S := nontrivial_of_ne 1 0 h1
  have hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P := fun k => hI k (c k) (Finset.mem_singleton_self _)
  obtain ⟨f₀, δ₀, hf₀, hf₀P, hloc⟩ := ChartNakayamaGen.chart_nakayama hS hM h𝓜 hP c hc hgen
  refine ⟨f₀ * ChartNakayamaGen.chartMon c (fun _ => 1), δ₀ + fun _ => 1,
    GenSESStep.isMultiHomog_mul hf₀ (ChartNakayamaGen.isMultiHomog_chartMon c _), fun h => ?_,
    ChartNakayamaGen.genNear_of_chart h𝓜 c hf₀ hloc⟩
  rcases hP.mem_or_mem h with h | h
  · exact hf₀P h
  · exact ChartNakayamaGen.cellMon_notMem hP hc (ChartNakayamaGen.chartMon_mem c _) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefAmpleGeneric

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem isArithVar_comap_of_isProjVarF {K : Type} [Fintype K] [Nonempty K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRingOver ℚ ι)} {d : ℕ} (hW : IsProjVarF W d) :
    IsArithVar (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) (d + 1) ∧
      (W.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = W := by
  classical
  obtain ⟨⟨hprime, hhom, hrel⟩, hdim⟩ := hW
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφdef
  set P := W.comap φ with hPdef
  have := hprime
  have hPp : P.IsPrime := Ideal.comap_isPrime φ W
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = φ := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hmap : P.map φ = W := by
    have h := IsLocalization.map_under S (MRingOver ℚ ι) W
    rwa [hφ] at h
  have hch : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
    intro m hm
    by_contra h0
    have hu : IsUnit (φ (C m)) := by
      rw [hφdef, map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using h0 : ((Int.castRingHom ℚ) m) ≠ 0)).map C
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hWN : NumbersDVR.IsMultiProjPrime (K := K) W :=
    (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff W).mpr ⟨hprime, hhom, hrel⟩
  have hPN : NumbersDVR.IsMultiProjPrime (K := K) P := by
    refine ⟨hPp, fun f hf b => ?_, fun k => ?_⟩
    · show φ _ ∈ W
      rw [hφdef, ← NumbersDVR.weightedHomogeneousComponent_map]
      exact hWN.multiHomog _ hf b
    · obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h => hi (by simpa [hPdef, hφdef] using h)⟩
  obtain ⟨-, hhomP, hrelP⟩ := (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff P).mp hPN
  obtain ⟨-, -, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨⟨‹Nonempty K›, ⟨hPp, hhomP, hrelP⟩, ?_, ?_⟩, hmap⟩
  · ext m
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨hch m, fun h => by rw [h, map_zero]; exact P.zero_mem⟩
  · have hext : ReciprocityTheory.AnForm.R.extQ P = W := hmap
    rw [← hd, hext, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]

end NefAmpleGeneric

theorem NefAmpleGeneric.proof (hKA : KH.KAmpStatement)
    (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) : NefAmpleGeneric.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 b a hV hP0 hs hb ha
  classical
  have : Nonempty K := hV.1
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hnef : KH.NefOnF I (KH.genIdeal y) M.a := by
    intro W hW hle
    obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have h0 : 0 ≤ geomDeg (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) M 1 :=
      NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hs _ hWar hPW
    have hdeg := hDG K ι (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) 1 ![M] hWar (fun j => by fin_cases j; exact hs.1)
    rw [hWmap] at hdeg
    have hpot : pot ![M] = fun (_ : Fin 1) z => Real.log (M.h z) := by
      funext j z
      fin_cases j
      rfl
    have hL : (fun j => (![M] j).a) = ![M.a] := by
      funext j
      fin_cases j
      rfl
    rw [hpot, hL] at hdeg
    have h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W ![M.a] : ℝ) := by
      rw [← hdeg]
      exact h0
    show 0 ≤ NumbersDVR.intNum ℚ W ![M.a]
    exact_mod_cast h1
  have h := hKA ℚ K ι I (KH.genIdeal y) D M.a b a hI (isProjVarF_map_of_isArithVar hV) hnef hb ha
  rwa [← natCast_zsmul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul SmallGenTwist

noncomputable section

namespace PerturbedMonomialBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartMono_exponent (c : ∀ k, ι k) (d : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ d k := by
  classical
  refine ⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩
  · simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
      rw [chartMono, monomial_sum_one]
      exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
    have e1 := eval_chartMono z c d
    rw [h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)] at e1
    simpa using e1

theorem smallGen_of_monomialsBounded (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ)
    (ha : A.a = fun k => (a k : ℤ)) (hB : MonomialsBounded (mCoordIdeal y) A a) : SmallGen y A := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert pow_mem hmem (a k) using 1
    simp [ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by
      simp [ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = a + dh := funext fun k => by
      have := hdeg k
      simp only [ha, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply]
      omega
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g - chartMono (e.symm j) a * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)
    have h0 : aeval y (g - chartMono (e.symm j) a * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨μ, hμ, hzμ⟩ := chartMono_exponent (e.symm j) a
    rw [← hzμ z]
    exact hB z hz μ hμ

end PerturbedMonomialBound


open PerturbedMonomialBound in
theorem PerturbMonomial.proof (hDeg : GenDegAmple.Statement) : PerturbMonomial.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _
  have hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1 := by
    funext k
    simp [HermLine.zcomb, ha, fsH_a]
  refine ⟨hP0, ?_, ?_, ?_⟩
  · exact PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one
  · rw [hBa]
    refine hDeg K ι Ω y D _ hV fun k => ?_
    have : (0 : ℤ) ≤ (q : ℤ) * a k := by positivity
    omega
  · have h := smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1
    rw [Nat.cast_one] at h
    exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ProjFSMass.proof : ProjFSMass.Statement := by
  intro D Ω _ _ κ _ x e m hfr hFS
  exact ⟨gbPsi e, gb_isGoodProj hfr, gb_ptsIntegralAt hfr hFS⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibreDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegralInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) → (M : Ω) ≠ 0 →
    (∀ (d : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      s / aeval y (L j) ^ (q * τ) ∈
        integralClosure
          (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / aeval y (L j)))) Ω

section Inhabitants

namespace PullSectionIntegralInt

end PullSectionIntegralInt

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

