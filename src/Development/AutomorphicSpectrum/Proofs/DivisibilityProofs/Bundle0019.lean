module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycle
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimension
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ
  obtain ⟨R, hR, hsum⟩ := psum_eq_sum_hsymm_neg N k hk
  rw [hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  rw [genNum_mul_expand]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : (classList b μ).length = k - a :=
    PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ
  have hl : a + (classList b μ ++ Q).length = e := by
    rw [List.length_append, hlen]
    omega
  rw [PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a
      (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl,
    PositivityTheory.HtPt.Pflag.genNum_hsymm,
    hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]
  simp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegree
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degreeStatement_of_intersectionSystem :
    ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun II h => GlobalTheory.CompanionTheory.Ar.Giv.degree_of_isIntersectionSystem II h

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEq
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

theorem divCycle_eq_off {K : Type} {ι : K → Type} {P : Ideal (MRing ι ℤ)} {f g : MRing ι ℤ} {S : Finset Nat.Primes}
    (h : ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W → IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    {W : Ideal (MRing ι ℤ)}
    (hW : W.IsPrime → ∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) :
    divCycle P f W = divCycle P g W := by
  by_cases hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hc.1 hc.2.1 hc.2.2 (hW hc.1)
    exact divCycle_eq_of_mul_sub_mem hu hv huv
  · have h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0 := fun s => by
      by_contra hne
      exact hc (le_and_isRelevant_of_divCycle_ne_zero hne)
    rw [h0, h0]

theorem not_mem_of_mem {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W) :
    (C ((q : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hq
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := hcop
  apply hW.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : MvPolynomial (Σ k, ι k) ℤ) =
      C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ) := by
    rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
  rw [e]
  exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)

theorem not_mem_of_horizontal {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : IsHorizontal W)
    (p : Nat.Primes) : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hp
  have h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := hp
  rw [show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem change_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  intro K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩ := hT ()
  obtain ⟨hAa, hA'a, hnorm⟩ := hiso ()
  let B : HermLine ι := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv
  have hB : IsSmoothHerm B := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)
  have hAB : IsSmoothHerm (A.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB
  have hAB' : IsSmoothHerm (A'.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB
  have dF : ∀ k, (A.tensor B).a k = bf k := fun k => by
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]
  have dG : ∀ k, (A'.tensor B).a k = bg k := fun k => by
    have h1 := congrFun hdeg k
    have h2 := congrFun hAa k
    have h3 := congrFun hA'a k
    simp only [Pi.sub_apply] at h1
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]
    linarith
  have e1 := hI.2.1 P D L A B hP hL hA hB
  have e2 := hI.2.1 P D L A' B hP hL hA' hB
  have r1 := hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP
  have r2 := hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP
  obtain ⟨fin1, s1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)
  obtain ⟨fin2, s2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)
  have hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
      ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
    refine finsum_congr fun W => ?_
    by_cases hW : IsHorizontal W
    · rw [divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]
    · have : W ∉ {W | IsHorizontal W} := hW
      simp [Set.indicator_of_notMem this]
  have ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L := by
    refine (_root_.GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog K ι P D _).1 _ _ fun z hz => ?_
    have h1 := hnorm z hz
    have pA := A.pos z hz.1
    have pA' := A'.pos z hz.1
    have pB := B.pos z hz.1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (B.h z) * h1
  have hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) =
      vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) := by
    intro p hp
    unfold vertAt cycEval
    refine finsum_congr fun W => ?_
    by_cases hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W
    · rw [divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp
        (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]
    · simp only [if_neg hpW, mul_zero]
  have vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) -
      (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) -
        (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
    have hF : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin1.subset fun p hp h0 => hp (by simp [h0])
    have hG : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin2.subset fun p hp h0 => hp (by simp [h0])
    rw [← finsum_sub_distrib hF hG,
      finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]
    · exact Finset.sum_congr rfl fun p _ => by ring
    · by_contra hpS
      exact hp (by simp [hv p (by simpa using hpS)])
  have e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') =
      I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B)) := by
    rw [e1, e2]; ring
  rw [e3, r1, r2, s1, s2, hor, ar, ← vert]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralEqGenericIntersection
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

theorem intNumL_ofFn_eq [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem divCycle_one (P W : Ideal (MRing ι ℤ)) : divCycle P (1 : MRing ι ℤ) W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  have e : (P ⊔ Ideal.span {(1 : MRing ι ℤ)}) = ⊤ := by simp
  rw [e] at h
  exact h.1.1.ne_top (top_le_iff.1 h.1.2)

theorem isPrime_mem_of_divCycle_ne {P W : Ideal (MRing ι ℤ)} {s : MRing ι ℤ}
    (h : divCycle P s W ≠ 0) : W.IsPrime ∧ s ∈ W := by
  unfold divCycle at h
  by_cases hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · exact ⟨hc.1.1.1, hc.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩
  · rw [dite_eq_right hc] at h
    exact absurd rfl h

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoHomog_C (c : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c : MRing ι ℤ) (0 : K → ℕ) := by
  intro m hm k
  rw [C_apply] at hm
  have h0 : m = 0 := Finset.mem_singleton.1 (support_monomial_subset hm)
  subst h0
  simp

theorem vertAt_two_of_ne (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) (l : List (K → ℤ)) :
    vertAt p P (C (2 : ℤ)) l = 0 := by
  classical
  unfold vertAt cycEval
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases h : divCycle P (C (2 : ℤ)) W = 0
  · rw [h, zero_mul]
  · obtain ⟨hW, h2⟩ := isPrime_mem_of_divCycle_ne h
    have hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
      intro hpW
      have hcop : IsCoprime (((p : ℕ) : ℤ)) 2 := by
        have : Nat.Coprime (p : ℕ) 2 := (Nat.coprime_primes p.2 Nat.prime_two).2 hp
        exact_mod_cast Nat.isCoprime_iff_coprime.2 this
      obtain ⟨a, b, hab⟩ := hcop
      apply hW.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Σ k, ι k) ℤ) = C a * C ((p : ℕ) : ℤ) + C b * C 2 := by
        rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
      rw [this]
      exact W.add_mem (W.mul_mem_left _ hpW) (W.mul_mem_left _ h2)
    exact mul_eq_zero_of_right _ (if_neg hpW)

theorem ptsIntegral_one_eq_vertAt (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (hI : IsIntersectionFamily I)
    (L : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) =
      (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hA : IsSmoothHerm (trivLine ι) := contDiffOn_const
  have hc := ptsIntegral_congr_and_homog K ι P D (fun j z => Real.log ((L j).h z))
  have nm1 : (1 : MRing ι ℤ) ∉ P := fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have nm2 : (C (2 : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : (2 : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    simp at h2
  have g1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := by
    simpa using geoHomog_C (K := K) (ι := ι) 1
  have g2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := geoHomog_C 2
  have f1 : IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_one _ _
  have f2 : IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have e1 := hI.2.2 P D L (trivLine ι) 1 0 hP hL hA (fun k => by simp [trivLine]) g1 nm1
  have e2 := hI.2.2 P D L (trivLine ι) (C 2) 0 hP hL hA (fun k => by simp [trivLine]) g2 nm2
  rw [(_root_.GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split K ι P D hP I 0 1 f1 nm1 L (trivLine ι)).2] at e1
  rw [(_root_.GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split K ι P D hP I 0 (C 2) f2 nm2 L (trivLine ι)).2] at e2
  have a1 : arInt P (1 : MRing ι ℤ) (trivLine ι) L = 0 := by
    unfold arInt
    rw [hc.1 _ (fun _ => (0 : ℝ) * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 0 (fun _ => 1)]
    simp
  have a2 : arInt P (C (2 : ℤ) : MRing ι ℤ) (trivLine ι) L =
      Real.log 2 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    rw [hc.1 _ (fun _ => Real.log 2 * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 (Real.log 2) (fun _ => 1)]
  have v1 : ∀ p : Nat.Primes, vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) = 0 := by
    intro p
    unfold vertAt cycEval
    exact finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h1 : ∑ᶠ W, (divCycle P (1 : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h2 : ∑ᶠ W, (divCycle P (C (2 : ℤ) : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_cases h : divCycle P (C (2 : ℤ) : MRing ι ℤ) W = 0
    · rw [h, Int.cast_zero, zero_mul]
    · have hW := (isPrime_mem_of_divCycle_ne h).2
      have : W ∉ {W : Ideal (MRing ι ℤ) | IsHorizontal W} := by
        intro hH
        have h2 : (2 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ) := hW
        rw [show W.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hH] at h2
        simp at h2
      rw [Set.indicator_of_notMem this, mul_zero]
  have p1 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) : ℝ) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun p => by rw [v1]; simp
  have p2 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) =
      Real.log 2 * (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
    refine (finsum_eq_single _ (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_).trans ?_
    · intro p hp
      have : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      rw [vertAt_two_of_ne P p this, Int.cast_zero, mul_zero]
    · norm_num
  rw [h1, p1, a1] at e1
  rw [h2, p2, a2] at e2
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  apply mul_left_cancel₀ hlog
  linarith

theorem vertAt_self_eq_intNum (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (p : Nat.Primes) (b : Fin D → K → ℤ) :
    (vertAt p P (C ((p : ℕ) : ℤ)) (List.ofFn b) : ℝ) = (intNum ℚ (extTo ℚ P) b : ℝ) := by
  classical
  have hlen : (List.ofFn b).length = D := by simp
  have hm := zp_model K ι P D hP p
  have f2 : IsMultiHomog (C ((p : ℕ) : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have nm2 : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    have := p.2.ne_zero
    simp_all
  rw [_root_.GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList K ι P D hP p 0 (C ((p : ℕ) : ℤ)) f2 nm2 (List.ofFn b) hlen]
  have hcy := _root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const (ZP p) (((p : ℕ) : ZP p)) hm.1 K ι (extTo (ZP p) P) D hm.2.1 1 1
    Empty Empty.elim 1 0 (MvPolynomial.isHomogeneous_one _ _) (List.ofFn b) (by simp)
  have hg := genNum_zp_eq_rat K ι P p Empty Empty.elim 1 (List.ofFn b)
  have hcN : ∀ Z : Ideal (MRing ι (ZP p)) → ℤ,
      cycNum Z (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) = (cycList Z (List.ofFn b) : ℝ) := by
    intro Z
    unfold cycNum
    simp [classList]
  have hgN : genNum ℚ (extTo ℚ P) (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) =
      (intNum ℚ (extTo ℚ P) b : ℝ) := by
    unfold genNum
    simp [classList, intNumL_ofFn_eq]
  rw [hcN, hg, hgN] at hcy
  have e : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      C (((1 : (ZP p)ˣ) : ZP p) * ((p : ℕ) : ZP p) ^ 1) := by
    simp
  rw [e, hcy]
  simp

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ptsIntegral_one_eq_intNum :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) = (intNum ℚ (extTo ℚ P) (fun j => (L j).a) : ℝ) := by
  intro K _ _ ι _ P D hP I hI L hL
  rw [GenInt.ptsIntegral_one_eq_vertAt P D hP I hI L hL]
  have h := GenInt.vertAt_self_eq_intNum P D hP ⟨2, Nat.prime_two⟩ (fun j => (L j).a)
  have e : (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℤ) = 2 := rfl
  rwa [e] at h

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SymmetricFormPolynomialCoeffStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_form_polynomial_coeff : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ), (∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) → ∀ (w₀ : Fin n → σ) (m : σ →₀ ℕ), (∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) → AddMonoidAlgebra.coeff (PB.formPoly n a) m * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul <;> assumption)
end

