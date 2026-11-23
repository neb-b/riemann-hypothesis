module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace LiftSpread

theorem exists_common {α : Type} [Fintype α] (Q : α → ℕ → Prop) (hQ : ∀ a n k, Q a n → Q a (k * n))
    (h : ∀ a, ∃ n, 1 ≤ n ∧ Q a n) : ∃ n, 1 ≤ n ∧ ∀ a, Q a n := by
  classical
  choose N hN1 hN using h
  refine ⟨∏ a, N a, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by
    have := hN1 a; omega), fun a => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hm, mul_comm]
  exact hQ a _ m (hN a)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem prod_zpow_nsmul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : ℕ) (a : K → ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(t • a) k) = ∏ _l : Fin t, ∏ k, y ⟨k, c k⟩ ^ (-a k) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem prod_mem_chartLat (y : (Σ k, ι k) → Ω) {σ : Type} (t : ℕ) (a : K → ℤ) (x : σ → Ω)
    (hx : ∀ j, x j ∈ chartLat y a 1) (f : Fin t → σ) : ∏ l, x (f l) ∈ chartLat y (t • a) 1 := by
  intro c hc
  have hW : ∀ j, x j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    have h := hx j c hc
    simpa only [Nat.cast_one, one_mul] using h
  simp only [Nat.cast_one, one_mul]
  rw [prod_zpow_nsmul, ← Finset.prod_mul_distrib]
  exact Subalgebra.prod_mem _ fun l _ => hW (f l)

end LiftSpread

theorem LiftSpread.proof : LiftSpread.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N _ hA
  classical
  obtain ⟨q, hq, hgen, -⟩ := hA
  obtain ⟨σ, _, s, hs, hrel⟩ := GenRead.exists_sections_of_generatedV (y := y) hgen

  obtain ⟨M, hM1, hM⟩ := LiftSpread.exists_common (fun j n => (n : Ω) * s j ∈ chartLat y (q • N) 1)
    (fun j n k h => by
      have e : ((k * n : ℕ) : Ω) * s j = k • ((n : Ω) * s j) := by
        rw [nsmul_eq_mul]; push_cast; ring
      rw [e]
      exact AddSubgroup.nsmul_mem _ h k)
    (fun j => ChartDenominator.proof K ι Ω y (q • N) 1 (s j) (hs j))

  have hrel' : ∀ c : ∀ k, ι k, ∃ v : σ → Ω, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ j, v j ∈ chartRingQ y c) ∧
      ∑ j, v j * (s j * ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k)) = 1 := fun c => by
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨v, hv⟩ := hrel c hc
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose v hv using hrel'
  obtain ⟨Δ, hΔ1, hΔ⟩ := LiftSpread.exists_common (α := (∀ k, ι k) × σ)
    (fun p n => (∀ k, y ⟨k, p.1 k⟩ ≠ 0) → (n : Ω) * v p.1 p.2 ∈ chartRingZ y p.1)
    (fun p n k h hc => by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ k) (h hc))
    (fun p => by
      by_cases hc : ∀ k, y ⟨k, p.1 k⟩ ≠ 0
      · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ ((hv p.1 hc).1 p.2)
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h => absurd h hc⟩)
  refine ⟨q, Δ * M, 0, hq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun t _ => ?_⟩

  let e := Fintype.equivFin (Fin t → σ)
  refine ⟨Fintype.card (Fin t → σ), fun i => ∏ l, (M : Ω) * s (e.symm i l), fun i => ?_, fun c hc => ?_⟩
  · rw [mul_smul]
    exact LiftSpread.prod_mem_chartLat y t (q • N) _ hM (e.symm i)
  · refine ⟨t, fun i => ∏ l, (Δ : Ω) * v c (e.symm i l), fun i => ?_, ?_⟩
    · exact Subalgebra.prod_mem _ fun l _ => hΔ (c, e.symm i l) hc
    · set w := ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k) with hw
      have hbase : ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = ((Δ * M : ℕ) : Ω) := by
        have h1 := (hv c hc).2
        calc ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = (Δ : Ω) * M * ∑ j, v c j * (s j * w) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = ((Δ * M : ℕ) : Ω) := by rw [h1]; push_cast; ring
      rw [e.symm.sum_comp (fun f : Fin t → σ =>
        (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
          ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)))]
      calc ∑ f : Fin t → σ, (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
            ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))
          = ∑ f : Fin t → σ, ∏ l, ((Δ : Ω) * v c (f l) * ((M : Ω) * s (f l) * w)) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [mul_smul, LiftSpread.prod_zpow_nsmul, ← hw, ← Finset.prod_mul_distrib,
              ← Finset.prod_mul_distrib]
        _ = (∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w)) ^ t := by
            rw [Finset.sum_pow', Fintype.piFinset_univ]
        _ = ((Δ * M : ℕ) : Ω) ^ t := by rw [hbase]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ChangeOfLattice

noncomputable section

namespace MetricTransportSmooth

theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

theorem proof : MetricTransportSmooth.Statement := by
  intro κ _ B m m' hB hm hm'
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  have hinv : ∀ w, matActC B (matActC B' w) = w := fun w => by
    rw [matActC_mul, hBB', matActC_one]
  have heq : ∀ w, m'.ρ w = m.ρ (matActC B' w) := fun w => by
    rw [← hm' (matActC B' w), hinv]
  have hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0} := fun w hw h0 => by
    apply hw
    rw [← hinv w, h0, matActC_zero]
  exact (hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w

end MetricTransportSmooth

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleiman
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanLow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanLow.exists_monomial {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (hP : P.IsPrime) (hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ (monomial μ 1 : MRing ι) ∉ P ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ 1 : MRing ι) a := by
  classical
  choose c hc using hrel
  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := fun k => by simp [μ]
  refine ⟨μ, hμ, fun hmem => ?_, fun m hm k => ?_⟩
  · rw [monomial_eq, map_one, one_mul, Finsupp.prod, hP.prod_mem_iff] at hmem
    obtain ⟨p, hp, hXp⟩ := hmem
    have hp2 : p.2 = c p.1 := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [μ, h])
    obtain ⟨k, i⟩ := p
    obtain rfl : i = c k := hp2
    exact hc k (hP.mem_of_pow_mem _ hXp)
  · rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    exact hμ k

theorem MixedKleimanLow.proof (hI : IntegralAgainstPositive.Statement)
    (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) : MixedKleimanLow.Statement := by
  classical
  intro d hd K _ ι _ P P0 M A a II hII h1 hP hP0 hMs hMn hMc hMW hAa hAs hAb hAc j hj
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hd
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => if (i : ℕ) < j then M else A
  have hsnoc : (fun i : Fin (n + 1) => if (i : ℕ) < j then M else A) = Fin.snoc L A := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, if_neg (by simp; omega)]
    · rw [Fin.snoc_castSucc]; rfl
  have hLs : ∀ i, IsSemipositiveRel P0 P (L i) := fun i => by
    simp only [L]; split_ifs <;> assumption
  obtain ⟨μ, hμ, hsP, hsh⟩ := MixedKleimanLow.exists_monomial P hP.2.1.1 hP.2.1.2.2 a
  have hAk : ∀ k, A.a k = a k := fun k => by rw [hAa]

  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz => ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  rw [hsnoc, (hII K ι).2.2 P n L A _ a hP (fun i => (hLs i).1) hAs.1 hAk hsh hsP]
  unfold recR
  refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW => ?_))
  ·
    refine hI K ι P P0 n L _ hP0 hLs fun z hz => ?_
    have hpos := A.pos z hz.1
    unfold logNorm
    refine Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).mpr ?_)
    rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact hAb z hz μ hμ
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n A _ W hP ⟨a, hAk, hsh, hsP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd hWv (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)
      exact hd K ι W P0 M A a II hII hn hWv (hP0.trans hPW)
        ⟨hMs.1, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) hAa ⟨hAs.1, fun z hz => hAs.2 z (hpts hPW hz)⟩
        (fun z hz => hAb z (hpts hPW hz)) hAc j (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun i => (L i).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun i => ?_
        intro W' h1 h2 h3
        simp only [L]
        split_ifs
        · exact hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        · rw [hAa]
          exact ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by positivity) W' h1 le_rfl (hchar W W' h2 hc) h3
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanTop.proof (hFS : ScaledFSHProps.Statement) (hE : ZCombExpand.Statement)
    (hSec : MixedSectionStep.Statement) (hH : ScaledFSTopPos.Statement) (hA : MixedTopAlgebra.Statement) :
    MixedKleimanTop.Statement := by
  intro d hd hAt hLow K _ ι _ P P0 M II hII h1 hP h0 hsM hnM hcM hhM
  obtain ⟨hsH, hcH, hmH⟩ := hFS K ι P P0
  have haH : (scaledFSH ι).a = fun k => (((fun _ => 1 : K → ℕ) k : ℕ) : ℤ) := by
    rw [scaledFSH_a]; rfl
  have e0 : II K ι P d (fun _ => M) =
      (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) 0 := by
    simp
  rw [e0]
  refine hA d (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) hd
    (fun i hi1 hid => hLow K ι P P0 M (scaledFSH ι) (fun _ => 1) II hII h1 hP h0 hsM hnM hcM hhM haH hsH hmH hcH
      (d - i) (by omega)) ?_ ?_
  · simpa using hH K ι P d II hII h1 hP
  · intro q p _ hp hpos
    obtain ⟨e1, e2⟩ := hE K ι (II K ι) (hII K ι) P d M (scaledFSH ι) q p hP hsM.1 hsH.1
    rw [← e2 h1]
    exact hSec K ι P P0 d M (scaledFSH ι) II hII hd hP h0 hsM hnM hcM hhM (scaledFSH_a ι) hsH hmH hcH hAt q p hp
      (by rw [e1]; exact hpos)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]




theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

end PieceDegreeAlt

open PieceDegreeAlt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  set_option synthInstance.maxHeartbeats 200000 in
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage


open ProjFrameImage in
theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurveSmallCountLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def CurveSmallCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    IsSmoothHerm A → IsConjInvariantH A →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n

namespace CurveSmallCountLower

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end CurveSmallCountLower

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

