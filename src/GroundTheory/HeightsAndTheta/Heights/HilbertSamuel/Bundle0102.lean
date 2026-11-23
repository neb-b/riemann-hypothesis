module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormGoodPrimeIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormGoodPrimeIntegral.proof (hN : PullConeNullModP.Statement) (hD : PullConeDegreeInt.Statement)
    (hI : PullSectionIntegralInt.Statement) (hP : DehomNormPIntegral.Statement) :
    FibreNormGoodPrimeIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz p hp hgood τ s hs j c hc μ
  classical
  obtain ⟨N, M, hpM, hrel⟩ := hN K ι Ω y D L hz p hp hgood
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    obtain ⟨_, ⟨_, _, hrv⟩, _, _⟩ := hA
    obtain ⟨c', hc'⟩ := CoordArithOfFnField.nonzero_of_relevant y hrv
    exact fun k => ⟨c' k, hc' k⟩
  have hM : (M : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hpM (dvd_zero p))
  obtain ⟨hj, hfin, -, hch, hcp⟩ := hc
  have := hfin
  have hint := hI K ι Ω y D e L q N M hy he hL hM (hD K ι Ω y D e L N M hy hL hrel) τ s hs j hj
  have hgen := PullFormsGeneric.proof
    (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof)
    K ι Ω y D e L hA hB he hL hz
  exact hP Ω D (fun i => aeval y (L i)) (pullField y L) rfl hgen p hp M hpM j (q * τ) _ hint c
    (hch _ le_rfl) hcp μ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace MonomialShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hY : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hrel := hY.2.1.2.2
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem norm_prod_le {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {a : K → ℕ} (hM : MonomialsBounded P A a)
    (c : ∀ k, ι k) (j n : ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ ≤ A.h z ^ j * (fsH ι).h z ^ n := by
  classical
  have e1 : ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) ^ j * (∏ k, ‖z ⟨k, c k⟩‖) ^ n := by
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow]
    ring

  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := by
    intro k
    simp [μ]
  have hmon : ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [μ, pow_ite]
  have hA : ∏ k, ‖z ⟨k, c k⟩‖ ^ a k ≤ A.h z := by
    have := hM z hz μ hμ
    rw [hmon, norm_prod] at this
    simpa [norm_pow] using this
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  rw [e1]
  gcongr
  exact pow_nonneg (A.pos z hz.1).le _

theorem isSmoothHerm_zcomb_fsH {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A (fsH ι) q 1) := by
  have hH : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hfun : (HermLine.zcomb A (fsH ι) q 1).h = fun z => A.h z ^ q * (fsH ι).h z := by
    funext z
    change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) = _
    rw [zpow_natCast, zpow_one]
  unfold IsSmoothHerm at hA hH ⊢
  rw [hfun]
  exact (hA.pow q).mul hH

theorem proof (hPack : PackingStatement) : MonomialShift.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q τ n hY hBir ha hP0 hsemi hM hq hτ
  classical
  obtain ⟨c, hc⟩ := exists_chart hY

  obtain ⟨e, he⟩ : ∃ e : K → ℕ, e = fun k => (q * n - τ) * a k + n := ⟨_, rfl⟩
  have hBa : ∀ k, (HermLine.zcomb A (fsH ι) q 1).a k = (q : ℤ) * a k + 1 := by
    intro k
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, ha]
  have hdeg : ∀ k, (n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k = τ * A.a k + e k := by
    intro k
    rw [hBa, he]
    simp only [ha]
    push_cast [Nat.cast_sub hτ]
    ring

  obtain ⟨mv, hmv⟩ : ∃ mv : Ω, mv = ∏ k, y ⟨k, c k⟩ ^ e k := ⟨_, rfl⟩
  have hmv0 : mv ≠ 0 := by
    rw [hmv]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hmvx : aeval y (xpow c e) = mv := by
    simp [hmv, xpow]

  have hlat : ∀ s ∈ chartLatNm y A.a τ, mv * s ∈ chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n := by
    intro s hs c' hc'
    have h1 := hs c' hc'
    have h2 : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ integralClosure (chartRingZ y c') Ω := by
      have hmem : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ chartRingZ y c' :=
        Subalgebra.prod_mem _ fun k _ =>
          pow_mem (Algebra.subset_adjoin
            (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩) ⟨k, c k⟩)) _
      exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem⟩
    have hsplit : ∀ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k)) * (y ⟨k, c' k⟩ ^ e k)⁻¹ := by
      intro k
      rw [hdeg k, neg_add, zpow_add₀ (hc' k), zpow_neg (y _) ((e k : ℕ) : ℤ), zpow_natCast]
    have key : mv * s * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k := by
      simp only [hsplit, div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmv]
      ring
    rw [key]
    exact mul_mem h1 h2

  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (mv * s) := by
    intro s hs dg dh g h z hg hh hd hgh hz
    have hmh := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_xpow c e) hh
    have hb := hs dg (e + dh) g (xpow c e * h) z hg hmh
      (fun k => by have := hd k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith)
      (by rw [hgh, map_mul, hmvx]; ring) hz
    have hApos : 0 < A.h z := A.pos z hz.1
    have hxz : eval z (map (Int.castRingHom ℂ) (xpow c e)) = ∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n) := by
      simp [xpow, he]
    have hBh : (HermLine.zcomb A (fsH ι) q 1).h z = A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) := rfl
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) (xpow c e * h))‖ * A.h z ^ τ := hb
      _ = ‖∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          rw [map_mul, eval_mul, norm_mul, hxz]
      _ ≤ (A.h z ^ (q * n - τ) * (fsH ι).h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          gcongr
          exact norm_prod_le hM c (q * n - τ) n hz
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (HermLine.zcomb A (fsH ι) q 1).h z ^ n := by
          rw [hBh, zpow_natCast, zpow_one, mul_pow, ← pow_mul,
            show A.h z ^ (q * n) = A.h z ^ (q * n - τ) * A.h z ^ τ by rw [← pow_add, Nat.sub_add_cancel hτ]]
          ring

  let f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
      {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} :=
    fun s => ⟨⟨mv * s.1, hlat s.1 s.1.2⟩, hsmall s.1 s.2⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h := congrArg (fun u => ((u.1 : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hmv0 h))
  have hfin := (hPack K ι Ω y D (HermLine.zcomb A (fsH ι) q 1)
    (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) hY hBir (isSmoothHerm_zcomb_fsH hsemi.1 q)
    (fun _ => le_rfl)).1 n
  have : Finite {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} := hfin.to_subtype
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end MonomialShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefPlusAmpleDegree

theorem genDeg_one_pos (hA : GenDegAmple.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    0 < genDeg W d 1 := by
  have : W.IsPrime := hW.2.1.1
  have hEq := CurvePointsFinite.mCoordIdeal_genericPt W hW.2.1.2.1
  have hV : IsArithVar (mCoordIdeal (CurvePointsFinite.genericPt W)) (d + 1) := by rw [hEq]; exact hW
  have h := hA K ι _ (CurvePointsFinite.genericPt W) d 1 hV fun _ => le_rfl
  rwa [hEq] at h


open Classical in
theorem nefOnF_of_nefOnGenericDeg {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {b : K → ℤ} (hb : NefOnGenericDeg P b) :
    KH.NefOnF (fun V _ L => NumbersDVR.intNum ℚ V L) (P.map (MvPolynomial.map (Int.castRingHom ℚ))) b := by
  intro W hW hle
  obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
  have hPW : P ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) := Ideal.map_le_iff_le_comap.mp hle
  have h := hb _ hWar hPW
  rw [genDeg, hWmap] at h
  have hL : (fun _ : Fin 1 => b) = ![b] := by
    funext j
    fin_cases j
    rfl
  rw [hL] at h
  exact h

end NefPlusAmpleDegree

theorem NefPlusAmpleDegree.proof (hK : KH.KleimanNefFStatement) (hA : GenDegAmple.Statement) :
    NefPlusAmpleDegree.Statement := by
  classical
  intro K _ ι _ P D a hP hnef q
  have : Nonempty K := hP.1
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  obtain ⟨hprime, hdimq⟩ := ShiftDegreePolynomial.genericFibre hP
  have hd : FieldNumbers.relDim Q = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hdimq]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let f : (Fin D → K → ℤ) → ℤ := fun bs => NumbersDVR.intNum ℚ Q bs
  have hadd : ∀ (bs : Fin D → K → ℤ) (j : Fin D) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y) :=
    fun bs j x y => FieldNumbers.IntNumAdd.full ℚ K ι Q hprime.multiHomog hprime.relevant D hd bs j x y
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hPV : IsProjVarF Q D := isProjVarF_map_of_isArithVar hP
  have hnefA : KH.NefOnF I Q a := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hnef
  have hnefH : KH.NefOnF I Q 1 := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg fun W hW _ =>
    (NefPlusAmpleDegree.genDeg_one_pos hA hW).le
  have hterm : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) (fun _ => 1)) := by
    intro s
    refine hK ℚ K ι I Q D _ hI hPV fun i => ?_
    by_cases hi : i ∈ s
    · simpa [Finset.piecewise, hi] using hnefA
    · simpa [Finset.piecewise, hi] using hnefH
  have hg : genDeg P D ((q : ℤ) • a + 1) = f (fun _ => (q : ℤ) • a + 1) := rfl
  rw [hg, ShiftDegreePolynomial.expand f hadd (q : ℤ) a 1]
  refine Finset.sum_pos' (fun s _ => mul_nonneg (pow_nonneg (Int.natCast_nonneg q) _) (hterm s))
    ⟨∅, Finset.mem_univ _, ?_⟩
  rw [Finset.card_empty, pow_zero, one_mul, Finset.piecewise_empty]
  exact NefPlusAmpleDegree.genDeg_one_pos hA hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegralInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegralInt

theorem aeval_mem_of_forall {σ Ω : Type} [Field Ω] (V : Subring Ω) (y' : σ → Ω) (hy : ∀ p, y' p ∈ V)
    (b : MvPolynomial σ ℤ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _)]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegralInt.Statement := by
  intro K _ ι _ Ω _ y D e L q N M hrel he hL hM hdeg τ s hs j hj
  classical
  set ℓ := aeval y (L j)
  set B := Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / ℓ))
  set R := (integralClosure B Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure B Ω) Ω)
  show s / ℓ ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hBV : ∀ x ∈ B, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := B) (A := Ω) (x := ⟨x, hx⟩))

  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set Mc : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hMc0 : Mc ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (Mc ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set w := N * ∑ k, Fintype.card (ι k)
  have hd : ∀ k, e k + N * Fintype.card (ι k) ≤ ((w + 1) • e) k := by
    intro k
    have h1 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : N * Fintype.card (ι k) ≤ w := Nat.mul_le_mul_left N h1
    have h3 : w ≤ w * e k := Nat.le_mul_of_pos_right w (he k)
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  obtain ⟨a, ha, hrelM⟩ := hdeg ((w + 1) • e) (xpow c ((w + 1) • e)) (isMultiHomog_xpow c _) hd
  have ha' : ∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a i) (fun k => w * e k) := by
    intro i
    convert ha i using 1
    ext k
    simp [Pi.smul_apply, smul_eq_mul, add_mul]
  have hg : aeval y (xpow c ((w + 1) • e)) = Mc ^ (w + 1) := by
    simp only [xpow, map_prod, map_pow, aeval_X, Mc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hscale : ∀ i, aeval (fun p => t p.1 * y p) (a i) = (Mc ^ w)⁻¹ * aeval y (a i) := by
    intro i
    rw [PullSectionIntegral.aeval_scale_of_isMultiHomog y t (ha' i)]
    congr 1
    simp only [Mc, t, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← pow_mul, mul_comm]

  have hsum : Mc / ℓ = (M : Ω)⁻¹ * ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) := by
    have : ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) =
        (Mc ^ w)⁻¹ * (∑ i, aeval y (a i) * aeval y (L i)) / ℓ := by
      simp only [hscale, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, ← hrelM, hg]
    field_simp
    ring
  have hMV : Mc / ℓ ∈ V := by
    rw [hsum]
    refine mul_mem (hBV _ (Algebra.subset_adjoin (Set.mem_insert _ _))) (sum_mem fun i _ => mul_mem ?_ ?_)
    · exact aeval_mem_of_forall V.toSubring _ (fun p => by simpa [t, div_eq_inv_mul] using hratio p) (a i)
    · exact hBV _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  apply htV
  have hMn : Mc ^ (q * τ) ≠ 0 := pow_ne_zero _ hMc0
  have : s / ℓ ^ (q * τ) = s * (Mc ^ (q * τ))⁻¹ * (Mc / ℓ) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegralInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

