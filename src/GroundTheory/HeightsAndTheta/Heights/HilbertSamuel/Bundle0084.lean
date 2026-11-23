module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix

noncomputable section

namespace SupBoundCount

theorem main {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f)
    {r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ} (hb : IsSecBasisM d.y d.k₀ n b) :
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      -(1 / 2) * Real.log (blockGram d n b).det - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n := by
  classical
  rw [finrank_secM hb]
  have hb' := hb
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb'.2.1
    simpa [aeval_map_int] using this
  have hG := gram_posDef d n f hf hli hc hsup
  refine ⟨rank_le d n f hf hli hc hsup, ?_⟩

  set Q : (Fin r → ℤ) → ℝ := fun m => (fun k => (m k : ℝ)) ⬝ᵥ
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)) with hQ
  set P : (Fin r → ℤ) → Prop := fun m =>
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y (∑ k, m k • f k)) with hPdef
  have hP1 : ∀ m, Q m ≤ (1 / c) ^ 2 → P m := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    refine (isSmallH_iff d n hF).2 fun z hz => ?_
    have h1 := hsup _ hF z hz
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    have h2 : Real.sqrt (Q m) ≤ 1 / c := by
      calc Real.sqrt (Q m) ≤ Real.sqrt ((1 / c) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / c := Real.sqrt_sq (by positivity)
    have h3 : c * Real.sqrt (Q m) ≤ 1 := by
      calc c * Real.sqrt (Q m) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 := by field_simp
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    exact (div_le_one hp).1 (h1.trans h3)
  have hP2 : ∀ m, P m → Q m ≤ 1 := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    have h1 := blockL2Norm_le_one_of_sup_bound d n hF ((isSmallH_iff d n hF).1 hm)
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    by_contra h
    push_neg at h
    have := Real.sqrt_lt_sqrt zero_le_one h
    rw [Real.sqrt_one] at this
    linarith
  obtain ⟨-, hcount⟩ := count_of_gram hG (by positivity : (0 : ℝ) < 1 / c) P hP1 hP2

  have hmem : ∀ m : Fin r → ℤ, aeval d.y (∑ k, m k • f k) ∈ secM d.y (blockDeg d.k₀ n) := by
    intro m
    rw [← hb'.2.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, by simp [aeval_map_int]⟩)
  have hinj : Function.Injective fun m : Fin r → ℤ => aeval d.y (∑ k, m k • f k) := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • aeval d.y (f k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul] at h
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)
  let E : {m // P m} → {s : secM d.y (blockDeg d.k₀ n) // IsSmallH (mCoordIdeal d.y) d.y d.A n (s : Ω)} :=
    fun m => ⟨⟨_, hmem m.1⟩, m.2⟩
  have hE : Function.Bijective E := by
    refine ⟨fun m m' h => Subtype.ext (hinj (congrArg (fun s => ((s.1 : secM d.y _) : Ω)) h)), ?_⟩
    rintro ⟨⟨s, hs⟩, hsm⟩
    have hs' := hs
    rw [← hb'.2.2] at hs'
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hs'
    have hms : aeval d.y (∑ k, m k • f k) = s := by
      rw [← hm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, aeval_map_int]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · show IsSmallH _ _ _ _ _
      rw [hms]
      exact hsm
    · exact Subtype.ext (Subtype.ext hms)
  have hcard := Nat.card_congr (Equiv.ofBijective E hE)
  simp only [smallSectionCount]
  rw [← hcard]

  have hV : (r : ℝ) * Real.log (2 / Real.sqrt r) ≤ Real.log (unitBallVolume r) := by
    have hpos : 0 < (2 / Real.sqrt r) ^ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact pow_pos (div_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))) r
    rw [← Real.log_pow]
    exact Real.log_le_log hpos (MinkowskiCount.cube_le_unitBallVolume r)
  have halg : (r : ℝ) * Real.log (2 / Real.sqrt r) + r * Real.log (1 / c / 2) =
      -((r : ℝ) * Real.log (c * Real.sqrt r)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast h0)
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      have : 2 / Real.sqrt r * (1 / c / 2) = (c * Real.sqrt r)⁻¹ := by
        field_simp
      rw [this, Real.log_inv]
      ring
  linarith

end SupBoundCount

theorem SupBoundCount.proof : SupBoundCount.Statement := by
  intro D K _ _ ι _ Ω _ _ d n c hc hsup
  have hex := SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  have h := SupBoundCount.main d n hc hsup hex.choose_spec
  refine ⟨h.1, ?_⟩
  rw [blockChi, dite_eq_left hex]
  exact h.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockModuleCycleAlt

section General

variable {K : Type} {ι : K → Type} {τ : Type}

theorem mem_minimalPrimes_iff_of {R : Type*} [CommRing R] {J J' W : Ideal R} (hJ : J ≤ J')
    (key : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → J ≤ Q → J' ≤ Q) :
    W ∈ J.minimalPrimes ↔ W ∈ J'.minimalPrimes := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, key W h.1.1 le_rfl h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, hJ.trans hQ.2⟩ hQW⟩
  · intro h
    exact ⟨⟨h.1.1, hJ.trans h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, key Q hQ.1 hQW hQ.2⟩ hQW⟩

theorem sup_range_le {R : Type*} [CommRing R] (P : Ideal R) (s : R) (v : τ → R) :
    P ⊔ Ideal.span (Set.range fun j => s * v j) ≤ P ⊔ Ideal.span {s} := by
  refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem mul_mem_sup_range {R : Type*} [CommRing R] {P : Ideal R} {s : R} {v : τ → R} (i : τ) {y : R}
    (hy : y ∈ P ⊔ Ideal.span {s}) : v i * y ∈ P ⊔ Ideal.span (Set.range fun j => s * v j) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hp)) (Ideal.mem_sup_right ?_)
  have e : v i * (t * s) = t * (s * v i) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem multAt_sup_range_eq {P W : Ideal (MRing ι)} {s : MRing ι} {v : τ → MRing ι} (hW : W.IsPrime) {i : τ}
    (hi : v i ∉ W) : multAt (P ⊔ Ideal.span (Set.range fun j => s * v j)) W = multAt (P ⊔ Ideal.span {s}) W := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW, GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedQuot_eq_of_mul_le
    (sup_range_le P s v) hi (fun y hy => mul_mem_sup_range i hy)]

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, Module.length_eq_zero_iff.mpr
    (GroundTheory.Heights₂.Heights.NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem log_charOf_of_horizontal {W : Ideal (MRing ι)} (h : IsHorizontal W) : Real.log (charOf W) = 0 := by
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h
  simp [charOf, hg]


open Classical in
theorem vert_weight_eq (W : Ideal (MRing ι)) (g : ℤ) :
    (if IsHorizontal W then 0 else (g : ℝ) * Real.log (charOf W)) = Real.log (charOf W) * g := by
  split_ifs with h
  · rw [log_charOf_of_horizontal h, zero_mul]
  · ring

end General

section TwoBlock

variable {Ω : Type} [Field Ω] {κ : Type}

theorem mem_twoBlockIdeal {x x' : Ix κ → Ω} {f : MRing (FinTwoTypeFamily κ)} :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (ι := FinTwoTypeFamily κ) (pair x x') f = 0 :=
  RingHom.mem_ker

theorem mConeMap_X_zero (x x' : Ix κ → Ω) (i : κ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (X ⟨0, i⟩) = MvPolynomial.C (x ⟨(), i⟩) * MvPolynomial.X 0 := by
  simp [mConeMap, pair]

theorem mConeMap_num [Fintype κ] (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (twoBlockNum l) =
      MvPolynomial.C (∑ j, (l j : Ω) * x' j) * MvPolynomial.X 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [twoBlockNum, mConeMap, pair, Finset.sum_mul, mul_assoc, map_sum]

theorem rel_mem [Fintype κ] (x x' : Ix κ → Ω) (c : κ) (l m : Ix κ → ℤ) (i : κ)
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j) (hm : x ⟨(), i⟩ = ∑ j, (m j : Ω) * x' j) :
    X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum m ∈ twoBlockIdeal x x' := by
  rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, mConeMap_num, mConeMap_num, twoBlockDen,
    mConeMap_X_zero, mConeMap_X_zero, ← hl, ← hm]
  ring

end TwoBlock

end TwoBlockModuleCycleAlt


open TwoBlockModuleCycleAlt in
theorem TwoBlockModuleCycle.proof : TwoBlockModuleCycle.Statement := by
  classical
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl e

  obtain ⟨hFp, -⟩ := TwoBlockFnField.proof Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hX
  have hxc : x ⟨(), c⟩ ≠ 0 := hx.ne_zero _
  have hx0 : x ≠ 0 := fun h => hxc (by rw [h]; rfl)
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    CoordArithOfFnField.proof Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hPp : (twoBlockIdeal x (matAct B x)).IsPrime := hpA.2.1.1
  have hdim := hpA.2.2.2

  have hnumP : twoBlockNum l ∉ twoBlockIdeal x (matAct B x) := by
    rw [mem_twoBlockIdeal, mConeMap_num, ← hl]
    simp [hxc]

  have hm : ∀ i : κ, ∃ m : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (m j : Ω) * matAct B x j := by
    intro i
    have h := hsp (Submodule.subset_span ⟨⟨(), i⟩, rfl⟩)
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨m, by rw [← hm]; simp [zsmul_eq_mul]⟩
  choose m hm using hm

  have hden_num : ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → twoBlockIdeal x (matAct B x) ≤ Q →
      (∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q) → twoBlockDen c ∈ Q → twoBlockNum l ∈ Q := by
    rintro Q hQ hPQ ⟨i, hi⟩ hd
    have h1 := hPQ (rel_mem x (matAct B x) c l (m i) i hl (hm i))
    have h2 : X ⟨0, i⟩ * twoBlockNum l ∈ Q := by
      have e : X ⟨0, i⟩ * twoBlockNum l =
          (X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum (m i)) + twoBlockDen c * twoBlockNum (m i) := by
        ring
      rw [e]
      exact Q.add_mem h1 (Q.mul_mem_right _ hd)
    exact (hQ.mem_or_mem h2).resolve_left hi

  have hmin : ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
      (W ∈ (twoBlockMInner x (matAct B x) l).minimalPrimes ↔
        W ∈ (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}).minimalPrimes) := by
    intro W hrel
    refine mem_minimalPrimes_iff_of (sup_range_le _ _ _) fun Q hQ hQW hJQ => ?_
    obtain ⟨i, hi⟩ := hrel 0
    have hiQ : (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := fun h => hi (hQW h)
    have hn : twoBlockNum l * X ⟨0, i⟩ ∈ Q :=
      hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    exact sup_le (le_sup_left.trans hJQ)
      ((Ideal.span_singleton_le_iff_mem _).mpr ((hQ.mem_or_mem hn).resolve_right hiQ))
  have hT : topComps (twoBlockMInner x (matAct B x) l) D = divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    ext W
    constructor
    · rintro ⟨hW, hrel, -⟩
      exact ⟨(hmin W hrel).mp hW, hrel⟩
    · rintro ⟨hW, hrel⟩
      exact ⟨(hmin W hrel).mpr hW, hrel, dim_of_minimal hnumP hW hdim⟩

  have hsub : divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) ⊆
      divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    rintro W ⟨hW, hrel⟩
    have hWp : W.IsPrime := hW.1.1
    have hPW : twoBlockIdeal x (matAct B x) ≤ W := le_sup_left.trans hW.1.2
    have hdW : twoBlockDen c ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnW := hden_num W hWp hPW (hrel 0) hdW
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hnW))
    have hQeq : Q = W := ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes hPp hW hQ.1.1
      (le_sup_left.trans hQ.1.2) (hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hnumP hQW
    exact ⟨hQeq ▸ hQ, hrel⟩

  have hback : ∀ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l), twoBlockDen c ∈ W →
      W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) := by
    rintro W ⟨hW, hrel⟩ hdW
    refine ⟨⟨⟨hW.1.1, sup_le (le_sup_left.trans hW.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hdW)⟩,
      fun Q hQ hQW => hW.2 ⟨hQ.1, ?_⟩ hQW⟩, hrel⟩
    have hPQ := le_sup_left.trans hQ.2
    have hrQ : ∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := by
      obtain ⟨i, hi⟩ := hrel 0
      exact ⟨i, fun h => hi (hQW h)⟩
    exact sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr
      (hden_num Q hQ.1 hPQ hrQ (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))))

  rw [hT]
  unfold twoBlockVert vertCycleNum
  have hfin := divSupp_finite (twoBlockIdeal x (matAct B x)) (twoBlockNum l)
  have hden_sum :
      ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) =
        ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) := by
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => hsub h, fun h => hback W h ?_⟩
    by_contra hd
    apply hW
    show (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * _ = 0
    rw [multAt_eq_zero_of_not_le h.1.1.1 fun hle =>
      hd (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))]
    simp
  rw [hden_sum, ← finsum_mem_sub_distrib _ _ hfin]
  refine finsum_mem_congr rfl fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 0
  obtain ⟨j, hj⟩ := hW.2 1
  have h1 : multAt (twoBlockMInner x (matAct B x) l) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W :=
    multAt_sup_range_eq (s := twoBlockNum l) (v := fun i : κ => (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hi
  have h2 : multAt (twoBlockMOuter x (matAct B x) c) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W :=
    multAt_sup_range_eq (s := twoBlockDen c) (v := fun j : κ => (X ⟨1, j⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hj
  rw [h1, h2, vert_weight_eq]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.ptsIntegral_curve_const (W : Ideal (MRing ι)) (hW1 : IsArithVar W 1)
    (hfin : Finite (GroundTheory.Heights₂.Heights.projPts W)) (c : ℝ) :
    ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) = c * degC W := by
  have : Nonempty K := hW1.1
  have hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0 := Subsingleton.elim _ _
  have hpts := GroundTheory.Heights₂.Heights.PtsIntegralPoints.homogProof K ι W (fun _ => c) hW1.2.1.2.1 hfin
    (fun _ _ _ _ => rfl)
  rw [hpot, hpts]
  letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]
  ring

theorem G5.proof' (hK : ArithKleiman.Statement) (hF : CurvePointsFinite.Statement) : G5.Statement := by
  intro K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW
  set A' := A.tensor (constLine (ι := ι) e) with hA'def
  have hA : IsSmoothHerm A := hsemi.1
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine e)
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hsemi' : IsSemipositiveRel P0 P A' := by
    refine ⟨hA', fun z hz w hw => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e :=
      (show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' =>
        G5.log_tensor_constLine A e z' hz'
    have : leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
      unfold leviForm
      rw [G5.fderiv_fderiv_eq_of_add_const (-e) hev]
    rw [this]
    exact hsemi.2 z hz w hw
  have ha : A'.a = A.a := by
    show A.a + 0 = A.a
    rw [add_zero]
  have hnef' : NefOnFibres P A'.a := ha ▸ hnef
  have hconj' : IsConjInvariantH A' := fun z => by
    show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)
    rw [hconj z]
  have hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A'] := by
    intro W hW1 hPW
    have hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] := by
      intro B
      funext j
      fin_cases j
      rfl
    have hmc := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1
      (fun j => j.elim0) hA contDiffOn_const
    rw [hsn, hsn] at hmc
    have hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W := by
      rw [← G5.ptsIntegral_curve_const W hW1 (hF K ι W hW1) e]
      exact hmc
    rw [hA'W]
    linarith [hW W hW1 hPW]
  have hkl := hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'
  have htop := G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA
  rw [← hA'def] at htop
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartNakayamaGen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartNakayamaGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → P.IsPrime → IsMultiHomogIdeal P →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    (∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d) →
    ∃ (f : MRingOver S ι) (δ : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧ GenNear S ι 𝓜 d f δ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

