module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0029
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_of_vd_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, u, -, hb, hH, hu, hunit⟩ := OrthogonalBases.exists_orth_basis hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv
  exact IsotropicCounts.alphaL_eq_of_bridge hK h𝔭 u hu hunit fun k => integralBasisSpans.akCount_eq h h𝔭 b hb hH k

theorem alphaStd_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (m : ℕ) : 0 < alphaStd K 𝔭 m := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (1 : ℝ) < Ideal.absNorm 𝔭 := by
    have : 1 < Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  unfold alphaStd
  apply Finset.prod_pos
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hN (by omega)
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by linarith) _
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h]
  · rw [one_pow, one_mul]
    linarith
  · rcases neg_one_pow_eq_or ℝ j with h' | h' <;> rw [h'] <;> linarith

theorem localMassFactor_of_valuation_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : lamP h L 𝔭 = 1 := by
  unfold lamP
  rw [hv, mul_zero, pow_zero, mul_one, alphaL_of_vd_zero hK hF hs hd hL hLi h𝔭 hv]
  exact div_self (alphaStd_pos hK hF h𝔭 _).ne'

theorem lamG_eq_one_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) : lamG F h I = 1 := by
  unfold lamG
  have hd := isTotPosDef_of_ortho hK hs hI
  have hL := isFullLattice_of_ortho hI
  have hLi := isIntegralLat_of_ortho hI
  have : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h I 𝔭.1 = 1 := by
    intro 𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2
    rw [← hP𝔭]
    exact (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mp (isUnimodularAt_of_ortho hK hs hI P hP)
  simp only [this, tprod_one]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoBallCount
section
open NumberField Module Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  have hB : Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
    { toIsLattice := BallB.isLattice_span b
      span_eq_top := by
        apply top_unique
        rw [← b.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL.toIsLattice hB
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumOfMean
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

private theorem abs_prod_sub_prod_le_of_bounded_differences {ι : Type*} (S : Finset ι) (x y C d : ι → ℝ)
    (hx : ∀ i ∈ S, |x i| ≤ C i) (hy : ∀ i ∈ S, |y i| ≤ C i)
    (hd : ∀ i ∈ S, x i ≠ y i → 1 ≤ d i) (hd0 : ∀ i ∈ S, 0 ≤ d i) :
    |∏ i ∈ S, x i - ∏ i ∈ S, y i| ≤ 2 * (∏ i ∈ S, C i) * ∑ i ∈ S, d i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Finset.prod_insert hp, Finset.sum_insert hp]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)) (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)) (fun i hi => hd0 i (Finset.mem_insert_of_mem hi))
    have hxp := hx p (Finset.mem_insert_self p s)
    have hyp := hy p (Finset.mem_insert_self p s)
    have hdp := hd0 p (Finset.mem_insert_self p s)
    have hCp : 0 ≤ C p := le_trans (abs_nonneg _) hxp
    have hys : |∏ i ∈ s, y i| ≤ ∏ i ∈ s, C i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hdiff : |x p - y p| ≤ 2 * C p * d p := by
      by_cases h : x p = y p
      · rw [h, sub_self, abs_zero]
        exact mul_nonneg (by linarith) hdp
      · have h1 := hd p (Finset.mem_insert_self p s) h
        have h2 : |x p - y p| ≤ 2 * C p := by
          rw [abs_le] at hxp hyp ⊢
          constructor <;> linarith
        calc |x p - y p| ≤ 2 * C p := h2
          _ ≤ 2 * C p * d p := le_mul_of_one_le_right (by linarith) h1
    calc |x p * ∏ i ∈ s, x i - y p * ∏ i ∈ s, y i|
        = |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x p - y p) * ∏ i ∈ s, y i| := by
          congr 1
          ring
      _ ≤ |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i)| + |(x p - y p) * ∏ i ∈ s, y i| := abs_add_le _ _
      _ = |x p| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x p - y p| * |∏ i ∈ s, y i| := by
          rw [abs_mul, abs_mul]
      _ ≤ C p * (2 * (∏ i ∈ s, C i) * ∑ i ∈ s, d i) + (2 * C p * d p) * ∏ i ∈ s, C i :=
          add_le_add (mul_le_mul hxp ih' (abs_nonneg _) hCp)
            (mul_le_mul hdiff hys (abs_nonneg _) (mul_nonneg (by linarith) hdp))
      _ = 2 * (C p * ∏ i ∈ s, C i) * (d p + ∑ i ∈ s, d i) := by ring

theorem abs_prod_sub_le (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (k : ℕ) {n : 𝓞 F} (hn : n ≠ 0) :
    |∏ 𝔭 ∈ S, a 𝔭 n - ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0) := by
  refine abs_prod_sub_prod_le_of_bounded_differences S _ _ C _ (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 n) (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 _) (fun 𝔭 h𝔭 hne => ?_)
    (fun 𝔭 _ => by split_ifs <;> norm_num)
  by_contra hlt
  have hni : n ∉ 𝔭.1 ^ (k + 1 - c 𝔭) := by
    intro hm
    rw [ite_eq_left hm] at hlt
    exact hlt le_rfl
  have hv := BoxSum.vF_lt_of_notMem hni
  have hk : vF 𝔭.1 n + c 𝔭 ≤ k := by omega
  apply hne
  refine hcg 𝔭 h𝔭 n _ k hn hk ?_
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

theorem tendsto_err (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (A B : ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) :
    Tendsto (fun k : ℕ => A * ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop
      (𝓝 (∑ 𝔭 ∈ S, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun 𝔭 _ => ?_
    have hne : 𝔭.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
    have h1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h2 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
    have hgt : (1 : ℝ) < Ideal.absNorm 𝔭.1 := by
      have : 1 < Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop_atTop_of_one_lt hgt).comp
      ((tendsto_sub_atTop_nat (c 𝔭)).comp (tendsto_add_atTop_nat 1))
  simpa using h0.const_mul A

private theorem finsum_boxSet_inf_eq_sum_ite_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (b I : Ideal (𝓞 F))
    (g : 𝓞 F → ℝ) (hb : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}, g n =
      ∑ n ∈ hb.toFinset, if n ∈ I then g n else 0 := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}.Finite := finite_box_inter hK hF T _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq, Submodule.mem_inf]
  tauto

private theorem local_density_error_le_of_bounded_congruent (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (b : Ideal (𝓞 F)) (T w : ℝ) (hw : 0 ≤ w) (k : ℕ) :
    |w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
      w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite := finite_box_inter hK hF T _
  simp_rw [finsum_boxSet_inf_eq_sum_ite_mem hK hF T b _ _ hfin]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hw]
  have hWn : ∀ n : 𝓞 F, 0 ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := fun n => by positivity
  calc w * |∑ n ∈ hfin.toFinset, ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))|
      ≤ w * ∑ n ∈ hfin.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0)) := by
        refine mul_le_mul_of_nonneg_left (le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun n hn => ?_)) hw
        rw [← mul_sub, abs_mul, abs_of_nonneg (hWn n)]
        exact mul_le_mul_of_nonneg_left (abs_prod_sub_le S a C c hbd hcg k
          (ne_zero_of_mem_boxSet (hfin.mem_toFinset.1 hn).1)) (hWn n)
    _ = 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ n ∈ hfin.toFinset,
          (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun 𝔭 _ => Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> ring

theorem tendsto_sum_of_mean (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n')
    (hmean : ∀ 𝔭 ∈ S, Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')) atTop (𝓝 1))
    {b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ))) := by
  classical
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
      Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) := ⟨_, rfl⟩
  rw [← hL1]
  have hL1n : 0 ≤ L1 := by
    rw [hL1]
    exact div_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  have hw : ∀ j : ℕ, 0 ≤ ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) := fun j =>
    zpow_nonneg (sq_nonneg _) _
  have hC0 : 0 ≤ 2 * ∏ 𝔭 ∈ S, C 𝔭 :=
    mul_nonneg (by norm_num) (Finset.prod_nonneg fun 𝔭 h𝔭 => le_trans (abs_nonneg _) (hbd 𝔭 h𝔭 0))
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭.1 ≠ ⊥ := fun 𝔭 =>
    Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
  have hIne : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ), b ⊓ 𝔭.1 ^ e ≠ ⊥ := by
    intro 𝔭 e h
    have h1 : b * 𝔭.1 ^ e ≤ b ⊓ 𝔭.1 ^ e := Ideal.mul_le_inf
    rw [h, le_bot_iff, ← Ideal.zero_eq_bot] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hb (by rwa [Ideal.zero_eq_bot] at h2)
    · exact hpos 𝔭 (by rw [← Ideal.zero_eq_bot]; exact pow_eq_zero_iff'.1 h2 |>.1)
  have hNle : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ),
      L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ e) : ℝ) ≤ L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ e := by
    intro 𝔭 e
    have hd : Ideal.absNorm (𝔭.1 ^ e) ∣ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) :=
      Ideal.absNorm_dvd_absNorm_of_le inf_le_right
    have hn0 : Ideal.absNorm (b ⊓ 𝔭.1 ^ e) ≠ 0 := fun h => hIne 𝔭 e (Ideal.absNorm_eq_zero_iff.1 h)
    have hp0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hpos 𝔭 (Ideal.absNorm_eq_zero_iff.1 h)
    have hle : Ideal.absNorm 𝔭.1 ^ e ≤ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) := by
      rw [← map_pow]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
    refine div_le_div_of_nonneg_left hL1n (by positivity) ?_
    exact_mod_cast hle
  have hμ : Tendsto (fun k : ℕ => L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n'))) atTop (𝓝 (L1 / (Ideal.absNorm b : ℝ) * 1)) := by
    have := tendsto_finsetProd S hmean
    simp only [Finset.prod_const_one] at this
    exact this.const_mul _
  have hErr := tendsto_err S (2 * ∏ 𝔭 ∈ S, C 𝔭) L1 c
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.1 hμ (ε / 4) (by linarith)
  obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.1 hErr (ε / 4) (by linarith)
  obtain ⟨k, hk1, hk2⟩ : ∃ k, K1 ≤ k ∧ K2 ≤ k := ⟨max K1 K2, le_max_left _ _, le_max_right _ _⟩
  have g1 := hK1 k hk1
  have g2 := hK2 k hk2
  rw [Real.dist_eq, mul_one] at g1
  rw [Real.dist_eq, sub_zero] at g2
  have hP := tendsto_sum_periodic hK hF hm k (fun 𝔭 q => a 𝔭 (Quotient.out q)) S b hb hbS 0
  simp only [sub_zero] at hP
  rw [← hL1] at hP
  have hE : Tendsto (fun j : ℕ => 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) atTop
      (𝓝 (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum S fun 𝔭 _ => ?_)
    have := tendsto_sum_ideal hK hF hm (hIne 𝔭 (k + 1 - c 𝔭))
    rwa [← hL1] at this
  obtain ⟨J1, hJ1⟩ := Metric.tendsto_atTop.1 hP (ε / 4) (by linarith)
  obtain ⟨J2, hJ2⟩ := Metric.tendsto_atTop.1 hE (ε / 4) (by linarith)
  refine ⟨max J1 J2, fun j hj => ?_⟩
  have d1 := hJ1 j (le_of_max_le_left hj)
  have d2 := hJ2 j (le_of_max_le_right hj)
  rw [Real.dist_eq] at d1 d2 ⊢
  have hcmp : 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ) ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun 𝔭 _ => hNle 𝔭 _) hC0
  have key := local_density_error_le_of_bounded_congruent hK hF m S a C c hbd hcg b ((j : ℝ) ^ 2) _ (hw j) k
  have t1 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
    (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ))
  have t2 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')))
    (L1 / (Ideal.absNorm b : ℝ))
  have d2' := (abs_lt.1 d2).2
  have g2' := (abs_lt.1 g2).2
  linarith

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

