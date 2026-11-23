module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot E m (lam c) (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralEqSum
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.HeckeStabY

theorem exists_integral_eq_sum {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ S : Finset G, ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → (∀ g, h g = 0 → F g = 0) →
      ∫ g, F g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ s ∈ S, F s := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset G, tsupport h ⊆ ⋃ g ∈ t, (fun x => g⁻¹ * x) ⁻¹' (K : Set G) := by
    have := (show IsCompact (tsupport h) from hc).elim_nhds_subcover
      (fun g => (fun x => g⁻¹ * x) ⁻¹' (K : Set G))
      (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds
        (by simpa using K.one_mem))
    obtain ⟨t, -, ht⟩ := this
    exact ⟨t, ht⟩
  let Q : Finset (G ⧸ K) := t.image (QuotientGroup.mk : G → G ⧸ K)
  refine ⟨Q.image Quotient.out, fun F hF hz => ?_⟩
  have hinj : Set.InjOn (Quotient.out : G ⧸ K → G) (Q : Set (G ⧸ K)) :=
    fun a _ b _ e => by simpa using congrArg (QuotientGroup.mk : G → G ⧸ K) e
  rw [Finset.sum_image hinj]
  have hfib : ∀ q : G ⧸ K, {g : G | (QuotientGroup.mk g : G ⧸ K) = q} =
      (fun x => (Quotient.out q)⁻¹ * x) ⁻¹' (K : Set G) := fun q => by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]
    simp
  have hmeas : ∀ q : G ⧸ K, MeasurableSet {g : G | (QuotientGroup.mk g : G ⧸ K) = q} := fun q => by
    rw [hfib]
    exact (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hvol : ∀ q : G ⧸ K, μ {g : G | (QuotientGroup.mk g : G ⧸ K) = q} = μ (K : Set G) := fun q => by
    rw [hfib]
    exact measure_preimage_mul μ _ _
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hval : ∀ g : G, F g = F (Quotient.out (QuotientGroup.mk g : G ⧸ K)) := fun g => by
    have hm : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K := by
      rw [← QuotientGroup.eq]
      simp
    have e := hF (Quotient.out (QuotientGroup.mk g : G ⧸ K)) _ hm
    rw [mul_inv_cancel_left] at e
    exact e
  have hsum : ∀ g, F g = ∑ q ∈ Q,
      ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g := by
    intro g
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    split_ifs with hq
    · exact hval g
    · refine hz g ?_
      by_contra hne
      have hg : g ∈ tsupport h := subset_tsupport h hne
      obtain ⟨g₀, hg₀, hm⟩ := Set.mem_iUnion₂.1 (ht hg)
      refine hq (Finset.mem_image.2 ⟨g₀, hg₀, ?_⟩)
      exact QuotientGroup.eq.2 hm
  have hint : ∀ q ∈ Q, Integrable
      (({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q))) μ := fun q _ =>
    (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol]; exact hfin))
  calc ∫ g, F g ∂μ = ∫ g, ∑ q ∈ Q,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ = ∑ q ∈ Q, ∫ g,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_finsetSum Q hint
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hmeas q), Measure.real, Measure.real, hvol, Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.HeckeStabY

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspace
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Inj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL_alt : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem R_apply_eq {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {U : Subgroup (GL (Fin a) (Af E))}
    {v : L2 (latticeGL E a) μ} (hv : ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) {g : GA E a}
    (hu : GeneralLinearGroup.map (pFin E) g⁻¹ ∈ U) :
    R (latticeGL E a) μ g v = R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v := by
  have e : g = infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹ * finGL E a (GeneralLinearGroup.map (pFin E) g⁻¹)⁻¹ := by
    rw [map_inv (infGL E a), map_inv (finGL E a), ← _root_.mul_inv_rev, ← infGL_comm, infGL_mul_finGL, inv_inv]
  conv_lhs => rw [e]
  rw [map_mul, ContinuousLinearMap.mul_apply, hv _ (U.inv_mem hu)]

theorem exists_isTest_Rop_injective : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  intro E _ _ _ a μ _ _ U hU hUc X hX hfix
  let Φ : GL (Fin a) (Cinf E) → (X →L[ℂ] L2 (latticeGL E a) μ) := fun y =>
    (R (latticeGL E a) μ (infGL E a y⁻¹) - ContinuousLinearMap.id ℂ _) ∘L X.subtypeL
  have hΦv : ∀ y (w : X), Φ y w = R (latticeGL E a) μ (infGL E a y⁻¹) w - w := fun _ _ => rfl
  have hΦ : Continuous Φ := by
    refine continuous_clm_apply.2 fun w => ?_
    simp only [hΦv]
    exact ((continuous_R (w : L2 (latticeGL E a) μ)).comp (continuous_infGL_alt.comp continuous_inv)).sub
      continuous_const
  have hΦ1 : Φ 1 = 0 := by
    ext w
    simp [hΦv]
  have hN : {y | ‖Φ y‖ ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) := by
    have h1 : Metric.closedBall (0 : X →L[ℂ] L2 (latticeGL E a) μ) (1 / 2) ∈ 𝓝 (Φ 1) := by
      rw [hΦ1]; exact Metric.closedBall_mem_nhds _ (by norm_num)
    have h2 := hΦ.continuousAt.preimage_mem_nhds h1
    change {y | dist (Φ y) 0 ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) at h2
    simpa only [dist_zero_right] using h2
  obtain ⟨β₀, h0, hpos, htest, hconj, hsupp⟩ := _root_.GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv E a _ hN
  refine ⟨fun x => (β₀ x : ℂ), htest, hconj, fun v hv hRv => ?_⟩
  obtain ⟨hc, hcs⟩ := _root_.GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst E a U hU hUc _ htest
  set f := tst U (fun x => (β₀ x : ℂ)) with hf
  set fr : GA E a → ℝ := fun g => (f g).re with hfr
  have hf_eq : ∀ g, f g = (fr g : ℂ) := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs <;> simp
  have hfr0 : ∀ g, 0 ≤ fr g := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs
    · simpa using h0 _
    · simp
  have hfrc : Continuous fr := Complex.continuous_re.comp hc
  have hfrs : HasCompactSupport fr := hcs.comp_left Complex.zero_re
  have hfr1 : fr 1 ≠ 0 := by
    have : fr 1 = β₀ (oneL E a) := by
      simp [hfr, hf, tst, ker, U.one_mem]
    rw [this]; exact hpos.ne'
  have hIpos : 0 < ∫ g, fr g ∂μ :=
    hfrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hfrs hfr0 hfr1
  have hint : Integrable f μ := hc.integrable_of_hasCompactSupport hcs
  have hfrint : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hrep := (isRepOp_Rop (Γ := latticeGL E a) (μ := μ) hint) v
  have key : (∫ g, f g ∂μ) • v = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
    calc (∫ g, f g ∂μ) • v = (∫ g, f g ∂μ) • v - ∫ g, f g • R (latticeGL E a) μ g v ∂μ := by
          have h2 := hrep.2.symm.trans hRv
          rw [show (∫ g, f g • R (latticeGL E a) μ g v ∂μ) = 0 from h2, sub_zero]
      _ = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
          rw [← integral_smul_const, ← integral_sub (hint.smul_const v) hrep.1]
          simp_rw [smul_sub]
  have hI : (∫ g, f g ∂μ) = ((∫ g, fr g ∂μ : ℝ) : ℂ) := by
    simp_rw [hf_eq]; exact integral_ofReal
  have hpt : ∀ g, fr g ≠ 0 → ‖v - R (latticeGL E a) μ g v‖ ≤ ‖v‖ / 2 := by
    intro g hg
    have hfg : f g ≠ 0 := fun h => hg (by show (f g).re = 0; rw [h]; simp)
    simp only [hf, tst, ker] at hfg
    split_ifs at hfg with hu
    · have hb : β₀ (toL (GeneralLinearGroup.map (pInf E) g⁻¹).val) ≠ 0 := by
        intro h; apply hfg; simp only [Complex.ofReal_eq_zero]; convert h using 1
      obtain ⟨y, hyN, hy⟩ := hsupp _ hb
      have hy' : y = GeneralLinearGroup.map (pInf E) g⁻¹ := Units.ext (Matrix.of.symm.injective hy)
      rw [R_apply_eq (fun u hu' => hfix u hu' v hv) hu, norm_sub_rev]
      calc ‖R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v - v‖
          = ‖Φ y ⟨v, hv⟩‖ := by rw [hΦv, hy']
        _ ≤ ‖Φ y‖ * ‖(⟨v, hv⟩ : X)‖ := (Φ y).le_opNorm _
        _ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hyN (norm_nonneg _)
        _ = ‖v‖ / 2 := by ring
    · exact absurd rfl hfg
  have hbound : ‖∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ‖ ≤ ∫ g, fr g * (‖v‖ / 2) ∂μ :=
    norm_integral_le_of_norm_le (hfrint.mul_const _) (Filter.Eventually.of_forall fun g => by
      rw [norm_smul, hf_eq, Complex.norm_real, Real.norm_of_nonneg (hfr0 g)]
      by_cases hg : fr g = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (hpt g hg) (hfr0 g))
  rw [integral_mul_const, ← key, hI, norm_smul, Complex.norm_real, Real.norm_of_nonneg hIpos.le] at hbound
  have hle : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 hle

end GlobalTheory.CompanionTheory.SmoothRep.Inj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
section
open NumberField MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

open Ad3.R

theorem pri_eq_diagonal (α : ℚˣ) : pri α = diagonal ℚ α := rfl

theorem md_eq (a : Jd) : md a = (ideleModule ℚ a : ℝ) := rfl

theorem lintegral_posReal_weight_lt_top (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ t : {r : ℝ // 0 < r}, ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ) ∂posRealMeasure < ∞ := by
  have hF : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  rw [posRealMeasure_eq_map_expPos, lintegral_map hF measurable_expPos]
  simp only [coe_expPos]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (τ * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ 1 :=
        pow_le_one₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_left _ _)
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ 1 * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (τ * x) := by rw [one_mul, mul_comm, Real.exp_mul]
    · exact Integrable.lintegral_lt_top (integrableOn_exp_mul_Iic h0 0)
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (-((M : ℝ) - τ) * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ (Real.exp x)⁻¹ ^ M :=
        pow_le_pow_left₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_right _ _) M
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (-((M : ℝ) - τ) * x) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    · exact Integrable.lintegral_lt_top (exp_neg_integrableOn_Ioi 0 (sub_pos.2 h1))

def fundD (w : InfinitePlace ℚ) : Set Jd :=
  (fun a => (normOneSplitting w a).1) ⁻¹' normOneFundamentalDomain ℚ

theorem measurableSet_fundD (w : InfinitePlace ℚ) : MeasurableSet (fundD w) := by
  exact (measurableSet_normOneFundamentalDomain ℚ).preimage (measurePreserving_normOneSplitting w).measurable.fst

theorem split_pri_mul (w : InfinitePlace ℚ) (α : ℚˣ) (a : Jd) :
    (normOneSplitting w (pri α * a)).1 = (normOneSplitting w a).1 * diagonalToNormOne ℚ α := by
  have hp : pri α = (normOneSplitting w).symm (diagonalToNormOne ℚ α, 1) := by
    simp only [normOneSplitting_symm_apply, map_one, mul_one, coe_diagonalToNormOne, pri_eq_diagonal]
  have key : normOneSplitting w (pri α) = (diagonalToNormOne ℚ α, 1) := by
    rw [hp]
    exact (normOneSplitting w).apply_symm_apply _
  rw [map_mul, Prod.fst_mul, key]
  exact mul_comm _ _

theorem existsUnique_pri_mul_mem (w : InfinitePlace ℚ) (a : Jd) :
    ∃! α : ℚˣ, pri α * a ∈ fundD w := by
  have h : ∀ α : ℚˣ, pri α * a ∈ fundD w ↔
      (normOneSplitting w a).1 * diagonalToNormOne ℚ α ∈ normOneFundamentalDomain ℚ := by
    intro α
    show (normOneSplitting w (pri α * a)).1 ∈ normOneFundamentalDomain ℚ ↔ _
    rw [split_pri_mul]
  exact (existsUnique_congr h).2 (existsUnique_mul_mem_normOneFundamentalDomain ℚ _)

theorem lintegral_fundD_lt_top (w : InfinitePlace ℚ) (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ a in fundD w, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞ := by
  have hφm : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  have hIm : Measurable ((normOneFundamentalDomain ℚ).indicator (1 : normOneSubgroup ℚ → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_normOneFundamentalDomain ℚ)
  have hpt : ∀ a : Jd, (fundD w).indicator (fun a => ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ)) a =
      (fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ)) (normOneSplitting w a) := by
    intro a
    by_cases ha : a ∈ fundD w
    · have ha' : (normOneSplitting w a).1 ∈ normOneFundamentalDomain ℚ := ha
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem ha', normOneSplitting_apply_snd, md_eq]
    · have ha' : (normOneSplitting w a).1 ∉ normOneFundamentalDomain ℚ := ha
      simp [ha, ha']
  rw [← lintegral_indicator (measurableSet_fundD w), lintegral_congr hpt,
    (measurePreserving_normOneSplitting w).lintegral_comp
      (f := fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ))
      ((hIm.comp measurable_fst).mul (hφm.comp measurable_snd)),
    lintegral_prod_mul hIm.aemeasurable hφm.aemeasurable, lintegral_indicator_one (measurableSet_normOneFundamentalDomain ℚ)]
  exact ENNReal.mul_lt_top (normOneMeasure_normOneFundamentalDomain_lt_top ℚ)
    (lintegral_posReal_weight_lt_top τ M h0 h1)

theorem exists_idele_fundamentalDomain : Ad3.R.D0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  unfold Ad3.R.D0
  exact ⟨fundD w, measurableSet_fundD w, existsUnique_pri_mul_mem w,
    fun τ M h0 h1 => lintegral_fundD_lt_top w τ M h0 h1⟩

end GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

end
end

