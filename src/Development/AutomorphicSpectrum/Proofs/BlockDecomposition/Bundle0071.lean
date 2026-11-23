module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
section
open PositivityTheory.Rg.BcB.E1

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_sub_of_kerBasic (hK : KerBasic) (X : Ctx) {φ φ' : X.G → ℂ} (h : Tst φ) (h' : Tst φ')
    (x y : X.G) :
    ker X.Γ (fun z => φ z - φ' z) x y = ker X.Γ φ x y - ker X.Γ φ' x y := by
  unfold ker
  exact finsum_sub_distrib ((hK X φ h).1 x y) ((hK X φ' h').1 x y)

theorem enorm_sq_Lp_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : Lp ℂ 2 ν) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖(f : α → ℂ) z‖ₑ ^ 2 ∂ν := by
  rw [Lp.eNorm_def]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : α → ℂ)) (μ := ν) (p := 2)
    (by norm_num) (Lp.aestronglyMeasurable f)
  simpa using h

theorem enorm_sq_piLp_two {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by
  have h : ‖f‖₊ ^ 2 = ∑ l, ‖f l‖₊ ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    simpa using PiLp.norm_sq_eq_of_L2 E f
  simp only [eNorm_eq_nnNorm]
  exact_mod_cast congrArg (fun t : NNReal => (t : ℝ≥0∞)) h

theorem vecClose_of_kerBasic_colSq : KerBasic → ColSq → VecClose := by
  intro hK hC X ι _ Φ Φ' Ω ε y j k k' hΩ hΦ hk hk'
  set R : ℝ≥0∞ := ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y with hR
  have key : ∀ l, ‖(k - k') l‖ₑ ^ 2 ≤ R := by
    intro l
    obtain ⟨t, t', s, s', hd⟩ := hΦ l
    have hT : Tst (fun z => Φ l j z - Φ' l j z) :=
      ⟨t.1.sub t'.1, t.2.sub t'.2⟩
    have hS : Function.support (fun z => Φ l j z - Φ' l j z) ⊆ Ω := by
      intro z hz
      by_contra hn
      have h1 : Φ l j z = 0 := by
        by_contra h0
        exact hn (s h0)
      have h2 : Φ' l j z = 0 := by
        by_contra h0
        exact hn (s' h0)
      exact hz (by simp [h1, h2])
    have hcol := hC X (fun z => Φ l j z - Φ' l j z) ε Ω hT hd hΩ hS y
    have hae : ((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν]
        fun z => ker X.Γ (fun w => Φ l j w - Φ' l j w) z y := by
      filter_upwards [Lp.coeFn_sub (k l) (k' l), hk l, hk' l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ker_sub_of_kerBasic hK X t t']
    have hsub : (k - k') l = k l - k' l := rfl
    rw [hsub, enorm_sq_Lp_two]
    calc ∫⁻ z, ‖((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) z‖ₑ ^ 2 ∂X.ν
        = ∫⁻ z, ‖ker X.Γ (fun w => Φ l j w - Φ' l j w) z y‖ₑ ^ 2 ∂X.ν :=
          lintegral_congr_ae (hae.mono fun z hz => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) hz)
      _ ≤ R := hcol
  rw [enorm_sq_piLp_two]
  calc ∑ l, ‖(k - k') l‖ₑ ^ 2 ≤ ∑ _l : ι, R := Finset.sum_le_sum fun l _ => key l
    _ = Fintype.card ι * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.KernelColumns

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.E1

theorem vecInner_of_kerBasic : KerBasic → VecInner := by
  intro hK X ι _ Φ y j k u hΦ
  constructor
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    have h := (hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y
    rw [hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]

end GlobalTheory.CompanionTheory.E1

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith

theorem vecLim_of (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'

end GlobalTheory.CompanionTheory.KernelColumns

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_zero (X : Ctx) (x y : X.G) : ker X.Γ (0 : X.G → ℂ) x y = 0 := by
  simp [ker]

theorem isVec_zero (X : Ctx) {ι : Type} [Fintype ι] (y : X.G) (j : ι) :
    X.IsVec (0 : Matrix ι ι (X.G → ℂ)) y j (0 : X.Hs ι) := by
  intro l
  have h : (((0 : X.Hs ι) l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν] 0 := Lp.coeFn_zero ℂ 2 X.ν
  refine h.trans (Filter.Eventually.of_forall fun z => ?_)
  exact (ker_zero X z y).symm

theorem tst_zero (X : Ctx) : Tst (0 : X.G → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero⟩

theorem exists_bound (X : Ctx) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ))
    (hΦ : ∀ i j, Tst (Φ i j)) : ∃ ε : ℝ, ∀ l j z, ‖Φ l j z‖ ≤ ε := by
  have h : ∀ i j, ∃ B : ℝ, ∀ z, ‖Φ i j z‖ ≤ B := fun i j => by
    obtain ⟨B, hB⟩ := ((hΦ i j).1.norm).bddAbove_range_of_hasCompactSupport (hΦ i j).2.norm
    exact ⟨B, fun z => hB ⟨z, rfl⟩⟩
  choose B hB using h
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => (norm_nonneg _).trans (hB i j 1)
  refine ⟨∑ i, ∑ j, B i j, fun l j z => (hB l j z).trans ?_⟩
  calc B l j ≤ ∑ j, B l j :=
        Finset.single_le_sum (f := fun j => B l j) (fun j _ => hB0 l j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j :=
        Finset.single_le_sum (f := fun i => ∑ j, B i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hB0 i j) (Finset.mem_univ l)

theorem vecNorm_of_vecClose : VecClose → VecNorm := by
  intro hV X ι _ Φ hΦ
  obtain ⟨ε, hε⟩ := exists_bound X Φ hΦ
  set Ω₀ : Set X.G := ⋃ i, ⋃ j, tsupport (Φ i j) with hΩ₀
  have hc : IsCompact Ω₀ := isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2
  have hci : IsCompact Ω₀⁻¹ := hc.inv
  refine ⟨(Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * X.μ Ω₀⁻¹), Ω₀⁻¹ * Ω₀, ?_,
    hci.mul hc, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hci.measure_lt_top.ne)
  · intro y j k hk
    have h := hV X ι Φ 0 Ω₀ ε y j k 0 hc (fun l => ⟨hΦ l j, tst_zero X, ?_, ?_, ?_⟩) hk
      (isVec_zero X y j)
    · simpa [mul_assoc] using h
    · exact (subset_tsupport _).trans
        (Set.subset_iUnion_of_subset l (Set.subset_iUnion_of_subset j subset_rfl))
    · simp
    · intro z
      simpa using hε l j z

end GlobalTheory.CompanionTheory.KernelColumns

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpPf
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)),
    IsWP ι → Pf p A → Pf p B → Pf p K := by
  intro p _ A _ B _ _ K _ _ n ι hW hA hB
  obtain ⟨⟨FA, hFA⟩, -⟩ := pf_facts p A hA
  obtain ⟨⟨FB, hFB⟩, -⟩ := pf_facts p B hB
  have hchar : (p : K) = 0 := by
    have := congrArg (algebraMap A K) hA.char
    simpa using this
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1
  have hF' : ∀ x, F x = x ^ p := fun x => by rw [hF, pow_one]
  have hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) =
      (algebraMap A K).comp (FA.symm : A →+* A) := by
    intro i
    ext a
    obtain ⟨b, rfl⟩ := FA.surjective a
    have h1 : algebraMap A B (FA b) = FB (algebraMap A B b) := by
      rw [hFA, hFB, map_pow]
    simp [h1]
  obtain ⟨z, hz1, hz2⟩ := hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A))
    (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat
  have hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a) := fun a => by
    simpa using congrArg (fun f : A →+* K => f a) hz1
  have hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b) := fun i b => by
    simpa using congrArg (fun f : B →+* K => f b) (hz2 i)
  have hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a) := fun a => by
    rw [hF', hFA, map_pow]
  have hFb : ∀ i b, F (ι i b) = ι i (FB b) := fun i b => by
    rw [hF', hFB, map_pow]
  have hFz : F.comp z = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  have hzF : z.comp F = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  refine ⟨hchar, ?_, ?_⟩
  · intro x y hxy
    have h : F x = F y := by rw [hF', hF']; exact hxy
    have := congrArg z h
    have hx : ∀ w, z (F w) = w := fun w => by
      simpa using congrArg (fun f : K →+* K => f w) hzF
    rwa [hx, hx] at this
  · intro y
    refine ⟨z y, ?_⟩
    have : F (z y) = y := by simpa using congrArg (fun f : K →+* K => f y) hFz
    simpa [hF'] using this

end GlobalTheory.CompanionTheory.PerfectRing
end

