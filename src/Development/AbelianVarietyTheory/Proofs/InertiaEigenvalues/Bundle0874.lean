module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExcludedPrimesFewAndSmallAlongFamily
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.ExcBound

open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

theorem card_Icc_ceil_floor_le (a b : ℝ) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ max (b - a + 1) 0 := by
  have h : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = max (⌊b⌋ + 1 - ⌈a⌉) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  have h' : (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) : ℝ) = ((max (⌊b⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  exact max_le_max (by linarith [Int.floor_le b, Int.le_ceil a]) le_rfl

variable {D : D7} (L : SizeData₂ D)

theorem excOK_at (P : ParameterChoice' D L) (hS : SizesAt L) :
    ∃ exc : Finset ℕ, (exc : Set ℕ) = Exc L ∧ ExcOK L exc := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, hLs, -⟩ := hS
  obtain ⟨hL1, hL2⟩ := hLs
  have hsz : szlStar L = LevelStarExponents.lStar L := rfl
  rw [hsz] at hL1 hL2
  set ls := LevelStarExponents.lStar L with hls_def
  have hls : 0 < ls := lStar_pos L
  have h2ls : 2 * ls < L.sc.b := GlobalTheory.Survey.CongruenceBoundParameters.two_lStar_lt_b L
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hbl : 0 ≤ L.sc.b / ls := by positivity

  have h8 : 8 * L.sc.b < ls ^ 2 := by
    have : 8 * L.sc.b / ls < ls := by
      have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
      linarith
    rw [div_lt_iff₀ hls] at this; nlinarith

  have hsg0 : (0 : ℝ) ≤ (sgPlus L : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  have hsg1 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / ls := Int.floor_le _
  have hsg2 : 2 * L.sc.b / ls = 2 * (L.sc.b / ls) := by ring
  rw [hsg2] at hsg1
  have hL2' : 2 * L.etaSz + D.R.t + 8 * (L.sc.b / ls) + 7 < ls := by
    have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
    linarith

  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := hBot t
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hxe : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos (by linarith) _
    have hΛ : 0 ≤ L.LaG := le_trans hxe.le hLa.1
    have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
      have := Real.log_nonneg hx.le
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L.sc.x) (szTh L)
      positivity
    have hone : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hA : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
      have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have := hRho
      unfold SizeRho at this
      linarith
    have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    rw [this] at h1
    nlinarith
  have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' := by
    refine (Int.floor_le _).trans (div_le_self hb'.le hx.le)
  have hW2 : ∀ W ∈ baseSizes L, W ≤ 2 * L.sc.b := by
    rintro W (rfl | rfl | ⟨t, rfl⟩)
    · linarith
    · linarith
    · have := hbT t; linarith

  have hhi : ∀ W ∈ baseSizes L,
      W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4) < 3 * L.sc.b := by
    intro W hW
    have := hW2 W hW
    linarith

  let BS : Finset ℝ := {L.sc.b, L.sc.w'' D.R.n} ∪
    Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))
  have hBS : ∀ W, W ∈ BS ↔ W ∈ baseSizes L := by
    intro W
    simp only [BS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, baseSizes, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | ⟨t, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, h.symm⟩)
    · rintro (h | h | ⟨t, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, h.symm⟩
  have hBScard : (BS.card : ℝ) ≤ (D.host.TT.card : ℝ) + 2 := by
    have h1 : BS.card ≤ ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card +
        (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card :=
      Finset.card_union_le _ _
    have h2 : ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    have h3 : (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card
        ≤ D.host.TT.card := by
      refine Finset.card_image_le.trans ?_
      simp
    have : BS.card ≤ D.host.TT.card + 2 := by omega
    exact_mod_cast this

  let lo : ℝ → ℝ := fun W => W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3)
  let hi : ℝ → ℝ := fun W => W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)
  let win : ℝ → Finset ℤ := fun W => Finset.Icc ⌈lo W⌉ ⌊hi W⌋
  have hwin : ∀ W n, n ∈ win W ↔ n ∈ window L W := by
    intro W n
    simp only [win, lo, hi, Finset.mem_Icc, Int.ceil_le, Int.le_floor, window, Set.mem_setOf_eq]
  have hwincard : ∀ W, ((win W).card : ℝ) ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by
    intro W
    refine (card_Icc_ceil_floor_le (lo W) (hi W)).trans (max_le (le_of_eq (by simp only [lo, hi]; ring)) ?_)
    linarith

  let exc : Finset ℕ := BS.biUnion fun W => (win W).biUnion fun n =>
    n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)
  have hmem : ∀ l, l ∈ exc ↔ ∃ W ∈ baseSizes L, ∃ n ∈ window L W,
      0 < n ∧ (n : ℝ) < 3 * L.sc.b ∧ l.Prime ∧ l ∣ n.natAbs ∧ ls < (l : ℝ) := by
    intro l
    simp only [exc, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨W, hW, n, hn, ⟨hp, hd, -⟩, hl⟩
      rw [hBS] at hW; rw [hwin] at hn
      exact ⟨W, hW, n, hn, GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn,
        lt_of_le_of_lt hn.2 (hhi W hW), hp, hd, hl⟩
    · rintro ⟨W, hW, n, hn, hpos, -, hp, hd, hl⟩
      refine ⟨W, (hBS W).2 hW, n, (hwin W n).2 hn, ⟨hp, hd, by omega⟩, hl⟩
  refine ⟨exc, ?_, ?_, ?_⟩
  · ext l
    simp only [Finset.mem_coe, hmem, Exc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨W, hW, n, hn, -, -, hp, hd, hl⟩
      exact ⟨hp, hl, W, hW, n, hn, Int.ofNat_dvd_left.2 hd⟩
    · rintro ⟨hp, hl, W, hW, n, hn, hd⟩
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      exact ⟨W, hW, n, hn, hpos, lt_of_le_of_lt hn.2 (hhi W hW), hp, Int.ofNat_dvd_left.1 hd, hl⟩
  ·
    have hone : ∀ W ∈ BS, ∀ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card ≤ 1 := by
      intro W hW n hn
      rw [hBS] at hW; rw [hwin] at hn
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      have hup : (n : ℝ) < 3 * L.sc.b := lt_of_le_of_lt hn.2 (hhi W hW)
      rw [Finset.card_le_one]
      intro p hp q hq
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp hq
      by_contra hpq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.1.1 hq.1.1).2 hpq
      have hdvd : p * q ∣ n.natAbs := hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1
      have hle : p * q ≤ n.natAbs := Nat.le_of_dvd (by omega) hdvd
      have hle' : ((p * q : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
        rw [← this]; exact_mod_cast hle
      push_cast at hle'
      have : ls ^ 2 < (p : ℝ) * q := by nlinarith [hp.2, hq.2]
      linarith
    have hc1 : exc.card ≤ ∑ W ∈ BS, ∑ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => Finset.card_biUnion_le)
    have hc2 : exc.card ≤ ∑ W ∈ BS, (win W).card := by
      refine hc1.trans (Finset.sum_le_sum fun W hW => ?_)
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun n hn => hone W hW n hn
    have hc3 : (exc.card : ℝ) ≤ ∑ W ∈ BS, (L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8) := by
      have : (exc.card : ℝ) ≤ ∑ W ∈ BS, ((win W).card : ℝ) := by exact_mod_cast hc2
      exact this.trans (Finset.sum_le_sum fun W _ => hwincard W)
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have hK0 : 0 ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by linarith
    have hK : L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 ≤
        L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9 := by
      have : 8 * L.sc.b / TwistedPlaces.lStar L = 4 * (2 * L.sc.b / ls) := by
        show 8 * L.sc.b / LevelStarExponents.lStar L = 4 * (2 * L.sc.b / ls); ring
      rw [this, hsg2]; linarith
    refine hc3.trans ?_
    exact mul_le_mul hBScard hK hK0 (by positivity)
  · intro l hl
    obtain ⟨W, hW, n, hn, hpos, hup, hp, hd, -⟩ := (hmem l).1 hl
    have hle : l ≤ n.natAbs := Nat.le_of_dvd (by omega) hd
    have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
    have hle' : (l : ℝ) ≤ (n : ℝ) := by rw [← this]; exact_mod_cast hle
    linarith

end GlobalTheory.NLink.ExcBound

namespace GlobalTheory.NLink

theorem excOK_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  intro eps Fm
  exact ⟨Fm.x1, fun x _ hx i => ExcBound.excOK_at (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i)⟩

end GlobalTheory.NLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPole
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspReg

theorem exists_cover_noPole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hF := cusp_le_sec Xo c U a n hf
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  have hY : ∃ Y : Model Xo c (algebraMap (la.valuation c.F).valuationSubring c.F),
      PushInvertible Y.t.G Y.t.PP.L := by
    by_cases hr : 1 ≤ Dw.p + Dw.q
    · obtain ⟨Y, hP, -⟩ := GlobalTheory.GoodTransfer.exists_model hr Xo c la p hp hpl hg
      exact ⟨Y, hP⟩
    · exact GlobalTheory.SupFinite.exists_model_rank_zero (Xo := Xo) (c := c) (by omega) _
  obtain ⟨Y, hP⟩ := hY
  obtain ⟨J, hJ, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c
    hE.bc (la.valuation c.F).valuationSubring Y hP
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : ∀ j, ∀ e ∈ (P j).es, evR Xo c f (P j).yg ∈ (P j).R e := fun j e he => by
    rw [(hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)]
    exact (evR Xo c f ((P j).y e he)).2
  have hint : ∀ j, IsIntegral (Algebra.adjoin c.F ((P j).gens : Set (P j).Ω)) (evR Xo c f (P j).yg) := by
    intro j
    refine GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem c.F (P j).Ω (P j).gens (P j).frac _ fun T hT φ hK hgn => ?_
    obtain ⟨e, he⟩ := (P j).es_ne
    let io : c.F →+* T.Fr := φ.comp (algebraMap c.F (P j).Ω)
    letI := io.toAlgebra
    let ψ : (P j).R e →ₐ[c.F] T.Fr :=
      { toRingHom := φ.comp ((P j).R e).val.toRingHom, commutes' := fun k => rfl }
    obtain ⟨z, hz⟩ := hE.bc _ _ ψ ((P j).y e he)
    have hzI := (P j).int e he T io ψ (fun a => hK _) (fun g hg' => hgn _ hg') z hz
    have h1 := _root_.GlobalTheory.EqCharCusp.integral_of_eqChar E H Dw l Xo c r U hU a n f hd hf T hT io hK ⟨z, hE.test _ z, hzI⟩
    have e1 : evR Xo c f z = ψ (evR Xo c f ((P j).y e he)) := (hev _).1 _ ψ _ _ hz
    have e2 : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    rw [e2]
    change evR Xo c f z ∈ _ at h1
    rw [e1] at h1
    exact h1
  choose P' hP'1 hP'2 using fun j => _root_.GlobalTheory.Reg.Enlarge.enlarge_exists E H Dw l Xo c (la.valuation c.F).valuationSubring f (P j) (hmem j) (hint j)
  refine ⟨J, hJ, P', fun L _ _ W hW y => ?_, hP'1⟩
  obtain ⟨j, hj⟩ := hC L W hW y
  exact ⟨j, hP'2 j L W hW y hj⟩

end GlobalTheory.CuspReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSums
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeReadRational

section SlopeTestRemainingChoices

open Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem hkC_eq_heckeScalar {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : hkC R i P k = heckeScalar R i P k := by
  rw [hkC, heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]

theorem heckeOn_mem_wall_of_hkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb) (hHW : R.models_HW)
    (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hd : IsHkData R i P k α Rc) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) ∈ R.Wall i σ := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.HeckeSup.exists_local_isDC hoL.splits hαL hR
  have key : heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) = heckeOn (R.MW i σ) A₀ ((R.HW i σ).e z) := by
    ext v : 1
    show heckeLin (Wc D i) Rc ((R.HW i σ).e z v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e z v)
    exact funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (GlobalTheory.HeckeSup.model_inv_cl hHW i σ z v) h
  rw [key]
  exact GlobalTheory.HeckeModel.heckeOn_mem_mult hoL (fun g hg => hq.2.2.1 g ((hLg g).1 hg)) hαL hA₀
    (show (R.HW i σ).e z ∈ R.Wall i σ from (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z)

end SlopeTestRemainingChoices

section Main

open Formalism.IndefR.Mult


set_option maxHeartbeats 1600000 in
theorem rationalHecke_of_readsCusp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i hT hlev hfam hmod hex _ hR P hP k hk
  have hHW : R.models_HW := hmod.HW
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, -⟩ := GlobalTheory.HeckeSup.exists_prime_under P
  have hoff := GlobalTheory.HeckeSup.not_dvd_level fw.laws hpP hP.2
  have hsp := GlobalTheory.HeckeSup.split_of_ne (H := T.Q.H) hP.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have htr : ∀ f : Cu T κ i, ∃ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g := by
    intro f
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hT GlobalTheory.ThetaTransport.heckePointLaws fw.laws i
      ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hk ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
    rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
      hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose g hg hfg using htr
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hread : ∀ f : Cu T κ i, ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys R i P k Rc →
      (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK)) =
        GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc
          ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
    rintro f Rc ⟨α, hα, hRc⟩
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R i P k α Rc := ⟨hP.1, hP.2, hk, hα, hRc⟩
    have h1 := hR hV P p k α Rc hd ⟨hP.1, hp, hpP, hoff, hk, hα, hRc⟩ f f.2 (g f) (hg f) (hfg f)
    rw [hkC_eq_heckeScalar] at h1
    obtain ⟨z', hz'⟩ : ∃ z', (R.HW i (sg0 D A)).e z' = heckeOn (R.MW i (sg0 D A)) Rc
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
      rw [← LinearMap.mem_range, (hHW i _).2.1]
      exact heckeOn_mem_wall_of_hkData (hlev.βW i) hfam.Sb hHW _ hd _
    have e1 : (R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK) = GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • z' := by
      apply hEI
      refine (GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) ⟨g f, hg f⟩).trans ?_
      funext h
      rw [h1 h, ← GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) f]
      unfold evAt
      rw [map_smul, hz']
      simp [heckeOn, postOn, heckeLin]
      exact Or.inl rfl
    rw [e1, map_smul, hz']
  obtain ⟨n, b, hbK, -, hKspan, hLind, hLspan⟩ := fw.ks i
  let B : Module.Basis (Fin n) D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := Module.Basis.mk hLind hLspan.ge
  have hB : ∀ l, B l = b l := fun l => Module.Basis.mk_apply hLind hLspan.ge l
  let f0 : Fin n → Cu T κ i := fun l => (fw.e i).symm ⟨b l, hbK l⟩
  let yv : Fin n → Fin (R.nW i) → D.what₂.LL := fun l => (fw.e i ⟨g (f0 l), hg (f0 l)⟩ : (R.FW i).WK)
  let hL := B.constr D.what₂.LL yv
  have hLb : ∀ l, hL (b l) = yv l := fun l => by rw [← hB l]; exact B.constr_basis _ _ _
  have hb0 : ∀ l, (fw.e i (f0 l) : Fin (R.nW i) → D.what₂.LL) = b l := fun l => by simp [f0]
  refine ⟨hL, fun Rc hRc => ?_, fun x hx => ?_⟩
  · have hext := B.ext (f₁ := ((R.HW i (sg0 D A)).e.comp ((R.FW i).j (sg0 D A))).comp hL)
      (f₂ := ((GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc).comp (R.HW i (sg0 D A)).e).comp
        ((R.FW i).j (sg0 D A))) fun l => by
      rw [hB l]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hLb l, ← hb0 l]
      exact hread (f0 l) Rc hRc
    intro x
    have := LinearMap.congr_fun hext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  · rw [← hKspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hLb]
      exact (fw.e i _).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ a hx

end Main

end GlobalTheory.HeckeReadRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext) | (exact GlobalTheory.SchurExt.exists_ext) | (intros; apply GlobalTheory.SchurExt.exists_ext <;> assumption)
end

