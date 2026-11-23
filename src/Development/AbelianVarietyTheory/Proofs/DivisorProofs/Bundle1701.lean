module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNorm
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_quot_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    Nat.card (𝓞 D.host.E ⧸ P'.asIdeal) = Nat.card (𝓞 D.host.E ⧸ P.asIdeal) := by
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)
  have hle : P.asIdeal.map σ ≤ P'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : σ c = c' := RingOfIntegers.ext h2.symm
    show σ c ∈ P'.asIdeal
    rw [e]; exact h1
  have hmax : (P.asIdeal.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ (hp := P.isMaximal)
  have e : P'.asIdeal = P.asIdeal.map σ := (hmax.eq_of_le P'.isPrime.ne_top hle).symm
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal P'.asIdeal σ e).toEquiv).symm

theorem twist_ram_prime_dvd_Qn : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  classical
  intro D T Lc sc G μ₀ hL i j t w hxi hnu

  have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro hS
    have hv := (Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1
    have hE := hv.2.2.2 (w.under (𝓞 D.host.F)) w rfl
    have hexp := (hE.2 (Finset.notMem_empty _) 0).1 ((Formalism.L2.Host.HChar.unrAt_iff _ _).1 hnu)
    rw [Model.expIn_condF, if_pos hS, condExp] at hexp
    split_ifs at hexp <;> omega

  obtain ⟨PP, hPP, hw⟩ : ∃ PP ∈ Lc.Q t, w = PP ∨ Formalism.IndefR.Lev.IsConjPl PP w := by
    rcases (hL.Q_ram t w).1 hxi with h | ⟨PP, h, hc⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨PP, h, Or.inr hc⟩
  have hunder : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = w.under (𝓞 D.host.F) := by
    rcases hw with rfl | hc
    · rfl
    · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
  have hW0 : PP ∉ G.pl.W0 := by
    intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    apply hS0
    rw [← hunder, G.pl.under_w hv]
    exact hv
  have hloc : PP ∈ GlobalTheory.FunObj.locPl G t := Finset.mem_union_right _ hPP
  have htw : PP ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t PP hPP
  have hnorm : Ideal.absNorm PP.asIdeal = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hcard]
  refine ⟨q, hq, ?_, ?_, PP, hloc, hnorm⟩
  · rcases hw with rfl | hc
    · exact hcard
    · rw [card_quot_of_isConjPl hc]; exact hcard
  · rw [← hnorm]
    exact Finset.dvd_prod_of_mem _ htw

end GlobalTheory.SqTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderPrimeNotMemOfNormCoprime
section
open NumberField IsDedekindDomain
open Classical

theorem GlobalTheory.twPl_under_not_mem_prime : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL}, (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal → ∀ q ∈ ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal := by
  intro D T L sc G t l hl w hlw hQ q hq hlq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
  have hlP : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h := hlq
    simp only [HeightOneSpectrum.under] at h
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ P.asIdeal := h
    simpa using this
  have hdvd : l ∣ Ideal.absNorm P.asIdeal := by
    have h1 := Ideal.absNorm_dvd_norm_of_mem hlP
    have h2 : ((l : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (l : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have h3 : Ideal.absNorm P.asIdeal ∣ l ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      simpa [Int.natAbs_pow] using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp h3
    have hne : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact P.isPrime.ne_top
    rcases k with _ | k
    · rw [pow_zero] at hk; exact absurd hk hne
    · rw [hk]; exact dvd_pow_self l (Nat.succ_ne_zero k)
  have hQd : l ∣ GlobalTheory.SqTop.Qn G t :=
    dvd_trans hdvd (Finset.dvd_prod_of_mem _ hP)
  obtain ⟨k, hk⟩ := hQd
  apply hQ
  rw [hk, Nat.cast_mul]
  exact w.asIdeal.mul_mem_right _ hlw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductor
section
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.KummerTwistLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_places_under_split_coprime_conductor : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL t q hq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP
    rcases Finset.mem_union.1 hP.1 with h | h
    · exact absurd h hP.2
    · exact ⟨h, hP.2⟩
  refine ⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩
  · apply (hL.Q_pl t P hP'.1).2 P hP'.1
    intro c hc
    refine ⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩
    have h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [← e] at h
  · exact congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)
  · have hS : P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
      intro h
      rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
      · exact G.pl.levelPlace_ne_basePlace t P hP'.1 h0
      · apply hP'.2
        rw [G.pl.w_Q t P hP'.1 h1]
        exact Finset.mem_image_of_mem _ h
    have h0 := GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))
    rw [if_neg hS] at h0
    have hne : GlobalTheory.FunObj.SqNum.condF G.pl ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    exact (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left (P.under (𝓞 D.host.F)).prime hne)).1 h0

end GlobalTheory.KummerTwistLemmas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF

theorem theta_of_vacuum_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (colLat frS : Set _) (colLat frT : Set _) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) := by
  intro D ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hΦ
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hSd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S frS hS
  have hTd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat T frT hT
  obtain ⟨-, -, h3⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T (colLat frS) (colLat frT) hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := _root_.GlobalTheory.ThetaLawLat.mem_La_frame S T frS frT hS hT δ x hx
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (colLat frS : Set _) (colLat frT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := _root_.GlobalTheory.ThetaSignLat.sign_eq_alpha ψ S T frS frT hS hT hψ δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.ThetaLawOF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchIntertw

open GlobalTheory.AdelicU

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

def infAd : mixedEmbedding.mixedSpace F →+ AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv.toAddMonoidHom

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_infAd (s : mixedEmbedding.mixedSpace F) : evI F (infAd s) = s :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s

theorem sndA_infAd (s : mixedEmbedding.mixedSpace F) : sndA F (infAd s) = 0 := rfl

theorem evFin_infAd (v : Pl (F := F)) (s : mixedEmbedding.mixedSpace F) : evFin F v (infAd s) = 0 := by
  show evalV F v (sndA F (infAd s)) = 0
  rw [sndA_infAd, map_zero]

theorem infAd_evI (t : AF F) (h : sndA F t = 0) : infAd (evI F t) = t := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1) = t.1
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact h.symm

theorem at_infAd (s : mixedEmbedding.mixedSpace F) : At (evI F) (infAd s) := by
  intro u hu
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  refine Prod.ext ?_ ?_
  · change fstA F (u * infAd s) = 0
    rw [map_mul, h1, zero_mul]
  · change sndA F (u * infAd s) = 0
    rw [map_mul, sndA_infAd, mul_zero]

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [NumberField F]

theorem evIHom_invOf [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] :
    evIHom (⅟(2 : AF F)) = ⅟(2 : mixedEmbedding.mixedSpace F) := by
  refine (invOf_eq_left_inv ?_).symm
  rw [show (2 : mixedEmbedding.mixedSpace F) = evIHom (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem schr_pure [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (Ψ : AddChar (AF F) ℂ) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) :
    schr Ψ (fun i => infAd (a i), fun i => infAd (b i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x =
      schr (Ψ.compAddMonoidHom infAd) (a, b) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (fun i => evI F (x i)) *
        ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  have e1 : (fun i => evI F ((x + fun i => infAd (a i)) i)) = (fun i => evI F (x i)) + a := by
    funext i
    change evIHom (x i + infAd (a i)) = evIHom (x i) + a i
    rw [map_add (f := _), evIHom_apply (infAd _), evI_infAd]
  have e2 : ∀ v, (fun i => evFin F v ((x + fun i => infAd (a i)) i)) = fun i => evFin F v (x i) := fun v => by
    funext i
    simp only [Pi.add_apply, map_add (f := _), evFin_infAd, add_zero]
  have hs : sndA F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_sum, map_mul, sndA_infAd, mul_zero, Finset.sum_const_zero, add_zero]
  have hi : evI F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) =
      (fun i => evI F (x i)) ⬝ᵥ b + ⅟(2 : mixedEmbedding.mixedSpace F) * (a ⬝ᵥ b) := by
    rw [← evIHom_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_sum, map_mul, evIHom_invOf]
    simp only [evIHom_apply, evI_infAd]
  have e3 := infAd_evI _ hs
  rw [hi] at e3
  simp only [schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have e2' : (∏ᶠ v, φ v fun i => evFin F v ((x + fun i => infAd (a i)) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) :=
    finprod_congr fun v => by rw [e2 v]
  rw [e1, e2', ← e3, AddChar.compAddMonoidHom_apply]
  ring


open Classical in
theorem exists_finprod_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (y : κ → mixedEmbedding.mixedSpace F) :
    ∃ x : κ → AF F, (fun i => evI F (x i)) = y ∧ ∏ᶠ v, φ v (fun i => evFin F v (x i)) ≠ 0 := by
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  have hS := Filter.eventually_cofinite.mp hstd
  let T := hS.toFinset
  let xf : κ → AF F := fun i => ∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w i)
  have hxf1 : ∀ i, evI F (xf i) = 0 := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← evIHom_apply, map_sum]
    exact Finset.sum_eq_zero fun w _ => (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hxf2 : ∀ w i, w ∈ T → evFin F w (xf i) = p w i := fun w i hw => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [xf, map_sum]
    rw [Finset.sum_eq_single_of_mem w hw]
    · exact GlobalTheory.LatVac.evFin_liftV w _
    · intro x _ hx
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hx) _
  have hxf3 : ∀ w i, w ∉ T → evFin F w (xf i) = 0 := fun w i hw => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [xf, map_sum]
    exact Finset.sum_eq_zero fun x hx => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hw (by rw [h]; exact hx)) _
  refine ⟨fun i => infAd (y i) + xf i, funext fun i => ?_, ?_⟩
  · rw [← evIHom_apply, map_add (f := _), evIHom_apply, evIHom_apply, evI_infAd, hxf1, add_zero]
  · have hfin := GlobalTheory.PureFactor.mulSupport_finite φ hstd (fun i => infAd (y i) + xf i)
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (subset_refl _)]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    by_cases hw : w ∈ T
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = p w := funext fun i => by
        rw [map_add (f := _), evFin_infAd, zero_add, hxf2 w i hw]
      rw [this]
      simpa using hp w
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = 0 := funext fun i => by
        rw [map_add (f := _), evFin_infAd, zero_add, hxf3 w i hw, Pi.zero_apply]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (hS.mem_toFinset.mpr h)
      rw [this, hw', Set.indicator_of_mem (fun i => by simpa using (w.adicCompletionIntegers F).zero_mem)]
      exact one_ne_zero

end Aux2

theorem ei_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE ei ev hei hev hloc _
  classical
  refine ⟨B.ψ.compAddMonoidHom infAd, fun a => ?_, ?_⟩
  · show B.ψ (infAd a) = _
    rw [hP.base.std.2.2 _ (at_infAd a), evI_infAd]
  let u : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
      (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := fun w => (fun i => infAd (w.1 i), fun i => infAd (w.2 i))
  refine ⟨fun w => (fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i),
    fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)), fun w f g hg => ?_⟩
  have hM := hP.good
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : ∀ h : SInf F (Fin n × Fin d), e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei h) M₁.vac :=
    fun h => by
      rw [hloc h M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
      congr 1
      funext v
      exact (hev v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hM.std
  have key := hE.Heisenberg₂ (M.co.e.symm (u w)) _ hmem
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at key

  have hL : M.co.rho B.ψ (M.co.e.symm (u w)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
    funext x
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, u]
    rw [schr_pure, Prod.mk.eta, ← hg]
    rfl

  let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hc : ∀ s, c * infAd s = 0 := fun s => by
    refine Prod.ext ?_ ?_
    · change fstA F (c * infAd s) = 0
      rw [map_mul]
      exact zero_mul _
    · change sndA F (c * infAd s) = 0
      rw [map_mul, sndA_infAd, mul_zero]
  have hcu : c • u w = 0 := Prod.ext (funext fun i => hc _) (funext fun i => hc _)
  have hcz : c • M₁.co.e (M.co.e.symm (u w)) = 0 := by
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hcu, map_zero, map_zero]
  have hsnd : ∀ y : AF F, c * y = 0 → sndA F y = 0 := fun y hy => by
    have := congrArg (sndA F) hy
    have h1c : sndA F c = 1 := rfl
    rw [map_mul, map_zero, h1c, one_mul] at this
    exact this
  have hz : M₁.co.e (M.co.e.symm (u w)) =
      u ((fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i)), fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)) := by
    refine Prod.ext (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm) (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm)
    · exact congrFun (congrArg Prod.fst hcz) i
    · exact congrFun (congrArg Prod.snd hcz) i
  rw [hL, hpure, hpure] at key
  funext y
  obtain ⟨x, hx, hne⟩ := exists_finprod_ne M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std y
  have k := congrFun key x
  rw [Darboux.rho, hz] at k
  simp only [u] at k
  rw [schr_pure] at k
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hx] at k
  exact mul_right_cancel₀ hne k

end GlobalTheory.ArchIntertw
end
end

