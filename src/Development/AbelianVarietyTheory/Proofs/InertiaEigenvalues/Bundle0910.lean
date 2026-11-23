module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0412
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceIdempotentEqCompletionEmbeddingOne
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.IdemIota


set_option maxHeartbeats 800000 in
theorem toCompl_map_mem {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ intAE D) :
    GlobalTheory.LFun.toCompl h (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) z)
      ∈ w.adicCompletionIntegers D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, rfl⟩ := hz
    have e2 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)
        (b ⊗ₜ[D.host.F] (x : D.host.E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q b ⊗ₜ[D.host.F] (x : D.host.E) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e2]
    exact GlobalTheory.LFun.InertChart.toCompl_mem h (GlobalTheory.AdelicU.tmul_mem_intLoc (hb q) x)
  | zero =>
    rw [map_zero (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_zero (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).zero_mem
  | add y y' _ _ h1 h2 =>
    rw [map_add (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_add (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).add_mem _ _ h1 h2
  | neg y _ h1 =>
    rw [map_neg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_neg (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).neg_mem _ h1

theorem cw_mem_integers {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) {a : AE D} (ha : finPart D a ∈ intAE D) :
    GlobalTheory.Core.Rk.SWQ.cw h a ∈ w.adicCompletionIntegers D.host.E := by
  have e : GlobalTheory.Core.Rk.SWQ.cw h a = GlobalTheory.LFun.toCompl h
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) (finPart D a)) := by
    show GlobalTheory.LFun.toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E q a) = _
    congr 1
    clear ha
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e]
  exact toCompl_map_mem h _ ha

theorem idemAt_eq_iota_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P →
    ∀ ι : P.adicCompletion D.host.E →+ AE D,
      GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  intro D P e he ι hι
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := hι
  have hq : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hee : e * e = e := he.1.1
  have hec : e * cA D e = 0 := he.1.2.1
  have hne : e ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (he.2 x hx0).1 hx
    rw [h0, zero_mul, map_zero] at this
    exact this (zero_mem _)
  have idem01 : ∀ a : AE D, a * a = a → GlobalTheory.Core.Rk.SWQ.cw hq a = 0 ∨ GlobalTheory.Core.Rk.SWQ.cw hq a = 1 := fun a ha =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (by show GlobalTheory.Core.Rk.SWQ.cw hq a * GlobalTheory.Core.Rk.SWQ.cw hq a = GlobalTheory.Core.Rk.SWQ.cw hq a; rw [← map_mul, ha])
  have he' := GlobalTheory.ExportSeries.LatHalf.isIdemAt_conjPl he
  have hPP : Formalism.L2.DIV.conjPl P ≠ P := by
    intro hP
    rw [hP] at he'
    have h1 := GlobalTheory.Tow.idemAt_unique he' he
    apply hne
    rw [← hee]
    nth_rewrite 2 [← h1]
    exact hec
  obtain ⟨x, hxP, hxP'⟩ : ∃ x ∈ P.asIdeal, x ∉ (Formalism.L2.DIV.conjPl P).asIdeal := by
    by_contra hc
    push Not at hc
    exact hPP (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (Formalism.L2.DIV.conjPl P).isPrime.ne_top hc)).symm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP' (Formalism.L2.DIV.conjPl P).asIdeal.zero_mem
  have hint : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hxP' ((he'.2 x hx0).2 hc)
  have hc0 : GlobalTheory.Core.Rk.SWQ.cw hq (cA D e) = 0 := by
    have hm := cw_mem_integers hq hint
    rw [map_mul, GlobalTheory.Core.Rk.SecPar.cw_incA] at hm
    rcases idem01 (cA D e) (by rw [← map_mul, hee]) with h | h
    · exact h
    · exfalso
      have hv : Valued.v ((algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P)) ((x : D.host.E))⁻¹)
          = HeightOneSpectrum.valuation D.host.E P ((x : D.host.E))⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
      rw [h, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, hv] at hm
      have hv0 : HeightOneSpectrum.valuation D.host.E P (x : D.host.E) ≠ 0 := by simpa using hx0
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← not_lt,
        HeightOneSpectrum.valuation_lt_one_iff_mem] at hm
      exact hm hxP
  have he0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin (P.under (𝓞 D.host.F)) 1)) =
      e + cA D e := by
    rw [Formalism.IndefR.Fin.below_of_idemAt he]
    show _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (Formalism.IndefR.Fin.sglV _ 1))
    have hb : Formalism.IndefR.Fin.belowPl P = P.under (𝓞 D.host.F) := HeightOneSpectrum.ext rfl
    rw [hb]
    congr 2
  have h6e := h6 e
  rw [he0, add_mul, hee, mul_comm (cA D e) e, hec, add_zero, hc0, map_zero, map_zero, add_zero] at h6e
  rcases idem01 e hee with h | h
  · rw [h, map_zero] at h6e
    exact absurd h6e hne
  · rw [h] at h6e
    exact h6e

end GlobalTheory.IdemIota

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypotheses
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremB

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem declNoColumns : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, dc.col = ∅ := by
  intro D i _
  have hf := placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  exact ⟨⟨hf.toFinset, ∅, Finset.disjoint_empty_right _, fun v => by simp⟩, rfl⟩

theorem localDelta_le_cuspTwistDepth : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.vdel i ≤ (D.R.t : ℚ) := by
  intro D i hl
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : D.R.t ≤ D.R.t * D.R.r := Nat.le_mul_of_pos_right _ hr1
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  have hlt : D.R.t < D.nd.l i := by
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; rw [h4] at this; omega
    · have := D.host.qd_big.2; rw [h4] at this; omega
  have hl2 : D.nd.l i ≠ 2 := by have := D.R.rank_add_five_le; omega
  unfold NData.vdel
  rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i (UpperTheory.Small.not_mem_of_qd D.host hl)]
  have hk : ∀ k ∈ Finset.Ioo 0 D.R.t, ((1 : ℕ) : ℚ) + (padicValNat (D.nd.l i) k : ℚ) = 1 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))]
    simp
  rw [Finset.sum_congr rfl hk]
  simp

theorem rowBound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d

theorem tbConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := GlobalTheory.T.blockBound_qd_places_uniformConst

theorem bkAt : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd

theorem cycDegree_gt : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := _root_.GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic

theorem ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := _root_.GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes

theorem degBounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := _root_.GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge

theorem closingIneq : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := _root_.GlobalTheory.closing_numerical_inequality

theorem theoremB_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro D HW F r ρ large₂ ep CA C Qp hC hP hW hA hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar
  obtain ⟨h0, h1⟩ := _root_.GlobalTheory.LocalFieldsQD.main D
  intro i hl tw hbig π hπ hsF hsha
  have hQ : EmbeddingTypeJumps.AtQD i := ⟨⟨hl, tw⟩, ⟨π, (D.Zgood_tie i π).1 hπ⟩⟩
  obtain ⟨dc, hcol⟩ := declNoColumns D i hl
  obtain ⟨lenRow, hROW, hRowB⟩ := rowBound D r ρ large₂ ep CA h0 h1 hA hJump hFon hG2 hSet hLit hPar i hQ π hπ dc
  obtain ⟨cB, hTBi, hcB⟩ := tbConst D HW F r ρ large₂ ep h0 h1 hW hTB hJump hFon hG2 hSet hLit hPar i hQ π hπ
  have hAdm : TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow (fun _ => 0) cB := by
    refine ⟨hG1 i hQ, hG2 i hQ π hπ, hG3 i hQ π hπ, hG4 i hQ, hG5 i hQ, (hLit i hQ).1, hG6 i hQ,
      bkAt D hBK hLit i hQ, hTBi, hROW, ?_, (hSet i hQ π hπ).1, (hSet i hQ π hπ).2.1,
      (hSet i hQ π hπ).2.2.1, (hSet i hQ π hπ).2.2.2, (hLit i hQ).2.2.1, (GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main D i).1,
      (hLit i hQ).2.2.2.1, (hLit i hQ).2.2.2.2.1, (hLit i hQ).2.2.2.2.2⟩
    intro w hw hwc
    simp [hcol] at hwc
  obtain ⟨hg0, hg1⟩ := ne_typePrimes D h1 i hl
  have key := hN5 i π dc lenRow (fun _ => 0) cB hAdm hg0 hg1 (LargeLevelLemmas.zgoodSubsetZ i hπ) hsF hsha
  have hlw : ∀ w ∈ dc.row, TruncatedSeriesCountingIdentities.lenW i (ρ i) π dc lenRow (fun _ => 0) w = lenRow w := by
    intro w _
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_right (by simp [hcol])]
  rw [hcol] at key
  simp only [Finset.union_empty] at key
  rw [Finset.sum_congr rfl hlw] at key
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one, mul_zero, zero_mul, add_zero] at key
  have keyR := (Rat.cast_le (K := ℝ)).2 key
  push_cast at keyR
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hmr : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hl3 : 3 ≤ D.nd.l i := by
    have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; nlinarith
    · have := D.host.qd_big.2; nlinarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hLb : 1 < Real.log large₂.sc.b := by
    unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
    exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrowP : ∀ w ∈ dc.row, w ∈ placesOver D.host.E (D.nd.l i) := fun w hw => (dc.cover w).1 (Or.inl hw)
  obtain ⟨hSD, hSC⟩ := degBounds D h1 i hl dc.row hrowP
  have hSDr : ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) ≤ 2 * D.R.f := by exact_mod_cast hSD
  have hSCr : 2 * (dc.row.card : ℝ) ≤ ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) := by exact_mod_cast hSC
  set SD : ℝ := ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) with hSDdef
  set K := max CA 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  set X := 4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ) with hX
  have hl3r : (3 : ℝ) ≤ D.nd.l i := by exact_mod_cast hl3
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) := Real.logb_nonneg (by linarith) (by linarith)
    have := large₂.Sc_pos; have := large₂.etaSz_pos
    have : 0 ≤ 4 * large₂.sc.b / (D.nd.l i : ℝ) := by positivity
    positivity
  set Y := 2 * large₂.sc.b + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hRw : (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤
      K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by
    have hcard : (dc.row.card : ℝ) ≤ D.R.f := by linarith
    have hsum : (∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
        3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1)) =
        (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := by
      have : ∀ w ∈ dc.row, K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1 =
          (K * D.R.r * X + 3 * K * D.R.m * Y) * ((locDeg D.host.E w : ℕ) : ℝ) + (K * D.R.r * X + 1) := by
        intro w _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    have e1 : (K * D.R.r * X + 3 * K * D.R.m * Y) * SD ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) :=
      mul_le_mul_of_nonneg_left hSDr (by positivity)
    have e2 : (dc.row.card : ℝ) * (K * D.R.r * X + 1) ≤ D.R.f * (K * D.R.r * X + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤ ∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1) := Finset.sum_le_sum hRowB
      _ = (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := hsum
      _ ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) + D.R.f * (K * D.R.r * X + 1) := add_le_add e1 e2
      _ = K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by ring
  have hTb : (D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) ≤
      240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by
    have hs : ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) = (SD + 2 * dc.row.card) * cB := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    rw [hs]
    have h4 : SD + 2 * (dc.row.card : ℝ) ≤ 4 * D.R.f := by linarith
    have hc0 : (0 : ℝ) ≤ cB := by positivity
    have hS0 : (0 : ℝ) ≤ SD + 2 * (dc.row.card : ℝ) := by positivity
    calc (D.R.t : ℝ) * ((SD + 2 * dc.row.card) * cB) ≤ (D.R.t : ℝ) * ((4 * D.R.f) *
          (60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b)) := by
          gcongr
      _ = 240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by ring
  have hVd : 4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ) ≤ 4 * ((D.R.r : ℝ) + D.R.t) * D.R.t := by
    rw [hnV]
    have h1' : ((D.nd.vdel i : ℚ) : ℝ) ≤ D.R.t := by exact_mod_cast localDelta_le_cuspTwistDepth D i hl
    have : (0 : ℝ) ≤ D.R.r + D.R.t := by positivity
    nlinarith
  have hK2 := (hKill i hl tw (Or.inr (cycDegree_gt D h1 i hl)) π hπ).2
  simp only [EmbeddingTypeJumps.vZeta] at hK2
  push_cast at hK2
  have har := closingIneq CA C large₂.sc.b (D.nd.l i) large₂.Sc large₂.etaSz (∑ w ∈ dc.row, (lenRow w : ℝ))
    ((D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ))
    (4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ)) D.R.f D.R.r D.R.t D.R.m (EmbeddingTypeJumps.polyVal Qp D.R.f D.R.r D.R.t)
    hC (hP _ _ _) ht1 hf1 hmr hl3r large₂.Sc_pos.le large₂.etaSz_pos.le hb0 hLb hRw hTb hVd
  unfold EmbeddingTypeJumps.bndB
  push_cast
  linarith [keyR, hK2, har]

end GlobalTheory.TheoremB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrime
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

noncomputable section

namespace GlobalTheory.TraceIdem

theorem nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [nval]
  rw [nval_of_ne hz, EReal.coe_nonneg]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_nonneg_iff]
  have h1 : valV T.V z ≠ 0 := valV_ne_zero hz
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h' : 0 ≤ vV T.V z := by exact_mod_cast h
      unfold vV at h'
      rw [← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]; omega
    · linarith
  · intro h
    left
    refine ⟨?_, he'.le⟩
    have := (WithZero.log_le_log h1 one_ne_zero).2 h
    rw [WithZero.log_one] at this
    have h' : 0 ≤ vV T.V z := by unfold vV; omega
    exact_mod_cast h'

theorem trace_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  intro D T hL j hj σ hσ a n hD hspan hmu C hU hP la p hla m β hβ hβi y hφ
  obtain ⟨g, hgs, hgp, hgi⟩ := (_root_.GlobalTheory.CoverPullComb.exists_pull_comb_integral D T hL j hj σ hσ a n hD C hU hP la m β (fun k => (hβ k).1) y hφ)
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.TraceSmall.trace_le_one T.Q.c.F C.d.c₂.F p la hla m y
  refine ⟨N, fun b hb v hv => ?_⟩
  have hx : ∀ k, 0 ≤ v (β k) := fun k => hβi k v hv
  obtain ⟨⟨q, T0, io, e, ho, pt, hpt, eta, heta, rfl⟩, rfl⟩ := hv
  have hx' : ∀ k, valV T0.V (evI pt (β k)) ≤ 1 := fun k => (nval_nonneg_iff ho.1 _).1 (hx k)
  have hs : ∀ (s : Finset (Fin m)) (t : Fin m → T.Q.c.F),
      evI pt (∑ k ∈ s, t k • β k) = ∑ k ∈ s, io (t k) * evI pt (β k) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simpa using (isEval_evI pt).zero ()
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evI_add, evI_smul, ih]
  show 0 ≤ nval T0.V e (evI pt _)
  rw [nval_nonneg_iff ho.1, hs]
  exact hN b hb T0 hpt io e ho (fun k => evI pt (β k)) hx'
    (fun T' i e' τ e'' he' hi hT' hτ ho' =>
      _root_.GlobalTheory.CoverLiftVal.le_one_at_lift D T hL j hj σ C hU la a n m β g (fun k => (hβ k).1) hgs hgp y hgi T0 io pt hpt T' i e' τ e'' he' hi hT' hτ ho')

end GlobalTheory.TraceIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectorsStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  first | (exact @GlobalTheory.RSnmCells.unfolded_cells_eq) | (exact GlobalTheory.RSnmCells.unfolded_cells_eq) | (intros; apply GlobalTheory.RSnmCells.unfolded_cells_eq  <;> assumption)
end

