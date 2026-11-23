module

public import Mathlib
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumNatCastMemHeightOneSpectrumIff
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeries
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthSumRecord
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie GlobalTheory.PlusRec
namespace GlobalTheory.DepthSum

noncomputable def primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (p : ℕ) : ℝ :=
  (if p ∈ (Finset.range (N + 1)).filter Nat.Prime then (N : ℝ) / ((p : ℝ) - 1) else 0) +
    ((padicValNat p Q : ℝ) * a + (if p = q then b else 0) + (if p = d then b else 0)) +
    ∑ i : Fin 2, if p = g i then (N : ℝ) / ((g i : ℝ) - 1) else 0

theorem div_pred_nonneg (N : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg (by positivity) (by linarith)

theorem sum_primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (S : Finset ℕ)
    (hA : (Finset.range (N + 1)).filter Nat.Prime ⊆ S) (h2 : Q.primeFactors ⊆ S) (hS : ∀ p ∈ S, p.Prime) (hq : q ∈ S) (hd : d ∈ S) (hg : ∀ i, g i ∈ S) :
    ∑ p ∈ S, primeBound N Q q d g a b p * Real.log p =
      (N : ℝ) * (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) +
        (a * Real.log Q + b * Real.log q + b * Real.log d) + ∑ i : Fin 2, (N : ℝ) / ((g i : ℝ) - 1) * Real.log (g i) := by
  have hQ : ∑ p ∈ S, (padicValNat p Q : ℝ) * a * Real.log p = a * Real.log Q := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
    symm
    refine Finset.sum_subset_zero_on_sdiff h2 (fun p hp => ?_) fun p hp => ?_
    · obtain ⟨h3, h4⟩ := Finset.mem_sdiff.1 hp
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ (hS p h3), Finsupp.notMem_support_iff.1 (Nat.support_factorization Q ▸ h4)]; simp
    · rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp), Nat.padicValNat_def]; ring
  unfold primeBound
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_mul]
  rw [hQ, Finset.sum_ite_mem, Finset.inter_eq_right.2 hA, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', hq, hd, hg, if_true, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem depth_sum {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j)
    (hn : 2 * D.R.f * D.R.r ≤ w.n) (hL : Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (h0 : ∀ la, 0 ≤ nu la)
    (h1 : ∀ la, nu la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1)) (h2 : ∀ la, WeightAlgebra.DF w < resCharOf la → nu la = 0) :
    (∀ la, 0 ≤ nusOf B w nu la) ∧ (Function.support (nusOf B w nu)).Finite ∧
      (∑ᶠ la, |nusOf B w nu la| * lw B.KO la) ≤ WeightAlgebra.PN D large₂ * w.size := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hg := D.host.g_prime
  have hn1 : 1 ≤ w.n := by
    have hf : 1 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord from D.R.ord_pos)
      omega
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      unfold Ranks.r
      omega
    have : 1 ≤ 2 * D.R.f * D.R.r := Nat.mul_pos (by omega) hr
    omega
  have hpos : ∀ la, 0 ≤ nusOf B w nu la := by
    intro la
    unfold nusOf
    split_ifs with ha hb hc
    · rw [mul_div_assoc]
      exact mul_nonneg (by positivity) (div_pred_nonneg _ (hg _))
    all_goals exact mul_nonneg (by positivity) (add_nonneg (h0 la) (by positivity))
  set N := WeightAlgebra.DF w with hN
  set A := (Finset.range (N + 1)).filter Nat.Prime with hA
  set S : Finset ℕ := A ∪ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1}) with hS
  have hgS : ∀ i, D.host.g i ∈ S := by
    intro i
    fin_cases i <;> simp [hS]
  have e1 : ∀ p, 0 ≤ (if p ∈ A then (N : ℝ) / ((p : ℝ) - 1) else 0) := by
    intro p
    split_ifs with hp
    · exact div_pred_nonneg _ (Finset.mem_filter.1 hp).2
    · exact le_rfl
  have e2 : ∀ (p x c : ℕ), (0 : ℝ) ≤ (if p = x then (c : ℝ) else 0) := by
    intro p x c
    split_ifs <;> positivity
  have e3 : ∀ p i, 0 ≤ (if p = D.host.g i then (N : ℝ) / ((D.host.g i : ℝ) - 1) else 0) := by
    intro p i
    split_ifs with hp
    · exact div_pred_nonneg _ (hg _)
    · exact le_rfl
  have e4 : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      nu la ≤ (if resCharOf la ∈ A then (N : ℝ) / ((resCharOf la : ℝ) - 1) else 0) := by
    intro la
    split_ifs with hp
    · exact h1 la
    · refine (h2 la ?_).le
      by_contra hlt
      exact hp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), Crude.resCharOf_prime la⟩)
  have hsm : D.host.small ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    simp only [hS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | rfl | rfl | rfl | rfl
    exacts [(Finset.mem_filter.1 hp).2, (D.host.mem_small_iff.1 hp).1, hq, hd, hg _, hg _]
  have hQ : ∀ la : HeightOneSpectrum (𝓞 B.KO), ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
    fun la => (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
  have e5 : ∀ p : ℕ, (0 : ℝ) ≤ (padicValNat p D.host.QS : ℝ) * (c2 D w : ℝ) := fun p => by positivity
  have key := GlobalTheory.T.sum_finitePlaces_le_sum_over_primes B.KO (primeBound N D.host.QS D.host.q D.host.d D.host.g (c2 D w) (cHalf w)) S hSp ?_
    (nusOf B w nu) hpos ?_ ?_
  · refine ⟨hpos, key.1, key.2.trans ?_⟩
    rw [sum_primeBound _ _ _ _ _ _ _ S Finset.subset_union_left hsm hSp (by simp [hS]) (by simp [hS]) hgS]
    refine le_trans ?_ (_root_.GlobalTheory.PtTie.depth_sum_le_PN D large₂ j w hn1 hL)
    have := mul_le_mul_of_nonneg_left (_root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le N) (Nat.cast_nonneg (α := ℝ) N)
    linarith
  · intro p
    unfold primeBound
    exact add_nonneg (add_nonneg (e1 p) (add_nonneg (add_nonneg (e5 _) (e2 _ _ _)) (e2 _ _ _)))
      (Finset.sum_nonneg fun i _ => e3 p i)
  · intro la
    have s3 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i
    have a1 := e1 (resCharOf la)
    have a2 := e5 (resCharOf la)
    have a3 := e2 (resCharOf la) D.host.q (cHalf w)
    have a4 := e2 (resCharOf la) D.host.d (cHalf w)
    have a5 := e4 la
    unfold nusOf primeBound
    rw [H1algLink.eWL_eq]
    by_cases ha : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
    · rw [dite_eq_left ha, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hc := (H1algLink.prime_mem_iff la (hg _)).1 (Classical.choose_spec ha)
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i)
        (Finset.mem_univ (Classical.choose ha))
      rw [if_pos hc] at this
      linarith
    · rw [dite_eq_right ha]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      by_cases hb : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
      · rw [if_pos hb, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
        linarith
      · rw [if_neg hb]
        by_cases hc : ((D.host.q : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
        · rw [if_pos hc]
          rw [H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd] at hc
          rcases hc with hc | hc
          · rw [if_pos hc]
            linarith
          · rw [if_pos hc]
            linarith
        · rw [if_neg hc]
          linarith
  · intro la hla
    have hne : ∀ p ∈ S, p.Prime → ((p : ℕ) : 𝓞 B.KO) ∉ la.asIdeal := fun p hp hpp hm =>
      hla ((H1algLink.prime_mem_iff la hpp).1 hm ▸ hp)
    have hnA : resCharOf la ∉ A := fun h => hla (Finset.mem_union_left _ h)
    have a5 := e4 la
    rw [if_neg hnA] at a5
    unfold nusOf
    rw [dite_eq_right (fun ⟨i, hi⟩ => hne _ (hgS i) (hg i) hi), if_neg (fun h => hla (hsm ((hQ la).1 h))),
      if_neg (not_or.2 ⟨hne _ (by simp [hS]) hq, hne _ (by simp [hS]) hd⟩), le_antisymm a5 (h0 la)]
    simp

theorem depth_sum_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) w (nusOf (recB h.toLawsCore) w (nuWt T w)) ∧ ∀ (Nd : NormDatum (recB h.toLawsCore)), WeightedPrimeSumBoundAlt large₂ (Nd.X' (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) w (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro D T h j hj large₂ w hn hL
  have hb := GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn
  have key := depth_sum (recB h.toLawsCore) large₂ w hn hL (nuWt T w) (fun la => (hb la).2.1) (fun la => (hb la).2.2.1)
    (fun la => (hb la).2.2.2.1)
  exact ⟨key, fun _ => key⟩

end GlobalTheory.DepthSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsReducedBasisLePhiCy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.PhiTie

theorem logb_uniformiser {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) {ϖ : S.V} (hϖ : Irreducible ϖ)
    {C : Type} [NormedField C] (f : S.V →+* C) (hf : ∀ a, ‖f a‖ ≤ 1)
    (hp : ‖((WeightAlgebra.resCh la : ℕ) : C)‖ = ((WeightAlgebra.resCh la : ℕ) : ℝ)⁻¹) :
    ((e : ℝ) * ramOverZ la) * -Real.logb (WeightAlgebra.resCh la : ℕ) ‖f ϖ‖ = 1 := by
  have hpr := resCh_prime la
  have h0 : ((WeightAlgebra.resCh la : ℕ) : S.V) ≠ 0 := by exact_mod_cast hpr.ne_zero
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h1 := ho.2 ((WeightAlgebra.resCh la : ℕ) : K)
  rw [map_natCast, show vLa la ((WeightAlgebra.resCh la : ℕ) : K) = ramOverZ la from Crude.crv_vLa_char la,
    ← map_natCast (algebraMap S.V S.Fr), hu] at h1
  have hmax : (IsDiscreteValuationRing.maximalIdeal S.V).asIdeal = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have h2 : vV S.V (algebraMap S.V S.Fr (u * ϖ ^ n)) = n := by
    have hu1 : (IsDiscreteValuationRing.maximalIdeal S.V).intValuation (u : S.V) = 1 :=
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl _ _).2 fun hm =>
        (IsDiscreteValuationRing.maximalIdeal S.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm u.isUnit)
    rw [vV, valV, HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, hu1,
      HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hmax, _root_.one_mul, ← WithZero.exp_nsmul,
      WithZero.log_exp]
    simp
  have h3 : (n : ℝ) = (e : ℝ) * ramOverZ la := by exact_mod_cast h2.symm.trans h1
  have h4 := congrArg (fun a => Real.logb (WeightAlgebra.resCh la : ℕ) ‖f a‖) hu
  have hp1 : (1 : ℝ) < (WeightAlgebra.resCh la : ℕ) := by exact_mod_cast hpr.one_lt
  simp only [map_natCast, hp, map_mul, norm_mul, GlobalTheory.PeriodBalance.norm_unit f hf u, _root_.one_mul, map_pow, norm_pow,
    Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hp1] at h4
  rw [← h3]
  linarith

theorem unif_clauses {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} (S : CDVR) (x : Sp S.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp S.V))
    (I : GlobalTheory.EtaVal.IntSec Xo S.V x s G) (P : PELUnif (maximalIdeal S.V) G) :
    Nonempty (SABMap G G (spMap (RingHom.id S.V))) ∧ (∀ χ, PsiUnitOn P.D.toPre χ (abLocus G.G)) ∧ P.TorsionIso := by
  have hprop : IsProper I.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H S.V inferInstance G G I.t' hprop I.m2 I.m2
  let mI : SABMap G G (spMap (RingHom.id S.V)) := PullbackSections.sabMapCast ψ (by simp [spMap])
  obtain ⟨hLL, k2, k3, k4, k5⟩ := GlobalTheory.lawsAndExpansions
  have hA : AdmBase S.V (maximalIdeal S.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have htors := GlobalTheory.UT.torsionIso_of_pelUnif hLL k2 k3 k4 k5 E H S.V _ hA G P
  have hadm : GlobalTheory.LN.admitted S.V (maximalIdeal S.V) := by
    refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance,
      inferInstance, ?_⟩
    letI := Ideal.Quotient.field (maximalIdeal S.V)
    infer_instance
  have hop : IsOpen (abLocus G.G) := by
    refine GlobalTheory.UnifAfterExt.isOpen_of_range_generic_subset S.V _ ?_
    rintro _ ⟨x, rfl⟩
    exact (abLocus_pullback abLocusOne G.semi I.m2.cart.1 x).2 fun _ _ _ _ _ => inferInstance
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := hLL
  have hU := GlobalTheory.PsiAbelian.psiUnitOn_abLocus L₁ L₂ L₃ L₄ L₅ S.V _ hadm P.D P.A G.G G.semi P.U hop
  exact ⟨⟨mI⟩, hU, htors⟩

theorem exists_datAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} (Y : Model Xo c β₀)
    (la : HeightOneSpectrum (𝓞 c.F)) (hB : PointsOfFlagModel.BaseAt la β₀) (S : CDVR) (io : c.F →+* S.Fr) (e : ℕ)
    (ho : OverLa la S.V io e) (x : Sp S.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp S.V))
    (I : GlobalTheory.EtaVal.IntSec Xo S.V x s G)
    (hx : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (C : SCF (WeightAlgebra.resCh la)) (Pc : PointsOfFlagModel.PtC Y C) (eF : S.Fr →+* ↥C.S) (h1 : eF.comp io = Pc.fK)
    (h2 : ∀ a : S.V, ‖eF (algebraMap S.V S.Fr a)‖ ≤ 1)
    (h3 : ∀ a ∈ maximalIdeal S.V, ‖eF (algebraMap S.V S.Fr a)‖ < 1)
    (h4 : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (P : PELUnif (maximalIdeal S.V) G) (ϖ : S.V) (hϖ : Irreducible ϖ)
    (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) :
    ∃ (A : DatAt Y Pc) (g : A.Ylat ≃+ P.D.toPre.X),
      (∀ a b, ((Q (g a + g b) - Q (g a) - Q (g b) : ℤ) : ℝ) = (e : ℝ) * ramOverZ la * A.beta a b) ∧
      ∀ a, (Q (g a) : ℝ) = (e : ℝ) * ramOverZ la * (A.beta a a / 2) := by
  obtain ⟨⟨mI⟩, hU, htors⟩ := unif_clauses S x s G I P
  let f : S.V →+* intO ↥C.S := (eF.comp (algebraMap S.V S.Fr)).codRestrict _ h2
  obtain ⟨A, g, hg⟩ := GlobalTheory.EtaVal.datAt_of_uniformisation E H Dw l Xo c _ _ Y la hB S io e ho x s G
    I hx S (RingHom.id _) G mI P hU htors _ C Pc eF f h1 h4
    (fun _ => rfl) h3
  obtain ⟨Q', β, hQ', -, hβ, hβ2, hb⟩ := GlobalTheory.ValForm.main E H S.V G P ϖ hϖ _ fun _ => rfl
  obtain rfl : Q = Q' := funext fun χ => by
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main S.V P.D inferInstance χ).1
    exact hasVal_unique hϖ (GlobalTheory.ValForm.hasVal_coord (hQ χ) hr) (GlobalTheory.ValForm.hasVal_coord (hQ' χ) hr)
  have hinj : Function.Injective ((intO ↥C.S).subtype.comp f) :=
    eF.injective.comp (IsFractionRing.injective S.V S.Fr)
  have hlog := logb_uniformiser la S io e ho hϖ ((intO ↥C.S).subtype.comp f) h2 C.norm_p
  have key : ∀ a b, (e : ℝ) * ramOverZ la * A.beta a b = (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) (g a) (g b) := fun a b => by
    rw [hg, hb _ _ _ hinj h2, ← _root_.mul_assoc, hlog, _root_.one_mul]
  refine ⟨A, g.toAddEquiv, fun a b => ?_, fun a => ?_⟩
  · exact ((key a b).trans (hβ _ _)).symm
  · rw [← mul_div_assoc, key, hβ2]
    exact (mul_div_cancel_left₀ _ two_ne_zero).symm

theorem phiCy_nonneg {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) : 0 ≤ L.phiCy y := by
  unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
  refine Real.sInf_nonneg ?_
  rintro x ⟨l, -, h2, rfl⟩
  by_cases hb : L.beS y = 0
  · rw [hb]; simp
  · refine (h2 _ ?_ hb).le
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    · exact (L.be_pos y a ha).le

theorem exists_reduced_basis {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) :
    ∃ b : Module.Basis (Fin (L.dP y)) ℤ (L.Ylat y),
      (∀ i, L.be y (b i) (b i) / 2 ≤ D.host.rdE ^ 2 / (4 * D.R.f) * (L.dP y : ℝ) ^ 3 * L.phiCy y) ∧
      ∀ i z, |L.be y (b i) z| ≤ 2 * Real.sqrt (L.dP y) * (L.be y z z / 2) := by
  obtain ⟨w₀, hw⟩ := ConjugateMinimaInstance.scalar_frame_w_zero_exists D
  obtain ⟨κ, hκ, b₀, -⟩ := L.be_posDef y
  obtain ⟨b, h1, h2⟩ := gram_form_phi_holds D.host.E (fun z => D.host.conj z) (fun φ z => WeightFamilies.emb_conj D φ z)
    (ConjugateMinimaInstance.conj_ne D) w₀ hw (L.Ylat y) (L.beS y) ⟨κ, hκ, b₀, L.gram_posDef y b₀⟩
  refine ⟨b, fun i => (h1 i).trans (le_of_eq ?_), h2⟩
  have e1 : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
    rw [Formalism.BasicNotions.Host.rdE, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  rw [e1, hostSize_finrank]
  push_cast
  show _ * (L.dP y : ℝ) ^ 3 * L.phiCy y = _
  ring

theorem transfer_basis {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) {X X' : Type}
    [AddCommGroup X] [AddCommGroup X'] (g' : L.Ylat y ≃+ X') (g : X' ≃+ X) (β : X' → X' → ℝ) (Q : X → ℤ) (e m N : ℕ)
    (hrk : L.dP y ≤ N) (hg' : ∀ a b, β (g' a) (g' b) = L.be y a b)
    (hg1 : ∀ a b, ((Q (g a + g b) - Q (g a) - Q (g b) : ℤ) : ℝ) = (e : ℝ) * m * β a b)
    (hg2 : ∀ a, (Q (g a) : ℝ) = (e : ℝ) * m * (β a a / 2)) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) ℤ X), r ≤ N ∧
      (∀ i, (Q (b i) : ℝ) ≤ (e : ℝ) * (D.host.rdE ^ 2 / (4 * D.R.f) * (r : ℝ) ^ 3 * ((m : ℝ) * L.phiCy y))) ∧
      ∀ i z, |((Q (b i + z) - Q (b i) - Q z : ℤ) : ℝ)| ≤ 2 * Real.sqrt (N : ℝ) * Q z := by
  obtain ⟨b, hb1, hb2⟩ := exists_reduced_basis L y
  have hv : (0 : ℝ) ≤ (e : ℝ) * m := by positivity
  refine ⟨_, b.map (g'.trans g).toIntLinearEquiv, hrk, fun i => ?_, fun i x => ?_⟩
  · show (Q (g (g' (b i))) : ℝ) ≤ _
    rw [hg2, hg']
    exact (mul_le_mul_of_nonneg_left (hb1 i) hv).trans (le_of_eq (by ring))
  · obtain ⟨x₀, rfl⟩ := g.surjective x
    obtain ⟨x', rfl⟩ := g'.surjective x₀
    show |((Q (g (g' (b i)) + g (g' x')) - Q (g (g' (b i))) - Q (g (g' x')) : ℤ) : ℝ)| ≤ _ * (Q (g (g' x')) : ℝ)
    rw [hg1, hg2, hg', hg', abs_mul, abs_of_nonneg hv]
    refine (mul_le_mul_of_nonneg_left (hb2 i x') hv).trans ?_
    have hs : Real.sqrt (L.dP y) ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hrk)
    have h0 : 0 ≤ L.be y x' x' / 2 := by
      by_cases ha : x' = 0
      · subst ha; simp
      · exact (half_pos (L.be_pos y x' ha)).le
    have := mul_le_mul_of_nonneg_right hs (mul_nonneg hv h0)
    linarith

theorem exists_reduced_basis_le_phiCy : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), j < D.R.m → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (S : CDVR) (io : T.Q.c.F →+* S.Fr) (e : ℕ) (y : IntFr (T.Q.Xo j) T.Q.c S io), OverLa la S.V io e → y.IsAlg → ∀ eta, T.G.lies j la S io y eta →
 letI := T.Q.H.starRing
 ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c S io y) (P : PELUnif (maximalIdeal S.V) C.I.G) (ϖ : S.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → 0 ≤ (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy eta ∧ ∃ (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), r ≤ 2 * D.R.f * D.R.m ∧ (∀ i, (Q (b i) : ℝ) ≤ (e : ℝ) * (D.host.rdE ^ 2 / (4 * D.R.f) * (r : ℝ) ^ 3 * ((ramOverZ la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy eta))) ∧ ∀ i z, |((Q (b i + z) - Q (b i) - Q z : ℤ) : ℝ)| ≤ 2 * Real.sqrt ((2 * D.R.f * D.R.m : ℕ) : ℝ) * Q z := by
  intro D T h j hj hm la S io e y ho hy eta heta C P ϖ hϖ Q hQ
  letI := T.Q.H.starRing
  letI := io.toAlgebra
  obtain ⟨z, hrel, hz⟩ := heta hm
  have hl := h.lattice_condition j hj.1 hm la z ⟨S, io, e, y, ho, hy, hz⟩ eta hrel
  obtain ⟨hv, eF, h1, h2, h3, h4, -⟩ := hz
  have hB : PointsOfFlagModel.BaseAt la ((T.G.Tw j (WeightAlgebra.resCh la)).β z.1) := by
    have := ((h.tower j hj.1 hm _ (resCh_prime la)).1 z.1).1
    rwa [show z.1.1 = la from congrArg Subtype.val hv] at this
  have hd := exists_datAt _ la hB S io e ho y.1.x y.1.s C.I.G (GlobalTheory.EtaVal.IntSec.ofIntData C.I) y.1.x_over
    z.2.1 z.2.2.1 eF h1 h2 h3 h4 P ϖ hϖ Q hQ
  obtain ⟨hr, hjj⟩ := h.datum_condition j hj.1 hm
  have hrk : (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).dP eta ≤ 2 * D.R.f * D.R.m := by
    have hk := D.R.m_add_three_le_k
    have hj1 := hj.1
    refine ((T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).dP_le ?_ ?_ eta).trans
      (Nat.mul_le_mul_left _ ((min_le_right _ _).trans ?_)) <;>
    · simp only [hr, hjj, Ranks.sigW, Ranks.r]
      omega
  refine ⟨phiCy_nonneg _ _, hd.elim fun A hA => hA.elim fun g hg => (hl A).elim fun g' hg' => ?_⟩
  exact transfer_basis _ eta g'.toAddEquiv g A.beta Q e _ _ hrk hg' hg.1 hg.2

end GlobalTheory.PhiTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspFormsStatement
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mem_cuspForms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.LevelCusp.actLev_mem_cuspA | exact GlobalTheory.LevelCusp.actLev_mem_cuspA | (intros; apply GlobalTheory.LevelCusp.actLev_mem_cuspA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeriesStatement
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mem_thetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  first | exact @GlobalTheory.ThetaLevelMove.actLev_mem_th | exact GlobalTheory.ThetaLevelMove.actLev_mem_th | (intros; apply GlobalTheory.ThetaLevelMove.actLev_mem_th <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyUniformisedFormalChartAlgebraicPoint
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem nonempty_unifChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ∀ (p : ℕ) [Fact p.Prime] (X : ValExt T p), Nonempty (UnifChart Ch X) := by
  intro E _ _ _ H Dw l Xo c T io y Ch hy p _ X
  let _ := H.starRing
  obtain ⟨T', φ, t', m, hi, hf, -, -, P, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T Ch.I.G Ch.I.t' Ch.I.m2 _ Ch.I.m1 hy
  obtain ⟨ι', hl, hι⟩ := ValExt.exists_local_extension T T' φ hi hf p X
  obtain ⟨F', x', act', hF, hA, hc, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw l Xo c T io y Ch T' φ t' m
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map X.ι f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hι, RingHom.comp_apply]
  refine ⟨⟨T', ι', hl, t', P, F', x', hc, act', ha, ?_, fun a => ?_⟩⟩
  · funext i
    show MvPowerSeries.map ι' (F'.F i) = _
    rw [hF]
    exact key _
  · funext i
    show MvPowerSeries.map ι' (act'.act a i) = _
    rw [hA]
    exact key _

end GlobalTheory.CharDepth
end

