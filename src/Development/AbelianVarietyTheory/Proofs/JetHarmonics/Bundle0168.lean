module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0167
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProof
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨_root_.GlobalTheory.InertPackage.pkgInert hU E H Dw lv Xo c, (_root_.GlobalTheory.PkgConj.packages_conj hU E H Dw lv Xo c).1, _root_.GlobalTheory.SplitPackage.pkgSplit hU E H Dw lv Xo c,
    _root_.GlobalTheory.LargePkg.pkgZero hU E H Dw lv Xo c, (_root_.GlobalTheory.PkgConj.packages_conj hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwoStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChartDepth_le_residueChar_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_over_two | exact GlobalTheory.CharDepth.nuLocC_le_over_two | (intros; apply GlobalTheory.CharDepth.nuLocC_le_over_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem leaves_sup_span_lemmaS_of_formTieK : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc), (∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J), ∃ (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j) (p : ℕ) (_ : Algebra (recB h.toLawsCore).KO K), ∃ z act, ∃ ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), FormTieK (recPJ h j hj) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO O v i z act ∧ IsLevAct T.toTop h j (kaR Tp hK j) ℓ act ∧ LawsFull T ∧ (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) ∧ OneCover T.toTop j ∧ 0 < p ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j (kaR Tp hK j) ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) (kaR Tp hK j) ∧ WeightAlgebra.H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j)) → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
  intro hCI D L Pm Tp hK hinj EX K _ _ _ Bs Df S P _ _ oc O H
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J),
      (IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i) ∧
      (IsLatIn ⊤ (O.Th v i) ∧ IsLatIn ⊤ (O.ThK v i)) ∧
      (O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧
        O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i)) := by
    intro v i
    obtain ⟨T, h, j, hj, p, inst, z, act, ℓ, hFK, hA, hFull, hxi, hO, hp, hLat, hSp, hH⟩ := H v i
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.RunDepth.run_weights_sum D L Pm Tp hK j hj
    have hF := hFK.toFormTie (shortTh_fg _ hinj EX hp _ _ _ _ hLat.toIsLattice hH)
      (productsShort_rec hCI D T.toTop h j hj hFull.sh hO (hFull.lvA j hj 0) _ _ _ _ h1 h2 h3 h4 (kaWt_n _ _ _ _))
    exact ⟨supLattice_isLatIn_stable D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hLat
        (levAct_mem_Mlat D T.toTop h j hj _ P ℓ act hA),
      theta_spans_isLatIn D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hp h1 h2 h3 hLat.toIsLattice hSp hH,
      GlobalTheory.scaledSpan_clauses D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF h1 h2 h3 hH
        (levAct_theta hCI D T h j hj hFull hxi _ _ _ _ _ h1 h2 h3 h4 P ℓ act hA)⟩
  obtain ⟨v₀, -⟩ := exists_place3 K
  exact ⟨fun i => (key v₀ i).1,
    fun w _ => ⟨fun i => (key w i).2.1, fun i => (key (conjPl w) i).2.1⟩,
    fun w _ => ⟨fun i => (key w i).2.2, fun i => (key (conjPl w) i).2.2⟩⟩

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesOverLevel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthOverLevel

theorem lattice_terms_le (R N φ Φ e n n₁ r Dg g c : ℝ) (hR : 0 < R) (hN : 0 < N) (he : 0 < e) (hΦ : 0 ≤ Φ)
    (hΦe : Φ ≤ e * (R * N ^ 3 * φ)) (hn0 : 0 ≤ n₁) (hn : n₁ ≤ n) (hr0 : 0 ≤ r) (hr : r ≤ N) (hD : 1 ≤ Dg) (hg : 0 < g)
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g ≤ c) :
    (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by linarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have hD2 : 1 ≤ Dg ^ 2 := one_le_pow₀ hD
  have hn' : 0 ≤ n := hn0.trans hn
  have h1 : n₁ * r / 4 ≤ n * N * Dg ^ 2 := by
    have h2 : n₁ * r ≤ n * N := mul_le_mul hn hr hr0 hn'
    have h3 : n * N * 1 ≤ n * N * Dg ^ 2 := mul_le_mul_of_nonneg_left hD2 (by positivity)
    have h4 : 0 ≤ n₁ * r := by positivity
    linarith
  calc (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e = (n₁ * r / 4 + 2 * Dg ^ 2) * Φ / g / e := by
        field_simp
    _ ≤ (n * N * Dg ^ 2 + 2 * Dg ^ 2) * (e * (R * N ^ 3 * φ)) / g / e := by gcongr
    _ = R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g * φ := by field_simp
    _ ≤ c * φ := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vLa_sWt {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    sWt B hinj EX w ≠ 0 ∧ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 ∧
      vLa la ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) = vLa la ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hnd : ¬ D.host.g i ∣ D.host.condN := fun h => by
    have hc : D.host.g i % D.host.condN = 1 := D.ntypes.g_cond i
    have h1 := Nat.mod_mod_of_dvd (D.host.g i) h
    rw [hc, Nat.mod_self, Nat.mod_eq_of_lt (D.host.g_prime i).one_lt] at h1
    exact one_ne_zero h1
  have hl : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hnn : nnW B hinj EX w ≠ 0 := by
    have hπ : ∀ k, iE D hinj B (EX.piG k) ≠ 0 ∧ iE D hinj B (piBarO EX k) ≠ 0 := by
      intro k
      rw [← mul_ne_zero_iff, ← map_mul, RPfVal.piG_mul_bar, map_natCast]
      exact Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
    exact Finset.prod_ne_zero_iff.2 fun k _ => mul_ne_zero (pow_ne_zero _ (hπ k).1) (pow_ne_zero _ (hπ k).2)
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn (NumberField.RingOfIntegers.coe_eq_zero_iff.1 h)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN : pPow D (c2 D w) (cHalf w) (cHalf w) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  refine ⟨mul_ne_zero hnn (Nat.cast_ne_zero.2 hN), hnn0, ?_⟩
  have hc : ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO (_ * _) = _
    rw [map_mul, map_natCast]
  rw [hc, Crude.crv_vLa_mul la hnn0 (Nat.cast_ne_zero.2 hN), hP, RPfVal.vLa_pPow la D.host.QS_pos.ne' hq hd, hl,
    Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (fun h => hnd (h.trans D.host.QS_dvd_condN)),
    if_neg (D.host.ne_q_of_not_dvd hnd), if_neg (D.host.ne_d_of_not_dvd hnd)]
  simp

theorem nusOf_of_mem {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (w : WeightFamilies.Wt D j) (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    nusOf B w nu la = (ramOverZ la : ℝ) * (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) := by
  have h : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal := ⟨i, hg⟩
  have h1 : D.host.g (Classical.choose h) = D.host.g i :=
    ((RPfVal.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec h)).symm.trans
      ((RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg)
  unfold nusOf
  rw [dite_eq_left h, h1, H1algLink.eWL_eq]

theorem wtA_antitone {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) : Antitone fun i => wtA w (τ, i) := by
  intro i i' hii
  unfold wtA
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hii
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hii
    · exact le_rfl

theorem depth_le_over_level : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro hHT D T h j hj hinj EX w c hO hR la i hg y
  letI := T.Q.H.starRing
  obtain ⟨hlast, hn, hDg, hc0, hc⟩ := hR
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ, b, hb1, hb2⟩, hr, hM0, hjm, hΦe⟩ :=
    GlobalTheory.ShortBasisAt.exists_shortBasis D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hphi : (recPJ h j hj).phiC la (PtV.mk la ho z hz (imgV y) hl) = (recPJ h j hj).phiC la y := rfl
  rw [hphi] at hΦe
  have hM := h.toLawsCore.toLawsM
  obtain ⟨hDF, -, hpos, -, -, hf1, hr1, hrank⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore hM.pins j hj w
  have hD1 := (hpos hlast).2
  have hpq := ((GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins).2.2.2.2.2.2 j hj).1
  obtain ⟨-, hst, hMb, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore hM EX
  have hMb := hMb hO
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  obtain ⟨i', hne, hMg, hMb', hα⟩ : ∃ i' : Fin 2, D.host.g i ≠ D.host.g i' ∧ T.Q.l.M = D.host.g i' * D.host.g i ∧
      T.Q.l.Mb = Ideal.span {piBarO EX i * piBarO EX i'} ∧
      star (piBarO EX i) * star (piBarO EX i') = EX.piG 0 * EX.piG 1 := by
    have hs : ∀ k, star (piBarO EX k) = EX.piG k := fun k => by rw [← (hst k).1, star_star]
    have hLM := level_M T.toCore hM
    fin_cases i
    · exact ⟨1, D.host.g_ne, hLM.trans (mul_comm _ _), hMb, by rw [hs, hs]; rfl⟩
    · exact ⟨0, D.host.g_ne.symm, hLM, by rw [hMb, mul_comm]; rfl, by rw [hs, hs, mul_comm]; rfl⟩
  have hres : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hvg : vV S.V ((D.host.g i : ℕ) : S.Fr) = (e : ℤ) * ramOverZ la := by
    rw [← map_natCast io, ho.2, ← hres, Crude.crv_vLa_char]
  have hnu : ¬ IsUnit ((D.host.g i : ℕ) : S.V) := by
    refine not_isUnit_of_vV_ne_zero S _ ?_
    rw [hvg]
    exact mul_ne_zero (Nat.cast_ne_zero.2 ho.1.ne') (Nat.cast_ne_zero.2 (H1algLink.ramOverZ_ne_zero la))
  have hsp := GlobalTheory.LevelSplit.splitsIn_level_prime D i
  have hg' : (0 : ℝ) < D.host.g i' := by exact_mod_cast (D.host.g_prime i').pos
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hnr : 2 * D.R.r ≤ w.n := le_trans (by nlinarith) hn
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < D.host.g i' := by
    by_cases hlt : j < D.R.m
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)) (hc hlt i').1
    · rw [(hjm (not_lt.1 hlt)).1, mul_zero]; exact hg'
  have hA := GlobalTheory.T.theta_generators_least_value_over_level_prime hHT _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ hb1 hb2 (D.host.g i) (D.host.g i') (D.host.g_prime i) (D.host.g_prime i') hne hMg
    (piBarO EX i) (piBarO EX i') (hst i).2 (hst i').2 hMb' hsp.1 hsp.2 hnu (wtA w) w.n e
    (wtA_antitone w) (by rw [hpq]; exact hnr) (by omega) ho.1
    (by rw [hDF]; have := hDg i; omega) (by rw [hDF]; exact hDg i') (by rw [hDF]; exact hDM)
  obtain ⟨hs0, hnn0, hsv⟩ := vLa_sWt (recB h.toLawsCore) hinj EX w la i hg
  have hN : nval S.V e (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
      (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
      (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    have h1 : (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
        (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
        io ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
      rw [← GlobalTheory.PtTie.nrm_eq_nnW D T h j hj hinj EX w, hα]
      unfold nrm
      simp only [map_prod, map_pow]
    rw [h1, nval_of_ne ((map_ne_zero io).2 hnn0), ho.2]
    refine congrArg (fun x : ℝ => (x : EReal)) ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ he.ne']
    exact congrArg (fun x : ℤ => (x : ℝ)) hsv.symm
  rw [hN, hDF, hpq, hvg] at hA
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) +
        (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    exact GlobalTheory.DepthRule.depth_le_scaled_value D T h j hj w hlast _ hs0 la y f hf
  refine hdep.trans (le_trans hA (EReal.coe_le_coe_iff.2 ?_))
  rw [nusOf_of_mem (recB h.toLawsCore) w _ la i hg, add_assoc, add_div]
  refine add_le_add (le_of_eq ?_) ?_
  · push_cast
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ he.ne']
  · by_cases hlt : j < D.R.m
    · have hm := D.R.two_le_m
      have hf' : (0 : ℝ) < D.R.f := by exact_mod_cast hf1
      have hm' : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      refine lattice_terms_le (rr0 D) (2 * D.R.f * D.R.m) _ Φ e w.n _ r _ _ c ?_ (by positivity) he hΦ hΦe
        (Nat.cast_nonneg _) (by exact_mod_cast (by omega : D.R.r ≤ w.n)) (Nat.cast_nonneg _) (by exact_mod_cast hr)
        (by exact_mod_cast hD1) hg' (hc hlt i').2
      unfold rr0
      have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
        abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
      have hk : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
      positivity
    · have h0 : (recPJ h j hj).phiC la y = 0 := by
        unfold WeightAlgebra.PJ.phiC
        rw [if_neg hlt]
      rw [h0, (hjm (not_lt.1 hlt)).2]
      simp

end GlobalTheory.DepthOverLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesPrimeToLevel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthPrimeToLevel

theorem isUnit_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h1 := RPfVal.vLa_int_not_mem la hN
  have h2 : (((N : ℕ) : 𝓞 K) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [h2] at h1
  have h3 := ho.2 (N : K)
  rw [h1, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem rootDiscriminantDegreeRatio_pos (D : D7) : 0 < rr0 D := by
  unfold rr0
  have h1 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have h2 : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  positivity

theorem err_le (R N n Dg Φ φ c e g₀ g₁ : ℝ) (hR : 0 < R) (hN : 0 < N) (hn : 0 ≤ n) (he : 0 < e) (hg₀ : 0 < g₀)
    (hg₁ : 1 ≤ g₁) (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ e * (R * N ^ 3 * φ))
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g₀ ≤ c) : Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by nlinarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc hφ)
  calc Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ Dg ^ 2 * (e * (R * N ^ 3 * φ)) / (g₀ * 1) / e := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ := by field_simp
    _ ≤ _ := by
      have h1 : 0 ≤ N ^ 4 * n := by positivity
      have h2 : 0 ≤ N ^ 3 := by positivity
      gcongr
      linarith

theorem depth_le : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro D T h j hj hinj EX w c _ hrun la hg y
  letI := T.Q.H.starRing
  obtain ⟨hlp, hn, h4, hc0, hc⟩ := hrun
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ0, b, hb1, hb2⟩, -, hM0, hjm, hΦ⟩ :=
    GlobalTheory.T.exists_short_basis_uniformization_lattice D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hΦ' : Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la y) := hΦ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M T.toCore h.toLawsCore.toLawsM
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S.V) := by
    refine isUnit_natCast la S _ e ho _ ?_
    rw [hM, Nat.cast_mul]
    intro hm
    rcases la.isPrime.mem_or_mem hm with h1 | h1
    · exact hg 0 h1
    · exact hg 1 h1
  have hf1 : 1 ≤ D.R.f := by
    have h1 := GlobalTheory.DepthLink.finrank_host D
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hm2 := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ w.n := le_trans (Nat.mul_pos (by omega) hr1) hn
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ D.host.g 0 * D.host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by rw [hM]; exact_mod_cast hle
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < (T.Q.l.M : ℕ) := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · exact ((mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)).trans_lt (hc hjm' 0).1).trans_le hle'
    · rw [(hjm hjm').1, mul_zero]; linarith
  have hnum : (WeightAlgebra.DF w : ℝ) ^ 2 * Φ / (T.Q.l.M : ℕ) / e ≤ c * (recPJ h j hj).phiC la y := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · rw [hM, Nat.cast_mul]
      have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
      exact err_le (rr0 D) _ w.n _ Φ _ c e _ _ (rootDiscriminantDegreeRatio_pos D) (by positivity) (Nat.cast_nonneg _) he' (by linarith)
        (by linarith) hΦ0 hΦ' (hc hjm' 0).2
    · unfold WeightAlgebra.PJ.phiC
      rw [(hjm hjm').2, if_neg (not_lt.2 hjm')]
      simp
  have hA := GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ0 hb1 hb2 α hα1 hα2 hMu (wtA w) w.n (WeightAlgebra.DF w) e hn1 ho.1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.DF_wtA_le _ _) (by rw [hM]; exact (h4 0).trans hle) hDM
  have hB := (GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn la).2.2.2.2 S io e ho z hz C
  have hsW := RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX w la hg
  have hs0 : sWt (recB h.toLawsCore) hinj EX w ≠ 0 := by
    refine mul_ne_zero (fun h0 => RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX w la hg ?_) ?_
    · rw [h0]; exact la.asIdeal.zero_mem
    · have hq : D.host.q.Prime := D.host.hyp.1
      have hd : D.host.d.Prime := D.host.hyp.2.1
      exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
        (pow_ne_zero _ hd.ne_zero))
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) + (((ramOverZ la : ℝ) * clOf w la : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    refine (_root_.GlobalTheory.DepthRule.depth_le_scaled_value D T h j hj w hlp _ hs0 la y f hf).trans (le_of_eq ?_)
    exact congrArg (fun x : ℝ => (x : EReal) + vAtV y f) hsW
  have hnu : nusOf (recB h.toLawsCore) w (nuWt T w) la =
      (ramOverZ la : ℝ) * nuWt T w la + (ramOverZ la : ℝ) * clOf w la := by
    unfold nusOf
    rw [dite_eq_right (fun ⟨i, hi⟩ => hg i hi), ← mul_add, ← H1algLink.eWL_eq la]
    rfl
  refine hdep.trans ?_
  rw [hnu, add_right_comm, EReal.coe_add, EReal.coe_add]
  exact add_le_add (hA.trans (add_le_add hB (EReal.coe_le_coe_iff.2 hnum))) le_rfl

end GlobalTheory.DepthPrimeToLevel
end
end

