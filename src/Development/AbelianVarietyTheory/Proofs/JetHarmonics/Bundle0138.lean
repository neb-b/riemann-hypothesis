module

public import Mathlib
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightRestDegreeAfterGapsBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliParamMemIntAddHalf
section
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace GlobalTheory

theorem capelliParam_mem_int_add_half : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → Q.IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, u i = (m : ℝ) + ((k : ℝ) - 1) / 2 := by
  intro k r Wp _ _ _ z π u hz hT hπ i hi
  obtain ⟨u₀, h₀⟩ := GlobalTheory.besType_hcParam k r Wp z π u hz hT hπ
  have ha := (GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW h₀).2
  rw [Finset.mem_Icc] at hi
  have h1 := GlobalTheory.SupNonzero.prod_eq hπ h₀ (-(u i : ℂ))
  have h2 : ∏ s : Fin k, (-(u i : ℂ) + (u (s.val + 1) : ℂ)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨i - 1, by omega⟩) ?_
    have : i - 1 + 1 = i := by omega
    simp [this]
  rw [h2] at h1
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h1
  have e : u i = u₀ t := by exact_mod_cast neg_add_eq_zero.1 ht
  obtain ⟨m, hm⟩ := ha t
  exact ⟨m, by rw [e]; linarith⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartDepthLeOfCharacterFlagsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDepth_le_of_characterFlags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_of_character_flags | exact GlobalTheory.CharDepth.nuLocC_le_of_character_flags | (intros; apply GlobalTheory.CharDepth.nuLocC_le_of_character_flags <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamilyFunctionalsStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_functionals : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → ∃ (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ), (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) ∧ (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) := by
  first | exact @GlobalTheory.exists_sideFam_both_sides | exact GlobalTheory.exists_sideFam_both_sides | (intros; apply GlobalTheory.exists_sideFam_both_sides <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParameters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem goodPage_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  intro D L Pm Tp hK T hP hC h5 hx hkb hlog j hj
  obtain ⟨hfirst, hw⟩ := _root_.GlobalTheory.FirstRows.first_rows_and_sizes D L Pm Tp hK j hj hx hkb
  obtain ⟨hr0, hr1⟩ := _root_.GlobalTheory.RestDegree.rest_degree_bounds D L Pm Tp hK T hP j hj
  have hgap := fun z => _root_.GlobalTheory.GoodDepth.Gap.gap_bounds D L Pm Tp hK j hj z (hw z).1
  have hj1 : 1 ≤ j := hj.1
  have hj2 : j ≤ D.R.m := hj.2
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hn : 0 < D.R.n := by unfold Ranks.n; have := D.R.m_le_f; omega
  have hf : 1 ≤ D.R.f := by unfold Ranks.f; omega
  have hr : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hDp : 1 ≤ Tp.Dp := by
    rw [Tp.Dp_eq]
    exact Nat.mul_pos hf (Nat.choose_pos hr)
  have h40 := Tp.TO_40
  have hTpos : (0 : ℝ) < Tp.TO := by exact_mod_cast TO_pos Tp
  have hx0 : 0 < L.sc.x := by linarith
  have hw'' : 0 < L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b Scale.X'
    have : (0 : ℝ) < D.R.n := by exact_mod_cast hn
    positivity
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hwj : ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
    intro z
    have h1 : j - 1 < D.R.m := by omega
    have h2 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := ⟨hj1, hj2⟩
    unfold NumDatum.w NumDatum.eQ wj
    rw [dite_eq_left h1, dite_eq_left h2]
    rfl
  refine ⟨⟨((Tp.Dp : ℝ) + 4) / Tp.TO, ?_, fun z => lt_of_lt_of_le hw'' (hw z).1, fun z => (hgap z).1,
    fun z => (hgap z).2, ⟨by positivity, ?_⟩, ?_, hr0, hr1⟩, fun τ _ => hfirst τ, ?_, ?_, hlog, ?_, ?_⟩
  · exact_mod_cast TO_pos Tp
  · rw [div_le_one hTpos]
    exact_mod_cast (by omega : Tp.Dp + 4 ≤ Tp.TO)
  · show ((D.R.k : ℝ) - 1) * (((Tp.Dp : ℝ) + 4) / Tp.TO) ≤ 5 * D.R.m
    have h := Tp.TO_Dk
    rw [div_le_iff₀ hm0] at h
    rw [← mul_div_assoc, div_le_iff₀ hTpos]
    have hD : (1 : ℝ) ≤ Tp.Dp := by exact_mod_cast hDp
    have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    nlinarith [mul_nonneg (sub_nonneg.2 hD) (sub_nonneg.2 hk)]
  · refine le_trans ?_ Tp.nW_win.1
    show 10 * (D.R.r : ℝ) * (D.R.f + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤ _
    unfold LevelStarExponents.nW
    have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      linarith
    gcongr
  · refine le_trans h5 ?_
    unfold Scale.L
    have := L.sc.eps_pos
    have := L.sc.ez_le
    exact Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)
  · intro p hp hin
    by_contra h
    have hin' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := hin
    have hne2 : p ≠ 2 := by
      rintro rfl
      have e : D.host.cls 2 = PrimeClass.ram2 := primeClass_two D.host.toHostRaw
      rw [e] at hin'
      simp at hin'
    have hp3 : p = 3 := by
      have h5 : p < 5 := not_le.1 h
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hne2
      · rfl
      · exact absurd hp (by norm_num)
    have hp4 : p ≤ D.host.splitBound := by
      rw [hp3]
      exact le_trans (Nat.le_floor (by exact_mod_cast h5)) L.split_tie
    have hjac := D.host.split_small p hp hne2 hp4
    rcases hin' with e | e
    · exact ((primeClass_eq_inert_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
    · exact ((primeClass_eq_signal_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
  · intro z z'
    rw [hwj, hwj]
    exact Pm.X''_ratio j j _ _ hj1 hj2 hj1 hj2

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.FormalSeriesBounds
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PairKernel

open GlobalTheory.KerPow

theorem mulA_finite_flat_surjective (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left := by
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hf : IsFinite (mulA P.A n).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1 gi S P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance
    inferInstance hf fun K _ _ t => (hgeo K t).1,
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

end Alg

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

end GlobalTheory.PairKernel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLawsUnitPeriod
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.GenusOne

variable {q : ℕ} [Fact q.Prime]

theorem norm_root_eq (M : Mdl q) (h : M.Ok) (δ : ℂ) (hδ : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) :
    ‖M.ι δ‖ = ‖M.ι M.c‖ ∧ ‖M.ι M.c‖ ≠ 0 := by
  obtain ⟨hc, -, -, -, -, -, hΔ, h4, h6⟩ := h
  have hιc : M.ι M.c ≠ 0 := (map_ne_zero M.ι).mpr hc
  refine ⟨?_, norm_ne_zero_iff.mpr hιc⟩

  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 4 hιc)] at h4
  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 6 hιc)] at h6
  have key : M.ι δ ^ 12 = M.ι M.c ^ 12 * M.W.Δ := by
    have e : M.ι δ ^ 12 = M.ι M.L.g₂ ^ 3 - 27 * M.ι M.L.g₃ ^ 2 := by
      rw [← map_pow, hδ]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, ← h4, ← h6]
    linear_combination (-(M.ι M.c ^ 12) / 1728) * M.W.c_relation
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, norm_pow, hΔ, mul_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hn

theorem norm_period (M : Mdl q) (ω : ℂ_[q]) (h : M.MChart ω) : ‖ω‖ * ‖M.ι M.c‖ = 1 := by
  obtain ⟨hok, h0, -, h1⟩ := h
  obtain ⟨-, -, -, -, -, -, hdu, -, hsmall⟩ := uw_elliptic_flow q M hok
  obtain ⟨han, -⟩ := hsmall 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, hcc, hder, -, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) h0

  have hd0 : ∀ f : ℂ_[q]⟦X⟧, constantCoeff (PowerSeries.derivative f) = coeff 1 f := by
    intro f
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hℓ : coeff 1 (C ω * logS : ℂ_[q]⟦X⟧) = ω := by
    simp [logS, coeff_C_mul, coeff_mk]
  have e : coeff 1 (hat M.ι (C ω * logS) M.u) = ω * M.ι M.c := by
    rw [← hd0, hder M.u han, map_mul, hd0, hℓ, hcc, hdu]
  rw [e, norm_mul] at h1
  exact h1

theorem thetaLaws_unit_period : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ), d.Prime → d % 16 = 7 → Split d q →
    δ ^ 12 = discr d → ∃ θ : ℂ → ℂ, IsTh d θ ∧ δ ≠ 0 ∧
      ∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ := by
  intro d q _ δ hd h16 hsp hδ
  obtain ⟨⟨L, hL, hLd⟩, θ, hθ⟩ := _root_.GlobalTheory.MomOne.exists_pair_and_isTh d hd h16
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact (Basic.discr_eq hL).2 (by rw [← hδ]; norm_num)
  refine ⟨θ, hθ, hδ0, fun ι => ?_⟩
  obtain ⟨M, hMι, hML, hok, a1, a2, a3, a4, a6⟩ := _root_.GlobalTheory.MomOne.exists_model d q ι L hd h16 hL
  subst hMι
  have hL' : IsOK d M.L := by rw [hML]; exact hL
  obtain ⟨ω₀, hω₀⟩ := _root_.GlobalTheory.MomOne.SplitChart.exists_mChart d q M hd h16 hsp hL' hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hgood⟩ := _root_.GlobalTheory.MomOne.Norm.exists_normalised_chart d q M ω₀ hd h16 hsp hL' hω₀
  have hδM : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2 := by rw [hML, hLd]; exact hδ
  obtain ⟨hn, -⟩ := norm_root_eq M hok δ hδM
  have hp := norm_period M (ω₀ * zc a) hω
  have hιδ : M.ι δ ≠ 0 := (map_ne_zero M.ι).mpr hδ0
  refine ⟨ω₀ * zc a * M.ι δ, by rw [norm_mul, hn]; exact hp, ?_⟩
  rw [mul_div_cancel_right₀ _ hιδ]
  have hU0 : U1 d 0 θ = θ := (_root_.GlobalTheory.MomOne.heisenbergOne d hd.pos).2.1 θ
  have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
  have hB := _root_.GlobalTheory.MomOne.theta_series_integral d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ
  refine ⟨fun t ht => ?_, _root_.GlobalTheory.MomOne.TranslateLaw.main d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ hgood,
    _root_.GlobalTheory.MomOne.TranslNorm.norm_law d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ⟩

  have := _root_.GlobalTheory.MomOne.TranslNorm.norm_law d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ 1 1 (fun _ => 1) (fun _ => 0) t 1
    (fun _ => h0) ht (by simpa [hU0] using hB)
  simpa [hU0] using this

end GlobalTheory.MomOne.GenusOne
end

