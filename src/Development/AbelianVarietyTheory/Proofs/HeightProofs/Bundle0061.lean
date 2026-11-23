module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem exists_hostK : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  intro R H
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hb : (H.φ₀ H.sqrtMinusD) ^ 2 = -(H.d : ℂ) := by
    have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
    rw [← map_pow, h, map_neg, map_natCast]
  let σ : H.K →ₐ[ℚ] ℂ := H.φ₀.toRatAlgHom.comp H.K.val
  let e : H.K ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have hNF : NumberField σ.fieldRange := NumberField.mk
  have h2 : Module.finrank ℚ σ.fieldRange = 2 :=
    e.toLinearEquiv.finrank_eq.symm.trans
      (Formalism.FrobeniusOrbits.SplitK.finrank_K hd.pos (H.sqd_sq))
  let r : σ.fieldRange := ⟨H.φ₀ H.sqrtMinusD, ⟨Formalism.FrobeniusOrbits.SplitK.bK H.sqrtMinusD, rfl⟩⟩
  have hr : r ^ 2 = -(H.d : σ.fieldRange) := by
    apply Subtype.ext
    simpa [r] using hb
  have h4 : H.d % 4 = 3 := by omega
  have hD : discr σ.fieldRange = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 hd.squarefree h4 hr
  have hTC : IsTotallyComplex σ.fieldRange := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    let ψ := InfinitePlace.embedding_of_isReal hv
    have h1 : ψ r ^ 2 = -(H.d : ℝ) := by rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg (ψ r)]
  obtain ⟨x, -, hx, -, hgen, -⟩ := ringOfIntegers_sqrt_neg_three_mod_four H.d hd.squarefree h4 σ.fieldRange h2 r hr
  have hx' : ((x : σ.fieldRange) : ℂ) = (1 + H.φ₀ H.sqrtMinusD) / 2 := by
    have := congrArg (fun y : σ.fieldRange => (y : ℂ)) hx
    simp only [r] at this
    push_cast at this
    have e2 : ((2 : σ.fieldRange) : ℂ) = 2 := rfl
    rw [e2] at this
    linear_combination this / 2
  have hc : ∀ m n : ℤ, ((((m : 𝓞 σ.fieldRange) + n * x : 𝓞 σ.fieldRange) : σ.fieldRange) : ℂ) =
      m + n * ((1 + H.φ₀ H.sqrtMinusD) / 2) := fun m n => by
    rw [← hx']
    simp
  refine ⟨σ.fieldRange, hNF, hTC, h2, hD, by omega, ?_, fun z => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : H.E), rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, hc s.1 s.2⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    exact ⟨(m, n), hc m n⟩
  · rw [H.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
section
set_option autoImplicit false

namespace GlobalTheory.FinalJoin.RecordRun

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem exists_pageRun_record_sub_four : ∃ CK : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → ∀ (B : WeightFamilies.Prov D) (Q : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B Q j), InR D j → OPO L B → PageRun L X ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP L.Ct (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) :=
  ⟨10, fun _ _ _ T hK S hCnW hg hx hC hCZ B Q _ X hj hO =>
    pageRun_record T hK S hCnW hg hx hC hCZ B Q hj.1 hj.2 X hO⟩

end GlobalTheory.FinalJoin.RecordRun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
section
noncomputable section

namespace GlobalTheory.FinalJoin2.ReadTwist

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val (D : D7) (y : (AfE D)ˣ) :
    ((cjFin D y : (AfE D)ˣ) : AfE D) = GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin
  rw [h]
  rfl

theorem normOne_iff {D : D7} (x : (AfE D)ˣ) :
    NormOne x ↔ (x : AfE D) * GlobalTheory.NormOneChar.bar (cF D) (x : AfE D) = 1 := Iff.rfl

theorem congOne_iff {D : D7} (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ GlobalTheory.NormOneChar.congOne (cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem cF_cF (D : D7) (y : D.host.E) : cF D (cF D y) = y := star_star y

theorem exists_rat {D : D7} (x : (AfE D)ˣ) (a : D.host.E) (h : (x : AfE D) = 1 ⊗ₜ a) (hn : NormOne x) :
    ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := by
  have key : ∀ b : D.host.E, b ≠ 0 → (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D b) =
      GlobalTheory.NormOneChar.diag D.host.F D.host.E b →
      ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := fun b hb e => by
    refine ⟨(GlobalTheory.NormOneChar.isUnit_diag D.host.F D.host.E hb).unit, b, rfl, eq_div_iff_mul_eq'.2 (Units.ext ?_)⟩
    rw [Units.val_mul, cjFin_val]
    exact e
  have hx : (x : AfE D) = GlobalTheory.NormOneChar.diag D.host.F D.host.E a := h
  by_cases ha : 1 + a = 0
  · have hc : cF D ≠ 1 := by
      have : cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [this]
      exact IsCMField.complexConj_ne_one _
    obtain ⟨z, hz⟩ : ∃ z, cF D z ≠ z := by
      by_contra h0
      push_neg at h0
      exact hc (AlgEquiv.ext h0)
    refine key (z - cF D z) (sub_ne_zero.2 hz.symm) ?_
    rw [hx, ← map_mul, map_sub, cF_cF]
    congr 1
    linear_combination (cF D z - z) * ha
  · refine key (1 + a) ha ?_
    have h1 : (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D a) = 1 := by
      have := (normOne_iff x).1 hn
      rw [h] at this
      rw [h]
      exact this
    rw [map_add (f := _), map_one, map_add (f := _), map_add (f := _), map_one, mul_add, h1, ← hx, mul_one, add_comm]

theorem cong_div {D : D7} (N : ℕ) (y : (AfE D)ˣ) (hu : IntUnit y) (hy : CongOne N y) :
    CongOne N (y / cjFin D y) ∧ NormOne (y / cjFin D y) := by
  have hv : ((y / cjFin D y : (AfE D)ˣ) : AfE D) =
      (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
    rw [div_eq_mul_inv, ← map_inv, Units.val_mul, cjFin_val]
  have h1 : (y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := Units.mul_inv y
  have h2 : GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := by
    rw [← map_mul, h1, map_one]
  rw [← congOne_iff]
  obtain ⟨-, hi⟩ := hu
  obtain ⟨w, hw, e⟩ := hy
  rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers] at hi hw
  rw [nsmul_eq_mul] at e
  have e' := congrArg (GlobalTheory.NormOneChar.bar (cF D)) e
  rw [map_sub, map_one, map_mul, map_natCast] at e'
  have hi' := GlobalTheory.NormOneChar.bar_mem (cF D) hi
  have hw' := GlobalTheory.NormOneChar.bar_mem (cF D) hw
  refine ⟨⟨(w - GlobalTheory.NormOneChar.bar (cF D) w) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D),
    mul_mem (sub_mem hw hw') hi', ?_⟩, ?_⟩
  · rw [hv]
    linear_combination (GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D)) * (e - e') + h2
  · rw [hv, map_mul, GlobalTheory.NormOneChar.bar_bar _ (cF_cF D)]
    linear_combination ((y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D)) * h2 + h1

theorem exists_xiOK_xiTilde : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  intro D p de hp h
  obtain ⟨h90, hfix, hcong⟩ := _root_.GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpp.2 (by norm_num)
  let q : (AfE D)ˣ →* (AfE D)ˣ := MonoidHom.id _ / cjFin D
  obtain ⟨xi, hxi⟩ := GlobalTheory.PrimaryCharacter.exists_factor_of_ker_le q de fun x hx => by
    have h1 : x = cjFin D x := div_eq_one.1 hx
    obtain ⟨a, ha⟩ := hfix x h1.symm
    exact h.real x a ha
  have ht : XiTilde xi de := hxi
  refine ⟨xi, ⟨fun x a ha hn => ?_, fun x hn hc => ?_, ?_, ?_, fun x hn => ?_⟩, ht⟩
  · obtain ⟨y, b, hb, rfl⟩ := exists_rat x a ha hn
    rw [ht, h.rat y b hb]
  · obtain ⟨y, hy, hyc, rfl⟩ := hcong p _ x hpp.1 hp2 (Dvd.intro_left _ rfl)
      (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hpp.1.pos) hn hc
    rw [ht, h.tame y hy hyc]
  · obtain ⟨y, hy, hyc, hne⟩ := h.ram
    obtain ⟨c1, c2⟩ := cong_div _ y hy hyc
    exact ⟨_, c2, c1, by rwa [ht]⟩
  · obtain ⟨m, hm, hf⟩ := h.fin
    refine ⟨m, hm, fun x hn => ?_⟩
    obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht, hf]
  · obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht]
    exact h.val y

end GlobalTheory.FinalJoin2.ReadTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_compactUnitaryFourier_value_one : ∀ {n : ℕ} (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ), (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ g : KG ε → ℂ, Continuous g → ∀ b : ℕ → ℝ, Summable b → (∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) → HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  first | exact @GlobalTheory.KFourier.hasSum_kFourier | exact GlobalTheory.KFourier.hasSum_kFourier | (intros; apply GlobalTheory.KFourier.hasSum_kFourier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open scoped IntermediateField

theorem scale_le_rank {D : D7} {L : SizeData₂ D} (S : SizesAt L) : L.sc.x ≤ (D.R.r : ℝ) := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
  exact (h1.trans S.2.2.1.1).trans (Pm.k_le_r D)

theorem hostSz_of_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (_Tp : ParamsT D L Pm), SizesAt L →
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x →
    HostSz D.host L.sc.L ∧ (Sz (FO D) (poR D.R L.sc.L) (poR D.R L.sc.L) → FieldSmall D L) := by
  intro D L P _ S hg hx
  have hL := Pm.one_le_L L
  have h6 := Pm.six_le_r D
  have hf := Pm.two_le_f D
  refine ⟨⟨?_, ?_, ?_, hg, P.pde_log, ?_⟩, fun h => h.2⟩
  · have h : ((62 : ℕ) : ℝ) ≤ D.R.r := le_trans (by norm_num) (hx.trans (scale_le_rank S))
    exact_mod_cast h
  · have h1 := Pm.log_r_le P
    have h2 : Real.log 2 ≤ Real.log (D.R.r : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  · linarith [Pm.log_f_le P]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypotheses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨hB, G, Gc, PH, Prw, Pet, Pd, hN, hF, hP⟩ := h
  obtain ⟨n, h1, h2, h3⟩ := secNorm_of_netIn D B P j X large₂ K ka Pd hN
  obtain ⟨G', hF', hP'⟩ := GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n G Gc PH Prw Pet
    Pd _ hF hP
  exact ⟨n, baseIn_secNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n hB, h1, h2,
    G', Gc, PH, Prw, Pet, Pd, h3, hF', hP'⟩

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PeterssonSquareIntegrableDefiniteOfLaws
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.L2

theorem norm_complexEmbedding_traceElement_const (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem petersson_squareIntegrable_definite_of_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans
    (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)

end GlobalTheory.FinalJoin2.L2
end

