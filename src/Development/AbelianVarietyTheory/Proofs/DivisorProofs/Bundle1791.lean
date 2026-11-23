module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Counterexamples.ThetaValuation.UniformMultiplier
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
section
noncomputable section

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem rest_finPart {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add (f := _), hz0, add_zero]

theorem hasDerivAt_pure {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : ActsD (evI F) T f f₁) :
    ∀ x, HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 :=
  h _ (rest_finPart f φ hSB hstd)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

end GlobalTheory.ThetaFacInf.Fib

end

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

end GlobalTheory.ThetaFacInf.Fib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralTensorSwapIffMemIdealSubgroup
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IdealDict

open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem toE_bijective (D : D7) : Function.Bijective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective

theorem toE_inc (b : 𝓞 D.host.E) :
    toE D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  rw [← finQ_incA, toE_finQ]
  rfl

theorem inId_of_mem {𝔪 : Ideal (𝓞 D.host.E)} {y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hy : y ∈ hatId D 𝔪) : InId 𝔪 (toE D y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    have ht' := (toE_int_iff t).2 ht
    have h := Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _
      (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
    rw [RingHom.map_mul, toE_inc]
    exact ⟨_, h⟩
  | zero => rw [RingHom.map_zero]; exact ⟨zero_mem _, Ideal.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    rw [RingHom.map_add (f := _)]
    exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    rw [RingHom.map_neg]
    exact ⟨neg_mem h1, Submodule.neg_mem _ h2⟩

theorem exists_of_mem_idS {𝔪 : Ideal (𝓞 D.host.E)} {u : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hu : u ∈ Ideal.map (Formalism.L2.DIV.oToS D.host.F D.host.E) 𝔪) : ∃ y ∈ hatId D 𝔪, toE D y = u.1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩
  | zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [RingHom.map_add (f := _), e, e']
    exact (AddMemClass.coe_add _ a b).symm
  | smul s a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨t, ht⟩ := (toE_bijective D).2 s.1
    have htO : t ∈ OhE D := (toE_int_iff t).1 (by rw [ht]; exact s.2)
    refine ⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩
    have h1 := (toE D).map_mul t y
    rw [e, ht] at h1
    rw [smul_eq_mul]
    exact h1.trans (MulMemClass.coe_mul _ s a).symm

theorem inId_toE_iff : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  intro D 𝔪 y
  refine ⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩
  obtain ⟨z, hz, e⟩ := exists_of_mem_idS hm
  rwa [← (toE_bijective D).1 e]

end GlobalTheory.StdRead.IdealDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev uAt {D : D7} {J : CoreJ D} {G : Type} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) :=
  (r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

theorem mem_localLattice_iff_mulVec {r : ℕ} (D : D7) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    (A : Matrix (Fin r) (Fin r) D.host.E) (h : ∀ w, w ∈ Λ ↔ A.mulVec w ∈ Λ') (w : Fin r → D.host.E) :
    w ∈ lattice₂ D Λ ↔ A.mulVec w ∈ lattice₂ D Λ' := by
  simp only [mem_latP]
  refine forall₂_congr fun a _ => ?_
  rw [h, Matrix.mulVec_smul]

theorem chi_one_of_toData {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xd : DataX E r) (X : Data E r)
    (e : Xd.toData = X) (h : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) : ∀ la, ∀ γ ∈ Xd.Γ, Xd.χ la γ = 1 := by
  subst e
  exact h

theorem nonempty_place (D : D7) : Nonempty (HeightOneSpectrum (𝓞 D.what₂.LL)) := by
  obtain ⟨I, hb, ht⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 (NumberField.RingOfIntegers.not_isField D.what₂.LL)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I ht.ne
  exact ⟨⟨P, hP.isPrime, fun e => hb.ne' (le_bot_iff.1 (e ▸ hIP))⟩⟩

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_dataX_latP (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (uAt r v i).X k ∧ Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
  obtain ⟨X, ⟨h1, -, h3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore (h.laws v).p.toLawsCore
    ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  refine ⟨X, h1, ?_⟩
  rw [GlobalTheory.ModelLatExamples.eq_latP D X.Λ X.L' h3]
  show lattice₂ D X.toData.Λ = _
  rw [h1]

end Build

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.NumSizes

theorem r_log_div_le (r t q : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hq : 4 * t * r + 1 < q) :
    (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  set Q : ℝ := 4 * t * r + 2 with hQ
  have hqQ : Q ≤ q := by rw [hQ]; exact_mod_cast (by omega : 4 * t * r + 2 ≤ q)
  have hQ6 : (6:ℝ) ≤ Q := by rw [hQ]; nlinarith
  have he : Real.exp 1 ≤ Q := by have := Real.exp_one_lt_d9; linarith
  have hant : Real.log q / q ≤ Real.log Q / Q :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hqQ)) hqQ
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have s1 : (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ (r : ℝ) * Real.log q / ((q : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have s2 : (r : ℝ) * Real.log q / ((q : ℝ) / 2) = 2 * r * (Real.log q / q) := by
    field_simp
  have s3 : 2 * (r : ℝ) * (Real.log Q / Q) ≤ 2 * Real.log Q := by
    have hrQ : (r : ℝ) ≤ Q := by rw [hQ]; nlinarith
    have hQ0 : (0:ℝ) < Q := by linarith
    rw [mul_div_assoc', div_le_iff₀ hQ0]
    nlinarith
  have s4 : Real.log Q ≤ Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
    have h6 : Q ≤ 6 * ((r : ℝ) + t) ^ 2 := by rw [hQ]; nlinarith
    calc Real.log Q ≤ Real.log (6 * ((r : ℝ) + t) ^ 2) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  calc (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * r * (Real.log q / q) := s1.trans s2.le
    _ ≤ 2 * r * (Real.log Q / Q) := mul_le_mul_of_nonneg_left hant (by positivity)
    _ ≤ 2 * Real.log Q := s3
    _ ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by linarith

theorem sq_le_dim (f r m : ℕ) (hf : 2 ≤ f) (hr : 2 ≤ r) (hm : 2 ≤ m) : r ^ 2 ≤ m * (f * r.choose 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.add_one_mul_choose_eq (s + 1) 1
    rw [Nat.choose_one_right] at this
    exact this.symm
  have h4 : 2 * (2 * (s + 2).choose 2) ≤ m * (f * (s + 2).choose 2) :=
    Nat.mul_le_mul hm (Nat.mul_le_mul hf le_rfl)
  nlinarith

variable {D : D7} {L : SizeData₂ D}

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem ranks_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    1 ≤ T.PP ∧ (D.R.f : ℝ) * D.R.r ≤ L.sc.b ∧ (D.R.r : ℝ) + D.R.t ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hL := one_le_L L.sc
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : (D.R.f : ℝ) * D.R.r ≤ zBase L := le_mul_of_one_le_right (by positivity) hL
  have hZ1 : 1 ≤ zBase L := hfr.trans hZ
  have hZP : zBase L ≤ T.PP := by
    rw [T.PP_eq]
    have a : zBase L ≤ zBase L ^ T.eP := Real.self_le_rpow_of_one_le hZ1 (by linarith [T.eP_ge])
    exact a.trans (le_mul_of_one_le_left (by linarith) T.one_le_CP)
  have hPP : 1 ≤ T.PP := hZ1.trans hZP
  have hTO : (1 : ℝ) ≤ T.TO := by exact_mod_cast (by have := T.TO_40; omega : 1 ≤ T.TO)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hs : (T.TO : ℝ) * T.PP ≤ L.sc.b := T.TO_PP'.trans (Real.rpow_le_self_of_one_le hb (by norm_num))
  have hP2 : T.PP ≤ (T.TO : ℝ) * T.PP := le_mul_of_one_le_left (by linarith) hTO
  refine ⟨hPP, by linarith, ?_⟩
  have e1 : (D.R.r : ℝ) + D.R.t = T.nP + T.TO * T.nWn := by exact_mod_cast T.split
  have e2 : (T.nP : ℝ) ≤ T.nWn := by exact_mod_cast T.nW_lo.2.2
  have e3 : (T.TO : ℝ) * T.nWn ≤ T.TO * T.PP := mul_le_mul_of_nonneg_left T.nW_le (by linarith)
  linarith [T.nW_le]

variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem unitE_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem dim_eq : GlobalTheory.CompHt.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  exact GlobalTheory.SlopeRec.dimFlag_eq p.fw.laws.pins ⟨Nat.le_add_left 1 i, i.2⟩

theorem lenT_mul_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3 ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hsq := sq_le_dim D.R.f D.R.r D.R.m (by unfold Ranks.f; omega) hr2 h1
  rw [← T.Dp_eq] at hsq
  have hD1 : 1 ≤ T.Dp := by
    rcases Nat.eq_zero_or_pos T.Dp with h | h
    · rw [h] at hsq; nlinarith
    · exact h
  have hsq' : (D.R.r : ℝ) ^ 2 ≤ D.R.m * T.Dp := by exact_mod_cast hsq
  have hD : (1 : ℝ) ≤ T.Dp := by exact_mod_cast hD1
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hPP := (ranks_le T).1
  have hW : (1 : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) (one_le_pow₀ hD)) hk
  have hlen : (lenT p i T.PP : ℝ) ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) := by
    unfold lenT
    rw [dim_eq, ← T.Dp_eq]
    have a := (Nat.ceil_lt_add_one (a := T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m) (by positivity)).le
    have b : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k := div_le_self (by linarith) hm
    linarith
  have hr3 : (D.R.r : ℝ) ^ 3 ≤ D.R.r * (D.R.m * T.Dp) := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
  have hb : (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have : T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 =
      T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) T.CbN_ge
  calc (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3
      ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) * (D.R.r * (D.R.m * T.Dp)) :=
        mul_le_mul hlen hr3 (by positivity) (by linarith)
    _ = 2 * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    _ ≤ 2 * L.sc.b := by linarith

theorem numAt {P : ParameterChoice' D L} (T : ParamsT D L P) (hll : 1 ≤ Real.log (Real.log L.sc.x)) :
    NumAt p i T.PP (|L.Ct| + 20) := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := one_le_L L.sc
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hC := abs_nonneg L.Ct
  obtain ⟨-, hfr, hrt⟩ := ranks_le T
  have hCL : 20 * L.sc.L ≤ (|L.Ct| + 20) * L.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlr : Real.log D.R.r ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_left (by linarith) hf).trans hfr)
  have hlf : Real.log D.R.f ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_right (by linarith) hr).trans hfr)
  refine ⟨hL, hb, by linarith, hll, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [unitE_eq]
    refine le_mul_of_one_le_left ?_ (by linarith)
    have : 0 ≤ L.sc.L := by linarith
    have : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
    positivity
  · have hx := L.sc.one_lt_alt
    have hlx : 0 < Real.log L.sc.x := Real.log_pos hx
    have hk : (2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 2 ≤ D.R.k)
    have hkt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
    have a : Real.log D.R.k ≤ L.Ct * Real.log L.sc.x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (hkt.trans L.t_win.2)
    have b : Real.log D.R.k ≤ (|L.Ct| + 1) * Real.log L.sc.x :=
      a.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L.Ct]) hlx.le)
    have c := Real.log_le_log (Real.log_pos (by linarith)) b
    rw [Real.log_mul (by linarith) hlx.ne'] at c
    have d := Real.log_le_sub_one_of_pos (by linarith : 0 < |L.Ct| + 1)
    nlinarith
  · have hQ : (D.host.QS : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by
      have := D.host.QS_le
      exact_mod_cast this.trans (Nat.pow_le_pow_left (by unfold Ranks.f; omega) 2)
    have hQ0 : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
    have a := Real.log_le_log hQ0 hQ
    rw [Real.log_pow] at a
    push_cast at a
    have h2' := Real.log_two_gt_d9
    unfold Formalism.MainNotions.DIV.Cons.vd2
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (lenT_mul_le p i T).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · intro q hq
    have hq' : 4 * D.R.t * D.R.r + 1 < q := by
      rcases Finset.mem_insert.1 hq with h | h
      · exact h ▸ D.host.qd_big.1
      · exact (Finset.mem_singleton.1 h) ▸ D.host.qd_big.2
    have a := r_log_div_le D.R.r D.R.t q hr1 (by omega) hq'
    have b : Real.log ((D.R.r : ℝ) + D.R.t) ≤ Real.log 2 + L.sc.L := by
      rw [← hlb, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hrt
    have c := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have d := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have e : (|L.Ct| + 20) * L.sc.L ≤ (|L.Ct| + 20) * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hm) (by linarith)
    linarith

end GlobalTheory.RefSum.NumSizes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEqTrace
section
open Matrix

namespace GlobalTheory.PairingTraceExpansion

variable {K : Type} [Field K] {n d : ℕ}

theorem pair_eq_trace (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = trace (Xᵀ * Y) := by
  simp only [GlobalTheory.FlipMatch.pairM, trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem pair_expand (P M : Matrix (Fin n) (Fin d) K) :
    trace (Pᵀ * M) = ∑ i : Fin n, ∑ j : Fin d, P i j * M i j := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem main (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
      (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  have hb : (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (↑b : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have ht : ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * (↑c⁻¹ : Matrix (Fin d) (Fin d) K)ᵀ)ᵀ *
      -((↑b : Matrix (Fin n) (Fin n) K)ᵀ * A * Q * Bᵀ * (↑c : Matrix (Fin d) (Fin d) K)) =
      -((↑c⁻¹ : Matrix (Fin d) (Fin d) K) * (Pᵀ * (A * Q * Bᵀ)) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_inj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, hb, Matrix.one_mul]
  rw [pair_eq_trace, ht, trace_neg, trace_mul_comm, ← Matrix.mul_assoc, hc, Matrix.one_mul, pair_expand]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

end GlobalTheory.PairingTraceExpansion
end

