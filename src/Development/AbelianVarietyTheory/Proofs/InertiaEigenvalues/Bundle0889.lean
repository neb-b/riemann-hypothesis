module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Shift

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ}


set_option maxHeartbeats 4000000 in
theorem shift_central (hP : O.Pins κ v₀ ι x₀) (hn : κ.n = (Vc D i).rank) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0) {ph : ℂ} (hE : O.OneMapOf κ v₀ cE ph)
    (hE0 : O.EquivAt κ c0) (hS : GlobalTheory.AdTh.SerOf O κ v₀ c0 1)
    (hW : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∃ U ∈ R.Wall i (sg0 D A), ∀ h,
      U v₀ h = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cE f h) :
    ∃ (z : G) (ze : ℂ), z ∈ Subgroup.center G ∧ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧
      (∃ k, LiftW R i z k) ∧ ∀ k, LiftW R i z k →
      ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ h, O.phi c0 f h = ze * chiC R i z / ph * O.phi cE f (h * k) := by
  obtain ⟨hEq, ⟨-, hBC, hAct, hcE, hph, z, hz, hrow⟩, -⟩ := hE
  obtain ⟨ze, hzL, ⟨m, hm, hze⟩, hrow⟩ := hrow ()
  have hze0 : ze ≠ 0 := fun h => by
    rw [h, zero_pow hm.ne'] at hze
    exact zero_ne_one hze
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have h0 : ∀ k, c0 k ≠ 0 := fun k h => by simpa [h] using hS.1 k
  have hE0' : ∀ k, cE k ≠ 0 := fun k h => by simpa [h] using hcE k
  have hl : ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hlift : ∀ g, ∃ k, LiftW R i g k := fun g => (hP.lift.lev g).imp fun _ h => h.1
  have hinvW : ∀ U ∈ R.Wall i (sg0 D A), ∀ γ ∈ GQ (Wc D i), ∀ g, U v₀ (γ * g) = U v₀ g := fun U hU =>
    (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ U hU v₀).1
  have hinv : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ γ ∈ GQ (Wc D i), ∀ g, O.phi cE f (γ * g) = O.phi cE f g := by
    intro f hf γ hγ g
    obtain ⟨U, hU, e⟩ := hW f hf
    exact mul_left_cancel₀ hl (by rw [← e, ← e, hinvW U hU γ hγ])
  refine ⟨z, ze, hz, hzL, ⟨m, hm, hze⟩, hlift z, fun k hk => ?_⟩
  have hbase : ∀ y, R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈
      shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k := by
    intro y
    obtain ⟨hh, J', hrep, hPl, hth, hpl⟩ := (hP.tuple ()).reps
    obtain ⟨x, hx⟩ := hPl y
    obtain ⟨⟨f', hf', hcl⟩, hid⟩ := hrow x ((hpl x).2 ⟨y, hx⟩)
    have hs := hS.2.2 () hh J' hrep _ x hx f' hf'.1 hcl
    have hq := hid f' hf'.1 hcl
    have hth' : ∀ q : AutQ (Wc D i), O.thAd () x q = R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out := fun q => congrFun (hth _ x hx) q
    have hf'' : f' ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank := hf'
    have hb := hBC (wtA κ) (Vc D i).rank f' hf''
    obtain ⟨n, as, fs, hfs, hbc⟩ := hb
    have hbc' := hAct _ _ z n as fs f' hf'.1 (fun j => (hfs j).1) hbc
    have hfs' : ∀ j, fs j ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun j => by rw [hn]; exact hfs j
    have r1 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc
    have r2 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc'
    have e1 : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ = ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        inC O.c' (as j)) • O.phi c0 (fs j) := by
      funext g
      have := hs g
      rw [one_mul, r1] at this
      rw [this]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, phi_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmemL : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈ liftSub (LiftW R i) (ratio O cE c0) := by
      rw [e1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (phi_mem_liftSub O h0 hEq hE0 (hfs' j))
    refine ⟨hmemL, fun g => ?_⟩
    have e2 : ∀ q : AutQ (Wc D i), ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (q.out * k) := by
      intro q
      have h3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out = ze * cE (O.dict q.out).1 *
          (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f') (O.dict q.out).1 (O.dict q.out).2) :=
        (congrArg (ph * ·) (hth' q)).symm.trans (hq q)
      rw [h3, r2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := (hEq z k hk (fs j) (hfs' j)).2 q.out
      rw [← chiC_coe, phi_apply] at h2
      linear_combination (ze * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * h2
    have e3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (g * k) := by
      refine eq_of_out (fun g => ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g) (fun g => ze * chiC R i z *
        ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * O.phi cE (fs j) (g * k))
        (fun γ hγ g => congrArg (ph * ·) (hinvW _ (hmem i A.μ0 _) γ hγ g)) (fun γ hγ g => ?_) e2 g
      refine congrArg (ze * chiC R i z * ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [mul_assoc γ, hinv _ (hfs' j) γ hγ]
    exact shift_eq (pE := fun j => O.phi cE (fs j)) hph0 e1 (fun j h => phi_ratio O h0 (fs j) h) (hmemL.1 z k hk g) e3
  let ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun U => U v₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hall : ∀ y, R.thF i A.μ0 y v₀ ∈ shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k :=
    GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hHV i A.μ0).1 (hHV i A.μ0).2.1 (jVx R i A.μ0) (hjV i A.μ0)
      ((shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap (ev ∘ₗ R.thF i A.μ0)) hbase
  have hWall : R.Wall i (sg0 D A) ≤ (shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap ev := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, y, rfl⟩
    obtain ⟨k', hk', e⟩ := exists_liftW_act R i (hlift g)
    have h1 := shiftSub_translate (liftW_mul R i) hz hk (hall y) hk'
    rw [← funext (e (R.thF i A.μ0 y v₀))] at h1
    exact h1
  intro f hf h
  obtain ⟨U, hU, e⟩ := hW f hf
  have h1 : U v₀ h = ze * chiC R i z / ph * ratio O cE c0 h * U v₀ (h * k) := (hWall hU).2 h
  rw [e, e, phi_ratio O h0 f h] at h1
  have hr : ratio O cE c0 h ≠ 0 := div_ne_zero (hE0' _) (h0 _)
  refine mul_left_cancel₀ (mul_ne_zero hl hr) ?_
  linear_combination h1

theorem phi_smul (s : ℂ) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi (s • cc) f h = s * O.phi cc f h := by
  rw [phi_apply, phi_apply, Pi.smul_apply, smul_eq_mul]
  ring


set_option maxHeartbeats 1000000 in
theorem oneMapOf_smul {ph ze : ℂ} (h : O.OneMapOf κ v₀ c0 ph) (hL : ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange)
    {m : ℕ} (hm : 0 < m) (hze : ze ^ m = 1) : O.OneMapOf κ v₀ (ze⁻¹ • c0) ph := by
  have hn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hn
  obtain ⟨hE, ⟨h1, h2, h3, h4, h5, z, hz, h6⟩, h7⟩ := h
  refine ⟨fun g k hk f hf => ⟨(hE g k hk f hf).1, fun x => ?_⟩, ⟨h1, h2, h3, fun k => ?_, h5, z, hz, fun t => ?_⟩, fun x => ?_⟩
  · rw [phi_smul, phi_smul, (hE g k hk f hf).2 x, mul_left_comm]
  · have := h4 k
    show ‖ze⁻¹ * c0 k‖ = 1
    rw [norm_mul, norm_inv, hn, inv_one, one_mul]
    exact this
  · obtain ⟨y, hy, ⟨n, hn0, hyn⟩, h8⟩ := h6 t
    refine ⟨y * ze, mul_mem hy hL, ⟨n * m, Nat.mul_pos hn0 hm, ?_⟩, fun x hx => ⟨(h8 x hx).1, fun f hf hc q => ?_⟩⟩
    · rw [mul_pow, pow_mul, hyn, one_pow, mul_comm n, pow_mul, hze, one_pow, one_mul]
    · refine ((h8 x hx).2 f hf hc q).trans ?_
      have e : ∀ a : ℂ, y * a = y * ze * (ze⁻¹ * a) := fun a => by field_simp
      exact congrArg (fun u => u * _ * _) (e _)
  · obtain ⟨n, a, f, hf⟩ := h7 x
    obtain ⟨y, hy⟩ := hL
    have hy' : D.what₂.embLL y = ze := hy
    refine ⟨n, fun k => a k * y, f, fun g => (hf g).trans (Finset.sum_congr rfl fun k _ => ?_)⟩
    rw [phi_smul, map_mul, hy']
    field_simp

end Shift

section Frame

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

omit iA in
theorem lawsJ_setCE (hL : LawsJ T) {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ}
    (h : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ)) : LawsJ (setCE T c') :=
  ⟨hL.toLawsM, h, hL.muVal, hL.muConj, hL.intAll, hL.modelW, hL.familyUniformisationBasePointOrthogonal, hL.kfHalf, hL.adPin⟩


set_option maxHeartbeats 1000000 in
theorem framePin_smul {c' c'' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
    {hV : T.V ((i : ℕ) + 1) σ = Wc D i} {s : ℂ} (hs : ‖s‖ = 1) (e : c'' ((i : ℕ) + 1) σ = s • c' ((i : ℕ) + 1) σ)
    (h : @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i σ hV) :
    @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c'') iA R i σ hV := by
  have h0 : s ≠ 0 := fun e => by simp [e] at hs
  obtain ⟨ph, b, h1, h2, h3⟩ := h
  refine ⟨ph / s, b, by rw [norm_div, h1, hs, div_one], h2, fun g γ hγ hf hx Wt Y X z hz => ?_⟩
  refine (h3 g γ hγ hf hx Wt Y X z hz).trans ?_
  have e1 : ∀ k (a : ℂ), ph * (c' ((i : ℕ) + 1) σ k * a) = ph / s * (c'' ((i : ℕ) + 1) σ k * a) := fun k a => by
    rw [e, Pi.smul_apply, smul_eq_mul]
    field_simp
  exact congrArg (· * _) (e1 _ _)


set_option maxHeartbeats 2000000 in
theorem exists_shift (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A} (hC : GlobalTheory.Core5 R F)
    (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hJ : JEvExists T R B.κ B.v₀) (i : Fin D.R.m) :
    ∃ (c1 : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (z : G), z ∈ Subgroup.center G ∧
      (B.O i).OneMapOf (B.κ i) (B.v₀ i (sg0 D A)) c1 1 ∧
      (∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, c' ((i : ℕ) + 1) T.σ₀ = c1 → ∀ hV,
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n, ∀ h,
        (B.O i).phi c1 f h = (B.O i).phi (T.cE ((i : ℕ) + 1) (B.O i).s0) (actLev T.Q.c (B.O i).lev2 z f) h := by
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B
  dsimp only at hJ ⊢
  have ht : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hC.lev hC.fam hC.models hC.thP
  obtain ⟨cc, hcc, u, hu, hE0, hS, -⟩ := GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_ofFive GlobalTheory.ChartFree.chartIndep
    D G Pl0 T0 A T R F κ v₀ hC ht hio i _ _ (O i) (pins i).2
  have h1 : (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (u • cc) 1 :=
    GlobalTheory.OneMapPhaseOne.oneMapOf_one_of_serOf D G Pl0 T0 A T R F κ v₀ hC.grp hC.thP ht O i (pins i) (u • cc) hS
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofFive GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC ht i _ _ (O i) (pins i).2 ())
      hE0
  have hrow := phase i hU ⟨_, _, h1⟩
  have hσ : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hg := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV₁ : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f := fun f hf =>
    ⟨_, (baseEmbedding_reading_eval_adelicFunction fw hV₁ (hJ i _ hg hV₁) ⟨f, hf⟩).trans (phiC_congr hσ hV₁ hV _ _)⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hphi : ∀ f h, phiC T hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h :=
    fun f h => phiC_apply hV _ f h
  obtain ⟨z, ze, hz, hzL, ⟨m, hm, hze⟩, ⟨k, hk⟩, hs⟩ := shift_central (O i) (pins i).2 hn hC.models.HV hC.models.jV hC.thP.thF_mem
    (GlobalTheory.ThetaSpanObj.spanAtObj R hP hsz hC.lev hC.fam hC.models hC.thP i A.μ0) hrow hE0 hS fun f hf => by
      obtain ⟨y, hy⟩ := hev f hf
      exact ⟨_, (hC.models.HW i _).2.1.le (LinearMap.mem_range_self _ y), fun h => (congrFun hy h).trans (hphi f h)⟩
  have hzn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hzn
  refine ⟨ze⁻¹ • u • cc, z, hz, oneMapOf_smul (O i) h1 hzL hm hze, fun c'' hc'' hV' => ?_, fun f hf h => ?_⟩
  · obtain ⟨c', hc', hL'⟩ := exists_withConst fw.laws ((i : ℕ) + 1) T.σ₀ cc hcc.1
    have hx0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hσ ▸ fw.x0 i (sg0 D A) hg
    have hpin := @GlobalTheory.FrameConst.framePin_of_ccIs D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV rfl hL' hC.models.inf
      (pins i).2.lift.std hx0 (by subst hc'; exact hcc)
    refine framePin_smul (c' := c') (s := ze⁻¹ * u) (by rw [norm_mul, norm_inv, hzn, hu, inv_one, one_mul]) ?_ hpin
    rw [hc'', hc']
    exact funext fun _ => (mul_assoc _ _ _).symm
  · have h2 := hs k hk f hf h
    have h3 := (hrow.1 z k hk f hf).2 h
    rw [← chiC_coe] at h3
    rw [phi_smul, h2, h3]
    field_simp

end Frame

end GlobalTheory.Unframe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX Formalism.IndefR.FWT GlobalTheory.TwInputs NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupReal

open GlobalTheory.HeckeSup


set_option maxHeartbeats 1600000 in
theorem readsCusp_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D)
    (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i),
    GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV := by
  intro hDec hRT D X i hV
  have hC := X.char
  have ht : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have h5 : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hr := GlobalTheory.OneMapTies.oneMapRow0_of_ties_ofFive GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core X.R.toRealDat X.F.lv2
    X.geo.κ X.geo.v₀ h5 ht hio X.geo.O i (X.geo.pins i)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.constPinned_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O i (X.geo.pins i) hr (X.geo.cTie i)
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.readAt0_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.inGeo.jEvExists X.geo.fw X.unif i hc
  have hsp := GlobalTheory.AdSpan.spanAt X.R.toRealDat hDec X.size hC.lev hC.fam hC.models hC.thP i X.A3.A.μ0
  refine readsCusp_of_clauses (hC.lev.βW i) hC.fam.Sb hC.models.inf hC.models.HW hC.models.gW hC.models.HV hC.models.jV
    hC.thP.thF_mem X.geo.fw hV (h0.ex hV) h0.const hsp (fun O hO => ?_) fun c' hL hV' => ?_
  · obtain ⟨cc, h1, u, h2, h3, h4, -⟩ := GlobalTheory.AdTh.ioExt_oneMap_ofFive.2.1 GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core
      X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ h5 ht hio i _ _ O hO
    exact ⟨cc, h1, u, h2, h3, h4⟩
  · exact @hRT D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ hC.lev hC.grp
      hC.fam hC.models hC.thP
      (@TieIn.mk D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.geo.κ X.geo.v₀ hL X.geo.fw.alg_eq
        X.geo.fw.kap X.geo.fw.hv₀ X.geo.fw.chiR X.geo.fw.x0) i _ rfl hV'

end GlobalTheory.HeckeSupReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IncLocChiEpsUZpow
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem chiRat_eq_epsU_zpow (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) : chiU D.nd i c * (chiU D.nd i 1)⁻¹ = epsU D.nd i ^ (-((c : ℤ) - 1)) := by
    show D.nd.chi i c * (D.nd.chi i 1)⁻¹ = _
    rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
    rfl

theorem charL_chiOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C χ) g =
      Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw χ g) := by
    apply Units.ext
    rfl

theorem inc_cycLL_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g) : Units.map C.inc.toMonoidHom (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g := by
    apply Units.ext
    exact (IntermediateField.inclusion C.le).commutes _

theorem locChi_zpow_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (k : ℤ) (g) : Br.locChi D.nbr i w hw (χ ^ k) g = Br.locChi D.nbr i w hw χ g ^ k := by
    show Units.map _ ((χ ^ k) _) = (Units.map _ (χ _)) ^ k
    rw [MonoidHom.zpow_apply, map_zpow]

theorem charL_mul_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (a b : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (a * b) g =
      tableLineDegreeTwo.charL (LL := ↥C.LL.1) a g * tableLineDegreeTwo.charL (LL := ↥C.LL.1) b g := by
    show Units.map _ ((a * b) g) = _
    rw [MonoidHom.mul_apply, map_mul]
    rfl

theorem locChi_one_apply (g : Br.G D.nbr i w hw) : Br.locChi D.nbr i w hw (1 : GE D.nd →* (D.nd.O i)ˣ) g = 1 := by
    simp [Br.locChi, Br.chiG]

theorem inc_locChi_epsU_zpow (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) (k : ℤ) :
    Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw (epsU D.nd i) g ^ k) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ k := by
  rw [map_zpow, ← inc_cycLL_apply C g, GlobalTheory.CycBridge.locChi_epsU D i w hw g]

theorem chiT_cyc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → ∀ g, tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g = tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
  intro D i w hw C θ c h1 h2 g
  have e1 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) g =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
    rw [charL_chiOC_apply, chiRat_eq_epsU_zpow c h1 h2, locChi_zpow_apply, inc_locChi_epsU_zpow]
  have e0 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) g = 1 := by
    rw [charL_chiOC_apply, mul_inv_cancel, locChi_one_apply]
    exact map_one _
  unfold chiT
  rw [charL_mul_apply, charL_mul_apply, e1, e0, one_mul]
  exact mul_comm _ _

end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialKillsPotentiallyCrystallineModuStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → ∀ p : (D.nd.O i)[X], p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))), ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e (σ ^ n)) d = 0 := by
  intro D i w hw K' h hN hF hS m r hr hpc σ hσ p hp d hd
  have hPst := _root_.GlobalTheory.PstOfCrys.pst_of_pc
    D i w hw K' h hN hF hS m r hr hpc
  obtain ⟨LL', hL, hV', hchar⟩ :=
    GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement D i w hw m r hPst
  have hkill := GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne
    (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.naut.iotaQC i)
    (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ hV' ⟨(σ : GE D.nd), hσ⟩ _
    (hchar σ hσ p hp)
  have hinj : Function.Injective (GlobalTheory.PstLine.incV hL m) := by
    intro x y hxy
    funext j
    exact (IntermediateField.inclusion hL).injective (congrFun hxy j)
  have hd' := _root_.GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst
    (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL LL' h hN hF hS hL
    _ _ (GlobalTheory.PstLine.incV hL m) hinj
    (GlobalTheory.PstLine.isMor_incV (D.nbr i w hw) hL m _) _
    (p.map (D.nbr i w hw).toLL) hkill d hd
  have hsum : ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) •
      (actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw)
        ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e σ) ^ n) d = 0 := by
    rw [GlobalTheory.KillLocal.sumAeval]
    exact hd'
  refine (Finset.sum_congr rfl fun n _ => ?_).trans hsum
  rw [map_pow, GlobalTheory.KillLocal.actPow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepTwist
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc.TwistCrysW

theorem isTwistRep_twist (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) :
    IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (repV C (twistM (locOC C M) θ)) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  have hent : ∀ a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g) a b =
      algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (TruncatedSeriesCountingIdentities.locC C M g) a b := by
    intro a b
    change algebraMap ↥(OL C.LL) ↥C.LL.1 (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (locOC C M g) a b) = _
    rw [map_mul]
    rfl
  change (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec v =
    algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • (TruncatedSeriesCountingIdentities.locC C M g).mulVec v
  funext a
  simp only [Matrix.mulVec, dotProduct, hent, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem isCrys_and_multV : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → IsCrys (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (b : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b ≠ 0 → ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) τ (a + b) = multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a := by
  intro D i w hw C k M θ hM hθ
  have key := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (Fin k → ↥C.LL.1) (repV C (twistM (locOC C M) θ))
    (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (isTwistRep_twist D i w hw C k M θ) hθ hM
  refine ⟨key.1, fun τ b hb a => key.2 τ a b ?_⟩
  exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    ↥C.LL.1 (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b).2.2.2 hb

end GlobalTheory.UseLoc.TwistCrysW
end
end

