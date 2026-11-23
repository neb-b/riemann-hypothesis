module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.ExactBig

variable {D : D7}

theorem exists_change {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ₁ χ' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H₁ : IsWeilDatumO ψ S T χ₁ χ' ω₁)
    (hχ : IsHeckeChar D χ) (rχ : ResEta D χ S.rank) :
    ∃ ω, IsWeilDatumO ψ S T χ χ' ω ∧ ∀ u g y, IsDetRoot T g y → ω₁ (u, g) = (((χ₁ / χ) y : Circle) : ℂ) • ω (u, g) := by
  have r0 : ResEta D (χ * χ₁⁻¹) 0 :=
    Formalism.L2.Theta.resEta_parity (Formalism.L2.Theta.resEta_mul rχ (Formalism.L2.Theta.resEta_inv H₁.resS)) (by omega)
  have r1 : ResEta D 1 0 := ⟨r0.1, fun _ _ _ => by simp⟩
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨ω, H, hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H₁.std S T χ₁ χ' (χ * χ₁⁻¹) 1 ω₁ H₁
    (GlobalTheory.WeilChange.hecke_mul hχ (GlobalTheory.WeilChange.hecke_inv H₁.hecS)) h1 r0 r1
  have e : χ₁ * (χ * χ₁⁻¹) = χ := by rw [mul_comm χ, mul_inv_cancel_left]
  rw [e, mul_one] at H
  refine ⟨ω, H, fun u g y hy => ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D S u
  have e1 : (χ₁ / χ) y * (((1 : (AE D)ˣ →* Circle) x)⁻¹ * (χ * χ₁⁻¹) y) = 1 := by
    rw [MonoidHom.one_apply, inv_one, one_mul, ← MonoidHom.mul_apply, ← mul_assoc, div_mul_cancel, mul_inv_cancel,
      MonoidHom.one_apply]
  rw [hv u g x y hx hy, smul_smul, ← Circle.coe_mul, e1, Circle.coe_one, one_smul]

theorem seesaw_exact {ψ : AddChar (AF D.host.F) ℂ} {S A B : HSp D} {χ χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)} {ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)}
    {ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ)}
    (H₁ : IsWeilDatumO ψ S A χ₁ χ₁' ω₁) (H₂ : IsWeilDatumO ψ S B χ₂ χ₂' ω₂)
    (H : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ (χ₁' * χ₂') ω)
    {φ : WO S A → ℂ} {φ' : WO S B → ℂ} (hφ : IsThetaFunO ψ S A φ) (hφ' : IsThetaFunO ψ S B φ')
    (u : GA D S) (g : GA D A) (g₁ : GA D B) {x y : (AE D)ˣ} (hx : IsDetRoot A g x) (hy : IsDetRoot B g₁ y) :
    thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ' = (((χ₁ / χ) x : Circle) : ℂ) * (((χ₂ / χ) y : Circle) : ℂ) *
      thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') := by
  obtain ⟨o₁, K₁, e₁⟩ := exists_change H₁ H.hecS H.resS
  obtain ⟨o₂, K₂, e₂⟩ := exists_change H₂ H.hecS H.resS
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ H.std _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ χ₁' χ₂' ω o₁
    o₂ H K₁ K₂ u g g₁ φ φ' hφ hφ'
  simp only [thetaKO]
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec, ← GlobalTheory.SeesawSumTarget.boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero,
    e₁ u g x hx, e₂ u g₁ y hy]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjoint_exact {ψ : AddChar (AF D.host.F) ℂ} {S B : HSp D} {χB χS : (AE D)ˣ →* Circle}
    {ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)} (H : IsWeilDatumO ψ B S χB χS ω₂) :
    ∃ ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ),
      IsWeilDatumO ψ (negSp S) B χS⁻¹ χB⁻¹ ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  have hψ := H.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂),
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM, adjM_zero]

theorem attChr_eq {C : Type} [CommGroup C] (χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n = χ / η ^ (n % 2) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]; simp
  · rw [if_pos h, Nat.odd_iff.1 h]; simp [div_eq_mul_inv]

theorem kerBig_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  intro D T L sc G μ₀ hL W t i j ωA hA B ρ Θ Θ' hΘ g g₁ u
  have hd := isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := adjoint_exact h2
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  obtain ⟨s, hs⟩ := odd_sLen D
  obtain ⟨t', ht⟩ := D.R.t_odd
  have pW : (G.V (.grid (i + 1) (j + 1))).rank % 2 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have cT : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j =
      G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    simp only [GridData.chrT, GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  have cV : G.chrS (.chi i (j + 1)) / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = (L.eta ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j))⁻¹ := by
    simp only [GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, two_mul, pow_add, div_div, mul_left_comm, div_mul_cancel_left]
  have cV₁ : (G.chrT (.mu t (i + 1) j))⁻¹ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j =
      (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ := by
    simp only [GridData.chrT, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, inv_div, div_div, ← mul_assoc, div_mul_cancel_right]
  rw [cT] at hA
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  have hA' : IsWeilDatumO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) _ _ (ωA.toSgn true) := hA
  have e : ∀ d ∈ Θ.support, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ * ωA (u, GlobalTheory.SquareComm.blk A Bs (g, g₁))
        (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) 0 := fun d hdm => by
    have k := seesaw_exact h1 hω₂ hA' (hd d hdm).1 (hadj _ (hd d hdm).2).1 (negGA S u) g g₁
      (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec (GlobalTheory.RecDict.exists_isDetRoot D _ g₁).choose_spec
    rw [(hadj _ (hd d hdm).2).2, cV, cV₁] at k
    exact k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, GlobalTheory.SquareDict.datumA, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  rw [e d hdm]
  ring

end GlobalTheory.SquareDict.ExactBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OmegaDer

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_gen {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (m : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous m)
    (h0 : m 0 = 1) (hadd : ∀ s t, m (s + t) = m s * m t) (hG : ∀ t, (m t)ᴴ * G * m t = G) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ ∀ t : ℝ, m t = NormedSpace.exp (t • Z) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := ((GlobalTheory.contDiff_of_continuous_oneParameter _ m hc h0 hadd).differentiable (by simp) 0).hasDerivAt
  set Z := deriv m 0
  refine ⟨Z, ?_, fun t => ?_⟩
  · let c : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun A => Aᴴ
        map_add' := fun A B => conjTranspose_add A B
        map_smul' := fun r A => by rw [conjTranspose_smul, star_trivial]; rfl }
    have h1 : HasDerivAt (fun t => (m t)ᴴ) Zᴴ 0 :=
      (LinearMap.toContinuousLinearMap c).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h2 := (h1.mul_const G).fun_mul h
    simp only [hG, h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h2
    exact h2.unique (hasDerivAt_const _ _)
  · have hd : ∀ s, HasDerivAt m (m s * Z) s := fun s => by
      have h1 : HasDerivAt (fun u => m s * m (u - s)) (m s * Z) s := by
        refine HasDerivAt.const_mul _ ?_
        have h2 : HasDerivAt m Z (s - s) := by rwa [sub_self]
        exact h2.comp_sub_const s s
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      beta_reduce
      rw [← hadd, add_sub_cancel]
    have hk : ∀ s, HasDerivAt (fun u : ℝ => m u * NormedSpace.exp (u • (-Z))) 0 s := fun s => by
      refine ((hd s).fun_mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s)).congr_deriv ?_
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
    have hcst := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    simp only [zero_smul, NormedSpace.exp_zero, h0, Matrix.mul_one] at hcst
    have e : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
      rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc m t = m t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [e, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hcst, Matrix.one_mul]

end Mat

variable {D : D7}

theorem exists_expInf {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : GlobalTheory.SmoothForms.LieN V, ∀ t : ℝ, g t = GlobalTheory.SmoothForms.expInf θ V (t • Z) := by
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have h0 : g 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := g 0) (by rw [← this, mul_one])
  have key : ∀ τ, ∃ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, Zᴴ * gramAt D V τ + gramAt D V τ * Z = 0 ∧
      ∀ t : ℝ, infMat D.sp.cm.sig V.gram (θ τ) (g t) = NormedSpace.exp (t • Z) := fun τ =>
    exists_gen _ _ ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
        ((Units.continuous_val.comp continuous_subtype_val).comp hc))
      (by rw [h0]; exact R.2.2.2.2.1 1 (one_mem _) τ) (fun s t => by rw [hadd, R.2.2.2.1])
      fun t => (_root_.GlobalTheory.FockCompare.RealAction.real_action D θ hθ).1 V (g t) τ
  choose Z hZ hg using key
  refine ⟨fun τ => ⟨Z τ, hZ τ⟩, fun t => ?_⟩
  have h1 := GlobalTheory.SmoothForms.isExpFam_expInf R (t • fun τ => ⟨Z τ, hZ τ⟩)
  exact R.2.2.1 _ (hinf t) _ h1.1 fun τ => (hg τ t).trans (h1.2 τ).symm

theorem der_sum {θ : InfFam D} (hθ : IsInfFam θ) {U : HSp D} (𝒮 : Set (GA D U → ℂ)) (hc : ∀ φ ∈ 𝒮, Continuous φ)
    (hd : ∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt U τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ U τ X t)) (φ' g) 0)
    {φ : GA D U → ℂ} (hφ : φ ∈ 𝒮) (Z : GlobalTheory.SmoothForms.LieN U) (a : D.what₂.Tau → ℂ)
    (ha : ∀ τ, HasDerivAt (fun t : ℝ => φ (oneP θ U τ (Z τ).1 t)) (a τ) 0) :
    HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • Z))) (∑ τ, a τ) 0 := by
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ U
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ U 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ U) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  set L := fderiv ℝ (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) 0
  have key : ∀ v : GlobalTheory.SmoothForms.LieN U, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • v))) (L v) 0 := by
    intro v
    have h4 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const v
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) L ((0 : ℝ) • v) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp, one_mul]
  have e1 : ∀ τ, a τ = L (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ)) := fun τ =>
    (ha τ).unique ((key (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => congrArg φ (GlobalTheory.SmoothForms.oneP_eq R τ (Z τ) t)))
  have e2 : Z = ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U) :=
    (GlobalTheory.SmoothForms.sum_atPlace Z).symm
  refine (key Z).congr_deriv ?_
  simp only [e1]
  exact (congrArg L e2).trans
    (map_sum L (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U)) Finset.univ)

theorem exists_conjU (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} {c : D.host.E} (hc : c ≠ 0)
    (h : J = c • M.gram) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D M, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h g = k ∧
      Formalism.L2.Theta.matHom M g = GeneralLinearGroup.map (cA D) k.1 := by
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hk : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := k.2
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map _
  have hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram := by
    generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = m at hk
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hk
    exact hu.smul_left_cancel.1 hk
  refine ⟨⟨GeneralLinearGroup.map (cA D) k.1, ?_⟩, Subtype.ext (Units.ext e), rfl⟩
  show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram *
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram
  rw [e, hk2]

theorem map_finPart_conj {n : ℕ} (m : Matrix (Fin n) (Fin n) (AE D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) (i j : Fin n) :
    finPart D (cA D (m i j)) = finPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (1 + cA D ((m - 1) i j) - 1) := by
    intro u hu
    have h2 : u • (m - 1) i j = 0 := congrFun (congrFun (hm u hu) i) j
    rw [add_sub_cancel_left]
    have h3 : cA D (u • (m - 1) i j) = u • cA D ((m - 1) i j) :=
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) u _
    rw [← h3, h2, RingHom.map_zero]
  have h4 := GlobalTheory.ConjInfExp.finPart_eq_one _ h1
  have h5 : cA D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) = (1 : Matrix (Fin n) (Fin n) (AE D)) i j :=
    congrFun (congrFun (Matrix.map_one (cA D) (RingHom.map_zero _) (RingHom.map_one _)) i) j
  rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_left, Matrix.sub_apply, RingHom.map_sub, h5, RingHom.map_sub,
    sub_eq_zero] at h4
  exact h4

theorem mem_GinfC_of_conj {M : HSp D} (g : GA D M) (m : Matrix (Fin M.rank) (Fin M.rank) (AE D))
    (hg : Formalism.L2.Theta.mt M g = m.map (cA D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) : g ∈ GinfC M := by
  show finHom M g = 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (finHom M g).1 i j = finPart D (Formalism.L2.Theta.mt M g i j) := rfl
  have h2 : (finHom M 1).1 i j = finPart D ((1 : Matrix (Fin M.rank) (Fin M.rank) (AE D)) i j) := rfl
  rw [← map_one (finHom M), h1, h2, hg]
  exact map_finPart_conj _ hm i j

theorem exists_line (M : HSp D) {c : D.host.E} (hc : c ≠ 0) (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank)
    (hJ : Xs.J = c • M.gram) (γ) (hγ : γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs) :
    ∃ g : ℝ → GA D M, (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hJ (g t) = γ (Multiplicative.ofAdd t)) ∧ Continuous g ∧
      (∀ s t, g (s + t) = g s * g t) ∧ ∀ t, g t ∈ GinfC M := by
  choose g h1 h2 using fun t : ℝ => exists_conjU M hc hJ (γ (Multiplicative.ofAdd t))
  refine ⟨g, h1, ?_, fun s t => ?_, fun t => ?_⟩
  · have h3 : Continuous fun t : ℝ => (γ (Multiplicative.ofAdd t)).1 :=
      continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)
    have h4 : Continuous fun t => Formalism.L2.Theta.matHom M (g t) := by
      simp only [h2]
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact (Units.continuous_val.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
      · exact (Units.continuous_coe_inv.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    exact continuous_induced_rng.2 h4
  · have h3 : Formalism.L2.Theta.matHom M (g (s + t)) = Formalism.L2.Theta.matHom M (g s * g t) := by
      rw [map_mul, h2, h2, h2, ← map_mul, ofAdd_add, map_mul γ]
      rfl
    exact Subtype.ext h3
  · exact mem_GinfC_of_conj _ _ (congrArg Units.val (h2 t)) (hγ.2 _)

theorem der_line {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (A : Fr V) (B : Fr W) {eS eT : D.what₂.Tau → ℚ} (he : ∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ))
    {f : WO V W → ℂ} (hf : IsVacF ψ θ A B f) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, Z τ ∈ lieAt V τ) ∧ ∀ P z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
          ((A.fr τ * Z τ * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + (-((eT τ : ℂ) * (Z τ).trace)) • P)) z) 0 := by
  obtain ⟨Z, hZ⟩ := exists_expInf hθ V g hc hadd hinf
  refine ⟨fun τ => (Z τ).1, fun τ => (Z τ).2, fun P z => ?_⟩
  have hs : ∀ Q : D.what₂.Tau → PolF D W.rank V.rank, ptF ψ θ A B f (∑ τ, Q τ) z = ∑ τ, ptF ψ θ A B f (Q τ) z :=
    fun Q => (congrFun (map_sum (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) Q Finset.univ) z).trans
      (Finset.sum_apply _ _ _)
  rw [hs]
  simp only [hZ]
  rcases isEmpty_or_nonempty D.what₂.Tau with h0 | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
    simp only [e, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  let 𝒮 : Set (GA D V → ℂ) := {φ | ∃ f z, IsThetaFunO ψ V W f ∧ φ = fun g => ω (g, 1) f z}
  refine der_sum hθ 𝒮 ?_ ?_ (φ := fun g => ω (g, 1) (ptF ψ θ A B f P) z)
    ⟨_, z, (GlobalTheory.LieScalar.ptF_laws hθ hω.std A B hf).1 τ₀ P, rfl⟩ Z _ fun τ =>
    (GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ (eS τ) (eT τ) hθ hω (he τ).1 (he τ).2 hf).1 _ (Z τ).2 P z
  · rintro _ ⟨f, z, hf, rfl⟩
    exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
  · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (g, 1) z
    simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this

end GlobalTheory.OmegaDer

end
end

