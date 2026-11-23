module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

theorem atLin_X {σ κ : Type} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) F = Formalism.L2.Th1.G.linSub c F := rfl

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem analytic_U (B : Base D cc δ) (t : TaylorLogMetric.VC D N N') {G : TaylorLogMetric.VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (TaylorLogMetric.U D B.tor t G) Set.univ := by
  have hadd : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => z + t) Set.univ := fun z _ => by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => G (z + t)) Set.univ :=
    hG.comp hadd (fun _ _ => Set.mem_univ _)
  let ℓ : TaylorLogMetric.VC D N N' →ₗ[ℂ] ℂ := (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N').flip t
  have h2 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => ℓ z) Set.univ :=
    (LinearMap.toContinuousLinearMap ℓ).analyticOnNhd _
  have h3 : ∀ z : TaylorLogMetric.VC D N N', TaylorLogMetric.Hf D B.tor z t = ℓ z := fun z => by
    show _ = formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' z t
    rw [formV_apply]; rfl
  intro z hz
  have h4 : AnalyticAt ℂ (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) z := by
    have := h2 z hz
    fun_prop
  have h5 := (h1 z hz).mul h4
  have e : TaylorLogMetric.U D B.tor t G = (fun z => G (z + t)) * (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) := by
    funext z
    simp only [TaylorLogMetric.U, h3, Pi.mul_apply]
  rw [e]
  exact h5

abbrev jetS (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hd : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : ℂ_[p] :=
  Formalism.L2.Th1.C.jet (Formalism.L2.Th1.A.logSer (curveL p (cmL a₀ b₀ dK ha hd lam hlam) ι))
    (Formalism.L2.Th1.Top.phC p (cmL a₀ b₀ dK ha hd lam hlam) ι) 2

theorem term_shape (hIn : GlobalTheory.ThLoc.Inputs) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {X : Fields} (s : Seam D X) (hs : s.Ok)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁') {p : ℕ} [Fact p.Prime] (hpd : p = D.host.d)
    (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁')
    (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : Formalism.L2.KerInert.IotaExt lm ι)
    (hInt : IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι))
    (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t)
    (u : HH D → ℂ_[p]) (M : D.what₂.Tau × Fin N' × Fin N → (Bool × HH D) × Fin N × Fin N' → ℂ_[p])
    (hfr : ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p])
      (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p]))
      (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)),
      Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)))
        (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb
        act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = M (s.iT i.1, i.2) x) :
    ‖jetS a₀ b₀ D.host.d ha hd lam hlam p ι‖ ≤ ‖(D.host.d : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p], JetsIntegral sg ∧
      TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁'))) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-jetS a₀ b₀ D.host.d ha hd lam hlam p ι) • Formalism.L2.Th1.G.betaPair (HH D) N N' u) * sg := by
  obtain ⟨M₀, hM0, hMc, hMm⟩ := (Formalism.L2.KerInert.pairing_fact D cc δ p N N' L L₁ L' L₁' hE hE').2 t ht
  obtain ⟨J, _, v, A, cE, sE, δE, emb, act, hEF, hfM⟩ := hfr
  have hLat := _root_.GlobalTheory.ThLoc.latAt_all D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L₁ L₁' hA₁ p ι
  have hθ := hLat.mem_th.1
  have hEan : AnalyticOnNhd ℂ (B.eNat χ N N' L₁ L₁') Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) Set.univ :=
      (LinearMap.toContinuousLinearMap (s.flatV N N').symm.toLinearMap).analyticOnNhd _
    have h2 := hθ.comp h1 (fun _ _ => Set.mem_univ _)
    have e : (B.eNat χ N N' L₁ L₁') = (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) ∘ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) := by
      funext w
      simp
    rw [e]
    exact h2
  have hGan := analytic_U B t hEan
  have hCo : TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')) TaylorLogMetric.Qbar :=
    hIn.algT D cc δ B χ hcc hδ hχ N N' L₁ L₁' hA₁ t ⟨M₀, hM0, hMm⟩
  have hU : (fun z => TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁') (s.flatV N N' z)) =
      Formalism.L2.Th1.H.opU (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) ((s.flatV N N').symm t)
        (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) := by
    funext z
    rw [KS.opU_pb (s.flatV N N') _ _ (KS.form_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))), LinearEquiv.apply_symm_apply]
    simp only [Formalism.L2.Th1.H.opU, formV_apply]
    rfl
  have hfr' : (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) = frameM (ι : ℂ →+* ℂ_[p]) v A := by
    funext i x
    exact (hfM i x).symm
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨hS, sg, hsg, heq⟩ := hIn.shape GlobalTheory.EmbSepUnram.embSep a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (DVar X.Tau N N')
    (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L₁ L₁') hLat.selfDual hLat.stable
    (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) hLat.mem_th p (dvd_of_eq hpd) ι hInt hLat.locNorm Unit (fun _ => 1)
    (fun _ => (s.flatV N N').symm t) M₀ (fun _ => by simp) hM0
    (fun h => by
      have := Nat.Coprime.eq_one_of_dvd hMc.symm h
      exact (Fact.out : p.Prime).one_lt.ne' this)
    (fun _ => by
      show s.flatV N N' ((M₀ : ℂ) • (s.flatV N N').symm t) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
      rw [map_smul, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
      exact hMm)
    J v (HH D) N N' A u D.host.E cE sE δE emb act hEF
  refine ⟨hS, sg, hsg, ?_⟩
  rw [GlobalTheory.FlatTaylorBridge.bridge D X s N N' p lm ι hι _ hGan hCo _ M, hfr', hU]
  simpa [thetaLin] using heq

end GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

namespace GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem expS_eq (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (S : ℂ_[p]) (u : HH D → ℂ_[p]) :
    product_zeroth_first_parts.expS ℂ_[p] (-(S • ∑ t : HH D, u t • ∑ a : Fin N, ∑ b : Fin N',
      (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
        MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))) =
    Formalism.DworkPowerSeriesWeights.mvExp ((-S) • Formalism.L2.Th1.G.betaPair (HH D) N N' u) := by
  have e : (-(S • ∑ t : HH D, u t • ∑ a : Fin N, ∑ b : Fin N',
      (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
        MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))) =
      (-S) • Formalism.L2.Th1.G.betaPair (HH D) N N' u := by
    rw [neg_smul]
    congr 2
    unfold Formalism.L2.Th1.G.betaPair
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
  rw [e]
  rfl

theorem norm_bound {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : ‖x‖ ≤ ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ))) :
    ‖x‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  have e2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [e, norm_algebraMap', Padic.norm_p]
  rw [e2, Real.inv_rpow hp.le, Real.rpow_neg hp.le, inv_inv] at h
  exact h

theorem atLin_comb {σ ν κ : Type} [Finite σ] [Fintype ν] [Fintype κ] {p : ℕ} [Fact p.Prime] (M : σ → ν → ℂ_[p]) (r : κ → ℂ_[p])
    (G : κ → MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (r k) * G k) =
      ∑ k, MvPowerSeries.C (r k) * TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (G k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [atLin_X, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, AlgHom.commutes, Formalism.L2.Th1.G.linSubHom_apply]
  rfl

theorem jets_prod {ν : Type} {p : ℕ} [Fact p.Prime] {sg : MvPowerSeries ν ℂ_[p]} (h : JetsIntegral sg) (m : ν →₀ ℕ) :
    ‖(m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m sg‖ ≤ 1 := by
  have := h m
  simpa only [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod, Nat.cast_prod] using this

theorem comb_exp {ν κ : Type} [Fintype κ] {K : Type} [CommRing K] (E : MvPowerSeries ν K) (r : κ → K)
    (T sg : κ → MvPowerSeries ν K) (h : ∀ k, T k = E * sg k) :
    ∑ k, MvPowerSeries.C (r k) * T k = E * ∑ k, MvPowerSeries.C (r k) * sg k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k, mul_left_comm]

end GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → OrbitPlaces.ShapeD D p (GlobalTheory.KerStd.stdSer D lm κ P P' F) := by
  intro hIn D cc δ hcc hδ B χ hχ X s hs N N' L L' hA p _ lm hpd cD hgen P P' κ hP hP' hκ F hF
  obtain ⟨ι, hι⟩ := hIn.lamExt p lm
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by
    rw [hL]
    exact B.lat
  have h5 : 5 ≤ p := by omega
  have hInt := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hlat p h5 ι
  obtain ⟨u, hu, hfr⟩ := _root_.GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d D cc δ hcc hδ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p lm hpd ι hι cD hgen P P' κ hP hP' hκ
  let M : D.what₂.Tau × Fin N' × Fin N → (Bool × HH D) × Fin N × Fin N' → ℂ_[p] :=
    fun k j => κ k.1 * TaylorLogMetric.chgB D lm P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))
  have hterm := fun (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁')
      (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁') (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t) =>
    GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.term_shape hIn hcc hδ B χ hχ s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat hA₁ hpd hE hE' lm ι hι hInt t ht u M
      (hfr L₁ L₁' hA₁ hE hE')
  have hb := (hterm L L' hA ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩ 0
    ⟨1, one_pos, Nat.coprime_one_left p, by simpa using AddSubgroup.zero_mem _⟩).1
  have hbound : ‖GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jetS a₀ b₀ D.host.d ha hd lam hlam p ι‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
    refine GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.norm_bound ?_
    have e3 : ((D.host.d : ℕ) : ℂ_[p]) = (p : ℂ_[p]) := congrArg _ hpd.symm
    rw [e3] at hb
    exact hb
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL1, rfl⟩ := hF
  have hk := fun k => (hterm (L₁ k) (L₁' k) (hL1 k).1 (hL1 k).2.1 (hL1 k).2.2 (t k) (ht k)).2
  choose sg hsg he using hk
  refine ⟨GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jetS a₀ b₀ D.host.d ha hd lam hlam p ι, hbound, u, hu, ∑ k, MvPowerSeries.C (r k) * sg k,
    GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jets_prod (GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jets_comb r sg hr hsg), ?_⟩
  rw [GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.expS_eq, ← GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.comb_exp _ r _ sg he]
  exact GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.atLin_comb M r _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HeckeScalarDC

open GlobalTheory.HeckeScalarSph

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem dc_scalar_fin (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (s : SplitPlace L) (α : GAf L n) (hα : TrivOutside {s.v} α) (Rα : Finset (GAf L n))
    (hRα0 : (∀ γ ∈ Rα, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ Rα ∧ γ⁻¹ * x ∈ Umax L n) :
    ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      ∑ γ ∈ Rα, NG.rt L n γ f = c • f := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα hRα0
  have hRtriv : ∀ γ ∈ Rα, TrivOutside {s.v} γ := by
    intro γ hγ
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hRα0.1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ Rα, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ Rα, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact _root_.GlobalTheory.SplitHeckeComm.doubleCoset_comm L n a.W s α b Rα (R b) hα hb (fun y hy => hRα0.2 y (conv.1 hy))
        (fun γ hγ => conv.2 (hRα0.1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [← e]
  rfl

theorem dc_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS s α hα ι R r h1 h2
  classical
  have hinj : Set.InjOn r R := by
    intro γ hγ δ hδ e
    have hx := h1 γ hγ
    have hU : (r γ)⁻¹ * r γ ∈ Umax L n := by rw [inv_mul_cancel]; exact one_mem _
    exact (h2 (r γ) hx).unique ⟨hγ, hU⟩ ⟨hδ, by rw [← e]; exact hU⟩
  have hA : ∀ γ ∈ R.image r, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    exact h1 δ hδ
  have hB : ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) →
      ∃! γ, γ ∈ R.image r ∧ γ⁻¹ * x ∈ Umax L n := by
    intro x hx
    obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h2 x hx
    refine ⟨r γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hy
    rw [hu δ ⟨hδ, ey⟩]
  obtain ⟨c, hc⟩ := dc_scalar_fin a S hS s α hα (R.image r) ⟨hA, hB⟩
  refine ⟨c, fun f hf hfix => ?_⟩
  rw [← hc f hf hfix, Finset.sum_image (fun γ hγ δ hδ e => hinj hγ hδ e)]

end GlobalTheory.HeckeScalarDC

end
end

