module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MrelConjTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0118
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0116
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousZetaL
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

theorem glev_last_eq (r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  simp only [Glev, B2.UWb, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a _ => h2 a⟩

theorem image_glev : ιLev k 1 ρ '' Glev k ρ (Fin.last ρ) = Glev k (1 + ρ) (Fin.last (1 + ρ)) := by
  rw [glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]

theorem map_levM_smul {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs) :
    ∃ c : NNReal, μs.map (B2.levM k ρ) = c • μ := by
  rw [glev_last_eq] at hμs hμ
  have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ
  obtain ⟨_, hν⟩ := Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs
  have e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ) := by
    rw [← glev_last_eq, ← glev_last_eq, image_glev]
  rw [e] at hν
  exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc
    hν.left hν.finite_compact

theorem zeta_levM (z z' : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of (B2.levM k ρ x)) =
      zetaL k ρ z z' (Fin.last ρ) (Matrix.of x) := by
  have hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v := fun r v => by
    simp [fvec]
  change herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ)))
      (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) =
    herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))
  rw [hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]

theorem measurable_levM : Measurable (B2.levM k ρ) := by
  exact (Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable

theorem continuous_zetaL (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x) := by
  exact (LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id

theorem map_levM_eq {z z' : Fin (2 * ρ + k + 1) → ℂ} {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (wt : ℂ → ℝ≥0∞) (hfin : ∀ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ < (⊤ : ℝ≥0∞))
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, wt ζ * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs = ∫⁻ ζ, wt ζ * ψ ζ) :
    μs.map (B2.levM k ρ) = μ := by
  obtain ⟨c, hc⟩ := map_levM_smul hμ hμs
  have key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ := by
    intro ψ hψ
    have hm : Measurable fun y : Mt k (1 + ρ) =>
        ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y)) :=
      hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable
    rw [← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]
    simp_rw [zeta_levM]
    rw [hlaws ψ hψ, hlaw ψ hψ]
  by_cases hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0
  · obtain ⟨R, hR⟩ := hR
    have hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator Metric.isClosed_closedBall.measurableSet
    have h1 := key _ hψ
    have e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ =
        ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      congr 1
      funext ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]
    rw [e, ENNReal.smul_def] at h1
    have h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [one_mul]
      exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hR (hfin R).ne).mp h2
    rw [hc, ENNReal.coe_eq_one.mp hc1, one_smul]
  · push_neg at hR
    have h0 : ∫⁻ ζ, wt ζ = 0 := by
      rw [← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]
      refine le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'
      simp [hR]
    have hμ0 : μ = 0 := by
      have h3 := hlaw (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    have hμs0 : μs = 0 := by
      have h3 := hlaws (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    rw [hμ0, hμs0, Measure.map_zero]

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFamLocal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_locality_holds : FamLocal := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk X Dc Φ hΦ q
  have hk1 : 1 ≤ P.k := by omega
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hpl.2.2.2.1]; exact hpl.1.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos
  have hsec := Bs.sec
  obtain ⟨hOpen, hIsDom, hMu, hFF⟩ := hΦ

  have hdom : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', x.2 ∈ Dc x.1 := by
    intro x hx
    obtain ⟨h, hh, h', hh', hg⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk1 hz hz' hT hT' hsec hx.2.1 hx.2.2
    set ζ := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 with hζ
    have hζT : P.TT < Complex.normSq ζ := by
      have h1 := hx.2.2
      unfold Q.GGl at h1
      show P.T * P.T' < _
      rw [← hpl.2.2.2.1, ← hpl.2.2.2.2.1]
      linarith
    let q' : MA.Qp P.r P.TT := ⟨(x.1, ζ), hx.1, hζT⟩
    have hmu : NF.muZ P.k P.r Bs.μsec ζ ∈ Dc x.1 := hMu q'
    have hmuG : NF.muZ P.k P.r Bs.μsec ζ ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.muZ_glev hpl q'
    have hS : ∀ {w : Fin (2 * P.r + P.k + 1) → ℂ} {s : Q.Mx P.k P.r}, s ∈ UWset P.k P.r w →
        s ∈ Q.Slev P.k P.r w (Fin.last P.r) := by
      intro w s hs
      exact ⟨s, hs, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, by simp⟩
    rw [hg]
    exact (hIsDom x.1 hx.1).2 _ ⟨hmuG, hmu⟩ h (hS hh) h' (hS hh')

  let Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => if (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ c g else 0
  have hΦt_mem : Φt ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = 0
      rw [if_neg hx]
    · obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hFF.1 x₀ ⟨hx₀.1, hdom x₀ hx₀⟩ hx₀.2.1
      have hO : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} := by
        have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
          have : IsOpen (OmX P.r) := by
            have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
            rw [e]
            exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
          exact this.preimage continuous_fst
        have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
          isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
        exact h1.inter h2
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2}, F, hU.inter hO, ⟨hx₀U, hx₀.1, hx₀.2.2⟩,
        hF.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : x ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = F x
      rw [if_pos hxD]
      exact hΦF x hx.1 hxG
    · have hxD' := Formalism.FourierDecayAlt.P.Qx5.DomR_inv hh hh' hx
      show (if (x.1, h * x.2 * h') ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 (h * x.2 * h') else 0) =
        (Bs.π h).comp ((if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0).comp (Bs.π' h'))
      rw [if_pos hxD', if_pos hx]
      exact (hFF.2 x.1 hx.1).2.2.2 x.2 ⟨hx.2.1, hdom x hx⟩ h hh h' hh'
  refine ⟨⟨Φt, hΦt_mem⟩, {ζ' | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ'}, ?_, fun ζ' hζ' => ?_⟩
  · refine (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds ?_
    show Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hqD : (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec (q := (q.1.1, ζ')) ⟨q.2.1, hζ'⟩
  have hval : Φt q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') := by
    show (if (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' then _ else 0) = _
    rw [if_pos hqD]
  refine ⟨hval, fun Y a b => ?_⟩
  rw [X.t_apply Y a b ⟨Φt, hΦt_mem⟩ (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') hqD]
  show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φt q.1.1) (NF.muZ P.k P.r Bs.μsec ζ') =
    Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φ q.1.1) (NF.muZ P.k P.r Bs.μsec ζ')
  have hDo : IsOpen {g : Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z')
  refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := Fin.last P.r) hDo Bs.z Bs.z' Y a b).1 (Φt q.1.1) (Φ q.1.1) (fun x hx => ?_)
    _ ⟨hqD.2.1, hqD.2.2⟩
  show (if (q.1.1, x) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ q.1.1 x else 0) = Φ q.1.1 x
  rw [if_pos ⟨q.2.1, hx.1, hx.2⟩]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem radial_torus_of_jets_taylor : GTCLRadTOfCut := by
  intro hJT hJR hTay Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X Y a b
  obtain ⟨N, hN⟩ := hJT (Wq →L[ℂ] Wp) P.k P.r Bs.z Bs.z' Y a b
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  by_cases hne : ∃ ζs, ζs ∈ RadTA.Ann Bs.z Bs.z'
  swap
  · exact ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q hq => absurd ⟨q.2, hq.2⟩ hne⟩
  obtain ⟨ζs, hζs⟩ := hne
  obtain ⟨Pr, hPr1, hPr2⟩ := RadTA.exists_pr (RadTA.fibS Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs)
  have hfib : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ =
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζs hζ hζs]
  have hG : RadTA.Gd Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr := ⟨hB, fun x ζ hζ => by rw [hfib ζ hζ]; exact hPr1 x⟩
  have hPrF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', ∀ x ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Pr x = x := by
    intro ζ hζ x hx
    rw [hfib ζ hζ] at hx
    exact hPr2 x hx
  have hc0 : (fun _ => (1 : ℂ)) ∈ OmX P.r := fun _ => one_ne_zero
  refine ⟨N, fun j => RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j,
    fun j => RadTA.AA_smooth hG hc0 j, ?_⟩
  rintro Φ ⟨c, ζ0⟩ hq
  have hc : c ∈ OmX P.r := hq.1
  have hζ0 : ζ0 ∈ RadTA.Ann Bs.z Bs.z' := hq.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Φ.2
  set ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)
    with hψdef
  have hψs : ContDiffOn ℝ ∞ ψ (RadTA.Ann Bs.z Bs.z') :=
    hmem.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc, hζ⟩
  have hψF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', Pr (ψ ζ) = ψ ζ := fun ζ hζ => hPrF ζ hζ _ (hmem.2.1 (c, ζ) ⟨hc, hζ⟩)
  have hterm : ∀ j, ContDiff ℝ ∞
      (fun ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) := by
    intro j
    exact ((iteratedFDeriv ℝ j ψ ζ0).contDiff.comp
      (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).const_smul _
  set tay : ℂ → (Wq →L[ℂ] Wp) := fun ζ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0) with htay
  have htays : ContDiff ℝ ∞ tay := ContDiff.sum fun j _ => hterm j
  have hR := RadTA.radR_PhiP (μs := Bs.μsec) (π := Bs.π) (π' := Bs.π') hG htays

  have hsum : ∑ j ∈ Finset.range (N + 1), RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j ζ0
        (iteratedFDeriv ℝ j ψ ζ0) = RadTA.VV Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) tay ζ0 :=
    (Finset.sum_congr rfl fun j _ => RadTA.AA_apply hG j ζ0 _).trans
      (RadTA.VV_sum hG (Finset.range (N + 1))
        (fun j ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) hterm ζ0).symm

  have hΦtc : ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c = ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1) := by
    refine RadTA.fn_eq_of_radR hB _ hc hc0 fun ζ => ?_
    rw [hR]
    by_cases hζ : ζ ∈ RadTA.Ann Bs.z Bs.z'
    · simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩),
        Set.indicator_of_mem (show ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc0, hζ⟩)]
    · simp only [RadTA.phiP, Set.indicator_of_notMem (show (c, ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2),
        Set.indicator_of_notMem (show ((fun _ => (1 : ℂ)), ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2)]
  have hT0 := RadTA.t_slice (μs := Bs.μsec) hB X Y a b (RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) hc hc0 hΦtc hζ0

  have hz : ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) ζ0 = 0 := by
    intro i hi
    let Prr : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) := LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)
    have hev : (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) =ᶠ[nhds ζ0] (fun ζ => Prr (ψ ζ - tay ζ)) := by
      filter_upwards [(RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0] with ζ hζ
      rw [Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, hR]
      simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩)]
      show ψ ζ - Pr (tay ζ) = Pr (ψ ζ - tay ζ)
      rw [map_sub, hψF ζ hζ]
    rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
    have hcd : ContDiffAt ℝ ∞ (fun ζ => ψ ζ - tay ζ) ζ0 :=
      (hψs.sub htays.contDiffOn).contDiffAt ((RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0)
    have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left Prr hcd (i := i)
      (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    have h2 : iteratedFDeriv ℝ i (fun ζ => ψ ζ - tay ζ) ζ0 = 0 :=
      hTay (Wq →L[ℂ] Wp) ψ (RadTA.Ann Bs.z Bs.z') ζ0 N (RadTA.ann_open Bs.z Bs.z') hζ0 hψs i hi
    rw [show (fun ζ => Prr (ψ ζ - tay ζ)) = Prr ∘ (fun ζ => ψ ζ - tay ζ) from rfl, h1, h2]
    ext v
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
    simp
  have hZ := hJR Wp Wq P Bs hpl hk (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) (c, ζ0) hq N hz
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem hcs.1 hq
  have hv := hN _ _ hdom.2.1 hZ
  have ht := X.t_apply Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) _ hdom
  have hdiff : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((X.t Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ0) = 0 := by
    rw [RadTA.radR_apply _ hq]
    exact ht.trans hv
  rw [map_sub, Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, sub_eq_zero] at hdiff
  rw [hdiff, hT0]
  exact hsum.symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrame
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section fin

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gcl_fn_mulZ {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    ((X.fn 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∧
      ((X.fn 2 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
  have key : ∀ (j : Fin 6) (f : ℂ → ℂ),
      (∀ g, Q.fnVal P.k P.r Bs.z Bs.z' j g = f (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g)) →
      ((X.fn j Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' f (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro j f hf
    funext c g
    unfold NF.mulZ
    by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
    · rw [Set.indicator_of_mem hx]
      have h1 := X.fn_apply j Φ (c, g) hx
      dsimp only at h1
      rw [h1, hf]
    · simp only [Set.indicator, hx, if_false]
      obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
      exact h0 (c, g) hx
  exact ⟨key 0 id (fun _ => rfl), key 2 (starRingEnd ℂ) (fun _ => rfl)⟩

end fin

private theorem fnZ_apply_eq_snd (P : M.Par) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (q : MA.Qp P.r P.TT) :
    ((fnZ P f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = f q.1.2 := by
  have hmem : (fun q : MA.Qp P.r P.TT => f q.1.2) ∈ MA.smSub P.r P.TT := by
    show ContDiffOn ℝ _ (MA.ext _) (MA.Qset P.r P.TT)
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => x.2) (MA.Qset P.r P.TT) :=
      contDiff_snd.contDiffOn
    refine (hf.comp hs (fun x hx => hx.2)).congr (fun x hx => ?_)
    simp [MA.ext, hx]
  simp only [fnZ, MA.toSm, dif_pos hmem]

theorem local_frame_holds : GTCLFrame := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hN hNs
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hact := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hζ1 : d.L.ζ.1 = X.fn 0 := by
    rw [hact.2.2.2.2.2.2.1]
    rfl
  have hζb1 : d.L.ζb.1 = X.fn 2 := by
    rw [hact.2.2.2.2.2.2.2.2.1]
    rfl
  have hmulζ : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζ.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζ1]
    exact (gcl_fn_mulZ X Φ).1
  have hmulζb : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ((d.L.ζb.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Φ
    rw [hζb1]
    exact (gcl_fn_mulZ X Φ).2
  have hΨζ : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζ.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζ Φ).symm)
  have hΨζb : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
        NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        Ψ = d.L.ζb.1 Φ :=
    fun Φ Ψ h => Subtype.ext (h.trans (hmulζb Φ).symm)
  have c1 : d.L.nab.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nab.1 + 1 := congrArg Prod.fst d.L.nab_ζ
  have c2 : d.L.nab.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nab.1 := congrArg Prod.fst d.L.nab_ζb
  have c3 : d.L.nabs.1 * d.L.ζ.1 = d.L.ζ.1 * d.L.nabs.1 := congrArg Prod.fst d.L.nabs_ζ
  have c4 : d.L.nabs.1 * d.L.ζb.1 = d.L.ζb.1 * d.L.nabs.1 - 1 := congrArg Prod.fst d.L.nabs_ζb
  have hκ1 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nab.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nab.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nab (Or.inr (Or.inl rfl))).eq
    have h1 : (d.κ f).1 * d.L.nab.1 = d.L.nab.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  have hκ2 : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      d.L.nabs.1 ((d.κ f).1 Φ) = (d.κ f).1 (d.L.nabs.1 Φ) := by
    intro f Φ
    have h := (hR.2.1 f d.L.nabs (Or.inr (Or.inr rfl))).eq
    have h1 : (d.κ f).1 * d.L.nabs.1 = d.L.nabs.1 * (d.κ f).1 := congrArg Prod.fst h
    exact (LinearMap.congr_fun h1 Φ).symm
  obtain ⟨A, hAs, hA⟩ := gcl_core P Bs X d hH e he hk d.L.nab.1 hN 1 0
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nab.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nab.1 Φ) + Φ from LinearMap.congr_fun c1 Φ,
        Submodule.coe_add, hmulζ, one_smul])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nab.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nab.1 Φ) from LinearMap.congr_fun c2 Φ,
        hmulζb, zero_smul, add_zero])
    hκ1
  obtain ⟨B, hBs, hB⟩ := gcl_core P Bs X d hH e he hk d.L.nabs.1 hNs 0 (-1)
    (fun Φ Ψ h => by
      rw [hΨζ Φ Ψ h, show d.L.nabs.1 (d.L.ζ.1 Φ) = d.L.ζ.1 (d.L.nabs.1 Φ) from LinearMap.congr_fun c3 Φ,
        hmulζ, zero_smul, add_zero])
    (fun Φ Ψ h => by
      rw [hΨζb Φ Ψ h, show d.L.nabs.1 (d.L.ζb.1 Φ) = d.L.ζb.1 (d.L.nabs.1 Φ) - Φ from LinearMap.congr_fun c4 Φ,
        Submodule.coe_sub, hmulζb, neg_one_smul, sub_eq_add_neg])
    hκ2
  refine ⟨A, B, fun ρ => ⟨hAs ρ, hBs ρ⟩, fun Φ ρ => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    funext q
    rw [hA Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply]
    rw [dzQ_apply P hTT, fnZ_apply_eq_snd P (A ρ) (hAs ρ)]
    ring
  · apply Subtype.ext
    funext q
    rw [hB Φ ρ q]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply,
      Pi.neg_apply]
    rw [dzbQ_apply P hTT, fnZ_apply_eq_snd P (B ρ) (hBs ρ)]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAt
section
namespace Formalism.FourierDecayAlt.P

theorem head_weight_at : PBI.HeadWeightAt := by
  intro Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF
  exact head_weight_at_of_exists Wp Wq P p w X μ L st ν'r m₀r hD hcut hLev x hx γ₀ hγG hζ hγF
    (fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF)

end Formalism.FourierDecayAlt.P
end

