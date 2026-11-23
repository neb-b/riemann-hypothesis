module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_opU_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Formalism.L2.Th1.H.Sesq V) (x : V) {F : V → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU H x F) := by
  have h1 : ContDiff ℂ ⊤ F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun z => H z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hl : ContDiff ℂ ⊤ (fun z => H z x) := (LinearMap.toContinuousLinearMap f).contDiff
  have h2 : ContDiff ℂ ⊤ (fun z => F (z + x)) := h1.comp (contDiff_id.add contDiff_const)
  have h3 : ContDiff ℂ ⊤ (fun z => Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) :=
    ((contDiff_const.mul hl).sub contDiff_const).cexp
  exact h2.mul h3

theorem latInt_U_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hP N N' s hs
  have hS := B.stdOK hcc hδ
  have han : AnalyticOnNhd ℂ B.thMM Set.univ := (B.thMM_spec hS).1.1
  have hLat : La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hA : area (lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  set G : Fin N' → Fin N → (D.what₂.Tau → ℂ) → ℂ := fun i j =>
    Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ i j) B.thMM with hG
  have hU : U D B.tor s (B.thZero N N') = fun z => ∏ i, ∏ j, G i j (entry D.what₂.Tau N N' i j z) := by
    funext z
    rw [U_eq]
    show Formalism.L2.Th1.H.opU (formV (area (lamOf D cc δ)) D.what₂.Tau N N') s (tensPow B.thMM N N') z = _
    rw [hA, opU_tensPow]
    rfl
  have hGc : ∀ i j, ContDiff ℂ ⊤ (G i j) := fun i j => contDiff_opU_of_analytic _ _ han
  have hEc : ∀ i j, ContDiff ℂ ⊤ (fun z : VC D N N' => G i j (entry D.what₂.Tau N N' i j z)) :=
    fun i j => (hGc i j).comp (entry D.what₂.Tau N N' i j).contDiff
  obtain ⟨n, -, hnq, hns⟩ := hs
  rw [hLat] at hns
  have hF : ∀ i j, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (fun z => G i j (entry D.what₂.Tau N N' i j z)) := by
    intro i j
    have hm : LatInt ι (Ω / ι δ₀) B.lamM (G i j) := by
      refine _root_.GlobalTheory.MomN.translates_latInt D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hP (fun τ => s τ i j) n hnq ?_
      have := hns i j
      convert this using 1
      funext τ
      simp [nsmul_eq_mul]
    refine _root_.GlobalTheory.MomN.latInt_pull q ι (D.what₂.Tau → ℂ) (VC D N N') (Ω / ι δ₀) B.lamM
      (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (entry D.what₂.Tau N N' i j) (G i j) (hGc i j) ?_ hm
    intro x hx
    rw [hLat] at hx
    exact ⟨1, Nat.coprime_one_left q, by rw [one_smul]; exact hx i j⟩
  rw [hU]
  refine (_root_.GlobalTheory.MomN.latInt_prod_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N')
    (fun i z => ∏ j, G i j (entry D.what₂.Tau N N' i j z)) (fun i => ?_) (fun i => ?_)
  · exact contDiff_prod fun j _ => hEc i j
  · exact (_root_.GlobalTheory.MomN.latInt_prod_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N)
      (fun j z => G i j (entry D.what₂.Tau N N' i j z)) (hEc i) (hF i)

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolEqMassSelfDualRankGeTwo
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_step (D : D7) (hT : VolTie D) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D)
    (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hPQ : 2 ≤ P + Q)
    (hup : ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U = massI D (P + Q + 1)) :
    D.vol W = massI D (P + Q) := by
  obtain ⟨U, hU, hUs⟩ := _root_.GlobalTheory.exists_hSpace_sigOK_sig D (P + 1) Q
  have hr := _root_.GlobalTheory.VolRatioUp.volRatio_up D hT h2 W P Q hW hs hPQ U hU hUs
  have hb := massRatio_of_definiteVolume D h2 hv (P + Q + 1) (by omega)
  have e : P + Q + 1 - 1 = P + Q := by omega
  rw [e] at hb
  rw [← hb, hup U hU hUs] at hr
  have h1 := massI_pos D (P + Q + 1)
  have h3 := massI_pos D (P + Q)
  have h4 := D.vol_pos W
  field_simp at hr
  nlinarith [hr]

theorem vol_eq_massI_of_two_le_rank : ∀ D : D7, VolTie D → Conclusion2 D → DefiniteVolumeEqMass D → ∀ (W : HSpace D.host.E) (P Q : ℕ),
    W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → D.vol W = massI D (P + Q) := by
  intro D hT h2 hv
  have h2v := volume_eq_mass_of_definite D h2 hv
  have hP1 : ∀ (W : HSpace D.host.E) (Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (1, Q)) → 2 ≤ 1 + Q →
      D.vol W = massI D (1 + Q) := by
    intro W Q hW hs hQ
    refine vol_eq_massI_step D hT h2 hv W 1 Q hW hs hQ fun U hU hUs => ?_
    have := h2v.2 U 2 Q hU hUs le_rfl
    rw [this]; congr 1; omega
  intro W P Q hW hs hPQ
  rcases Nat.lt_or_ge P 2 with hP | hP
  · interval_cases P
    · refine vol_eq_massI_step D hT h2 hv W 0 Q hW hs hPQ fun U hU hUs => ?_
      rw [hP1 U Q hU hUs (by omega)]; congr 1; omega
    · exact hP1 W Q hW hs hPQ
  · exact h2v.2 W P Q hW hs hP

end GlobalTheory.Glob
end

