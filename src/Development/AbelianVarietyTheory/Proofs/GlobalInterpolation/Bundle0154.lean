module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NatFamily

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem exists_taylor_ne (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) (h0 : F ≠ 0) :
    ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D F α ≠ 0 := by
  by_contra h
  push_neg at h
  apply h0
  funext z
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  simp [h]

theorem coef {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) {χ : IdE D → ℂ}
    (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L')
    (hmem : B.eNat χ N N' L L' ∈ Th D B.tor L L') :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (B.eNat χ N N' L L') M := by
  have hC : Crv D cc δ := ⟨hcc, hδ⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ hC
  obtain ⟨he, hne, M₀, hfd, hM₀⟩ := hv N N' L L' hA
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)).1 _ hmem _ he hne
  have hdiff : Differentiable ℂ (e N N' L L') := he.1
  have htay : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by
    intro α
    rw [hc]
    exact GlobalTheory.ProdThetaConj.taylor_const_mul hdiff c α
  obtain ⟨α₀, hα₀⟩ := exists_taylor_ne D hdiff hne
  have halg : Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α₀ ∈ Qbar := by
    have h := (GlobalTheory.MomEq.eq_and_alg).2 D cc δ B χ hcc hδ hχ N N' L L' ⟨hN, hN', hL, hL'⟩ 0
      ⟨1, one_pos, by simp⟩ α₀
    rwa [U_zero] at h
  have hM₀Q : ∀ x ∈ M₀, x ∈ Qbar := by
    intro x hx
    rw [mem_algebraicClosure_iff]
    have : IsIntegral ℚ (⟨x, hx⟩ : M₀) := IsIntegral.of_finite ℚ _
    exact (IntermediateField.isIntegral_iff.1 this).isAlgebraic
  have hcQ : c ∈ Qbar := by
    have e1 : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α₀ / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α₀ := by
      rw [htay, mul_div_cancel_right₀ _ hα₀]
    rw [e1]
    exact div_mem halg (hM₀Q _ (hM₀ α₀))
  have hcI : IsIntegral ℚ c := (mem_algebraicClosure_iff.1 hcQ).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hcI
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ {c}, inferInstance, fun α => ?_⟩
  rw [htay]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ c))
    ((le_sup_left : M₀ ≤ _) (hM₀ α))

theorem family : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.VecP χ ∧ B.LatAll ∧ ∀ a b, B.ThZeroMem a b := by
  intro D cc δ B χ hcc hδ hχ
  have h0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.standard_basis_ok_link D cc hcc δ hδ B
  refine ⟨fun N N' L L' hA => ?_, B.latAll hcc hδ h0, fun a b => B.thZeroMem hS a b⟩
  have hv := B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA
  exact ⟨hv.1, hv.2, coef B hcc hδ hχ hA hv.1⟩

end GlobalTheory.NatFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedVectorTranslatesPrimeOrderIntegral
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_U {D : D7} {N N' : ℕ} (T : Tor D) (t : VC D N N') {G : VC D N N' → ℂ} (hG : ContDiff ℂ ⊤ G) :
    ContDiff ℂ ⊤ (U D T t G) := by
  have hH : ContDiff ℂ ⊤ fun z : VC D N N' => Hf D T z t := by
    unfold Hf
    refine ContDiff.div_const ?_ _
    refine ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine ContDiff.mul ?_ contDiff_const
    fun_prop
  unfold U
  refine ContDiff.mul (hG.comp (contDiff_id.add contDiff_const)) ?_
  exact ContDiff.cexp ((contDiff_const.mul hH).sub contDiff_const)

theorem transPrime_int : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  intro hEq D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hPer χ hχ N N' L L' hA t ht
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime D q hq2 hsplit N N' L L' hA
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    (hEq D cc δ B χ hcc hδ hχ).1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  obtain ⟨g, hg, hU⟩ := GlobalTheory.T.unitaryPairPullback_lattices_translates D cc δ N N' γ γ' M M'
  have ht' : TorsPrime D q (La D B.tor M M') (g t) := by
    obtain ⟨n, hn, hc, hm⟩ := ht
    refine ⟨n, hn, hc, ?_⟩
    have := hg _ hm
    rwa [map_nsmul] at this
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  obtain ⟨m, c, s, hc, hs, heq⟩ :=
    _root_.GlobalTheory.MomN.transl_normVec_int D cc δ B hcc hδ χ hχ q lam N N' M M' hAM hE hE' (g t) ht'
  have hzero : ∀ k, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (U D B.tor (s k) (B.thZero N N')) := fun k =>
    _root_.GlobalTheory.MomN.latInt_U_thZero D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hPer N N' (s k) (hs k)
  have hd : ContDiff ℂ ⊤ (B.thZero N N') :=
    AnalyticOnNhd.contDiff (B.thZeroMem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) N N').1
  have hsm : ∀ k, ContDiff ℂ ⊤ (U D B.tor (s k) (B.thZero N N')) := fun k => contDiff_U _ _ hd
  have hcn : ∀ k, ‖ι (c k)‖ ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hc k
    have e : lamC lam (c k) = ι (c k) := by
      unfold lamC
      rw [dite_eq_left h1]
      rfl
    rw [← e]
    exact h2
  have hsum := (_root_.GlobalTheory.MomN.latInt_prod_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).2
    (Fin m) Finset.univ c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k _ => hsm k) (fun k _ => hcn k)
    (fun k _ => hzero k)
  have hGs : ContDiff ℂ ⊤ fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z :=
    ContDiff.sum fun k _ => contDiff_const.mul (hsm k)
  obtain ⟨a, ha, hsM, hMs⟩ := hE
  obtain ⟨b, hb, hsM', hMs'⟩ := hE'
  have hpull := _root_.GlobalTheory.MomN.latInt_pull q ι (VC D N N') (VC D N N') (Ω / ι δ₀)
    (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
    (La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) g _ hGs
    (fun x hx => ⟨a * b, Nat.Coprime.mul_left ha hb,
      Formalism.L2.KerInert.ISd.La_smul cc δ a b hsM hMs' (hg x hx)⟩) hsum
  rw [← hcov, show U D B.tor t (pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.eNat χ N N' M M')) =
      fun z => U D B.tor (g t) (B.eNat χ N N' M M') (g z) from hU t _, heq]
  exact hpull

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_all_sig : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  intro D hT h2 W P Q hW hs
  have hv : DefiniteVolumeEqMass D := mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
    (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    rw [← hrk]
    exact hv W hW (fun τ => by rw [hs τ, hrk]; rfl)
  · by_cases h2r : 2 ≤ P + Q
    · exact _root_.GlobalTheory.Glob.vol_eq_massI_of_two_le_rank D hT h2 hv W P Q hW hs h2r
    · have hP : P = 0 := by omega
      have hQ1 : Q = 1 := by omega
      subst hP hQ1
      have e1 : D.vol W = D.vol (GlobalTheory.NegSpace.neg W) :=
        _root_.GlobalTheory.NegVol.vol_neg_eq D hT W 1 hW hs
      have hN : (GlobalTheory.NegSpace.neg W).SigOK := _root_.GlobalTheory.NegSpace.sigOK_neg _ W hW
      have e2 : D.vol (GlobalTheory.NegSpace.neg W) = massI D (GlobalTheory.NegSpace.neg W).rank :=
        hv _ hN (fun τ => by rw [GlobalTheory.NegSpace.neg_sig, hs τ, GlobalTheory.NegSpace.neg_rank, hrk])
      rw [e1, e2, GlobalTheory.NegSpace.neg_rank, hrk]

end GlobalTheory.Glob
end

