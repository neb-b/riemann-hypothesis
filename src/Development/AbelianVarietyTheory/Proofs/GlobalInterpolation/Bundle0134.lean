module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalLevelRelIndexAtLevelPrimeSelfDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SWQ.FourierSeries

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem bd_rat_add (a : Fin N → F) (η ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a (rat η + u) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) + Bd (AF F) a u (rat ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bd, rat, Pi.add_apply, map_sum, map_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem bd_sub (a : Fin N → F) (ξ' ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a u (rat ξ') + -Bd (AF F) a u (rat ξ) = Bd (AF F) a u (rat (ξ' - ξ)) := by
  simp only [Bd, rat, Pi.sub_apply, map_sub, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem bd_zero (a : Fin N → F) (u : Fin N → AF F) : Bd (AF F) a u (rat 0) = 0 := by
  simp [Bd, rat]

theorem continuous_bd (a : Fin N → F) (ξ : Fin N → F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u (rat ξ) := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.FourierSeries

namespace GlobalTheory.SWQ.FourierSeries

theorem countable_fn (F : Type) [Field F] [NumberField F] (N : ℕ) : Countable (Fin N → F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  infer_instance

theorem fourier_series : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ (P : (Fin N → AF F) → ℂ) (c : (Fin N → F) → ℂ), Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ) → Summable (fun ξ => ‖c ξ‖) → ∀ u, P u = ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) := by
  intro F _ _ N ψ lam ν a hC D hD hD1 P c hP hper hc hsum
  classical
  have hC' := hC
  obtain ⟨_, ⟨hψc, hψn, hψF, -⟩, -, hcov, -⟩ := hC'
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, -⟩ := _root_.GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hcov
  haveI : Countable (Fin N → F) := countable_fn F N
  haveI : IsFiniteMeasure ((muV N ν).restrict D) := isFiniteMeasure_restrict.mpr (by rw [hD1]; simp)
  have hmass : ((muV N ν).restrict D) Set.univ = 1 := by rw [Measure.restrict_apply_univ, hD1]
  have he : ∀ ξ, Continuous fun u : Fin N → AF F => ψ (Bd (AF F) a u (rat ξ)) :=
    fun ξ => hψc.comp (continuous_bd a ξ)
  set S : (Fin N → AF F) → ℂ := fun u => ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) with hSdef
  have hS : Continuous S := continuous_tsum (fun ξ => continuous_const.mul (he ξ)) hsum
    (fun ξ u => by simp [norm_mul, hψn])
  have hSper : ∀ η u, S (rat η + u) = S u := by
    intro η u
    simp only [hSdef, bd_rat_add, AddChar.map_add_eq_mul, hψF, one_mul]

  obtain ⟨M, hM⟩ : ∃ M, ∀ u, ‖P u‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hP.norm).bddAbove
    refine ⟨M, fun u => ?_⟩
    obtain ⟨ξ, hξ⟩ := hKc u
    have : P u = P (u - rat ξ) := by
      rw [← hper ξ (u - rat ξ)]; congr 1; abel
    rw [this]; exact hM ⟨_, hξ, rfl⟩
  set Q : (Fin N → AF F) → ℂ := fun u => P u - S u with hQdef
  have hQc : Continuous Q := hP.sub hS
  have hQper : ∀ ξ u, Q (rat ξ + u) = Q u := fun ξ u => by simp only [hQdef, hper, hSper]
  have hint : ∀ f : (Fin N → AF F) → ℂ, Continuous f → ∀ B : ℝ, (∀ u, ‖f u‖ ≤ B) →
      Integrable f ((muV N ν).restrict D) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  have hcoefS : ∀ ξ, ∫ u in D, S u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ := by
    intro ξ
    have hterm : ∀ ξ' u, c ξ' * ψ (Bd (AF F) a u (rat ξ')) * ψ (-(Bd (AF F) a u (rat ξ))) =
        c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro ξ' u
      rw [mul_assoc, ← AddChar.map_add_eq_mul, bd_sub]
    have hsw : ∀ u, S u * ψ (-(Bd (AF F) a u (rat ξ))) =
        ∑' ξ', c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro u
      simp only [hSdef, ← tsum_mul_right, hterm]
    simp_rw [hsw]
    have hInt : ∀ ξ', Integrable (fun u => c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))))
        ((muV N ν).restrict D) :=
      fun ξ' => hint _ (continuous_const.mul (he _)) ‖c ξ'‖ (fun u => by simp [norm_mul, hψn])
    have hnorm : ∀ ξ', ∫ u in D, ‖c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ)))‖ ∂(muV N ν) = ‖c ξ'‖ := by
      intro ξ'
      simp only [norm_mul, hψn, mul_one]
      rw [integral_const, smul_eq_mul, measureReal_def, hmass]; simp
    rw [← integral_tsum_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum)]
    have hval : ∀ ξ', ∫ u in D, c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) ∂(muV N ν) =
        if ξ' = ξ then c ξ else 0 := by
      intro ξ'
      rw [integral_const_mul]
      split_ifs with h
      · subst h
        simp only [sub_self, bd_zero, AddChar.map_zero_eq_one]
        simp [integral_const, measureReal_def, hmass]
      · rw [_root_.GlobalTheory.SWQ.charOrth F N ψ lam ν a hC D hD hD1 (ξ' - ξ) (sub_ne_zero.mpr h), mul_zero]
    simp_rw [hval]
    simp
  have hQcoef : ∀ ξ : Fin N → F, ∫ u in D, Q u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0 := by
    intro ξ
    have h1 : Integrable (fun u => P u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hP.mul (hψc.comp (continuous_bd a ξ).neg)) M (fun u => by simpa [norm_mul, hψn] using hM u)
    have hSb : ∀ u, ‖S u‖ ≤ ∑' ξ, ‖c ξ‖ := fun u =>
      (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun ξ' => by simp [norm_mul, hψn]))).trans
        (le_of_eq (tsum_congr fun ξ' => by simp [norm_mul, hψn]))
    have h2 : Integrable (fun u => S u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hS.mul (hψc.comp (continuous_bd a ξ).neg)) _ (fun u => by simpa [norm_mul, hψn] using hSb u)
    simp only [hQdef, sub_mul]
    rw [integral_sub h1 h2, hc, hcoefS, sub_self]
  have hQ0 := _root_.GlobalTheory.SWQ.periodic_eq_zero_of_coeff F N ψ lam ν a hC D hD hD1 Q hQc hQper hQcoef
  intro u
  have := congrFun hQ0 u
  simp only [hQdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.SWQ.FourierSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volMeas_fundDomain_eq_of_tiedIndep :
    (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  intro H D W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr μ 𝓕 μ₀ 𝓕₀ hμ h𝓕 hμ₀ h𝓕₀
  have hT : VolTie (GlobalTheory.Mem.retie D) :=
    Formalism.L2.Theta.VolTieG.volTie (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have e1 : μ 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W) :=
    ((hT W P Q hW hs).2 μ hμ).2 𝓕 h𝓕
  have e2 : μ₀ 𝓕₀ = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W₀) :=
    ((hT W₀ P₀ Q₀ hW₀ hs₀).2 μ₀ hμ₀).2 𝓕₀ h𝓕₀
  rw [e1, e2, H (GlobalTheory.Mem.retie D) hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr]

end GlobalTheory.Glob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMass
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRestObj

theorem defClassRest : ∀ D : D7, DefClassRest D := by
  intro D W hW hsig
  obtain ⟨⟨θ, hθ⟩, A, hA⟩ := GlobalTheory.DecompCompare.exists_data D W hW hsig
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨-, n, g, hcov, hdisj, -, hsum⟩ := GlobalTheory.DefiniteDecompObj.doubleCosets_mass D W hW hsig θ hθ A hA
  rw [hK] at hcov hdisj hsum
  exact ⟨n, g, hcov, hdisj, hsum⟩

end GlobalTheory.ClassRestObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LawsAndChart
section
open PowerSeries GlobalTheory.MomOne GlobalTheory.MomN
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomN.PeriodData

variable {q : ℕ} [Fact q.Prime]

theorem laws_and_chart (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (L : PeriodPair)
    (hd : d.Prime) (h7 : d % 16 = 7) (hs : Split d q) (hL : IsOK d L)
    (hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) (hδ : δ ^ 12 = discr d) (hδ0 : δ ≠ 0) (hθ : IsTh d θ) :
    ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ ∧
      ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ) := by
  obtain ⟨M, rfl, rfl, hok, a1, a2, a3, a4, a6⟩ := _root_.GlobalTheory.MomOne.exists_model d q ι L hd h7 hL
  obtain ⟨ω₀, hω₀⟩ := _root_.GlobalTheory.MomOne.SplitChart.exists_mChart d q M hd h7 hs hL hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hn⟩ := _root_.GlobalTheory.MomOne.Norm.exists_normalised_chart d q M ω₀ hd h7 hs hL hω₀
  set ω := ω₀ * zc a
  have hι : M.ι δ ≠ 0 := by simpa using hδ0
  refine ⟨ω * M.ι δ, ?_, ?_, M, rfl, hL, ?_⟩
  · rw [norm_mul, (GenusOne.norm_root_eq M hok δ (hδ.trans hD.symm)).1, GenusOne.norm_period M ω hω]
  · rw [mul_div_cancel_right₀ _ hι]
    have hN := _root_.GlobalTheory.MomOne.TranslNorm.norm_law d q M ω θ hd h7 hs hL hω hθ
    refine ⟨fun t ht => ?_, _root_.GlobalTheory.MomOne.TranslateLaw.main d q M ω θ hd h7 hs hL hω hθ hn, hN⟩
    have hU := (_root_.GlobalTheory.MomOne.heisenbergOne d hd.pos).2.1
    have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩
    have := hN 1 1 (fun _ => 1) (fun _ => 0) t 1 (fun _ => h0) ht
      (by simpa [hU] using _root_.GlobalTheory.MomOne.theta_series_integral d q M ω θ hd h7 hs hL hω hθ)
    simpa [hU] using this
  · rw [mul_div_cancel_right₀ _ hι]; exact hω

end GlobalTheory.MomN.PeriodData

namespace GlobalTheory.MomN

theorem exists_per : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q →
    ∃ (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per d ι δ₀ θ Ω := by
  intro d q _ ι hd h7 hs
  obtain ⟨δ₀, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr d) (by norm_num : 0 < 12)
  obtain ⟨⟨L, hL, hD⟩, θ, hθ⟩ := _root_.GlobalTheory.MomOne.exists_pair_and_isTh d hd h7
  have hδ0 : δ₀ ≠ 0 := (GenusOne.thetaLaws_unit_period d q δ₀ hd h7 hs hδ).choose_spec.2.1
  obtain ⟨Ω, hΩ, hT, hM⟩ := PeriodData.laws_and_chart d ι δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  refine ⟨δ₀, θ, Ω, hθ, hδ, hδ0, fun ι' => ?_, hΩ, hT, hM⟩
  obtain ⟨Ω', h1, h2, -⟩ := PeriodData.laws_and_chart d ι' δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  exact ⟨Ω', h1, h2⟩

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabiliserSelfDualLatticeLevelIndexFormula
section
namespace GlobalTheory.LevelIndex

theorem selfDualLatticeIndex_stabiliserLevelIndexFormula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel.indexKU_iff.mp
    (GlobalTheory.LevelIndex.indexKU_of_selfDualOverBase
      (GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice))

end GlobalTheory.LevelIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Unfolding
section
namespace GlobalTheory.UnfoldingObj

theorem unfolding : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D := fun D =>
  (GlobalTheory.UnfoldingCompare.unfolding_iff D).1 (_root_.GlobalTheory.VolumeUnfolding.unfolding _root_.GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures _root_.GlobalTheory.adelicUnitaryHaar_holds _root_.GlobalTheory.StabOrbit.stabTransitive D)

end GlobalTheory.UnfoldingObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrimeStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  first | exact @GlobalTheory.MomN.weakApprox_split | exact GlobalTheory.MomN.weakApprox_split | (intros; apply GlobalTheory.MomN.weakApprox_split <;> assumption)
end

