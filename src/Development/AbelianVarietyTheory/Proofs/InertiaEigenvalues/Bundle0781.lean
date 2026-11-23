module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastStepIntertwinerOneTupleAllTuples
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe GlobalTheory.CompactHowe.LastStep
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwinerTransfer

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isItW_transfer (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (hd : ∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) (hd' : ∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt pt₁ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ))
    (hpt : Function.Injective pt) (hpt₁ : Function.Injective pt₁)
    (hω : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ))
    (hω' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ))
    (hω₁ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω₁ (atTau θ V τ g, 1) (pt₁ φ) = pt₁ (ρ τ g φ))
    (hω₁' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω₁ (1, atTau θ W τ h) (pt₁ φ) = pt₁ (ρ' τ h φ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hIt : IsItW θ M M' ω pt It) :
    IsItW θ M M' ω₁ pt₁ It := by
  refine ⟨hIt.ne, hIt.bdd, ?_, ?_, ?_, ?_⟩
  · intro τ g hg φ φ' h v
    rw [hω₁ τ g hg] at h
    refine hIt.eqK τ g hg φ φ' ?_ v
    rw [hω τ g hg, hpt₁ h]
  · intro τ X hX φ φ' h v
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M τ) hX t
    simp only [oneP, hω₁ τ _ (hm _)] at h
    refine hIt.eqg τ X hX φ φ' (fun z => ?_) v
    simp only [oneP, hω τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)
  · intro τ h hh φ φ' v v' e e'
    rw [hω₁' τ h hh] at e
    refine hIt.invK τ h hh φ φ' v v' ?_ e'
    rw [hω' τ h hh, hpt₁ e]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M' τ) hX t
    simp only [oneP, hω₁' τ _ (hm _)] at h
    refine hIt.invg τ X hX φ φ' v v' (fun z => ?_) h'
    simp only [oneP, hω' τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd' τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)


open Classical in
theorem isItW_lastStep_transfer (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK)
    (hW : W.SigOK) (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f f₁ : WO V W → ℂ)
    (hω : IsStepWeil k ψ V W ω) (hf : IsVacVec ψ θ M M' f) (hω₁ : IsStepWeil k ψ V W ω₁) (hf₁ : IsVacVec ψ θ M M' f₁)
    (hIt : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : IsItW θ M M' ω₁ (ptOf ψ θ M M' f₁) It := by
  subst ha
  have hp := fun τ => _root_.GlobalTheory.LastStepParam.lastStep_param D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 _ using fun τ => (hp τ).2.2
  have act : ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω →
      IsVacVec ψ θ M M' f →
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) (fun _ => 1) φ)) ∧
      (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h) φ)) := by
    intro ω f hω hf
    refine ⟨fun τ g hg φ => ?_, fun τ h hh φ => ?_⟩
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
      rwa [compAt_atTau hθ τ hg, compAt_one] at this
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
      rwa [compAt_atTau hθ τ hh, compAt_one] at this
  have a0 := act ω f hω hf
  have a1 := act ω₁ f₁ hω₁ hf₁
  exact isItW_transfer θ M M' (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h))
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) ω ω₁
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₁)
    (_root_.GlobalTheory.FockInj.ptOf_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf)
    (_root_.GlobalTheory.FockInj.ptOf_injective D V W _ _ ψ θ M M' f₁ hω₁.choose_spec.choose_spec.1.std hθ hf₁)
    a0.1 a0.2 a1.1 a1.2 It hIt

theorem pItX_of_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hω hv t₀ y hy t
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => _root_.GlobalTheory.LastStepVac.last_step D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  exact isItW_lastStep_transfer k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
    (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ y (R.ωX t₀) (R.ωX t) (R.vX t₀) (R.vX t) (hS t₀).1 (hS t₀).2 (hS t).1 (hS t).2 hy

end GlobalTheory.IntertwinerTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.BadSuppPf

theorem rank_le (D : D7) (i : Fin D.R.m) : (Wc D i).rank ≤ (Vc D i).rank := by
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  exact r_le_V i

theorem badSupp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ P hP e f hPf k hk hnot
  classical
  have hv := hL.thP.vP i t
  have hθ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  obtain ⟨-, e', he', hth⟩ := hv
  obtain ⟨cV, hBV⟩ := hL.lev.βV i
  obtain ⟨cW, hBW⟩ := hL.lev.βW i
  rw [one_pow] at hBV hBW
  have hsdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i)
  have hsdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i)
  have hdat : (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e') x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
          omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) = GlobalTheory.FinZeta.levDatum (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t) (R.xiR t) e' := by
    funext x
    simp only [GlobalTheory.FinZeta.levDatum, GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv R i]
  rw [hdat] at hth
  obtain ⟨hkf, hk1⟩ := GlobalTheory.SuppLocal.suppF_local D (Wc D i) P e f k hPf hk
  have hZ : ∀ PP, PP ∈ R.Pg ∪ R.Q t ↔ PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ R.Q t := fun PP => Finset.mem_union
  have hsb := GlobalTheory.FinZeta.isSBHalf_levDatum D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv)
    (R.Q t) (R.xiR t) (R.Pg ∪ R.Q t) e' hsdV hsdW hBV.1 hBW.1 he'
  have horth := GlobalTheory.ThetaOrth.orth D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hF i t).datum (R.ΛV i) (R.ΛW i) hsdV hsdW
    (R.Pg ∪ R.Q t) e' he' (R.vacP i) _ (R.vP i t) hsb hth hθ μ 𝓕 hμ k hkf (fun x hx => by
      by_contra hx'
      obtain ⟨k', hk', hag⟩ := _root_.GlobalTheory.SuppLev.supp_level D (Vc D i) (Wc D i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
        (R.xiR t) (R.Pg ∪ R.Q t) e' hsdW hBW.1 (rank_le D i) rfl he' hZ k hkf x hx hx'
      apply hnot
      have hlo := (GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i R.triv) ((R.Pg ∪ R.Q t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) hBW
        (fun PP hPP => Finset.mem_image_of_mem _ (by
          rcases hPP with h | h
          · exact Finset.mem_union_left _ h
          · exact absurd h (Finset.notMem_empty _)))).2.1 k hkf
      refine hlo.2 ⟨⟨k', hk', fun v hvS => ?_⟩, fun v hvS => ?_⟩
      · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hvS
        exact hag PP hPP
      · have hne : v ≠ P.under (𝓞 D.host.F) := fun h => hvS (h ▸ Finset.mem_image_of_mem _
          (hP.elim (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ h)))
        rw [hk1 v hne]
        exact Subgroup.one_mem _)
  have h0 : thetaIP μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := by
    have h1 : Formalism.IndefR.Lift.pet μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := horth
    unfold Formalism.IndefR.Lift.pet at h1
    unfold thetaIP
    have h2 : (fun w => star (R.ωP i t (1, k) (R.vP i t) w) * R.vP i t w) =
        fun w => starRingEnd ℂ (R.ωP i t (1, k) (R.vP i t) w * starRingEnd ℂ (R.vP i t w)) := by
      funext w; simp [mul_comm]
    rw [h2, integral_conj, h1, map_zero]
  unfold coef
  rw [h0, zero_div]

end GlobalTheory.BadSuppPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatOfIsIntMAdjConjHalf
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatAdj

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.DatumFourier

variable {D : D7}

theorem tie_mul_inv_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (f * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h0 : FractionalIdeal.count D.host.E Q D.host.AA⁻¹ = 0 := by
    rw [FractionalIdeal.count_inv, hQ, neg_zero]
  obtain ⟨b, t, ht, hbc⟩ := GlobalTheory.exists_den_not_mem_of_count_eq_zero Q _ h0 hc
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D b)
  have e : c = (t : D.host.E)⁻¹ * (b : D.host.E) := by
    rw [eq_inv_mul_iff_mul_eq₀ ht0']
    exact hbc
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_inv_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (cA D (GlobalTheory.ExportSeries.idem Pg) * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine tie_mul_inv_mem ht.conj ?_ hc
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))


set_option maxHeartbeats 4000000 in
theorem mem_latO_of_adj_int {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q) {x : WO S T}
    (hx : IsHalf (cA D (GlobalTheory.ExportSeries.idem Pg)) x) (hi : IsIntM (frMapAdj S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set e : AE D := GlobalTheory.ExportSeries.idem Pg with he_def
  have he : IsIdemSum e Pg := by
    obtain ⟨P, h1, -, hsp⟩ := hP.split
    exact (hsp.mono h1).isIdemSum
  obtain ⟨L, pa, pc, hpa, hpc, hac⟩ := GlobalTheory.HostAAPartition.host_AA_partition D
  have hpc' : ∀ l, pc l ∈ D.host.AA⁻¹ := fun l => by
    refine (FractionalIdeal.mem_inv_iff (GlobalTheory.HostAAPartition.host_AA_ne_zero D)).2 fun y hy => ?_
    obtain ⟨b, hb⟩ := hpc l y hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S ΛS hS
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t k a := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * S.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : t₁ * (t₂ᴴ * T.gram) = 1 := by
    subst ht₁ ht₂
    exact Matrix.ext fun a j => (htt a j).trans (Matrix.one_apply).symm
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin m) (Fin n) (AE D), w = (t₂ᴴ * T.gram).map (incA D) * x * s₁.map (incA D) := ⟨_, rfl⟩
  have hx' : cA D e • x = x := Matrix.ext hx
  have hw1 : cA D e • w = w := by rw [hw, ← Matrix.smul_mul, ← Matrix.mul_smul, hx']
  have hG : T.gramᴴ = T.gram := Matrix.ext fun i j => gram_star T j i
  have hw2 : ((w.map (toEAf D)).map (cF D))ᵀ = (s₁ᴴ * S.gram).map (eToEAf D) * βS.val * frMapAdj S T βS βT x *
      ((βT⁻¹).val * t₂.map (eToEAf D)) := by
    rw [hw, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := cF D),
      Matrix.map_mul (f := cF D), Matrix.transpose_mul,
      Matrix.transpose_mul, conj_map, conj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      frMapAdj_eq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc βT.val, Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (S.gram.map (eToEAf D)), gram_map_mul_inv, Matrix.one_mul]
  have hcol : ∀ a, (fun k => βS.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS := fun a => by
    refine (fS _).2 fun i => ?_
    have e : ((βS⁻¹).val *ᵥ fun k => βS.val k a) i = ((βS⁻¹).val * βS.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : IsIntM ((s₁ᴴ * S.gram).map (eToEAf D) * βS.val) := fun k a => by
    refine GlobalTheory.PairIntegral.sum_mem_intAf ΛS (fun j => (s₁ᴴ * S.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hS.2 y).1 hy _ (hs k).1
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm, hs₁]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : IsIntM ((βT⁻¹).val * t₂.map (eToEAf D)) := fun a k => by
    rw [ht₂]
    exact (fT _).1 (pure_mem_hatL ΛT 1 (one_mem _) _ (ht k).2) a
  have hwe : ∀ i k, cA D e * w i k = w i k := fun i k => congrFun (congrFun hw1 i) k
  have hw3 : ∀ i k l, toEAf D (w i k * incA D (pc l)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i k l => by
    have h1 : cF D (toEAf D (w i k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [show cF D (toEAf D (w i k)) = _ from congrFun (congrFun hw2 k) i, Matrix.mul_apply]
      refine sum_mem fun p _ => mul_mem ?_ (i2 p i)
      rw [Matrix.mul_apply]
      exact sum_mem fun q _ => mul_mem (i1 k q) (hi q p)
    have h2 : toEAf D (w i k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := cF_mem_int h1
      rwa [cF_cF_toEAf] at this
    rw [← hwe i k, mul_comm (cA D e) (w i k), mul_assoc, RingHom.map_mul]
    exact mul_mem h2 (toEAf_cA_idem_mul_inv_mem hP (hpc' l))
  have hxw : x = t₁.map (incA D) * w * (s₂ᴴ * S.gram).map (incA D) := by
    rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, e2, Matrix.mul_assoc, ← Matrix.map_mul, e1,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mul, Matrix.mul_one]
  have hsum : x = ∑ k, ∑ i, ∑ l, (w i k * incA D (pc l)) • finTens 1 (genMap S T (pa l) (s' k) (t i)) := by
    rw [hxw]
    ext a j
    simp only [Matrix.mul_apply (M := t₁.map (incA D) * w), Matrix.mul_apply (M := t₁.map (incA D)), Matrix.sum_apply,
      Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have h0 : infPart D (w i k) = 0 := by
      rw [← hwe i k, RingHom.map_mul, infPart_cA (idemSum_infPart he), zero_mul]
    have hterm : ∀ l, (w i k * incA D (pc l)) * finTens 1 (genMap S T (pa l) (s' k) (t i)) a j =
        w i k * incA D (pc l * pa l * (t₁ a i * (s₂ᴴ * S.gram) k j)) := fun l => by
      have h4 : finPart D (finTens 1 (genMap S T (pa l) (s' k) (t i)) a j) =
          finPart D (incA D (pa l * t₁ a i * (s₂ᴴ * S.gram) k j)) := by
        rw [ht₁, hs₂]; rfl
      refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
      rw [RingHom.map_mul, RingHom.map_mul, h4, ← RingHom.map_mul, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D)]
      congr 3
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
    have hac' : ∑ l, pc l * pa l = 1 := by rw [← hac]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hac', one_mul, Matrix.map_apply, Matrix.map_apply, mul_comm (incA D (t₁ a i)), mul_assoc, ← RingHom.map_mul]
  rw [hsum]
  exact sum_mem fun k _ => sum_mem fun i _ => sum_mem fun l _ =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hw3 i k l)) _
      (finTens_mem_latO (one_mem_intAf _) (AddSubgroup.subset_closure ⟨_, hpa l, _, (hs k).2, _, (ht i).1, rfl⟩))

end General

end GlobalTheory.ConjLatAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D}

def divPts (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {y | c • y = y ∧ N • y ∈ Λ}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], by rw [nsmul_add]; exact Λ.add_mem hx2 hy2⟩
  zero_mem' := ⟨smul_zero _, by rw [nsmul_zero]; exact Λ.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], by rw [smul_neg]; exact Λ.neg_mem hx2⟩

theorem mem_divPts {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} {y : WO S T} :
    y ∈ divPts Λ c N ↔ c • y = y ∧ N • y ∈ Λ := Iff.rfl

abbrev DQ (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) :=
  ↥(divPts Λ c N) ⧸ (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N)

noncomputable def rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) : ↥(divPts Λ c N) :=
  (QuotientAddGroup.mk_surjective q).choose

theorem mk_rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) :
    (QuotientAddGroup.mk (rep q) : DQ Λ c N) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

theorem rep_injective {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} :
    Function.Injective fun q : DQ Λ c N => ((rep q : ↥(divPts Λ c N)) : WO S T) := by
  intro q₁ q₂ h
  rw [← mk_rep q₁, ← mk_rep q₂, Subtype.ext h]

variable (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

end GlobalTheory.DivPtFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}


open Classical in
def allP (B : Base S T) (Q : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := B.G.Pg ∪ (B.de.Q ∪ Q)


open Classical in
def resP (B : Base S T) (ν : Twist D Circle) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  (if PP ∈ B.G.Pg then B.G.muC PP else 1) * B.de.locC PP * ν.locC PP

def vacC (B : Base S T) (ν : Twist D Circle) (g : GA D S) (h : GA D T) : ℂˣ :=
  ∏ PP ∈ allP B ν.Q, (resP B ν PP (GeneralLinearGroup.det (redFn B.F.βS PP (Lev.finE S g))))⁻¹ *
    resP B ν PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T h)))

end GlobalTheory.ExportSeries.DualType
end
end

