module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsTest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermVolumeClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance

private theorem pair_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.SquareComm.ThetaLeft

theorem isThetaFunO_of_mem_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {M X : HSp D} (A : Fr M) (B : Fr X) {Φ : WO M X → ℂ} (hΦ : Φ ∈ algF ψ θ false A B) :
    IsThetaFunO ψ M X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (M X : HSp D) (A : Fr M) (B : Fr X)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ false M X χ χ' ω → ∀ Φ ∈ algF ψ θ false A B, ∀ γ ∈ GQ M,
    ∀ (g : GA D M) (h : GA D X), thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  intro D ψ θ hθ M X A B χ χ' ω hω Φ hΦ γ hγ g h
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hth : IsThetaFunO ψ M X Φ := isThetaFunO_of_mem_algF hω'.std hθ A B hΦ
  unfold thetaKO
  have e : (γ * g, h) = (γ, (1 : GA D X)) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω'.om_aut _ hγ _ (Subgroup.one_mem _) _ (hω'.om_pres _ _ hth)

end GlobalTheory.SquareComm.ThetaLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionCommutesOnGrid
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem natCast_not_mem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hn) (w.asIdeal.mul_mem_left _ hp)

theorem natCast_mem_w {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) {n : ℕ} (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
  rw [← P.under_w hv] at hn
  have h : (n : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.w v).asIdeal := hn
  rwa [Ideal.mem_comap, map_natCast] at h

end GlobalTheory.SquareComm

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem squareStanding_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {large₂ : SizeData₂ D}
    {R : RealDat D A Ks} {F : Face D A} (s : HidaSetting large₂ R F) (h11 : 11 ≤ D.host.splitBound) {sc : Consts}
    (G : GridData R.toLevCh sc) (t : T) : SquareStanding G t := by
  classical
  refine ⟨h11, fun w hw => ?_⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := s.size
  have hq := D.host.hyp.1
  have hd := D.host.hyp.2.1
  have cop : ∀ p ∈ D.host.levelPrimes, p.Prime →
      Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) p := by
    intro p hpl hp
    exact Nat.Coprime.mul_left (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (Pm.level_split p hpl)).symm
      (D.host.ccK_coprime p (by simp [hpl]))
  have cop0 : Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) (q0 D) := by
    obtain ⟨hp0, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
    have c1 : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
      rw [Nat.Coprime, Nat.gcd_rec, hm]
      simp
    refine Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left ⟨Formalism.MainNotions.rPrAv D, by unfold LevelStarExponents.condE; ring⟩ c1) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp0).2 hn).symm
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
    · exact natCast_not_mem_of_coprime _ cop0 (natCast_mem_w G.pl hv G.pl.basePlace_over_qZero)
    · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 0) (D.host.g_prime 0)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 1) (D.host.g_prime 1)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.1 D.host.pde_prime) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.2 D.host.pde'_prime) (natCast_mem_w G.pl hv h)
  · have h1 := (s.core.lev.Q_off t w hw).1
    have h2 := s.guard.2 t w hw
    simp only [Nat.cast_mul, w.isPrime.mul_mem_iff_mem_or_mem, not_or] at h1 h2 ⊢
    tauto

end GlobalTheory.SquareComm
end
end

