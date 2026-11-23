module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate
section
open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

noncomputable section

namespace GlobalTheory.AlgTranslate

open GlobalTheory.GalTheta

theorem taylor_sum (D : D7) {N N' : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem exists_alg_comb (D : D7) {N N' k : ℕ} (c : Fin k → ℂ) (f : Fin k → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (ha : ∀ i, CoefIn D (f i) Qbar)
    (h : CoefIn D (fun z => ∑ i, c i * f i z) Qbar) :
    ∃ c' : Fin k → ℂ, (∀ i, c' i ∈ Qbar) ∧ (fun z => ∑ i, c i * f i z) = fun z => ∑ i, c' i * f i z := by
  obtain ⟨pr, hpr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hp : ∀ a : Qbar, pr (a : ℂ) = a := fun a => LinearMap.congr_fun hpr a
  refine ⟨fun i => pr (c i), fun i => (pr (c i)).2, ?_⟩
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α =
      TaylorLogMetric.taylor D (fun z => ∑ i, (pr (c i) : ℂ) * f i z) α := by
    intro α
    have h1 : (pr (TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α) : ℂ) =
        TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α := congrArg Subtype.val (hp ⟨_, h α⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, taylor_sum D _ _ _ hf, taylor_sum D _ _ _ hf, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * TaylorLogMetric.taylor D (f i) α = (⟨_, ha i α⟩ : Qbar) • c i := mul_comm _ _
    rw [this, map_smul, mul_comm]
    rfl
  funext z
  have e1 := GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' (fun z => ∑ i, c i * f i z) (by fun_prop) z
  have e2 := GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' (fun z => ∑ i, (pr (c i) : ℂ) * f i z) (by fun_prop) z
  simp only [ht] at e1
  exact e1.unique e2

theorem coefIn_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), StandardLatticesGL3.Crv D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → ∀ e ∈ Th D (tor0 D cc δ) L L', CoefIn D e Qbar → ∀ x, StandardLatticesGL3.LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x e) Qbar := by
  intro D cc δ hc N N' L L' hL hL' e he hq x hx
  have hG : StandardLatticesGL3.admG1 D := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨-, -, -, -, hfg, -, -⟩ :=
    _root_.GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)
  obtain ⟨m, r, B, hB⟩ := _root_.GlobalTheory.FourCopies.exists_onB_four D N N'
  obtain ⟨R, hR, hRA⟩ := _root_.GlobalTheory.PadCommensurable.nsmul_pad_mem D hG cc δ hc N N' m r L L' B hB hfg
  have hee : IsTr D (tor0 D cc δ) (La D (tor0 D cc δ) L L') e e := by
    have := IsTr.single D (tor0 D cc δ) (A := La D (tor0 D cc δ) L L') e 1 0 1 one_pos (by simp)
    simpa [U_zero] using this
  obtain ⟨G₁, ⟨k, c, t, n, hn, ht, rfl⟩, hGG⟩ := exists_restriction D cc δ hc L L' hL hL' B hB e e he hee
  have hS := GlobalTheory.ThetaAlgebraic.good_sigma hG (_root_.GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D) hc hB
  set S := StandardLatticesGL3.pullB D (tor0 D cc δ) B (sgStar (lamOf D cc δ))
  have hT := fun i => hS.transl hG hc hB (t := t i) ⟨n, hn, ht i⟩
  have hd : ∀ i, Differentiable ℂ (U D (tor0 D cc δ) (t i) S) := fun i => (hS _ ⟨n, hn, ht i⟩).differentiable
  obtain ⟨c', hc', he'⟩ := exists_alg_comb D c (fun i z => U D (tor0 D cc δ) (t i) S (pad D m z))
    (fun i => (hd i).comp (differentiable_pad D m))
    (fun i α => by
      rw [GlobalTheory.ConjRestrict.taylor_pad D m (hd i)]
      exact (hT i).coefIn _)
    (by rw [hGG] at hq; exact hq)
  have hg := GlobalTheory.ThetaAlgebraic.Good.sum Finset.univ _ fun i _ => (hT i).const_mul (hc' i)
  have hpx : pad D m x ∈ GlobalTheory.ThetaAlgebraic.sat (StandardLatticesGL3.LaB D (tor0 D cc δ) B) := by
    obtain ⟨j, hj, hx⟩ := hx
    refine ⟨R * j, mul_pos hR hj, ?_⟩
    rw [mul_smul, ← pad_nsmul]
    exact hRA _ hx
  have hgen := hg _ hpx
  have e1 : e = fun z => (fun w => ∑ i, c' i * U D (tor0 D cc δ) (t i) S w) (pad D m z) := hGG.trans he'
  intro α
  rw [e1, U_pad D _ m x (fun w => ∑ i, c' i * U D (tor0 D cc δ) (t i) S w),
    GlobalTheory.ConjRestrict.taylor_pad D m hgen.differentiable]
  exact hgen.coefIn _

end GlobalTheory.AlgTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.CrysFromGTwo

theorem matRep_twistM {K Γ : Type} [Field K] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) K)
    (χ : Γ →* Kˣ) (g : Γ) (v : Fin k → K) :
    matRep (twistM M χ) g v = ((χ g : Kˣ) : K) • matRep M g v := by
  change (((χ g : Kˣ) : K) • M g).mulVec v = ((χ g : Kˣ) : K) • (M g).mulVec v
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ h

theorem crys_chi (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π))))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  exact GlobalTheory.ChiOneEnl.chiOneE_of_isBlockSum hF D i r ρ π hs hc w hw C.LL C.le

theorem twist_mat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K LL : FinExt l)
    {k : ℕ} (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (χ : ↥(GK K) →* (↥LL.1)ˣ)
    (ht : IsTwistRep χ (matRep M) (matRep M')) (hχ : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : IsCrys (P.PD K) (matRep M)) : IsCrys (P.PD K) (matRep M') :=
  (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI T K LL _ _ _ _ χ ht hχ h).1

theorem crys_tw (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  have := D.nd.lPrime i
  have ht : IsTwistRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
    rw [locC_rTwO]
    exact matRep_twistM _ _ g v
  exact twist_mat (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL _ _ _ ht hχ h

end GlobalTheory.CrysFromGTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

variable (D : D7)

def rho {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (z : Bool × HH D) : D.host.E →+* ℂ_[p] :=
  (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D (tauPl D z))

abbrev JJ (n : Bool × HH D → ℕ) (N N' : ℕ) : Type :=
  (Σ z : Bool × HH D, Fin (n z)) × ((Bool × HH D) × Fin N) × ((Bool × HH D) × Fin N')

def rowL {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E)
    (l : (Bool × HH D) × Fin N) : Fin N → D.host.E :=
  fun j => (σ l.1 : D.host.E) * (P (tauPl D l.1))⁻¹ l.2 j

def colR {N' : ℕ} (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ' : Bool × HH D → 𝓞 D.host.E)
    (r : (Bool × HH D) × Fin N') : Fin N' → D.host.E :=
  fun i => (σ' r.1 : D.host.E) * P' (tauPl D r.1) i r.2

def mat {n : Bool × HH D → ℕ} {N N' : ℕ} (a : ∀ z, Fin (n z) → D.host.E)
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N') : Matrix (Fin N') (Fin N) D.host.E :=
  Matrix.of fun i k => a j.1.1 j.1.2 * colR D P' σ' j.2.2 i * rowL D P σ j.2.1 k

def vecF {X : Fields} (s : Seam D X) {N N' : ℕ} (M : Matrix (Fin N') (Fin N) D.host.E) : DVar X.Tau N N' → ℂ :=
  fun k => TaylorLogMetric.embT D (s.iT k.1) (M k.2.1 k.2.2)

def act {X : Fields} (s : Seam D X) (N N' : ℕ) (e : 𝓞 D.host.E) : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ) where
  toFun x := fun k => TaylorLogMetric.embT D (s.iT k.1) (e : D.host.E) * x k
  map_add' x y := by funext k; simp [mul_add]
  map_smul' c x := by funext k; simp; ring

def gc {p : ℕ} [Fact p.Prime] {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p])
    (z : Bool × HH D) (α : Σ z : Bool × HH D, Fin (n z)) : ℂ_[p] :=
  if α.1 = z then cκ z * r α.1 α.2 else 0

def pc {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ} (σ : Bool × HH D → 𝓞 D.host.E) (z : Bool × HH D)
    (l : (Bool × HH D) × Fin N) (a : Fin N) : ℂ_[p] :=
  if l = (z, a) then (rho D ι z (σ z : D.host.E))⁻¹ else 0

def coef {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} {N N' : ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N')
    (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  gc D cκ r x.1 j.1 * pc D ι σ x.1 j.2.1 x.2.1 * pc D ι σ' x.1 j.2.2 x.2.2

def uu {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (a : ∀ z, Fin (n z) → D.host.E) (t : HH D) : ℂ_[p] :=
  ∑ α, ∑ α', gc D cκ r (false, t) α * rho D ι (false, t) (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) *
    gc D cκ r (true, t) α'

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris0_le_sa : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  intro l _ ϖ hϖ a
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  refine GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2
  intro x hx n y hn
  have hx2 : x ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ RingHom.mem_ker.2 hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx2
  obtain ⟨c', hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
  have hc' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') =
      ((l : ℕ) : Per.AinfP l) ^ n := by
    have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
    rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
  have hX : algebraMap (Per.Ainf l) (Per.AinfP l) (c * (((l : ℕ) : Per.Ainf l) - Per.tm ϖ)) =
      -algebraMap (Per.Ainf l) (Per.AinfP l) c * (((l : ℕ) : Per.AinfP l) * beta ϖ) := by
    rw [l_mul_beta, map_mul, map_sub, map_natCast]; ring
  have key : y = algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') *
      (-algebraMap (Per.Ainf l) (Per.AinfP l) c) ^ n * beta ϖ ^ n := by
    apply (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [hn, hX, mul_pow, mul_pow, ← hc']
    ring
  rw [key]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _))
    (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivDual

section Abstract

variable {R : Type} [CommRing R] {n : ℕ}

def Dv (Λ : (Fin n → R) → Prop) (O : R → Prop) (e : R) (u : Fin n → R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, O (z i)) → Λ (e • B.mulVec z)) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • y = e • B.mulVec z) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i)) ∧
    (∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i))

theorem Dv.inv {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u u' : Fin n → R}
    {A A' : Matrix (Fin n) (Fin n) R} (he : e * e = e) (hA : A' * A = 1)
    (hu : ∀ i, u i * u' i.rev = 1) (h : Dv Λ O e u A) : Dv Λ O e u' A' := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have hcancel : ∀ y, A'.mulVec (e • A.mulVec y) = e • y := fun y => by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  let B' : Matrix (Fin n) (Fin n) R := Matrix.of fun a j => (A' * B) a j.rev * u j.rev
  have hB' : ∀ z, B'.mulVec z = A'.mulVec (B.mulVec fun i => u i * z i.rev) := fun z => by
    rw [Matrix.mulVec_mulVec]
    funext a
    simp only [B', Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    ring
  have hB'' : ∀ z : Fin n → R, B'.mulVec (fun i => u' i * z i) = A'.mulVec (B.mulVec fun i => z i.rev) := fun z => by
    rw [hB']
    congr 2
    funext i
    rw [← mul_assoc, hu, one_mul]
  refine ⟨B', fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := h4 (fun i => z i.rev) (fun i => hz _)
    rw [hB', ← Matrix.mulVec_smul, ← hyz, hcancel]
    obtain ⟨w, hw, hyw⟩ := h2 y hy
    rw [hyw]
    exact h1 w hw
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB', ← Matrix.mulVec_smul]
    simp only [Fin.rev_rev]
    rw [← hyz, hcancel]
  · obtain ⟨z, hz, hyz⟩ := h2 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB'', ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hyz]
    simp only [Fin.rev_rev]
  · refine ⟨e • B.mulVec (fun i => z i.rev), h1 _ (fun i => hz _), ?_⟩
    rw [hB'', Matrix.mulVec_smul, smul_smul, he]

theorem Dv.mul {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u : Fin n → R}
    {A a a' b b' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (hbb : b * b' = 1)
    (ha : ∀ y, Λ y ↔ Λ (a.mulVec y)) (hb : ∀ y, Λ y ↔ Λ (b.mulVec y))
    (h : Dv Λ O e u A) : Dv Λ O e u (a * A * b) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have ea : ∀ y, a.mulVec (a'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, haa, Matrix.one_mulVec]
  have eb : ∀ y, b.mulVec (b'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  refine ⟨a * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    exact (ha _).1 (h1 z hz)
  · obtain ⟨z, hz, hyz⟩ := h2 (a'.mulVec y) ((ha _).2 (by rw [ea]; exact hy))
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hyz, Matrix.mulVec_smul, ea]
  · obtain ⟨z, hz, hyz⟩ := h3 (b.mulVec y) ((hb _).1 hy)
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]
  · obtain ⟨y, hy, hyz⟩ := h4 z hz
    refine ⟨b'.mulVec y, (hb _).2 (by rw [eb]; exact hy), ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]

end Abstract

theorem getD_dualLab (d : List ℤ) {n : ℕ} (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.rev.1 0 = -(d.getD i.1 0) := by
  subst hd
  have h1 : i.rev.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.rev.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  have := i.2
  congr 2
  omega

theorem divAt_iff {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V) :
    DivAt V e ϖ d α ↔ d.length = V.rank ∧ Dv (fun y => y ∈ LamHat V) (fun x => x ∈ intAE D) (finPart D e)
      (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0)))) (finMat D.sp.cm.sig V.gram α) := Iff.rfl

theorem divAt_inv_and_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  intro D V e ϖ d α he hϖ h
  rw [divAt_iff] at h
  obtain ⟨hd, h⟩ := h
  have hm : ∀ g g' : GA D V, finMat D.sp.cm.sig V.gram (g * g') =
      finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g' := fun g g' =>
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ g g'
  have h1 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one _ _
  refine ⟨?_, fun a ha b hb => ?_⟩
  · rw [divAt_iff]
    refine ⟨by simpa [dualLab] using hd, h.inv (by rw [← map_mul, he]) ?_ fun i => ?_⟩
    · rw [← hm, inv_mul_cancel, h1]
    · rw [getD_dualLab d hd, ← map_mul, ← map_mul, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ), map_one, map_one]
  · rw [divAt_iff, hm, hm]
    refine ⟨hd, h.mul (a' := finMat D.sp.cm.sig V.gram a⁻¹) (b' := finMat D.sp.cm.sig V.gram b⁻¹) ?_ ?_
      ha.2.1 hb.2.1⟩
    · rw [← hm, mul_inv_cancel, h1]
    · rw [← hm, mul_inv_cancel, h1]

end GlobalTheory.DivDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetReps
section
namespace GlobalTheory.FinsetConjugateRepresentatives

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp [mul_assoc]
    rw [this]
    exact hz
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp [mul_assoc]

theorem exists_finset_reps : ∀ {G : Type} [inst : Group G] {K : Subgroup G},
    Formalism.UG.IsCommensurated K → ∀ (g : G), ∃ (R : Finset G),
      (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K hK g
  classical
  set H : Subgroup K := (K.map (MulAut.conj g).toMonoidHom).subgroupOf K with hH
  have hidx : H.index ≠ 0 := hK g
  haveI : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (q : K ⧸ H) (a : K) (b : G), b ∈ K →
      ((((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b) ∈ K ↔ q = (a : K ⧸ H)) := by
    intro q a b hb
    have e : (((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b)
        = (g⁻¹ * (((q.out)⁻¹ * a : K) : G) * g) * b := by
      simp [mul_assoc]
    rw [e, K.mul_mem_cancel_right hb, ← mem_map_conj, ← Subgroup.mem_subgroupOf, ← hH,
      ← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, by simp⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨((((⟨k₁, hk₁⟩ : K) : K ⧸ H).out : K) : G) * g,
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _ ⟨k₁, hk₁⟩ k₂ hk₂).mpr rfl⟩, ?_⟩
    rintro γ ⟨hγ, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    rw [(key q ⟨k₁, hk₁⟩ k₂ hk₂).mp hx]

end GlobalTheory.FinsetConjugateRepresentatives
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem filtration_eq_span_pow : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  intro l _ Co ϖ hb n
  have he := core_isEps l Co
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l Co.ε he
  obtain ⟨-, -, -, -, hdom, -, hk⟩ := thetaP_facts l
  haveI := hdom
  have hass : Associated (algebraMap (Per.Ainf l) (Per.AinfP l) (xi Co.ε)) (beta ϖ) :=
    Ideal.span_singleton_eq_span_singleton.1 ((hk Co.ε he).symm.trans hb)
  have hD : Associated (aDp l (xi Co.ε) ^ n) (betaD ϖ ^ n) :=
    (hass.map (algebraMap (Per.AinfP l) (Per.BdRp l))).pow_pow
  ext y
  rw [hfil, Ideal.mem_span_singleton]
  exact hD.dvd_iff_dvd_left

end GlobalTheory.Pst.StLat
end

