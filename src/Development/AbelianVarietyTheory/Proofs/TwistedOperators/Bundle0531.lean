module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

theorem tame_kills_real_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ →
    ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) →
    ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  intro D ψ θ hψ hθ S T A B ℓ hℓ f hf hP w hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hcont, hsurj, htr⟩ := _root_.GlobalTheory.FockTransport.fockPt_transport D θ σ hσ S T A B
  obtain ⟨z₀, rfl⟩ := hsurj w hw
  have hth := hf.1
  set F : VCx D.what₂.Tau S.rank T.rank → ℂ := fun z => ℓ (heisO ψ S T (fockPt σ A B z) f) with hFdef
  have hFc : Continuous F := (hℓ.cont f hth).comp hcont
  obtain ⟨M, hM⟩ := hℓ.bdd f hth
  have hFb : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M := ⟨M, fun z => hM _⟩
  have key : ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g →
      IsThetaFunO ψ S T (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) →
      ℓ (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = ∫ z, g z * F z := by
    intro g hg hthg
    obtain ⟨m, α, hm, hα, hH⟩ := htr g hg
    have e1 : (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = fun x => ∫ w, α w * heisO ψ S T w f x ∂m := by
      funext x; exact (hH fun w => heisO ψ S T w f x).symm
    rw [e1] at hthg ⊢
    rw [hℓ.sup f hth m α hα hthg]
    exact hH fun w => ℓ (heisO ψ S T w f)
  obtain ⟨C, hC⟩ := ((GlobalTheory.ThetaSquare.squareIntegrable hψ) f hth).2.1
  have hG : ∀ x, ∃ M : ℝ, ∀ z, ‖rd ψ σ A B f x z‖ ≤ M * Real.exp (gq (fw D) z / 2) := by
    intro x
    refine ⟨C, fun z => ?_⟩
    rw [rd, norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have hent := _root_.GlobalTheory.FockEntire.rd_differentiable D ψ θ σ hψ hσ S T A B f hf
  have hc : ∀ τ, 0 < fw D τ := fw_pos D
  obtain ⟨hint1, hint2⟩ := _root_.GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss D.what₂.Tau S.rank T.rank (fw D) hc
  have hgq : ∀ z : VCx D.what₂.Tau S.rank T.rank, ∀ x, (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z =
      (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x := by
    intro z x
    rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring

  obtain ⟨Cj, hCj⟩ := _root_.GlobalTheory.FockTransl.Jet.jet_eq_fock D ψ θ σ hψ hσ S T A B
  have hpt : ∀ P, IsThetaFunO ψ S T (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    fun P => GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hth P
  have hmom : ∀ m : DVar D.what₂.Tau S.rank T.rank →₀ ℕ,
      ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * F z = 0 := by
    intro m
    set K : ℂ := ((∏ τ, (Real.pi / fw D τ) ^ (S.rank * T.rank) : ℝ) : ℂ) *
      ((m.prod fun k n => (fw D k.1)⁻¹ ^ n : ℝ) : ℂ) with hK
    have e : (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
        (K * Cj m) • GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) := by
      funext x
      have h1 := _root_.GlobalTheory.FockMoment.gaussMoment D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) m
      rw [hCj f hf x m] at h1
      have h2 : (fun z => conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
          fun z => conjMono m z * (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z := by
        funext z; rw [mul_assoc, mul_assoc, hgq]
      rw [h2, h1, Pi.smul_apply, smul_eq_mul]
      ring
    have hthe : IsThetaFunO ψ S T (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) *
        heisO ψ S T (fockPt σ A B z) f x) := by
      rw [e]
      exact GlobalTheory.OrientedHeis.theta_smul _ (hpt _)
    have := key _ (hint1 m) hthe
    rw [← this, e, hℓ.smul _ _ (hpt _), hP, mul_zero]

  have hU := _root_.GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments D.what₂.Tau S.rank T.rank (fw D) hc F hFc hFb hmom z₀
  set K' : ℂ := ((∏ τ, (fw D τ / Real.pi) ^ (S.rank * T.rank) : ℝ) : ℂ) * (Real.exp (-gq (fw D) z₀ / 2) : ℂ) with hK'
  have e : (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) = heisO ψ S T (fockPt σ A B z₀) f := by
    funext x
    have h1 := _root_.GlobalTheory.FockRepr.bargmann_repr D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) z₀
    have h2 : heisO ψ S T (fockPt σ A B z₀) f x = (Real.exp (-gq (fw D) z₀ / 2) : ℂ) * rd ψ σ A B f x z₀ := by
      rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [show -gq (fw D) z₀ / 2 + gq (fw D) z₀ / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [h2, h1]
    have h3 : (fun z => (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
        heisO ψ S T (fockPt σ A B z) f x) = fun z => K' * (Complex.exp (bk (fw D) z₀ z) *
          ((Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z)) := by
      funext z; rw [hgq]; ring
    rw [h3, integral_const_mul, hK']
    simp only [mul_assoc]
    ring
  have hthe : IsThetaFunO ψ S T (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) := by
    rw [e]; exact (GlobalTheory.ThetaSquare.heisUnitary hψ).2.2.1 _ _ hth
  have := key _ ((hint2 z₀).const_mul K') hthe
  rw [e] at this
  change ℓ (heisO ψ S T (fockPt σ A B z₀) f) = 0
  rw [this]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc] at hU ⊢
  rw [hU, mul_zero]

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.SplitSymp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA' {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

end GlobalTheory.FlipMatch.SplitSymp

namespace GlobalTheory.FlipMatch.SplitSymp

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    pairM P Q = pairM Q P := by
  simp only [pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | (apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.SumFourSwap.sum_four_swap
  | exact _root_.GlobalTheory.SumFourSwap.sum_four_swap
  | (apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumFourSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumFourSwap.sum_four_swap ..)

theorem symp_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hX hY ψ v t b c x u hx hu
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) *
      GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz]
  change psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  rw [pairM_comm (coY σ X Y t b c x), coX, coX, coY, coY, pairM_chart, pairM_chart]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA', piW_incl,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.FlipMatch.SplitSymp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThGEquiv
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaGoodEquiv

theorem thG_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ y, R.thG i t (S y) = R.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP hgr _ i t g0 κ κ' hκ hκ' S hS y
  have hinj := (hM.HW i (sg0 D A)).1
  apply hinj
  have hX := hP.thF_mem i t y
  have hsh := GlobalTheory.ThetaShiftSmooth.thF_shift_all R hL hM hP i t g0 κ κ' hκ hκ' y (S y) (hS y)
  have hcomm := (GlobalTheory.ProjComm.proj_comm R hL hgr).2
  have e1 := hP.thG i t (S y)
  have e2 := hM.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y)
  have e3 := hP.thG i t y
  have hκ'' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) κ' := by
    rw [MulEquiv.apply_symm_apply]; exact hκ'
  have hT : ∀ v, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := fun v k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i (sg0 D A)) _ _ (R.thF i t y) hX v).2.2 k hk h
  have h2 := GlobalTheory.ThetaShiftSmooth.levChi_flag_eq_one R i κ'
  have hUe : ∀ v, R.thF i t (S y) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) (R.thF i t y v) := fun v => by
    funext z
    have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (hT v) ⟨κ', hκ''⟩ κ' hκ'' z
    have h3 := congrArg (fun c : ℂ => c⁻¹ * R.thF i t y v (z * κ')) h2
    have h4 : (1 : ℂ)⁻¹ * R.thF i t y v (z * κ') = R.thF i t y v (z * κ') := by simp
    exact (hsh v z).trans (h1.trans (h3.trans h4)).symm
  have key : postOn _ (R.eWf i (sg0 D A)) (R.thF i t (S y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)))
        (postOn _ (R.eWf i (sg0 D A)) (R.thF i t y)) := by
    refine MultilinearMap.ext fun v => ?_
    exact (congrArg (R.eWf i (sg0 D A)) (hUe v)).trans (hcomm i (sg0 D A) (R.eG.symm g0) (R.thF i t y v) (hT v))
  exact e1.trans (key.trans ((congrArg _ e3).symm.trans e2.symm))

end GlobalTheory.ThetaGoodEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.SiegelTorusTheta

theorem torus_bound : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  intro D ψ θ hθ ε M X χ χ' ω hω r Xf Yf hW c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨S₀, d, hA1⟩ := _root_.GlobalTheory.WittLevi.witt_levi θ hθ ε M r Xf Yf hW
  obtain ⟨μ', 𝓕', hcov, hA2⟩ := _root_.GlobalTheory.LeviThetaSum.levi_sum ψ (sgn ε M) S₀ X r d χ χ' (ω.toSgn ε) hω
  obtain ⟨k, A, C, hC, hB⟩ := GlobalTheory.T.torus_mixedCoordinate_sum_le_sobolev_seminorm ψ (IsWeilDatumO.std hω) θ hθ (sgn ε M) X S₀ r d μ' 𝓕' hcov c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  refine ⟨k, A, C, hC, fun n hn Ψ hΨ hlev t ht a ha => ?_⟩
  obtain ⟨α, hα1, hα2, hlevi⟩ := hA1 t ht.1 a ha
  have e : ω (a, 1) Ψ 0 = ω.toSgn ε (d.levi α, 1) Ψ 0 := by
    rw [← hlevi]
    show ω (a, 1) Ψ 0 = ω ((ofSgn ε M) ((ofSgn ε M).symm a), 1) Ψ 0
    rw [MulEquiv.apply_symm_apply]
  have hle := hA2 Ψ hΨ α
  rw [← e, _root_.GlobalTheory.HalfModTorus.halfMod_torus θ hθ r X.rank t ht.1 α hα1 hα2] at hle
  have h2 := hB n hn Ψ hΨ hlev t ht α.1 hα1 hα2
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have hQ : 0 ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal :=
    mul_nonneg (mul_nonneg hC (pow_nonneg n.cast_nonneg _)) ENNReal.toReal_nonneg
  have h3 : ‖ω (a, 1) Ψ 0‖ₑ ≤ ENNReal.ofReal (C * (n : ℝ) ^ A *
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) := by
    refine hle.trans ((mul_le_mul' le_rfl h2).trans_eq ?_)
    rw [← ENNReal.ofReal_mul hP, mul_comm]
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hQ hP)).1 h3

end GlobalTheory.SiegelTorusTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateLiftLinearIsometry
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem translate_lift_linear_isometry : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∃ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y, ‖S y‖ = ‖y‖) ∧ ∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hMod i t g0 κ hκ
  have hex := fun y => GlobalTheory.translate_unitary_lifts R hlev hMod.HV hMod.cV i t g0 κ hκ y
  choose S hS hSn using hex
  have hinj : Function.Injective (R.HV i t).e := (hMod.HV i t).1
  refine ⟨{ toFun := S, map_add' := ?_, map_smul' := ?_ }, hSn, ?_⟩
  · intro y z
    apply hinj
    funext h
    simp only [map_add (f := _), Pi.add_apply, hS, smul_add]
  · intro a y
    apply hinj
    funext h
    simp only [map_smul, Pi.smul_apply, hS, RingHom.id_apply]
    exact smul_comm _ _ _
  · intro y h
    have hk : (R.cV i).ρ κ⁻¹ = 1 := (hMod.cV i).1 _ (inv_mem hκ.1)
    have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) =
        (finHom (Vc D i)).rangeRestrict h * (finHom (Vc D i)).rangeRestrict κ := map_mul _ _ _
    show (R.cV i).ρ h⁻¹ ((R.HV i t).e (S y) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)))
    have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
      rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
    refine (congrArg ((R.cV i).ρ h⁻¹) (hS y _)).trans ?_
    refine (LinearMap.map_smul _ _ _).trans (congrArg (fun w => (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) ?_)
    exact congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e y) hrr.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacMoveHigh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_move_high : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      ∃ c : ℂ, W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c • Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hinf : infPart D (e + cA D e) = 0 := by
    rw [RingHom.map_add (f := _), ho.infPart_eq, infPart_cA ho.infPart_eq, add_zero]
  have hgfin : g ∈ GfC (G.V (.top (j + 1))) := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hg1fin : cutPart (e + cA D e) _ g ∈ GfC (G.V (.top (j + 1))) :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF _ hinf (suppAt_cutPart hee hce _ g)
  have hg2fin : cutPart (1 - (e + cA D e)) _ g ∈ GfC (G.V (.top (j + 1))) := by
    have e1 : cutPart (1 - (e + cA D e)) _ g = (cutPart (e + cA D e) _ g)⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← cutPart_mul hf]
    rw [e1]
    exact mul_mem (inv_mem hg1fin) hgfin
  have hΛ : ∀ u, u ∈ stdLatO S (.top t (j + 1)) ↔
      ∃ u₀ ∈ stdLatO S (.top t (j + 1)), u = actO _ _ (cutPart (1 - (e + cA D e)) _ g) 1 u₀ :=
    _root_.GlobalTheory.OffPartLattice.offPart_keeps_stdLatO S ht j hj k hk e he
  have hV := G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hV' := G.isV (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ (cutPart (1 - (e + cA D e)) _ g) 1
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg2fin τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ (one_mem _) τ, Matrix.mul_one, Matrix.one_mul]) hΛ _ hvac
  obtain ⟨c₂, -, hc₂⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ hV.sigOK hV'.sigOK
    (W.cart_is _ (show j + 1 ≤ D.R.m by omega)) (W.cart_is _ (show j + 1 + 1 ≤ D.R.m by omega)) _ _ hS hT _ _ hvac hv'
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  refine ⟨c₂ * ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)), ?_⟩
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = c₂ • W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hc₂, map_smul]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        conv_rhs => rw [mul_smul, ← map_smul]
        congr 2
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

end GlobalTheory.ExpansionInvariance

end
end

