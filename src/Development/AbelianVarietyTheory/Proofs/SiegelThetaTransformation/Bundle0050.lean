module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSeriesSpanBoundedForms
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem exists_infFam_and_stdChar : ∀ D : D7, (∃ θ : InfFam D, IsInfFam θ) ∧ ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) :=
  fun D => ⟨GlobalTheory.DualPairCompare.exists_infFam D, GlobalTheory.StdAdelicChar.exists_isStdChar D⟩

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitIdempotents_of_relTraceOneModTwo : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∃ s : Finset (Formalism.L2.Theta.AE D), (∀ e ∈ s, IsSplitIdem D e ∧ ∀ e' ∈ s, e ≠ e' → e * e' = 0 ∧ e * cA D e' = 0) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] w - ∑ e ∈ s, e = 2 * a) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) - ∑ e ∈ s, (e + cA D e) = 2 * a) ∧ ∀ e, IsSplitIdem D e → e ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)} ∧ (e ∈ s ∨ cA D e ∈ s ∨ ∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, e = 2 * a) := by
  first | exact @GlobalTheory.IdemModTwo.exists_split_idempotents | exact GlobalTheory.IdemModTwo.exists_split_idempotents | (intros; apply GlobalTheory.IdemModTwo.exists_split_idempotents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsM (D : D7) (T : Core D) (h : LawsM T) : GamAt T := by
  intro j hj σ hσ k γ hst hc
  obtain ⟨hgood, hA, -, -, -, -, hrest⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hrest j hj).2.1
  have hpins := h.pins
  unfold Formalism.L2.Pj.Par.Pins at hpins
  have hlev := hpins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at hlev
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hlev.1
  have h3 : 3 ≤ T.Q.l.M := by
    obtain ⟨p, hlt, hp⟩ := Nat.exists_infinite_primes (T.Q.l.M + 1)
    have h0 : T.Q.l.M.factorization p = 0 := Nat.factorization_eq_zero_of_lt (by omega)
    have := hgood p hp
    simpa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt, h0] using this
  have hU := (Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 (h.unf j hj σ hσ)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ :=
    GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ _ _ _ hU hA hr k γ hst hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hc' : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x =
        ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) • y := by
    rw [← hM]; exact hc
  have hu1 : u = 1 :=
    GlobalTheory.PrincCore.root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
      (h.muUnit j hj σ hσ) (D.host.g 0 * D.host.g 1) (hM ▸ h3) (h.levelK j hj σ hσ) k γ γ' hγ' hc' u n hn hu he
  have hγγ : γ' = γ := by
    ext a b
    have := congrFun (congrFun he a) b
    simpa [hu1] using this
  exact hγγ ▸ hγ'

theorem gamAt_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → GamAt T.toCore := by
  intro D T h
  exact gamAt_of_lawsM D T.toCore h.toLawsM

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D}

theorem EFR_conj (C : Ctx S T) (x y : RW T S) :
    EFR C.X (fun σ k a => conj (x (C.m.e.symm σ) a k) : WR C.X S.rank) (fun σ k a => conj (y (C.m.e.symm σ) a k)) =
      -omO S T x y := by
  simp only [EFR, hermC, omO, LinearMap.mk₂_apply, formAt]
  rw [← C.m.e.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.symm_apply_apply, C.m.e_emb, C.m.ka, C.m.gT, C.m.gS, inv_one,
    ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply, RCLike.conj_conj]
  have hx : (-(2 * D.host.xi0 / 2)) = -D.host.xi0 := by ring
  have hone : ∀ F : Fin S.rank → Fin S.rank → ℂ,
      ∑ a, ∑ b, tauE D τ ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) a b) * F a b = ∑ a, F a a := by
    intro F; simp [Matrix.one_apply]
  rw [hx]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hone, ← Complex.re_sum, ← Finset.mul_sum]
  have hc : conj (tauE D τ (-D.host.xi0)) *
      ∑ k, ∑ a, conj (x τ a k) * ∑ b, conj (tauE D τ (T.gram b a)) * y τ b k =
      conj (-(tauE D τ D.host.xi0 *
        ∑ k, ∑ b, conj (y τ b k) * ∑ a, tauE D τ (T.gram b a) * x τ a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_mul, map_sum, RCLike.conj_conj, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hc, Complex.conj_re, Complex.neg_re]
  ring

theorem pi_lineAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  obtain ⟨-, -, h⟩ := isLineAt_lineAt hθ τ z
  funext τ' i j
  have h1 := congrFun (congrFun (h 1 τ') i) j
  rw [Pi.single_apply]
  split_ifs at h1 ⊢ with hτ
  · rw [Complex.ofReal_one, one_smul] at h1
    exact h1
  · exact h1

theorem single_conj (C : Ctx S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) =
      fun σ k a => conj (piW C.θ T S (lineAt C.θ τ z 1) (C.m.e.symm σ) a k) := by
  rw [pi_lineAt C.inf]
  funext σ k a
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> simp

theorem dRho_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  intro D S T C f hf τ z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  have hθ := C.inf
  have hψ := C.std
  have hD' : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ),
      dRho (heisO C.ψ S T) C.θ τ z g =
        hD (iotaW σ T S) (piW C.θ T S) (omO S T) (piW C.θ T S (lineAt C.θ τ z 1)) g := by
    intro τ z g
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ z)]
  have hsm : ∀ g, C.IsTh g → Sm (iotaW σ T S) g := fun g hg => theta_sm hσ hg
  have hform : ∀ g, C.IsTh g → ∀ (u : RW T S) (w : WO S T),
      hD (iotaW σ T S) (piW C.θ T S) (omO S T) u g w =
        -(Real.pi * Complex.I) * (omO S T (piW C.θ T S w) u : ℝ) * g w +
          fderiv ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 u :=
    fun g hg u w => hD_eq_fderiv _ _ _ g (hsm g hg) u w
  have hdiff : ∀ g, C.IsTh g → ∀ w : WO S T,
      DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun g hg w => ((hsm g hg w).differentiable (by simp)) 0
  refine ⟨theta_dRho hθ hψ τ z hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0
    rw [map_zero, heisO_zero, ← dRho_eq_dLine] at h
    exact h
  · intro f' hf'
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f' hf', hform (f + f') (theta_add hf hf')]
    rw [show (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        (fun x => f (w + iotaW σ T S x)) + (fun x => f' (w + iotaW σ T S x)) from rfl,
      fderiv_add (hdiff f hf w) (hdiff f' hf' w)]
    simp only [Pi.add_apply, _root_.add_apply]
    ring
  · intro a
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform (a • f) (theta_smul a hf)]
    rw [show (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        (fun x => a * f (w + iotaW σ T S x)) from rfl, fderiv_const_mul (hdiff f hf w)]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
    ring
  · intro z'
    have hadd : piW C.θ T S (lineAt C.θ τ (z + z') 1) =
        piW C.θ T S (lineAt C.θ τ z 1) + piW C.θ T S (lineAt C.θ τ z' 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, e, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f hf, hform f hf, hadd, map_add (f := _),
      ContinuousLinearMap.map_add]
    push_cast
    ring
  · intro t
    have hs : piW C.θ T S (lineAt C.θ τ ((t : ℂ) • z) 1) = t • piW C.θ T S (lineAt C.θ τ z 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp [Complex.real_smul]
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform f hf, hs, map_smul, ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · intro u hu
    exact GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f
  · intro τ' z'
    have hskew : ∀ u v : RW T S, omO S T v u = -omO S T u v := by
      intro u v
      have h := omO_self hσ (u + v)
      simp only [map_add (f := _), LinearMap.add_apply, omO_self hσ, zero_add, add_zero] at h
      linarith
    simp only [hD']
    rw [heisenberg_derivative_commutator (WO S T) (RW T S) (iotaW σ T S) (piW C.θ T S) (omO S T)
      (hσ.pi_iota T S) (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) hskew f (hsm f hf),
      single_conj C τ z, single_conj C τ' z', EFR_conj]
    congr 1
    push_cast
    ring

end GlobalTheory.Ker.HeisDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.level_theta_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X D.grp D.lats μ (wtOf X hr c c' n) F → InSpan X hr bas idx M D.lats (D.phi bas hn v₀) (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ c c' F hF

  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hr1 : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r hd
  have h4 : 4 * r < n := by
    generalize Module.finrank ℚ E * r = k at hr1 hn4
    omega

  exact _root_.GlobalTheory.SW.SpanMain.theta_span E r X g q0 hr bas idx n hS hE h4 M D.grp D.lats (D.phi bas hn v₀) μ hM
    (_root_.GlobalTheory.SW.isSystem_level E r X g bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ) c c' F hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C) :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ β : A →+* B, x = spMap β := by
  exact ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem rho_eq_of_ne (hpq : Dw.p ≠ Dw.q) {l₂ : Geo.Tor.Level H} {Xo₂ : Moduli Dw l₂} {π : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t π) {k : Type} [Field k] [IsAlgClosed k] {x : Sp k ⟶ Xo₂.X}
    {β : KA l →+* k} {β₂ : KA l₂ →+* k} (h : (x ≫ π) ≫ Xo.s = spMap β) (h₂ : x ≫ Xo₂.s = spMap β₂) :
    β (baseKA l).ρ = β₂ (baseKA l₂).ρ := by
  have : CharZero k := (RingHom.charZero_iff β.injective).mp inferInstance
  have hsq1 : (β (baseKA l).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β (baseKA l).ρ_sq
    simpa using e
  have hsq2 : (β₂ (baseKA l₂).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β₂ (baseKA l₂).ρ_sq
    simpa using e
  let τE : E →ₐ[ℚ] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ : 𝓞 E →+* k := (τE : E →+* k).comp (algebraMap (𝓞 E) E)
  have ht : (τ H.rt) ^ 2 = -(H.d : k) := by
    have e := congrArg τ H.rt_sq
    simpa using e
  have D1 := (Xo.univ.geom k (x ≫ π) β h).1
  have D2 := (Xo₂.univ.geom k x β₂ h₂).1
  have P : ∀ n, LieMult Xo₂.univ.t.act x τ n ↔ LieMult Xo.univ.t.act (x ≫ π) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo.X Xo₂.X Xo.univ.t.G Xo₂.univ.t.G π m.cm.F Xo.univ.t.act Xo₂.univ.t.act
      m.cart m.act k x τ n
  let b' : Base l₂ k :=
    { unit := fun n hn => (Nat.cast_ne_zero.mpr hn.ne').isUnit
      ρ := β₂ (baseKA l₂).ρ
      ρ_sq := hsq2
      ζ := β₂ (baseKA l₂).ζ
      ζ_prim := (baseKA l₂).ζ_prim.map_of_injective β₂.injective }
  obtain ⟨o', ⟨om⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) k (baseKA l₂) b' β₂ Xo₂.X (Sp k) Xo₂.s (𝟙 (Sp k)) x rfl rfl
    (by rw [Category.id_comp]; exact h₂) Xo₂.univ
  have P' : ∀ n, LieMult o'.t.act (𝟙 (Sp k)) τ n ↔ LieMult Xo₂.univ.t.act (𝟙 (Sp k) ≫ x) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo₂.X (Sp k) Xo₂.univ.t.G o'.t.G x om.cm.F Xo₂.univ.t.act o'.t.act
      om.cart om.act k (𝟙 _) τ n
  have U : ∀ n n', LieMult Xo₂.univ.t.act x τ n → LieMult Xo₂.univ.t.act x τ n' → n = n' := by
    intro n n' hn hn'
    have hn2 := (P' n).mpr (by rw [Category.id_comp]; exact hn)
    have hn2' := (P' n').mpr (by rw [Category.id_comp]; exact hn')
    obtain ⟨bn⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n).mp hn2
    obtain ⟨bn'⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n').mp hn2'
    have e := (Module.finrank_eq_card_basis bn).symm.trans (Module.finrank_eq_card_basis bn')
    simpa using e
  by_contra hne
  have h21 : β₂ (baseKA l₂).ρ = -(β (baseKA l).ρ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq2.trans hsq1.symm) with e | e
    · exact absurd e.symm hne
    · exact e
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (ht.trans hsq1.symm) with e | e
  · have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (P _).mpr ((D1 τ).1 e)
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (D2 τ).2 (by rw [e]; exact hne)
    exact hpq (U _ _ hp hq)
  · have e' : τ H.rt = β₂ (baseKA l₂).ρ := e.trans h21.symm
    have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (D2 τ).1 e'
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (P _).mpr ((D1 τ).2 (by rw [e']; exact fun h' => hne h'.symm))
    exact hpq (U _ _ hp hq)

private theorem ringHom_KA_ext_of_A_eq_one (hA : l.A = 1) {R : Type} [CommRing R] {β β' : KA l →+* R}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  have hz : zeta l.A = 1 := by
    rw [hA]
    simp [zeta, Complex.exp_two_pi_mul_I]
  ext ⟨z, hz'⟩
  change z ∈ IntermediateField.adjoin ℚ {H.rt0, zeta l.A} at hz'
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      rw [e, map_one, map_one]
  | algebraMap q =>
    show β (algebraMap ℚ (KA l) q) = β' (algebraMap ℚ (KA l) q)
    exact DFunLike.congr_fun (RingHom.ext_rat (β.comp (algebraMap ℚ (KA l))) (β'.comp (algebraMap ℚ (KA l)))) q
  | add x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ + ⟨y, hy⟩) = β' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add (f := _), map_add (f := _), ihx, ihy]
  | mul x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ * ⟨y, hy⟩) = β' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]
  | inv x hx ih =>
    show β (⟨x, hx⟩⁻¹) = β' (⟨x, hx⟩⁻¹)
    by_cases h0 : (⟨x, hx⟩ : KA l) = 0
    · rw [h0, _root_.inv_zero, map_zero, map_zero]
    · have e1 : β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      have e2 : β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      calc β (⟨x, hx⟩⁻¹) = β (⟨x, hx⟩⁻¹) * (β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹)) := by rw [e2, mul_one]
        _ = (β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹)) * β' (⟨x, hx⟩⁻¹) := by rw [← ih]; ring
        _ = β' (⟨x, hx⟩⁻¹) := by rw [e1, one_mul]

theorem emb_ext_of_one (hA : l.A = 1) {k : Type} [Field k] {β β' : KA l →+* k}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  exact ringHom_KA_ext_of_A_eq_one hA h

def OverBase (d : DeltaDat Xo c n) : Prop :=
  ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom

theorem point_over_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) (h : KA l ≤ KA d.l₂)
    {K : Type} [Field K] (t : Sp K ⟶ d.Xo₂.X) :
    t ≫ d.r ≫ Xo.s = t ≫ d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom := by
  obtain ⟨γ1, e1⟩ := exists_spMap' (t ≫ d.r ≫ Xo.s)
  obtain ⟨γ2, e2⟩ := exists_spMap' (t ≫ d.Xo₂.s)
  have key : γ1 = γ2.comp (IntermediateField.inclusion h).toRingHom := by
    apply emb_ext_of_one hA
    let ι := algebraMap K (AlgebraicClosure K)
    apply ι.injective
    have e := rho_eq_of_ne hpq d.m (x := spMap ι ≫ t) (β := ι.comp γ1) (β₂ := ι.comp γ2)
      (by simp only [Category.assoc]; rw [e1, spMap_comp']) (by rw [Category.assoc, e2, spMap_comp'])
    exact e
  rw [e1, ← Category.assoc, e2, spMap_comp', key]

theorem overBase_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) : OverBase d := by
  intro h
  have : IsReduced d.Xo₂.X := GlobalTheory.UnivPol.isReduced d.Xo₂
  set f := d.r ≫ Xo.s with hf
  set g := d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom with hg
  have hpt : ∀ p : d.Xo₂.X, d.Xo₂.X.fromSpecResidueField p ≫ f = d.Xo₂.X.fromSpecResidueField p ≫ g :=
    fun p => point_over_of_ne hpq hA d h (K := d.Xo₂.X.residueField p) (d.Xo₂.X.fromSpecResidueField p)
  let φf := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop).hom
  let φg := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop).hom
  have key : ∀ p : d.Xo₂.X, p ∉ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
    intro p hp
    let t := d.Xo₂.X.fromSpecResidueField p
    have e1 : f.appTop ≫ t.appTop = g.appTop ≫ t.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hpt p]
    have e2 : t.appTop (φf (baseKA l).ρ - φg (baseKA l).ρ) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom (baseKA l).ρ)) e1
    have e3 := Scheme.preimage_basicOpen_top t (φf (baseKA l).ρ - φg (baseKA l).ρ)
    rw [e2, Scheme.basicOpen_zero] at e3
    obtain ⟨q⟩ : Nonempty ↥(Spec (d.Xo₂.X.residueField p)) := ⟨IsLocalRing.closedPoint _⟩
    have hq : q ∈ t ⁻¹ᵁ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hp
    rw [e3] at hq
    simp at hq
  have hφ : φf = φg := by
    apply ringHom_KA_ext_of_A_eq_one hA
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro p hp
    exact (key p hp).elim
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop := CommRingCat.hom_ext hφ
  rw [cancel_epi] at h1
  rw [← cancel_mono (Sp (KA l)).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h1]

theorem coe_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (t : S) :
    (((IntermediateField.inclusion h).toRingHom t : T) : ℂ) = (t : ℂ) := rfl

theorem eq_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (j : S →+* T) (hj : ∀ t, ((j t : T) : ℂ) = (t : ℂ)) :
    j = (IntermediateField.inclusion h).toRingHom := by
  exact RingHom.ext fun t => Subtype.ext ((hj t).trans (coe_incl h t).symm)

section Reads

variable {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : UW U) (k : U.Comp) {a : (E →+* ℂ) × ℕ → ℕ}

variable {U W k}

end Reads

end

end GlobalTheory.ClsVal.Cmp
end

