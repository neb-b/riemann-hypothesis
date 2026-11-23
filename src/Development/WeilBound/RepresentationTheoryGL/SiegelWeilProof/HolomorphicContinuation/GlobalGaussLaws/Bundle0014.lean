module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag
section
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

variable {m n : ℕ}

def sigR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sigR ε a : ℝ) : ℂ) := by
  unfold sgn sigR
  by_cases h : ε a <;> simp [h]

theorem ftLoc_eq (ε : Fin m → Bool) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s f u = ftG (sigR ε) s f u := by
  simp only [ftLoc, ftG]
  congr 1
  funext y
  have key : ((of u)ᴴ * diagonal (sgn ε) * of y).trace.re =
      ∑ a, ∑ j, sigR ε a * ((starRingEnd ℂ) (u a j) * y a j).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sgn_eq, mul_comm (star (u a j)) _, mul_assoc, Complex.re_ofReal_mul]
    rfl
  rw [key]

theorem gramX_diag (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramX ε u j j = ∑ a, ((sigR ε a : ℝ) : ℂ) * ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, if_true,
    Bool.false_eq_true, if_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a <;> simp [h, sigR, Complex.conj_mul']

theorem chN_DG (ε : Fin m → Bool) (t : ℝ) (β : Fin n → ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (u : Fin m → Fin n → ℂ) :
    chN ε t (diagonal fun j => (β j : ℂ)) u * DG K γ u =
      DG K (fun a j => γ a j - I * t * (sigR ε a : ℂ) * (β j : ℂ)) u := by
  simp only [chN, DG]
  simp only [← Complex.exp_sum]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have htr : (diagonal (fun j => (β j : ℂ)) * gramX ε u).trace = ∑ j, (β j : ℂ) * gramX ε u j j := by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr]
  simp_rw [gramX_diag, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dg_const (K γ0 : ℂ) (v : Fin m → Fin n → ℂ) :
    DG K (fun _ _ => γ0) v = K * cexp (-γ0 * ∑ a, ∑ j, ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [DG]
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]

theorem vac_eq (ε : Fin m → Bool) (t c : ℝ) : vac (n := n) ε t c = DG 1 (fun _ _ => (c : ℂ)) := by
  funext y
  rw [dg_const, one_mul]
  simp only [vac, gZf]
  congr 1
  have hsum : (gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace =
      ∑ a, ∑ j, ((‖y a j‖ ^ 2 : ℝ) : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, gramB, Qb, evX, map_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : epsT t ε a <;> simp [h, Complex.conj_mul']
  rw [smul_mul_assoc, one_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination ((c : ℂ) * ((gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace)) *
    Complex.I_sq + (-(c : ℂ)) * hsum

theorem levF_diag (e : ℤ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) (K : ℂ) (γ : Fin m → Fin n → ℂ) :
    levF e (diagonal fun j => (δ j : ℂ)) (DG K γ) =
      DG (K * (∏ j, (δ j : ℂ)) ^ m) (fun a j => γ a j * ((δ j : ℂ) ^ 2)) := by
  funext u
  simp only [levF, DG, Matrix.det_diagonal]
  have hD : (∏ j, (δ j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (hδ j).ne'
  have hs : star (∏ j, (δ j : ℂ)) = ∏ j, (δ j : ℂ) := by
    rw [← Complex.ofReal_prod]
    exact Complex.conj_ofReal _
  rw [hs, ← zpow_add₀ hD, add_sub_cancel, zpow_natCast]
  rw [← mul_assoc, mul_comm (_ ^ m) K]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_diagonal, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.VacC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_realPar_ne (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l ∧ ∀ τ, l τ ≠ 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  have hy0 : y ≠ 0 := by
    rw [hy_def]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 ha0
  refine ⟨fun τ => -(tauE D τ y).re, ?_, fun τ => ?_⟩
  · intro x
    have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
      simp only [psiInf]
      rw [ha]
      congr 1
      show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
      rw [mul_zero]; rfl
    rw [e1, h₀.2.2 θ hθ]
    congr 1
    have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
      intro ρ
      have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
          ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
      rw [e3, map_mul, (hθ ρ).1]
    simp only [e2]
    have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
      intro ρ
      apply Complex.ext <;> simp [hreal ρ]
    simp only [e4, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  · intro h
    have h1 : tauE D τ y ≠ 0 := (map_ne_zero_iff _ (tauE D τ).injective).2 hy0
    apply h1
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp [hreal τ]

theorem cx_lne {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → NNReal}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)} {τ : D.what₂.Tau}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : PositivityTheory.Rg.Sw.GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) : ∀ τ', l τ' ≠ 0 := by
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

open LocLawH in
theorem lIl : LIl := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne τ

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob


set_option synthInstance.maxHeartbeats 400000 in
theorem realPar_explicit (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ a : D.host.F, a ≠ 0 ∧
      HasRealPar ψ θ (fun τ => -(tauE D τ (algebraMap D.host.F D.host.E a)).re) ∧
      ∀ τ, (tauE D τ (algebraMap D.host.F D.host.E a)).im = 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨a, ha0, ?_, hreal⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e5 : ∀ ρ, (((tauE D ρ (algebraMap D.host.F D.host.E a)).re : ℝ) : ℂ) = tauE D ρ y := by
    intro ρ
    have h := hreal ρ
    rw [hy_def] at h ⊢
    apply Complex.ext
    · simp
    · simp [h]
  simp only [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [e5 ρ]
  ring

theorem lNZ : LNZ := by
  intro D ψ θ l hψ hθ hl τ
  obtain ⟨a, ha0, hl0, hre⟩ := realPar_explicit D ψ hψ θ hθ
  have e : l = _ := GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl0
  rw [e]
  intro h0
  apply ha0
  have h1 : tauE D τ (algebraMap D.host.F D.host.E a) = 0 := by
    apply Complex.ext
    · simpa using h0
    · simpa using hre τ
  have h2 : algebraMap D.host.F D.host.E a = 0 := (map_eq_zero _).1 h1
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h2

end PositivityTheory.Rg.Sw.Glob
end
end

