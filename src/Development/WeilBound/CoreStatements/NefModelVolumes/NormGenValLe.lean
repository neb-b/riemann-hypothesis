module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.WeilBound.CoreStatements.ProjectiveValuations.NonemptyToroidalFlagBundle
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.WeilBound.CoreStatements.NefModelVolumes.NV
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CuspFormExtensionVanishing

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace PositivityTheory.Xj7N

open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem fac_nsmul {K : Type} [Field K] [Algebra c.F K] {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {y : FrPt Xo c K}
    {ρ : K →+* ℂ} (F : InfFr U y ρ) (x : ℝ) {G : WTZ E} (hG : Even G.2) (n : ℕ) :
    F.fac x (n • G) = F.fac x G ^ n := by
  have hev : ∀ m : ℕ, Even (m • G).2 := fun m => by
    rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left _
  induction n with
  | zero =>
    have h0 : Even ((0 : WTZ E).2) := by simp
    have e := F.fac_add x h0 h0
    rw [add_zero] at e
    have hp := F.fac_pos x (0 : WTZ E)
    rw [zero_smul, pow_zero]
    exact mul_left_cancel₀ hp.ne' (by rw [mul_one, ← e])
  | succ n ih =>
    rw [succ_nsmul, F.fac_add x (hev n) hG, ih, pow_succ]

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}

theorem norm_genVal_le {Z : Comp Xo c} {G : WTZ E} {N m : ℕ} {b : Module.Basis (Fin N) c.F (cuspOn U Z G)}
    {g : Matrix (Fin N) (Fin m) c.F} {A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hF : IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A) (ρ : Om Z →+* ℂ) (f : cuspOn U Z G) :
    ‖ρ (genVal Z (f : Rul Xo c))‖ ≤ petOn U x V dict Z G (ρ.comp (algebraMap c.F (Om Z))) f *
      archSize (A (ρ.comp (algebraMap c.F (Om Z)))) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) := by
  have e : ρ (genVal Z (f : Rul Xo c)) = ∑ j, (ρ.comp (algebraMap c.F (Om Z))) (b.repr f j) *
      ρ (genVal Z ((b j : cuspOn U Z G) : Rul Xo c)) := by
    conv_lhs => rw [← b.sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Algebra.smul_def, map_mul, RingHom.comp_apply, AlgHom.commutes]
  rw [e]
  have h := norm_pairing_le (hF.herm (ρ.comp (algebraMap c.F (Om Z))))
    (fun j => (ρ.comp (algebraMap c.F (Om Z))) (b.repr f j)) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c)))
  rwa [hF.norm] at h

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}

theorem norm_small_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hd : ∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2)
    (hspan : ∀ σ, GoodEmb c σ → ∀ P ∈ holSub (U σ).X (modelWt (U σ) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U σ) Z, P w.1 w.2 = Q w.1 w.2)
    {N m : ℕ} {b : Module.Basis (Fin N) c.F (cuspOn U Z G)}
    {g : Matrix (Fin N) (Fin m) c.F} {A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hF : IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A) (σ : c.F →+* ℂ) (ρ : Om Z →+* ℂ)
    (hρ : ρ.comp (algebraMap c.F (Om Z)) = σ) (τ : ℕ) (t : ℝ) (f : cuspOn U Z (τ • G))
    (hf : f ∈ smallL U x V dict Z G τ t) :
    ‖ρ (genVal Z (f : Rul Xo c))‖ ≤ Real.exp (τ * t) *
      archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) ^ τ := by
  subst hρ
  set σ := ρ.comp (algebraMap c.F (Om Z)) with hσdef
  set S := archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn U Z G) : Rul Xo c))) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hgen : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨F⟩ := InfFr.nonempty hU (genFr hgen Z) ρ
  have hgood : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  have hmem : F.pt ∈ framesOn (U (goodOf c σ)) Z := F.mem_framesOn (liesOn_genFr hgen Z)
  have hval : ∀ (G' : WTZ E) (f' : Rul Xo c), f' ∈ secZ Xo c (exZ Dw G') →
      homN (U (goodOf c σ)) x G' f' F.pt = F.fac x G' * ‖ρ (genVal Z f')‖ := fun G' f' h => F.nrm_eq x h
  have hc := F.fac_pos x G
  have hcusp : ∀ f' ∈ cuspOn U Z G, homN (U (goodOf c σ)) x G f' F.pt ^ 2 ≤
      (F.fac x G * S) ^ 2 * petOn U x V dict Z G σ f' ^ 2 := fun f' hf' => by
    rw [hval G f' (cuspW_le_secZ G hf'.1)]
    have h1 := norm_genVal_le hF ρ ⟨f', hf'⟩
    have h2 : F.fac x G * ‖ρ (genVal Z f')‖ ≤ F.fac x G * S * petOn U x V dict Z G σ f' := by
      have := mul_le_mul_of_nonneg_left h1 hc.le
      simp only at this
      linarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) h2 2
  have hB : bergCusp U x V dict Z G σ F.pt ≤ ENNReal.ofReal ((F.fac x G * S) ^ 2) :=
    (bergCusp_le_iff (sq_nonneg _)).2 hcusp
  have hBO : bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G ⟨F.k, F.z⟩ ≤
      ENNReal.ofReal ((F.fac x G * S) ^ 2) := by
    rw [← bergCusp_eq_bergOn (hd _ hgood) (hspan _ hgood) ⟨F.k, F.z⟩ hmem]
    exact hB
  have hsm := hf.2 _ hgood ⟨F.k, F.z⟩ hmem
  have hfs : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G)) := cuspW_le_secZ _ f.2.1
  have e1 : homN (U (goodOf c σ)) x (τ • G) f ⟨F.k, F.z.1⟩ = F.fac x G ^ τ * ‖ρ (genVal Z (f : Rul Xo c))‖ := by
    rw [← fac_nsmul F x hG τ]
    exact hval _ _ hfs
  rw [e1] at hsm
  have h3 := hsm.trans (mul_le_mul_right (pow_le_pow_left' hBO τ) _)
  have hn := norm_nonneg (ρ (genVal Z (f : Rul Xo c)))
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 : (F.fac x G ^ τ * ‖ρ (genVal Z (f : Rul Xo c))‖) ^ 2 ≤
      (F.fac x G ^ τ * (Real.exp (τ * t) * S ^ τ)) ^ 2 := by
    refine h3.trans_eq ?_
    have : Real.exp (2 * τ * t) = Real.exp (τ * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    ring
  have h5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
  exact le_of_mul_le_mul_left h5 (pow_pos hc τ)

end Main

end PositivityTheory.Xj7N
