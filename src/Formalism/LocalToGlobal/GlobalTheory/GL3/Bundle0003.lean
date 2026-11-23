module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageTrivialLevel
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.G0

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.FrobeniusOrbits Classical

variable (D : D7)

theorem rat_mem (t : ℚ) : (t : D.host.E) ∈ D.host.K := by
  rw [← eq_ratCast (algebraMap ℚ D.host.E) t]; exact D.host.K.algebraMap_mem t

theorem conj_b : D.host.conj (D.host.sqd) = -D.host.sqd := by
  apply D.host.φ₀.injective
  rw [CU.emb_conj, map_neg, CS.embedding_sqrt_neg_d, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_mem (k : D.host.K) : D.host.conj (k : D.host.E) ∈ D.host.K := by
  obtain ⟨p, q, e⟩ := CS.K_repr D _ k.2
  rw [e, map_add (f := _), map_mul, map_ratCast, map_ratCast, conj_b]
  exact add_mem (rat_mem D p) (mul_mem (rat_mem D q) (neg_mem (FL.bE_mem D)))

def cK : D.host.K →+* D.host.K where
  toFun k := ⟨D.host.conj (k : D.host.E), conj_mem D k⟩
  map_one' := Subtype.ext (by show D.host.conj ((1 : D.host.K) : D.host.E) = _; simp)
  map_mul' x y := Subtype.ext (by
    show D.host.conj ((x * y : D.host.K) : D.host.E) = D.host.conj x * D.host.conj y
    rw [IntermediateField.coe_mul, map_mul])
  map_zero' := Subtype.ext (by show D.host.conj ((0 : D.host.K) : D.host.E) = _; simp)
  map_add' x y := Subtype.ext (by
    show D.host.conj ((x + y : D.host.K) : D.host.E) = D.host.conj x + D.host.conj y
    rw [IntermediateField.coe_add, map_add (f := _)])

def hK (x y : D.host.E) : D.host.K := Algebra.trace D.host.K D.host.E (x * D.host.conj y)

theorem tau_nonempty : Nonempty D.what₂.Tau := by
  rw [← Fintype.card_pos_iff, FL.card_tau]
  exact Nat.mul_pos (by decide) D.R.ord_pos

theorem herm : FS.Herm4 (cK D) (hK D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [hK, add_mul, map_add (f := _)]
  · intro k x y
    simp only [hK, smul_mul_assoc, map_smul, smul_eq_mul]
  · intro x y
    apply Subtype.ext
    apply D.host.φ₀.injective
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (y * D.host.conj x) : D.host.K) : D.host.E)
      = D.host.φ₀ (D.host.conj ((Algebra.trace D.host.K D.host.E (x * D.host.conj y) : D.host.K) : D.host.E))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [CU.emb_conj, ← FL.sum_tau_trace, ← FL.sum_tau_trace, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_mul, map_mul, CU.emb_conj, CU.emb_conj, Complex.conj_conj, mul_comm]
  · intro x hx
    have hφ : D.host.φ₀ ((hK D x x : D.host.K) : D.host.E)
        = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
      show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
      rw [← FL.sum_tau_trace]
      push_cast
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, CU.emb_conj, Complex.mul_conj]
    have hpos : 0 < ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) := by
      haveI := tau_nonempty D
      exact Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ((map_ne_zero _).2 hx)) Finset.univ_nonempty
    obtain ⟨p, q, e⟩ := CS.K_repr D _ (hK D x x).2
    have hs := IO.sqrt_d_pos D
    rw [e, map_add (f := _), map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
    have him := congrArg Complex.im hφ
    have hre := congrArg Complex.re hφ
    simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
    have hq : (q : ℝ) = 0 := by
      have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hs.ne'
    have hq' : q = 0 := by exact_mod_cast hq
    have hp : (0 : ℝ) < (p : ℝ) := by rw [hq] at hre; linarith
    have hp' : 0 < p := by exact_mod_cast hp
    have hKp : hK D x x = ((p : ℚ) : D.host.K) := by
      apply Subtype.ext
      rw [e, hq']
      show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
      rw [map_ratCast]; simp
    obtain ⟨a, b, c, d, h4⟩ := FS.rat_four_sq p hp'.le
    refine ⟨by rw [hKp]; exact Rat.cast_ne_zero.2 hp'.ne', (a : D.host.K), (b : D.host.K), (c : D.host.K), (d : D.host.K),
      map_ratCast _ a, map_ratCast _ b, map_ratCast _ c, map_ratCast _ d, ?_⟩
    rw [hKp, h4]; push_cast; ring

theorem card_eq : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  letI := FL.algKC D
  rw [← AlgHom.card D.host.K D.host.E ℂ]
  exact Fintype.card_of_bijective (FL.embA_bij D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.G0

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.ThirdClauseIntegralCombination
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Int

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

theorem isPadicIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (h : ∀ i ∈ s, IsIntP (f i)) :
    IsIntP (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold IsIntP; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isPadicIntegral_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isPadicIntegral_mul {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x * y) := by
  unfold IsIntP at *
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem integralMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact isPadicIntegral_sum _ _ fun x _ => isPadicIntegral_mul (hF _) (hG _)

end Int

section Subst

variable {p : ℕ} [Fact p.Prime]

theorem cc_psubst' {ι : Type*} {a : MvPowerSeries ι ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

variable {D : D7} {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def atLogA : D.what₂.Tau × Fin N' × Fin N → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogA_hasSubst : MvPowerSeries.HasSubst (atLogA lam Λ C wq b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [atLogA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLog_eq (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b F = MvPowerSeries.substAlgHom (atLogA_hasSubst lam Λ C wq b) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

end Subst

section Clauses

variable {D : D7} (T : Tor D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

end Clauses

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
end
end

