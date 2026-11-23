module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical IntermediateField

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_b : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = conj (φ x) :=
  H.conjE_apply φ x

theorem d_pos : 0 < H.d := H.hyp.2.1.pos

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_b : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  rw [phi_conj, map_neg, phi_b]
  simp

theorem b_mem_K : H.sqd ∈ H.K := mem_adjoin_simple_self ℚ _

def bK : H.K := ⟨H.sqd, b_mem_K H⟩

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  SplitK.finrank_K (L := H.E) (b := H.sqd) (d := H.d) (d_pos H) (bE_sq H)

theorem K_induction {p : H.E → Prop} (hb : p (H.sqd)) (hq : ∀ r : ℚ, p (algebraMap ℚ H.E r))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hinv : ∀ x, p x → p x⁻¹) (hmul : ∀ x y, p x → p y → p (x * y))
    (k : H.K) : p (k : H.E) := by
  have hk : (k : H.E) ∈ ℚ⟮H.sqd⟯ := k.2
  refine IntermediateField.adjoin_induction ℚ (motive := fun x _ => p x) ?_ hq (fun x y _ _ => hadd x y) (fun x _ => hinv x)
    (fun x y _ _ => hmul x y) hk
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact hb

theorem conj_mem_K (k : H.K) : H.conj (k : H.E) ∈ H.K := by
  refine K_induction H (p := fun x => H.conj x ∈ H.K) ?_ ?_ ?_ ?_ ?_ k
  · rw [conj_b]; exact neg_mem (b_mem_K H)
  · intro r; rw [AlgEquiv.commutes]; exact H.K.algebraMap_mem r
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_inv₀]; exact inv_mem hx
  · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy

theorem fix_K (σ : H.E ≃ₐ[ℚ] H.E) (hσ : σ (H.sqd) = H.sqd) (k : H.K) : σ (k : H.E) = k := by
  refine K_induction H (p := fun x => σ x = x) hσ ?_ ?_ ?_ ?_ k
  · intro r; rw [AlgEquiv.commutes]
  · intro x y hx hy; rw [map_add (f := _), hx, hy]
  · intro x hx; rw [map_inv₀, hx]
  · intro x y hx hy; rw [map_mul, hx, hy]

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem tr_pos (x : H.E) (hx : x ≠ 0) : 0 < Algebra.trace ℚ H.E (x * H.conj x) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := H.E) ℂ (x := x * H.conj x)
  have h2 : ∀ σ : H.E →ₐ[ℚ] ℂ, σ (x * H.conj x) = ((Complex.normSq (σ x) : ℝ) : ℂ) := by
    intro σ
    have h3 := phi_conj H (σ : H.E →+* ℂ) x
    rw [map_mul]
    have h4 : σ (H.conj x) = conj (σ x) := h3
    rw [h4, Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ), ← Complex.ofReal_sum] at h
  have h5 : ((Algebra.trace ℚ H.E (x * H.conj x) : ℚ) : ℝ) = ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    apply Complex.ofReal_injective
    rw [← h]
    simp
  have h6 : 0 < ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    have : Nonempty (H.E →ₐ[ℚ] ℂ) := ⟨(H.φ₀ : H.E →+* ℂ).toRatAlgHom⟩
    apply Finset.sum_pos
    · intro σ _
      exact Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)
    · exact Finset.univ_nonempty
  rw [← h5] at h6
  exact_mod_cast h6

theorem finrank_E_K : Module.finrank H.K H.E = 2 * R.ord := by
  have h1 := Module.finrank_mul_finrank ℚ H.K H.E
  rw [finrank_K H, H.finrank_cmField] at h1
  omega

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  H.gal.apply_symm_apply _

theorem emb_on_K (g : R.GG) (hg : g ∈ R.Psi) (k : H.K) : H.emb g (k : H.E) = H.φ₀ (k : H.E) := by
  have h1 : H.sigmaOf g (H.sqd) = H.sqd := by
    rw [← H.galE_mem_Psi_iff, galE_sigmaOf]; exact hg
  show H.φ₀ (H.sigmaOf g (k : H.E)) = _
  rw [fix_K H _ h1]

theorem d_mod_eight_eq_seven : H.d % 8 = 7 := by
  have := H.hyp.2.2.2.1
  omega

theorem bK_mul : bK H * bK H = -(H.d : H.K) := by
  apply Subtype.ext
  have h := bE_sq H
  rw [sq] at h
  simpa [bK] using h

theorem sqrt_in_K : ∃ s : H.K, s * s = -(H.d : H.K) ∧
    H.conj (algebraMap H.K H.E s) = -algebraMap H.K H.E s :=
  ⟨bK H, bK_mul H, conj_b H⟩

theorem theta_integral : IsIntegral ℤ ((1 + bK H) / 2 : H.K) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := d_mod_eight_eq_seven H; omega⟩
  refine ⟨Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (m : ℤ)), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (b := ((1 : ℕ) : WithBot ℕ)) ?_ (by norm_num)
    compute_degree
    exact le_rfl
  · have hb := bK_mul H
    have hm' : (H.d : H.K) + 1 = 4 * (m : H.K) := by exact_mod_cast congrArg (Nat.cast : ℕ → H.K) hm
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_neg, Polynomial.eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    field_simp
    linear_combination hb - hm'

def thetaK : 𝓞 H.K := ⟨(1 + bK H) / 2, theta_integral H⟩

theorem phi_thetaK : H.φ₀ (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
  have h : (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + H.sqd) / 2 := by
    simp [thetaK, bK]
    rfl
  rw [h, map_div₀, map_add (f := _), map_one, phi_b, map_ofNat]

end Host

section Facts

variable (D : D7)

theorem kQuad : KQuad D := finrank_K D.host

theorem cardTau : CardTau D := by
  unfold CardTau
  rw [D.what₂.card_Tau, finrank_E_K D.host]
  rfl

theorem embInj : EmbInj D := fun _ _ h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embOnK : EmbOnK D := fun τ k => emb_on_K D.host _ (D.eTau τ).2 k

theorem dMod8 : DMod8 D := d_mod_eight_eq_seven D.host
theorem sqrtInK : SqrtInK D := sqrt_in_K D.host

theorem latStable : LatStable D := by
  intro cc δ w hw
  refine AddSubgroup.closure_induction (p := fun w _ => thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨c, hc, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨thetaK D.host * c, cc.mul_mem_left _ hc, ?_⟩
    have h : (((thetaK D.host * c : 𝓞 D.host.K) : D.host.K) : D.host.E)
        = (((thetaK D.host : 𝓞 D.host.K) : D.host.K) : D.host.E) * (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      push_cast; rfl
    rw [h, map_mul, phi_thetaK]
    unfold thetaC
    ring
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro x _ hx; rw [mul_neg]; exact neg_mem hx

end Facts

section Exist

variable {D : D7}

theorem splitKSplits_of (hd : DMod8 D) (hs : SqrtInK D) : SplitKSplits D := by
  obtain ⟨s, h1, h2⟩ := hs
  exact fun p hp hsp => kernel_split_of_jacobi D.host.K D.host.E D.host.conj D.host.d p s hd h1 h2 hp hsp

end Exist

section Final

variable (D : D7)

theorem splitKSplits : SplitKSplits D := splitKSplits_of (dMod8 D) (sqrtInK D)

theorem yIndep (γ₀ : IsoK D) : YIndep γ₀ :=
  fun p 𝔭 γ γ' hp _ hm h1 h2 =>
    ordRelativeDet_independence D.host.K D.host.E D.what₂.Tau {x | x ∈ D.host.AA0} p 𝔭 γ.g γ'.g γ₀.g hp hm h1 h2

theorem distinguished_ideal_ne_zero : D.host.AA0 ≠ 0 := by
  have hd : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [D.host.𝔟_spec.1, h0]
    exact Ideal.bot_mul _
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb)

theorem yFinite (γ₀ : IsoK D) (k : KapChoice γ₀) : k.YFinite :=
  ordRelativeDet_finite D.host.K D.host.E D.what₂.Tau D.host.AA0 (distinguished_ideal_ne_zero D) (SplitK D) k.pp (fun p => (k.gaP p).g) γ₀.g
    k.pp_over k.gaP_at

theorem Base.half_not_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.ω₀ / 2 ∉ B.L.lattice := by
  intro h
  have h1 : B.ω₀ / 2 ∈ TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; exact h
  exact B.t0.2.1 (latStable D cc δ _ h1)

end Final

namespace Test

open Formalism.BasicNotions.Examples₂

end Test

end Formalism.L2.Ker
