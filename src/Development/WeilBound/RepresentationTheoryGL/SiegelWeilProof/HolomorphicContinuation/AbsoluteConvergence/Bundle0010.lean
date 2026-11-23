module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GlobCore
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

structure GlobCore (ε : Fin m → Bool) (c : ℝ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n)
    (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop where
  ιcont : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ ∀ P, sec P (x * ι y') = S * sL P y'
  Icont : Continuous (I 1)
  Ileft : ∀ γ ∈ Γ, ∀ g, I 1 (γ * g) = I 1 g
  Ik : ∀ P g (k : GR n), InK (mR k) → I P (g * ι k) = I (ρ k P) g
  Iinv : ∀ g a b P, I (hOp ε c a b P) g = 0
  Idil : ∀ (g : G) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (F : GR n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (F y) U ∧
      (∀ t : ℝ, F y t = I 1 (g * ι (y * a t))) ∧ ∀ r : ℕ, iteratedDeriv r (F y) 0 = I ((dil c X ^ r) 1) (g * ι y)
  eis : ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ GlobalTheory.Cont.IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ) ∧
    (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
    ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * (star (x a i) * x a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, eval_X, Finset.sum_filter, if_true]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h]

theorem gramX_scal (ε : Fin m → Bool) (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    gramX ε (scal α x) = diagonal (fun j => (α j : ℂ)) * gramX ε x * diagonal (fun j => (α j : ℂ)) := by
  ext i j
  simp only [gramX_apply, mul_diagonal, diagonal_mul, scal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h, mul_comm]

theorem trace_im (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    ((b * gramX ε x).trace).im = 0 := by
  have hG := gramX_herm ε x
  have h1 : star ((b * gramX ε x).trace) = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hG, hb.eq, trace_mul_comm]
  have h2 := congrArg Complex.im h1
  simp only [Complex.star_def, Complex.conj_im] at h2
  linarith

theorem norm_phase (t : ℝ) (z : ℂ) (hz : z.im = 0) : ‖Complex.exp (Complex.I * t * z)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, hz]

theorem trace_scal (ε : Fin m → Bool) (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    (bS X h b * gramX ε (scal (aH X h) y)).trace = (b * gramX ε y).trace := by
  rw [gramX_scal]
  simp only [bS]
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (-(h * X j)) : ℝ) : ℂ)
  set B : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((aH X h j : ℝ) : ℂ)
  have hAB : A * B = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hBA : B * A = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [show A * b * A * (B * gramX ε y * B) = A * (b * ((A * B) * gramX ε y * B)) by
    simp only [mul_assoc], hAB, one_mul, trace_mul_comm,
    show b * (gramX ε y * B) * A = b * gramX ε y * (B * A) by simp only [mul_assoc], hBA, mul_one]

theorem ept_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, true) = star (v a j) := rfl
theorem ept_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, false) = v a j := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X Q) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q v +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX Q v := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have key : ∀ a b c d a' b' c' d' : ℂ, a = a' → b = c' → c = b' → d = d' →
      a + (b + c - d) = a' + (b' + c') - d' := by
    intros
    subst_vars
    ring
  show eval (ept v) (dil c X Q) = ((m : ℂ) * ∑ j, (X j : ℂ)) * eval (ept v) Q +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * eval (ept v) Q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul, nsmul_eq_mul, map_sum, map_add, map_sub,
    map_mul, eval_X, eval_C, map_natCast, ept_true, ept_false, Derivation.coeFn_coe, hn]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ept_true, ept_false]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))), Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  apply key
  · exact Finset.sum_congr rfl (fun _ _ => by ring)
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GroupPart
section
namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

theorem groupPart : GroupPart := by
  intro n X a ha
  exact ⟨dil_mul ha, dil_zero ha, dil_up ha, cont_dil ha, fun y hy s => up_mul hy (dil_up ha s), cell_dec,
    fun g b hg h => conj_cell ha g b hg h, fun y hy s => cell_mul ha y hy s, dense_cell,
    fun p q e h => weight_factor_dilation ha p q e h⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ImportsAlt
section
noncomputable section

open MeasureTheory Set Filter Topology GlobalTheory.Cont

namespace PositivityTheory.Rg.Sw.AbsSt

private theorem ev_ne_lemma {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ha : ∃ a, f a ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨a, ha⟩ := ha
    have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
    exact ha (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h (mem_univ a))
  · exact h

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamLocal
section
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

def invSub (Γ : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g}
  add_mem' := fun {F F'} hF hF' => ⟨hF.1.add hF'.1, fun γ hγ g => by simp [hF.2 γ hγ g, hF'.2 γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := fun a F hF => ⟨hF.1.const_smul a, fun γ hγ g => by simp [hF.2 γ hγ g]⟩

theorem lam_zero (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) : l 0 = 0 := by
  obtain ⟨C, -, hC⟩ := hG.Λbd l hl
  have h0 := hC 0 0 continuous_const (fun _ _ _ => rfl) (fun x _ => by simp)
  exact norm_le_zero_iff.mp h0

theorem lam_smul (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) (a : ℂ) (F : G → ℂ)
    (hF : Continuous F) (hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) : l (fun g => a * F g) = a * l F := by
  have h := hG.Λadd l hl a F 0 hF continuous_const hFi (fun _ _ _ => rfl)
  rw [lam_zero hG l hl, add_zero, add_zero] at h
  have hfun : (fun g => a * F g) = a • F := by
    funext g
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h

theorem lam_local (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hs : s₀ ∈ U) (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g)
    (hEr : ∀ z : ℂ, σ < z.re → ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧ H s₀ = l (I 1) ∧ ∀ᶠ z in 𝓝[≠] s₀, l (E z) = d.eval z * H z := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hEcont : ∀ z ∈ U, Continuous (E z) := by
    intro z hzU
    exact hEc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzU, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C U (fun z x => E z x) hUo
    (hEc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hEh x)
  have hfeq : ∀ z ∈ U, l (E z) = L (Φ z) := by
    intro z hzU
    have hmem : E z ∈ invSub Γ := ⟨hEcont z hzU, hEinv z hzU⟩
    rw [hL (E z) hmem (hEcont z hzU)]
    congr 1
    ext x
    rw [hΦ z hzU x]
    rfl
  have hfan : AnalyticOnNhd ℂ (fun z => l (E z)) U :=
    ((L.differentiable.comp_differentiableOn hΦd).congr hfeq).analyticOnNhd hUo
  obtain ⟨H, hHext, hHan, hHval⟩ := hG.Λval l hl
  refine ⟨H, hHan, hHval, ?_⟩
  have hext1 : GlobalTheory.Cont.IsExtAt (fun z => l (E z)) s₀ (fun z => l (E z)) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, hfan, ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hpoly : GlobalTheory.Cont.IsExtAt (fun z => d.eval z) s₀ (fun z => d.eval z) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, fun z _ => (Polynomial.differentiable d).analyticAt z,
      ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hmul := hpoly.mul hHext
  have hright : GlobalTheory.Cont.EqRight (fun z => l (E z))
      (fun s => d.eval s * l (GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (s - s₀) * sec 1 x))) := by
    obtain ⟨σ₁, hσ₁⟩ := hUr.1
    refine ⟨max σ σ₁, fun z hzr => ?_⟩
    have hzr' : max σ σ₁ < z.re := hzr
    have hz1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hzr'
    have hzU : z ∈ U := hσ₁ (show σ₁ < z.re from lt_of_le_of_lt (le_max_right _ _) hzr')
    show l (E z) = d.eval z * l (GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z))
    obtain ⟨cs, hcsdef⟩ : ∃ cs, cs = GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) := ⟨_, rfl⟩
    rw [← hcsdef]
    have hE : ∀ g, E z g = d.eval z * cs g := by
      intro g
      rw [hEr z hz1 g, hcsdef]
    by_cases hd0 : d.eval z = 0
    · have hE0 : E z = 0 := funext fun g => by rw [hE g, hd0, zero_mul]; rfl
      rw [hE0, lam_zero hG l hl, hd0, zero_mul]
    · have hcs : cs = fun g => (d.eval z)⁻¹ * E z g := by
        funext g
        rw [hE g, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      have hcsc : Continuous cs := by
        rw [hcs]
        exact continuous_const.mul (hEcont z hzU)
      have hcsi : ∀ γ ∈ Γ, ∀ g, cs (γ * g) = cs g := by
        intro γ hγ g
        rw [hcs]
        simp only
        rw [hEinv z hzU γ hγ g]
      have hEf : E z = fun g => d.eval z * cs g := funext hE
      rw [hEf, lam_smul hG l hl _ cs hcsc hcsi]
  exact (hext1.congr hright).eventuallyEq hmul

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpC
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def fLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (y : KR n × (Fin n → Fin n → ℝ)) (w : ℂ) : ℂ :=
  (F0 p q e (y.1 : GR n))⁻¹ * (((hLoc ((y.1 : GR n) * A * nbEl y.2 * B) : ℂ) ^ w *
    F0 p q e ((y.1 : GR n) * A * nbEl y.2 * B)) * ψ y.2)

theorem continuous_fLoc (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) :
    Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => fLoc p q e A B ψ y.1 y.2) := by
  have hg : Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => ((y.1.1 : GR n) * A * nbEl y.1.2 * B)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_const).mul
      (continuous_nbEl.comp (continuous_snd.comp continuous_fst))).mul continuous_const
  unfold fLoc
  refine (((continuous_weight_factor p q e).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).inv₀
    (fun _ => weight_factor_ne_zero _ _ _ _)).mul ?_
  refine ((Continuous.cpow ?_ continuous_snd ?_).mul ((continuous_weight_factor p q e).comp hg)).mul
    (hψ.comp (continuous_snd.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (continuous_hLoc.comp hg)
  · intro y
    exact Complex.ofReal_mem_slitPlane.2 (hLoc_pos _)

theorem continuous_fLoc_w (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (w : ℂ) :
    Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => fLoc p q e A B ψ y w) := by
  have h1 := continuous_fLoc p q e A B hψ
  have h2 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y, w) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
    continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

theorem cz_eq (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] (w : ℂ) :
    czLoc p q e A B ψ μ w =
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hint : Integrable (fun y => fLoc p q e A B ψ y w) ((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    ((continuous_fLoc_w p q e A B hψ.1 w).continuousOn).integrableOn_compact hK
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hint ⊢
  rw [integral_prod _ hint]
  unfold czLoc jLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [fLoc]
  rw [integral_const_mul]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport ψ (Function.mem_support.2 h))
  simp [h0]

theorem cz_diff (hH : HolParam) (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] :
    Differentiable ℂ (czLoc p q e A B ψ μ) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hmeas : MeasurableSet ((univ : Set (KR n)) ×ˢ tsupport ψ) :=
    MeasurableSet.univ.prod (isClosed_tsupport ψ).measurableSet
  haveI : IsFiniteMeasure ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) hψ.2.1.measure_lt_top⟩
  have hnull : ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
      ((univ : Set (KR n)) ×ˢ tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]
  have hcont := (continuous_fLoc p q e A B hψ.1).continuousOn (s := ((univ : Set (KR n)) ×ˢ tsupport ψ) ×ˢ (univ : Set ℂ))
  have hdiff : ∀ y ∈ ((univ : Set (KR n)) ×ˢ tsupport ψ),
      DifferentiableOn ℂ (fun w => fLoc p q e A B ψ y w) univ := by
    intro y _
    refine Differentiable.differentiableOn ?_
    unfold fLoc
    refine Differentiable.const_mul ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.const_cpow differentiable_id (Or.inl ?_)
    exact_mod_cast (hLoc_pos _).ne'
  have h := (hH (KR n × (Fin n → Fin n → ℝ)) ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
    _ hK hnull univ (fun y w => fLoc p q e A B ψ y w) isOpen_univ hcont hdiff).1
  have heq : czLoc p q e A B ψ μ = fun w =>
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    funext (cz_eq p q e A B hψ μ)
  rw [heq]
  exact differentiableOn_univ.1 h

set_option maxHeartbeats 800000 in
theorem locOp : LV → Iwa → Mult → HolParam → LocOp := by
  intro hLV hIwa hMult hHol n p q e hgood _ _ μ _ _
  let ι : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)
  have hι : Continuous ι := continuous_mR.comp continuous_subtype_val
  have hιs : ∀ g : M2 n, InK g ↔ ∃ k, ι k = g := by
    intro g
    constructor
    · intro hg
      exact ⟨LocOpA.kOf ⟨g, hg⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  obtain ⟨ψ, a, b, hψ, ha, hb, hne⟩ := hLV n p q hgood (KR n) μ ι hι hιs
  refine ⟨ψ, mkG a ha, mkG b hb, nbEl, czLoc p q e (mkG a ha) (mkG b hb) ψ μ, hψ, fun x => rfl, continuous_nbEl,
    cz_diff hHol p q e _ _ hψ μ, ?_, fun w y => eigen hIwa hMult p q e _ _ ψ μ w y⟩
  rw [cz_zero]
  refine mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (det_mR_ne (mkG a ha)) (det_mR_ne (mkG b hb)))) ?_
  exact hne

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMB
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem coV : CoV := by
  intro m n A hA F
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = mulR A y := by
    intro y; funext a j
    simp [L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hdetLi : LinearMap.det Li = Complex.normSq A.det := by
    simp only [Li]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]
  have hdet : LinearMap.det L = Complex.normSq A.det ^ m := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : 0 < Complex.normSq A.det ^ m := pow_pos (Complex.normSq_pos.2 hA) _
  have hne : LinearMap.det L ≠ 0 := by rw [hdet]; exact hD.ne'
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.equivOfDetNeZero L hne
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = mulR A y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  have h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x := by
    have := integral_map_equiv e F (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphA
section
namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem helpA : HelpA :=
  ⟨fun _ X => ⟨aD X, isDil_aD X⟩, fun _ X s a a' h h' => isDil_unique X s a a' h h', fun _ => isCompact_KR,
    fun _ h => ⟨automorphy_first_det_ne_zero h, automorphy_second_det_ne_zero h⟩, fun _ p q e X a ha h s => holomorphic_section_extension_eq p q e X a ha h s,
    fun _ p q e X S hS => holomorphic_section_extension_exists p q e X S hS,
    fun _ p q e => ⟨(spherical_section_continuous_ne_zero p q e).1, fun k _ => (spherical_section_continuous_ne_zero p q e).2 k⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
end

