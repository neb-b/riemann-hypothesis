module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0018

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

open Classical in
theorem gen_sch (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hfr : IsUnit fr.det)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hl : ∀ τ', l τ' ≠ 0)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (hp : ∀ v ∈ p.vars, v.1 ≠ τ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    tens θ τ fr f (fun x => evalPoly p (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
  obtain ⟨S, hS⟩ := hf
  set A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun t => gramAt D V t * s t with hAdef
  have hA : ∀ t, t ≠ τ → (A t).PosDef := fun t _ => (hs t).2.2
  have hw : ∀ t, t ≠ τ → 0 < |l t| := fun t _ => abs_pos.mpr (hl t)
  obtain ⟨G, hG⟩ := exists_gauss (n := n) τ A hA (fun t => |l t|) hw
  set poly : Bsp τ V.rank n → ℂ := fun b => MvPolynomial.eval (fun k => vC τ k b) p with hpoly
  have hpolyT : poly.HasTemperateGrowth := tg_poly τ p
  set h : 𝓢(Bsp τ V.rank n, ℂ) := SchwartzMap.smulLeftCLM ℂ poly G with hh
  have hhv : ∀ b, h b = poly b * G b := fun b => by
    rw [hh, SchwartzMap.smulLeftCLM_apply_apply hpolyT, smul_eq_mul]
  obtain ⟨Fp, hFp⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod S h
  let e₀ : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ≃ₗ[ℝ]
      ((Fin V.rank → Fin n → ℂ) × Bsp τ V.rank n) :=
    { toFun := fun z => (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun t => z t.1)
      invFun := fun ab t => if ht : t = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨t, ht⟩
      map_add' := fun z w => by
        ext1
        · exact Matrix.mul_add fr⁻¹ (Matrix.of (z τ)) (Matrix.of (w τ))
        · rfl
      map_smul' := fun r z => by
        ext1
        · exact Matrix.mul_smul fr⁻¹ r (Matrix.of (z τ))
        · rfl
      left_inv := fun z => by
        funext t
        by_cases ht : t = τ
        · subst t
          simp
          change (fr * (fr⁻¹ * Matrix.of (z τ))).row = (Matrix.of (z τ)).row
          rw [Matrix.mul_nonsing_inv_cancel_left fr _ hfr]
        · simp [ht]
      right_inv := fun ab => by
        ext1
        · simp
          change (fr⁻¹ * (fr * Matrix.of ab.1)).row = (Matrix.of ab.1).row
          rw [Matrix.nonsing_inv_mul_cancel_left fr _ hfr]
        · funext t
          simp [t.2] }
  let e := e₀.toContinuousLinearEquiv
  let Fz : 𝓢(D.what₂.Tau → Fin V.rank → Fin n → ℂ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Fp
  have hFz : ∀ z, Fz z = S (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (poly (fun t => z t.1) * G (fun t => z t.1)) := by
    intro z
    simp only [Fz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hFp, hhv]
    rfl
  have hpolyz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      poly (fun t => z t.1) = evalPoly p (fun t => Matrix.of (z t)) := by
    intro z
    rw [evalPoly_congr p τ hp (fun t => Matrix.of (z t)) (extF τ (fun t => z t.1)) (fun t ht => by simp only [extF, dif_neg ht]; rfl)]
    rfl
  have hGz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      G (fun t => z t.1) = gAway V l s τ (fun t => Matrix.of (z t)) := by
    intro z
    rw [hG]
    unfold gAway qf
    congr 1
    rw [Finset.sum_subtype _ (p := fun τ' => τ' ≠ τ) (fun x => by simp)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← tr_im_zero (hA t.1 t.2).isHermitian (Matrix.of (z t.1))]
    simp only [hAdef]
    ring
  have key : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, Fz z = f (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) *
      (evalPoly p (fun t => Matrix.of (z t)) * gAway V l s τ (fun t => Matrix.of (z t))) := by
    intro z
    rw [hFz, hpolyz, hGz, hS]
  refine Submodule.subset_span ⟨Fz, g, hg, ?_⟩
  funext x
  rw [key]
  simp only [tens, mul_assoc]
  rfl

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
section
noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def DBoundPQ : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X)) ∧
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p' ∈ N, p'.2 ∈ stripS X → ∀ u, ‖famPQ ε t c e p q p'.1 X p'.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

namespace DBoundBH

open DBoundH DBoundAH

variable {n : ℕ}

theorem isOpen_stripS (X : Fin n → ℝ) : IsOpen (stripS X) := by
  have : stripS X = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by ext z; simp [stripS]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_abs.comp (Complex.continuous_im.mul continuous_const))) continuous_const

private theorem entC_mR_mul_aC_univ_prod_stripS (X : Fin n → ℝ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => mR p.1 * aC X p.2) := by
  apply entC_mul
  · intro i j
    exact (Continuous.matrix_elem (mR_cont.comp continuous_fst) i j).continuousOn
  · intro i j
    apply Continuous.continuousOn
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases h : i = j <;> simp [aC, Matrix.diagonal_apply, h] <;> fun_prop

theorem ptZ_entC (X : Fin n → ℝ) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => ptZ p.1 X p.2 s) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h11 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₁) :=
    fun i j => hM (Sum.inl i) (Sum.inl j)
  have h12 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₂) :=
    fun i j => hM (Sum.inl i) (Sum.inr j)
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  have hden : ∀ p ∈ Set.univ ×ˢ stripS X,
      ((mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂).det ≠ 0 := by
    intro p hp
    rcases hs with rfl | rfl
    · exact (dSieg n p.1 X p.2 hp.2).2.2.1
    · exact (dSieg n p.1 X p.2 hp.2).2.2.2
  exact entC_mul (entC_add (entC_mul h11 (entC_const _ _)) h12)
    (entC_inv (entC_add (entC_mul h21 (entC_const _ _)) h22) hden)

private theorem entC_toBlocks_smul_add_univ_prod_stripS (X : Fin n → ℝ) (s : ℂ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ =>
      (mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  exact entC_add (entC_mul h21 (entC_const _ _)) h22

theorem jC_contOn (X : Fin n → ℝ) (e : ℤ) (p q : ℕ) :
    ContinuousOn (fun p' : GR n × ℂ => jC e p q p'.1 X p'.2) (Set.univ ×ˢ stripS X) := by
  have h0 : ContinuousOn (fun x : GR n × ℂ => (mR x.1 * aC X x.2).det ^ e) (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_mR_mul_aC_univ_prod_stripS X)).zpow₀ _ fun x _ => Or.inl (det_bigM_ne x.1 X x.2)
  have h1 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(p : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X Complex.I)).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.1
  have h2 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * -Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(q : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X (-Complex.I))).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.2
  exact (h0.mul h1).mul h2

private theorem re_I_mul_ofReal_mul_eq_neg_mul_im (c : ℝ) (w : ℂ) : (Complex.I * c * w).re = -(c * w.im) := by
  simp [Complex.mul_re, Complex.mul_im]

private theorem sum_norm_sq_rowC_eq_sum_norm_sq {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) :
    ∑ j, ‖rowC u a j‖ ^ 2 = ∑ j, ‖u a j‖ ^ 2 := by
  simp [rowC, norm_star]

theorem re_bound {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (Z Z' : Matrix (Fin n) (Fin n) ℂ)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : ∀ w : Fin n → ℂ, δ₁ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re)
    (h2 : ∀ w : Fin n → ℂ, δ₂ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z'ᴴ - Z')) *ᵥ w)).re)
    (u : Fin m → Fin n → ℂ) :
    (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace).re ≤
      -(c * min δ₁ δ₂ * ∑ a, ∑ j, ‖u a j‖ ^ 2) := by
  set S : Fin m → ℝ := fun a => ∑ j, ‖u a j‖ ^ 2 with hSdef
  have hS : ∀ a, 0 ≤ S a := fun a => by positivity
  have hT : ∀ a, c * min δ₁ δ₂ * S a ≤
      c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im := by
    intro a
    have e1 := h1 (rowC u a)
    rw [sum_norm_sq_rowC_eq_sum_norm_sq, ← im_eq_re] at e1
    have hm : min δ₁ δ₂ * S a ≤ δ₁ * S a := mul_le_mul_of_nonneg_right (min_le_left _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e1 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hF : ∀ a, c * min δ₁ δ₂ * S a ≤
      -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) := by
    intro a
    have e2 := h2 (rowC u a)
    have hflip : (star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z'ᴴ - Z')) *ᵥ rowC u a)
        = -(star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z' - Z'ᴴ)) *ᵥ rowC u a) := by
      rw [← neg_sub Z' Z'ᴴ, smul_neg, Matrix.neg_mulVec, dotProduct_neg]
    rw [hflip, Complex.neg_re, ← im_eq_re, sum_norm_sq_rowC_eq_sum_norm_sq] at e2
    have hm : min δ₁ δ₂ * S a ≤ δ₂ * S a := mul_le_mul_of_nonneg_right (min_le_right _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e2 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hsplit : ∑ a, S a = ∑ a with epsT t ε a = true, S a + ∑ a with epsT t ε a = false, S a := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => epsT t ε a = true) S]
    simp only [Bool.not_eq_true]
  rw [trace_gramB, trace_gramB, Finset.mul_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum,
    Complex.re_sum]
  simp only [re_I_mul_ofReal_mul_eq_neg_mul_im]
  have A : ∑ a with epsT t ε a = true, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = true, c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im :=
    Finset.sum_le_sum fun a _ => hT a
  have B : ∑ a with epsT t ε a = false, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = false, -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) :=
    Finset.sum_le_sum fun a _ => hF a
  rw [← Finset.mul_sum] at A B
  rw [Finset.sum_neg_distrib] at B ⊢
  rw [Finset.sum_neg_distrib]
  have hall : ∑ a, ∑ j, ‖u a j‖ ^ 2 = ∑ a, S a := rfl
  rw [hall, hsplit]
  nlinarith

end DBoundBH

open DBoundH DBoundAH DBoundBH in
theorem dBoundPQ : DBoundPQ := by
  intro m n ε t c e p q X hc _
  refine ⟨fun y u => famPQ_holo ε t c e p q X y u, famPQ_cont ε t c e p q X, ?_⟩
  intro y₀ z₀ hz₀
  have hopen : IsOpen (Set.univ ×ˢ stripS X : Set (GR n × ℂ)) := isOpen_univ.prod (isOpen_stripS X)
  have hmem : Set.univ ×ˢ stripS X ∈ 𝓝 ((y₀, z₀) : GR n × ℂ) := hopen.mem_nhds ⟨trivial, hz₀⟩
  have cZ : ∀ s : ℂ, (s = Complex.I ∨ s = -Complex.I) → ∀ i j,
      ContinuousAt (fun x : GR n × ℂ => ptZ x.1 X x.2 s i j) (y₀, z₀) :=
    fun s hs i j => (ptZ_entC X s hs i j).continuousAt hmem
  obtain ⟨δ₁, hδ₁, ev1⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • (ptZ x.1 X x.2 Complex.I - (ptZ x.1 X x.2 Complex.I)ᴴ))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inl rfl) i j).sub (cZ _ (Or.inl rfl) j i).star))
    (dSieg n y₀ X z₀ hz₀).1
  have hpd2 : ((-(Complex.I / 2)) • ((ptZ y₀ X z₀ (-Complex.I))ᴴ - ptZ y₀ X z₀ (-Complex.I))).PosDef := by
    have h := (dSieg n y₀ X z₀ hz₀).2.1
    unfold IsSiegel at h
    rwa [Matrix.conjTranspose_conjTranspose] at h
  obtain ⟨δ₂, hδ₂, ev2⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • ((ptZ x.1 X x.2 (-Complex.I))ᴴ - ptZ x.1 X x.2 (-Complex.I)))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inr rfl) j i).star.sub (cZ _ (Or.inr rfl) i j)))
    hpd2
  have evJ : ∀ᶠ x in 𝓝 ((y₀, z₀) : GR n × ℂ),
      ‖jC e p q x.1 X x.2‖ < ‖jC e p q y₀ X z₀‖ + 1 :=
    ((jC_contOn X e p q).continuousAt hmem).norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨N, hN, hNp⟩ := (ev1.and (ev2.and evJ)).exists_mem
  refine ⟨N, c * min δ₁ δ₂, ‖jC e p q y₀ X z₀‖ + 1, hN, by positivity, ?_⟩
  intro x hx _ u
  obtain ⟨b1, b2, bJ⟩ := hNp x hx
  have hr := re_bound ε t c hc (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) δ₁ δ₂ hδ₁ hδ₂ b1 b2 u
  show ‖jC e p q x.1 X x.2 * gC ε t c (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) u‖ ≤ _
  rw [norm_mul, gC, Complex.norm_exp]
  exact mul_le_mul bJ.le (Real.exp_le_exp.2 hr) (Real.exp_pos _).le (by positivity)

theorem dBound : DBound := by
  intro m n ε t c e X hc ht
  exact dBoundPQ m n ε t c e (cnt (epsT t ε) true) (cnt (epsT t ε) false) X hc ht

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcE
section
noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcEH

open DCalcH DCalcBH DCalcDH

variable {m n : ℕ}

theorem crd_cont (X : Fin n → ℝ) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => crd (vS u X s) := by
  refine continuous_pi fun k => ?_
  unfold crd vS
  split_ifs <;> fun_prop

theorem fF_cont (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => fF c X Q u s := by
  unfold fF fP
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · simp only [evX_eq]
    exact (MvPolynomial.continuous_eval Q).comp (crd_cont X s)
  · simp only [gs, vS]
    fun_prop

theorem norm_gs (c : ℝ) (v : Fin m → Fin n → ℂ) : ‖gs c v‖ = Real.exp (-(c * sqN v)) := by
  simp only [gs, sqN]
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem sq_vS_le (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s R : ℝ) (hs : |s| ≤ R) :
    Real.exp (-(2 * R * ∑ j, |X j|)) * sqN u ≤ sqN (vS u X s) ∧ sqN (vS u X s) ≤ Real.exp (2 * R * ∑ j, |X j|) * sqN u := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hX : ∀ j, |2 * s * X j| ≤ 2 * R * ∑ j, |X j| := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| := Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hs h1 (abs_nonneg _) hR
    nlinarith
  have hterm : ∀ a j, ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (2 * s * X j) := by
    intro a j
    rw [norm_vS, ← Real.exp_nat_mul]; push_cast; ring_nf
  unfold sqN
  simp only [hterm]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    linarith [neg_abs_le (2 * s * X j), hX j]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity) |>.trans_eq (mul_comm _ _)
    linarith [le_abs_self (2 * s * X j), hX j]

theorem fF_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) :
    ∃ K a, 0 ≤ K ∧ 0 < a ∧ ∀ u, ∀ s' ∈ Set.Icc (s - 1) (s + 1), ‖fF c X Q u s'‖ ≤ K * Real.exp (-(a * sqN u)) := by
  set R := |s| + 1
  set M := ∑ j, |X j|
  set κ := Real.exp (-(2 * R * M))
  set κ' := Real.exp (2 * R * M)
  have hκ : 0 < κ := Real.exp_pos _
  have hκ' : 1 ≤ κ' := Real.one_le_exp (by positivity)
  obtain ⟨C, N, hC, hev⟩ := evX_growth Q
  obtain ⟨C2, hC2, hpe⟩ := poly_exp N (c * κ) (by positivity)
  refine ⟨Real.exp (R * m * M) * (C * (κ' ^ N * C2)), c * κ / 2, by positivity, by positivity, fun u s' hs' => ?_⟩
  have hs'R : |s'| ≤ R := by
    rw [abs_le]; constructor <;> linarith [hs'.1, hs'.2, neg_abs_le s, le_abs_self s]
  obtain ⟨hlo, hhi⟩ := sq_vS_le u X s' R hs'R
  have hS := sqN_nonneg u
  have h1 : ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ ≤ Real.exp (R * m * M) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have : |∑ j, X j| ≤ M := Finset.abs_sum_le_sum_abs _ _
    have h2 : s' * (m : ℝ) * ∑ j, X j ≤ |s'| * m * |∑ j, X j| := by
      calc s' * (m : ℝ) * ∑ j, X j ≤ |s' * (m : ℝ) * ∑ j, X j| := le_abs_self _
        _ = |s'| * m * |∑ j, X j| := by rw [abs_mul, abs_mul, Nat.abs_cast]
    have h3 : |s'| * m * |∑ j, X j| ≤ R * m * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hs'R (by positivity)) this (abs_nonneg _) (by positivity)
    linarith
  have h2 : ‖evX Q (vS u X s')‖ ≤ C * (κ' ^ N * (1 + sqN u) ^ N) := by
    refine (hev _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [sqN_nonneg (vS u X s')]) ?_ N
    nlinarith
  have h3 : ‖gs c (vS u X s')‖ ≤ Real.exp (-(c * κ * sqN u)) := by
    rw [norm_gs]; refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlo hc.le
    linarith
  unfold fF fP
  rw [norm_mul, norm_mul]
  calc ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ * (‖evX Q (vS u X s')‖ * ‖gs c (vS u X s')‖)
      ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (1 + sqN u) ^ N) * Real.exp (-(c * κ * sqN u))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg hC (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))))
          (by positivity) (by positivity)
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * ((1 + sqN u) ^ N * Real.exp (-(c * κ * sqN u))))) := by ring
    _ ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (C2 * Real.exp (-(c * κ / 2 * sqN u))))) := by
        have := hpe (sqN u) hS
        gcongr
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * C2)) * Real.exp (-(c * κ / 2 * sqN u)) := by ring

end DCalcEH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIwasawa
section
namespace PositivityTheory.Rg.Sw.Glob

theorem gIwasawa : GIwasawa := GlobalTheory.StdUnn.Iwasawa.exists_mul

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussE
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_conj (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    (actZ y Z)ᴴ = ((mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂)⁻¹ := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hM' := det_CZhD hg hZ
  have hid := identG hg Z Zᴴ
  rw [sub_self] at hid
  have hE := sub_eq_zero.mp hid
  unfold actZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  set N' := (mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂
  set M' := (mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂
  have hMh : IsUnit (Mᴴ).det := by
    rw [det_conjTranspose]
    exact hM.star
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  calc (Mᴴ)⁻¹ * Nᴴ = (Mᴴ)⁻¹ * (Nᴴ * M') * M'⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hM', Matrix.mul_one]
    _ = (Mᴴ)⁻¹ * (Mᴴ * N') * M'⁻¹ := by rw [hE]
    _ = N' * M'⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hMh, Matrix.one_mul]

theorem isSiegel_actZ (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) : IsSiegel (actZ y Z) := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hid := identG hg Z Z
  unfold IsSiegel actZ
  unfold IsSiegel at hZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
  have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
    rw [← neg_sub, hid, neg_sub]
  have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
      (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
    rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
  rw [key]
  refine Matrix.PosDef.conjTranspose_mul_mul_same hZ ?_
  exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hM))

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

