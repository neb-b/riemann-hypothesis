module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHilbertEisensteinWeightTwoSeries
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.QHolo

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_upperHalf : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, (fun z : Emb F → ℂ => (z τ).im) ⁻¹' Set.Ioi 0 := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ => isOpen_Ioi.preimage (by fun_prop)

theorem qClass_two (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : qClass 𝔞 𝔟 2 z c =
    ((|(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 : ℝ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ (c.out.1.1 * c.out.1.2) : ℂ) * z τ) := by
  simp [qClass, qTerm, qPow]

theorem differentiable_qClass (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) :
    Differentiable ℂ (fun z => qClass 𝔞 𝔟 2 z c) := by
  simp only [qClass_two]
  fun_prop

theorem norm_qClass (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ‖qClass 𝔞 𝔟 2 z c‖ =
    |(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 *
      Real.exp (-(2 * Real.pi) * ∑ τ, τ (c.out.1.1 * c.out.1.2) * (z τ).im) := by
  rw [qClass_two, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _))]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem summable_of_fiber {α β : Type} (g : α → β) (f : α → ℝ) (B : β → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hB : Summable B) (hfib : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ B b) :
    Summable f := by
  classical
  have hB0 : ∀ b, 0 ≤ B b := fun b => by simpa using hfib b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, B b) fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g) (g := g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  calc ∑ b ∈ u.image g, ∑ a ∈ u with g a = b, f a ≤ ∑ b ∈ u.image g, B b :=
        Finset.sum_le_sum fun b _ => hfib b _ fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑' b, B b := hB.sum_le_tsum _ fun b _ => hB0 b

theorem card_fiber_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟)))
    (hs : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) :
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := _root_.GlobalTheory.QFiber.card_le_norm F 𝔞 𝔟 ξ s hs

theorem abs_norm_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟) :
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := _root_.GlobalTheory.NormLe.main F 𝔞 𝔟 p

theorem summable_exp_trace [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) :=
  _root_.GlobalTheory.LatExpSum.summable_exp_neg_trace F L δ hδ

theorem norm_sq_exp_le [IsTotallyReal F] {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
    |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) :=
  _root_.GlobalTheory.norm_sq_mul_exp_neg_trace_le F δ hδ

theorem summable_key [IsTotallyReal F] (𝔞 𝔟 : Frac F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun c : Quotient (qRel 𝔞 𝔟) =>
      |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))) := by
  have hna : 0 ≤ nrm 𝔞 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  have hnb : 0 ≤ nrm 𝔟 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  let β := {x : F // x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) ∧ ∀ τ : Emb F, 0 < τ x}
  let g : Quotient (qRel 𝔞 𝔟) → β := fun c =>
    ⟨c.out.1.1 * c.out.1.2, FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1, c.out.2.2.2⟩
  let B : β → ℝ := fun x => |(Algebra.norm ℚ x.1 : ℝ)| / (nrm 𝔞 * nrm 𝔟) *
    (|(Algebra.norm ℚ x.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ x.1))
  obtain ⟨C, hC⟩ := norm_sq_exp_le (F := F) hδ
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
      ((summable_exp_trace (F := F) ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) (half_pos hδ)).mul_left
        ((nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ * C))
    have h := hC x.1 x.2.2
    have : B x = (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ *
        (|(Algebra.norm ℚ x.1 : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
      simp only [B]; field_simp
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ by positivity)
    linarith
  refine summable_of_fiber g _ B (fun c => by positivity) hB fun b s hs => ?_
  have hξ : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = b.1 := fun c hc => by rw [← hs c hc]
  calc ∑ c ∈ s, |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))
      ≤ ∑ c ∈ s, |(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [← hξ c hc]
        exact mul_le_mul_of_nonneg_right (abs_norm_le 𝔞 𝔟 c.out) (Real.exp_pos _).le
    _ = (s.card : ℝ) * (|(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B b := mul_le_mul_of_nonneg_right (card_fiber_le 𝔞 𝔟 b.1 s hξ) (by positivity)

theorem exists_im_bound {y : Emb F → ℂ} (hy : y ∈ upperHalf F) :
    ∃ ε > 0, ∀ v ∈ Metric.ball y ε, ∀ τ, ε ≤ (v τ).im := by
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ τ, 2 * ε ≤ (y τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => isEmptyElim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min (fun τ => (y τ).im)
      exact ⟨(y τ₀).im / 2, half_pos (hy τ₀), fun τ => by linarith [hτ₀ τ]⟩
  refine ⟨ε, hε, fun v hv τ => ?_⟩
  have h1 : dist (v τ) (y τ) < ε := (dist_le_pi_dist v y τ).trans_lt (Metric.mem_ball.1 hv)
  have h2 : |(v τ).im - (y τ).im| < ε := by
    rw [Complex.dist_eq] at h1
    exact (by simpa using Complex.abs_im_le_norm (v τ - y τ) : |(v τ).im - (y τ).im| ≤ ‖v τ - y τ‖).trans_lt h1
  linarith [hle τ, (abs_lt.1 h2).1]

theorem qholo : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc isOpen_upperHalf
    (fun c z => qClass 𝔞 𝔟 2 z c) (fun c => (differentiable_qClass 𝔞 𝔟 c).differentiableOn) ?_
  intro y hy
  obtain ⟨ε, hε, hv⟩ := exists_im_bound hy
  refine ⟨ε, hε, fun c => (nrm 𝔞)⁻¹ * (|(Algebra.norm ℚ c.out.1.1 : ℝ)| *
      Real.exp (-(2 * Real.pi * ε) * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))),
    (summable_key 𝔞 𝔟 (by positivity)).mul_left _, fun c v hvb => ?_⟩
  rw [norm_qClass, div_eq_inv_mul, mul_assoc]
  have hn : 0 ≤ (nrm 𝔞)⁻¹ := inv_nonneg.2 (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hn
  refine Real.exp_le_exp.2 ?_
  have hpos := c.out.2.2.2
  have : ε * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) ≤ ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) * (v τ).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hv v hvb τ]
  have hπ := Real.pi_pos
  nlinarith

end GlobalTheory.QHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitOfPullbackEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_unit_of_pullback_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ (T : Scheme.{0}) (t : T ⟶ S)
    (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → φ' ≫ u.left = φ' ≫ v.left →
    ∀ τ : T, ∀ x : A.left, A.hom x = t τ → (u * v⁻¹).left x = (η[B]).left (t τ) := by
  intro S A B _ _ _ _ u v _ _ _ _ T t A' _ φ' hp he τ x hx
  have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
  let P : Over.mk (A'.hom ≫ t) ⟶ A := Over.homMk φ' (by simpa using hw)
  have hPu : P ≫ u = P ≫ v := by
    ext1; simpa [P] using he
  have h1 : P ≫ (u * v⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hPu, mul_inv_cancel]
  have h2 : φ' ≫ (u * v⁻¹).left = A'.hom ≫ t ≫ (η[B]).left := by
    have := congrArg CommaMorphism.left h1
    simpa [P, Hom.one_def] using this
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x τ hx
  have hf : (hp.1.isoPullback.inv ≫ φ') z = x := by rw [hp.1.isoPullback_inv_fst]; exact hz1
  have hs : (hp.1.isoPullback.inv ≫ A'.hom) z = τ := by rw [hp.1.isoPullback_inv_snd]; exact hz2
  rw [Scheme.Hom.comp_apply] at hf hs
  rw [← hf, ← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePred
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

theorem eq_one_off_mul {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (M N : Matrix (Fin r) (Fin r) F)
    (hM : ∀ i j, ¬ (S i ∧ S j) → M i j = (1 : Matrix (Fin r) (Fin r) F) i j)
    (hN : ∀ i j, ¬ (S i ∧ S j) → N i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ∀ i j, ¬ (S i ∧ S j) → (M * N) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  intro i j hij
  by_cases hi : S i
  · have hj : ¬ S j := fun h => hij ⟨hi, h⟩
    have e : (M * N) i j = (M * (1 : Matrix (Fin r) (Fin r) F)) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hN a j fun h => hj h.2]
    rw [e, Matrix.mul_one, hM i j hij]
  · have e : (M * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hM i a fun h => hi h.1]
    rw [e, Matrix.one_mul, hN i j hij]

theorem exists_gl_vecMul_eq_single_of_ne {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l c ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  set e : Fin r → F := Pi.single c 1 with he
  set A : Matrix (Fin r) (Fin r) F := vecMulVec e (l - e) with hA
  have hd : (l - e) ⬝ᵥ e = l c - 1 := by simp [he]
  have hAA : A * A = (l c - 1) • A := by
    rw [hA, vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
  have h1 : (1 - (l c)⁻¹ • A) * (1 + A) = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc, mul_add, mul_one, hAA]
    have : A + (l c - 1) • A = l c • A := by rw [sub_smul, one_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hl, one_smul]; abel
  refine ⟨⟨1 - (l c)⁻¹ • A, 1 + A, h1, mul_eq_one_comm.mp h1⟩, ?_, ?_⟩
  · intro i j hij
    have : A i j = 0 := by
      rw [hA, vecMulVec_apply]
      by_cases hi : i = c
      · have hj : ¬ S j := fun h => hij ⟨hi ▸ hc, h⟩
        have hlj : l j = 0 := by
          by_contra h
          exact hj (hS j h)
        have hjc : j ≠ c := fun h => hj (h ▸ hc)
        simp [he, hlj, hjc]
      · simp [he, hi]
    simp [this]
  · have hv : Matrix.vecMul l A = l c • (l - e) := by
      rw [hA, vecMul_vecMulVec]
      simp [he]
    show Matrix.vecMul l (1 - (l c)⁻¹ • A) = e
    rw [vecMul_sub, vecMul_one, vecMul_smul, hv, smul_smul, inv_mul_cancel₀ hl, one_smul]
    abel

theorem exists_gl_vecMul_eq_single {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  by_cases hlc : l c = 0
  swap
  · exact exists_gl_vecMul_eq_single_of_ne S c hc l hlc hS
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
  have ha : l a ≠ 0 := ha
  have hac : a ≠ c := fun h => ha (h ▸ hlc)
  have h1 : transvection a c (1 : F) * transvection a c (-1 : F) = 1 := by
    rw [transvection_mul_transvection_same a c hac, add_neg_cancel, transvection_zero]
  let t : GL (Fin r) F := ⟨transvection a c 1, transvection a c (-1), h1, mul_eq_one_comm.mp h1⟩
  have hv : ∀ j, Matrix.vecMul l (transvection a c (1 : F)) j = l j + if j = c then l a else 0 := by
    intro j
    rw [transvection, vecMul_add, vecMul_one, Pi.add_apply]
    congr 1
    by_cases hj : j = c
    · subst hj
      simp [vecMul, dotProduct, Matrix.single_apply]
    · simp [vecMul, dotProduct, Matrix.single_apply, hj, Ne.symm hj]
  obtain ⟨h, hh1, hh2⟩ := exists_gl_vecMul_eq_single_of_ne S c hc (Matrix.vecMul l (transvection a c (1 : F)))
    (by rw [hv]; simpa [hlc] using ha)
    (by
      intro i hi
      by_cases hic : i = c
      · exact hic ▸ hc
      · rw [hv] at hi
        exact hS i (by simpa [hic] using hi))
  refine ⟨t * h, ?_, ?_⟩
  · refine eq_one_off_mul S (transvection a c (1 : F)) _ ?_ hh1
    intro i j hij
    have : ¬ (a = i ∧ c = j) := fun h => hij ⟨h.1 ▸ hS a ha, h.2 ▸ hc⟩
    simp [transvection, Matrix.single_apply, this]
  · rw [← hh2, vecMul_vecMul]
    rfl

theorem exists_blockTri_vecMul_eq_single : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  intro F _ r b hb k k' hk l hl hS
  have hk' : k' < k ∧ b k' = b k := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
    obtain ⟨h1, h2⟩ := hS a ha
    have h3 : k' < k := by rw [Fin.lt_def]; omega
    have h4 : a ≤ k' := by rw [Fin.lt_def] at h1; rw [Fin.le_def]; omega
    exact ⟨h3, le_antisymm (hb h3.le) (h2 ▸ hb h4)⟩
  obtain ⟨h, h1, h2⟩ := exists_gl_vecMul_eq_single (fun i => i < k ∧ b i = b k) k' hk' l hl hS
  refine ⟨⟨h, ?_⟩, ?_, h2⟩
  · have : (h : Matrix (Fin r) (Fin r) F).BlockTriangular b := by
      intro i j hij
      rw [h1 i j (fun hh => by rw [hh.1.2, hh.2.2] at hij; exact lt_irrefl _ hij)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
    exact this
  · intro i j hij
    by_contra hn
    exact hij (h1 i j fun hh => hn ⟨hh.1.1, hh.2.1⟩)

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_complex_linear_of_pure_types_of_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ N hN hsp h₁ h₂
  obtain ⟨r, hr⟩ := exists_real_extension_of_lattice P hP.2.1 hP.2.2.1 hP.2.2.2.1
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  have hr' : ∀ a, r (P a) = P' (Φ a) := hr
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 ∧ H.rt0.im ≠ 0 := by
    have e₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have e₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at e₁ e₂
    have him : H.rt0.im ≠ 0 := fun h => by
      rw [h] at e₁; nlinarith [mul_self_nonneg H.rt0.re]
    refine ⟨?_, him⟩
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hρ : H.rt0 = (H.rt0.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre.1]
  have key : ∀ (ρ : ℂ) (a : D.La), a ∈ lat hP ρ → Φ a ∈ lat hP' ρ → r (ρ • P a) = ρ • r (P a) := by
    intro ρ a ha ha'
    rw [← period_rt_smul hP ha, hr', hr', map_smul, period_rt_smul hP' ha']
  have hPN : ∀ a, r (H.rt0 • P (N • a)) = H.rt0 • r (P (N • a)) := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hsp a)
    rw [← hxy]
    have k₁ := key _ x hx (h₁ x hx)
    have k₂ := key _ y hy (h₂ y hy)
    rw [neg_smul, neg_smul, map_neg, neg_inj] at k₂
    rw [map_add (f := _), smul_add, map_add (f := _), map_add (f := _), smul_add, k₁, k₂]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hP0 : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    have h := hPN a
    rw [map_nsmul, smul_comm H.rt0 N, map_nsmul, map_nsmul, smul_comm H.rt0 N,
      ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact smul_right_injective _ hNc h
  have h0 : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hP0 a
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, r.map_smul, r.map_smul, hx, smul_comm]
  have hI : ∀ v, r (Complex.I • v) = Complex.I • r v := by
    intro v
    have := h0 v
    rw [hρ, mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_smul] at this
    exact smul_right_injective _ hre.2 this
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← Complex.re_add_im c, add_smul, add_smul, mul_smul, mul_smul, Complex.coe_smul,
          Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul, hI] }
  have hsurj : Function.Surjective L := by
    show Function.Surjective r
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hP'.2.2.2.1, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨P (Φ.symm a), by rw [hr', Φ.apply_symm_apply]⟩
  exact ⟨LinearEquiv.ofBijective L ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun a => (hr' a).symm⟩

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

def TrivCond {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S) : Prop :=
  ∀ (Y : Scheme.{0}) (φ : Y ⟶ A.left) (y : Y ⟶ T), IsPullback φ y A.hom t →
    ∃ s : (N.pull φ).Gen, s.IsGen

theorem exists_gen_pull_comp {X Y Y' : Scheme.{0}} (N : LB X) (φ : Y ⟶ X)
    (h : Y' ⟶ Y) (hs : ∃ s : (N.pull φ).Gen, s.IsGen) : ∃ s : (N.pull (h ≫ φ)).Gen, s.IsGen := by
  obtain ⟨s, hs⟩ := hs
  exact ⟨LB.pullGen N (fun _ => φ) (fun _ => 1) s h, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ s hs h⟩

theorem trivCond_comp {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T T' : Scheme.{0}) (t : T ⟶ S)
    (u : T' ⟶ T) (h : TrivCond A N T t) : TrivCond A N T' (u ≫ t) := by
  intro Y φ y hY
  have hw : φ ≫ A.hom = (y ≫ u) ≫ t := by rw [hY.w, Category.assoc]
  have := exists_gen_pull_comp N _ (pullback.lift φ (y ≫ u) hw)
    (h _ _ _ (IsPullback.of_hasPullback A.hom t))
  rwa [pullback.lift_fst] at this

theorem trivCond_iff {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S)
    (X : Scheme.{0}) (φ' : X ⟶ A.left) (x : X ⟶ T) (hP : IsPullback φ' x A.hom t) :
    (∃ s : (N.pull φ').Gen, s.IsGen) ↔ TrivCond A N T t := by
  refine ⟨fun h Y φ y hY => ?_, fun h => h _ _ _ hP⟩
  have := exists_gen_pull_comp N φ' (hP.lift φ y hY.w) h
  rwa [hP.lift_fst] at this

end GlobalTheory.TrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFinite
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.exists_pow_char_eq_of_isReduced_finite : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  intro p _ k _ _ _ A _ _ _ _ a
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  let e := IsArtinianRing.equivPi A
  have key : ∀ I : MaximalSpectrum A, ∃ c : A ⧸ I.asIdeal, e a I = c ^ p := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite k (A ⧸ I.asIdeal) := Module.Finite.trans A (A ⧸ I.asIdeal)
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : PerfectField (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.perfectField k
    haveI : CharP (A ⧸ I.asIdeal) p :=
      charP_of_injective_algebraMap (algebraMap k (A ⧸ I.asIdeal)).injective p
    haveI : PerfectRing (A ⧸ I.asIdeal) p := PerfectField.toPerfectRing p
    obtain ⟨c, hc⟩ := surjective_frobenius (A ⧸ I.asIdeal) p (e a I)
    exact ⟨c, by rw [← hc, frobenius_def]⟩
  choose c hc using key
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  rw [hc I, Pi.pow_apply]
end

