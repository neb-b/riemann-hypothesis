module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
section
namespace GlobalTheory.HatNF.SpanMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem gen_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) (H : List A)
    (hl : H.length = n) (hT : ∀ h ∈ H, h ∈ T) :
    b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod ∈ nfSpan d T i j n :=
  Submodule.subset_span ⟨b, hb, H, hl, hT, rfl⟩

theorem map_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) (f : A →ₗ[ℂ] A) (S : Submodule ℂ A)
    (h : ∀ b ∈ bmon d, ∀ H : List A, H.length = n → (∀ h ∈ H, h ∈ T) →
      f (b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod) ∈ S) :
    ∀ x ∈ nfSpan d T i j n, f x ∈ S := by
  have : nfSpan d T i j n ≤ S.comap f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hl, hT, rfl⟩
    exact h b hb H hl hT
  exact fun x hx => this hx

theorem bdd_mul (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) :
    ∀ x ∈ nfSpan d T i j n, b * x ∈ nfSpan d T i j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ b) _ ?_
  intro b' hb' H hl hT
  have := gen_mem d T i j n ((bmon d).mul_mem hb hb') H hl hT
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di * x ∈ nfSpan d T (i + 1) j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ d.L.Di) _ ?_
  intro b hb H hl hT
  have := gen_mem d T (i + 1) j n hb H hl hT
  rw [pow_succ', ← mul_assoc b, (hD b hb).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem gi_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L * x ∈ nfSpan d T i (j + 1) n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ (TL.gI d.L)) _ ?_
  intro b hb H hl hT
  have := gen_mem d T i (j + 1) n hb H hl hT
  rw [pow_succ', ← mul_assoc (b * _), ((hG b hb).mul_left (hDG.pow_left i)).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_pow_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di ^ k * x ∈ nfSpan d T (i + k) j n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact di_mul d hD T _ j n _ ih

theorem gi_pow_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L ^ k * x ∈ nfSpan d T i (j + k) n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact gi_mul d hG hDG T i _ n _ ih

theorem one_letter_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di)
    (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L)) (hDG : Commute d.L.Di (TL.gI d.L)) (T T' : Set A)
    (i₀ j₀ n i j : ℕ) (u : A) (hu : ∀ X ∈ T', X * u ∈ nfSpan d T i₀ j₀ n) :
    ∀ x ∈ nfSpan d T' i j 1, x * u ∈ nfSpan d T (i₀ + i) (j₀ + j) n := by
  refine map_mem d T' i j 1 (LinearMap.mulRight ℂ u) _ ?_
  intro b hb H hl hT
  obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
  have := bdd_mul d T _ _ n hb _ (di_pow_mul d hD T _ _ n i _
    (gi_pow_mul d hG hDG T _ _ n j _ (hu X (hT X (by simp)))))
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_cons, List.prod_nil, mul_one] using this

theorem mul_prod (d : Q.NFData P A) (T : Set A) (i j m : ℕ) (H : List A) (hT : ∀ h ∈ H, h ∈ T) :
    ∀ x ∈ nfSpan d T i j m, x * H.prod ∈ nfSpan d T i j (H.length + m) := by
  refine map_mem d T i j m (LinearMap.mulRight ℂ H.prod) _ ?_
  intro b hb H' hl hT'
  have := gen_mem d T i j (H.length + m) hb (H' ++ H) (by simp [hl, add_comm]) (by
    intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · exact hT' h h1
    · exact hT h h1)
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_append] using this

theorem span_mul : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  intro P A _ _ _ _ d hd T
  have h1 := _root_.GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan P A d hd
  obtain ⟨h2, h3, hDG⟩ := _root_.GlobalTheory.HatNF.Den.hat_den P A d hd
  have hD : ∀ b ∈ bmon d, Commute b d.L.Di := fun b hb => (h3 b hb).2.1
  have hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L) := fun b hb => (h3 b hb).2.2.1
  refine ⟨fun i j n x hx => ⟨fun b hb => bdd_mul d T i j n hb x hx, di_mul d hD T i j n x hx,
    gi_mul d hG hDG T i j n x hx⟩, ?_⟩
  intro a ha i j n X hX
  refine map_mem d T i j n (LinearMap.mulLeft ℂ X) _ ?_
  intro b hb H hl hT
  have e1 : ∀ k, X * b * d.L.Di ^ k ∈ nfSpan d (hats d.L) k 0 1 := by
    intro k
    induction k with
    | zero => simpa using h1 X hX b hb
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 1 0 1 k 0 _ (fun Y hY => (h2 Y hY).1) _ ih
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e2 : ∀ k, X * b * d.L.Di ^ i * TL.gI d.L ^ k ∈ nfSpan d (hats d.L) i k 1 := by
    intro k
    induction k with
    | zero => simpa using e1 i
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 0 1 1 i k _ (fun Y hY => (h2 Y hY).2) _ ih
      rw [zero_add] at this
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e3 := one_letter_mul d hD hG hDG T _ 0 a (H.length + 1) i j H.prod
    (fun Y hY => mul_prod d T 0 a 1 H hT Y (ha Y hY)) _ (e2 j)
  rw [zero_add, hl, add_comm a j] at e3
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using e3

end GlobalTheory.HatNF.SpanMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpNormSumSmulSqLe
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh.ContrPlus

theorem herm_sum_smul_left {ι κ : Type} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (l : κ → ℂ) (B : κ → ι → ℂ)
    (w : ι → ℂ) : herm H (∑ c, l c • B c) w = ∑ c, l c * herm H (B c) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_conj {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H w v = star (herm H v w) := by
  unfold herm
  rw [← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem herm_real_smul_right {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℝ) (v w : ι → ℂ) :
    herm H v ((t : ℂ) • w) = (t : ℂ) * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  simp

theorem opNorm_sum_smul_sq_le {V V₂ κ : Type} [Fintype κ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (a : κ → (V₂ →L[ℂ] V)) (l : κ → ℂ)
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) : ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have hS : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans ?_
    have h4 := Real.le_sqrt_of_sq_le h3
    rwa [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg y)] at h4
  calc _ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

theorem contraction_wigMap :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) (B c) ω • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c) (B c₀) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha hequi
  obtain ⟨hcomp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((Hpk k r *ᵥ B c) j) * MvPolynomial.X (Sum.inr j), a, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · intro ω
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [herm, dotProduct, mul_comm]
  · intro h hh ω
    obtain ⟨hW, hiso, -⟩ := hU h hh
    ext y
    have key : ∀ d, ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) * herm (Hpk k r) (B c) (h *ᵥ ω)
        = herm (Hpk k r) (B d) ω := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2, hiso]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, hequi h hh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← key d]
    simp only [mul_comm]
  · intro t ω
    simp only [herm_real_smul_right, pow_one, Finset.smul_sum, smul_smul]
  · intro ω h1 h2
    rw [pow_one]
    refine (opNorm_sum_smul_sq_le a _ ha).trans (le_of_eq ?_)
    have h3 : herm (Hpk k r) ω ω = ∑ c, herm (Hpk k r) ω (B c) * herm (Hpk k r) (B c) ω := by
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2]
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [herm_conj _ hH (B c) ω, Complex.star_def, Complex.conj_mul']
    norm_cast
  · intro c₀
    simp [hB.2.1]

end GlobalTheory.WigSh.ContrPlus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
section
open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.HatNF

section abstract

variable {V E ι : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ev_symm_of_nonneg (ev : V →ₗ[ℂ] E) (T : Module.End ℂ V) (h : ∀ v, 0 ≤ ⟪ev v, ev (T v)⟫_ℂ) (v w : V) :
    ⟪ev w, ev (T v)⟫_ℂ = ⟪ev (T w), ev v⟫_ℂ := by
  have hd : ∀ u, ⟪ev u, ev (T u)⟫_ℂ = ⟪ev (T u), ev u⟫_ℂ := by
    intro u
    rw [← inner_conj_symm (ev (T u)) (ev u)]
    exact (Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp (h u)).2.symm).symm
  have h1 := hd (v + w)
  have h2 := hd (v + Complex.I • w)
  have h3 := hd v
  have h4 := hd w
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
    - (1 / 2 + Complex.I / 2 * (-Complex.I * Complex.I)) * h4
    + (1 / 2 : ℂ) * (⟪ev w, ev (T v)⟫_ℂ - ⟪ev (T w), ev v⟫_ℂ - ⟪ev v, ev (T w)⟫_ℂ + ⟪ev (T v), ev w⟫_ℂ) * hI

variable [Fintype ι] [DecidableEq ι]

theorem ev_symm_single (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v w : V) :
    ⟪ev w, ev (K (Pi.single i 1) v)⟫_ℂ = ⟪ev (K (Pi.single i 1) w), ev v⟫_ℂ := by
  have hp : ∀ j, (0 : ℂ) < ((Pi.single i 1 : ι → ℂ) + 1) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using add_pos (zero_lt_one' ℂ) (zero_lt_one' ℂ)
    · simp [hj]
  have h1 := ev_symm_of_nonneg ev _ (h _ hp) v w
  simp only [map_add (f := _), map_one, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right] at h1
  linear_combination h1

theorem algHom_apply_eq_sum (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V) (f : ι → ℂ) (v : V) :
    ev (K f v) = ∑ i, f i • ev (K (Pi.single i 1) v) := by
  have hf : f = ∑ i, f i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem ev_adj (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v w : V) :
    ⟪ev w, ev (K f v)⟫_ℂ = ⟪ev (K (fun i => star (f i)) w), ev v⟫_ℂ := by
  rw [algHom_apply_eq_sum, algHom_apply_eq_sum ev K (fun i => star (f i)), inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_left, ev_symm_single ev K h]
  simp

theorem ev_single_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v : V) :
    ‖ev (K (Pi.single i 1) v)‖ ≤ ‖ev v‖ := by
  have hid : K (Pi.single i 1) (K (Pi.single i 1) v) = K (Pi.single i 1) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
  have h1 := ev_symm_single ev K h i v (K (Pi.single i 1) v)
  rw [hid] at h1
  set a := ev (K (Pi.single i 1) v)
  have h2 : ‖a‖ * ‖a‖ ≤ ‖a‖ * ‖ev v‖ := by
    calc ‖a‖ * ‖a‖ = ‖⟪a, a⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖⟪a, ev v⟫_ℂ‖ := by rw [h1]
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h2 h0

theorem ev_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v : V) :
    ‖ev (K f v)‖ ≤ (∑ i, ‖f i‖) * ‖ev v‖ := by
  rw [algHom_apply_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ev_single_le ev K h i v) (norm_nonneg _)

end abstract

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem kappa_ptAdj_ptB : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN f
  classical
  let ev : (Fin P.r → ℂ) × Q.Mx P.k P.r →
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun x =>
    { toFun := fun Φ => B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : (M.Ty P → ℂ) →ₐ[ℂ] Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :=
    (P5.Kfp.fstAlg _).comp d.κ
  have hpos : ∀ x, ∀ g : M.Ty P → ℂ, (∀ i, 0 < g i) → ∀ v, 0 ≤ ⟪ev x v, ev x (K g v)⟫_ℂ := fun x g hg v =>
    P5.kappaFibrePos Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hD.1 X d hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 g hg v x.1 x.2
  refine ⟨fun Φ Ψ x _ => ?_, ∑ i, ‖f i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Φ x _ => ?_⟩
  · rw [hN.2.2.1.1 f]
    exact ev_adj (ev x) K (hpos x) f Φ Ψ
  · exact ev_le (ev x) K (hpos x) f Φ

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensorKFinite

variable {k r : ℕ} {ι : Type} [Fintype ι]

theorem smMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have h := hT.smul 0 0 R.smSub.zero_mem
  simpa using h

theorem kfin_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm)
    (hA : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, R'.σ g (T c y) = ∑ i, a i • T i (R.σ g y))
    (c : ι) (y : R.H) (hy : R.KFin y) : R'.KFin (T c y) := by
  obtain ⟨S, hfd, hyS, hst⟩ := hy
  have hsm : ∀ x ∈ S, x ∈ R.sm := fun x hx => hK x ⟨S, hfd, hx, hst⟩
  let L : ι → (S →ₗ[ℂ] R'.H) := fun i =>
    { toFun := fun x => T i x
      map_add' := fun x x' => (hT i).add _ (hsm _ x.2) _ (hsm _ x'.2)
      map_smul' := fun a x => (hT i).smul a _ (hsm _ x.2) }
  have hmem : ∀ i, ∀ x ∈ S, T i x ∈ ⨆ i, LinearMap.range (L i) := fun i x hx =>
    Submodule.mem_iSup_of_mem i ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⨆ i, LinearMap.range (L i), inferInstance, hmem c y hyS, fun g hg x hx => ?_⟩
  have hle : (⨆ i, LinearMap.range (L i)) ≤
      (⨆ i, LinearMap.range (L i)).comap (R'.σ g : R'.H →ₗ[ℂ] R'.H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hA g hg.1 i z (hsm _ z.2)
    have : R'.σ g (T i z) ∈ ⨆ i, LinearMap.range (L i) := by
      rw [ha]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j _ (hst g hg _ z.2))
    exact this
  exact hle hx

theorem tk_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm) (hTK : ∀ v ∈ R.TK, v ∈ R.sm)
    (hF : ∀ c y, R.KFin y → R'.KFin (T c y))
    (hB : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, T c (R.σ g y) = ∑ i, a i • R'.σ g (T i y))
    (c : ι) (y : R.H) (hy : y ∈ R.TK) : T c y ∈ R'.TK := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hB g hg c v (hK v hv)
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g, hg, _, hF j v hv, rfl⟩)
  | zero => rw [smMap_zero (hT c)]; exact Submodule.zero_mem _
  | add x x' hx hx' h1 h2 =>
    rw [(hT c).add _ (hTK _ hx) _ (hTK _ hx')]; exact Submodule.add_mem _ h1 h2
  | smul a x hx h1 =>
    rw [(hT c).smul a _ (hTK _ hx)]; exact Submodule.smul_mem _ _ h1

theorem inv_rows [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι ι ℂ) (h : A * B = 1)
    (u v : ι → V) (huv : ∀ i, u i = ∑ j, B i j • v j) (c : ι) : v c = ∑ i, A c i • u i := by
  simp_rw [huv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]
  simp

end GlobalTheory.TensorKFinite


open GlobalTheory.TensorKFinite in
theorem GlobalTheory.tensor_decomposition_kfinite : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  intro hKS k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hRσ, hRT, -, hRK, -, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε mu R hR
  have hIT : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hIK : ∀ I, ∀ v, (RI I).KFin v → v ∈ (RI I).sm := fun I v hv =>
    hIT I v ((GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.2.2.1 v hv)
  have hRK' : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hRT v (hRK v hv)
  obtain ⟨-, -, h1, hmul, -⟩ := hF
  have hinv : ∀ g ∈ GG k r, ρ g⁻¹ * ρ g = 1 ∧ ρ g * ρ g⁻¹ = 1 := fun g hg => by
    obtain ⟨a, b, c⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    exact ⟨by rw [← hmul _ a _ hg, c, h1], by rw [← hmul _ hg _ a, b, h1]⟩
  have ioB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      io I c ((RI I).σ g y) = ∑ i, ρ g c i • R.σ g (io I i y) := fun I g hg c y hy =>
    congrFun (hT.io_eq I g hg y hy) c
  have ioA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      R.σ g (io I c y) = ∑ i, ρ g⁻¹ c i • io I i ((RI I).σ g y) := fun I g hg c y hy =>
    inv_rows _ _ (hinv g hg).1 (fun i => io I i ((RI I).σ g y)) (fun i => R.σ g (io I i y))
      (fun i => ioB I g hg i y hy) c
  have prA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      (RI I).σ g (pr I c x) = ∑ i, (ρ g)ᵀ c i • pr I i (R.σ g x) := fun I g hg c x hx => by
    have hs : ∀ e, (Pi.single c x : ι → R.H) e ∈ R.sm := fun e => by
      by_cases he : e = c
      · subst he; simpa using hx
      · rw [Pi.single_eq_of_ne he]; exact R.smSub.zero_mem
    have h := hT.pr_eq I g hg (Pi.single c x) hs
    have e1 : ∑ e, pr I e ((Pi.single c x : ι → R.H) e) = pr I c x := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        rw [Pi.single_eq_of_ne he, smMap_zero (hT.pr_sm I e)]
      · simp
    have e2 : ∀ i, act ρ R g (Pi.single c x) i = ρ g i c • R.σ g x := fun i => by
      unfold act
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [Pi.single_eq_of_ne he]
      · simp
    rw [e1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, (hT.pr_sm I i).smul _ _ (hRσ g hg x hx), Matrix.transpose_apply]
  have prB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      pr I c (R.σ g x) = ∑ i, (ρ g⁻¹)ᵀ c i • (RI I).σ g (pr I i x) := fun I g hg c x hx =>
    inv_rows _ _ (by rw [← Matrix.transpose_mul, (hinv g hg).2, Matrix.transpose_one])
      (fun i => (RI I).σ g (pr I i x)) (fun i => pr I i (R.σ g x)) (fun i => prA I g hg i x hx) c
  have K1 : ∀ I c y, (RI I).KFin y → R.KFin (io I c y) := fun I =>
    kfin_of_family (io I) (hT.io_sm I) (hIK I) fun g hg c y hy => ⟨_, ioA I g hg c y hy⟩
  have K2 : ∀ I c x, R.KFin x → (RI I).KFin (pr I c x) := fun I =>
    kfin_of_family (pr I) (hT.pr_sm I) hRK' fun g hg c y hy => ⟨_, prA I g hg c y hy⟩
  exact ⟨K1, K2,
    fun I => tk_of_family (io I) (hT.io_sm I) (hIK I) (hIT I) (K1 I) fun g hg c y hy => ⟨_, ioB I g hg c y hy⟩,
    fun I => tk_of_family (pr I) (hT.pr_sm I) hRK' hRT (K2 I) fun g hg c y hy => ⟨_, prB I g hg c y hy⟩⟩
end
end

