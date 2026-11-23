module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointIntertwinerDiscreteSeriesDescends
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
open Matrix

namespace GlobalTheory.AdjDescent

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_conjTranspose]

theorem conjR_conjTranspose_mul {p q : ℕ} (Z : Mat p q) : (conjR Z)ᴴ * Jm p q = -(Jm p q * Z) := by
  unfold conjR adjZ
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, jm_conjTranspose, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, jm_mul_jm, Matrix.mul_one]

theorem mul_conjR {p q : ℕ} (Z : Mat p q) : Jm p q * conjR Z = -(Zᴴ * Jm p q) := by
  unfold conjR adjZ
  rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jm_mul_jm, Matrix.one_mul]

theorem re_mem_upq {p q : ℕ} (Z : Mat p q) : Z + conjR Z ∈ upq p q := by
  show (Z + conjR Z)ᴴ * Jm p q + Jm p q * (Z + conjR Z) = 0
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, conjR_conjTranspose_mul, mul_conjR]
  abel

theorem im_mem_upq {p q : ℕ} (Z : Mat p q) : Complex.I • (Z - conjR Z) ∈ upq p q := by
  show (Complex.I • (Z - conjR Z))ᴴ * Jm p q + Jm p q * (Complex.I • (Z - conjR Z)) = 0
  have hI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  rw [Matrix.conjTranspose_smul, hI, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, conjR_conjTranspose_mul, mul_conjR]
  simp only [neg_smul, sub_neg_eq_add, smul_add]
  abel

theorem decomp {p q : ℕ} (Z : Mat p q) :
    Z = (1 / 2 : ℂ) • (Z + conjR Z) + (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) := by
  have h : (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) = (1 / 2 : ℂ) • (Z - conjR Z) := by
    rw [smul_smul]
    congr 1
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  rw [h, ← smul_add, show Z + conjR Z + (Z - conjR Z) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

theorem inner_apply_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (H →L[ℂ] H)) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : H) :
    inner ℂ x (ρ g y) = inner ℂ (ρ g⁻¹ x) y := by
  have e : ρ g * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv : ρ g (ρ g⁻¹ x) = x := by
    calc ρ g (ρ g⁻¹ x) = (ρ g * ρ g⁻¹) x := rfl
      _ = x := by rw [e]; rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ g : H →ₗ[ℂ] H), h g⟩
  calc inner ℂ x (ρ g y) = inner ℂ (L (ρ g⁻¹ x)) (L y) := by
        show inner ℂ x (ρ g y) = inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y)
        rw [hinv]
    _ = inner ℂ (ρ g⁻¹ x) y := L.inner_map_map _ _

private theorem kFin_map_of_intertwining {p q : ℕ} (T : GrpData p q) {E F : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (πE : T.G → (E →L[ℂ] E)) (πF : T.G → (F →L[ℂ] F)) (L : E →L[ℂ] F)
    (hL : ∀ g x, L (πE g x) = πF g (L x)) (x : E) (hx : KFin T πE x) : KFin T πF (L x) := by
  unfold KFin at hx ⊢
  have key : ∀ (κ : Type) (c : κ → T.G),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πE (c k) x)) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πF (c k) (L x))) := by
    intro κ c hc
    have e : (Set.range fun k => πF (c k) (L x)) =
        (L : E →ₗ[ℂ] F) '' Set.range (fun k => πE (c k) x) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      simp [hL]
    rw [e, Submodule.span_image]
    haveI := hc
    infer_instance
  exact key _ _ hx

theorem adjoint_descends : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : T.G →* (H →L[ℂ] H)), (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ S : D.U.H →L[ℂ] H, (∀ g x, ρ g (S x) = S (D.U.π g x)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : V →ₗ[ℂ] H) (act : Mat p q →ₗ[ℂ] Module.End ℂ V), (∀ P, KFin T (fun g => ρ g) (ι P)) → (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => ρ (T.expt (t • Y)) (ι P)) (ι (act Y P)) 0) → ∃ φ : V →ₗ[ℂ] D.HK.V, (∀ P x, inner ℂ x (D.ι (φ P)) = inner ℂ (S x) (ι P)) ∧ ∀ Z P, φ (act Z P) = D.HK.act Z (φ P) := by
  intro p q T D H _ _ _ ρ hρ S hS V _ _ ι act hK hD

  have hA : ∀ g y, ContinuousLinearMap.adjoint S (ρ g y) =
      D.U.π g (ContinuousLinearMap.adjoint S y) := by
    intro g y
    apply ext_inner_left ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_right, inner_apply_of_norm ρ hρ, hS,
      ← ContinuousLinearMap.adjoint_inner_right S, inner_apply_of_norm D.U.π D.U.isom]

  have hmem : ∀ P, ∃ w, D.ι w = ContinuousLinearMap.adjoint S (ι P) := fun P =>
    (D.ι_range _).2 (kFin_map_of_intertwining T (fun g => ρ g) (fun g => D.U.π g) _ hA (ι P) (hK P))
  choose f hf using hmem
  have hinj := D.ι_inj
  let φ : V →ₗ[ℂ] D.HK.V :=
    { toFun := f
      map_add' := fun P Q => hinj (by simp only [map_add (f := _), hf])
      map_smul' := fun c P => hinj (by simp only [RingHom.id_apply, map_smul, hf]) }
  have hφ : ∀ P, D.ι (φ P) = ContinuousLinearMap.adjoint S (ι P) := hf

  have hY : ∀ Y ∈ upq p q, ∀ P, φ (act Y P) = D.HK.act Y (φ P) := by
    intro Y hYm P
    apply hinj
    rw [hφ]
    have h1 : HasDerivAt (fun t : ℝ => D.U.π (T.expt (t • Y)) (D.ι (φ P)))
        (ContinuousLinearMap.adjoint S (ι (act Y P))) 0 := by
      have h0 := ((ContinuousLinearMap.adjoint S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hD Y hYm P)
      convert h0 using 1
      all_goals first
        | rfl
        | (funext t; simp [hA, hφ])
    exact h1.unique (D.der Y hYm (φ P))
  refine ⟨φ, fun P x => ?_, fun Z P => ?_⟩
  · rw [hφ, ContinuousLinearMap.adjoint_inner_right]
  · have hre := re_mem_upq Z
    have him := im_mem_upq Z
    rw [decomp Z]
    generalize Z + conjR Z = A at hre ⊢
    generalize Complex.I • (Z - conjR Z) = B at him ⊢
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hY A hre, hY B him]

end GlobalTheory.AdjDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

open Filter Topology

namespace GlobalTheory.OrbitAnalytic

theorem hasDerivAt_orbit {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (hU : ∀ s t, U (s + t) = U s * U t) (v v' : H)
    (h : HasDerivAt (fun t : ℝ => U t v) v' 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => U t v) (U t v') t := by
  have h0 : HasDerivAt (fun s : ℝ => U t (U s v)) (U t v') (t - t) := by
    rw [sub_self]
    exact ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine (h0.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  show U x v = U t (U (x - t) v)
  rw [← ContinuousLinearMap.mul_apply, ← hU]
  congr 2
  ring

private lemma hasDerivAt_sum_pow_div_factorial_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℕ → E) (N : ℕ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range (N + 1), (x ^ k / (k.factorial : ℝ)) • c k)
      (∑ k ∈ Finset.range N, (s ^ k / (k.factorial : ℝ)) • c (k + 1)) s := by
  induction N with
  | zero => simpa using hasDerivAt_const s (c 0)
  | succ n ih =>
    have hterm : HasDerivAt (fun x : ℝ => (x ^ (n + 1) / ((n + 1).factorial : ℝ)) • c (n + 1))
        ((s ^ n / (n.factorial : ℝ)) • c (n + 1)) s := by
      have h := ((hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ)).smul_const (c (n + 1))
      convert h using 2
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    have e : (fun x : ℝ => ∑ k ∈ Finset.range (n + 1 + 1), (x ^ k / (k.factorial : ℝ)) • c k) =
        fun x => (∑ k ∈ Finset.range (n + 1), (x ^ k / (k.factorial : ℝ)) • c k) +
          (x ^ (n + 1) / ((n + 1).factorial : ℝ)) • c (n + 1) := by
      funext x
      exact Finset.sum_range_succ _ _
    rw [e]
    exact (ih.add hterm).congr_deriv (Finset.sum_range_succ _ _).symm

private lemma norm_sub_taylor_sum_le_of_hasDerivAt_tower {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (M a : ℝ)
    (N : ℕ) : ∀ (f : ℕ → ℝ → E), (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) →
      (∀ t, ‖f N t‖ ≤ M) → ∀ z : ℝ, 0 ≤ z →
      ‖f 0 (a + z) - ∑ k ∈ Finset.range N, (z ^ k / (k.factorial : ℝ)) • f k a‖
        ≤ z ^ N / (N.factorial : ℝ) * M := by
  induction N with
  | zero =>
    intro f _ hM z _
    simpa using hM (a + z)
  | succ n ih =>
    intro f hf hM z hz
    have hder : ∀ s, HasDerivAt
        (fun s : ℝ => f 0 (a + s) - ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • f k a)
        (f 1 (a + s) - ∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • f (k + 1) a) s := by
      intro s
      exact ((hf 0 (a + s)).comp_const_add a s).sub (hasDerivAt_sum_pow_div_factorial_smul (fun k => f k a) n s)
    have hB : ∀ s, HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n + 1).factorial : ℝ) * M)
        (s ^ n / (n.factorial : ℝ) * M) s := by
      intro s
      refine (((hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ)).mul_const M).congr_deriv ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    have ha0 : ‖(fun s : ℝ => f 0 (a + s) -
          ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • f k a) 0‖ ≤
        (fun x : ℝ => x ^ (n + 1) / ((n + 1).factorial : ℝ) * M) 0 := by
      simp [Finset.sum_range_succ']
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) z,
        ‖f 1 (a + s) - ∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • f (k + 1) a‖ ≤
          s ^ n / (n.factorial : ℝ) * M := fun s hs =>
      ih (fun k => f (k + 1)) (fun k t => hf (k + 1) t) hM s hs.1
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun s _ => (hder s).continuousAt.continuousWithinAt)
      (fun s _ => (hder s).hasDerivWithinAt) ha0 hB hbound
    exact key ⟨hz, le_rfl⟩

theorem taylor_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ → E) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (a z : ℝ) (N : ℕ) (M : ℝ)
    (hM : ∀ t, ‖f (N + 1) t‖ ≤ M) :
    ‖f 0 (a + z) - ∑ k ∈ Finset.range (N + 1), (z ^ k / (k.factorial : ℝ)) • f k a‖
      ≤ |z| ^ (N + 1) / (N.factorial : ℝ) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfac : (0 : ℝ) < N.factorial := by positivity
  have hfac' : (N.factorial : ℝ) ≤ (N + 1).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ N)
  rcases le_or_gt 0 z with hz | hz
  · have h := norm_sub_taylor_sum_le_of_hasDerivAt_tower M a (N + 1) f hf hM z hz
    rw [abs_of_nonneg hz]
    exact h.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (pow_nonneg hz _) hfac hfac') hM0)
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → E, ∀ k t, g k t = ((-1 : ℝ) ^ k) • f k (-t) :=
      ⟨fun k t => ((-1 : ℝ) ^ k) • f k (-t), fun _ _ => rfl⟩
    have hgd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t := by
      intro k t
      have h1 := (hf k (0 - t)).comp_const_sub 0 t
      simp only [zero_sub] at h1
      have h2 := h1.const_smul ((-1 : ℝ) ^ k)
      have hgk : g k = fun x => ((-1 : ℝ) ^ k) • f k (-x) := funext (hg k)
      rw [hgk, hg]
      exact h2.congr_deriv (by rw [pow_succ, mul_smul, neg_one_smul])
    have hgM : ∀ t, ‖g (N + 1) t‖ ≤ M := by
      intro t
      simpa [hg, norm_smul] using hM (-t)
    have h := norm_sub_taylor_sum_le_of_hasDerivAt_tower M (-a) (N + 1) g hgd hgM (-z) (by linarith)
    have e1 : g 0 (-a + -z) = f 0 (a + z) := by
      rw [hg]
      simp only [pow_zero, one_smul, neg_add, neg_neg]
    have e2 : ∑ k ∈ Finset.range (N + 1), ((-z) ^ k / (k.factorial : ℝ)) • g k (-a) =
        ∑ k ∈ Finset.range (N + 1), (z ^ k / (k.factorial : ℝ)) • f k a := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hg, neg_neg, smul_smul]
      congr 1
      rw [neg_pow]
      have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc (-1) ^ k * z ^ k / (k.factorial : ℝ) * (-1) ^ k
          = ((-1) ^ k * (-1) ^ k) * (z ^ k / (k.factorial : ℝ)) := by ring
        _ = z ^ k / (k.factorial : ℝ) := by rw [h1, one_mul]
    rw [e1, e2] at h
    rw [abs_of_neg hz]
    exact h.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (pow_nonneg (by linarith) _) hfac hfac') hM0)

theorem analyticAt_of_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℕ → ℝ → E) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (C r : ℝ) (hr : 0 < r)
    (hM : ∀ k t, ‖f k t‖ ≤ C * (k.factorial : ℝ) / r ^ k) (a : ℝ) :
    AnalyticAt ℝ (f 0) a := by
  obtain ⟨p, hp⟩ : ∃ p : FormalMultilinearSeries ℝ ℝ E, ∀ k,
      p k = ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (((k.factorial : ℝ)⁻¹) • f k a) :=
    ⟨fun k => ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (((k.factorial : ℝ)⁻¹) • f k a),
      fun _ => rfl⟩
  have happly : ∀ k (y : ℝ), p k (fun _ => y) = (y ^ k / (k.factorial : ℝ)) • f k a := by
    intro k y
    rw [hp, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_smul, div_eq_mul_inv]
  have hnorm : ∀ k, ‖p k‖ = (k.factorial : ℝ)⁻¹ * ‖f k a‖ := by
    intro k
    rw [hp, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, norm_inv,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hbd : ∀ k, ‖p k‖ * r ^ k ≤ C := by
    intro k
    have hrk : 0 < r ^ k := pow_pos hr k
    have hk : (0 : ℝ) < k.factorial := by positivity
    rw [hnorm]
    calc (k.factorial : ℝ)⁻¹ * ‖f k a‖ * r ^ k
        ≤ (k.factorial : ℝ)⁻¹ * (C * (k.factorial : ℝ) / r ^ k) * r ^ k := by
          gcongr
          exact hM k a
      _ = C := by field_simp
  have hrad : ENNReal.ofReal r ≤ p.radius :=
    p.le_radius_of_bound C (r := r.toNNReal) fun k => by
      rw [Real.coe_toNNReal _ hr.le]
      exact hbd k
  refine ⟨p, ENNReal.ofReal r, hrad, ENNReal.ofReal_pos.mpr hr, ?_⟩
  intro y hy
  rw [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
  have hq0 : 0 ≤ |y| / r := by positivity
  have hq1 : |y| / r < 1 := (div_lt_one hr).mpr hy
  have hterm : ∀ n, ‖p n (fun _ => y)‖ ≤ C * (|y| / r) ^ n := by
    intro n
    calc ‖p n (fun _ => y)‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := (p n).le_opNorm _
      _ = ‖p n‖ * r ^ n * (|y| / r) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.norm_eq_abs, div_pow]
          field_simp
      _ ≤ C * (|y| / r) ^ n := by
          gcongr
          exact hbd n
  have hsum : Summable (fun n => ‖p n (fun _ => y)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsum, ← tendsto_add_atTop_iff_nat 1]
  simp only [happly]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun N : ℕ => C * (((N + 1 : ℕ) : ℝ) * (|y| / r) ^ (N + 1)))
    (fun _ => norm_nonneg _) (fun N => ?_) ?_
  · rw [norm_sub_rev]
    calc _ ≤ |y| ^ (N + 1) / (N.factorial : ℝ) *
          (C * ((N + 1).factorial : ℝ) / r ^ (N + 1)) :=
          taylor_bound f hf a y N _ (fun t => hM (N + 1) t)
      _ = C * (((N + 1 : ℕ) : ℝ) * (|y| / r) ^ (N + 1)) := by
          rw [Nat.factorial_succ, div_pow]
          push_cast
          field_simp
  · have := ((tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp
      (tendsto_add_atTop_nat 1)).const_mul C
    simpa using this

theorem bound_of_analyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℕ → ℝ → E) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (a : ℝ)
    (h : AnalyticAt ℝ (f 0) a) :
    ∃ C r : ℝ, 0 < r ∧ ∀ k, ‖f k a‖ ≤ C * (k.factorial : ℝ) / r ^ k := by
  obtain ⟨p, ρ, hp⟩ := h
  have hiter : ∀ k, iteratedDeriv k (f 0) = f k := by
    intro k
    induction k with
    | zero => exact iteratedDeriv_zero
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hf k t).deriv
  have hval : ∀ k, f k a = k.factorial • p k (fun _ => (1 : ℝ)) := by
    intro k
    rw [hp.factorial_smul 1 k, ← iteratedDeriv_eq_iteratedFDeriv, hiter]
  obtain ⟨r', hr'0, hr'ρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  obtain ⟨C, -, hCb⟩ := p.norm_mul_pow_le_of_lt_radius (hr'ρ.trans_le hp.r_le)
  have hr'pos : (0 : ℝ) < r' := by exact_mod_cast hr'0
  refine ⟨C, r', hr'pos, fun k => ?_⟩
  have hpos : (0 : ℝ) < (r' : ℝ) ^ k := pow_pos hr'pos k
  calc ‖f k a‖ = ‖k.factorial • p k (fun _ => (1 : ℝ))‖ := by rw [← hval k]
    _ ≤ k.factorial * ‖p k (fun _ => (1 : ℝ))‖ := norm_nsmul_le
    _ ≤ k.factorial * ‖p k‖ := by
        gcongr
        simpa using (p k).le_opNorm (fun _ => (1 : ℝ))
    _ ≤ k.factorial * (C / (r' : ℝ) ^ k) := by
        gcongr
        rw [le_div_iff₀ hpos]
        exact hCb k
    _ = C * (k.factorial : ℝ) / (r' : ℝ) ^ k := by ring

theorem analyticOnNhd_orbit_of_norm_eq : ∀ (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂), (∀ s t, U₁ (s + t) = U₁ s * U₁ t) → (∀ s t, U₂ (s + t) = U₂ s * U₂ t) → U₁ 0 = 1 → U₂ 0 = 1 → (∀ t x, ‖U₂ t x‖ = ‖x‖) → ∀ (w₁ : ℕ → H₁) (w₂ : ℕ → H₂), (∀ k, HasDerivAt (fun t : ℝ => U₁ t (w₁ k)) (w₁ (k + 1)) 0) → (∀ k, HasDerivAt (fun t : ℝ => U₂ t (w₂ k)) (w₂ (k + 1)) 0) → (∀ k, ‖w₁ k‖ = ‖w₂ k‖) → AnalyticAt ℝ (fun t : ℝ => U₁ t (w₁ 0)) 0 → AnalyticOnNhd ℝ (fun t : ℝ => U₂ t (w₂ 0)) Set.univ := by
  intro H₁ _ _ _ H₂ _ _ _ U₁ U₂ hU₁ hU₂ h01 _ hiso w₁ w₂ hd₁ hd₂ hw han
  have hF₁ : ∀ k t, HasDerivAt (fun s : ℝ => U₁ s (w₁ k)) (U₁ t (w₁ (k + 1))) t :=
    fun k t => hasDerivAt_orbit U₁ hU₁ (w₁ k) (w₁ (k + 1)) (hd₁ k) t
  have hF₂ : ∀ k t, HasDerivAt (fun s : ℝ => U₂ s (w₂ k)) (U₂ t (w₂ (k + 1))) t :=
    fun k t => hasDerivAt_orbit U₂ hU₂ (w₂ k) (w₂ (k + 1)) (hd₂ k) t
  obtain ⟨C, r, hr, hCr⟩ := bound_of_analyticAt (fun k t => U₁ t (w₁ k)) hF₁ 0 han
  intro a _
  refine analyticAt_of_bound (fun k t => U₂ t (w₂ k)) hF₂ C r hr (fun k t => ?_) a
  have h1 := hCr k
  simp only [h01, ContinuousLinearMap.one_apply] at h1
  simp only [hiso]
  rw [← hw k]
  exact h1

end GlobalTheory.OrbitAnalytic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasimirNumberIdentityDualPair
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.CasimirNumber

def sqSum (l : List ℚ) : ℚ := (l.map fun x => x ^ 2).sum

theorem sqSum_append (l₁ l₂ : List ℚ) : sqSum (l₁ ++ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold sqSum
  rw [List.map_append, List.sum_append]

theorem sum_range_getD_sq (l : List ℚ) :
    ∑ i ∈ Finset.range l.length, (l.getD i 0) ^ 2 = sqSum l := by
  induction l with
  | nil => simp [sqSum]
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    unfold sqSum
    simp only [List.map_cons, List.sum_cons]
    ring

theorem sum_fin_getD_sq (l : List ℚ) (p : ℕ) (h : l.length = p) :
    ∑ i : Fin p, (l.getD i 0) ^ 2 = sqSum l := by
  subst h
  rw [Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0) ^ 2)]
  exact sum_range_getD_sq l

theorem normSq_ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    normSq (ofBlocks (p := p) (q := q) l₁ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold normSq ofBlocks
  rw [Fintype.sum_sum_type]
  simp only
  rw [sum_fin_getD_sq l₁ p h₁, sum_fin_getD_sq l₂ q h₂]

theorem sum_range_sub_sq (c : ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (c - (i : ℚ)) ^ 2 =
      n * c ^ 2 - c * (n * (n - 1)) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem rhoSq_eq (n : ℕ) : rhoSq n = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  unfold rhoSq
  rw [sum_range_sub_sq]
  ring

theorem length_block (t : ℕ) : (Formalism.BasicNotions.TH.block t).length = t := by
  unfold Formalism.BasicNotions.TH.block
  simp

theorem sqSum_map_range (f : ℕ → ℚ) (n : ℕ) :
    sqSum ((List.range n).map f) = ∑ i ∈ Finset.range n, f i ^ 2 := by
  induction n with
  | zero => simp [sqSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sqSum_append, ih, Finset.sum_range_succ]
    simp [sqSum]

theorem sqSum_block (t : ℕ) : sqSum (Formalism.BasicNotions.TH.block t) = rhoSq t := by
  have hb : Formalism.BasicNotions.TH.block t = (List.range t).map (fun m : ℕ => ((t : ℚ) - 1) / 2 - m) := by
    have hf : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(Nat.cast a : ℚ)]) l = List.map (fun a : ℕ => (Nat.cast a : ℚ)) l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_cons, ih]
    unfold Formalism.BasicNotions.TH.block
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [hf, List.map_map]
    rfl
  rw [hb, sqSum_map_range]
  unfold rhoSq
  rfl

theorem normSq_lamA (al be ga de : List ℚ) :
    normSq (lamA al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de := by
  unfold lamA
  rw [normSq_ofBlocks _ _ (by simp) (by simp), sqSum_append, sqSum_append]
  ring

theorem normSq_lamA' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamA' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamA'
  rw [normSq_ofBlocks _ _ (by simp [length_block] <;> omega) (by simp <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem normSq_lamM' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamM' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamM'
  rw [normSq_ofBlocks _ _ (by simp <;> omega) (by simp [length_block] <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem casimir_number_identity : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  intro t al be ga de _
  refine ⟨?_, by rw [normSq_lamM', normSq_lamA']⟩
  rw [normSq_lamA', normSq_lamA, rhoSq_eq, rhoSq_eq, rhoSq_eq]
  push_cast
  ring

end GlobalTheory.CasimirNumber
end

