module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinors

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
section
open Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

def den (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g 0 0 + g 0 1 * a

def mob (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := (g 1 0 + g 1 1 * a) / den g a

def mobD (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g.det / den g a ^ 2

def mob1 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cons (mob (g (Fin.tail z)) (z 0)) (Fin.tail z)

def mob2 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 2) → ℂ) : Fin (d + 2) → ℂ :=
  Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 0))
    (Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 1)) (Fin.tail (Fin.tail z)))

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry {d : ℕ} (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (p q : Fin 2) :
    ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y := by
  have hg' : ∀ i j, ContDiffAt ℝ 2 (fun y' => g y' i j) y := fun i j =>
    ((ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg i j).differentiableOn y (Set.mem_univ _)).contDiffAt).restrict_scalars ℝ
  have hs : ∀ i j, ContDiffAt ℝ 2 (fun y' => star (g y' i j)) y := fun i j => by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp y (hg' i j)
    simpa [Function.comp_def] using h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  exact ((((hs 0 p).mul (hC 0 0)).add ((hs 1 p).mul (hC 1 0))).mul (hg' 0 q)).add
    ((((hs 0 p).mul (hC 0 1)).add ((hs 1 p).mul (hC 1 1))).mul (hg' 1 q))

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_xiPot {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → Matrix (Fin 2) (Fin 2) ℂ) (b : E → ℂ) (w₀ : E) (hpd : (H w₀).PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun w => H w p q) w₀) (hb : ContDiffAt ℝ 2 b w₀) :
    ContDiffAt ℝ 2 (fun w => xiPot (H w) (b w)) w₀ := by
  have hb' : ContDiffAt ℝ 2 (fun w => star (b w)) w₀ := by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp w₀ hb
    simpa [Function.comp_def] using h
  have h00 := hC 0 0
  have h01 := hC 0 1
  have h10 := hC 1 0
  have h11 := hC 1 1
  have hq : ContDiffAt ℝ 2 (fun w => herm2 (H w) ![1, b w] ![1, b w]) w₀ := by
    simp only [herm2, dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_one, one_mul, mul_one]
    fun_prop
  have hd : ContDiffAt ℝ 2 (fun w => (H w).det) w₀ := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hqr : ContDiffAt ℝ 2 (fun w => (herm2 (H w) ![1, b w] ![1, b w]).re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hq
  have hdr : ContDiffAt ℝ 2 (fun w => (H w).det.re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hd
  have hv : (![1, b w₀] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hp1 : 0 < herm2 (H w₀) ![1, b w₀] ![1, b w₀] := by
    exact hpd.dotProduct_mulVec_pos hv
  have hp2 : 0 < (H w₀).det := hpd.det_pos
  simp only [xiPot]
  exact (hqr.log (Complex.pos_iff.1 hp1).1.ne').neg.add (contDiffAt_const.mul (hdr.log (Complex.pos_iff.1 hp2).1.ne'))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConstAddEquivOfRangeEq
section
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_const_addEquiv_of_range_eq : ∀ (n g : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Countable Λ] [AddCommGroup Λ'] [Countable Λ'] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (P' : (Fin n → ℂ) → (Λ' →+ (Fin g → ℂ))), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ x, DifferentiableOn ℂ (fun b => P' b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ Function.Injective (P' b) ∧ (P b).range = (P' b).range) → ∃ T : Λ' ≃+ Λ, ∀ b ∈ B, ∀ x, P' b x = P b (T x) := by
  intro n g Λ Λ' _ _ _ _ B hB hc hne P P' hP hP' h
  have h1 : ∀ x : Λ', ∃ y : Λ, ∀ b ∈ B, P' b x = P b y := fun x =>
    exists_const_of_section_mem_range n g Λ B hB hc hne P (fun b => P' b x) hP (hP' x)
      (fun b hb => by rw [(h b hb).2.2]; exact ⟨x, rfl⟩)
  have h2 : ∀ y : Λ, ∃ x : Λ', ∀ b ∈ B, P b y = P' b x := fun y =>
    exists_const_of_section_mem_range n g Λ' B hB hc hne P' (fun b => P b y) hP' (hP y)
      (fun b hb => by rw [← (h b hb).2.2]; exact ⟨y, rfl⟩)
  choose f hf using h1
  choose k hk using h2
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨hi, hi', -⟩ := h b₀ hb₀
  refine ⟨{ toFun := f, invFun := k, left_inv := ?_, right_inv := ?_, map_add' := ?_ }, ?_⟩
  · intro x
    apply hi'
    rw [← hk _ b₀ hb₀, ← hf _ b₀ hb₀]
  · intro y
    apply hi
    rw [← hf _ b₀ hb₀, ← hk _ b₀ hb₀]
  · intro x x'
    apply hi
    rw [map_add (f := _), ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, map_add (f := _)]
  · intro b hb x
    exact hf x b hb

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNext
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_toWtS_homogeneous_coeff_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) :=
  @PositivityTheory.Xgp.t_poly_towt_bound

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix Topology
open scoped ComplexOrder

theorem posDef_eventually_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (A : X → Matrix n n ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := isCompact_sphere 0 1
  have hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    simp only [dotProduct, mulVec]
    refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetSum _ fun j _ =>
        ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y),
      0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp [hKdef] at hy
    have h := h0.dotProduct_mulVec_pos hy0
    rw [Complex.lt_def] at h
    exact (hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K := by
    simp [hKdef, norm_smul, hn.ne']
  have h1 := hx _ hyK
  have e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y)) := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := (hH x).apply i j
    rw [Complex.star_def] at h
    rw [h]; ring
  rw [Complex.lt_def]
  refine ⟨?_, by simpa using him.symm⟩
  have := pos_of_mul_pos_right h1 (by positivity)
  simpa using this

theorem gramOf_isHermitian {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply, h, Ne.symm h]

theorem continuous_gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) :
    Continuous fun g : Matrix (Fin N) (Fin N) ℂ => gramHead hd k g := by
  unfold gramHead gramOf
  exact (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id).matrix_submatrix _ _

theorem isOpen_inFlagDomain (N j : ℕ) :
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} := by
  have h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef} := by
    refine isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_
    refine posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_)
      (fun g => ?_) g0 hg0
    · exact ((continuous_gramHead _ _).neg).matrix_elem a b
    · exact ((gramOf_isHermitian _ g).submatrix _).neg
  exact h1.inter h2

theorem gramOf_mul_of_preserves {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ)
    (hu : gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ))) :
    gramOf hd (u * g) = gramOf hd g := by
  unfold gramOf at hu ⊢
  rw [conjTranspose_mul]
  calc gᴴ * uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * (u * g)
      = gᴴ * (uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * u) * g := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem gramHead_of_triangular {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (b : Matrix (Fin N) (Fin N) ℂ)
    (hb : b.BlockTriangular id) :
    gramHead hd k b = (b.submatrix Subtype.val Subtype.val)ᴴ *
      diagonal (fun a : {a : Fin N // (a : ℕ) < k} => ((hd a : ℝ) : ℂ)) *
      b.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [gramHead, gramOf, submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, submatrix_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp)
    (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]
  rw [Finset.sum_filter_of_ne]
  intro l _ hl
  by_contra hlk
  apply hl
  have : b l i.1 = 0 := hb (by
    show i.1 < l
    have := i.2
    exact Fin.lt_def.2 (by omega))
  simp [this]

theorem sigForm_apply_ne_zero (N j : ℕ) (a : Fin N) : sigForm N j a ≠ 0 := by
  unfold sigForm; split_ifs <;> norm_num

theorem gramHead_det_ne_zero_of_triangular {N : ℕ} (hd : Fin N → ℝ) (hd0 : ∀ a, hd a ≠ 0) (k : ℕ)
    (b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
    (gramHead hd k b).det ≠ 0 := by
  have hbd : ∀ i, b i i ≠ 0 := by
    have h := (isUnit_iff_ne_zero.1 hu)
    rw [det_of_upperTriangular hb] at h
    exact fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0 := by
    have ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id :=
      fun i j hij => hb hij
    rw [det_of_upperTriangular ht]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1
  rw [gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]
  refine mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs
  exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)

theorem gramHead_det_ne_zero (N j : ℕ) (hj : j ≤ N) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : InFlagDomain N j g) (k : ℕ) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbu, hug⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag N j hj g hg
  have e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b := by
    unfold gramHead
    rw [← hug, gramOf_mul_of_preserves _ _ _ hu]
  rw [e]
  exact gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu

theorem flagDomain_open_and_minors : ∀ (N j : ℕ), j ≤ N →
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧
      ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k,
        (gramHead (sigForm N j) k g).det ≠ 0 :=
  fun N j hj => ⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransform
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_logDet_fderiv_norm_le : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a :=
  @PositivityTheory.Xgp.t_gram_grad

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightMapAntisymmetricDeltaIdentity
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_eq_C_mul_antisymDelta :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ),
      (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) →
      toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) :=
  @PositivityTheory.Xgp.t_poly_delta

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBound
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem normal_holomorphic_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 :=
  PositivityTheory.Xgp.projective_line_normal_frame

end GlobalTheory.CompanionTheory.Ar.PB
end

