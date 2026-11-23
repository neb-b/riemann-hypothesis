module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace GramContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem det_gram_le_prod {α : Type*} [Fintype α] [DecidableEq α] (y : α → V) :
    (Matrix.gram ℝ y).det ≤ ∏ a, ‖y a‖ ^ 2 := by
  by_cases hy : LinearIndependent ℝ y
  · let e := Fintype.equivFin α
    have h := HadamardGramBound.det_gram_le_prod_norm_sq (y ∘ e.symm) (hy.comp _ e.symm.injective)
    have hg : Matrix.gram ℝ (y ∘ e.symm) = (Matrix.gram ℝ y).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.gram_apply]
    rw [hg, Matrix.det_submatrix_equiv_self] at h
    rwa [Fintype.prod_equiv e.symm (fun i => ‖(y ∘ e.symm) i‖ ^ 2) (fun a => ‖y a‖ ^ 2) (fun _ => rfl)] at h
  · have h0 : (Matrix.gram ℝ y).det = 0 := by
      by_contra h; exact hy (Matrix.det_gram_ne_zero_iff_linearIndependent.mp h)
    rw [h0]; exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem gram_comb {α : Type*} [Fintype α] (M : Matrix α α ℝ) (y : α → V) :
    Matrix.gram ℝ (fun a => ∑ b, M a b • y b) = M * Matrix.gram ℝ y * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GramContraction

theorem GramContraction.proof : GramContraction.Statement := by
  intro ι κ _ _ _ _ V _ _ Ψ u w hΨ
  let e := EuclideanSpace.basisFun ι ℝ
  let U : Matrix ι ι ℝ := Matrix.of fun i j => u i j
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks U 0 0 1
  let y : ι ⊕ κ → V := Sum.elim (fun i => Ψ (e i)) w
  have hu : ∀ i, Ψ (u i) = ∑ j, U i j • Ψ (e j) := fun i => by
    conv_lhs => rw [← e.sum_repr (u i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [U, e, map_sum, map_smul]
  have hfam : Sum.elim (Ψ ∘ u) w = fun a => ∑ b, M a b • y b := by
    funext a
    rcases a with i | k
    · simp [Fintype.sum_sum_type, M, y, hu]
    · simp [Fintype.sum_sum_type, M, y, Matrix.one_apply]
  have hGu : Matrix.gram ℝ u = U * U.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp [Matrix.gram_apply, U, PiLp.inner_apply, mul_comm]
  have hdet : (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det = U.det ^ 2 * (Matrix.gram ℝ y).det := by
    rw [hfam, GramContraction.gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one]
    ring
  have hP : ∏ i, ‖Ψ (e i)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => sq_nonneg _) fun i _ => by
      have := hΨ (e i); rw [e.orthonormal.1 i] at this
      nlinarith [norm_nonneg (Ψ (e i))]
  have hW : 0 ≤ ∏ j, ‖w j‖ ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hH := GramContraction.det_gram_le_prod y
  rw [Fintype.prod_sum_type] at hH
  rw [hdet, hGu, Matrix.det_mul, Matrix.det_transpose, ← sq]
  refine mul_le_mul_of_nonneg_left (hH.trans ?_) (sq_nonneg _)
  simpa [y] using mul_le_of_le_one_left hW hP

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace HyperplaneQuotientBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem {b b' : K → ℤ} {s t : Ω} (hs : s ∈ chartLatQ y b 1) (ht : t ∈ chartLatQ y b' 1) :
    s * t ∈ chartLatQ y (b + b') 1 := by
  intro c hc
  have h := Subalgebra.mul_mem _ (hs c hc) (ht c hc)
  have heq : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + b') k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact h


omit [∀ k, Fintype (ι k)] in
theorem pow_mem {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1) (n : ℕ) :
    σ ^ n ∈ chartLatQ y ((n : ℤ) • e) 1 := by
  induction n with
  | zero =>
    intro c _
    simp
  | succ n ih =>
    have h := mul_mem ih hσ
    have hb : (n : ℤ) • e + e = ((n + 1 : ℕ) : ℤ) • e := by
      push_cast
      rw [add_smul, one_smul]
    rw [hb] at h
    rw [pow_succ]
    exact h


omit [∀ k, Fintype (ι k)] in
theorem pow_regular {c : ∀ k, ι k} {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1)
    (hreg : ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
      σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + e - 1) 1 → s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    (n : ℕ) (b : K → ℤ) (s : Ω) (hs : s ∈ chartLatQ y b 1)
    (h : σ ^ n * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (n : ℤ) • e - 1) 1) :
    s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  induction n generalizing b s with
  | zero => simpa using h
  | succ n ih =>
    have hσs : σ * s ∈ chartLatQ y (b + e) 1 := by
      have h' := mul_mem hσ hs
      rwa [add_comm e b] at h'
    refine hreg b s hs (ih (b + e) (σ * s) hσs ?_)
    have hb : b + ((n + 1 : ℕ) : ℤ) • e - 1 = b + e + (n : ℤ) • e - 1 := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hb, pow_succ, mul_assoc] at h
    exact h

theorem finiteDimensional (hF : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (b : K → ℤ) :
    FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨G, hG, hGfin⟩ := (AddSubgroup.fg_iff (chartLat y b 1)).mp (hF K ι Ω y b 1 hy)
  have := FiniteDimensional.span_of_finite ℚ hGfin
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ G) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have hmem : (N : Ω) * s ∈ Submodule.span ℚ G := by
    rw [← hG] at hNs
    exact (AddSubgroup.closure_le (Submodule.span ℚ G).toAddSubgroup).mpr Submodule.subset_span hNs
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hmem

theorem mem_chartDivSec {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (s : chartLatQ y b 1) :
    s ∈ chartDivSec y c b ↔ (s : Ω) / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  simp only [chartDivSec, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [← hts, mul_div_cancel_left₀ _ hm0]
    exact ht
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ hm0⟩

theorem finrank_quot_add_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ)
    [FiniteDimensional ℚ (chartLatQ y b 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) + Module.finrank ℚ (chartLatQ y (b - 1) 1) ≤
      Module.finrank ℚ (chartLatQ y b 1) := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hmem : ∀ t ∈ chartLatQ y (b - 1) 1, (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 :=
    fun t ht => mul_mem_chartLatQ b ht
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, hmem t t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Submodule.finrank_quotient_add_finrank (chartDivSec y c b)
  omega

theorem finrank_quot_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {b d b' : K → ℤ} (hbd : b + d = b') {τ : Ω}
    (hτ : τ ∈ chartLatQ y d 1)
    (hreg : ∀ s ∈ chartLatQ y b 1, τ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b' - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    [FiniteDimensional ℚ (chartLatQ y b' 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) ≤
      Module.finrank ℚ (chartLatQ y b' 1 ⧸ chartDivSec y c b') := by
  subst hbd
  have hmem : ∀ s ∈ chartLatQ y b 1, τ * s ∈ chartLatQ y (b + d) 1 := fun s hs => by
    have h := mul_mem hτ hs
    rwa [add_comm d b] at h
  let φ : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y (b + d) 1 :=
    { toFun := fun s => ⟨τ * s, hmem s s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r τ (s : Ω)) }
  have hle : chartDivSec y c b ≤ (chartDivSec y c (b + d)).comap φ := by
    intro s hs
    rw [Submodule.mem_comap, mem_chartDivSec hc]
    rw [mem_chartDivSec hc] at hs
    have h := mul_mem hτ hs
    rw [show d + (b - 1) = b + d - 1 by abel] at h
    show τ * (s : Ω) / _ ∈ _
    rw [mul_div_assoc]
    exact h
  have hinj : Function.Injective (Submodule.mapQ _ _ φ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]
      exact hreg s s.2 hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

end HyperplaneQuotientBound


open HyperplaneQuotientBound in
theorem HyperplaneQuotientBound.proof (hR : HyperplaneRegularSection.Statement)
    (hS : DiagonalSectionDifference.Statement) (hF : SectionLatticeFinite.Statement) :
    HyperplaneQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a c hD hV _ hc
  obtain ⟨M, hM1, hMa⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, a k ≤ M := by
    refine ⟨(∑ k, (a k).toNat) + 1, Nat.le_add_left _ _, fun k => ?_⟩
    have h1 : (a k).toNat ≤ ∑ k, (a k).toNat :=
      Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (a k)
    have h3 : ((a k).toNat : ℤ) ≤ ((∑ k, (a k).toNat : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 ⊢
    omega
  set e : K → ℕ := fun k => ((M : ℤ) - a k).toNat with he
  have hek : ∀ k, (e k : ℤ) = M - a k := fun k => Int.toNat_of_nonneg (sub_nonneg.mpr (hMa k))
  obtain ⟨σ, -, hσ, hreg⟩ := hR K ι Ω y c e hc
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  obtain ⟨C, hC⟩ := hS K ι Ω y D hD hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨C * (M : ℝ) ^ (D - 1), eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have hbd : (n : ℤ) • a + (n : ℤ) • (fun k => (e k : ℤ)) = ((n * M : ℕ) : ℤ) • (1 : K → ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek, Pi.one_apply]
    push_cast
    ring
  have := finiteDimensional hF hy (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h1 := finrank_quot_le hc hbd (pow_mem hσ n) (fun s hs h => pow_regular hσ hreg n _ s hs (by rwa [← hbd] at h))
  have h2 := finrank_quot_add_le hc (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h3 := hN (n * M) (le_trans hn (Nat.le_mul_of_pos_right n hM1))
  have h1' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) := by exact_mod_cast h1
  have h2' : (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) +
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1) : ℝ) := by exact_mod_cast h2
  have hpow : ((n * M : ℕ) : ℝ) ^ (D - 1) = (M : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by
    push_cast
    ring
  rw [hpow] at h3
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem LiftAtPrime.proof (hC : GeneratedPow.Statement) (hA : FibreSectionLift.Statement)
    (hB : FibreRelLift.Statement) : LiftAtPrime.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N p hY hp hN
  obtain ⟨q, hq, hgen, hvan⟩ := hN
  obtain ⟨t₀, ht₀⟩ := hvan 0
  refine ⟨q, t₀, hq, fun t ht => ?_⟩
  have hga : KH.GeneratedV (ZMod p) (fibreIdeal p y) ((t * q) • N) := by
    have h := hC (ZMod p) K ι (fibreIdeal p y) (q • N) t hgen
    rwa [smul_smul] at h
  have hH1 : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) ((t * q) • N) 1) := by
    have h := ht₀ t ht
    rwa [zero_add] at h
  have hfi : fibreIdeal p y = GenOnFibres.idealOver y (ZMod p) := rfl
  rw [hfi] at hga hH1
  choose r z u hz hu hrel using hga
  have hlift : ∀ I j, ∃ s ∈ chartLat y ((t * q) • N) 1,
      GenOnFibres.secCoch y (ZMod p) s ((t * q) • N) = z I j :=
    fun I j => hA K ι Ω y D p ((t * q) • N) hY hp hH1 (z I j) (hz I j)
  choose s hs hsz using hlift
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  have : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Σ I, Fin (r I))).symm
  refine ⟨Fintype.card (Σ I, Fin (r I)), fun j => s (e j).1 (e j).2, fun j => hs _ _, fun c hc => ?_⟩
  let J : KH.Cell K ι 0 := ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hJ : GenOnFibres.cellChart J = c :=
    funext fun k => Finset.mem_singleton.mp (GenOnFibres.cellChart_mem J k)
  have hrelJ : ∑ j, u J j * GenOnFibres.secCoch y (ZMod p) (s J j) ((t * q) • N) J = 1 := by
    rw [← hrel J]
    exact Finset.sum_congr rfl fun j _ => by rw [hsz J j]
  obtain ⟨u', v, hu', hv, hsum⟩ :=
    hB K ι Ω y p ((t * q) • N) (r J) (s J) J (u J) (hs J) (by rw [hJ]; exact hc) (hu J) hrelJ
  rw [hJ] at hu' hv hsum
  let U : (Σ I, Fin (r I)) → Ω := fun x => if h : x.1 = J then u' (Fin.cast (congrArg r h) x.2) else 0
  refine ⟨fun j => U (e j), v, fun j => ?_, hv, ?_⟩
  · simp only [U]
    split_ifs
    · exact hu' _
    · exact zero_mem _
  · rw [← hsum]
    congr 1
    rw [e.sum_comp (fun x => U x * (s x.1 x.2 * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))),
      Fintype.sum_sigma, Finset.sum_eq_single J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [U]
    · intro I _ hI
      exact Finset.sum_eq_zero fun j _ => by simp [U, hI]
    · intro h
      exact absurd (Finset.mem_univ J) h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ChartDimLt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (p : (k : K) → ι k),
    IsMultiHomogIdeal J →
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ ReciprocityTheory.AnForm.R.chartIdeal J p) < (e : WithBot ℕ∞)

def ChartRatioImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < (e : WithBot ℕ∞) →
      volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

