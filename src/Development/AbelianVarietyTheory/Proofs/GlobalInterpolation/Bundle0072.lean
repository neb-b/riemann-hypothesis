module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormLeOfCoord
section
noncomputable section

namespace GlobalTheory.LvT.PtNorm

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
open Formalism.REAL (fockF)
open Formalism.L2.DIV (fockL fockS)
open scoped ComplexOrder Matrix

theorem psd_had {κ : Type} {A B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i j => A i j * B i j).PosSemidef := hA.hadamard hB

theorem psd_prod {ι κ : Type} [Fintype κ] (A B : ι → Matrix κ κ ℂ) (hB : ∀ τ, (B τ).PosSemidef)
    (hAB : ∀ τ, (A τ - B τ).PosSemidef) (s : Finset ι) :
    (Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - (Matrix.of fun i j => ∏ τ ∈ s, B τ i j)).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : κ => (1 : ℂ))
      convert h using 1
      ext i j
      simp [Matrix.vecMulVec]
    · simpa using Matrix.PosSemidef.zero
  | insert τ s hτ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · convert psd_had (hB τ) h1 using 1
      ext i j
      simp [Finset.prod_insert hτ]
    · have h3 := (psd_had (hAB τ) (h2.add h1)).add (psd_had (hB τ) h2)
      convert h3 using 1
      ext i j
      simp [Finset.prod_insert hτ]
      ring

theorem fockF_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = fockL g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) g f (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  rw [Formalism.L2.DIV.fockL_apply, h]

theorem fockL_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockL f f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [← fockF_eq]; exact (Formalism.L2.DIV.ps_fockF_pos f hf).le

def gram {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : Matrix κ κ ℂ := Matrix.of fun i j => fockL (v i) (v j)

theorem gram_dot {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (gram v) *ᵥ x = fockL (∑ i, x i • v i) (∑ i, x i • v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_herm {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : (gram v).IsHermitian := by
  ext i j
  simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact (Formalism.L2.DIV.fockL_symm _ _).symm

theorem gram_psd {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) : (gram v).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_herm v) fun x => by rw [gram_dot]; exact fockL_nonneg _

theorem gram_sub_psd {σ σ' κ : Type} [Fintype κ] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (F : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ' ℂ) (C : ℝ)
    (h : ∀ f ∈ V, (fockL (F f) (F f)).re ≤ C * (fockL f f).re) (v : κ → MvPolynomial σ ℂ) (hv : ∀ i, v i ∈ V) :
    ((C : ℂ) • gram v - gram fun i => F (v i)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.sub ?_ (gram_herm _)
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (gram_herm v).eq]
    simp
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot]
    have e : ∑ i, x i • F (v i) = F (∑ i, x i • v i) := by simp
    rw [e]
    have hm : ∑ i, x i • v i ∈ V := V.sum_mem fun i _ => V.smul_mem _ (hv i)
    have h1 := h _ hm
    have h2 := (Complex.le_def.mp (fockL_nonneg (∑ i, x i • v i))).2
    have h3 := (Complex.le_def.mp (fockL_nonneg (F (∑ i, x i • v i)))).2
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · simp only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul]; linarith
    · simp only [smul_eq_mul, Complex.zero_im, Complex.sub_im, Complex.im_ofReal_mul, ← h2, ← h3]; simp

def eN {n : ℕ} (l : DomWeight n) : ℝ := (fockF (extremal ℂ n l) (extremal ℂ n l)).re

theorem eN_pos {n : ℕ} (l : DomWeight n) : 0 < eN l :=
  (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).1

theorem eN_eq {n : ℕ} (l : DomWeight n) : fockF (extremal ℂ n l) (extremal ℂ n l) = (eN l : ℂ) := by
  have h := (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).2
  exact Complex.ext (by simp [eN]) (by simpa using h.symm)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}
  (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

end GlobalTheory.LvT.PtNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RankRowsOfCrudeBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_rows_of_crude_bounds (y m k f L l A B : ℝ) (hy : 8 ≤ y) (hA : 64 * A ≤ y) (hB : B ≤ y)
    (hm0 : 0 ≤ m) (hm : m ≤ 2 * y) (hk : y ^ 9 ≤ k) (hf : y ^ 4 ≤ f) (hL0 : 0 ≤ L) (hL : L ≤ y)
    (hl0 : 0 ≤ l) (hl : l ≤ y ^ 2) :
    m ^ 2 * L ≤ k ∧ m * y * l ≤ k ∧ A * m ^ 6 * L ≤ k * Real.log k ∧ B * L ≤ f * Real.log k := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → y ^ a ≤ y ^ b := fun a b h => pow_le_pow_right₀ hy1 h
  have hk8 : 8 ≤ k := by
    have := hpow 1 9 (by norm_num)
    rw [pow_one] at this
    linarith
  have hlog : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkk : k ≤ k * Real.log k := le_mul_of_one_le_right (by linarith) hlog
  have hff : f ≤ f * Real.log k := le_mul_of_one_le_right (le_trans (by positivity) hf) hlog
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m ^ 2 * L ≤ (2 * y) ^ 2 * y := by gcongr
      _ = 4 * y ^ 3 := by ring
      _ ≤ y * y ^ 3 := by gcongr; linarith
      _ = y ^ 4 := by ring
      _ ≤ k := (hpow 4 9 (by norm_num)).trans hk
  · calc m * y * l ≤ (2 * y) * y * y ^ 2 := by gcongr
      _ = 2 * y ^ 4 := by ring
      _ ≤ y * y ^ 4 := by gcongr; linarith
      _ = y ^ 5 := by ring
      _ ≤ k := (hpow 5 9 (by norm_num)).trans hk
  · calc A * m ^ 6 * L = A * (m ^ 6 * L) := by ring
      _ ≤ (y / 64) * (m ^ 6 * L) := by gcongr; linarith
      _ ≤ (y / 64) * ((2 * y) ^ 6 * y) := by gcongr
      _ = y ^ 8 := by ring
      _ ≤ k := (hpow 8 9 (by norm_num)).trans hk
      _ ≤ _ := hkk
  · calc B * L ≤ y * L := by gcongr
      _ ≤ y * y := by gcongr
      _ = y ^ 2 := by ring
      _ ≤ f := (hpow 2 4 (by norm_num)).trans hf
      _ ≤ _ := hff

theorem szRow_rank_lower_bounds :
    SzRow (fun C D L => ((D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k) ∧ ((D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x ≤ D.R.k) ∧ (C.P.Ck6 * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) ∧ (C.P.CfL * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(max 8 (max (64 * C.P.Ck6) C.P.CfL)) ^ 2, ?_⟩⟩⟩
  intro D L _ hx hV
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hp := L.sc.eps_pos
  have hq := L.sc.eps_lt
  have hy : max 8 (max (64 * C.P.Ck6) C.P.CfL) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hx
  have hnat : ∀ j : ℕ, (L.sc.x ^ ((1 : ℝ) / 2)) ^ j = L.sc.x ^ ((j : ℝ) / 2) := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hmono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  refine rank_rows_of_crude_bounds (L.sc.x ^ ((1 : ℝ) / 2)) _ _ _ _ _ _ _
    ((le_max_left _ _).trans hy) (((le_max_left _ _).trans (le_max_right _ _)).trans hy)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hy) (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have hd : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
    have : L.sc.x * L.sc.delta1 ≤ L.sc.x := mul_le_of_le_one_right hx0.le hd
    gcongr
  · rw [hnat]
    exact (hmono _ _ (by push_cast; linarith)).trans hk
  · rw [hnat]
    refine ((hmono _ _ (by push_cast; linarith)).trans hn).trans ?_
    have h0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
    unfold Ranks.f
    push_cast
    linarith
  · exact Real.rpow_nonneg hx0.le _
  · exact hmono _ _ (by linarith)
  · exact Real.log_nonneg hx1.le
  · rw [hnat]
    have := Real.log_le_sub_one_of_pos hx0
    norm_num
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RbSNumeric
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rbS_numeric {x E P X b k r m de Del lg : ℝ} (hx : 8 ≤ x) (hE0 : 0 < E) (hE : E ≤ x) (hP : 0 ≤ P)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * x ^ 5) (hr : r ≤ 2 * k) (hm : 2 ≤ m) (hde : E⁻¹ ≤ de)
    (hD0 : 0 ≤ Del) (hD : Del ≤ 2 * P) (hl0 : 0 ≤ lg) (hl : lg ≤ x) (hb : 0 < b)
    (hX : x ^ 16 ≤ X) (hPb : x ^ 22 * P ≤ b) :
    r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de)) ≤ de * m * b := by
  have hx0 : 0 < x := by linarith
  have hxde : x⁻¹ ≤ de := (inv_anti₀ hE0 hE).trans hde
  have hde0 : 0 < de := lt_of_lt_of_le (inv_pos.mpr hx0) hxde
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h1 : k * E / (m * de) ≤ 2 * x ^ 7 := by
    calc k * E / (m * de) ≤ (2 * x ^ 5) * x / (1 * x⁻¹) := by
          gcongr
          linarith
      _ = 2 * x ^ 7 := by field_simp
  have h2 : x * b / X ≤ b / (8 * x ^ 14) := by
    calc x * b / X ≤ x * b / x ^ 16 := by gcongr
      _ = b / (x * x ^ 14) := by field_simp
      _ ≤ b / (8 * x ^ 14) := by gcongr
  have h3 : k * (4 * Del) ≤ b / (8 * x ^ 14) := by
    rw [le_div_iff₀ (by positivity)]
    have h128 : (128 : ℝ) ≤ x ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 3)
    calc k * (4 * Del) * (8 * x ^ 14) ≤ (2 * x ^ 5) * (4 * (2 * P)) * (8 * x ^ 14) := by gcongr
      _ = 128 * (x ^ 19 * P) := by ring
      _ ≤ x ^ 3 * (x ^ 19 * P) := by gcongr
      _ = x ^ 22 * P := by ring
      _ ≤ b := hPb
  have hr' : r ≤ 4 * x ^ 5 := by linarith
  calc r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de))
      ≤ (4 * x ^ 5) * (b / (8 * x ^ 14) + b / (8 * x ^ 14)) * x * (2 * x ^ 7) := by
        gcongr
    _ = x⁻¹ * 2 * b := by field_simp; ring
    _ ≤ de * m * b := by gcongr

theorem szRow_rbS : SzRow (fun C D L => ((D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤
    L.de2 * D.R.m * L.sc.b)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 16 0 1 0 le_rfl (by linarith) one_pos
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps (22 + cD) 0 1 0 le_rfl he0 one_pos
  refine ⟨max 8 (max x1 x2), fun D L heps hx V => ?_⟩
  have hx8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx1 := h1 _ (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx)
  have hx2 := h2 _ (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx)
  simp only [zero_mul, add_zero, one_mul] at hx1 hx2
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hP : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hone hcD
  have hn : (0 : ℝ) < D.R.n := by
    have hn : 0 < D.R.n := by
      unfold Ranks.n
      have := D.R.two_le_m
      have := D.R.m_le_f
      omega
    exact_mod_cast hn
  beta_reduce
  unfold lA Scale.b' Scale.a
  rw [L.Sc_eq, V.Del_eq]
  refine rbS_numeric (P := L.sc.x ^ cD) hx8 (Real.rpow_pos_of_pos hx0 _) ?_ (by linarith) (Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_ (by positivity) ?_ (Real.log_nonneg hone) ((Real.log_le_sub_one_of_pos hx0).trans (by linarith))
    (Real.exp_pos _) ?_ ?_
  · calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = L.sc.x := Real.rpow_one _
  · refine V.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hone (by push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  · have h := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  · exact_mod_cast D.R.two_le_m
  · rw [L.typeDensity_eq_card_div, le_div_iff₀ hn, ← Real.rpow_neg hx0.le]
    exact V.host.2.2.1
  · have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    simp only [Delv, Rat.cast_natCast]
    linarith
  · unfold Scale.X'
    rw [heps, ← Real.exp_log (pow_pos hx0 16), Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  · unfold Scale.b Scale.L
    rw [heps, ← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem words_real_bound {x e G F m n : ℝ} {k : ℕ} (hx : 1 < x) (he : 0 < e) (hG : 1 ≤ G) (hF : 1 ≤ F)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm : m ≤ 2 * Real.sqrt (x * x ^ (-(e / 8)))) (hn : n ≤ 2 * x ^ (2 + 8 * e))
    (hk : x ^ (9 / 2 + 10 * e) ≤ (k : ℝ)) (hk3 : 3 ≤ k)
    (hK : 2 * (256 * G + F + 2) + 3 ≤ x ^ e) :
    3 * Real.exp (G * m ^ 5 * (2 * n) * x ^ e) ^ 2 * x ^ F ≤ (2 : ℝ) ^ (k - 3) := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (9 / 2 + 9 * e) with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hy1 : 1 ≤ y := by linarith
  have hm' : m ≤ 2 * x ^ (1 / 2 : ℝ) := by
    refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have h1 : x ^ (-(e / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    have : Real.sqrt (x * x ^ (-(e / 8))) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hm5 : m ^ 5 ≤ 32 * x ^ (5 / 2 : ℝ) := by
    have h1 : m ^ 5 ≤ (2 * x ^ (1 / 2 : ℝ)) ^ 5 := pow_le_pow_left₀ hm0 hm' 5
    have h2 : (x ^ (1 / 2 : ℝ)) ^ 5 = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [mul_pow, h2] at h1
    linarith
  have hprod : x ^ (5 / 2 : ℝ) * x ^ (2 + 8 * e) * x ^ e = y := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hy]; congr 1; ring
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 e
  have hA : m ^ 5 * (2 * n) * x ^ e ≤ 128 * y := by
    rw [← hprod]
    have h1 : m ^ 5 * (2 * n) ≤ (32 * x ^ (5 / 2 : ℝ)) * (2 * (2 * x ^ (2 + 8 * e))) :=
      mul_le_mul hm5 (by linarith) (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_right h1 hxe.le
    linarith
  have hky : y * x ^ e ≤ (k : ℝ) := by
    refine le_trans (le_of_eq ?_) hk
    rw [hy, ← Real.rpow_add hx0]; congr 1; ring
  have hlogx : Real.log x ≤ y := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hk' : 2 * ((256 * G + F + 2) * y) ≤ ((k - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk3]
    push_cast
    have := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have hR : (2 : ℝ) ^ (k - 3) = Real.exp (((k - 3 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hR, Real.rpow_def_of_pos hx0 F, ← Real.exp_nat_mul]
  calc 3 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F)
      ≤ Real.exp 2 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F) := by
        gcongr
    _ = Real.exp (2 + ((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e) + Real.log x * F) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h1 : G * (m ^ 5 * (2 * n) * x ^ e) ≤ G * (128 * y) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have h2 : Real.log x * F ≤ y * F := mul_le_mul_of_nonneg_right hlogx (by linarith)
        have h4 : ((k - 3 : ℕ) : ℝ) * (1 / 2) ≤ ((k - 3 : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        push_cast
        nlinarith

theorem szRow_card_words_le : SzRow (fun C D L => (Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3))) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP, -, hmid, -⟩ := hC
  have hG : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hG' : 1 ≤ C.CGam * C.P.Cpde := by nlinarith
  have hP0 : 0 < C.P.Cpde := by linarith
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3) ^ eps⁻¹, ?_⟩⟩⟩
  intro D L hLe hx hV
  have hK : 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 ≤ L.sc.x ^ eps := by
    have h0 : (0 : ℝ) ≤ 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 := by linarith
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hx he.le
    rwa [Real.rpow_inv_rpow h0 he.ne'] at this
  have hn0 := hV.ranks.n_le_of_o hV.host.o_le
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [hV.words, Nat.ceil_le]
  rw [hLe] at hn0 hk
  have hn : (D.R.n : ℝ) / C.P.Cpde ≤ 2 * L.sc.x ^ (2 + 8 * eps) := by
    rw [div_le_iff₀ hP0]; linarith
  simp only [Scale.delta1, hLe] at hm
  have := words_real_bound L.sc.one_lt_alt he hG' hF (Nat.cast_nonneg D.R.m)
    (div_nonneg (Nat.cast_nonneg D.R.n) hP0.le) hm hn hk hk3 hK
  have e : C.CGam * C.P.Cpde * (D.R.m : ℝ) ^ 5 * (2 * ((D.R.n : ℝ) / C.P.Cpde))
      = C.CGam * (D.R.m : ℝ) ^ 5 * (2 * (D.R.n : ℝ)) := by
    field_simp
  rw [e] at this
  simp only [GamL, Scale.L, Ranks.f, hV.CGam_eq, hLe]
  push_cast
  exact this

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowExact
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_exact : SzRow (fun C D L => (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + (⌊L.sc.b' / L.sc.x⌋ : ℤ)) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * L.Sc) ∧ (∀ τ (hk : 2 ≤ D.R.k), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ - 1 / 2) ∧ (∀ τ (hm : 0 < D.R.m), |((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ τ (j : ℕ) (h : j + 1 < D.R.m), h0 L ≤ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ∧ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ≤ h0 L + 1) ∧ (∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) ∧ (D.div.etaF = C.P.CetaF * L.sc.x ^ (-C.P.CF)) ∧ (D.host.pde % 15 = 1 ∧ D.host.pde' % 15 = 1) ∧ (∀ i, D.host.pde ≠ D.host.g i ∧ D.host.pde' ≠ D.host.g i) ∧ (Real.log (Ideal.absNorm D.host.ccK) ≤ L.sc.L) ∧ ((Ideal.absNorm D.host.ccK : ℝ) ≤ C.P.CccK * D.host.d)) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  obtain ⟨hv, hu, ⟨b1, hb, htop, -, -⟩, hpar⟩ := hV.hc
  have hm2 := D.R.two_le_m
  have hm0 : (D.R.m : ℝ) ≠ 0 := by
    have : D.R.m ≠ 0 := by omega
    exact_mod_cast this
  have hh0 : h0 L = (h0v L.sc ch : ℝ) := by
    unfold h0
    rw [hV.eta_eq]
    field_simp
  have hcen : ∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2 := by
    intro τ j
    rw [(hb τ j).2, hh0]
    push_cast
    simp
  have hcc : D.host.ccK = ⊤ := hV.host.2.2.2.2.2.2.1
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  refine ⟨?_, ?_, ?_, fun τ hm => hcen τ _, ?_, hcen, hpar, ?_, D.host.pde_mod, D.host.pde_ne_g, ?_, ?_⟩
  · intro τ t hm ht
    rw [(hb τ ⟨0, hm⟩).1, htop τ t ht]
    push_cast
    simp
  · intro τ h0 ht
    rw [(hu τ (by omega) ht).1, hv τ ⟨0, h0⟩, L.Sc_eq, hV.Del_eq]
    have hD : (1 : ℝ) ≤ (Delv L.sc cD : ℝ) := by
      have : 0 < Delv L.sc cD := Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
      exact_mod_cast this
    have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
      have : 1 ≤ D.R.k := by omega
      exact_mod_cast this
    simp only [Nat.sub_zero]
    push_cast
    nlinarith
  · intro τ hk ht
    rw [(hu τ (by omega) ht).2, hv τ ⟨D.R.k - 2, by omega⟩]
    simp
    norm_num
  · intro τ j h
    rw [(hb τ ⟨j + 1, h⟩).1, (hb τ ⟨j, by omega⟩).1, hh0]
    push_cast
    constructor <;> nlinarith
  · rw [hV.etaF_eq, hC.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hcc, Ideal.absNorm_top]
    simp only [Nat.cast_one, Real.log_one]
    unfold Scale.L
    positivity
  · rw [hcc, Ideal.absNorm_top, hC.2.2.2.2.2.2.1]
    have : 1 ≤ D.host.d := D.host.hyp.2.1.one_le
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast this

end GlobalTheory.EX
end

