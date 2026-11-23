module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZeroOfBlk
public import Formalism.HermitianCurvature.StatementSz

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsTr
section
noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsTr

open Formalism.L2.SG.Pf.AllRowsGA

section One

variable {G : Type} [Group G] [Fintype G]

theorem tau_mul_comm (a b : MonoidAlgebra ℂ G) : (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [coeff_mul_fin, coeff_mul_fin]
  simp only [mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by rw [Equiv.inv_apply, inv_inv, mul_comm])

theorem tau_conj (P : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff 1 = a.coeff 1 := by
  rw [tau_mul_comm, ← mul_assoc, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
    ← MonoidAlgebra.one_def, one_mul]

theorem tau_normSq (x : MonoidAlgebra ℂ G) :
    (conjA x * x).coeff 1 = ((∑ h : G, Complex.normSq (x.coeff h) : ℝ) : ℂ) := by
  rw [coeff_mul_fin, Complex.ofReal_sum]
  simp only [conjA_coeff, mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _
    (fun h => by rw [Equiv.inv_apply, Complex.star_def, mul_comm, Complex.mul_conj])

theorem tau_proj (a e : MonoidAlgebra ℂ G) (ha : a * a = a) (hsa : conjA a = a) (he : e * e = e)
    (hc : ∀ y, e * y = y * e) (hse : conjA e = e) :
    (a * e).coeff 1 = ((∑ h : G, Complex.normSq ((a * e).coeff h) : ℝ) : ℂ) := by
  have hx : conjA (a * e) * (a * e) = a * e := by
    rw [conjA_mul, hse, hsa, mul_assoc, ← mul_assoc a a e, ha, ← mul_assoc, hc a, mul_assoc, he]
  rw [← tau_normSq (a * e), hx]

end One

section Prod

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

def pA (f : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun γ => ∏ i, (f i).coeff (γ i))

theorem pA_coeff (f : ∀ i, MonoidAlgebra ℂ (G i)) (γ : ∀ i, G i) : (pA f).coeff γ = ∏ i, (f i).coeff (γ i) := by
  simp [pA, MonoidAlgebra.coeff_ofCoeff]

theorem pA_mul (f g : ∀ i, MonoidAlgebra ℂ (G i)) : pA f * pA g = pA (fun i => f i * g i) := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin, pA_coeff]
  simp only [pA_coeff, coeff_mul_fin]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.prod_mul_distrib]
  rfl

theorem pA_one_coeff (f : ∀ i, MonoidAlgebra ℂ (G i)) : (pA f).coeff 1 = ∏ i, (f i).coeff 1 := by
  rw [pA_coeff]
  rfl

end Prod

end Formalism.L2.SG.Pf.AllRowsTr
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LastDiagMulVec
section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {r : ℕ}

def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0

theorem lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]

theorem gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdBounds
section
noncomputable section

open Finset

namespace Formalism.L2.SG.Pf.ThresholdBounds

open Formalism.FourierDecayAlt

variable (c : Sz.Cfg)

private theorem v_eq_vlast_add_four_mul_Del (i : ℕ) : c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ)) := rfl

theorem v_sub (i j : ℕ) : c.v i - c.v j = 4 * c.Del * ((j : ℝ) - (i : ℝ)) := by
  rw [v_eq_vlast_add_four_mul_Del c i, v_eq_vlast_add_four_mul_Del c j]; ring

theorem b_one_le (hOk : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro hj hjm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact le_refl _
    · have h1 := ih (by omega) (by omega)
      have h2 := hOk.hgap n (by omega) (by omega)
      linarith

theorem qfac_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    {l : ℕ} (hl : l + 1 ≤ c.k) {Y : ℝ} (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) {i : ℕ} (hi1 : 1 ≤ i)
    (hik : i ≤ c.k) : Y + 1 / 2 + c.u de i ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  have hkD : 4 * c.Del ≤ (c.k : ℝ) * c.Del := mul_le_mul_of_nonneg_right hk4 (by linarith)
  have hw1 : ∀ i, de i = 0 ∨ de i = 1 :=
    (show (∀ i, de i = 0 ∨ de i = 1) ∧ de (c.k - 1) = 0 from hw).1
  by_cases h1 : i = 1
  · subst h1
    have hu : c.u de 1 = c.a := by simp [Formalism.FourierDecayAlt.Sz.Cfg.u]
    have ha := hOk.ha
    have e := v_sub c 1 l
    push_cast at e
    have hl0 : 0 ≤ 4 * c.Del * (l : ℝ) := by positivity
    rw [hu]; apply ne_of_gt; linarith
  · by_cases hk : i = c.k
    · have hu : c.u de i = c.ulast := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_pos hk]
      rw [hu]
      cases ht : c.top
      · have hul : c.ulast = c.vlast - 1 / 2 := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        rcases Nat.lt_or_ge (l + 1) c.k with hlt | hge
        · have h2' : l + 2 ≤ c.k := by omega
          have h2 : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast h2'
          have hvl' : c.vlast + 4 * c.Del ≤ c.v l := by
            rw [v_eq_vlast_add_four_mul_Del c l]
            have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (c.k : ℝ) - 1 - l by linarith)
              (by linarith : (0 : ℝ) ≤ 4 * c.Del)
            linarith
          apply ne_of_lt; linarith
        · have heq : (l : ℝ) + 1 = c.k := by exact_mod_cast (le_antisymm hl hge)
          have hv' : c.v l = c.vlast := by rw [v_eq_vlast_add_four_mul_Del c l, ← heq]; ring
          apply ne_of_gt; linarith
      · have hul : c.ulast = -c.bp := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        have hbp := (hOk.htop ht).1
        apply ne_of_lt; linarith
    · have hu : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_neg hk]
      rw [hu]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have e := v_sub c j l
      have hde := hw1 j
      rcases lt_trichotomy j l with hjl | rfl | hlj
      · have h' : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
        have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - j) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_gt <;> linarith
      · rcases hde with h | h <;> rw [h]
        · apply ne_of_gt; linarith
        · apply ne_of_lt; linarith
      · have h' : (l : ℝ) + 1 ≤ j := by exact_mod_cast hlj
        have : 4 * c.Del * ((l : ℝ) - j) ≤ 4 * c.Del * (-1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_lt <;> linarith

theorem q_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {Y : ℝ}
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) : c.q de de' T T' Y ≠ 0 := by
  show -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)) ≠ 0
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT hT')) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact mul_ne_zero (qfac_ne c hOk hb1 hw hl hY1 hY2 hi.1 hi.2)
    (qfac_ne c hOk hb1 hw' hl hY1 hY2 hi.1 hi.2)

theorem P_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {l : ℕ} (hl : l + 1 ≤ c.k) {t : ℝ}
    (ht0 : 0 < t) (ht4 : t < 4) : c.P (t - c.v l) ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  show (∏ s ∈ Icc 1 (c.k + c.m - 1), ((t - c.v l) + c.lam s)) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  rw [Finset.mem_Icc] at hs
  by_cases hsk : s < c.k
  · have hlam : c.lam s = c.v s := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have e := v_sub c s l
    rcases lt_trichotomy s l with h | rfl | h
    · have h' : (s : ℝ) + 1 ≤ l := by exact_mod_cast h
      have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_gt; linarith
    · apply ne_of_gt; linarith
    · have h' : (l : ℝ) + 1 ≤ s := by exact_mod_cast h
      have : 4 * c.Del * ((l : ℝ) - s) ≤ 4 * c.Del * (-1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_lt; linarith
  · have hlam : c.lam s = -c.b (s + 1 - c.k) := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have hj1 : 1 ≤ s + 1 - c.k := by omega
    have hjm : s + 1 - c.k ≤ c.m := by have := hOk.hm; omega
    have hbj := b_one_le c hOk _ hj1 hjm
    apply ne_of_lt; linarith

theorem cutI_eq (l : ℕ) : c.cutI l = Set.Icc (5 / 2 - c.v l) (c.Del / 2 - c.v l) := by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)

theorem cutIntervalLong_eq_Icc (l : ℕ) (N : ℝ) : c.cutIntervalLong l N = Set.Icc (5 / 2 - c.v l) (N ^ 3 - c.v l) :=
  by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutIntervalLong, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)

private theorem continuousOn_mul_be_of_window (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) {S : Set ℝ}
    (hS : ∀ Y ∈ S, 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2) :
    ContinuousOn (fun Y => gm * c.be ka de de' T T' Y) S := by
  have hP : Continuous c.P := by
    show Continuous (fun Y : ℝ => ∏ s ∈ Icc 1 (c.k + c.m - 1), (Y + c.lam s))
    exact continuous_finsetProd _ (fun s _ => continuous_add_const _)
  have hq : Continuous (fun Y => c.q de de' T T' Y) := by
    show Continuous (fun Y : ℝ =>
      -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)))
    exact continuous_const.fun_mul (continuous_finsetProd _ (fun i _ => by fun_prop))
  have hP1 : Continuous (fun Y : ℝ => c.P (Y + 1)) := hP.comp (continuous_add_const 1)
  have hd : ContinuousOn (fun Y => c.P Y * c.P (Y + 1) / c.q de de' T T' Y) S :=
    (hP.mul hP1).continuousOn.div hq.continuousOn
      (fun Y hY => q_ne c hOk hb1 hw hw' hl hT hT' (hS Y hY).1 (hS Y hY).2)
  have h : ContinuousOn (fun Y => gm * ((ka ^ (c.m - 1))⁻¹ *
      Real.sqrt |c.P Y * c.P (Y + 1) / c.q de de' T T' Y|)) S :=
    continuousOn_const.mul (continuousOn_const.mul hd.abs.sqrt)
  exact h

theorem bdd_cutI (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) :
    BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  rw [cutI_eq c l]
  exact isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm
    (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))

private theorem mul_be_pos_of_isWord (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm)
    (hN : 11 / 4 ≤ c.Del / 2) : 0 < gm * c.be ka de de' T T' (11 / 4 - c.v l) := by
  have hP0 : c.P (11 / 4 - c.v l) ≠ 0 := P_ne c hOk hb1 hl (by norm_num) (by norm_num)
  have hP1 : c.P (11 / 4 - c.v l + 1) ≠ 0 := by
    have h := P_ne c hOk hb1 hl (t := 15 / 4) (by norm_num) (by norm_num)
    rwa [show (15 / 4 : ℝ) - c.v l = 11 / 4 - c.v l + 1 by ring] at h
  have hq : c.q de de' T T' (11 / 4 - c.v l) ≠ 0 :=
    q_ne c hOk hb1 hw hw' hl hT hT' (by linarith) (by linarith)
  have hs : 0 < Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  show 0 < gm * ((ka ^ (c.m - 1))⁻¹ *
    Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)|)
  exact mul_pos hgm (mul_pos (inv_pos.mpr (pow_pos hka _)) hs)

theorem supI_pos (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) (hD : 11 / 2 ≤ c.Del) {de de' : ℕ → ℝ}
    (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0)
    (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  have hbdd := bdd_cutI c hOk hb1 hw hw' hl hT hT' ka gm
  have hY0 : (11 / 4 - c.v l) ∈ c.cutI l := by
    show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ c.Del / 2
    constructor <;> linarith
  exact lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith))
    (le_csSup hbdd ⟨_, hY0, rfl⟩)

theorem sSup_be_image_cutIntervalLong_pos (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {N : ℝ} (hN1 : 11 / 4 ≤ N ^ 3)
    (hN2 : N ^ 3 ≤ c.Del / 2) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ}
    (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N) := by
  have hbdd : BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N) := by
    rw [cutIntervalLong_eq_Icc c l N]
    exact isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm
      (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))
  have hY0 : (11 / 4 - c.v l) ∈ c.cutIntervalLong l N := by
    show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ N ^ 3
    constructor <;> linarith
  exact lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith))
    (le_csSup hbdd ⟨_, hY0, rfl⟩)

end Formalism.L2.SG.Pf.ThresholdBounds
end
end

