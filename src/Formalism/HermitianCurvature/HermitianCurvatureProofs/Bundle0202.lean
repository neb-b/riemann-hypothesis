module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddPowLeExp
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    have hd : (β - α) / 3 ≤ -(y + 1 + lam t) := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    have hx2 : 0 ≤ x0 ^ 2 := sq_nonneg _
    have hF2 : 0 ≤ F ^ 2 := sq_nonneg _
    have hA : 0 ≤ E1 * (sA ^ 2 * q) := by positivity
    have hB : 0 ≤ q / TT := by positivity
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLift
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem nice_mono {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {ε ε' : ℝ} {F : B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : JC.NiceCoef Bs ε F) (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => hε.trans (h.2.2 g hg hne)⟩

theorem poly_coeff_unique {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (A B : Fin n → V)
    (h : ∀ y : ℝ, ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • A l = ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • B l) : A = B := by
  set τ : Fin n → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  have key : ∀ (C : Fin n → V) (l : Fin n),
      C l = ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i • ∑ m : Fin n, (τ i ^ (m : ℕ)) • C m := by
    intro C l
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [vand_row τ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  funext l
  rw [key A l, key B l]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact h ((i : ℕ) : ℝ)

section lift

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sum_pad {V : Type} [AddCommGroup V] [Module ℂ V] {d n : ℕ} (hdn : d ≤ n) (c : Fin (d + 1) → V) (y : ℂ) :
    ∑ m : Fin (d + 1), (y ^ (m : ℕ)) • c m =
      ∑ l : Fin (n + 1), (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0) := by
  classical
  have e := Finset.sum_map (Finset.univ : Finset (Fin (d + 1))) (Fin.castLEEmb (by omega : d + 1 ≤ n + 1))
    (fun l : Fin (n + 1) => (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0))
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (d + 1))).map
    (Fin.castLEEmb (by omega : d + 1 ≤ n + 1)))) ?_, e]
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [dite_eq_left (by omega)]
  · intro l _ hl
    rw [dite_eq_right, smul_zero]
    intro hle
    apply hl
    rw [Finset.mem_map]
    exact ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem reduceJ {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) (hs : s ≤ j)
    (hSP : SlicePoly T F j hj (h ++ [(s, τ)]) ha) (hLD : LiftDeg T F j s hj h τ ha)
    (w' : List C.Letter) (hN : ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a'))
    (b : Bool) (δ : ℝ) :
    ∃ E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      (∀ l, ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (E l a')) ∧ (∀ l : Fin (j + 1), j - s < (l : ℕ) → E l = 0) ∧
      E ⟨j - s, by omega⟩ = cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha ∧
      ∀ (y : ℝ) (a' : Wd.Ix (Fin w'.length)), ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z',
        B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
          B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) a') g := by
  classical
  obtain ⟨C1, -, hC1n, hC1⟩ := hSP w' b δ 1
  obtain ⟨εN, hεN⟩ := hN
  set E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) := fun l =>
    if (l : ℕ) < j - s then C1 l else if (l : ℕ) = j - s then cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha
    else 0 with hE

  choose εC hεC using hC1n
  set ε0 : ℝ := min εN (Finset.univ.inf' Finset.univ_nonempty εC) with hε0
  have hC1n' : ∀ l a', JC.NiceCoef (T.bs j) ε0 (C1 l a') := fun l a' =>
    nice_mono (hεC l a') ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l)))
  have hNn' : ∀ a', JC.NiceCoef (T.bs j) ε0 (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') := fun a' =>
    nice_mono (hεN a') (min_le_left _ _)
  have hEn : ∀ l a', JC.NiceCoef (T.bs j) ε0 (E l a') := by
    intro l a'
    simp only [hE]
    split_ifs
    · exact hC1n' l a'
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hNn' a')
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  refine ⟨E, fun l => ⟨ε0, hEn l⟩, fun l hl => ?_, ?_, fun y a' g hg => ?_⟩
  · simp only [hE]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [hE]; rw [if_neg (by simp), if_pos (by simp)]
  ·
    have hsum : ∀ (y : ℝ) (V : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)),
        (∀ l, JC.NiceCoef (T.bs j) ε0 (V l a')) →
        B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a') g =
          ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (V l a') g := by
      intro y V hV
      have e1 : (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a' = ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l a' := by
        simp [Finset.sum_apply]
      rw [e1, Formalism.FourierDecayAlt.P.JCx2.bc_JF_sum Finset.univ (fun l : Fin (j + 1) => ((y : ℂ) ^ (l : ℕ)) • V l a')
        (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hV l)) hg]
      apply Finset.sum_congr rfl
      intro l _
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _
    have hgGV : g ∈ B.GV k (r - j) := hg.1

    have hL : ∀ y' : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y' + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j + 1), ((y' : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (C1 l a') g := by
      intro y'
      rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr (T.bs j) (fun g' hg' => hC1 y' a' g' hg') hgGV]
      exact hsum y' C1 (fun l => hC1n' l a')
    obtain ⟨c, hcl, hcy⟩ := hLD w' a' b δ g hg
    have hcomp := poly_coeff_unique (j + 1) (fun l => B.JF (T.bs j) (C1 l a') g)
      (fun l => if hl : (l : ℕ) ≤ j - s then c ⟨l, by omega⟩ else 0) (fun y' => by
        rw [← hL y', hcy y', sum_pad (n := j) (by omega) c (y' : ℂ)])
    rw [hL y, hsum y E (fun l => hEn l a')]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    have hcl' := congrFun hcomp l
    by_cases h1 : (l : ℕ) < j - s
    · simp only [hE, if_pos h1]
    · rw [show B.JF (T.bs j) (C1 l a') g = _ from hcl']
      by_cases h2 : (l : ℕ) = j - s
      · simp only [hE, if_neg h1, if_pos h2]
        rw [dite_eq_left (by omega)]
        have e3 : (⟨(l : ℕ), by omega⟩ : Fin (j - s + 1)) = Fin.last (j - s) := Fin.ext (by simp [h2])
        rw [e3, hcl]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _).symm
      · simp only [hE, if_neg h1, if_neg h2]
        rw [dite_eq_right (by omega)]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero g).symm

theorem nice_lincomb {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} {S ι : Type} [Fintype S] [Fintype ι] [Nonempty ι]
    (V : ι → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hV : ∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (V l a)) (c : ι → ℂ) :
    ∃ ε, ∀ a, JC.NiceCoef Bs ε ((∑ l, c l • V l) a) := by
  classical
  choose ε hε using hV
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, fun a => ?_⟩
  have e : (∑ l, c l • V l) a = fun g => ∑ l, c l • V l a g := by
    funext g; simp [Finset.sum_apply]
  rw [e]
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum Finset.univ (fun l g => c l • V l a g)
    (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (nice_mono (hε l a) (Finset.inf'_le _ (Finset.mem_univ l))))

end lift

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pOp l f₁ c = pOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pOp, wirt, ite_eq_left hc, hev.fderiv_eq]

theorem vAB_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (Q.vAB r Y i).1 f₁ c = (Q.vAB r Y i).1 f₂ c ∧ (Q.vAB r Y i).2 f₁ c = (Q.vAB r Y i).2 f₂ c := by
  intro i f₁ f₂ h
  induction i with
  | zero =>
    intro c hc
    exact ⟨h c hc, rfl⟩
  | succ i ih =>
    intro c hc
    by_cases hi : i < r
    · simp only [Q.vAB, dite_eq_left hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
        rw [(ih c hc).1, (ih c hc).2, pOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [ciOp]
        rw [(ih c hc).1]
    · simp only [Q.vAB, dite_eq_right hi]
      exact ih c hc

end loc

section jd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_dinv (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g =
      (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • B.JF Bs H g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g ∂Bs.μSS =
    (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • ∫ p, JF.xiP Bs p • B.rho Bs p H g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho]
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

end jd

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_raising_top_of_parts : PBN.RadAATopOfParts := by
  intro hJ hC hM hR hCp Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 y hD F hF
  refine ⟨hCp P.k P.r Wp Wq Bs F y hF, fun Φ hΦ x hx => ?_⟩
  have hL : Q.IsActualLevel X L := hD.2.2.1
  have hc0 : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hγ := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx

  have e1 : (TL.aP L (y : ℂ)).1 Φ = (L.ζi).1 ((L.Ar (y : ℂ)).1 Φ) := rfl
  rw [e1, hL.2.2.2.2.2.2.2.1]
  show ((X.fn 1 ((L.Ar (y : ℂ)).1 Φ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.fn_apply 1 _ x hx, hR P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' X L (y : ℂ) hL Φ x hx]
  have eΦ : Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) x.1 x.2 :=
    (vAB_loc (y : ℂ) P.r _ _ (fun c' hc' => hΦ (c', x.2) ⟨hc', hx.2⟩) x.1 hx.1).1
  rw [eΦ, ← hM P.k P.r Wp Wq Bs F (y : ℂ) hF x hx]

  simp only [Q.resG]
  have eJ : B.JF Bs (aaTop Bs y F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) =
      (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ •
        qminorOp (EabH (Hpk P.k P.r)) (C3.xR P.k P.r P.r le_rfl) (C3.xR P.k P.r P.r le_rfl)
          ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) := by
    unfold aaTop
    rw [jf_dinv, hJ P.k P.r Wp Wq Bs F _ hF _ hγ, hC P.k P.r _ _ _ _ _ hx.2.1, hcell.2.2.1, smul_smul]
    congr 1
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [eJ, smul_comm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorLiftHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

