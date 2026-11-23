module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem det_map_algebraMap {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by
  rw [RingHom.map_det]
  rfl

theorem eq_one_of_le_one_of_mul_eq_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  have h1 := mul_le_of_le_one_right (zero_le : (0 : NNReal) ≤ a) hb
  rw [h] at h1
  exact le_antisymm ha h1

private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext x j
  have hx := congrFun (hc j) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hx
  rw [Matrix.mul_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

theorem valuation_det_eq_of_span_eq_alt (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by
  obtain ⟨A, hA⟩ := cols_mul_lemma (R := R) h.ge
  obtain ⟨B, hB⟩ := cols_mul_lemma (R := R) h.le
  have hdQ : Q.det = P.det * algebraMap R C A.det := by
    rw [hA, Matrix.det_mul, det_map_algebraMap]
  have hdP : P.det = Q.det * algebraMap R C B.det := by
    rw [hB, Matrix.det_mul, det_map_algebraMap]
  have hAB : algebraMap R C A.det * algebraMap R C B.det = 1 := by
    refine mul_left_cancel₀ hP.ne_zero ?_
    calc P.det * (algebraMap R C A.det * algebraMap R C B.det)
        = P.det * algebraMap R C A.det * algebraMap R C B.det := (mul_assoc _ _ _).symm
      _ = P.det := by rw [← hdQ, ← hdP]
      _ = P.det * 1 := (mul_one _).symm
  have hvA : v (algebraMap R C A.det) = 1 :=
    eq_one_of_le_one_of_mul_eq_one (hv.map_le_one _) (hv.map_le_one _)
      (by rw [← map_mul v, hAB, map_one])
  rw [hdQ, map_mul, hvA, mul_one]

theorem exists_matrix_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  suffices key : ∀ (n : ℕ) (S : Finset (X → C)), S.card = n →
      Submodule.span C (↑S : Set (X → C)) = ⊤ →
      ∃ β : Matrix X X C, IsUnit β.det ∧
        Submodule.span R (↑S : Set (X → C)) = Submodule.span R (Set.range fun j x => β x j) from
    key _ S rfl hsp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hspC
  by_cases hli : LinearIndependent C (fun i : S => (i : X → C))
  · have hb := Module.Basis.mk hli (by simpa using hspC.ge)
    let e : X ≃ S := (hb.indexEquiv (Pi.basisFun C X)).symm
    refine ⟨Matrix.of fun x j => ((e j : S) : X → C) x, ?_, ?_⟩
    · refine (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)
      exact hli.comp e e.injective
    · congr 1
      ext f
      constructor
      · intro hf
        exact ⟨e.symm ⟨f, hf⟩, by ext x; simp⟩
      · rintro ⟨j, rfl⟩
        exact (e j).2
  · obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hli
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i))
      ⟨i1, Finset.mem_univ _⟩
    have hg0 : g i0 ≠ 0 := by
      intro h0
      have h2 := hmax i1 (Finset.mem_univ _)
      rw [h0, map_zero] at h2
      exact hi1 ((Valuation.zero_iff v).1 (le_antisymm h2 zero_le))
    have key : (i0 : X → C) =
        ∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun i => g i • (i : X → C)) (Finset.mem_univ i0)
      rw [hg] at h1
      have h2 : g i0 • (i0 : X → C) = -∑ i ∈ Finset.univ.erase i0, g i • (i : X → C) :=
        eq_neg_of_add_eq_zero_left h1
      calc (i0 : X → C) = (g i0)⁻¹ • (g i0 • (i0 : X → C)) := by
            rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
        _ = _ := by
          rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, neg_smul, mul_comm]
    have hle1 : ∀ i, v (-(g i * (g i0)⁻¹)) ≤ 1 := by
      intro i
      rw [Valuation.map_neg, map_mul, map_inv₀]
      calc v (g i) * (v (g i0))⁻¹ ≤ v (g i0) * (v (g i0))⁻¹ :=
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ _)) zero_le
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 hg0)
    choose r hr using fun i => hv.exists_of_le_one (hle1 i)
    have hx0R : (i0 : X → C) ∈ Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      have hsum : (∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C)) ∈
          Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [← hr i, algebraMap_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Finset.mem_coe.2 (Finset.mem_erase.2
          ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩)
      rw [← key] at hsum
      exact hsum
    have hx0C : (i0 : X → C) ∈ Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) :=
      Submodule.span_le_restrictScalars R C _ hx0R
    have hS : (↑S : Set (X → C)) = insert (i0 : X → C) ↑(S.erase (i0 : X → C)) := by
      rw [← Finset.coe_insert, Finset.insert_erase i0.2]
    have hspR : Submodule.span R (↑S : Set (X → C)) =
        Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      rw [hS, Submodule.span_insert_eq_span hx0R]
    have hspC' : Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) = ⊤ := by
      rw [← hspC, hS, Submodule.span_insert_eq_span hx0C]
    obtain ⟨β, hβ, hβS⟩ := ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem i0.2)
      (S.erase (i0 : X → C)) rfl hspC'
    exact ⟨β, hβ, hspR.trans hβS⟩

private lemma cols_le_lemma_2 {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (A : Matrix X X R) (hA : Q = P * A.map (algebraMap R C)) :
    Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hcol : (fun x => Q x j) = ∑ i, A i j • fun x => P x i := by
    ext x
    simp [hA, Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun x => Q x j) ∈ Submodule.span R _
  rw [hcol]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem inv_mem_of_valuation_eq_one (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (A : Submodule R (X → C)) (P : Matrix X X C) (hP : IsUnit P.det)
    (hA : A = Submodule.span R (Set.range fun j x => P x j))
    (one : (1 : X → C) ∈ A) (mul : ∀ f g, f ∈ A → g ∈ A → f * g ∈ A)
    (u : X → C) (hu : u ∈ A) (hunit : ∀ x, v (u x) = 1) : u⁻¹ ∈ A := by
  have hu0 : ∀ x, u x ≠ 0 := fun x h0 => by simpa [h0] using hunit x
  have hPA : ∀ j, (fun x => P x j) ∈ A := fun j => by
    rw [hA]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcolD : ∀ j, (fun x => (Matrix.diagonal u * P) x j) = u * fun x => P x j := by
    intro j; ext x; simp [Matrix.diagonal_mul]
  have hDle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (fun x => (Matrix.diagonal u * P) x j) ∈ Submodule.span R _
    rw [hcolD, ← hA]
    exact mul u _ hu (hPA j)
  obtain ⟨T, hT⟩ := cols_mul_lemma hDle
  have hdT : algebraMap R C T.det = ∏ x, u x := by
    have e := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_map_algebraMap] at e
    exact mul_left_cancel₀ hP.ne_zero (by rw [← e]; ring)
  have hvT : v (algebraMap R C T.det) = 1 := by
    rw [hdT, map_prod]
    exact Finset.prod_eq_one fun x _ => hunit x
  have hy : algebraMap R C T.det ≠ 0 := by
    rw [hdT]; exact Finset.prod_ne_zero_iff.2 fun x _ => hu0 x
  obtain ⟨s, hs⟩ := hv.exists_of_le_one
    (show v (algebraMap R C T.det)⁻¹ ≤ 1 from le_of_eq (by rw [map_inv₀, hvT, inv_one]))
  have hTs : T.det * s = 1 := hv.hom_inj (by rw [map_mul, hs, mul_inv_cancel₀ hy, map_one])
  have hTu : IsUnit T.det := ⟨⟨T.det, s, hTs, by rw [mul_comm]; exact hTs⟩, rfl⟩
  have hPD : P = (Matrix.diagonal u * P) * (T⁻¹).map (algebraMap R C) := by
    rw [hT, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv T hTu]
    simp
  have hPle := cols_le_lemma_2 _ hPD
  have hmem : (1 : X → C) ∈
      Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) :=
    hPle (by rw [← hA]; exact one)
  have hle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      A.comap (LinearMap.mulLeft R u⁻¹) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    convert hPA j using 1
    ext x
    simp [Matrix.diagonal_mul, hu0 x]
  simpa using hle hmem

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.ProdEraseUpdate
section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]

def xc (k : Type) [Field k] [CharP k p] (i : ι) (x : ι → ZMod p) : k :=
  ZMod.castHom (dvd_refl p) k (x i)

def lam (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) : k := ∑ i, Cm j i * xc k i x

def monF (Cm : Matrix ι ι k) (α : ι → ZMod p) (x : ι → ZMod p) : k :=
  ∏ j, lam Cm j x ^ (α j).val

theorem xc_pow (i : ι) (x : ι → ZMod p) : xc k i x ^ p = xc k i x := by
  simp only [xc, ← map_pow, ZMod.pow_card]

theorem lam_pow (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) :
    lam Cm j x ^ p = ∑ i, Cm j i ^ p * xc k i x := by
  simp only [lam, sum_pow_char, mul_pow, xc_pow]

theorem xc_eq (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (i : ι) (x : ι → ZMod p) :
    xc k i x = ∑ m, Cinv i m * lam Cm m x := by
  have e : ∀ i', ∑ m, Cinv i m * Cm m i' = (1 : Matrix ι ι k) i i' := by
    intro i'; rw [← h, Matrix.mul_apply]
  simp only [lam, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, e, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

def MulStable (S : Submodule k ((ι → ZMod p) → k)) (h : (ι → ZMod p) → k) : Prop :=
  ∀ f ∈ S, h * f ∈ S

theorem monF_split (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (x : ι → ZMod p) :
    monF Cm α x = lam Cm l x ^ (α l).val * ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  unfold monF
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ l)).symm

theorem prod_erase_update (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (a : ZMod p)
    (x : ι → ZMod p) :
    ∏ j ∈ univ.erase l, lam Cm j x ^ (Function.update α l a j).val =
      ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem sum_erase_update (α : ι → ZMod p) (l : ι) (a : ZMod p) :
    ∑ j ∈ univ.erase l, (Function.update α l a j).val = ∑ j ∈ univ.erase l, (α j).val := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem key_step (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    ∀ (N : ℕ) (α : ι → ZMod p), ∑ j, (α j).val = N → ∀ l,
      (fun x => lam Cm l x * monF Cm α x) ∈
        Submodule.span k (Set.range (monF (p := p) Cm)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro α hα l
  have hlt : (α l).val < p := ZMod.val_lt (α l)
  by_cases hcase : (α l).val + 1 < p
  ·
    have hv : (α l + 1).val = (α l).val + 1 := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt hcase]
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        monF Cm (Function.update α l (α l + 1)) := by
      funext x
      rw [monF_split Cm α l x, monF_split Cm (Function.update α l (α l + 1)) l x,
        prod_erase_update, Function.update_self, hv, pow_succ]
      ring
    rw [hfun]
    exact Submodule.subset_span ⟨_, rfl⟩
  ·
    have hval : (α l).val = p - 1 := by omega
    have hsplit : (α l).val + ∑ j ∈ univ.erase l, (α j).val = ∑ j, (α j).val :=
      Finset.add_sum_erase univ (fun j => (α j).val) (Finset.mem_univ l)
    have hsplitγ : (Function.update α l 0 l).val +
        ∑ j ∈ univ.erase l, (Function.update α l 0 j).val =
        ∑ j, (Function.update α l 0 j).val :=
      Finset.add_sum_erase univ (fun j => (Function.update α l 0 j).val) (Finset.mem_univ l)
    have hγl : (Function.update α l 0 l).val = 0 := by simp
    have hse := sum_erase_update α l 0
    have hlow : ∑ j, (Function.update α l 0 j).val < N := by omega
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        ∑ i, ∑ m, (Cm l i ^ p * Cinv i m) •
          (fun x => lam Cm m x * monF Cm (Function.update α l 0) x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : monF Cm α x = lam Cm l x ^ (p - 1) * monF Cm (Function.update α l 0) x := by
        rw [monF_split Cm α l x, monF_split Cm (Function.update α l 0) l x, prod_erase_update,
          Function.update_self, ZMod.val_zero, pow_zero, one_mul, hval]
      have e2 : lam Cm l x * lam Cm l x ^ (p - 1) = lam Cm l x ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
      rw [e1, ← mul_assoc, e2, lam_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [xc_eq Cm Cinv h i x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hfun]
    refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_))
    exact ih _ hlow _ rfl m

theorem monF_zero (Cm : Matrix ι ι k) : monF Cm (0 : ι → ZMod p) = 1 := by
  funext x
  simp [monF]

theorem mulStable_lam (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (l : ι) :
    MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (lam Cm l) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, rfl⟩ := hg
    exact key_step Cm Cinv h _ α rfl l
  | zero => simpa using Submodule.zero_mem _
  | add f g _ _ hf hg => rw [mul_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hf

theorem MulStable.add {S : Submodule k ((ι → ZMod p) → k)} {h₁ h₂ : (ι → ZMod p) → k}
    (a : MulStable S h₁) (b : MulStable S h₂) : MulStable S (h₁ + h₂) := by
  intro f hf
  rw [add_mul]
  exact S.add_mem (a f hf) (b f hf)

theorem MulStable.mul {S : Submodule k ((ι → ZMod p) → k)} {h₁ h₂ : (ι → ZMod p) → k}
    (a : MulStable S h₁) (b : MulStable S h₂) : MulStable S (h₁ * h₂) := by
  intro f hf
  rw [mul_assoc]
  exact a _ (b f hf)

theorem MulStable.const (S : Submodule k ((ι → ZMod p) → k)) (c : k) :
    MulStable S (fun _ => c) := by
  intro f hf
  have e : (fun _ => c) * f = c • f := by funext x; simp
  rw [e]
  exact S.smul_mem c hf

theorem MulStable.sum {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∑ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f _
    simp
  · intro j s hj ih a
    rw [Finset.sum_insert hj]
    exact (a j (Finset.mem_insert_self j s)).add (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

theorem MulStable.prod {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∏ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f hf
    simpa using hf
  · intro j s hj ih a
    rw [Finset.prod_insert hj]
    exact (a j (Finset.mem_insert_self j s)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

theorem MulStable.pow {S : Submodule k ((ι → ZMod p) → k)} {h : (ι → ZMod p) → k}
    (a : MulStable S h) (n : ℕ) : MulStable S (h ^ n) := by
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih => rw [pow_succ]; exact ih.mul a

def delta (k : Type) [Field k] [CharP k p] (y : ι → ZMod p) : (ι → ZMod p) → k :=
  ∏ i, ((fun _ => (1 : k)) + (fun _ => (-1 : k)) *
    ((fun x => xc k i x) + (fun _ => -ZMod.castHom (dvd_refl p) k (y i))) ^ (p - 1))

theorem delta_apply (y x : ι → ZMod p) : delta k y x = if x = y then 1 else 0 := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hfac : ∀ i, (1 : k) + -1 * (xc k i x + -ZMod.castHom (dvd_refl p) k (y i)) ^ (p - 1) =
      if x i = y i then 1 else 0 := by
    intro i
    have e : xc k i x + -ZMod.castHom (dvd_refl p) k (y i) =
        ZMod.castHom (dvd_refl p) k (x i - y i) := by
      simp [xc, sub_eq_add_neg]
    rw [e, ← map_pow]
    by_cases hxy : x i = y i
    · simp [hxy, zero_pow hp1]
    · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hxy)]
      simp [hxy]
  simp only [delta, Finset.prod_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, hfac]
  rw [Finset.prod_boole]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hn : ¬ ∀ i ∈ (univ : Finset ι), x i = y i := fun hall => hxy (funext fun i => hall i (mem_univ i))
    rw [if_neg hn, if_neg hxy]

theorem span_monF_eq_top (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    Submodule.span k (Set.range (monF (p := p) Cm)) = ⊤ := by
  have hxc : ∀ i, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (fun x => xc k i x) := by
    intro i
    have e : (fun x => xc k i x) = ∑ m, (fun _ => Cinv i m) * lam Cm m := by
      funext x
      rw [xc_eq Cm Cinv h i x]
      simp [Finset.sum_apply]
    rw [e]
    exact MulStable.sum (fun m _ => (MulStable.const _ _).mul (mulStable_lam Cm Cinv h m))
  have hdelta : ∀ y, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (delta k y) := by
    intro y
    unfold delta
    exact MulStable.prod (fun i _ => (MulStable.const _ 1).add
      ((MulStable.const _ (-1)).mul (((hxc i).add (MulStable.const _ _)).pow _)))
  have h1 : (1 : (ι → ZMod p) → k) ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := by
    rw [← monF_zero Cm]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hmem : ∀ y, delta k y ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := fun y => by
    simpa using hdelta y 1 h1
  rw [eq_top_iff]
  intro f _
  have e : f = ∑ y, f y • delta k y := by
    funext x
    simp [Finset.sum_apply, delta_apply]
  rw [e]
  exact Submodule.sum_mem _ (fun y _ => Submodule.smul_mem _ _ (hmem y))

theorem det_monF_ne_zero (Cm : Matrix ι ι k) (hC : IsUnit Cm.det) :
    (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x).det ≠ 0 := by
  have hspan := span_monF_eq_top (p := p) Cm Cm⁻¹ (Matrix.nonsing_inv_mul Cm hC)
  have hli : LinearIndependent k
      (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) := by
    have hcols : (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) =
        monF (p := p) Cm := by
      funext α x
      simp [Matrix.transpose_apply]
    rw [hcols]
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
    simp
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end ReciprocityTheory.PGsh.Up
end
end

