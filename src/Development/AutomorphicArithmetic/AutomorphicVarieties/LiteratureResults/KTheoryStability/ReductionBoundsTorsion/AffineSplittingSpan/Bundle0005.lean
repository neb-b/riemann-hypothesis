module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.AevalSlice
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PolynomialPseudoInverse

open NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem pow_slice (t : P) {a b : ℕ} (n : ℕ) (x : Bi P Q a b) (x' : Fin a → Q) :
    ((TcL t a b ^ n) x) x' = (mapOp (fun y => t⁻¹ * y * t) b ^ n) (x x') := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem aeval_slice (t : P) {a b : ℕ} (f : Polynomial ℝ) (x : Bi P Q a b) (x' : Fin a → Q) :
    (Polynomial.aeval (TcL t a b) f x) x' = Polynomial.aeval (mapOp (fun y => t⁻¹ * y * t) b) f (x x') := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, hp, hr]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, pow_slice]

theorem pinv_Tc (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (Tc (s u) F) := by
  intro g x y
  have hp : pr ((s u)⁻¹ * g * s u) = pr g := by
    rw [map_mul, map_mul, map_inv, hs, mul_assoc, hu (pr g), inv_mul_cancel_left]
  have key := hF ((s u)⁻¹ * g * s u) x (fun j => (s u)⁻¹ * y j * s u)
  rw [hp] at key
  show F (fun i => pr g * x i) (fun j => (s u)⁻¹ * (g * y j) * s u) = F x (fun j => (s u)⁻¹ * y j * s u)
  rw [← key]
  congr 1
  funext j
  group

def pinvT (pr : P →* Q) (a b : ℕ) : Submodule ℝ (Bi P Q a b) where
  carrier := {F | PInv pr F}
  add_mem' := fun {F G} hF hG g x y => by
    change F _ _ + G _ _ = F x y + G x y
    rw [hF g x y, hG g x y]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c F hF g x y => by
    change c • F _ _ = c • F x y
    rw [hF g x y]

theorem pinv_aeval (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} (f : Polynomial ℝ) {F : Bi P Q a b} (hF : PInv pr F) :
    PInv pr (Polynomial.aeval (TcL (s u) a b) f F) := by
  have hpow : ∀ n : ℕ, PInv pr ((TcL (s u) a b ^ n) F) := by
    intro n
    induction n with
    | zero => simpa using hF
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact pinv_Tc pr s hs u hu ih
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact (pinvT pr a b).add_mem hp hr
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact (pinvT pr a b).smul_mem c (hpow n)

end PositivityTheory.KB.SplitAffineSpectral.PolynomialPseudoInverse

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PolynomialPseudoInverse

variable {P Q : Type} [Group P] [Group Q]

theorem colKill (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    (q : ℕ) (f : Polynomial ℝ)
    (hf : ∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e)
    {a : ℕ} (x : Bi P Q (a + 1) (q + 2)) (hx : PInv pr x) (hv : dv x = 0) :
    ∃ E : Bi P Q (a + 1) (q + 1), PInv pr E ∧ Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x = dv E := by
  have hX : PInv pr (Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x) :=
    pinv_aeval pr s hs u hu f hx
  have hinv : ∀ z : Fin (a + 1) → Q, InvS (pr.ker : Set P) (x z) := by
    intro z g hg y
    have hg' : pr g = 1 := hg
    have h := hx g z y
    simpa [hg'] using h
  have hdz : ∀ z : Fin (a + 1) → Q, dc (x z) = 0 := fun z => congrFun hv z
  choose e he1 he2 using fun z => hf (x z) (hinv z) (hdz z)
  refine ⟨fun x' y => e (fun i => (x' 0)⁻¹ * x' i) (fun j => (s (x' 0))⁻¹ * y j), ?_, ?_⟩
  · intro g x' y
    show e (fun i => (pr g * x' 0)⁻¹ * (pr g * x' i)) (fun j => (s (pr g * x' 0))⁻¹ * (g * y j))
      = e (fun i => (x' 0)⁻¹ * x' i) (fun j => (s (x' 0))⁻¹ * y j)
    have hn : (fun i => (pr g * x' 0)⁻¹ * (pr g * x' i)) = fun i => (x' 0)⁻¹ * x' i := by
      funext i
      group
    rw [hn]
    have hk : (s (x' 0))⁻¹ * (s (pr g))⁻¹ * g * s (x' 0) ∈ (pr.ker : Set P) := by
      show pr ((s (x' 0))⁻¹ * (s (pr g))⁻¹ * g * s (x' 0)) = 1
      simp only [map_mul, map_inv, hs]
      group
    rw [← he1 _ _ hk (fun j => (s (x' 0))⁻¹ * y j)]
    congr 1
    funext j
    rw [map_mul]
    group
  · funext x' y
    have hpr : pr (s (x' 0))⁻¹ = (x' 0)⁻¹ := by rw [map_inv, hs]
    calc Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x x' y
        = Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x (fun i => pr (s (x' 0))⁻¹ * x' i)
            (fun j => (s (x' 0))⁻¹ * y j) := (hX (s (x' 0))⁻¹ x' y).symm
      _ = Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f (x (fun i => (x' 0)⁻¹ * x' i))
            (fun j => (s (x' 0))⁻¹ * y j) := by
          rw [hpr, aeval_slice]
      _ = dc (e (fun i => (x' 0)⁻¹ * x' i)) (fun j => (s (x' 0))⁻¹ * y j) := by
          rw [he2]
      _ = _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreRec
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem zz_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) (a c : ℕ) :
    zz pr (r • b) a c = r • zz pr b a c := rfl

theorem Wtop_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) :
    Wtop pr (r • b) = r • Wtop pr b := rfl

theorem QC.smul {n : ℕ} {b : (Fin (n + 1) → Q) → ℝ} (hb : QC b) (r : ℝ) : QC (r • b) := by
  refine ⟨fun g x => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hb.1 g x]
  · rw [dc_smul, hb.2, smul_zero]

def GoodS (pr : P →* Q) {p q : ℕ} (x : Bi P Q (p + 2) (q + 2)) : Prop :=
  ∃ n : ℕ, n = p + q + 2 ∧ ∃ b : (Fin (n + 1) → Q) → ℝ, QC b ∧
    ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
    PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ dh e = 0 ∧ x = dh (zz pr b (p + 1) (q + 2)) + dh w + dv e

def GoodT (pr : P →* Q) {q : ℕ} (x : Bi P Q 1 (q + 2)) : Prop :=
  ∃ b : (Fin (q + 2) → Q) → ℝ, QC b ∧ ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ dh e = 0 ∧ x = Wtop pr b + dv e

section Rec

variable (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g)
include hs

end Rec

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSplit
section
noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

theorem cat_fc_lo {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (i : ℕ) (hi : i < a + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc i l) = cat (fun l' : Fin a => x (fc i l')) z (m + 1) l := by
  have hv := fc_val i l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

theorem cat_fc_hi {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (j : ℕ) (hj : j < c + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc (a + 1 + j) l) = cat x (fun l' : Fin c => z (fc j l')) (m + 1) l := by
  have hv := fc_val (a + 1 + j) l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

private theorem fin_succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc (i : ℕ) l := by
  ext
  rw [fc_val]
  split_ifs with hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    rfl

theorem dc_cat {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (F : (Fin (m + 1) → Q) → ℝ)
    (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q) :
    dc F (cat x z (m + 2)) =
      (∑ i : Fin (a + 1), (-1 : ℝ) ^ (i : ℕ) * F (cat (fun l => x (i.succAbove l)) z (m + 1))) +
        (-1 : ℝ) ^ (a + 1) *
          ∑ j : Fin (c + 1), (-1 : ℝ) ^ (j : ℕ) * F (cat x (fun l => z (j.succAbove l)) (m + 1)) := by
  simp only [dc]
  simp_rw [fin_succAbove_eq_fc]
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (fun l => cat x z (m + 2) (fc k l))) (m + 2),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat (fun l => x (fc k l)) z (m + 1))) (a + 1),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat x (fun l => z (fc k l)) (m + 1))) (c + 1),
    show Finset.range (m + 2) = Finset.range ((a + 1) + (c + 1)) by congr 1; omega,
    Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    congr 2
    funext l
    exact cat_fc_lo h x z k (Finset.mem_range.1 hk) l
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [pow_add, mul_assoc]
    congr 3
    funext l
    exact cat_fc_hi h x z j (Finset.mem_range.1 hj) l

theorem cat_zero_left {Q : Type} [Group Q] {n : ℕ} (x : Fin 0 → Q) (z : Fin n → Q) : cat x z n = z := by
  funext i
  simp [cat]

theorem cat_zero_right {Q : Type} [Group Q] {n : ℕ} (x : Fin n → Q) (z : Fin 0 → Q) : cat x z n = x := by
  funext i
  simp [cat]

theorem cat_mul {Q : Type} [Group Q] {a c n : ℕ} (h : a + c = n) (g : Q) (x : Fin a → Q) (z : Fin c → Q) :
    cat (fun i => g * x i) (fun j => g * z j) n = fun i => g * cat x z n i := by
  funext i
  have hi := i.isLt
  simp only [cat]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem splitA : SplitA := by
  intro P Q _ _ pr q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (q + 1 + 2))
  rw [dc_cat (a := 0) (c := q + 1) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_left, Fin.val_zero, pow_zero, one_mul, zero_add,
    pow_one, Pi.zero_apply, add_zero] at h0
  simp only [Wtop, dv, dc, zz]
  change (b fun j => pr (y j)) =
    ∑ i : Fin (q + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat x (fun j => pr (y (i.succAbove j))) (q + 1 + 1))
  linarith

theorem splitS : SplitS := by
  intro P Q _ _ pr p q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (p + q + 2 + 2))
  rw [dc_cat (a := p + 1) (c := q + 1) (by omega)] at h0
  simp only [Pi.zero_apply] at h0
  simp only [dh, dv, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) *
      b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (p + q + 2 + 1)) =
    (-1 : ℝ) ^ (p + 1) * ∑ j : Fin (q + 2), (-1 : ℝ) ^ (j : ℕ) *
      b (cat x (fun l => pr (y (j.succAbove l))) (p + q + 2 + 1))
  linear_combination h0

theorem splitB : SplitB := by
  intro P Q _ _ pr N b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (N + 1 + 2))
  rw [dc_cat (a := N + 1) (c := 0) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_right, Fin.val_zero, pow_zero, one_mul, Pi.zero_apply, add_zero] at h0
  simp only [dh, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (N + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (N + 1 + 1)) = _
  linear_combination h0

theorem zInv : ZInv := by
  intro P Q _ _ pr n a c b hn hb g x y
  simp only [zz, map_mul]
  rw [cat_mul hn]
  exact hb (pr g) _

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EvCob
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral

namespace EvaluationCoboundary

open PositivityTheory.KB

theorem ev_eq {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) z := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem key {G : Type} [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ) (he : Inv (MonoidHom.id G) e)
    (g : Fin (j + 1) → G) :
    dC e (fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) =
      ev (MonoidHom.id G) e 1 (bd G j (Finsupp.single g 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ev_eq, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum,
    Finsupp.linearCombination_single, dC, Fin.sum_univ_succ]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.succAbove_zero, one_smul,
    Fin.val_zero, pow_zero, one_mul, map_smul, Finsupp.linearCombination_single, Fin.val_succ]
  congr 1
  · have h := he (g 0) fun i => Fin.partialProd (fun i => g i.succ) i
    simp only [MonoidHom.id_apply, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext i
    rw [Fin.partialProd_succ']
    rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.partialProd_contractNth]
    rfl

end EvaluationCoboundary

theorem evCob : EvCob := by
  intro G _ j e he z hz
  have h : ∀ w : Chn G (j + 1), ev (MonoidHom.id G) (dC e) 1 w =
      ev (MonoidHom.id G) e 1 (bd G j w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp [ev]
    | add a b ha hb =>
      rw [map_add (f := _), EvaluationCoboundary.ev_eq, map_add (f := _), ← EvaluationCoboundary.ev_eq, ← EvaluationCoboundary.ev_eq, ha, hb,
        EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq e (bd G j b), ← map_add, ← EvaluationCoboundary.ev_eq]
    | single g r =>
      rw [EvaluationCoboundary.ev_eq, Finsupp.linearCombination_single, EvaluationCoboundary.key j e he g,
        ← Finsupp.smul_single_one, map_smul, EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq, map_smul]
      rw [one_smul, ← map_smul, ← map_smul, Finsupp.smul_single_one]
  rw [h, hz]
  simp [ev]

end PositivityTheory.KB.SplitAffineSpectral

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.HhZero
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

theorem ru_eq (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : Ru u F = Tc (s u) (Rt (s u)⁻¹ F) := by
  funext x y
  unfold PInv at hF
  have h := hF (s u)⁻¹ (fun i => x i * u) y
  simp only [map_inv, hs] at h
  show F (fun i => x i * u) y = F x (fun j => (s u)⁻¹ * y j * s u * (s u)⁻¹)
  rw [← h]
  congr 1
  · funext i
    rw [hu (x i), inv_mul_cancel_left]
  · funext j
    group

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

