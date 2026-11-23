module

public import Mathlib

@[expose] public section

open scoped BigOperators

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

variable {ι : Type} {dim : ι → ℕ} {n : ℕ}

section Operator

variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def wordDeriv (dir : Λ → W) (l : List Λ) (F : W → ℂ) (p : W) : ℂ :=
  iteratedFDeriv ℂ l.length F p fun j => dir (l.get j)

def applyAt (dir : Λ → W) (P : MvPolynomial Λ ℂ) (F : W → ℂ) (p : W) : ℂ :=
  ∑ μ ∈ P.support, P.coeff μ * wordDeriv dir (Finsupp.toMultiset μ).toList F p

theorem iteratedFDeriv_directions_comp_perm_of_analyticAt (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {k : ℕ} (u v : Fin k → Λ) (σ : Equiv.Perm (Fin k)) (h : u = v ∘ σ) :
    iteratedFDeriv ℂ k F p (fun j => dir (u j)) = iteratedFDeriv ℂ k F p (fun j => dir (v j)) := by
  subst h
  exact (hF.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (fun j => dir (v j)) σ

theorem wordDeriv_perm (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {l l' : List Λ} (h : l.Perm l') : wordDeriv dir l F p = wordDeriv dir l' F p := by
  have key : ∀ {l l' : List Λ}, l.Perm l' →
      ∃ e : Fin l.length ≃ Fin l'.length, ∀ j, l.get j = l'.get (e j) := by
    intro l l' h
    induction h with
    | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
    | cons x _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm), ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simpa using he j
    | swap x y l =>
      refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
      · simp
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
        simp
    | trans _ _ ih₁ ih₂ =>
      obtain ⟨e₁, h₁⟩ := ih₁
      obtain ⟨e₂, h₂⟩ := ih₂
      exact ⟨e₁.trans e₂, fun j => by rw [h₁, h₂]; rfl⟩
  obtain ⟨e, he⟩ := key h
  have hl := h.length_eq
  unfold wordDeriv
  have gen : ∀ (a b : ℕ) (_ : a = b) (u : Fin a → Λ) (v : Fin b → Λ) (e : Fin a ≃ Fin b),
      (∀ j, u j = v (e j)) → iteratedFDeriv ℂ a F p (fun j => dir (u j)) =
        iteratedFDeriv ℂ b F p (fun j => dir (v j)) := by
    intro a b hab u v e he
    subst hab
    exact iteratedFDeriv_directions_comp_perm_of_analyticAt dir hF u v e (funext he)
  exact gen _ _ hl _ _ e he

end Operator

section Columns

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Columns

def gDim (f r : ℕ) : ℕ := f * r

def bigR (rd : ℝ) : ℝ := rd ^ 7

def dStar (f m : ℕ) : ℕ := 2 * f * m

def omStar (f : ℕ) (rd : ℝ) : ℝ := 2 * (f : ℝ) ^ ((3 : ℝ) / 2) * rd

def thSq (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := f * R₀ ^ 2 * bigR rd ^ 3 / q

def bZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q / (R₀ ^ 2 * bigR rd ^ 4)

def tZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q * bZero rd q R₀

def mOne (f m : ℕ) (rd : ℝ) : ℝ := 90 * (m : ℝ) ^ 2 * (dStar f m : ℝ) ^ 2 * rd

structure Params {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ) where
  q : ℕ
  R₀ : ℝ
  m : ℕ
  one_le_m : 1 ≤ m
  min_dim_le : ∃ s, dim s ≤ m
  m_pow_le : m ^ 4 ≤ f
  f_sq_le : (f : ℝ) ^ 2 ≤ rd
  sixteen_le : 16 ≤ rd
  two_le_fr : 2 ≤ f * r
  three_le_q : 3 ≤ q
  one_le_D : 1 ≤ D
  one_le_n : 1 ≤ n
  R₀_pos : 0 < R₀
  R₀_sq : max (270 : ℝ) (90 * ((gDim f r : ℝ) + D)) ≤ R₀ ^ 2
  threshold_lt : (dStar f m : ℝ) ^ 2 * omStar f rd * thSq f rd q R₀ < 1
  one_le_bZero : 1 ≤ bZero rd q R₀
  mOne_le : mOne f m rd ≤ (q : ℝ) / 2
  D_le_q : D ≤ q
  tZero_ge_log : 4 * (D : ℝ) * (7 + Real.log ((q : ℝ) * D)) + (dStar f m : ℝ) + 1 ≤ tZero rd q R₀
  tZero_ge_rank : (gDim f r : ℝ) * Real.log 2 + 2 * (dStar f m : ℝ) + 3 +
    ((D : ℝ) + 1) * ((r : ℝ) * Real.log r + 3 * r + 3) ≤ tZero rd q R₀

namespace Params

variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)

end Params

end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
