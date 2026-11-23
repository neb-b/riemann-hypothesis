module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrder
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalInduct

def psum {N : ℕ} (ν : Fin N → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i

def pot {N : ℕ} (ν : Fin N → ℤ) : ℤ := ∑ j ∈ Finset.range (N + 1), psum ν j

theorem psum_succ {N : ℕ} (ν : Fin N → ℤ) (i : Fin N) : psum ν (i + 1) = psum ν i + ν i := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin N => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter (fun j : Fin N => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem pot_lt {N : ℕ} {μ ν : Fin N → ℤ} (h : ∀ j, psum μ j ≤ psum ν j) (hne : μ ≠ ν) : pot μ < pot ν := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ ν i := by
    by_contra h'; push_neg at h'; exact hne (funext h')
  have hiN := i.isLt
  have : ∃ j ∈ Finset.range (N + 1), psum μ j < psum ν j := by
    by_contra h'; push_neg at h'
    have e1 : psum μ i = psum ν i := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    have e2 : psum μ (i + 1) = psum ν (i + 1) := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    rw [psum_succ, psum_succ, e1] at e2
    exact hi (by linarith)
  obtain ⟨j, hj, hlt⟩ := this
  exact Finset.sum_lt_sum (fun j _ => h j) ⟨j, hj, hlt⟩

theorem pot_nonneg {N : ℕ} {ν : Fin N → ℤ} (h : ∀ i, 0 ≤ ν i) : 0 ≤ pot ν :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ => h i

theorem pos_iff_lt {N : ℕ} {e : Fin N → ℤ} (ha : Antitone e) (i : Fin N) :
    0 < e i ↔ (i : ℕ) < (Finset.univ.filter fun j => 0 < e j).card := by
  first
  | exact @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | (apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card ..)

theorem nonneg_of_dom {N : ℕ} {ν e : Fin N → ℤ} (hν : Antitone ν) (he : ∀ i, 0 ≤ e i)
    (hle : ∀ j, psum ν j ≤ psum e j) (hsum : ∑ i, ν i = ∑ i, e i) (i : Fin N) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  have sν := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) ν
  have se := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) e
  have tν : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), ν j < 0 := by
    refine Finset.sum_neg (fun j hj => ?_) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact lt_of_le_of_lt (hν (Fin.le_def.2 hj)) hneg
  have te : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), e j :=
    Finset.sum_nonneg fun j _ => he j
  have := hle i
  unfold psum at this
  linarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torusElt_add' {N : ℕ} (ϖ : kˣ) (a b : Fin N → ℤ) :
    torusElt k (Fin N) ϖ (a + b) = torusElt k (Fin N) ϖ a * torusElt k (Fin N) ϖ b := by
  apply Units.ext
  rw [Units.val_mul, val_torusElt, val_torusElt, val_torusElt, diagonal_mul_diagonal]
  congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]

theorem torusElt_zero' {N : ℕ} (ϖ : kˣ) : torusElt k (Fin N) ϖ (fun _ => 0) = 1 := by
  apply Units.ext
  rw [val_torusElt]; simp

theorem torusElt_one_comm {N : ℕ} (ϖ : kˣ) (g : GL (Fin N) k) :
    g * torusElt k (Fin N) ϖ (fun _ => 1) = torusElt k (Fin N) ϖ (fun _ => 1) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_torusElt]
  ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem vanish_of_shift {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} (hc : c N ≠ 0) {h : GL (Fin N) k → ℂ}
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) (j : ℕ) (m : GL (Fin N) k)
    (hm : h (m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))) = 0) : h m = 0 := by
  induction j generalizing m with
  | zero => simpa [torusElt_zero'] using hm
  | succ j ih =>
    apply ih
    have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
    obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic Finset.univ))
    set z := torusElt k (Fin N) ϖ (fun _ => 1) with hzdef
    set m' := m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))
    have hsplit : torusElt k (Fin N) ϖ (fun _ => ((j + 1 : ℕ) : ℤ)) = torusElt k (Fin N) ϖ (fun _ => (j : ℤ)) * z := by
      rw [hzdef, ← torusElt_add']; congr 1
    have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
    have key := hT Finset.univ R hR m'
    have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
      intro g hg
      obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
      rw [hz] at *
      have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
        rw [torusElt_one_comm]; simp only [mul_assoc]; rfl
      rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
    rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hc

theorem vanish_dominant {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} {h : GL (Fin N) k → ℂ}
    (hcart : ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
      x = κ * torusElt k (Fin N) ϖ ν * κ')
    (hdom : ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
          (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i))
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R)
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (h1 : h 1 = 0) :
    ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torusElt k (Fin N) ϖ e) = 0 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih e ha he hpot
  have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
      h (torusElt k (Fin N) ϖ ν) = 0 := by
    intro ν hν hν0 hlt
    have h0 := pot_nonneg hν0
    exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
  by_cases hzero : ∀ i, e i = 0
  · have : e = fun _ => 0 := funext hzero
    rw [this, torusElt_zero', h1]
  push_neg at hzero
  obtain ⟨i₀, hi₀⟩ := hzero
  have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
  have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
  have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
  have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
    intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
  have hscard : s.card = n₀ := by
    rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
  set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
  have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
  have hμa : Antitone μ := by
    intro i j hij
    have := ha hij; have hi := he i; have hj := he j
    simp only [hμdef, hind]
    split_ifs <;> omega
  have hμ0 : ∀ i, 0 ≤ μ i := by
    intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
  have hμlt : pot μ < pot e := by
    apply pot_lt
    · intro j; unfold psum
      exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
    · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, if_pos hi₀pos] at this; omega
  have hμv := IH μ hμa hμ0 hμlt
  have hTe : torusElt k (Fin N) ϖ e = torusElt k (Fin N) ϖ μ * torusElt k (Fin N) ϖ (indic s) := by
    rw [← torusElt_add']; congr 1; funext i; exact (hμe i).symm
  have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
    rw [← hscard]; simp [indic]
  obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic s))
  have hsum := hT s R hR (torusElt k (Fin N) ϖ μ)
  rw [hμv, mul_zero] at hsum
  have hterm : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) = 0 ∨
      h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) := by
    intro g hg
    obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torusElt k (Fin N) ϖ μ * g)
    have hval : h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ ν) := by
      rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
    obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
    have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
    simp only [← hs] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hle : ∀ j, psum ν j ≤ psum e j := by
      intro j; have := hd2 j; simp only [hμe] at this; exact this
    have hsumeq : ∑ i, ν i = ∑ i, e i := by
      rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
    have hν0 := nonneg_of_dom hν he hle hsumeq
    by_cases hνe : ν = e
    · right; rw [hval, hνe]
    · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
  obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
  have hg₁ : h (torusElt k (Fin N) ϖ μ * g₁) = h (torusElt k (Fin N) ϖ e) := by
    have e1 : torusElt k (Fin N) ϖ μ * g₁ =
        torusElt k (Fin N) ϖ e * (g₁⁻¹ * (1 * torusElt k (Fin N) ϖ (indic s)))⁻¹ := by
      rw [hTe]; group
    rw [e1, (hK _ (inv_mem hg₁K) _).2]
  by_contra hx
  have hite : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) =
      if h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) then h (torusElt k (Fin N) ϖ e) else 0 := by
    intro g hg
    rcases hterm g hg with h0 | h0
    · rw [h0, if_neg (Ne.symm hx)]
    · rw [if_pos h0]; exact h0
  rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (R.filter fun g => h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e)).card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
  rcases mul_eq_zero.1 hsum with hc0 | hc0
  · exact hcard (by exact_mod_cast hc0)
  · exact hx hc0

theorem zonal_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 → (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ') → (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k, (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') → (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') → ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) → (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) → ∀ h : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) → h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  set j : ℕ := (∑ i, |ν i|).toNat with hj
  apply vanish_of_shift hc hK hT hex j
  rw [← torusElt_add']
  refine vanish_dominant hcart hdom hex hK hT h1 (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega

end GlobalTheory.ZonalInduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoreIffCollapsesWith
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.CollapseCompare

section Average
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]

end Average

section Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]

variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}






end Pointwise

section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}





variable [MeasurableSpace k] [BorelSpace k]

end Transport

section Normalise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)




theorem hasConductor_mulShift {ψ : AddChar k Circle} {β : kˣ} (h : HasConductor ψ β) :
    HasConductor (ψ.mulShift (β : k)) 1 := by
  have hβ : 0 < valuation k (β : k) := by simp [zero_lt_iff]
  intro x
  have h1 := h (β * x)
  rw [map_mul, mul_le_iff_le_one_right hβ] at h1
  rw [Units.val_one, map_one, ← h1]
  simp only [AddChar.mulShift_apply]
  refine ⟨fun H y hy => ?_, fun H y hy => H _ (by rw [map_mul]; exact mul_le_mul_right hy _)⟩
  have := H ((β⁻¹ : kˣ) * y) (by rwa [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hβ])
  simpa using this

variable [MeasurableSpace k] [BorelSpace k]

end Normalise

section Main

end Main

end GlobalTheory.CollapseCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneIsPositionOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.ToOnePos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem toOne_lin (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ (m + 1) l v) ∧ IsNEquiv ψ 1 σ l₁ := by
  intro m
  induction m with
  | zero => intro _ l hl; exact ⟨l, fun v => rfl, hl⟩
  | succ m ih =>
    intro hm l hl
    obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.1 l hl
    obtain ⟨l₁, hl₁v, hl₁⟩ := ih (by omega) l' hl'
    refine ⟨l₁, fun v => ?_, hl₁⟩
    rw [hl₁v, toOne_succ]
    congr 1
    funext w
    exact hl'v w

theorem toOne_bil (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ (m + 1) π σ b →
      ∃ b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b₁ φ v = toOne ν σ (m + 1) (b φ) v) ∧ IsPos ψ 1 π σ b₁ := by
  intro m
  induction m with
  | zero => intro _ b hb; exact ⟨b, fun φ v => rfl, hb⟩
  | succ m ih =>
    intro hm b hb
    obtain ⟨b', hb'v, hb'⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.2 P π b).2 hb
    obtain ⟨b₁, hb₁v, hb₁⟩ := ih (by omega) b' hb'
    refine ⟨b₁, fun φ v => ?_, hb₁⟩
    rw [hb₁v, toOne_succ]
    congr 1
    funext w
    exact hb'v φ w

variable {n' : Type} [Fintype n'] [DecidableEq n']

def omRep (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ 1 g Ψ.1,
        (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.2.1 1 g Ψ.1 Ψ.2⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g 1 Ψ.1 Ψ'.1
        simpa using this
      map_smul' := fun z Ψ => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g z Ψ.1 0
        have h0 : om μ 1 g (0 : Matrix n n' k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := by
    ext Ψ : 2
    exact (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).1 Ψ.1
  map_mul' g h := by
    ext Ψ : 2
    have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.1 1 1 g h Ψ.1
    simpa using this

theorem bilPos_iff (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (p : ℕ)
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : BilPos ψ μ p σ B ↔ IsPos ψ p (omRep μ hμ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRep μ hμ g Ψ := Subtype.ext hΨ
    subst this
    exact h2 g Ψ v

end GlobalTheory.PosOne.ToOnePos


open GlobalTheory.PosOne.ToOnePos in
theorem GlobalTheory.PosOne.toOne_isPosOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  refine ⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩
  obtain ⟨B₁, hB₁v, hB₁⟩ := toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)
  exact ⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilSourceActionAndSmooth
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne

noncomputable section
namespace GlobalTheory.PosOne.SrcAction

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def srcRep {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) 1 Φ.1 Ψ.1
        simpa using this
      map_smul' := fun z Φ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) z Φ.1 0
        have h0 : om μ g (1 : GL b k) (0 : Matrix b a k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (by
    show om μ (g * h) 1 Φ.1 = om μ g 1 (om μ h 1 Φ.1)
    rw [← om_mul, mul_one])

end GlobalTheory.PosOne.SrcAction

namespace GlobalTheory.PosOne
open GlobalTheory.PosOne.SrcAction

theorem isSrc_exists_isSmoothRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by
  intro k _ _ _ _ _ _ a b _ _ _ _ μ hμ
  refine ⟨⟨srcRep μ, fun g Φ => rfl⟩, fun ρ' hρ' Φ => ?_⟩
  have hO := (om_isSmoothRepresentation k a b μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL a k => ((g, 1) : GL a k × GL b k) :=
    continuous_id.prodMk continuous_const
  convert hO.preimage hc using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [← hρ' g Φ]
  exact Subtype.ext_iff

end GlobalTheory.PosOne
end
end

