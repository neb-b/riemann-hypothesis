module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvaria
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj.FlatDep
open GlobalTheory.RootEx

variable {k : Type} [Field k]

theorem stepPt_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) :
    stepPt (x₀ + a₀) u = stepPt x₀ u + fromBlocks a₀ 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> (simp [stepPt, basePt]; try abel)

variable {G : Grid k}

theorem colVar_add (x a : ColArgs G) (u : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) :
    colVar (x + a) u j r = colVar x u j r := by
  simp [colVar, stepPt_add]

theorem rowVar_add (x a : ColArgs G) (u : Vars G) (j : ℕ) (s : Fin (topRank G j)) :
    rowVar (x + a) u j s = rowVar x u j s + if j < G.m - 1 then 0 else a j (topLast G (j + 1)) s := by
  unfold rowVar
  split_ifs with h
  · simp [stepPt_add]
  · simp

theorem ch_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) : ch (stepPt (x₀ + a₀) u) = ch (stepPt x₀ u) := by
  simp [ch, stepPt_add]

theorem phase_add (x a : ColArgs G) (u : Vars G) : phase (x + a) u = phase x u +
    ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0 else
      a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0 := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, ch_add]
  by_cases hE : Even (G.m - 2 - (j : ℕ))
  · simp only [if_pos hE, rowVar_add, colVar_add, add_mul, Finset.sum_add_distrib, add_assoc]
  · simp only [if_neg hE, add_zero]

section Loc
variable [ValuativeRel k] (hs : 1 ≤ G.s)

omit [ValuativeRel k] in
theorem mem_opp_theta {j : ℕ} (hj : j < G.m) : Edge.theta G.m j ∈ oppositePath G.m := by
  simp [oppositePath]; omega

omit [ValuativeRel k] in
theorem mem_opp {b : Edge} (hb : b ∈ oppositePath G.m) :
    (∃ i, i < G.m ∧ b = .ex i G.m) ∨ ∃ j, j < G.m ∧ b = .theta G.m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact .inl ⟨i, hi, rfl⟩
  · exact .inr ⟨j, hj, rfl⟩

omit [ValuativeRel k] in
theorem downMap_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) {j : ℕ} (hj : j < G.m) :
    downMap hs x u j = downMap hs x' u j := by
  unfold downMap; rw [hx j hj]

omit [ValuativeRel k] in
theorem fill_congr {x x' : ColArgs G} {y y' : RowArgs G} (hx : ∀ j, j < G.m → x j = x' j)
    (hy : ∀ i, i < G.m → y i = y' i) (u : Vars G) {b : Edge} (hb : b ∈ oppositePath G.m) :
    fill hs x y u b = fill hs x' y' u b := by
  rcases mem_opp hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [fill_ex, fill_ex, hy i hi]
  · rw [fill_theta, fill_theta, downMap_congr hs hx u hj]

omit [ValuativeRel k] in
theorem phase_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) :
    phase x u = phase x' u := by
  unfold phase colVar rowVar
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := hx j (by have := j.2; omega)
  have h2 := hx (j + 1) (by have := j.2; omega)
  rw [h1, h2]

theorem fromBlocks_le {n n' m m' : Type*} {A : Matrix n n' k} {t : ValueGroupWithZero k}
    (hA : ∀ r s, valuation k (A r s) ≤ t) (r : n ⊕ m) (s : n' ⊕ m') :
    valuation k (fromBlocks A 0 0 (0 : Matrix m m' k) r s) ≤ t := by
  rcases r with r | r <;> rcases s with s | s <;> simp [hA]

theorem fill_sub_le {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((fill hs (x + a) (y + b) u - fill hs x y u) c r s) ≤ t := by
  rcases mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Pi.sub_apply, fill_ex, Matrix.sub_apply, transpose_apply, Pi.add_apply, Matrix.add_apply,
      add_sub_cancel_left]
    exact hb i hi s r
  · simp only [Pi.sub_apply, fill_theta, Matrix.sub_apply, transpose_apply]
    unfold downMap
    split_ifs with h h'
    · simp only [reindex_apply, submatrix_apply, Pi.add_apply, stepPt_add, Matrix.add_apply, add_sub_cancel_left]
      exact fromBlocks_le (ha j hj) _ _
    · simp only [submatrix_apply, Pi.add_apply, Matrix.add_apply, add_sub_cancel_left]
      exact ha j hj _ _
    · simp

omit [ValuativeRel k] in
theorem exists_colVar_eq (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j : Fin (G.m - 1))
    (r : Fin (topRank G (j + 1))) : ∃ p q, colVar x u j r = fill hs x y u (.theta G.m j) p q := by
  refine ⟨frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega)
      (.inr ⟨(G.m - 2 - j) / 2, by omega⟩),
    frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) (.inl r), ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, colVar, Fin.eta]

end Loc
end GlobalTheory.FunObj.FlatDep

open GlobalTheory.FunObj.FlatDep in
theorem GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hψ hT
  obtain ⟨n, hA, hB⟩ := _root_.GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨fun x x' y y' hx hy => ?_, n, fun x a y b ha hb => ?_⟩
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    rw [phase_congr hx u]
    have hTe : T (G.moveArgs .one g (fill hs x y u)) = T (G.moveArgs .one g (fill hs x' y' u)) :=
      hT.1 fun c hc => by simp only [Grid.moveArgs, fill_congr hs hx hy u hc]
    simp only [moved, Grid.pathAct, hTe]
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    have hS : moved G keep g T (fill hs (x + a) (y + b) u) = moved G keep g T (fill hs x y u) := by
      have h := hB (fill hs x y u) (fill hs (x + a) (y + b) u - fill hs x y u)
        fun c hc r s => fill_sub_le hs ha hb u hc r s
      rwa [add_sub_cancel] at h
    rw [hS]
    by_cases h0 : moved G keep g T (fill hs x y u) = 0
    · simp [h0]
    have hbd := hA _ h0
    have hD : ∀ (j : Fin (G.m - 1)) r, valuation k ((if (j : ℕ) + 1 < G.m - 1 then 0 else
        a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r) ≤ 1 := by
      intro j r
      have := j.2
      split_ifs with h
      · simp
      · obtain ⟨p, q, hpq⟩ := exists_colVar_eq hs x y u j r
        rw [map_mul, hpq]
        calc _ ≤ valuation k ((ϖ ^ n : kˣ) : k) * valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) :=
              mul_le_mul' (ha _ (by omega) _ _) (hbd _ (mem_opp_theta (by omega)) _ _)
          _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hsum : valuation k (-(∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0
        else a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0)) ≤ valuation k ((1 : kˣ) : k) := by
      rw [Valuation.map_neg, Units.val_one, map_one]
      refine (valuation k).map_sum_le fun j _ => ?_
      by_cases hE : Even (G.m - 2 - (j : ℕ))
      · rw [if_pos hE]; exact (valuation k).map_sum_le fun r _ => hD j r
      · rw [if_neg hE, map_zero]; exact zero_le'
    rw [phase_add, neg_add, AddChar.map_add_eq_mul, (hψ 1).2 le_rfl _ hsum, mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatLast

open GlobalTheory.RootEx

section Step
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


open Classical in
theorem stepPt_add_apply (x₀ : Matrix n n' k) (e δ : StepVar n c n' → k) (a : n ⊕ Fin c) (b : n' ⊕ Fin (c + 1)) :
    stepPt x₀ (e + δ) a b =
      stepPt x₀ e a b + if h : Free (c / 2 + 1) (a, b) ∨ Kept (a, b) then δ ⟨(a, b), h⟩ else 0 := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

end Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}


open Classical in
def shiftVar (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) : Vars G := fun j w =>
  if j = j₀ ∧ Sum.elim (fun a : Fin (topRank G (j + 1)) => (a : ℕ) = r) (fun _ => False) w.1.1 ∧
    w.1.2.isRight = true then t else 0

theorem valuation_shiftVar_le (j₀ : Fin (G.m - 1)) (r : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    (j : Fin (G.m - 1)) (w) : valuation k (shiftVar j₀ r t j w) ≤ valuation k s₀ := by
  unfold shiftVar
  split_ifs
  · exact ht
  · simp

theorem ch_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : Fin (G.m - 1)) :
    ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) = ch (stepPt (x j) (e j)) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, stepPt_add_apply]
  split_ifs <;> simp [shiftVar]

theorem rowVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : ℕ) (s) :
    rowVar x (e + shiftVar j₀ r t) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Pi.add_apply, stepPt_add_apply]
      split_ifs <;> simp [shiftVar]
    · rfl
  · rfl

theorem colVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m) (r : ℕ) (t : k)
    (j : Fin (G.m - 1)) (r' : Fin (topRank G (j + 1))) :
    colVar x (e + shiftVar j₀ r t) j r' = colVar x e j r' + if j = j₀ ∧ (r' : ℕ) = r then t else 0 := by
  unfold colVar
  rw [Pi.add_apply, stepPt_add_apply]
  congr 1
  by_cases hj : j = j₀
  · subst hj
    rw [dite_eq_left (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]
    simp [shiftVar]
  · simp [shiftVar, hj]

theorem phase_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) (t : k) :
    phase x (e + shiftVar j₀ r t) = phase x e + rowVar x e ((j₀ : ℕ) + 1) r * t := by
  unfold phase
  have key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) +
      if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' *
        colVar x (e + shiftVar j₀ r t) j r' else 0) =
      (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * colVar x e j r' else 0) +
      if j = j₀ then rowVar x e ((j₀ : ℕ) + 1) r * t else 0 := by
    intro j
    rw [ch_shift]
    simp only [rowVar_shift, colVar_shift x e j₀ hj₀]
    by_cases hj : j = j₀
    · subst hj
      have hev : Even (G.m - 2 - (j : ℕ)) := by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos rfl]
      simp only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]
      congr 2
      simp_rw [Fin.val_inj, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

variable (hs : 1 ≤ G.s)

theorem valuation_downMap_sub_le (x : ColArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (j : ℕ) (a b) :
    valuation k (downMap hs x (e + δ) j a b - downMap hs x e j a b) ≤ valuation k s₀ := by
  classical
  unfold downMap
  split_ifs with h1 h2
  · simp only [reindex_apply, submatrix_apply, Pi.add_apply]
    rw [stepPt_add_apply, add_sub_cancel_left]
    split_ifs
    · exact hδ _ _
    · simp
  · simp
  · simp

theorem valuation_fill_sub_le (x : ColArgs G) (y : RowArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (b : Edge) (r s) :
    valuation k ((fill hs x y (e + δ) - fill hs x y e) b r s) ≤ valuation k s₀ := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp only [Matrix.sub_apply, transpose_apply, submatrix_apply]
      exact valuation_downMap_sub_le hs x e δ hδ j _ _
    · simp
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp
    · simp

end GlobalTheory.FunObj.FlatLast

namespace GlobalTheory.FunObj.FlatLast
open GlobalTheory.RootEx

theorem flatTensor_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  intro k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT
  obtain ⟨n, -, hper⟩ := GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨n, fun x y hF => ?_⟩
  let j₀ : Fin (G.m - 1) := ⟨G.m - 2, by omega⟩
  have hj₀ : (j₀ : ℕ) + 2 = G.m := by simp only [j₀]; omega
  suffices key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)),
      valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by
    have h : G.m - 1 = (j₀ : ℕ) + 1 := by omega
    rw [h]
    exact key
  intro r
  by_contra hlt
  have hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹) := by
    simpa [cball] using hlt
  obtain ⟨t, ht, hne⟩ := hψ.exists_ne_one (ϖ ^ n) hu
  set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def
  have hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u := fun e' => by
    rw [rowVar, dite_eq_right (by omega)]
  let δ : Vars G := shiftVar j₀ r (-t)
  have hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k) :=
    valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)
  have hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e') := fun e' => by
    have := hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e')
      (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)
    rwa [add_sub_cancel] at this
  have hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) =
      (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' := fun e' => by
    unfold flatIntegrand
    rw [hS, phase_shift x e' j₀ hj₀ r (-t), hrow,
      show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hFeq : flatTensor hs ψ ν (moved G keep g T) x y =
      (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y := by
    have : SigmaFinite ν := inferInstance
    have : ν.IsAddRightInvariant := inferInstance
    have : (varsVol G ν).IsAddRightInvariant := by unfold varsVol; infer_instance
    unfold flatTensor
    calc ∫ e', flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν)
        = ∫ e', flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) ∂(varsVol G ν) :=
          (integral_add_right_eq_self _ δ).symm
      _ = ∫ e', (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν) := by simp_rw [hI]
      _ = _ := integral_const_mul (ψ (t * u) : ℂ) _
  have hne' : (ψ (t * u) : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have : (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0 := by
    rw [sub_mul, one_mul, ← hFeq, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact hne' (sub_eq_zero.1 h).symm
  · exact hF h

end GlobalTheory.FunObj.FlatLast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBounded
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem abs_log_sum_pow_le {D : ℕ} (v : Fin (D + 1) → ℝ) (hv : ∀ l, 0 ≤ v l) {m M : ℝ} (hm : 0 < m) (hM : 1 ≤ M)
    (hvM : ∀ l, v l ≤ M) (hvm : ∃ l, m ≤ v l) {e n : ℕ} (he : 0 < e) (hn : 1 ≤ n) :
    |((e : ℝ) * n)⁻¹ * Real.log (∑ l, v l ^ (2 * n))| ≤ Real.log (D + 1) + 2 * Real.log M + 2 * |Real.log m| := by
  obtain ⟨l₀, hl₀⟩ := hvm
  have hD : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hM' : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlo : m ^ (2 * n) ≤ ∑ l, v l ^ (2 * n) :=
    (pow_le_pow_left₀ hm.le hl₀ _).trans
      (Finset.single_le_sum (f := fun l => v l ^ (2 * n)) (fun l _ => pow_nonneg (hv l) _) (Finset.mem_univ l₀))
  have hhi : ∑ l, v l ^ (2 * n) ≤ (D + 1 : ℝ) * M ^ (2 * n) := by
    refine (Finset.sum_le_sum (g := fun _ => M ^ (2 * n)) fun l _ => pow_le_pow_left₀ (hv l) (hvM l) _).trans ?_
    simp
  have hp : 0 < m ^ (2 * n) := pow_pos hm _
  have h1 := Real.log_le_log hp hlo
  have h2 := Real.log_le_log (hp.trans_le hlo) hhi
  rw [Real.log_pow] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
  push_cast at h1 h2
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hen : (n : ℝ) ≤ e * n := le_mul_of_one_le_left (by linarith) he'
  have ha := abs_nonneg (Real.log m)
  have hb := neg_abs_le (Real.log m)
  rw [abs_mul, abs_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hen (by positivity))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hn') hD, mul_nonneg (sub_nonneg.2 hn') hM',
    mul_nonneg (sub_nonneg.2 hn') ha, mul_nonneg (zero_le_one.trans hn') (sub_nonneg.2 hb)]

theorem can_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  intro k _ X _ p D hX P e x hx
  have hnn : ∀ (σ : k →+* ℂ) (y : CxPts p σ) l, 0 ≤ P.nu e 0 σ y (x l) := fun σ y l => by
    rw [← norm_val]; exact norm_nonneg _
  have hc := fun l => (GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P e 0).2 (x l) (hx.mem l)
  choose C hC using fun l => (hc l).2
  have hlow : ∀ σ : k →+* ℂ, ∃ κ : ℝ, 0 < κ ∧ ∀ y : CxPts p σ, κ ≤ ∑ l, P.nu e 0 σ y (x l) := fun σ => by
    haveI := hX.compactSpace σ
    have hcont : Continuous fun y : CxPts p σ => ∑ l, P.nu e 0 σ y (x l) :=
      continuous_finsetSum _ fun l _ => (hc l).1 σ
    have hpos : ∀ y : CxPts p σ, 0 < ∑ l, P.nu e 0 σ y (x l) := fun y => by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      exact Finset.sum_pos' (fun l _ => hnn σ y l) ⟨l, Finset.mem_univ _,
        ((GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2⟩
    rcases isEmpty_or_nonempty (CxPts p σ) with h | h
    · exact ⟨1, one_pos, fun y => h.elim y⟩
    · obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
      exact ⟨_, hpos y₀, fun y => hy₀ (Set.mem_univ y)⟩
  choose κ hκ hκ' using hlow
  haveI := hX.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  have hs : 0 ≤ ∑ σ, (κ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hκ σ)).le
  have hκ₀ : ∀ σ, (1 + ∑ σ, (κ σ)⁻¹)⁻¹ ≤ κ σ := fun σ => by
    refine inv_le_of_inv_le₀ (hκ σ) ?_
    have := Finset.single_le_sum (f := fun σ => (κ σ)⁻¹) (fun σ _ => (inv_pos.2 (hκ σ)).le) (Finset.mem_univ σ)
    linarith
  have hs' : 0 ≤ ∑ l, |C l| := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hM : 1 ≤ 1 + ∑ l, |C l| := by linarith
  refine ⟨Real.log (D + 1) + 2 * Real.log (1 + ∑ l, |C l|) + 2 * |Real.log ((1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1))|, ?_,
    fun n hn σ y => abs_log_sum_pow_le _ (hnn σ y) (by positivity) hM (fun l => ?_) ?_ hx.pos hn⟩
  · have h1 : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    have h2 := Real.log_nonneg hM
    positivity
  · have := Finset.single_le_sum (f := fun l => |C l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    linarith [hC l σ y, le_abs_self (C l)]
  · obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ : Fin (D + 1) => (1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1 : ℝ)) (g := fun l => P.nu e 0 σ y (x l)) (by
        refine le_trans (le_of_eq ?_) ((hκ₀ σ).trans (hκ' σ y))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp)
    exact ⟨l, hl⟩

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  first
  | exact @GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc
  | intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he hr
    exact GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc S T ΛS ΛT βS βT P e n r
      hS.toIsLattice hT.toIsLattice hFS hFT he hr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (exact GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSliceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (B : Type) [CommRing B] (y : Sp B ⟶ S) (x : Over.mk y ⟶ A), (∃ t : (P.pull (lift (snd A (Over.mk y) ≫ x) (fst A (Over.mk y))).left).Gen, t.IsGen) → ∃ M : ℕ, 0 < M ∧ x ^ M = 1 := by
  first | (exact @GlobalTheory.KerTorsion.exists_pow_eq_one) | (exact GlobalTheory.KerTorsion.exists_pow_eq_one) | (intros; apply GlobalTheory.KerTorsion.exists_pow_eq_one <;> assumption)
end

