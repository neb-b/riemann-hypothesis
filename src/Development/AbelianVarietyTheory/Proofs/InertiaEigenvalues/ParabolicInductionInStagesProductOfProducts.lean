module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure BR (k : Type) [Field k] (n : ℕ) : Type 1 where

  V : Type
  [ac : AddCommGroup V]
  [smul : Module ℂ V]

  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] BR.ac BR.smul

def one (w : IrrGL (k := k)) : BR k w.1 := ⟨_, w.rep⟩

def two {r t N : ℕ} (e : r + t = N) (A : BR k r) (C : BR k t) : BR k N :=
  ⟨_, ind₂ (stdSum e) (extTensor A.ρ C.ρ)⟩

def mp {d M : ℕ} (N : Fin d → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i)) : BR k M :=
  ⟨_, multiProd (stdBlocks N hM) fun i => (A i).ρ⟩

def pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : BR k N :=
  mp (fun i => (x i).1) hx fun i => one (x i)

def Iso {n : ℕ} (A C : BR k n) : Prop := Nonempty (A.ρ.Equiv C.ρ)

def Sm {n : ℕ} (A : BR k n) : Prop := IsSmooth A.ρ

theorem iso_refl {n : ℕ} (A : BR k n) : Iso A A := eqv_refl A.ρ

theorem iso_symm {n : ℕ} {A C : BR k n} (h : Iso A C) : Iso C A := eqv_symm (ρ := A.ρ) (σ := C.ρ) h

theorem iso_trans {n : ℕ} {A C D : BR k n} (h : Iso A C) (h' : Iso C D) : Iso A D :=
  eqv_trans (ρ := A.ρ) (σ := C.ρ) (τ := D.ρ) h h'

theorem sm_one (w : IrrGL (k := k)) : Sm (one w) := w.2.rep.smooth

theorem sm_pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : Sm (pr x hx) := isSmooth_prodIrr x hx

theorem two_congr {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : Iso A A') (h' : Iso C C') :
    Iso (two e A C) (two e A' C') :=
  ind₂_congr e (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := C.ρ) (σ₂ := C'.ρ) h h'

theorem two_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : BR k r) (C : BR k s) (D : BR k t) (s₁ : Sm A) (s₂ : Sm C) (s₃ : Sm D) :
    Iso (two h₂ (two h₁ A C) D) (two h₄ A (two h₃ C D)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ C.ρ D.ρ s₁ s₂ s₃

theorem mp_head {d T M : ℕ} (N : Fin (d + 1) → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i))
    (hT : ∑ i : Fin d, N i.succ = T) (e : N 0 + T = M) :
    Iso (mp N hM A) (two e (A 0) (mp (fun i : Fin d => N i.succ) hT fun i => A i.succ)) :=
  multiProd_head (d := N) (X := fun i => (A i).V) (fun i => (A i).ρ) (stdBlocks N hM) e
    (stdBlocks (fun i : Fin d => N i.succ) hT)

theorem two_unit {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (N : Fin 0 → ℕ) (hN : ∑ i, N i = t)
    (C : ∀ i, BR k (N i)) : Iso (two e A (mp N hN C)) A :=
  ind₂_unit_right e A.ρ hA (d := N) (X := fun i => (C i).V) (fun i => (C i).ρ) (stdBlocks N hN)

theorem two_unit_pr {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL (k := k))
    (hy : ∑ i, (y i).1 = t) : Iso (two e A (pr y hy)) A :=
  two_unit e A hA _ hy _

theorem pr_succ {a t N : ℕ} (z : Fin (a + 1) → IrrGL (k := k))
    (hx : ∑ i : Fin a, (z i.succ).1 = t) (hz : ∑ i, (z i).1 = N) (e : (z 0).1 + t = N) :
    Iso (pr z hz) (two e (one (z 0)) (pr (fun i : Fin a => z i.succ) hx)) :=
  mp_head (fun i => (z i).1) hz (fun i => one (z i)) hx e

theorem of_iso {d h : ℕ} (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) {M c : ℕ} (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M) (z : Fin c → IrrGL (k := k)) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

attribute [irreducible] one two mp pr Iso Sm

theorem pr_congr {a b N : ℕ} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)} (h : List.ofFn x = List.ofFn z)
    (hx : ∑ i, (x i).1 = N) (hz : ∑ i, (z i).1 = N) : Iso (pr x hx) (pr z hz) := by
  obtain rfl : a = b := by simpa using congrArg List.length h
  obtain rfl := List.ofFn_injective h
  exact iso_refl _

theorem pr_cons {a b t N : ℕ} {w : IrrGL (k := k)} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)}
    (h : List.ofFn z = w :: List.ofFn x) (hx : ∑ i, (x i).1 = t) (hz : ∑ i, (z i).1 = N) (e : w.1 + t = N) :
    Iso (pr z hz) (two e (one w) (pr x hx)) := by
  have hb : b = a + 1 := by simpa using congrArg List.length h
  subst hb
  have h' : z 0 :: List.ofFn (fun i : Fin a => z i.succ) = w :: List.ofFn x := List.ofFn_succ.symm.trans h
  have h₁ : z 0 = w := (List.cons.inj h').1
  have h₂ : (fun i : Fin a => z i.succ) = x := List.ofFn_injective (List.cons.inj h').2
  subst h₁ h₂
  exact pr_succ z hx hz e

theorem pr_append {a : ℕ} : ∀ {b c r t N : ℕ} (x : Fin a → IrrGL (k := k)) (y : Fin b → IrrGL (k := k)) (z : Fin c → IrrGL (k := k))
    (_ : List.ofFn z = List.ofFn x ++ List.ofFn y) (_ : a ≠ 0 ∨ b = 0) (hx : ∑ i, (x i).1 = r)
    (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (e : r + t = N),
    Iso (pr z hz) (two e (pr x hx) (pr y hy)) := by
  induction a with
  | zero =>
    intro b c r t N x y z h hab hx hy hz e
    obtain rfl : b = 0 := by simpa using hab
    obtain rfl : t = 0 := by simpa using hy.symm
    have e0 : N = r := e.symm
    subst e0
    exact iso_trans (pr_congr (by simpa using h) hz hx) (iso_symm (two_unit_pr e _ (sm_pr x hx) y hy))
  | succ a ih =>
    intro b c r t N x y z h _ hx hy hz e
    have hx' : List.ofFn x = x 0 :: List.ofFn fun i : Fin a => x i.succ := List.ofFn_succ
    have hs : (x 0).1 + ∑ i : Fin a, (x i.succ).1 = r := (Fin.sum_univ_succ fun i => (x i).1).symm.trans hx
    have A := pr_cons hx' rfl hx hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain rfl : (x 0).1 = r := by simpa using hs
      have B := iso_trans A (two_unit_pr hs _ (sm_one (x 0)) (fun i : Fin 0 => x i.succ) rfl)
      refine iso_trans (pr_cons (w := x 0) (by simpa using h) hy hz e) ?_
      exact two_congr e (iso_symm B) (iso_refl _)
    · let L := (List.ofFn fun i : Fin a => x i.succ) ++ List.ofFn y
      have hL : List.ofFn L.get = L := List.ofFn_get L
      have hT : ∑ i, (L.get i).1 = ∑ i : Fin a, (x i.succ).1 + t := by
        have := congrArg (fun l : List (IrrGL (k := k)) => (l.map Sigma.fst).sum) hL
        simp only [L, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
        rw [← hy]
        exact this
      have e' : (x 0).1 + (∑ i : Fin a, (x i.succ).1 + t) = N := by omega
      have B := pr_cons (w := x 0) (z := z) (x := L.get) (by rw [h, hx', hL]; rfl) hT hz e'
      have C := ih (fun i => x i.succ) y L.get hL (Or.inl ha.ne') rfl hy hT rfl
      have D := two_assoc hs e rfl e' (one (x 0)) (pr (fun i : Fin a => x i.succ) rfl) (pr y hy)
        (sm_one _) (sm_pr _ _) (sm_pr _ _)
      exact iso_trans B (iso_trans (two_congr e' (iso_refl _) C) (iso_trans (iso_symm D)
        (two_congr e (iso_symm A) (iso_refl _))))

end GlobalTheory.ProdFlatten
