module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section Jet

variable {C : Type} [Field C] {σ : Type}

theorem cc_mvExp (x : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp x) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1
  simp

theorem jetAt0_one (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  unfold jetAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simp [mfact]

end Jet

section Par

theorem odd_sub_val {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : y = x + (y - x) := by ring
  have e1 : y.val = (x.val + (y - x).val) % d := by
    conv_lhs => rw [e]
    exact ZMod.val_add _ _
  have e2 : y.val % 2 = (x.val + (y - x).val) % 2 := by rw [e1, Nat.mod_mod_of_dvd _ h2]
  rw [Nat.even_iff, Nat.even_iff] at h
  rw [Nat.odd_iff]
  omega

end Par

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

theorem vars_letter {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by
  obtain ⟨x, -, e⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)
  have e2 : (⟨g, F.en g a x.2⟩ : WV I) = w := congrArg Prod.snd e
  subst e2
  exact ⟨rfl, F.en_ty g a x.2⟩

theorem big_of_le_rk (hj : X.j' < X.n) {g : Fin 2} {a : ZMod d} (h : X.n ≤ X.rkF g a) : X.big g a := by
  by_contra hb
  have := X.rk_small g a hb
  unfold RowData.rkF at h
  omega

theorem big_one_iff (a : ZMod d) : X.big 1 a ↔ ¬ X.big 0 a := by
  simpa using X.big_compl 0 a

theorem alt_odd_of_big (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by
  have h3 : ¬ X.big g a' := (X.big_compl g a').1 h2
  rcases hdich with hA | hB
  · refine ⟨hA, odd_sub_val hA.1 a a' ?_⟩
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [← hA.2 a, ← hA.2 a']
      tauto
    · rw [big_one_iff] at h1 h3
      rw [← hA.2 a, ← hA.2 a']
      tauto
  · exfalso
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact h3 (hB a')
    · rw [big_one_iff] at h1
      exact h1 (hB a)

theorem attainsOK_of (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d) (c : ℝ)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) (h : b.Attains X F c) : b.AttainsOK X F c := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      exact (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)
      exact (vars_letter X F ha).1
  | bi g a i y =>
    by_cases hy : y = 0
    · subst hy
      have hp : (GlobalTheory.bi g a i 0).poly X F = 1 := by
        simp [GlobalTheory.poly]
        rfl
      obtain ⟨S, t, ht, gr, hg, hc⟩ := h
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, S, t, ht, gr, hg, ?_⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
      · refine le_of_eq_of_le ?_ hc
        congr 1
        unfold ValOf
        rw [hp, jetAt0_one, jetAt0_one, map_prod, map_prod]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [map_mul, map_mul, cc_mvExp, cc_mvExp]
    · have hl : 0 < V.l ^ i * y := Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)
      have w1 : X.n ≤ X.rkF g a := by
        apply hwt g a X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) := by
        apply hwt (1 - g) (a + (i : ZMod d)) X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have hao := alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

theorem le_sum_map {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · omega
    · have := ih h
      omega

variable {X F} in
theorem rkF_eq_of_big_iff {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by
  unfold RowData.rkF
  by_cases hb : X.big g a
  · rw [X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]
  · rw [X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]

end Formalism.L2.FormalSeriesBounds.RF

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem blkAdm (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : BlockAdmissible X F Z ga := by
  intro L hwt o ho q hq hatt
  refine attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt
  rw [← hwt o ho g a k]
  have := le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq
  omega

end G

section Cc

theorem zmod_two_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by revert a; decide

theorem zmod_two_even_succ_iff (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by revert a; decide

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)

theorem blkAdmC (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by
  intro L hwt o q hq hatt
  refine attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt
  have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hg with rfl | rfl
  · apply hga o a k
    rw [← hwt o a k]
    have h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _ :=
      le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq
    omega
  · have hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0 := by rwa [zmod_two_add_one_add_one]
    have h1 : k ≤ (X o).rkF 0 (a + 1) := by
      apply hga o (a + 1) k
      rw [← hwt o (a + 1) k]
      have h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _ :=
        le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq
      omega
    have h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a := by
      rw [big_one_iff, (hA o).2 (a + 1), (hA o).2 a]
      exact zmod_two_even_succ_iff a
    rwa [rkF_eq_of_big_iff h2] at h1

end Cc

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

def tyS (l : ℕ) (a : ℕ → C) : PowerSeries C :=
  PowerSeries.mk fun n => ∑ s ∈ Finset.range (n + 1), if l ^ s = n then a s else 0

def IsCv (V : VF C) {σ : Type} (γ : σ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.constantCoeff (γ i) = 0 ∧ ∀ n, V.Ge 0 (PowerSeries.coeff n (γ i))

def alongCv {σ : Type} (γ : σ → PowerSeries C) (f : MvPowerSeries σ C) : PowerSeries C :=
  MvPowerSeries.subst γ f

abbrev JJ (I : Fin 2 → Type) : Fin 2 → Type := fun g => I (1 - g)

structure RawChart (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) (κ : Type) where

  lg : κ → MvPowerSeries κ C
  ex : κ → MvPowerSeries κ C

  h : MvPowerSeries (Fin 2 × κ) C

  k : ℕ

  u : ∀ g, I g → κ → C
  ty : ∀ g, I g → ZMod d

  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def sg (v : κ → C) : MvPowerSeries κ C :=
  fun μ => -∑ i, v i * MvPowerSeries.coeff
    (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h

def sg1 (w v : κ → C) : C := ∑ x, w x * MvPowerSeries.coeff (Finsupp.single x 1) (X.sg v)

def tyC (g : Fin 2) : I g ⊕ JJ I g → ZMod d := Sum.elim (X.ty g) (X.ty (1 - g))

def TySet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {x | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0}

structure CartHyp (V : VF C) (g : Fin 2) : Prop where

  zero : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g

  add : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g
  neg : ∀ x, x ∈ X.TySet V g → -x ∈ X.TySet V g

  teich : ∀ c, V.Ge 0 c → ∀ x ∈ X.TySet V g, teich V.l c x ∈ X.TySet V g

  Vm : ∀ x ∈ X.TySet V g, Vpow 1 x ∈ X.TySet V g

  Fm : ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g

  sumV : ∀ y : ℕ → ℕ → I g ⊕ JJ I g → C, (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g

  t2 : ∀ x ∈ X.TySet V g, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : JJ I g → C, (∀ q, V.Ge 0 (ζ q)) → const0 (Sum.elim 0 ζ) ∈ X.TySet V g

  t4 : ∀ (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) → (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

variable {X}

def cart {V : VF C} {g : Fin 2} (H : X.CartHyp V g) : Cart V d (I g) (JJ I g) where
  ty := X.tyC g
  Ty :=
    { carrier := X.TySet V g
      zero_mem' := H.zero
      add_mem' := fun {x y} hx hy => H.add x y hx hy
      neg_mem' := fun {x} hx => H.neg x hx }
  teich_mem := H.teich
  V_mem := H.Vm
  F_mem := H.Fm
  sumV_mem := H.sumV
  t2 := H.t2
  t3 := H.t3
  t4 := H.t4

variable (X)

def pairK (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : C := if q = c then -(X.k : C) else 0

def expPt (g : Fin 2) (x : κ) : MvPowerSeries (WV I) C :=
  MvPowerSeries.subst (fun i : κ => ∑ c : I g, X.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
    (X.ex x)

def hRow : MvPowerSeries (WV I) C :=
  (X.k : C) • MvPowerSeries.subst (fun p : Fin 2 × κ => X.expPt p.1 p.2) X.h

def OnLf (g : Fin 2) (a a' : ZMod d) (w : WV I) : Prop :=
  (w.1 = g ∧ X.ty w.1 w.2 = a) ∨ (w.1 = 1 - g ∧ X.ty w.1 w.2 = a')

def hLf (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C :=
  fun μ => if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0

theorem onLf_swap (a a' : ZMod d) (w : WV I) : X.OnLf 1 a' a w ↔ X.OnLf 0 a a' w := by
  unfold OnLf
  simp only [sub_self, sub_zero]
  exact or_comm

theorem hLf_swap (a a' : ZMod d) : X.hLf 1 a' a = X.hLf 0 a a' := by
  unfold hLf
  funext μ
  exact if_congr (by simp only [onLf_swap]) rfl rfl

theorem hLf_leaf (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : MvPowerSeries.coeff μ (X.hLf g a a') ≠ 0) : ∀ w ∈ μ.support, X.OnLf g a a' w := by
  by_contra hn
  apply h
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [if_neg hn]

structure RankHyp : Prop where
  big_compl : ∀ g a, X.big (1 - g) a ↔ ¬ X.big g a
  rk_big : ∀ g a, X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j
  rk_small : ∀ g a, ¬ X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.j'

def AltC : Prop := Even d ∧ ∀ a : ZMod d, (X.big 0 a ↔ Even a.val)

def AxesSt : Prop :=
  ∀ (μ : WV I →₀ ℕ), ((∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1)) →
    MvPowerSeries.coeff μ X.hRow = 0

section Geo

variable {X} {V : VF C} (H : ∀ g, X.CartHyp V g)

def IntegralGermIndependentOfSystem : Prop :=
  ∀ (S S₂ : ∀ g, Sys (cart (H g))) (t t₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → (∀ g, (S₂ g).IsT (t₂ g)) → IntGerm V t = IntGerm V t₂

def CEqSt : Prop :=
  X.AltC → ∀ g a a', Odd (a' - a).val →
    ∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ k : I (1 - g), X.ty (1 - g) k = a' →
      ∃ K ∈ IntGerm V t,
        dVar (⟨1 - g, k⟩ : WV I) (X.hLf g a a') -
            toLeaf (fun g => cart (H g)) g a a' (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) =
          toLeaf (fun g => cart (H g)) g a a' K

def RankMaximalCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (cart (H g)).Good a w x →
    (∀ q, V.MM ((cart (H g)).c0' x q)) → ∀ c, V.MM (w c)

def IndependenceBoundCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (N : ℕ) (w : Fin N → I g → C) (x : Fin N → ℕ → I g ⊕ JJ I g → C),
    (∀ ν, (cart (H g)).Good a (w ν) (x ν)) → (∀ ν c, V.MM ((cart (H g)).V2 (x ν) c)) →
    IndepMod V w → N ≤ X.j'

def CHSt : Prop :=
  ∀ g a, X.big g a → ∀ w : Fin X.n → I g → C, IsSat V w →
    (∀ c x, X.ty g x ≠ a → w c x = 0) →
    ∃ y : Fin X.n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      (X.AltC →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          (((X.n : ℝ) * gam V.l + ((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, X.big g a) →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          ((((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

end Geo

structure Hyps (V : VF C) : Prop where
  charZero : CharZero C
  algClosed : IsAlgClosed C
  l_odd : V.l ≠ 2
  k_unit : V.v (X.k : C) = 0
  cartH : ∀ g, X.CartHyp V g
  rank : X.RankHyp
  axes : X.AxesSt
  G0 : IntegralGermIndependentOfSystem cartH
  CEq : CEqSt cartH
  R1 : IndependenceBoundCondition cartH
  R2 : RankMaximalCondition cartH
  CH : CHSt cartH

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

