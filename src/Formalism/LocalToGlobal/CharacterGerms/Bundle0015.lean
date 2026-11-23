module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

theorem pderiv_comm' {σ R : Type} [CommRing R] (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · congr 1
      · rw [tsub_right_comm]
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij),
          tsub_zero]
        ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

section One

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem no_conj_of_rowsOK {G : ∀ g, Cart V d (I g) (J g)} {alt : Prop} {N : ℕ} {P : MvPolynomial (Fin N × WV I) C}
    {kind : Fin N → Knd d} (h : RowsOK G alt P kind) {ρ : Fin N} {w w' : WV I} (hw : (ρ, w) ∈ P.vars)
    (hw' : (ρ, w') ∈ P.vars) (hg : w.1 ≠ w'.1) (ht : tyW G w = tyW G w') : False := by
  obtain ⟨h1, h2⟩ := h
  rw [MvPolynomial.mem_vars_iff_mem_support] at hw hw'
  obtain ⟨μ, hμ, hμw⟩ := hw
  obtain ⟨μ', hμ', hμw'⟩ := hw'
  rcases hk : kind ρ with _ | ⟨g, a, a'⟩
  · obtain ⟨g, hg'⟩ := h2 ρ hk
    have e1 := hg' μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have e2 := hg' μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    exact hg (e1.trans e2.symm)
  · obtain ⟨-, hodd, hleaf⟩ := h1 ρ g a a' hk
    have l1 := hleaf μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have l2 := hleaf μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    rcases l1 with ⟨e1, t1⟩ | ⟨e1, t1⟩ <;> rcases l2 with ⟨e2, t2⟩ | ⟨e2, t2⟩
    · exact hg (e1.trans e2.symm)
    · have he : a = a' := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · have he : a' = a := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · exact hg (e1.trans e2.symm)

variable (X : RowData C V d I J) (F : Flag X)

theorem exists_rowsOK (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) :
    ∃ kind : Fin (b.what₂ X.n) → Knd d, RowsOK X.G X.Alt (b.poly X F) kind := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      exact ⟨g, fun w hw => (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1⟩
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
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
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
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
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

end One

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin n}

end Fam

theorem lap_one_apply {T : Type} (r : T → ℕ) (n : ℕ) (C : Type) [Field C] (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (P : MvPolynomial (Letter T r n) C) :
    lap r n C 1 τ τ' a a' P = ∑ b, ∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      MvPolynomial.pderiv (⟨τ, a, b⟩ : Letter T r n) (MvPolynomial.pderiv (⟨τ', a', b'⟩ : Letter T r n) P) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Formal

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.chartLinearTerm (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 2 dd :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2

def cvAt (s : MvPowerSeries (Fin 2) C) (γ : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  MvPowerSeries.subst (fun _ : Unit => s) γ

def NDG (Y : FBChart C V O dd) : Prop :=
  ∀ γ : Fin dd → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => cvAt (MvPowerSeries.X p.1) (γ p.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
      (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
        (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
          ev (n := 2) ![pt C dd 1] b)))

end Formal

def RankMaximalOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    NDG Y → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def NondegenerateCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → NDG Y

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C]

def ZP (C : Type) [Field C] (σ : Type) : Subring (MvPolynomial σ C) := (MvPolynomial.map (Int.castRingHom C)).range

theorem X_mem_ZP {σ : Type} (x : σ) : (MvPolynomial.X x : MvPolynomial σ C) ∈ ZP C σ :=
  RingHom.mem_range.2 ⟨MvPolynomial.X x, MvPolynomial.map_X _ _⟩

theorem rename_mem_ZP {σ τ : Type} (k : σ → τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) :
    MvPolynomial.rename k P ∈ ZP C τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  exact RingHom.mem_range.2 ⟨MvPolynomial.rename k Q, MvPolynomial.map_rename _ _ _⟩

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (h : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun s _ => ?_
  rw [Units.smul_def]
  exact S.zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem minorK_mem_ZP (N N' k : ℕ) : minorK C N N' k ∈ ZP C (Fin N × Fin N') := by
  unfold minorK
  split_ifs with h
  · exact det_mem _ _ fun i j => X_mem_ZP _
  · exact one_mem _

theorem minorMonomial_mem_ZP (N N' : ℕ) (e : ℕ → ℕ) : monP C N N' e ∈ ZP C (Fin N × Fin N') := by
  unfold monP
  exact prod_mem fun k _ => pow_mem (minorK_mem_ZP N N' k) _

end Gen

theorem poly_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (b : GlobalTheory d) : b.poly X F ∈ ZP C _ := by
  unfold GlobalTheory.poly
  cases b with
  | bi g a i y =>
    exact mul_mem (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
      (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
  | ch g a u => exact pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _
  | mon g e N => exact prod_mem fun a _ => rename_mem_ZP _ (minorMonomial_mem_ZP _ _ _)

theorem blkProd_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : blkProd X F n L pl ∈ ZP C _ := by
  unfold blkProd toAll prodAll
  exact prod_mem fun o _ => rename_mem_ZP _ (prod_mem fun i _ => rename_mem_ZP _ (poly_mem_ZP _ _ _))

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NormOneRowDegrees
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_rename {σ τ : Type} {w : τ → ℕ} (f : σ → τ) {p : MvPolynomial σ R} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) p D) : IsWeightedHomogeneous w (rename f p) D := by
  intro dd hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f p dd hd
  rw [← h hu, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem isWH_of_zero {σ : Type} {w : σ → ℕ} (hw : ∀ x, w x = 0) (p : MvPolynomial σ R) :
    IsWeightedHomogeneous w p 0 := by
  intro dd _
  simp [Finsupp.weight_apply, hw]

theorem isWH_congr {σ : Type} {w w' : σ → ℕ} (h : ∀ x, w x = w' x) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w p D := by
  obtain rfl : w = w' := funext h
  exact hp

theorem isWH_deg {σ : Type} {w : σ → ℕ} {p : MvPolynomial σ R} {D D' : ℕ}
    (hp : IsWeightedHomogeneous w p D) (e : D = D') : IsWeightedHomogeneous w p D' := by
  subst e; exact hp

theorem isWH_minorK_gen {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (v : Fin N' → ℕ) (hw : ∀ x, w x = v x.2)
    (h : k ≤ N ∧ k ≤ N') :
    IsWeightedHomogeneous w (minorK R N N' k) (∑ c : Fin k, v (Fin.castLE h.2 c)) := by
  unfold minorK
  rw [dite_eq_left h, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous w (∏ i : Fin k, (Matrix.of fun b c : Fin k =>
      (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') R)) (σ i) i)
      (∑ c : Fin k, v (Fin.castLE h.2 c)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      simp only [Matrix.of_apply]
      have hx := isWeightedHomogeneous_X R w (Fin.castLE h.1 (σ i), Fin.castLE h.2 i)
      rwa [hw] at hx
  intro dd hdd
  apply hprod
  intro h0
  apply hdd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]

theorem sum_fin_ite (k c0 : ℕ) : (∑ c : Fin k, if (c : ℕ) = c0 then 1 else 0) = if c0 < k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c0, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro hc; exact hb (Fin.ext hc)
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hc
    exact h (by rw [← hc]; exact c.2)

theorem isWH_minorK_row {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (P : Prop) [Decidable P] (c0 : ℕ)
    (hw : ∀ x, w x = if P ∧ (x.2 : ℕ) = c0 then 1 else 0) :
    IsWeightedHomogeneous w (minorK R N N' k) (if k ≤ N ∧ k ≤ N' ∧ P ∧ c0 < k then 1 else 0) := by
  by_cases h : k ≤ N ∧ k ≤ N'
  · have hg := isWH_minorK_gen (R := R) (fun c : Fin N' => if P ∧ (c : ℕ) = c0 then 1 else 0) hw h
    refine isWH_deg hg ?_
    by_cases hP : P
    · simp only [hP, true_and, Fin.coe_castLE]
      rw [sum_fin_ite]
      simp [h.1, h.2, hP]
    · simp [hP]
  · unfold minorK
    rw [dite_eq_right h, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
    exact isWeightedHomogeneous_one R w

end WH

section Let

variable {T : Type} (r : T → ℕ) (n : ℕ)

def wLet (σ : T) (c0 : Fin (r σ)) (ℓ : Letter T r n) : ℕ := ∑ b : Fin n, if ℓ = ⟨σ, c0, b⟩ then 1 else 0

theorem weight_wLet (σ : T) (c0 : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (wLet r n σ c0) m = ∑ b : Fin n, m ⟨σ, c0, b⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [wLet, smul_eq_mul, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    exact h.symm

variable {r n}

theorem letEq {τ1 τ2 : T} {c1 : Fin (r τ1)} {c2 : Fin (r τ2)} {b1 b2 : Fin n} :
    ((⟨τ1, (c1, b1)⟩ : Letter T r n) = ⟨τ2, (c2, b2)⟩) ↔ ((⟨τ1, c1⟩ : Σ σ, Fin (r σ)) = ⟨τ2, c2⟩ ∧ b1 = b2) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    cases h1
    rfl

theorem wLet_mk (σ : T) (c0 : Fin (r σ)) (τ : T) (c : Fin (r τ)) (ρ : Fin n) :
    wLet r n σ c0 ⟨τ, (c, ρ)⟩ = if (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0 := by
  unfold wLet
  simp only [letEq]
  by_cases h : (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩
  · simp only [h, true_and, if_true]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

end Let

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]

variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)







end Block

end WeightHomogeneousMinors

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

def keyL (ℓ : Letter T r n) : T × ℕ × Fin n := (ℓ.1, ℓ.2.1.val, ℓ.2.2)

theorem keyL_inj : Function.Injective (keyL (T := T) (r := r) (n := n)) := by
  rintro ⟨σ, i, c⟩ ⟨σ', i', c'⟩ h
  simp only [keyL, Prod.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  obtain rfl : i = i' := Fin.ext hi
  rfl

theorem rowShift_X (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by
  unfold rowShift
  simp only [MvPolynomial.aeval_X]
  have key : (∃ b, ℓ = ⟨σ, (i, b)⟩) ↔ keyL ℓ = (σ, ↑i, ℓ.snd.2) := by
    constructor
    · rintro ⟨b, rfl⟩
      rfl
    · intro h
      exact ⟨ℓ.snd.2, keyL_inj (show keyL ℓ = keyL ⟨σ, (i, ℓ.snd.2)⟩ from h)⟩
  by_cases h : keyL ℓ = (σ, ↑i, ℓ.snd.2)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h]

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin n}

end Fam

end Formalism.L2.FormalSeriesBounds.RF
end
end

