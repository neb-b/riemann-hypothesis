module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CyclicSolvable
section
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.FlowProgramme

lemma sum_shift (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma duality (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => h2 a
  rw [Finset.sum_add_distrib, sum_shift] at hs
  have hT : 0 ≤ ∑ a, ∑ i ∈ Finset.range d, x a i :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => h0 a i
  constructor
  · have : (l : ℝ) * ∑ a, ∑ i ∈ Finset.range d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : x a i = 0
      · simp [h]
      · have hi : i ≠ 0 := by
          rintro rfl
          exact absurd (h1 a 0 h).1 (by decide)
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi) (h0 a i)
    linarith
  · intro i₀
    have hp : (0 : ℝ) < (l : ℝ) ^ i₀ := by positivity
    rw [le_inv_mul_iff₀ hp]
    have : (l : ℝ) ^ i₀ * ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i₀ * x a i
          ≤ ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i * x a i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (Finset.mem_Ico.1 hi).1) (h0 a i)
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (by positivity) (h0 a i)
            intro i hi
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    linarith

lemma cyclic_nonneg (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min y
  obtain ⟨a₁, h₁⟩ := Finite.exists_max y
  refine le_trans ?_ (h₀ a)
  have e0 := hy a₀
  have e1 := hy a₁
  have f0 := h₁ (a₀ - 1)
  have f1 := h₀ (a₁ - 1)
  have g := hX a₁ a₀
  have k : l * y (a₀ - 1) ≤ l * y a₁ := mul_le_mul_of_nonneg_left f0 (by linarith)
  have k2 : 0 ≤ (l * l - 1) * y a₀ := by rw [← e0] at g; nlinarith
  have k3 : 0 < l * l - 1 := by nlinarith
  exact (mul_nonneg_iff_of_pos_left k3).1 k2

lemma cyclic_solvable (l : ℝ) (d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) :
    ∃ y : ZMod d → ℝ, ∀ a, l * y a + y (a - 1) = X a := by
  let T : (ZMod d → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun y a => l * y a + y (a - 1)
      map_add' := fun y z => by ext a; simp; ring
      map_smul' := fun c y => by ext a; simp; ring }
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : ∀ a, l * y a + y (a - 1) = 0 := fun a => congrFun hy a
    ext a
    have h1 := cyclic_nonneg l d (fun _ => 0) y hl (by simp) hy' a
    have h2 := cyclic_nonneg l d (fun _ => 0) (fun a => - y a) hl (by simp)
      (fun a => by have := hy' a; linarith) a
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj X
  exact ⟨y, fun a => congrFun hy a⟩

lemma balanced (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hd : 2 ≤ d)
    (hX : ∀ a b, X a ≤ l * X b) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧
      ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨y, hy⟩ := cyclic_solvable l d X hl'
  have hpos := cyclic_nonneg l d X y hl' hX hy
  have h1 : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun a i => if i = 1 then y a else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a i
    dsimp only
    split_ifs
    · exact hpos a
    · exact le_rfl
  · intro a i h
    dsimp only at h
    split_ifs at h with hi
    · subst hi
      exact ⟨odd_one, by omega⟩
    · exact absurd rfl h
  · intro a
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', h1, if_true, pow_one, Nat.cast_one]
    exact (hy a).le
  · simp only [Finset.sum_ite_eq', h1, if_true]
    have : ∑ a, y (a - 1) = ∑ a, y a := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [← Finset.sum_congr rfl fun a _ => hy a, Finset.sum_add_distrib, this, ← Finset.mul_sum]
    ring

end GlobalTheory.FlowProgramme
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearIndependentSumElimOfFinrankEq
section
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem exists_linearIndependent_sumElim_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have h1 := Submodule.finrank_add_eq_of_isCompl hQ
  rw [finrank_span_eq_card hv, Fintype.card_fin, hV] at h1
  have h2 : Module.finrank k Q = n' := by omega
  let b := Module.finBasisOfFinrankEq k Q h2
  refine ⟨fun j => (b j : V), hv.sum_type (b.linearIndependent.map' Q.subtype Q.ker_subtype) ?_⟩
  refine hQ.disjoint.mono_right ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact (b j).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolyCoeff
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

namespace GlobalTheory.IntegralEndLimit

theorem exists_real_le (x : WithTop ℝ) : ∃ t : ℝ, (t : WithTop ℝ) ≤ x := by
  cases x with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem le_val_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x y : C} {s t u : ℝ}
    (hx : (s : WithTop ℝ) ≤ v x) (hy : (t : WithTop ℝ) ≤ v y) (h : u ≤ s + t) :
    (u : WithTop ℝ) ≤ v (x * y) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add hx hy)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 h

theorem eval_close {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (x : ι → C) (Q : MvPolynomial ι C) (s : ℝ) :
    ∃ r : ℝ, ∀ x' : ι → C, (∀ i, (r : WithTop ℝ) ≤ v (x i - x' i)) →
      (s : WithTop ℝ) ≤ v (MvPolynomial.eval x Q - MvPolynomial.eval x' Q) := by
  induction Q using MvPolynomial.induction_on generalizing s with
  | C a => exact ⟨0, fun x' _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨r₁, h₁⟩ := hp s
    obtain ⟨r₂, h₂⟩ := hq s
    refine ⟨max r₁ r₂, fun x' hx' => ?_⟩
    have e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) =
        (MvPolynomial.eval x p - MvPolynomial.eval x' p) +
          (MvPolynomial.eval x q - MvPolynomial.eval x' q) := by
      simp only [map_add (f := _)]; ring
    rw [e]
    refine le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i))
      (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)
    · exact WithTop.coe_le_coe.2 (le_max_left _ _)
    · exact WithTop.coe_le_coe.2 (le_max_right _ _)
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := exists_real_le (v (MvPolynomial.eval x p))
    obtain ⟨b, hb⟩ := exists_real_le (v (x i))
    obtain ⟨r, hr⟩ := hp (s - b)
    refine ⟨max r (max (s - a) b), fun x' hx' => ?_⟩
    have h1 := hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)
    have h2 := hx' i
    have e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i)
        = MvPolynomial.eval x p * (x i - x' i) +
          ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i +
            -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i))) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    have m1 : s - a ≤ max r (max (s - a) b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : b ≤ max r (max (s - a) b) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [e]
    refine le_trans (le_min (le_val_mul v ha h2 (by linarith))
      (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)
    rw [v.map_neg]
    exact le_val_mul v h1 h2 (by linarith)

theorem exists_poly_coeff {C : Type} [Field C] {d : ℕ} (l : Fin d → MvPowerSeries (Fin d) C)
    (hl : ∀ a, constantCoeff (l a) = 0) (f : MvPowerSeries (Fin d) C) (α : Fin d →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin d × Fin d) C, ∀ A : Matrix (Fin d) (Fin d) C,
      coeff α (subst (fun a => ∑ b, A a b • l b) f) =
        MvPolynomial.eval (fun p => A p.1 p.2) Q := by
  let ι : C →+* MvPolynomial (Fin d × Fin d) C := MvPolynomial.C
  let L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C) :=
    fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero fun a => by
    simp [L, hl]
  refine ⟨coeff α (subst L (map ι f)), fun A => ?_⟩
  have hm : ∀ g : MvPowerSeries (Fin d) C,
      map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g := by
    intro g; ext β; simp [ι]
  rw [← coeff_map, map_subst hL, hm]
  congr 2
  funext a
  simp [L, hm, smul_eq_C_mul]

theorem integral_of_limit :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (A : Matrix (Fin d) (Fin d) C),
    (∀ r : ℝ, ∃ A' : Matrix (Fin d) (Fin d) C, (∀ a b, (r : WithTop ℝ) ≤ v (A a b - A' a b)) ∧ ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A' a b • G.lg b) →
    ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A a b • G.lg b) := by
  intro C _ _ v d G A hA
  obtain ⟨ex, ⟨hex0, hr, hl⟩, -⟩ := GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg
    G.lg_const (by
      have : (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) :
          Matrix (Fin d) (Fin d) C) = 1 := by
        ext i j; simp [G.lg_lin, Matrix.one_apply]
      rw [this]; exact isUnit_one)
  have hex : HasSubst ex := hasSubst_of_constantCoeff_zero hex0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0 := fun a => by
    simp [G.lg_const]
  have hs : HasSubst fun a => ∑ b, A a b • G.lg b := hasSubst_of_constantCoeff_zero h0
  refine ⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_,
    fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_poly_coeff G.lg G.lg_const (ex a) α
    obtain ⟨r, hr'⟩ := eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0
    obtain ⟨A', hA', φ, hφi, hφ0, hφ⟩ := hA r
    have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
    have e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a := by
      rw [← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]
    have h1 := hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2
    have h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q) := by
      rw [← hQ, e]; exact hφi a α
    show 0 ≤ v _
    rw [hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q)
      (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]
    exact le_trans (le_min h1 h2) (v.map_add _ _)
  · rw [← subst_comp_subst_apply hex hs, hr, subst_X hs]

end GlobalTheory.IntegralEndLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawLogarithm
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.LawLog

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

def twoVars (k : Type) [CommRing k] (d : ℕ) : Fin 2 × Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  fun q => X (if q.1 = 0 then Sum.inl q.2 else Sum.inr q.2)

def oneVar (k : Type) [CommRing k] (d : ℕ) : Fin 1 × Fin d → MvPowerSeries (Fin d) k :=
  fun q => X q.2

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_twoVars (q : Fin 2 × Fin d) : constantCoeff (twoVars k d q) = 0 := by simp [twoVars]

theorem cc_oneVar (q : Fin 1 × Fin d) : constantCoeff (oneVar k d q) = 0 := by simp [oneVar]

theorem hs_twoVars : HasSubst (twoVars k d) := hasSubst_of_constantCoeff_zero cc_twoVars

theorem hs_oneVar : HasSubst (oneVar k d) := hasSubst_of_constantCoeff_zero cc_oneVar

def sndEmb (d : ℕ) : Fin 1 × Fin d ↪ Fin d :=
  ⟨Prod.snd, fun _ _ h => Prod.ext (Subsingleton.elim _ _) h⟩

theorem coeff_single_oneVar (f : PS k 1 d) (b : Fin d) :
    coeff (Finsupp.single b 1) (subst (oneVar k d) f) = coeff (Finsupp.single ((0 : Fin 1), b) 1) f := by
  have h1 : subst (oneVar k d) f = rename (sndEmb d) f := by
    rw [rename_eq_subst]; rfl
  have h2 : Finsupp.single b 1 = Finsupp.embDomain (sndEmb d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [h1, h2, coeff_embDomain_rename]

theorem subst_oneVar {n : ℕ} {τ : Type} [Finite τ] (T : Fin n × Fin d → MvPowerSeries τ k)
    (hT : ∀ q, constantCoeff (T q) = 0) (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (f : PS k 1 d) :
    subst (fun i => subst T (a i)) (subst (oneVar k d) f) = subst T (ev ![a] f) := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h1 : HasSubst (fun i => (subst T (a i) : MvPowerSeries τ k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hTs hT (ha i)
  have h2 : HasSubst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt k n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j; exact ha i
  unfold ev
  rw [subst_comp_subst_apply hs_oneVar h1, subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  simp only [oneVar]
  rw [subst_X h1]
  rfl

theorem add_pt (G : FGLaw k d) : G.add (pt k (n := 2) d 0) (pt k d 1) = G.F := by
  funext c
  show ev (n := 2) ![pt k d 0, pt k d 1] (G.F c) = G.F c
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [e, subst_self]
  rfl

end GlobalTheory.LawLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowAdditiveAndRoots
section
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.FrobRoot

variable {C : Type} [Field C] {V : VF C}

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_of_ge_one {a : C} (ha : V.Ge 1 a) : V.MM a := by
  refine lt_of_lt_of_le ?_ ha
  exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  unfold VF.MM at *
  rw [V.v.map_pow]
  exact nsmul_pos ha hn

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (ha : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  unfold VF.Ge at *
  rw [V.v.map_pow] at ha
  rw [WithTop.coe_zero] at ha ⊢
  by_contra h
  exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))

theorem mm_add_pow (e : ℕ) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime
    (⟨a, ha⟩ : intRing V) (⟨b, hb⟩ : intRing V) e
  have h := congrArg (Subtype.val) hr
  push_cast at h
  rw [h, add_sub_cancel_left]
  apply mm_of_ge_one
  have hr0 : V.Ge 0 (r : C) := r.2
  first
    | simpa using hr0.l_mul
    | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul

theorem mm_sum_pow (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C) (hx : ∀ i ∈ s, V.Ge 0 (x i)) :
    V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
    exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
    convert h using 1
    ring

end GlobalTheory.FrobRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TauBasisUnitDeterminant
section
open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.tau_basis_unit_determinant

theorem exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by
  intro p _ OE _ _ _ O _ _ _ w t ht hsep
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  have hxM := (mem_maximalIdeal _).2 hx
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] O ⧸ maximalIdeal O) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] (maximalIdeal O)).comp (tauExt (t j))
  refine GlobalTheory.UnitDeterminantBasis.det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    rw [← Ideal.Quotient.eq]
    simpa [T, tauExt] using h1
  · intro j
    have h1 : tauExt (t j) w.e = 1 := ht j
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1

end GlobalTheory.tau_basis_unit_determinant
end

