module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0019

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace PhPowP

open PartialDerivEval

section Gen

variable {C : Type} [Field C] {V : VF C}

theorem frob_mv {σ : Type} {A B : MvPowerSeries σ C} (hA : IntS V A) (hB : IntS V B) (μ : σ →₀ ℕ) :
    V.MM (coeff μ ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by
  have e : (A + B) ^ V.l - A ^ V.l - B ^ V.l = MvPowerSeries.C (V.l : C) *
      ∑ k ∈ Finset.Ioo 0 V.l, A ^ k * B ^ (V.l - k) * MvPowerSeries.C ((V.l.choose k / V.l : ℕ) : C) := by
    rw [add_pow_prime_eq' V.l_prime A B]
    simp only [map_natCast]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, coeff_C_mul, map_sum, mul_comm]
  refine ValuationNonnegativity.mm_mul_int (VF.Ge.sum fun k _ => ?_) FrobP.mm_l
  rw [coeff_mul_C]
  exact VF.Ge.mul_int (intS_mul (intS_pow hA k) (intS_pow hB _) μ) (VF.ge_natCast _)

theorem frob_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C) (hf : ∀ i, IntS V (f i))
    (μ : σ →₀ ℕ) : V.MM (coeff μ ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero, map_zero]
    exact ValuationNonnegativity.mm_zero
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    have hS : IntS V (∑ i ∈ s, f i) := intS_sum _ fun i _ => hf i
    have e : (f b + ∑ i ∈ s, f i) ^ V.l - (f b ^ V.l + ∑ i ∈ s, f i ^ V.l) =
        ((f b + ∑ i ∈ s, f i) ^ V.l - f b ^ V.l - (∑ i ∈ s, f i) ^ V.l) +
          ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by ring
    rw [e, map_add (f := _)]
    exact ValuationNonnegativity.mm_add (frob_mv (hf b) hS μ) ih

theorem monomial_pow' {σ : Type} (β : σ →₀ ℕ) (a : C) :
    ∀ n : ℕ, (monomial β a) ^ n = monomial (n • β) (a ^ n)
  | 0 => by
    ext μ
    rw [pow_zero, zero_smul, pow_zero, coeff_one, coeff_monomial]
  | n + 1 => by
    rw [pow_succ, monomial_pow' β a n, monomial_mul_monomial, succ_nsmul, pow_succ]

def divL {σ : Type} (l : ℕ) (α : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.mapRange (fun n => n / l) (Nat.zero_div l) α

theorem divL_apply {σ : Type} (l : ℕ) (α : σ →₀ ℕ) (t : σ) : divL l α t = α t / l := by
  simp [divL]

theorem frobPowMv {σ : Type} (F : MvPowerSeries σ C) (hF : IntS V F) (α : σ →₀ ℕ) :
    V.MM (coeff α (F ^ V.l) - if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0) := by
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨P, hPdef⟩ : ∃ P : MvPowerSeries σ C, P = ∑ β ∈ Finset.Iic α, monomial β (coeff β F) := ⟨_, rfl⟩
  have hmon : ∀ β, IntS V (monomial β (coeff β F)) := fun β μ => by
    rw [coeff_monomial]
    split_ifs
    · exact hF β
    · exact VF.Ge.zero 0
  have e1 : coeff α (F ^ V.l) = coeff α (P ^ V.l) := by
    obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow F P V.l
    have h0 : coeff α (F ^ V.l - P ^ V.l) = 0 := by
      rw [hR, coeff_mul]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx1 : x.1 ≤ α := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
        exact le_self_add
      have hc : coeff x.1 (F - P) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, sub_eq_zero, hPdef, map_sum]
        simp only [coeff_monomial]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 hx1)]
      rw [hc, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have e2 := frob_sum (Finset.Iic α) (fun β => monomial β (coeff β F)) hmon α
  have e3 : coeff α (∑ β ∈ Finset.Iic α, (monomial β (coeff β F)) ^ V.l) =
      if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [monomial_pow', coeff_monomial]
    split_ifs with hdiv
    · have hβ : α = V.l • divL V.l α := by
        ext t
        rw [Finsupp.smul_apply, smul_eq_mul, divL_apply, Nat.mul_div_cancel' (hdiv t)]
      rw [Finset.sum_eq_single (divL V.l α)]
      · rw [if_pos hβ]
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        ext t
        have := congrArg (fun f : σ →₀ ℕ => f t) (h.symm.trans hβ)
        simp only [Finsupp.smul_apply, smul_eq_mul] at this
        exact Nat.eq_of_mul_eq_mul_left hl0 this
      · intro h
        exfalso
        apply h
        rw [Finset.mem_Iic, Finsupp.le_def]
        intro t
        rw [divL_apply]
        exact Nat.div_le_self _ _
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      apply hdiv
      intro t
      rw [h, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.dvd_mul_right _ _
  rw [e1, ← e3, ← map_sub, hPdef]
  exact e2

end Gen

section Slice

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

end Slice

section FBs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

end FBs

end PhPowP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FirstStepSecondHalfCondition
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def frobTw {σ : Type} (l : ℕ) (c : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0

def cobd {dd : ℕ} (F : Fin dd → PS C 2 dd) (b : PS C 1 dd) : PS C 2 dd :=
  ev (n := 2) ![addOf F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b - ev (n := 2) ![pt C dd 1] b

end Defs

def FirstStepFirstHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ A : PS C 1 dd, IntS V A ∧
        (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) ∧
        ∀ μ, V.MM (MvPowerSeries.coeff μ
          (cobd Y.B.G.F A - frobTw V.l (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)))))

def FirstStepSecondHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    ∀ (dd : ℕ) (G : FGLaw C dd), (∀ i, IntS V (G.F i)) →
    ∀ (A : PS C 1 dd) (c : PS C 2 dd), IntS V A → IntS V c →
      (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) →
      (∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cobd G.F b))

theorem intS_c2lin {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.chartLinearTerm u) := by
  intro μ
  show V.Ge 0 (∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2)
  exact VF.Ge.sum fun i _ => by simpa using (hu i).mul (Y.intPh2 _)

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.GramMatrixMulRight
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

abbrev AA (r : T → ℕ) (tau : Orb → ZMod 2 → T) (N : ℕ) : Type := Fin N × Σ o, IIs r tau o

def eW (N : ℕ) : (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ≃ AA r tau N × Fin 2 where
  toFun y := ((y.1, ⟨y.2.1, y.2.2.2⟩), y.2.2.1)
  invFun z := (z.1.1, ⟨z.1.2.1, ⟨z.2, z.1.2.2⟩⟩)
  left_inv := by rintro ⟨ρ, ⟨o, ⟨g, c⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨ρ, ⟨o, c⟩⟩, g⟩; rfl

def lam (z : AA r tau N × Fin 2) : Letter T r n := ⟨tau z.1.2.1 z.1.2.2.1, z.1.2.2.2, plc (z.1.1, z.2)⟩

variable {r tau}

theorem lam_inj (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h
  simp only [lam, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := inj (a₁ := (o, t)) (a₂ := (o', t')) h1
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, h5⟩ := h4
  have h6 := plc.injective h5
  simp only [Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rfl

variable (r tau)

def Gm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 α.2.2.1 col g

def Mm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 (α.2.2.1 + 1) col (1 - g)

variable {r tau gm}

theorem gram_matrix_mul_right (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  have h := gm_hyp α.2.1 α.2.2.1 (1 - g') g
  unfold Mm Gm
  rw [h]
  clear h
  fin_cases g <;> fin_cases g' <;> simp

theorem gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

variable (r tau gm)

def coS (ℓ : Letter T r n) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) : C :=
  ∑ col, if ℓ = lam r tau plc ((eW r tau N y).1, col) then Mm r tau gm (eW r tau N y).1 col (eW r tau N y).2 else 0

variable {r tau gm}

theorem coS_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm r tau gm α col g else 0 := by
  unfold coS
  rw [Equiv.apply_symm_apply]
  simp only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]
  by_cases h : α = α'
  · subst h
    simp
  · simp [h]

theorem sum_coS (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  rw [← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single α]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [coS_lam plc inj, if_pos rfl]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [coS_lam plc inj, if_neg (Ne.symm hne), h0]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem subG_X (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl

theorem back_subG (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) *
      (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) =
      AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) *
        (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) =
        ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :=
      fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
        (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) *
          (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :
            MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) =
        MvPolynomial.C (if g = (eW r tau N y).2 then 1 else 0) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) := by
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [map_mul]; ring
    simp only [h2]
    rw [Finset.sum_eq_single (eW r tau N y).2]
    · simp
    · intro g _ hg; simp [hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact congrArg (fun φ => φ Q) h

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop
section
namespace Formalism.L2.FormalSeriesBounds

def GermIAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), GermISt Y

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Rename₂

theorem coeff_rename_outside {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)

variable {dd : ℕ}

theorem coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm

end Rename₂

section Self

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all

theorem FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

end Self

theorem hStabSelf_holds : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)

end Formalism.L2.FormalSeriesBounds
end
end

