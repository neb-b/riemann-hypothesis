module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieLab
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ge_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  obtain ⟨p, hpm, hp⟩ := hx
  have hZ : ∀ z : ℤ, V.Ge 0 (algebraMap ℤ C z) := by
    intro z
    rw [eq_intCast]
    refine Int.induction_on z ?_ ?_ ?_
    · rw [Int.cast_zero]; exact VF.Ge.zero 0
    · intro i ih
      rw [Int.cast_add, Int.cast_one]
      exact VF.Ge.add ih VF.Ge.one
    · intro i ih
      rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]
      exact VF.Ge.add ih (VF.Ge.neg VF.Ge.one)
  by_contra hneg
  have hlt : V.v x < ((0 : ℝ) : WithTop ℝ) := not_le.mp hneg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hr0 : r < 0 := by
    rw [← hr] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr
    exact WithTop.coe_ne_top hr
  set yv := x⁻¹ with hyv
  have hy0 : yv ≠ 0 := inv_ne_zero hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hy0 ((AddValuation.top_iff V.v).mp h))
  have hrs : r + s = 0 := by
    have h1 : V.v (x * yv) = 0 := by rw [hyv, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [AddValuation.map_mul, ← hr, ← hs] at h1
    exact_mod_cast h1
  have hy : V.Ge (-r) yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hy0' : V.Ge 0 yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hpow : ∀ k : ℕ, V.Ge 0 (yv ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact VF.Ge.one
    | succ k ih => rw [pow_succ]; exact VF.Ge.mul_int ih hy0'
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
  set n := p.natDegree
  have hsum : 1 + ∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) = 0 := by
    have h2 := congrArg (· * yv ^ n) hp
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [← h2]
    congr 1
    · rw [← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
      conv_rhs => rw [show n = (n - i) + i from (Nat.sub_add_cancel hi').symm]
      rw [pow_add, mul_assoc, mul_left_comm (x ^ i), ← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow, mul_one]
  have hS : V.Ge (-r) (∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i)) := by
    refine Finset.sum_induction _ (fun z => V.Ge (-r) z) (fun _ _ ha hb => VF.Ge.add ha hb) (VF.Ge.zero _) ?_
    intro i hi
    have hi' : n - i = (n - i - 1) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hi', pow_succ, ← mul_assoc]
    exact VF.Ge.mul_int (VF.Ge.mul_int (hZ _) (hpow _)) hy
  have h1 : (1 : C) = -∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) :=
    eq_neg_of_add_eq_zero_left hsum
  have hS' := VF.Ge.neg hS
  rw [← h1] at hS'
  unfold VF.Ge at hS'
  rw [AddValuation.map_one] at hS'
  have : (-r : ℝ) ≤ 0 := by exact_mod_cast hS'
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem embedding_integral (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)

theorem embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]

theorem embedding_conjugate (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]

theorem a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  rw [show chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) from C3.gen.1.2.2.2.2.2.2 ℓ i]
  exact embIntSt_holds T C V ι hι _

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

end Core

variable (Xo c)

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemC
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIs {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (o : Orb) : Type := Σ t : ZMod 2, Fin (r (tau o t))

def subG {C : Type} [Field C] {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T)
    (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) :
    MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  MvPolynomial.aeval fun x => ∑ col : Fin 2, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) *
    MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n)

def WtTieC {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (gaC : Orb → ZMod 2 → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), gaC o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0

structure SelfConjugatePlaceSetting {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N) : Prop where

  inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2
  conj : ∀ o t, cc (tau o t) = tau o (t + 1)

  gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1

  hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  alt : ∀ o, (X o).Alt
  hj : ∀ o, (X o).j' < (X o).n
  supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s

  mon : ∀ o, ∀ q ∈ L o, ∀ g e M, q.1 = GlobalTheory.mon g e M → ∃ s : ZMod 2, ∀ b k, b ≠ s → e b k = 0
  wt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k
  tie : WtTieC r tau gaC a
  plinj : Function.Injective pl

def IsotropicToStdSubstHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n) (isX : T → Prop),
      subG r tau gm plc (blkProd X F N L pl) ∈ harmK r n C cc isX (fun _ => 1)

def IsotropicToStdSubstLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowInv r n C (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstLineDegree : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowDeg r n C a (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin N) (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (O : Subring C), (∀ o t q s, gm o t q s ∈ O) → ∀ m, (subG r tau gm plc (blkProd X F N L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def selfConjTuplesInLattice : Set (∀ o, MvPolynomial (Fin N × WV fun _ => IIs r tau o) C) :=
  {Po | subG r tau gm plc (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree) (h4 : IsotropicToStdSubstIntegral)
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + 1))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieC r tau gaC a) :
    BlockMembershipSelfConjugate X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by
  intro L mon wt pl plinj
  have H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl := ⟨inj, conj, gm_hyp, hty, std, alt, hj, supp, mon, wt, tie, plinj⟩
  exact ⟨⟨h1 C V T r cc a Orb tau gm J X F gaC N L pl H n plc isX, h2 C V T r cc a Orb tau gm J X F gaC N L pl H n plc,
    h3 C V T r cc a Orb tau gm J X F gaC N L pl H n plc⟩, h4 C V T r Orb tau gm J X F N L pl n plc O gm_int⟩

end Mem

def OP {C : Type} [Field C] (O : Subring C) (σ : Type) : Subring (MvPolynomial σ C) :=
  (MvPolynomial.map O.subtype).range

theorem coeff_mem_of_OP {C : Type} [Field C] {O : Subring C} {σ : Type} {P : MvPolynomial σ C} (h : P ∈ OP O σ)
    (m : σ →₀ ℕ) : P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map]
  exact (Q.coeff m).2

theorem aeval_mem_OP {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  clear h
  induction Q using MvPolynomial.induction_on
  · rename_i z
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, eq_intCast (Int.castRingHom C) z, map_intCast]
    exact intCast_mem _ z
  · rename_i p q hp hq
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp hq
  · rename_i p x hp
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp (hf x)

theorem first_chern_integral : IsotropicToStdSubstIntegral := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hO m
  apply coeff_mem_of_OP
  unfold subG
  refine aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)
  refine sum_mem fun col _ => mul_mem ?_ ?_
  · exact RingHom.mem_range.2 ⟨MvPolynomial.C ⟨_, hO _ _ _ _⟩, by rw [MvPolynomial.map_C]; rfl⟩
  · exact RingHom.mem_range.2 ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Col

variable {dd : ℕ}

theorem hasSubst_col (col : Fin 2) :
    HasSubst (fun x : Fin dd => (X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]

theorem inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by
  unfold inCol
  rw [subst_X (hasSubst_col col)]

theorem coeff_subst_rename_out {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ)
    (he : ∀ e' : σ →₀ ℕ, e'.mapDomain φ ≠ e) :
    coeff e (subst (fun s => (X (φ s) : MvPowerSeries τ C)) F) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e'
  rw [prod_X_rename, coeff_monomial, if_neg (fun h => he e' h.symm), smul_zero]

theorem coeff_inCol_lin (col : Fin 2) (f f' : MvPowerSeries (Fin dd) C)
    (h : ∀ μ : Fin dd →₀ ℕ, μ.degree ≤ 1 → coeff μ f = coeff μ f') (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ (inCol col f) = coeff μ (inCol col f') := by
  unfold inCol
  by_cases hr : ∃ μ' : Fin dd →₀ ℕ, μ'.mapDomain (fun x => (col, x)) = μ
  · obtain ⟨μ', rfl⟩ := hr
    rw [coeff_subst_rename_inj _ (col_inj col), coeff_subst_rename_inj _ (col_inj col)]
    exact h μ' (by rw [Finsupp.degree_mapDomain] at hμ; exact hμ)
  · push_neg at hr
    rw [coeff_subst_rename_out _ _ _ hr, coeff_subst_rename_out _ _ _ hr]

end Col

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem FBChart.self_chart_log_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).lg x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.lg x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.lg_const x.2

theorem FBChart.self_chart_exp_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2

theorem FBChart.rawSelf_axis0 (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he

theorem FBChart.rawSelf_exlg (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).lg (inCol col (un1 (Y.ex i))) = _
  rw [subst_inCol (Y.self_chart_log_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.lg j))) (un1 (Y.ex i)) = _
  have hL : HasSubst (fun j => un1 (Y.lg j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.lg_const]
  have hx : un1 (comp1 Y.ex Y.lg i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.ex_lg]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.lg_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lin (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl

theorem SelfData.gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  have e : p.gm a r s = (p.gm a r s - p.em a (M r s)) + p.em a (M r s) := by ring
  rw [e]
  exact h.add (p.em_int a _)

theorem FBChart.rawSelf_u_integral (g : Fin 2) (c : I0) (x : Fin 2 × Fin dd) : V.Ge 0 ((Y.rawSelf p).u g c x) :=
  VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (p.e_int c x.2)

theorem SelfData.gm_pair (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h

theorem FBChart.exists_integral_right_inverse (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, huw⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c',
    fun x c' => VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (hw0 _ _), fun c c' => ?_⟩
  show ∑ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') = _
  have e1 : ∀ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') =
      (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (1 - g)) * (p.e c x.2 * w0 x.2 c') := fun x => by ring
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, huw c c']
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    simp only [mul_one]
    exact SelfData.gm_pair Y p _ g
  · simp [hc]

def PTSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabSelfSt : Prop :=
  AllSelf fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

theorem cartSelf_of (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }

end Formalism.L2.FormalSeriesBounds
end
end

