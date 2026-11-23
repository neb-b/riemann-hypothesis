module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanSt
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def HaSpanSt : Prop :=
  ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (K : Type) [Field K] [CharZero K] (O : Subring K), ∀ P ∈ HaO r n K O cc isX a,
    ∃ (m : ℕ) (c : Fin m → K) (Z : Fin m → MvPolynomial (Letter Ty r n) ℤ), (∀ i, c i ∈ O) ∧
      (∀ i (K' : Type) [Field K'] [CharZero K'], MvPolynomial.map (Int.castRingHom K') (Z i) ∈ HHa r n K' cc isX a) ∧
      P = ∑ i, c i • MvPolynomial.map (Int.castRingHom K) (Z i)

section Nab

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def gofY (Y : FBChart C V O dd) (n : ℕ) : PS C n dd :=
  FB.expS C (((Y.k : ℕ) : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))

theorem nab_eq_nabL (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (g : PS C n dd) (P : MvPolynomial (Ls.ι n) C) :
    Y.nab Ls n g P = DescP.nabL (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (gofY Y n) g :=
  rfl

end Nab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descSpanSt_of (hS : HaSpanSt) : DescSpanSt Xo c := by
  intro T io y C3 C _ _ V ι _hι k Y _hY a n P hP f hf
  have : CharZero T.Fr := charZero_of_inj_zero fun x hx => by
    have h1 := congrArg ι hx
    rwa [map_natCast, map_zero, Nat.cast_eq_zero] at h1
  obtain ⟨m, cc, Z, hc, hZ, hPe⟩ :=
    hS (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) C V.RR P hP
  let Q : Fin m → MvPolynomial (LtN Dw n) T.Fr := fun i => MvPolynomial.map (Int.castRingHom T.Fr) (Z i)
  have hmap : ∀ i, MvPolynomial.map ι (Q i) = MvPolynomial.map (Int.castRingHom C) (Z i) := by
    intro i
    simp only [Q]
    rw [MvPolynomial.map_map, RingHom.ext_int (ι.comp (Int.castRingHom T.Fr)) (Int.castRingHom C)]
  let Ls := chartLetterSystem C3 V ι a
  let tc : (Fin n × Fin (chD C3.ch) →₀ ℕ) → C := fun μ =>
    AddMonoidAlgebra.coeff (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f) μ
  have hP2 : ∀ g : PS C n (chD C3.ch),
      Y.nab Ls n g P = ∑ i, cc i * Y.nab Ls n g (MvPolynomial.map ι (Q i)) := by
    intro g
    have hg : ∀ i, Y.nab Ls n g (MvPolynomial.map ι (Q i)) = Y.nab Ls n g (MvPolynomial.map (Int.castRingHom C) (Z i)) :=
      fun i => congrArg (Y.nab Ls n g) (hmap i)
    simp only [hg, nab_eq_nabL]
    show MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (g * gofY Y n)) =
      ∑ i, cc i * MvPowerSeries.constantCoeff
        (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) (MvPolynomial.map (Int.castRingHom C) (Z i)) (g * gofY Y n))
    rw [hPe]
    exact DescP.const_dpolyN_lin (Y.B.FK C) (Ls.cp n) (Ls.uv n) Finset.univ cc _ (g * gofY Y n)
  have hmono : ∀ μ : Fin n × Fin (chD C3.ch) →₀ ℕ,
      (MvPowerSeries.monomial μ (1 : C) : PS C n (chD C3.ch)) =
        MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr)) := by
    intro μ
    rw [MvPowerSeries.map_monomial, ι.map_one]
  let S := (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f).support
  let g' : (Fin n × Fin (chD C3.ch) →₀ ℕ) × Fin m → C := fun x =>
    (tc x.1 * cc x.2) * Y.nab Ls n (MvPowerSeries.map ι (MvPowerSeries.monomial x.1 (1 : T.Fr)))
      (MvPolynomial.map ι (Q x.2))
  have hmain : Y.nab Ls n f P = ∑ x ∈ S ×ˢ (Finset.univ : Finset (Fin m)), g' x := by
    rw [Finset.sum_product, nab_eq_nabL, DescP.nabL_trunc]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← nab_eq_nabL, hP2, hmono μ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g', tc]
    ring
  obtain ⟨N, e, _he, hsum⟩ := DescP.exists_fin_sum (S ×ˢ (Finset.univ : Finset (Fin m))) g'
  refine ⟨N, fun j => tc (e j).1 * cc (e j).2, fun j => Q (e j).2,
    fun j => MvPowerSeries.monomial (e j).1 (1 : T.Fr), ?_, ?_, ?_, ?_⟩
  · intro j
    have htc : V.Ge 0 (tc (e j).1) := by
      simp only [tc]
      rw [MvPowerSeries.coeff_trunc']
      split_ifs
      · exact hf _
      · exact VF.Ge.zero 0
    exact VF.Ge.mul_int htc (hc (e j).2)
  · intro j
    refine ⟨hZ (e j).2 T.Fr, fun μ => ?_⟩
    simp only [Q]
    rw [MvPolynomial.coeff_map, eq_intCast]
    exact ⟨((AddMonoidAlgebra.coeff (Z (e j).2) μ : ℤ) : T.V), map_intCast _ _⟩
  · intro j μ
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hmain, hsum]

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePGaugeMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

private theorem cc_subst_lemma_2 {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem cc_ev_eq {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma_2 (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem constantCoeff_eval_pair {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := cc_ev_eq ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MapFB

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h

end Formalism.L2.FormalSeriesBounds.GmExArith
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem subst_zero_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, a s = 0)
    {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : MvPowerSeries.subst a f = 0 := by
  have h0 : a = 0 := funext ha
  subst h0
  have hs : MvPowerSeries.HasSubst (0 : σ → MvPowerSeries τ C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  ext e
  rw [MvPowerSeries.coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hsd⟩ : ∃ s, d s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have hp : (d.prod fun s n => (0 : σ → MvPowerSeries τ C) s ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hsd)
      simp [zero_pow hsd]
    rw [hp, map_zero, smul_zero]

private theorem ev_C_mul' {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (MvPowerSeries.C c * f) = MvPowerSeries.C c * ev a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ev_eq_alg ha, ev_eq_alg ha, map_smul]

theorem act_nat_mul (Y : FBChart C V O dd) (k : ℕ) (w : O) (j : Fin dd) :
    Y.B.A.act ((k : O) * w) j =
      ev ![fun j' => MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg j')] (Y.ex j) := by
  have hk : ∀ i, Y.B.A.act (k : O) i = ev ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] (Y.ex i) := by
    intro i
    have h := ex_lg_comp Y (Y.B.A.act (k : O)) (Y.B.A.const _) i
    simp only [lg_act_nat] at h
    exact h.symm
  have hw : Z0 ![Y.B.A.act w] := by
    intro k' i'
    fin_cases k'
    simp [Y.B.A.const]
  have hb : Z0 ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] := by
    intro k' i'
    fin_cases k'
    simp [lg_const]
  rw [Y.B.A.mul_act]
  show ev ![Y.B.A.act w] (Y.B.A.act (k : O) j) = _
  rw [hk, ev_ev hb hw]
  congr 1
  funext k' i'
  fin_cases k'
  show ev ![Y.B.A.act w] (MvPowerSeries.C (k : C) * Y.lg i') = MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg i')
  exact ev_C_mul' hw _ _

theorem tends_lpow : Tends V (fun n => ((V.l ^ (n + 1) : ℕ) : C)) 0 := by
  apply tends_of_nat
  intro N
  refine ⟨N, fun n hn => ?_⟩
  show ((N : ℝ) : WithTop ℝ) ≤ V.v (0 - ((V.l ^ (n + 1) : ℕ) : C))
  rw [zero_sub, AddValuation.map_neg, Nat.cast_pow, AddValuation.map_pow, V.v_l, nsmul_one]
  have h2 : ((N : ℝ) : WithTop ℝ) ≤ (((n + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_le_coe]
    exact_mod_cast (by omega : N ≤ n + 1)
  simpa using h2

theorem lSmall_holds : LSmallSt := by
  intro C _ _ V O _ _ dd Y x x' hx N i μ
  have hx' : ∀ n, ∃ c, x n - x' n = (V.l : O) ^ (n + 1) * c := fun n => hx n
  choose y hy using hx'
  have hsmall : ∀ (z : ℕ → O) (j : Fin dd),
      TendsS V (fun n => Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * z n) j) 0 := by
    intro z j
    have hw : ∀ n, Z0 ![Y.B.A.act (z n)] := by
      intro n k' i'
      fin_cases k'
      simp [Y.B.A.const]
    have hg : ∀ s2 : Fin dd, BddS V (fun n => ev ![Y.B.A.act (z n)] (Y.lg s2)) := by
      intro s2
      exact BddS.subst (a := fun n (p : Fin 1 × Fin dd) => (![Y.B.A.act (z n)] p.1) p.2)
        (f := fun _ => Y.lg s2)
        (by
          rintro n ⟨t1, t2⟩
          fin_cases t1
          simp [Y.B.A.const])
        (by
          rintro ⟨t1, t2⟩
          fin_cases t1
          exact BddS.of_int (fun n => Y.intAct _ _))
        (BddS.const _)
    have hcl := Close.subst (V := V)
      (a := fun n (p : Fin 1 × Fin dd) =>
        (![fun j' => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg j')] p.1) p.2)
      (b := fun _ _ => 0)
      (by
        rintro n ⟨s1, s2⟩
        fin_cases s1
        simp [const_ev (hw n) (lg_const Y s2)])
      (by intros; simp)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show BddS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2))
        apply BddS.mul _ (hg s2)
        intro ν
        refine ⟨0, fun n => ?_⟩
        show V.Ge 0 (MvPowerSeries.coeff ν (MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C))))
        rw [MvPowerSeries.coeff_C]
        split_ifs
        · exact ge_natCast _
        · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
          simp)
      (fun _ => BddS.const 0)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show TendsS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2) - 0) 0
        simp only [sub_zero]
        simp only [mul_comm (MvPowerSeries.C _)]
        apply TendsS.mul_bdd (hg s2)
        intro ν
        simp only [MvPowerSeries.coeff_C, map_zero]
        split_ifs
        · exact tends_lpow
        · exact tends_const 0)
      (Y.ex j)
    have h0 : MvPowerSeries.subst (fun _ : Fin 1 × Fin dd => (0 : MvPowerSeries (Fin 1 × Fin dd) C)) (Y.ex j) = 0 :=
      subst_zero_of (fun _ => rfl) (Y.ex_const j)
    intro ν
    have h1 := hcl ν
    simp only [h0, sub_zero] at h1
    simp only [act_nat_mul]
    exact h1
  have heq : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x n) i := by
    intro n
    have hxn : x n = x' n + ((V.l ^ (n + 1) : ℕ) : O) * y n := by
      rw [Nat.cast_pow, ← hy n]
      ring
    rw [hxn, Y.B.A.add_act]
    rfl
  have heq' : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x' n) i := by
    intro n
    have hxn : Y.B.A.act (x' n) i =
        Y.B.A.act (x' n + ((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n) i := by
      simp
    rw [hxn, Y.B.A.add_act]
    rfl
  have hcl := Close.subst (V := V)
    (a := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2)
    (b := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2)
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1
      · exact Close.refl (fun n => Y.B.A.act (x' n) s2)
      · intro ν
        have h1 := hsmall y s2 ν
        have h2 := hsmall (fun _ => 0) s2 ν
        have h3 := h1.sub h2
        simp only [map_zero, sub_zero] at h3
        rw [map_zero]
        simp only [map_sub]
        exact h3)
    (Y.B.G.F i)
  obtain ⟨n0, hn0⟩ := hcl μ (N : ℝ)
  refine ⟨n0, fun n hn => ?_⟩
  have h4 := hn0 n hn
  simp only [heq, heq', map_zero, zero_sub, map_sub] at h4
  show ((N : ℝ) : WithTop ℝ) ≤ V.v _
  have h5 : ((N : ℝ) : WithTop ℝ) ≤ V.v (-(MvPowerSeries.coeff μ (Y.B.A.act (x n) i) -
      MvPowerSeries.coeff μ (Y.B.A.act (x' n) i))) := h4
  rwa [AddValuation.map_neg] at h5

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePNvalEqSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem nvalEqSt_holds : NvalEqSt := by
  intro T C _ V ι hι x
  unfold nval eOf
  have hl : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rwa [map_natCast] at h
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl, map_zero, AddValuation.map_zero]
    rfl
  · rw [if_neg hx, hι x hx]
    have he : ((vV T.V ((V.l : ℕ) : T.Fr)).toNat : ℝ) = (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
      first
        | exact_mod_cast Int.toNat_of_nonneg hl
        | rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg hl]
    rw [he]
    rfl

end Formalism.L2.FormalSeriesBounds
end
end

