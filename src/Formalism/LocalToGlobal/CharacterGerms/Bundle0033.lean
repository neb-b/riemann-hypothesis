module

public import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
public import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0030
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0031
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0032
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0029
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePIndAr

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ConstantZeroRestrictPoints
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv (R := C) q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv (R := C) ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FirstVanishingCore
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogarithmSeriesLinearTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg0 (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp), MvPowerSeries.coeff_zero_X]

theorem exlg (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (lg0 Y)
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', exlg Y, MvPowerSeries.subst_X hA']

theorem lin (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  have hinj : Function.Injective (fun x : Fin dd => ((0 : Fin 1), x)) := fun a b h => (Prod.mk.inj h).2
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) μ) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  congr 1
  apply propext
  rw [← Finsupp.mapDomain_single, (Finsupp.mapDomain_injective hinj).eq_iff]

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => lin Y i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hL i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem lg_mulCv' (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (n : ℕ) (j : Fin dd) :
    MvPowerSeries.subst (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k))
        (un1 (Y.lg j)) = (n : C) • alongCv γ (un1 (Y.lg j)) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hM : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => mulL Y.B.G.F n q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n k)
  have h := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2)) (MulLFrob.lg_mulL Y n j)
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply hM hG,
    show (n • Y.lg j) = (n : C) • Y.lg j from (Nat.cast_smul_eq_nsmul C n _).symm,
    MvPowerSeries.subst_smul hG] at h
  show _ = (n : C) • MvPowerSeries.subst γ (un1 (Y.lg j))
  rw [subst_singlePointUncurry hL0, subst_singlePointUncurry hγ0]
  exact h

theorem coeff_l_mulCv_core (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (k : Fin dd) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k)
  have hX0 : ∀ (a : C), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X () : PowerSeries C)) = 0 := by
    intro a
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hcl : ∀ j, MvPowerSeries.constantCoeff (alongCv γ (un1 (Y.lg j))) = 0 := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) hγ0 (lg0 Y j)
  have eL := ex_lg_at' Y _ hL0 k
  simp only [lg_mulCv' Y hγ0 V.l] at eL
  have hAL : Agr (V.l ^ 2) (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
      (MvPowerSeries.subst (fun j => ((V.l : C) * U j) • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eL]
    refine agr_subst_left (fun j => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcl j, mul_zero])
      (fun j => hX0 _) (fun j => ?_) _
    have := FirstVanishing.Agr.smul (hL j) (V.l : C)
    rwa [smul_smul] at this
  have eG := ex_lg_at' Y γ hγ0 k
  have hAG : Agr (V.l ^ 2) (γ k)
      (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) (un1 (Y.ex k))) := by
    rw [← eG]
    exact agr_subst_left hcl (fun j => hX0 _) (fun j => hL j) _
  have hdeg : (Finsupp.single () V.l).degree < V.l ^ 2 := by
    rw [Finsupp.degree_single]
    nlinarith
  have e1 := hAL _ hdeg
  have e2 := hAG _ hdeg
  change PowerSeries.coeff V.l _ = PowerSeries.coeff V.l _ at e1 e2
  rw [e1, FirstVanishing.coeff_subst_scale, ← e2]
  obtain ⟨m, hm⟩ : ∃ m, V.l = m + 1 := ⟨V.l - 1, by omega⟩
  have e3 : (V.l : C) ^ V.l = (V.l : C) * (V.l : C) ^ m := by
    rw [← pow_succ', ← hm]
  rw [e3, mul_assoc]
  exact mm_l_mul ((VF.Ge.pow (ge_natCast V.l) m).mul_int ((hγ k).2 V.l))

end LogarithmSeriesLinearTerm

theorem first_vanishing_core : FirstVanishingCore := by
  intro C _ _ V O _ _ dd Y γ U hγ hL k
  have hB := LogarithmSeriesLinearTerm.coeff_l_mulCv_core Y hγ hL k
  have hA := FirstVanishing.coeff_l_mulCv_frob Y hγ k
  simp only [LogarithmSeriesLinearTerm.coeff1_of_lgLin Y hγ hL] at hA
  have h := MaximalIdealCongruence.mm_sub hB hA
  rwa [sub_sub_cancel] at h

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.PullbackLogCoordsEvalZero
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv (R := C) i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

end VP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigD
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey

theorem keyEig_of (hT : TeichSt) (hJ : JointEigSt) : KeyEigSt := by
  intro C _ _ V hAlg hc O _ n d hd0 K v
  have hd : d ≠ 0 := NeZero.ne d
  have hq2 : 2 ≤ V.l ^ d := le_trans V.l_prime.two_le (Nat.le_self_pow hd _)
  obtain ⟨m, w, hsum, hw⟩ := hJ C hAlg n (V.l ^ d) hq2 {τ | τ ∈ Acl K ∧ τ ^ V.l ^ d = τ}
    (fun _ ht => ht.2) (fun _ hs _ ht => comm_mem K hs.1 ht.1) (Matrix.mulVec K.P v)
  set w' : Fin m → Fin n → C := fun j => Matrix.mulVec K.P (w j) with hw'
  have hPq : K.P ^ V.l ^ d = K.P := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero d V.l_prime.ne_zero)
    rw [hk]
    clear hk
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, P_idem]

  have hw'e : ∀ j, ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ (w' j) = c • w' j := by
    intro j τ hτ hτq
    obtain ⟨c, hc'⟩ := hw j τ ⟨hτ, hτq⟩
    refine ⟨c, ?_⟩
    rw [hw', Matrix.mulVec_mulVec, comm_mem K hτ (P_mem K), ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
  have hPw' : ∀ j, Matrix.mulVec K.P (w' j) = w' j := fun j => by
    rw [hw', Matrix.mulVec_mulVec, P_idem]
  have hρ : ∀ j x, ∃ σ : C, Matrix.mulVec (K.ρ x) (w' j) = σ • w' j := by
    intro j x
    obtain ⟨σ, hσ⟩ := scal K hT hc hd (S_mem K x) (w' j) (hw'e j)
    refine ⟨σ, ?_⟩
    rw [← hPw' j, Matrix.mulVec_mulVec, ← P_comm, hPw' j]
    exact hσ
  have hχ : ∀ j, ∃ χ : O →+* C, ∀ x, Matrix.mulVec (K.ρ x) (w' j) = χ x • w' j := by
    intro j
    by_cases h0 : w' j = 0
    · exact ⟨K.em 0, fun x => by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    choose σ hσ using hρ j
    have uniq : ∀ a b : C, a • w' j = b • w' j → a = b := fun a b h => smul_left_injective C h0 h
    refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩
    · exact uniq _ _ (by rw [← hσ 1, map_one, Matrix.one_mulVec, one_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x * y), map_mul, ← Matrix.mulVec_mulVec, hσ y, Matrix.mulVec_smul, hσ x, smul_smul, mul_comm]
    · exact uniq _ _ (by rw [← hσ 0, map_zero, Matrix.zero_mulVec, zero_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x + y), map_add (f := _), Matrix.add_mulVec, hσ x, hσ y, add_smul]
  choose χ hχ using hχ
  refine ⟨m, w', χ, ?_, fun j => ⟨hPw' j, hχ j⟩⟩
  rw [hw', ← Matrix.mulVec_sum, ← hsum, Matrix.mulVec_mulVec, P_idem]

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimSelf
section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem limSelf_holds : LimSelfSt := by
  unfold LimSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.rawSelf p) V.l_prime.two_le
    (fun i => FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.self_chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem typ_link (V : VF C) (g : Fin 2) {L : ℕ → I g ⊕ JJ I g → C} (hL : L ∈ X.AllSet V g)
    (h0 : ∀ n k, (¬ ∃ s, V.l ^ s = n) → L n k = 0) :
    (fun s k => L (V.l ^ s) k) ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hL
  have key : ∀ k, tyS V.l (fun s => L (V.l ^ s) k) = PowerSeries.mk (fun n => L n k) := by
    intro k
    apply tyS_eq V.l_prime.two_le
    · intro s; rw [PowerSeries.coeff_mk]
    · intro m hm
      rw [PowerSeries.coeff_mk]
      exact h0 m k (fun ⟨s, hs⟩ => hm s hs)
  refine ⟨γ, lam, hγ, hlam, ?_, ?_⟩
  · intro i; simp only [key]; exact h1 i
  · intro q; simp only [key]; exact h2 q

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

