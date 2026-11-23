module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBlock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellMain
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S Matrix

variable {E : Type} [Field E] [NumberField E]

def pm (L : List (E × ℕ)) : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E :=
  fun a b => ptEntry L a.val b.val

theorem pm_cons (t : E) (s : ℕ) (bs : List (E × ℕ)) :
    (pm ((t, s) :: bs) : Matrix (Fin (s + (bs.map Prod.snd).sum)) (Fin (s + (bs.map Prod.snd).sum)) E).submatrix
      finSumFinEquiv finSumFinEquiv = fromBlocks (t • revJ E s) 0 0 (pm bs) := by
  ext (i | i) (j | j)
  · show ptEntry ((t, s) :: bs) (i : ℕ) (j : ℕ) = t * (if j = Fin.rev i then (1 : E) else 0)
    simp only [ptEntry]
    rw [if_pos ⟨i.isLt, j.isLt⟩]
    have hiff : ((i : ℕ) + (j : ℕ) + 1 = s) ↔ j = Fin.rev i := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    by_cases h : j = Fin.rev i
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  · show ptEntry ((t, s) :: bs) (i : ℕ) (s + (j : ℕ)) = 0
    have := i.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (j : ℕ) = 0
    have := j.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (s + (j : ℕ)) = ptEntry bs (i : ℕ) (j : ℕ)
    simp only [ptEntry]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

theorem bd_all : ∀ L : List (E × ℕ), (∀ b ∈ L, b.1 ≠ 0 ∧ 1 ≤ b.2) → BDm (pm L) := by
  intro L
  induction L with
  | nil =>
    intro _ d _
    refine ⟨1, one_ne_zero, ?_⟩
    rintro Z _ ⟨L0, U0, hL0, hU0, hZ⟩
    exact ⟨L0, U0, hL0, hU0, hZ, ⟨0, by ext i; exact absurd i.isLt (by simp)⟩,
      ⟨0, by ext i; exact absurd i.isLt (by simp)⟩⟩
  | cons b bs ih =>
    rcases b with ⟨t, s⟩
    intro h
    have ht : t ≠ 0 := (h (t, s) List.mem_cons_self).1
    exact bd_step t ht (pm bs) (pm ((t, s) :: bs)) (pm_cons t s bs)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem map_smul' {m n : Type*} (c : 𝓞 E) (X : Matrix m n (𝓞 E)) :
    (c • X).map (algebraMap (𝓞 E) E) = algebraMap (𝓞 E) E c • X.map (algebraMap (𝓞 E) E) := by
  ext i j; simp

theorem alg_inj {x y : 𝓞 E} (h : algebraMap (𝓞 E) E x = algebraMap (𝓞 E) E y) : x = y :=
  IsFractionRing.injective (𝓞 E) E h

theorem lob_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsLoUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_gt h')]

theorem upb_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsUpUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), UpB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_lt h')]

theorem close_rel {N : ℕ} {D b : 𝓞 E} (W : Matrix (Fin N) (Fin N) E)
    {Lx Ux Ly Uy : Matrix (Fin N) (Fin N) E} (hLx : IsLoUni Lx) (hUx : IsUpUni Ux) (hLy : IsLoUni Ly)
    (hUy : IsUpUni Uy) (hLxi : Intg D Lx) (hUxi : Intg D Ux)
    (ML MU : Matrix (Fin N) (Fin N) (𝓞 E))
    (hL : Ly - Lx = algebraMap (𝓞 E) E (D ^ N * b) • ML.map (algebraMap (𝓞 E) E))
    (hU : Uy - Ux = algebraMap (𝓞 E) E (D ^ N * b) • MU.map (algebraMap (𝓞 E) E)) :
    ∃ A B : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * (Lx * W * Ux) * B.map (fun x => (x : E)) = Ly * W * Uy := by
  have hpow : D ^ N = D ^ (N - (N - 1)) * D ^ (N - 1) := by rw [← pow_add]; congr 1; omega
  obtain ⟨AL, hAL⟩ := intg_adj hLxi
  obtain ⟨AU, hAU⟩ := intg_adj hUxi
  have hA1 : Ly * Lx.adjugate - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (ML * AL)).map (algebraMap (𝓞 E) E)) := by
    rw [← lo_mul_adj hLx, ← Matrix.sub_mul, hL, map_smul', Matrix.map_mul, hAL, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  have hB1 : Ux.adjugate * Uy - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (AU * MU)).map (algebraMap (𝓞 E) E)) := by
    rw [← up_adj_mul hUx, ← Matrix.mul_sub, hU, map_smul', Matrix.map_mul, hAU, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  obtain ⟨A, hA, hAm⟩ := lob_of (lo_mul hLy (lo_adj hLx)) _ hA1
  obtain ⟨B, hB, hBm⟩ := upb_of (up_mul (up_adj hUx) hUy) _ hB1
  refine ⟨A, B, hA, hB, ?_⟩
  rw [hAm, hBm]
  calc Ly * Lx.adjugate * (Lx * W * Ux) * (Ux.adjugate * Uy)
      = Ly * (Lx.adjugate * Lx) * W * (Ux * Ux.adjugate) * Uy := by simp only [Matrix.mul_assoc]
    _ = Ly * W * Uy := by rw [lo_adj_mul hLx, up_mul_adj hUx, Matrix.mul_one, Matrix.mul_one]

end PI.TermsAtPtFiniteW.CellW

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.MainNotions.S CellW

theorem cellReduce_holds : CellReduce := by
  intro E _ _ N p b hb
  obtain ⟨L, hL, hsum⟩ := p
  subst hsum
  obtain ⟨D, hD, hbd⟩ := bd_all L hL 1 one_ne_zero
  let X : Set (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) :=
    {x | IsLoUni x.2.1 ∧ IsUpUni x.2.2 ∧ x.1 = x.2.1 * pm L * x.2.2 ∧ Intg D x.2.1 ∧ Intg D x.2.2}
  let f : (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) →
      Bool × Fin (L.map Prod.snd).sum × Fin (L.map Prod.snd).sum → E := fun x k =>
    if k.1 then algebraMap (𝓞 E) E D * x.2.2 k.2.1 k.2.2 else algebraMap (𝓞 E) E D * x.2.1 k.2.1 k.2.2
  have hf : ∀ x ∈ X, ∀ k, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x k := by
    rintro x ⟨-, -, -, ⟨L', hL'⟩, ⟨U', hU'⟩⟩ ⟨c, i, j⟩
    cases c
    · exact ⟨L' i j, by simpa [f] using congrFun (congrFun hL' i) j⟩
    · exact ⟨U' i j, by simpa [f] using congrFun (congrFun hU' i) j⟩
  have hc : D ^ (L.map Prod.snd).sum * D * b ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) hD) hb
  obtain ⟨Zs, hfin, hZs⟩ := fin_of_cong X f hf _ hc
    (fun x y => ∃ A B : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * x.1 * B.map (fun x => (x : E)) = y.1) (by
    rintro x ⟨hLx, hUx, hx, hLxi, hUxi⟩ y ⟨hLy, hUy, hy, -, -⟩ hxy
    have hDE := alg_ne_zero hD
    have hM : ∀ c : Bool, ∃ M : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E),
        ∀ i j, algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) *
          algebraMap (𝓞 E) E (M i j) = f y (c, i, j) - f x (c, i, j) := by
      intro c
      refine ⟨fun i j => Classical.choose (hxy (c, i, j)), fun i j => ?_⟩
      rw [← Classical.choose_spec (hxy (c, i, j))]
      simp only [map_mul, map_pow]; ring
    obtain ⟨ML, hML⟩ := hM false
    obtain ⟨MU, hMU⟩ := hM true
    have hL : y.2.1 - x.2.1 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • ML.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hML i j
      simp only [f, Bool.false_eq_true, if_false] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    have hU : y.2.2 - x.2.2 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • MU.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hMU i j
      simp only [f, if_true] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    obtain ⟨A, B, hA, hB, hAB⟩ := close_rel (pm L) hLx hUx hLy hUy hLxi hUxi ML MU hL hU
    exact ⟨A, B, hA, hB, by rw [hx, hy]; exact hAB⟩)
  refine ⟨Prod.fst '' Zs, hfin.image _, ?_⟩
  intro Z hZ hcell
  obtain ⟨L1, U1, hL1, hU1, hZe, hL1i, hU1i⟩ := hbd Z (intg_of_entries hZ) hcell
  obtain ⟨y, hy, A, B, hA, hB, hAB⟩ := hZs (Z, L1, U1) ⟨hL1, hU1, hZe, hL1i, hU1i⟩
  exact ⟨A, B, hA, hB, ⟨y, hy, hAB.symm⟩⟩

end PI.TermsAtPtFiniteW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DdSPowLeOne
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ndS_mul_int (D : D7) (a : Fin D.R.rS) (t : D.host.E) (ht : t ∈ aaS D a) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * t := by
  have ha := a.isLt
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.R.rS = (a : ℕ) + m := ⟨D.R.rS - (a : ℕ), by omega⟩
  have haa : aaS D a = (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    unfold aaS ddS
    rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  rw [haa] at ht
  by_cases hJ : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 0
  · rw [hJ] at ht
    have ht0 : t = 0 := by
      first
        | (rw [FractionalIdeal.inv_zero', FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | (rw [inv_zero, FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | simpa using ht
    exact ⟨0, by rw [ht0, map_zero, mul_zero]⟩
  · rw [FractionalIdeal.inv_eq] at ht
    first
      | rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ] at ht
      | rw [FractionalIdeal.mem_div_iff_of_nonzero hJ] at ht
    have hN : ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) :=
      Ideal.pow_mem_pow (Ideal.absNorm_mem _) m
    have hy : algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈
        (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      by
        first
          | exact FractionalIdeal.mem_coeIdeal_of_mem _ hN
          | exact FractionalIdeal.mem_coeIdeal_of_mem hN
          | exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hN, rfl⟩
    have h1 := ht _ hy
    rw [FractionalIdeal.mem_one_iff] at h1
    obtain ⟨o', ho'⟩ := h1
    refine ⟨(Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ (a : ℕ) * o', ?_⟩
    have hsplit : (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ D.R.rS =
        (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ (a : ℕ) * (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ m := by
      rw [← pow_add, ← hm]
    rw [map_mul, ho']
    simp only [ndS, map_pow, map_natCast, Nat.cast_pow, hsplit]
    ring

theorem fInt_holds : FInt := by
  intro D T F0 Λ f L hff hef hL hΛ
  refine ⟨?_, ?_⟩
  ·
    have hd : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
      first
        | exact differentIdeal_ne_bot
        | exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)
        | exact differentIdeal_ne_bot ℤ ℚ D.host.F (𝓞 D.host.F)
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
      first
        | exact FaithfulSMul.algebraMap_injective _ _
        | exact NoZeroSMulDivisors.algebraMap_injective _ _
        | (have h1 : Function.Injective (algebraMap (𝓞 D.host.F) D.host.E) := by
             rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) D.host.F D.host.E, RingHom.coe_comp]
             exact (algebraMap D.host.F D.host.E).injective.comp (IsFractionRing.injective _ _)
           rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, RingHom.coe_comp] at h1
           exact h1.of_comp)
    have hmap : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hN : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    unfold ndS
    exact pow_pos (Nat.pos_of_ne_zero hN) _
  · intro x hx c

    have hec : ∀ a, (VS D).hT (f c) (F0.e a) = if a = c then 1 else 0 := by
      intro a
      have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f c)) = (VS D).hT (f c) (F0.e a) := by
        first
          | exact (VS D).herm.eq _ _
          | exact (VS D).herm _ _
      rw [← hs, hef]
      split_ifs <;> simp
    let P : Submodule (𝓞 D.host.E) (VS D).V :=
      { carrier := {y | ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)}
        add_mem' := by
          rintro y z ⟨o1, h1⟩ ⟨o2, h2⟩
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y + z) from ⟨o1 + o2, by rw [map_add (f := _), map_add (f := _), mul_add, h1, h2]⟩)
        zero_mem' := by
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (0) from ⟨0, by rw [map_zero, map_zero, mul_zero]⟩)
        smul_mem' := by
          rintro r y ⟨o, h⟩
          refine (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (r • y) from ⟨r * o, ?_⟩)
          rw [← algebraMap_smul D.host.E r y, map_smul, smul_eq_mul, map_mul, h]
          ring }
    have hP : Λ ≤ P := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • F0.e a)
        rw [map_smul, smul_eq_mul, hec a]
        by_cases hac : a = c
        · subst hac
          obtain ⟨o, ho⟩ := ndS_mul_int D a t ht
          exact ⟨o, by rw [ho, if_pos rfl, mul_one]⟩
        · exact ⟨0, by rw [if_neg hac, mul_zero, mul_zero, map_zero]⟩
      · intro y hy
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)
        exact ⟨0, by rw [(hL y hy c).2, mul_zero, map_zero]⟩
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • f a)
        exact ⟨0, by rw [map_smul, smul_eq_mul, hff c a, mul_zero, mul_zero, map_zero]⟩
    obtain ⟨o, ho⟩ := hP hx
    exact ⟨o, ho⟩

end PI.TermsAtPtFiniteW
end
end

