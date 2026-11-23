module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionChar
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.TensorInd

section Paths

variable {n : Type} [Fintype n] [DecidableEq n]

theorem trace_reindex_eq {m : Type} [Fintype m] (e : n ≃ m) (A : Matrix n n ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem path_sum : ∀ (k : ℕ) (B : ℕ → Matrix n n ℂ) (a c : n),
    ∑ w : Fin k → n, ∏ i : Fin (k + 1),
      B i ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc)
        ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ)
      = ((List.range (k + 1)).map B).prod a c := by
  intro k
  induction k with
  | zero =>
    intro B a c
    simp [Fin.snoc]
  | succ k ih =>
    intro B a c
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← ih (B ∘ Nat.succ) x c, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hc : (Fin.consEquiv fun _ => n) (x, w) = Fin.cons x w := rfl
    rw [Fin.prod_univ_succ, hc, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc, Function.comp_apply,
      Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one]

theorem cyc_sum (k : ℕ) (B : ℕ → Matrix n n ℂ) :
    ∑ w : Fin (k + 1) → n, ∏ i : Fin (k + 1), B i (w i) (w (i + 1))
      = Matrix.trace ((List.range (k + 1)).map B).prod := by
  rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← path_sum k B a a]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hc : (Fin.consEquiv fun _ => n) (a, w) = Fin.cons a w := rfl
  have h1 : (Fin.cons a w : Fin (k + 1) → n) i
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc := by
    cases i using Fin.cases with
    | zero => simp
    | succ j => rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
  have h2 : (Fin.cons a w : Fin (k + 1) → n) (i + 1)
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ := by
    rw [Fin.cons_succ]
    cases i using Fin.lastCases with
    | last => rw [Fin.last_add_one, Fin.snoc_last, Fin.cons_zero]
    | cast j => rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]
  rw [hc, h1, h2]

end Paths

section Rep

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

def ker (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) (r : Γ) :
    Matrix (Γ → Fin d) (Γ → Fin d) ℂ :=
  fun u v => ∏ t, (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) (u t) (v (t * r))

theorem ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : ker ρ φ 1 1 = 1 := by
  ext u v
  simp only [ker, map_one, Units.val_one, mul_one]
  by_cases h : u = v
  · subst h
    simp
  · obtain ⟨t, ht⟩ := Function.ne_iff.1 h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (Matrix.one_apply_ne ht)

theorem ker_mul (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g₁ g₂ : G) (r₁ r₂ : Γ) :
    ker ρ φ g₁ r₁ * ker ρ φ g₂ r₂ = ker ρ φ (g₁ * φ r₁ g₂) (r₁ * r₂) := by
  ext u v
  simp only [Matrix.mul_apply, ker]
  have hre : ∀ w : Γ → Fin d, ∏ t, (ρ (φ t g₂) : Matrix (Fin d) (Fin d) ℂ) (w t) (v (t * r₂))
      = ∏ t, (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) (w (t * r₁)) (v (t * r₁ * r₂)) :=
    fun w => (Fintype.prod_equiv (Equiv.mulRight r₁) _ _ (fun t => rfl)).symm
  simp_rw [hre, ← Finset.prod_mul_distrib]
  rw [← (Equiv.arrowCongr (Equiv.mulRight r₁) (Equiv.refl (Fin d))).sum_comp]
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.coe_mulRight,
    Equiv.mulRight_symm, mul_inv_cancel_right, id]
  refine (Fintype.prod_sum (fun t (j : Fin d) =>
    (ρ (φ t g₁) : Matrix (Fin d) (Fin d) ℂ) (u t) j *
      (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) j (v (t * r₁ * r₂)))).symm.trans ?_
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [map_mul (φ t), ← MulAut.mul_apply, ← map_mul φ, map_mul ρ, Units.val_mul, Matrix.mul_apply, mul_assoc]

def tensRep (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : G ⋊[φ] Γ →* Matrix (Γ → Fin d) (Γ → Fin d) ℂ where
  toFun x := ker ρ φ x.left x.right
  map_one' := by simpa using ker_one ρ φ
  map_mul' x y := by rw [ker_mul]; simp

theorem trace_ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) :
    Matrix.trace (ker ρ φ g 1) = ∏ t, Matrix.trace (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [Matrix.trace, Matrix.diag, ker, mul_one]
  rw [Fintype.prod_sum]

end Rep

end GlobalTheory.Shin.TensorInd

namespace GlobalTheory.Shin.TensorInd

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

theorem trace_ker_gen (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (s : Γ)
    (hs : ∀ t : Γ, t ∈ Subgroup.zpowers s) (δ : G) :
    Matrix.trace (ker ρ φ δ s) = Matrix.trace (((List.range (Nat.card Γ)).map
      fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ)).prod) := by
  have hl : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  obtain ⟨k, hk⟩ : ∃ k, Nat.card Γ = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Γ)).ne'
  rw [hk] at hl ⊢
  have hinj : Function.Injective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    intro i j hij
    have := pow_injOn_Iio_orderOf (x := s) (by rw [hl]; exact i.2) (by rw [hl]; exact j.2) hij
    exact Fin.ext this
  have hbij : Function.Bijective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hk]
  let e : Fin (k + 1) ≃ Γ := Equiv.ofBijective _ hbij
  have he : ∀ i : Fin (k + 1), e i * s = e (i + 1) := by
    intro i
    show s ^ (i : ℕ) * s = s ^ ((i + 1 : Fin (k + 1)) : ℕ)
    have hv : ((i + 1 : Fin (k + 1)) : ℕ) = ((i : ℕ) + 1) % orderOf s := by
      rw [hl, Fin.val_add_one]
      split_ifs with h
      · subst h; simp
      · rw [Nat.mod_eq_of_lt]
        have := Fin.val_lt_last h
        omega
    rw [hv, pow_mod_orderOf, pow_succ]
  rw [← cyc_sum k (fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ))]
  simp only [Matrix.trace, Matrix.diag, ker]
  rw [← (Equiv.arrowCongr e (Equiv.refl (Fin d))).sum_comp]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, he, Equiv.symm_apply_apply]
  rfl

theorem exists_tensorInduction_char : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hs χ hχ
  obtain ⟨d, ρ, hρ⟩ := (matrixChar_iff_isChar G χ).2 hχ
  let e := Fintype.equivFin (Γ → Fin d)
  let R : G ⋊[φ] Γ →* GL (Fin (Fintype.card (Γ → Fin d))) ℂ := MonoidHom.toHomUnits
    (((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom).comp (tensRep ρ φ))
  refine ⟨fun x => Matrix.trace (tensRep ρ φ x), ?_, ?_, ?_⟩
  · refine (matrixChar_iff_isChar _ _).1 ⟨_, R, fun x => ?_⟩
    show _ = Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e (tensRep ρ φ x))
    rw [Matrix.reindexAlgEquiv_apply, trace_reindex_eq]
  · intro g
    show Matrix.trace (ker ρ φ (inl g).left (inl g).right) = _
    rw [left_inl, right_inl, trace_ker_one]
    exact Finset.prod_congr rfl (fun t _ => (hρ _).symm)
  · intro δ
    show Matrix.trace (ker ρ φ (inl δ * inr s).left (inl δ * inr s).right) = _
    have h1 : (inl δ * inr s : G ⋊[φ] Γ).left = δ := by simp
    have h2 : (inl δ * inr s : G ⋊[φ] Γ).right = s := by simp
    rw [h1, h2, trace_ker_gen ρ φ s hs δ, hρ, nrmG]
    congr 1
    have hm := map_list_prod ((Units.coeHom (Matrix (Fin d) (Fin d) ℂ)).comp ρ)
      ((List.range (Nat.card Γ)).map fun i => φ (s ^ i) δ)
    rw [List.map_map] at hm
    exact hm.symm

end GlobalTheory.Shin.TensorInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtDAlgebraMapPowCharMul
section
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section

variable {K : Type} [CommRing K]

theorem kaehlerZ_span_induction {P : Ω[K⁄ℤ] → Prop} (v : Ω[K⁄ℤ]) (hD : ∀ a, P (KaehlerDifferential.D ℤ K a))
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : K) x, P x → P (c • x)) : P v := by
  have hv : v ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℤ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem kaehlerZ_D_pow_char (c : K) : KaehlerDifferential.D ℤ K (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem extD_algebraMap_pow_char_mul {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by
  rw [hd.mul, hd.alg, kaehlerZ_D_pow_char p, map_zero, zero_mul, zero_add]
  congr 1
  exact AlgHom.commutes _ _

end

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem isDatum_of_frobenius_lifts {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ])
    (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (hπ : IsFlatLift p π)
    (hF : ∀ i, IsFrob p π (F i)) (hd : IsExtD ℤ K d) (hf : ∀ i, IsF p π (F i) (f i))
    (hh : ∀ i j, IsH p π (F i) (F j) (h i j)) : IsDatum p d f h := by

  have hw : ∀ i z, ∃ w, F i z = z ^ p + p * w := by
    intro i z
    obtain ⟨w, hw⟩ := (hπ.ker (F i z - z ^ p)).1 (by rw [map_sub, hF i, map_pow, sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have hsm : ∀ (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]), d (c ^ p • x) = c ^ p • d x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, extD_algebraMap_pow_char_mul p hd]

  have hfD : ∀ i z w, F i z = z ^ p + p * w → ExteriorAlgebra.ι K (f i (KaehlerDifferential.D ℤ K (π z))) =
      algebraMap K _ (π z ^ (p - 1)) * ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z)) +
        d (algebraMap K _ (π w)) := by
    intro i z w hz
    rw [(hf i).2 z w hz, map_add (f := _), map_smul, Algebra.smul_def, hd.alg]
  refine ⟨fun i c v => (hf i).1 c v, fun i j c v => (hh i j).1 c v, ?_, ?_, ?_⟩
  · intro i v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨w, hz⟩ := hw i z
      have h2 : d (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z))) = 0 := by
        rw [← hd.alg, hd.sq]
      rw [hfD i z w hz, map_add (f := _), hd.sq, add_zero, hd.mul, h2, mul_zero, add_zero, hd.alg,
        Derivation.leibniz_pow, map_nsmul, map_smul, smul_mul_assoc, smul_mul_assoc,
        ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | hsmul c x hx => rw [(hf i).1, map_smul, hsm, hx, smul_zero]
  · intro i j v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), hfD i z wi hzi, hfD j z wj hzj, map_sub, map_sub,
        map_sub]
      abel
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]; abel
    | hsmul c x hx =>
      rw [(hh i j).1, (hf i).1, (hf j).1, map_mul, ← Algebra.smul_def, hsm, hx, map_smul, map_smul, smul_sub]
  · intro i j l v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      obtain ⟨wl, hzl⟩ := hw l z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), (hh j l).2 z (wl - wj) (by rw [hzj, hzl]; ring),
        (hh i l).2 z (wl - wi) (by rw [hzi, hzl]; ring), map_sub, map_sub, map_sub]
      ring
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; ring
    | hsmul c x hx => rw [(hh i j).1, (hh j l).1, (hh i l).1, ← hx]; ring

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMono
section
set_option autoImplicit false

namespace GlobalTheory.DI

section
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem forms_gen_mem {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩

theorem forms_le_comap_of_gen {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv

theorem ι_mul_ιMulti_eq (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem ιMulti_one_eq (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem forms_mul_smul_mono (A : Subring K) (L : Set V) :
    (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧
    (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q →
      x * y ∈ forms (A : Set K) L (q + 1)) ∧
    (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧
    (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧
    ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := forms_gen_mem (B := (A : Set K)) (L := L) A.one_mem (Fin.elim0 : Fin 0 → V)
      (fun k => k.elim0)
    simpa using h
  · intro q x y hx hy

    have key : ∀ a ∈ (A : Set K), ∀ u : Fin 1 → V, (∀ k, u k ∈ L) →
        a • ExteriorAlgebra.ιMulti K 1 u * y ∈ forms (A : Set K) L (q + 1) := by
      intro a ha u hu
      have := forms_le_comap_of_gen (B := (A : Set K)) (L := L) (B' := (A : Set K)) (L' := L)
        (q := q) (q' := q + 1) (AddMonoidHom.mulLeft (a • ExteriorAlgebra.ιMulti K 1 u)) ?_ hy
      · exact this
      intro b hb w hw
      show a • ExteriorAlgebra.ιMulti K 1 u * (b • ExteriorAlgebra.ιMulti K q w) ∈ _
      rw [smul_mul_smul_comm, ιMulti_one_eq, ι_mul_ιMulti_eq]
      refine forms_gen_mem (A.mul_mem ha hb) _ ?_
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hu 0
      · simpa using hw k
    exact forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q + 1)
      (AddMonoidHom.mulRight y) (fun a ha u hu => key a ha u hu) hx
  · intro q c y hc hy
    refine forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (A.mul_mem hc hb) v hv
  · intro B q c y hy
    refine forms_le_comap_of_gen (B' := (fun b => c * b) '' B) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (B := (fun b => c * b) '' B) (Set.mem_image_of_mem _ hb) v hv
  · intro B B' L' q hB hL
    refine (forms_le_comap_of_gen (B' := B') (L' := L') (q' := q) (AddMonoidHom.id _) ?_)
    intro b hb v hv
    exact forms_gen_mem (hB hb) v (fun k => hL (hv k))

end

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutAffineFlatAndPushouts
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerAffine

theorem nilKer {A B C D : CommRingCat.{0}} (e : A ≅ B) (g : B ⟶ C) (e' : C ≅ D)
    (h : IsNilpotent (RingHom.ker g.hom)) : IsNilpotent (RingHom.ker (e.hom ≫ g ≫ e'.hom).hom) := by
  have hk : RingHom.ker (e.hom ≫ g ≫ e'.hom).hom = Ideal.map e.inv.hom (RingHom.ker g.hom) := by
    ext x
    have hinj : Function.Injective e'.hom.hom := e'.commRingCatIsoToRingEquiv.injective
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx' : g.hom (e.hom.hom x) = 0 := by
        apply hinj; simpa using hx
      have : x = e.inv.hom (e.hom.hom x) := by
        change x = (e.hom ≫ e.inv).hom x; simp
      rw [this]; exact Ideal.mem_map_of_mem _ hx'
    · intro hx
      rw [RingHom.mem_ker]
      have hle : Ideal.map e.inv.hom (RingHom.ker g.hom) ≤ RingHom.ker (e.hom ≫ g ≫ e'.hom).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        simp only [Ideal.mem_comap, RingHom.mem_ker] at hz ⊢
        change (e'.hom.hom (g.hom ((e.inv ≫ e.hom).hom z))) = 0
        simp [hz]
      exact hle hx
  rw [hk]
  exact h.map (Ideal.mapHom e.inv.hom)

theorem appTop_eq (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]; simp

theorem inv_comp_appTop (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [appTop_eq]; simp

theorem surjTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : Function.Surjective f) :
    Function.Surjective (Spec.map f).appTop := by
  rw [appTop_eq]
  have h1 := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  have h2 := (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.surjective
  exact (h2.comp h).comp h1

theorem nilTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : IsNilpotent (RingHom.ker f.hom)) :
    IsNilpotent (RingHom.ker (Spec.map f).appTop.hom) := by
  rw [appTop_eq]
  exact nilKer (Scheme.ΓSpecIso R) f (Scheme.ΓSpecIso S).symm h

theorem pushout_of_eq (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S)
    (h : IsPullback f g p q) [IsAffine S] [IsAffine S'] (W : X.Opens) (hW : IsAffineOpen W)
    (O : X'.Opens) (hO : f ⁻¹ᵁ W = O) :
    IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.appLE W O hO.ge)
      (g.appLE ⊤ O (fun _ _ => trivial)) := by
  subst hO
  have := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine X X' S S' f g p q h
    inferInstance inferInstance W hW
  rwa [Scheme.Hom.app_eq_appLE] at this

end GlobalTheory.SchlessingerAffine


open GlobalTheory.SchlessingerAffine in
theorem GlobalTheory.SchlessingerAffine.flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hF₁ hF₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂ V hVa
  have hU₁ : IsAffineOpen (j₁ ⁻¹ᵁ V) := hVa.preimage j₁
  have hU₂ : IsAffineOpen (j₂ ⁻¹ᵁ V) := hVa.preimage j₂
  have hPT : IsPullback (Spec.map f₁).appTop (Spec.map f₂).appTop (Spec.map g₁).appTop
      (Spec.map g₂).appTop :=
    IsPullback.of_iso hP (Scheme.ΓSpecIso P).symm (Scheme.ΓSpecIso R₁).symm
      (Scheme.ΓSpecIso R₂).symm (Scheme.ΓSpecIso R₀).symm
      (inv_comp_appTop _ _ f₁).symm (inv_comp_appTop _ _ f₂).symm
      (inv_comp_appTop _ _ g₁).symm (inv_comp_appTop _ _ g₂).symm
  have q₁ := pushout_of_eq Y₁ Y₀ (Spec R₁) (Spec R₀) i₁ p₀ p₁ (Spec.map g₁) h₁ (j₁ ⁻¹ᵁ V) hU₁
    ((i₁ ≫ j₁) ⁻¹ᵁ V) rfl
  have q₂ := pushout_of_eq Y₂ Y₀ (Spec R₂) (Spec R₀) i₂ p₀ p₂ (Spec.map g₂) h₂ (j₂ ⁻¹ᵁ V) hU₂
    ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; rfl)
  have c₁ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₁.app V =
      (Spec.map f₁).appTop ≫ p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₁ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₁ (Spec.map f₁) _ _ _ _ _).symm
    simp only [hy₁]
  have c₂ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₂.app V =
      (Spec.map f₂).appTop ≫ p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₂ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₂ (Spec.map f₂) _ _ _ _ _).symm
    simp only [hy₂]
  exact _root_.GlobalTheory.SchlessingerFlat.schlessinger_flat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPT (surjTop g₁ hs₁) (surjTop g₂ hs₂)
    (nilTop g₁ hn₁) (nilTop g₂ hn₂) q₁ q₂
    (p₁.flat_appLE (isAffineOpen_top _) hU₁ le_top) (p₂.flat_appLE (isAffineOpen_top _) hU₂ le_top)
    (hV V) c₁ c₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass : ∀ {K Z : Type} [Group K] [Finite K] [MulAction K Z] (f : Z → ℂ), (∀ (k : K) (z : Z), f (k • z) = f z) → (Function.support f).Finite → ∑ᶠ o : MulAction.orbitRel.Quotient K Z, ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) = ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  first | exact @GlobalTheory.finsum_orbits_stabilizer_mass | exact GlobalTheory.finsum_orbits_stabilizer_mass | (intros; apply GlobalTheory.finsum_orbits_stabilizer_mass <;> assumption)
end

