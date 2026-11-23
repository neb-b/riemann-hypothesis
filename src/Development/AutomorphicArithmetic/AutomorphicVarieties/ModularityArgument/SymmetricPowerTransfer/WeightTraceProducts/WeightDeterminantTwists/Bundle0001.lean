module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale
section
open Polynomial UpperTheory.V.Z.Sym.Wt

open MvPolynomial in
private theorem coeff_scale {σ : Type} [Fintype σ] (t : σ → ℂ) (P : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) P : MvPolynomial σ ℂ).coeff m =
      (∏ p, t p ^ m p) * P.coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have : (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) (MvPolynomial.monomial u a) : MvPolynomial σ ℂ) =
        MvPolynomial.C (∏ p, t p ^ u p) * MvPolynomial.monomial u a := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
      ring
    rw [this, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

open MvPolynomial in
private theorem eval_scale {σ : Type} (t x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) P : MvPolynomial σ ℂ) =
      MvPolynomial.eval (fun p => t p * x p) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem UpperTheory.V.Z.Sym.Wt.memMH :
    UpperTheory.V.Z.Sym.Wt.MemMH := by
  intro K _ d n P
  classical
  have e : ∀ (s : K → ℂ) (m : K × Fin d →₀ ℕ), ∏ p : K × Fin d, s p.1 ^ m p = ∏ k, s k ^ ∑ i, m (k, i) := fun s m => by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ (fun i => m (k, i)) (s k)
  constructor
  · intro h m hm k
    have h1 : (MvPolynomial.aeval (fun p : K × Fin d => MvPolynomial.C (Function.update (fun _ => (1 : ℂ)) k 2 p.1) * MvPolynomial.X p) P :
        MvPolynomial (K × Fin d) ℂ) = MvPolynomial.C (∏ v, Function.update (fun _ => (1 : ℂ)) k 2 v ^ n v) * P :=
      MvPolynomial.funext fun x => by rw [eval_scale, map_mul, MvPolynomial.eval_C]; exact h _ x
    have h2 := congrArg (AddMonoidAlgebra.coeff · m) h1
    rw [coeff_scale, MvPolynomial.coeff_C_mul, e] at h2
    have h3 := mul_right_cancel₀ (MvPolynomial.mem_support_iff.1 hm) h2
    have h4 : ∀ a : K → ℕ, ∏ v, Function.update (fun _ => (1 : ℂ)) k 2 v ^ a v = 2 ^ a k := fun a => by
      rw [Finset.prod_eq_single k] <;> simp +contextual [Function.update_of_ne]
    rw [h4, h4] at h3
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast h3)
  · intro h s x
    rw [← eval_scale, ← MvPolynomial.eval_C (f := x) (∏ v, s v ^ n v), ← map_mul]
    congr 1
    ext m
    rw [coeff_scale, MvPolynomial.coeff_C_mul, e]
    by_cases hm : m ∈ P.support
    · simp only [h m hm]
    · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HOption
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem ev_h {σ : Type} [Fintype σ] [DecidableEq σ] (x : σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm σ ℂ n) = ∑ s : Sym σ n, ((s : Multiset σ).map x).prod := by
  simp [MvPolynomial.hsymm, map_multiset_prod, Multiset.map_map]

private theorem h_option {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (n + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ n) +
        MvPolynomial.eval (fun i => x (some i)) (MvPolynomial.hsymm σ ℂ (n + 1)) := by
  rw [ev_h, ev_h, ev_h, ← Equiv.sum_comp (symOptionSuccEquiv).symm, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [symOptionSuccEquiv, Equiv.coe_fn_symm_mk, SymOptionSuccEquiv.decode_inl]
    rw [Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [symOptionSuccEquiv, Multiset.map_map, Function.comp_def]

private theorem h_equiv {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (e : σ ≃ τ)
    (x : τ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm τ ℂ n) = MvPolynomial.eval (x ∘ e) (MvPolynomial.hsymm σ ℂ n) := by
  rw [ev_h, ev_h, ← Equiv.sum_comp (Sym.equivCongr e)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Sym.equivCongr, Multiset.map_map]

private theorem h_succ (d : ℕ) (x : Fin (d + 1) → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (n + 1)) =
      x 0 * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ n) +
        MvPolynomial.eval (fun i => x (Fin.succ i)) (MvPolynomial.hsymm (Fin d) ℂ (n + 1)) := by
  rw [h_equiv (finSuccEquiv d).symm x, h_equiv (finSuccEquiv d).symm x, h_option]
  simp

private theorem h_one (x : Fin 1 → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin 1) ℂ n) = x 0 ^ n := by
  rw [ev_h]
  have hs : ∀ s : Sym (Fin 1) n, ((s : Multiset (Fin 1)).map x).prod = x 0 ^ n := by
    intro s
    have hrep : (s : Multiset (Fin 1)).map x = Multiset.replicate n (x 0) := by
      rw [Multiset.eq_replicate]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hb
      rw [Subsingleton.elim a 0]
    rw [hrep, Multiset.prod_replicate]
  rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
  simp

private theorem hq_step (a b : ℂ) (n : ℕ) :
    hq (a + b) (a * b) (n + 1) = a * hq (a + b) (a * b) n + b ^ (n + 1) := by
  induction n with
  | zero => simp [hq.eq_1, hq.eq_2]
  | succ k ih =>
    rw [hq.eq_3, ih]
    ring

theorem UpperTheory.V.Z.Sym.Wt.hqTwo :
    UpperTheory.V.Z.Sym.Wt.HqTwo := by
  intro j a b
  induction j with
  | zero =>
    have h0 : ∀ s : Sym (Fin 2) 0, ((s : Multiset (Fin 2)).map ![a, b]).prod = 1 := by
      intro s
      rw [Subsingleton.elim s Sym.nil]
      simp
    rw [ev_h, Finset.sum_congr rfl fun s _ => h0 s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
    simp [hq.eq_1]
  | succ k ih =>
    rw [hq_step, ← ih]
    refine (h_succ 1 ![a, b] k).trans ?_
    rw [h_one]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HqKappa
section
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt
private theorem hq_kap (τ : ℂ) (j : ℕ) : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j ∧ hq (2 + τ) (2 + τ) (2 * (j+1) + 1) = (2 + τ) ^ (j + 2) * hq τ 1 (j+1) := by
  have e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i :=
    fun i => hq.eq_3 _ _ i
  have f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i := fun i => hq.eq_3 _ _ i
  induction j with
  | zero =>
    have e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0 := e 0
    have e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1 := e 1
    refine ⟨?_, ?_⟩
    · show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0
      rw [hq.eq_2, hq.eq_1]
      ring
    · show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1
      rw [e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]
      ring
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e5 : hq (2 + τ) (2 + τ) (2 * j + 5) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) := e (2 * j + 3)
    have e4 : hq (2 + τ) (2 + τ) (2 * j + 4) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) := e (2 * j + 2)
    have e3 : hq (2 + τ) (2 + τ) (2 * j + 3) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1) := e (2 * j + 1)
    have f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j := f j
    have i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j := ih.1
    have i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1) := ih.2
    show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)
    rw [f2]
    linear_combination e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0
theorem hqKappa : HqKappa := fun j τ => (hq_kap τ j).1
end UpperTheory.V.Z.Sym.Wt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.MainOf
section
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt

private theorem map_invT {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map f (invT R d g) = invT ℂ d (Matrix.GeneralLinearGroup.map f g) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply, invT_val, invT_val, ← map_inv, Matrix.transpose_apply,
    Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply]

private theorem map_scal {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin d) x) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map f.toMonoidHom x) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, apply_ite f]

private theorem val_map {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = (g : Matrix (Fin d) (Fin d) R).map f := rfl

theorem wtMain_of (h1 : FinMH) (h2 : ThFacts) (h3 : TwineC) (h4 : TrDC) (h5 : Scalars) (h6 : HqKappa) : WtMain := by
  intro R I _ _ em j hj
  classical
  have hWG : ∀ g : GL (Fin 3) R,
      WG em j g = repG I j (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ => rfl
  have hWD : ∀ (n : ℕ) (e : ℤ) (g : GL (Fin 2) R),
      WD em n e g = repD I n e (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ _ _ => rfl
  have hdet : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
        em w (g : Matrix (Fin 2) (Fin 2) R).det := by
    intro w g
    rw [val_map, RingHom.map_det]
    rfl
  have htr : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
        em w (g : Matrix (Fin 2) (Fin 2) R).trace := by
    intro w g
    rw [val_map, AddMonoidHom.map_trace]
  refine
    { finG := ?_, finD := ?_, th_sq := (h2 I j).1, th_rep := ?_, scalG := ?_, scalD := ?_,
      twine := ?_, stable := ?_, kappa := ?_ }
  · haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => h1 _ _ _
    infer_instance
  · intro n
    exact h1 _ _ _
  · intro g
    rw [hWG, hWG, (h2 I j).2]
    have hfun : (fun v => invT ℂ 3 (Matrix.GeneralLinearGroup.map (em v) g)) =
        fun w => Matrix.GeneralLinearGroup.map (em w) (invT R 3 g) :=
      funext fun v => (map_invT _ _ _).symm
    rw [hfun]
  · intro x
    rw [hWG]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 3) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun]
    exact (h5 I _).1 j
  · intro n e x
    rw [hWD]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun, (h5 I _).2 n e]
    congr 1
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  · intro δ τ hch
    rw [hWG]
    refine h3 I j hj (fun w => Matrix.GeneralLinearGroup.map (em w) δ) (fun w => em w τ) ?_
    intro v
    rw [← map_invT, ← map_mul, val_map, Matrix.charpoly_map, hch]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add (f := _)]
  · intro e γ hγ
    rw [hWD, h4]
    show _ = ∏ w, hq (em w (γ : Matrix (Fin 2) (Fin 2) R).trace) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hdet, htr, hγ, map_one, one_zpow, one_mul]
  · intro z τ htz hdz
    rw [hWD, h4]
    show _ = ∏ w, hq (em w τ) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    have hu : em w (z : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
      have hz : IsUnit (z : Matrix (Fin 2) (Fin 2) R).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.isUnit _
      exact (hz.map (em w)).ne_zero
    rw [hdet, htr, htz, hdz, map_add (f := _), map_ofNat, h6 j (em w τ)]
    rw [hdz, map_add (f := _), map_ofNat] at hu
    rw [zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ hu)]

end UpperTheory.V.Z.Sym.Wt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Scalars
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem mRep_scal {K : Type} [Fintype K] {d : ℕ} (n : K → ℕ) (s : K → ℂˣ) (Q : MH d n) :
    mRep d n (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) Q = (∏ k, (s k : ℂ) ^ n k) • Q := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_mRep]
  have hact : act (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) x = fun p => (s p.1 : ℂ) * x p := by
    funext p
    simp [act, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]
  rw [hact, Q.2 (fun k => (s k : ℂ)) x]
  simp

private theorem invT_scal {d : ℕ} (s : ℂˣ) :
    invT ℂ d (Matrix.GeneralLinearGroup.scalar (Fin d) s) = Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ := by
  refine Units.ext ?_
  rw [invT_val, ← map_inv]
  exact Matrix.diagonal_transpose _

theorem UpperTheory.V.Z.Sym.Wt.scalars :
    UpperTheory.V.Z.Sym.Wt.Scalars := by
  intro I _ s
  refine ⟨fun j => ?_, fun n e => ?_⟩
  · have hd : dbl 3 (fun v ↦ Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) =
        fun k => Matrix.GeneralLinearGroup.scalar (Fin 3) (if k.2 then (s k.1)⁻¹ else s k.1) := by
      funext k
      obtain ⟨v, b⟩ := k
      cases b <;> simp [dbl, invT_scal]
    apply LinearMap.ext
    intro P
    funext S
    rw [repG_apply, Module.End.one_apply]
    change mRep 3 (fun k => dg j S k.1) (dbl 3 _) (P S) = P S
    rw [hd, mRep_scal]
    convert one_smul ℂ (P S)
    rw [Fintype.prod_prod_type]
    apply Finset.prod_eq_one
    intro v _
    rw [Fintype.prod_bool]
    simp
  · apply LinearMap.ext
    intro P
    rw [repD_apply, LinearMap.smul_apply, mRep_scal, smul_smul, LinearMap.smul_apply, Module.End.one_apply]
    congr 1
    simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    simp
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have ha : (s v : ℂ) ≠ 0 := (s v).ne_zero
    rw [zpow_add₀ ha, zpow_mul, zpow_natCast, mul_comm]
    norm_cast
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.ThFacts
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem swp_eval {I : Type} [Fintype I] {d : ℕ} (n : I → ℕ) (Q : Bi d n) (x : (I × Bool) × Fin d → ℂ) :
    MvPolynomial.eval x (swp d n Q).1 = MvPolynomial.eval (x ∘ UpperTheory.V.Z.Sym.Wt.flip I d) Q.1 := MvPolynomial.eval_rename _ _ _

theorem UpperTheory.V.Z.Sym.Wt.thFacts :
    UpperTheory.V.Z.Sym.Wt.ThFacts := by
  intro I _ j
  have key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n),
      swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P) := by
    intro n g P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval]
    change MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 =
      MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1
    rw [eval_mRep, eval_mRep, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    obtain ⟨⟨v, b⟩, i⟩ := p
    cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]
  have hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P := by
    intro n P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hsg : ∀ S : I → Bool, sg S * sg S = 1 := by
    intro S
    simp only [sg, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]
  · intro g
    apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]
end

