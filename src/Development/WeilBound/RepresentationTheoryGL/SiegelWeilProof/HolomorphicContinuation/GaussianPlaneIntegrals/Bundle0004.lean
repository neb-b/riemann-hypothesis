module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyT
section
noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT

open AsmA

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]


variable (ι A B) in
abbrev NN : ℕ := Fintype.card ι + (Fintype.card A + Fintype.card B)

def emb (i : ι) : Fin (NN ι A B) := Fin.castAdd _ (Fintype.equivFin ι i)

theorem emb_injective : Function.Injective (emb (ι := ι) (A := A) (B := B)) := fun i i' h => by
  simpa [emb] using h


variable (A B) in
def invE (j : Fin (NN ι A B)) : Option ι :=
  if h : (j : ℕ) < Fintype.card ι then some ((Fintype.equivFin ι).symm ⟨j, h⟩) else none

theorem sum_invE (f : Fin (NN ι A B) → ℂ) (g : ι → ℂ) :
    ∑ j, f j * (invE A B j).elim 0 g = ∑ i, f (emb i) * g i := by
  rw [Fin.sum_univ_add]
  have h2 : ∑ j : Fin (Fintype.card A + Fintype.card B), f (Fin.natAdd _ j) * (invE A B (Fin.natAdd _ j)).elim 0 g = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : invE A B (Fin.natAdd (Fintype.card ι) j) = none := by
      simp [invE]
    rw [this]; simp
  rw [h2, add_zero]
  have h1 : ∀ j : Fin (Fintype.card ι), invE A B (Fin.castAdd _ j) = some ((Fintype.equivFin ι).symm j) := by
    intro j
    simp [invE]
  simp_rw [h1]
  simp only [Option.elim]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => f (emb i) * g i)).symm.trans
    (Finset.sum_congr rfl fun j _ => by simp [emb]) |>.symm


variable (ι) in
def resφ : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) → PV ι A B :=
  Sum.elim (fun x => (invE A B x.1).elim 0 fun i => X (Sum.inl (i, x.2)))
    (fun y => (invE A B y.1).elim 0 fun i => X (Sum.inr (i, y.2)))

def res : PV (Fin (NN ι A B)) A B →ₐ[ℂ] PV ι A B := aeval (resφ ι)

def ren : (ι × A) ⊕ (ι × B) → (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) :=
  Sum.map (Prod.map emb id) (Prod.map emb id)

def blk (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) : Matrix ι ι ℂ := fun i i' => u (emb i) (emb i')

theorem eval_resφ (z : (ι × A) ⊕ (ι × B) → ℂ) (v : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B)) :
    eval z (resφ ι v) = Sum.elim (fun x : Fin (NN ι A B) × A => (invE A B x.1).elim 0 fun i => z (Sum.inl (i, x.2)))
      (fun y : Fin (NN ι A B) × B => (invE A B y.1).elim 0 fun i => z (Sum.inr (i, y.2))) v := by
  rcases v with ⟨j, a⟩ | ⟨j, b⟩ <;> cases h : invE A B j <;> simp [resφ, h]

theorem act_ren (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    (act u (u.map star) (fun v => eval z (resφ ι v))) ∘ ren = act (blk u) ((blk u).map star) z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [Function.comp, ren, Sum.map_inl, Prod.map, act, Sum.elim_inl, id, eval_resφ]
    exact sum_invE (fun j => u (emb i) j) (fun i' => z (Sum.inl (i', a)))
  · simp only [Function.comp, ren, Sum.map_inr, Prod.map, act, Sum.elim_inr, id, eval_resφ, Matrix.map_apply]
    exact sum_invE (fun j => star (u (emb i) j)) (fun i' => z (Sum.inr (i', b)))

def Tf (hA : Avg) (q : PV ι A B) : PV ι A B := res (Classical.choose (hA (NN ι A B) A B (rename ren q)))

theorem continuous_toMK (N : ℕ) :
    Continuous fun k : Formalism.REAL.KG (fun _ : Fin N => true) => Formalism.REAL.toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_blk : Continuous fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
    blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k) :=
  continuous_pi fun i => continuous_pi fun i' => (continuous_toMK _).matrix_elem _ _

theorem eval_Tf (hA : Avg) (q : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true),
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q
        ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  rw [Tf, res, eval_aeval', hs.2.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [AsmA.eval_sub, eval_rename, act_ren]

theorem Tf_mem (hS : Stable) (hA : Avg) (q : PV ι A B) : Tf hA q ∈ pairAlg ι A B := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  have hP := hS (Fin (NN ι A B)) A B (by simp only [Fintype.card_fin, NN]; omega) (by simp only [Fintype.card_fin, NN]; omega) _ hs.1
  have hle : Subalgebra.map (res (ι := ι) (A := A) (B := B)) (pairAlg (Fin (NN ι A B)) A B) ≤ pairAlg ι A B := by
    rw [pairAlg, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨(a, b), ?_⟩
    apply MvPolynomial.funext
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [res, map_sum, map_mul, aeval_X, eval_resφ, Sum.elim_inl, Sum.elim_inr]
    rw [sum_invE (fun j => (invE A B j).elim 0 fun i => z (Sum.inl (i, a))) (fun i => z (Sum.inr (i, b)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : invE A B (emb (A := A) (B := B) i) = some i := by simp [invE, emb]
    simp [this]
  exact hle ⟨_, hP, rfl⟩

theorem Tf_deg (hA : Avg) (q : PV ι A B) : (Tf hA q).totalDegree ≤ q.totalDegree := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  refine (totalDegree_aeval_le _ (fun v => ?_) _).trans (hs.2.1.trans (totalDegree_rename_le _ _))
  rcases v with ⟨j, a⟩ | ⟨j, b⟩
  · simp only [resφ, Sum.elim_inl]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]
  · simp only [resφ, Sum.elim_inr]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]

theorem integrable_eval_act (hA : Avg) (F G : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) → Matrix ι ι ℂ)
    (hF : Continuous F) (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k => eval (act (F k) (G k) z) q) (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrableOn_univ.mp ((continuous_act_eval hF hG z q).continuousOn.integrableOn_compact isCompact_univ)

end PositivityTheory.Rg.Sw.FFTSteps.AsmT
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFTC
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

def eqv : Fin m × Fin n × Bool ≃ VV (Rw ε false) n ⊕ VV (Rw ε true) n where
  toFun k := if h : ε k.1 = true then Sum.inr (if k.2.2 then Sum.inr (⟨k.1, h⟩, k.2.1) else Sum.inl (⟨k.1, h⟩, k.2.1))
    else Sum.inl (if k.2.2 then Sum.inr (⟨k.1, by simpa using h⟩, k.2.1) else Sum.inl (⟨k.1, by simpa using h⟩, k.2.1))
  invFun := Sum.elim (jv ε false) (jv ε true)
  left_inv k := by
    obtain ⟨a, i, t⟩ := k
    by_cases h : ε a = true <;> cases t <;> simp [h, jv]
  right_inv x := by
    rcases x with (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) | (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) <;> simp [jv, ha]

def Th : PX m n ≃ₐ[ℂ] MvPolynomial (VV (Rw ε false) n) (PV (Rw ε true) (Fin n) (Fin n)) :=
  (renameEquiv ℂ (eqv ε)).trans (sumAlgEquiv ℂ _ _)

variable {ε}

theorem th_X (k : Fin m × Fin n × Bool) : Th ε (X k) = sumAlgEquiv ℂ _ _ (X (eqv ε k)) := by
  simp [Th]

theorem th_embT (c : PV (Rw ε true) (Fin n) (Fin n)) : Th ε (emb ε true c) = C c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε true v) = Sum.inr v := (eqv ε).apply_symm_apply (Sum.inr v)
    have hx : Th ε (emb ε true (X v)) = C (X v) := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inr ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, C_mul]

theorem th_embF (t : PV (Rw ε false) (Fin n) (Fin n)) :
    Th ε (emb ε false t) = map (algebraMap ℂ (PV (Rw ε true) (Fin n) (Fin n))) t := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε false v) = Sum.inl v := (eqv ε).apply_symm_apply (Sum.inl v)
    have hx : Th ε (emb ε false (X v)) = X v := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inl ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, map_mul, map_X]

theorem th_prod (c : PV (Rw ε true) (Fin n) (Fin n)) (μ : VV (Rw ε false) n →₀ ℕ) :
    Th ε (emb ε true c * emb ε false (monomial μ 1)) = monomial μ c := by
  rw [map_mul, th_embT, th_embF, map_monomial, map_one, C_mul_monomial, mul_one]

theorem decomp (Q : PX m n) :
    Q = ∑ μ ∈ (Th ε Q).support, emb ε true ((Th ε Q).coeff μ) * emb ε false (monomial μ 1) := by
  apply (Th ε).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [th_prod]
  exact (Th ε Q).as_sum

theorem coeff_sum_monomial {σ R : Type*} [CommSemiring R] [DecidableEq σ] (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → R) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (∑ ν ∈ S, monomial ν (f ν)) μ = if μ ∈ S then f μ else 0 := by
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h'
      exact absurd h h'
  · apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ μ := fun e => h (e ▸ hb)
    simp [this]

theorem indep {J : Type} [Fintype J] (b : J → PV (Rw ε true) (Fin n) (Fin n)) (hb : LinearIndependent ℂ b)
    (t : J → PV (Rw ε false) (Fin n) (Fin n)) (h : ∑ j, emb ε true (b j) * emb ε false (t j) = 0) : ∀ j, t j = 0 := by
  have h2 := congrArg (Th ε) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h2
  simp_rw [map_mul, th_embT, th_embF] at h2
  intro j
  ext μ
  have h3 := congrArg (AddMonoidAlgebra.coeff · μ) h2
  rw [coeff_sum] at h3
  change _ = 0 at h3
  simp_rw [coeff_C_mul, coeff_map] at h3
  have h4 : ∑ i, (AddMonoidAlgebra.coeff (t i) μ) • b i = 0 := by
    rw [← h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  have := Fintype.linearIndependent_iff.1 hb _ h4 j
  change AddMonoidAlgebra.coeff (t j) μ = 0
  exact this

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralMonSelf
section
noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem gw_prod (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]

def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s

theorem mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]

theorem integrable_mon (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this

theorem integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)

theorem integral_mon_ne (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)

theorem integral_mon_self (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _

def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)

def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s

theorem Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]

theorem gip_diag (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [MeasureTheory.integral_finsetSum _ fun m _ => MeasureTheory.integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

