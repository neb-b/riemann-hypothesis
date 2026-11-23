module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionNum
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDecomp
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem dominant_weight_ext {N : ℕ} (a b : DomWeight N) (hab : a.w = b.w) : a = b := by
  obtain ⟨w, hw⟩ := a
  obtain ⟨w', hw'⟩ := b
  simp only at hab
  subst hab
  rfl

theorem extremal_mem_nablaSq' (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))

theorem degree_sub_det_shift_nonneg {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu) : 0 ≤ degZ lam mu - lam.detShift := by
  subst h
  have hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i) := fun i => (hmu i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (by omega)]
    congr 1
  unfold degZ wsum
  rw [hl, Fin.sum_univ_castSucc]
  linarith

theorem weight_sum_eq_of_last_gap {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith

theorem decomp_of (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvDiv
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

section SlopeTestRemainingChoices

def tvU {r : ℕ} (a b : Fin r) (hab : a ≠ b) (t : ℂ) : GL (Fin r) ℂ where
  val := Formalism.UG.P.wlocal_E a b t
  inv := Formalism.UG.P.wlocal_E a b (-t)
  val_inv := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, add_neg_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]
  inv_val := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, neg_add_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]

lemma wlocal_E_eq_tv {r : ℕ} (a b : Fin r) (t : ℂ) :
    Formalism.UG.P.wlocal_E a b t = Matrix.transvection a b t := by
  ext i j
  simp [Formalism.UG.P.wlocal_E, Matrix.transvection, Matrix.one_apply]
  rw [Matrix.single_apply]
  exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩) rfl rfl

lemma wlocal_E_transpose {r : ℕ} (a b : Fin r) (t : ℂ) :
    (Formalism.UG.P.wlocal_E a b t).transpose = Formalism.UG.P.wlocal_E b a t := by
  ext i j
  simp only [Matrix.transpose_apply, Formalism.UG.P.wlocal_E]
  congr 1
  · exact if_congr eq_comm rfl rfl
  · exact if_congr and_comm rfl rfl

lemma sqAct_tv {r : ℕ} (ν : DomWeight r) (a b : Fin r) (hab : a ≠ b) (t : ℂ) (u : GL (Fin r) ℂ)
    (hu : (u : Matrix (Fin r) (Fin r) ℂ) = Formalism.UG.P.wlocal_E a b t) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    sqAct ℂ r ν u f = Polynomial.eval (C t) (rowGen ℂ a b f) := by
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hu, wlocal_E_eq_tv,
      Matrix.det_transvection_of_ne _ _ hab]
  unfold sqAct detPow
  rw [hdet, one_zpow, Units.val_one, one_smul, hu, wlocal_E_transpose]
  induction f using MvPolynomial.induction_on
  next c => simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen]
  next p q hp hq => simp only [map_add (f := _), Polynomial.eval_add, hp, hq]
  next p v hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    congr 1
    obtain ⟨i, j⟩ := v
    simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X]
    by_cases hi : i = b
    · subst hi
      simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, ite_and]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
    · simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, hi]

lemma embGL_tv {n N : ℕ} (h : n + 1 = N) (a b : Fin n) (hab : a ≠ b) (t : ℂ) :
    ((PI.embGL ℂ n N h (tvU a b hab t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Formalism.UG.P.wlocal_E (eRow h a) (eRow h b) t := by
  subst h
  have he : ∀ x : Fin n, eRow (rfl : n + 1 = n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  have hl : ∀ x : Fin n, (Fin.last n = Fin.castSucc x) ↔ False :=
    fun x => ⟨fun e => (Fin.castSucc_lt_last x).ne' e, False.elim⟩
  ext i j
  simp only [he]
  simp [PI.embGL, PI.blkHom, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, tvU]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Formalism.UG.P.wlocal_E, hl]

end SlopeTestRemainingChoices

private theorem coeff_eq_of_eval_lemma {σ τ : Type*}
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (P : Polynomial (MvPolynomial σ ℂ)) (Q : Polynomial (MvPolynomial τ ℂ))
    (hPQ : ∀ t : ℂ, φ (P.eval (C t)) = Q.eval (C t)) (k : ℕ) :
    φ (P.coeff k) = Q.coeff k := by
  obtain ⟨d, hdP, hdQ⟩ : ∃ d, P.natDegree < d ∧ Q.natDegree < d :=
    ⟨P.natDegree + Q.natDegree + 1, by omega, by omega⟩
  have hP : ∀ t : ℂ, P.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • P.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  have hQ : ∀ t : ℂ, Q.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • Q.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  by_cases hk : k < d
  · refine MvPolynomial.ext _ _ fun m => ?_
    let p : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (AddMonoidAlgebra.coeff (φ (P.coeff i)) m)
    let q : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (AddMonoidAlgebra.coeff (Q.coeff i) m)
    have hpq : p = q := by
      apply Polynomial.funext
      intro t
      have e := congrArg (AddMonoidAlgebra.coeff · m) (hPQ t)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hP t, hQ t, map_sum] at e
      simp only [map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at e
      simp only [p, q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      simpa [mul_comm] using e
    have e2 := congrArg (fun r : Polynomial ℂ => r.coeff k) hpq
    simpa only [p, q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
      Finset.sum_ite_eq', Finset.mem_range, hk, if_true] using e2
  · have h1 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h1, h2, map_zero]

theorem equivariant_divisibility : EqvDiv := by
  intro n N h mu lam φ hφ a b hab k s hs
  unfold IsEqv at hφ
  have hab' : eRow h a ≠ eRow h b := fun he =>
    hab (Fin.ext (by simpa [eRow] using congrArg Fin.val he))
  exact coeff_eq_of_eval_lemma φ (rowGen ℂ a b s) (rowGen ℂ (eRow h a) (eRow h b) (φ s))
    (fun t => by
      have e1 := hφ.2 (tvU a b hab t) s hs
      rwa [sqAct_tv mu a b hab t _ rfl s,
        sqAct_tv lam (eRow h a) (eRow h b) hab' t _ (embGL_tv h a b hab t) (φ s)] at e1) k

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM
section
noncomputable section

namespace PI.WGL.LTM

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def liftRows {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin N :=
  fun p => if hp : p.1 < m then eRow h (ρ ⟨p.1, hp⟩) else ⟨N - 1, by omega⟩

def unl {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (eRow h ∘ ρ) hm

def lif {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (liftRows h ρ) hm

def C0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : MvPolynomial (Fin N × Fin N) ℤ :=
  ∏ i : Fin n, (if i.1 + 1 = n then (lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat
      else 1) *
    (if i.1 = 0 then (initMinor ℤ (n := N) (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat else 1)

def Mlift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) : MvPolynomial (Fin N × Fin N) ℤ :=
  C0 h lam sg * ∏ k : Fin K,
    if k ∈ L then lif h (I k) (by have := hsz k; omega) else unl h (I k) (by have := hsz k; omega)

def GoodL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Prop :=
  (∀ k ∈ L, 0 < sz k) ∧
  ∀ i : Fin n, (Finset.univ.filter fun k => k ∈ L ∧ sz k = i.1).card = if i.1 = 0 then 0 else (bb h lam sg i).toNat

def stdT {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : ∀ k, Fin (sz k) → Fin n :=
  fun k p => ⟨p.1, lt_of_lt_of_le p.2 (hsz k)⟩

def TopPart : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∀ L : Finset (Fin K), GoodL h lam sg sz L →
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ Mlift h lam sg sz hsz L J = ε • xi ℤ h lam sg) ∧
      tupCnt (stdT sz hsz) = sg.natW ∧ bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg ∧
        Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg

end PI.WGL.LTM
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.NablaSqLeOfGen
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem nablaSq_le_of_gen (h4 : PI.GTBranch) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (P : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hP : ∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∀ s ∈ nablaSq ℂ n mu, φ s ∈ P) :
    nablaSq ℂ N lam ≤ P := by
  rw [(h4 n N h lam).2]
  refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro s hs
  exact hP mu hmu φ hφ s hs

theorem comp_gen (hW : EqvRowWt) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (z : ℂ)
    (hz : ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) (ν : Fin N → ℕ) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    Z (weightedHomogeneousComponent (rowW N N) ν (φ s)) =
      weightedHomogeneousComponent (rowW N N) ν (Z (φ s)) := by

  have hterm : ∀ ω : Fin n → ℕ,
      Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) =
        z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s)) := by
    intro ω
    have hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu :=
      dualWeylRowGraded ℂ n n mu.natW ω s hs
    have hhom : IsWeightedHomogeneous (rowW N N)
        (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω) :=
      hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)
    by_cases hν : ν = liftWt h lam mu ω
    · subst hν
      rw [hhom.weightedHomogeneousComponent_same]
      exact hz _ hc
    · rw [hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]
  have hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w := rowW n n) s).toFinset,
      weightedHomogeneousComponent (rowW n n) ω s := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]
    exact finsum_eq_sum _ _
  rw [hz s hs, map_smul]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ω _ => hterm ω

theorem zComm_of (h4 : PI.GTBranch) (hD : EqvDiv) (hW : EqvRowWt) : ZComm := by
  intro n N h lam Z hZ

  have hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam,
      Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f) := by
    intro ν f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν)
        (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        exact comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have hle := nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by
      intro mu hmu φ hφ s hs
      obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
      rw [Submodule.mem_comap, hz s hs]
      exact Submodule.smul_mem _ z (hφ.1 s hs))
    exact hle hf
  · intro a b hab k f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k)
        (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        simp only [LinearMap.comp_apply, rowDivL_apply]
        have hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu := rowDivStable ℂ n n mu.natW a b k s hs
        rw [← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul,
          hD n N h mu lam φ hφ a b hab k s hs])
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    simpa only [LinearMap.comp_apply, rowDivL_apply] using this
  · intro ω f hf hhom
    rw [← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]
    exact weightedHomogeneousComponent_isWeightedHomogeneous ω _

end PI.WGL
end
end

