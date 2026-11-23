module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def Aop (K : P → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ q, K q (I q) (J q)) • LinearMap.proj J

def mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ j, A (I p) j • LinearMap.proj (Function.update I p j)

theorem Aop_apply (K : P → Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    Aop K f I = ∑ J, (∏ q, K q (I q) (J q)) • f J := by
  simp only [Aop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem mAt_apply (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    mAt p A f I = ∑ j, A (I p) j • f (Function.update I p j) := by
  simp only [mAt, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem actT_eq {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) : actT lab κ ρ γ = lift (ρ γ) * Aop (fun q => κ (lab q) γ) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [actT_apply, Module.End.mul_apply, lift_apply, Aop_apply, map_sum]
  simp only [map_smul]

theorem lift_comm_Aop (B : Module.End ℂ M) (K : P → Matrix (Fin n) (Fin n) ℂ) : Commute (lift B) (Aop K) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, lift_apply, Aop_apply, map_sum, map_smul]

theorem lift_comm_mAt (B : Module.End ℂ M) (p : P) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute (lift B) (mAt p A : Module.End ℂ (TV n M P)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, lift_apply, mAt_apply, map_sum, map_smul]

theorem prod_one_apply (I J : P → Fin n) :
    ∏ q, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)

theorem Aop_one : (Aop (fun _ : P => (1 : Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ (TV n M P)) = 1 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Aop_apply, prod_one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Module.End.one_apply]

theorem Aop_mul (K L : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop (fun q => K q * L q) : Module.End ℂ (TV n M P)) = Aop K * Aop L := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem eAt_eq (p : P) (a b : Fin n) :
    (eAt p a b : Module.End ℂ (TV n M P)) = mAt p (Matrix.single a b 1) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [eAt_apply, mAt_apply]
  simp only [Matrix.single_apply]
  rcases eq_or_ne (I p) a with h | h
  · simp [h]
  · simp [h, Ne.symm h]

def mAtL (p : P) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (TV n M P) where
  toFun := mAt p
  map_add' A B := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, mAt_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, mAt_apply, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem prod_split (p : P) (g : P → ℂ) : ∏ q, g q = g p * ∏ q ∈ Finset.univ.erase p, g q :=
  (Finset.mul_prod_erase _ g (Finset.mem_univ p)).symm

theorem mAt_mul_Aop (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (mAt p A * Aop K : Module.End ℂ (TV n M P)) = Aop (Function.update K p (A * K p)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, mAt_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [prod_split p (fun q => Function.update K p (A * K p) q (I q) (J q))]
  simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_split p (fun q => K q (Function.update I p j q) (J q))]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun q hq => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]

theorem Aop_mul_mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop K * mAt p A : Module.End ℂ (TV n M P)) = Aop (Function.update K p (K p * A)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [mAt_apply, Finset.smul_sum, smul_smul]
  let φ : (P → Fin n) × Fin n → (P → Fin n) × Fin n := fun x => (Function.update x.1 p x.2, x.1 p)
  have hφ : Function.Involutive φ := fun x => by
    simp only [φ, Function.update_idem, Function.update_self, Function.update_eq_self]
  let H : (P → Fin n) × Fin n → M := fun x =>
    ((∏ q, K q (I q) (Function.update x.1 p x.2 q)) * A x.2 (x.1 p)) • f x.1
  calc ∑ J : P → Fin n, ∑ j, ((∏ q, K q (I q) (J q)) * A (J p) j) • f (Function.update J p j)
      = ∑ x : (P → Fin n) × Fin n, H (φ x) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [H, φ, Function.update_idem, Function.update_self, Function.update_eq_self]
    _ = ∑ x : (P → Fin n) × Fin n, H x := Equiv.sum_comp (hφ.toPerm φ) H
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [H]
        rw [← Finset.sum_smul]
        congr 1
        rw [prod_split p (fun q => Function.update K p (K p * A) q (I q) (J q))]
        simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [prod_split p (fun q => K q (I q) (Function.update J p i q))]
        simp only [Function.update_self]
        have hr : ∏ q ∈ Finset.univ.erase p, K q (I q) (Function.update J p i q) =
            ∏ q ∈ Finset.univ.erase p, Function.update K p (K p * A) q (I q) (J q) :=
          Finset.prod_congr rfl fun q hq => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        rw [hr]
        ring

theorem pm_Aop (σ : Equiv.Perm P) (K : P → Matrix (Fin n) (Fin n) ℂ) (hK : ∀ q, K (σ q) = K q) :
    (pm σ * Aop K : Module.End ℂ (TV n M P)) = Aop K * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, pm_apply, Aop_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin n)) : (P → Fin n) ≃ (P → Fin n)) _ _ fun J => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_def, id, Equiv.symm_apply_apply]
  congr 1
  conv_rhs => rw [← Equiv.prod_comp σ]
  simp [hK]

theorem eAt_comm (p q : P) (h : p ≠ q) (a b c d : Fin n) :
    Commute (eAt p a b : Module.End ℂ (TV n M P)) (eAt q c d) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne h.symm,
    Function.update_comm h b d I]
  split_ifs <;> rfl

theorem tE_comm {ι : Type} [DecidableEq ι] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (hcomm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) (lab : P → ι) (τ τ' : ι) (h : τ ≠ τ')
    (a b c d : Fin n) : Commute (tE (fib lab τ) (E τ) a b) (tE (fib lab τ') (E τ') c d) := by
  unfold tE
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
  · exact (hcomm τ τ' h a b c d).map (liftA n M P)
  · exact Commute.sum_right _ _ _ fun p _ => lift_comm_eAt _ _ _ _
  · exact Commute.sum_left _ _ _ fun p _ => (lift_comm_eAt _ _ _ _).symm
  · refine Commute.sum_left _ _ _ fun p hp => Commute.sum_right _ _ _ fun q hq => eAt_comm p q ?_ _ _ _ _
    rintro rfl
    simp only [fib, Finset.mem_filter] at hp hq
    exact h (hp.2.symm.trans hq.2)

theorem actT_one {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ, κ τ 1 = 1) (hρ : ρ 1 = 1) : actT lab κ ρ 1 = 1 := by
  rw [actT_eq]
  simp only [hκ, hρ, Aop_one, mul_one]
  rfl

theorem actT_mul {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ) (hρ : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ)
    (γ δ : Γ) : actT lab κ ρ (γ * δ) = actT lab κ ρ γ * actT lab κ ρ δ := by
  simp only [actT_eq, hκ, hρ, Aop_mul, lift_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (lift_comm_Aop _ _).eq, mul_assoc]

theorem conj_single (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ∑ c, ∑ d, (U c a * star (U d b)) • Matrix.single c d (1 : ℂ) = U * Matrix.single a b 1 * Uᴴ := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem tE_sum (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (k : Fin n → Fin n → ℂ) :
    ∑ c, ∑ d, k c d • tE S E c d =
      lift (∑ c, ∑ d, k c d • E c d) + ∑ p ∈ S, mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) := by
  simp only [tE, smul_add, Finset.sum_add_distrib, Finset.smul_sum, eAt_eq]
  congr 1
  · refine LinearMap.ext fun f => funext fun I => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply]
  · have : ∀ p, (mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) : Module.End ℂ (TV n M P)) =
        ∑ c, ∑ d, k c d • mAt p (Matrix.single c d 1) := fun p => by
      rw [show (mAt p : _ → Module.End ℂ (TV n M P)) = mAtL p from rfl]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simp only [this]
    conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
    rw [Finset.sum_comm]

theorem actT_ad {ι Γ : Type} [DecidableEq ι] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hu : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ)
    (γ : Γ) (τ : ι) (a b : Fin n) :
    actT lab κ ρ γ * tE (fib lab τ) (E τ) a b =
      (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • tE (fib lab τ) (E τ) c d) * actT lab κ ρ γ := by
  rw [actT_eq, tE_sum]
  unfold tE
  simp only [eAt_eq]
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [mul_assoc, ← (lift_comm_Aop _ _).eq, ← mul_assoc, ← lift_mul, had, lift_mul, mul_assoc]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [fib, Finset.mem_filter] at hp
    rw [mul_assoc, Aop_mul_mAt, ← mul_assoc (mAt _ _), ← (lift_comm_mAt _ _ _).eq, mul_assoc, mAt_mul_Aop]
    congr 2
    simp only [hp.2]
    rw [conj_single (κ τ γ) a b, mul_assoc, mul_eq_one_comm.mp (hu τ γ), mul_one]

theorem pm_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (σ : Equiv.Perm P) (hσ : ∀ p, lab (σ p) = lab p) (γ : Γ) : Commute (pm σ) (actT lab κ ρ γ) := by
  rw [actT_eq]
  refine Commute.mul_right (lift_comm_pm _ _).symm ?_
  exact pm_Aop σ _ fun q => by simp only [hσ]

end PositivityTheory.Rg.Cz.TGK

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKC
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def cLam (lam : TV n M P →ₗ[ℂ] ℂ) (I : P → Fin n) : M →ₗ[ℂ] ℂ :=
  lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I

theorem cLam_sum (lam : TV n M P →ₗ[ℂ] ℂ) (v : TV n M P) : lam v = ∑ I, cLam lam I (v I) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

omit [DecidableEq P] in
theorem cprod_one (I J : P → Fin n) :
    ∏ p, (1 : Matrix (Fin n) (Fin n) ℂ) (I p) (J p) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (Matrix.one_apply_ne hp)

theorem cprod_erase (I J : P → Fin n) (p : P) (x : ℂ) :
    (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * x =
      ∑ b, if J = Function.update I p b then x else 0 := by
  by_cases h : ∀ q, q ≠ p → I q = J q
  · rw [Finset.prod_eq_one, one_mul, Finset.sum_eq_single (J p)]
    · rw [if_pos]; funext q; by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, h q hq]
    · intro b _ hb; rw [if_neg]; intro hJ; apply hb; rw [hJ]; simp
    · simp
    · intro q hq; rw [h q (Finset.ne_of_mem_erase hq)]; simp
  · push Not at h
    obtain ⟨q, hqp, hq⟩ := h
    have h0 : ∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩) (Matrix.one_apply_ne hq)
    rw [h0, zero_mul]
    refine (Finset.sum_eq_zero fun b _ => if_neg ?_).symm
    intro hJ; apply hq; rw [hJ, Function.update_of_ne hqp]

theorem csum_erase (I : P → Fin n) (p : P) (φ : (P → Fin n) → ℂ) :
    ∑ J, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * φ J =
      ∑ b, φ (Function.update I p b) := by
  simp_rw [cprod_erase]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

omit [Fintype P] [DecidableEq P] in
theorem ckey (I : P → Fin n) (S : Finset P) (F : Fin n → Fin n → ℂ) (h : Fin n → P → ℂ) :
    ∑ a, ∑ b, F a b * ∑ p ∈ S, (if I p = a then h b p else 0) = ∑ p ∈ S, ∑ b, F (I p) b * h b p := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

def cD {ι : Type} [DecidableEq ι] (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) (σ : ι) (i j : Fin n) : ℂ :=
  (if σ = τ then X i j else 0) + (if σ = bar τ then star (X i j) else 0)

theorem cderiv_entry {ι Γ : Type} [DecidableEq ι] (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (bar : ι → ι) (τ : ι)
    (hne : bar τ ≠ τ) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) (σ : ι) (i j : Fin n) :
    HasDerivAt (fun t => κ σ (c t) i j) (cD bar τ X σ i j) 0 := by
  unfold cD
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    exact hd i j
  · by_cases h2 : σ = bar τ
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]
      simp_rw [hconj τ]
      exact (hd i j).star
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [show (fun t => κ σ (c t) i j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j from
        funext fun t => by rw [hoth σ h1 h2 t]]
      exact hasDerivAt_const _ _

omit [DecidableEq P] in
theorem cpart {ι : Type} [DecidableEq ι] (lab : P → ι) (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ)
    (I : P → Fin n) (h : Fin n → P → ℂ) :
    ∑ p, ∑ b, cD bar τ X (lab p) (I p) b * h b p =
      ∑ p ∈ fib lab τ, ∑ b, X (I p) b * h b p + ∑ p ∈ fib lab (bar τ), ∑ b, star (X (I p) b) * h b p := by
  unfold fib
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold cD
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]

theorem actT_der {ι Γ : Type} [DecidableEq ι] [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) (bar : ι → ι) (τ : ι) (hne : bar τ ≠ τ)
    (hρ1 : ρ 1 = 1) (hκ1 : ∀ σ, κ σ 1 = 1) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ) (hc0 : c 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1)
    (hρ : ∀ y (lam : M →ₗ[ℂ] ℂ), HasDerivAt (fun t => lam (ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)) y)) 0)
    (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => lam (actT lab κ ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • tE (fib lab τ) (E τ) a b + star (X a b) • tE (fib lab (bar τ)) (E (bar τ)) a b)) y))
      0 := by
  have hf : (fun t => lam (actT lab κ ρ (c t) y)) = fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J)) := by
    funext t
    rw [cLam_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [actT_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hf]
  have hg : ∀ I J : P → Fin n, HasDerivAt (fun t => ∏ p, κ (lab p) (c t) (I p) (J p))
      (∑ p, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) •
        cD bar τ X (lab p) (I p) (J p)) 0 := by
    intro I J
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun p t => κ (lab p) (c t) (I p) (J p)) (x := 0)
      (fun p _ => cderiv_entry κ bar τ hne hconj X c hd hoth (lab p) (I p) (J p))
    simp only [hc0, hκ1] at this
    exact this
  have hall : HasDerivAt (fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J))) _ 0 :=
    HasDerivAt.fun_sum fun I _ => HasDerivAt.fun_sum fun J _ => (hg I J).fun_mul (hρ (y J) (cLam lam I))
  refine hall.congr_deriv ?_
  simp only [hc0, hκ1, hρ1, Module.End.one_apply]
  rw [cLam_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_add_distrib]
  simp_rw [cprod_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [csum_erase, Function.update_self]
  rw [cpart lab bar τ X I (fun b p => cLam lam I (y (Function.update I p b)))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, tE_apply, map_sum, map_add, map_smul, smul_eq_mul, apply_ite (cLam lam I), map_zero,
    mul_add, Finset.sum_add_distrib]
  rw [ckey I (fib lab τ) (fun a b => X a b) (fun b p => cLam lam I (y (Function.update I p b))),
    ckey I (fib lab (bar τ)) (fun a b => star (X a b)) (fun b p => cLam lam I (y (Function.update I p b)))]
  ring

end PositivityTheory.Rg.Cz.TGK

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinCK
section
noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

theorem pow_mem' {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih => intro z hz; rw [pow_succ', Module.End.mul_apply]; exact hZ _ (ih z hz)

theorem restrict_pow_coe {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ (k : ℕ) (w : Z), (((T.restrict hZ) ^ k) w : U) = (T ^ k) (w : U) := by
  intro k
  induction k with
  | zero => intro w; simp
  | succ k ih => intro w; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, ← Module.End.mul_apply, ← pow_succ']

theorem fit_step {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (e : U →ₗ[ℂ] ℂ)
    (Z : Submodule ℂ U) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) (he : ∀ z ∈ Z, e (T z) = 0)
    (z0 : U) (hz0 : z0 ∈ Z) (hez : e z0 ≠ 0) : ∃ N : ℕ, ∃ a ∈ Z, (T ^ N) a = 0 ∧ e a ≠ 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow (T.restrict hZ))
  have hc := hN (N + 1) (by omega)
  have hmem : (⟨z0, hz0⟩ : Z) ∈ LinearMap.ker ((T.restrict hZ) ^ (N + 1)) ⊔
      LinearMap.range ((T.restrict hZ) ^ (N + 1)) := by
    rw [hc.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨w, rfl⟩ := hb
  refine ⟨N + 1, a, a.2, ?_, ?_⟩
  · rw [← restrict_pow_coe T Z hZ, LinearMap.mem_ker.1 ha]; rfl
  · have h1 : (z0 : U) = (a : U) + (T ^ (N + 1)) (w : U) := by
      rw [← restrict_pow_coe T Z hZ, ← Submodule.coe_add, hab]
    have h2 : e ((T ^ (N + 1)) (w : U)) = 0 := by
      rw [pow_succ', Module.End.mul_apply]
      exact he _ (pow_mem' T Z hZ N _ w.2)
    intro h0
    apply hez
    rw [h1, map_add (f := _), h0, h2, add_zero]

theorem common_ker {U : Type*} [AddCommGroup U] [Module ℂ U] (T : ℕ → Module.End ℂ U)
    (hT : ∀ i j, Commute (T i) (T j)) (e : U →ₗ[ℂ] ℂ) (s : Finset ℕ) :
    ∀ Z : Submodule ℂ U, FiniteDimensional ℂ Z → (∀ i ∈ s, ∀ z ∈ Z, T i z ∈ Z) →
      (∀ i ∈ s, ∀ z ∈ Z, e (T i z) = 0) → (∃ z ∈ Z, e z ≠ 0) → ∃ z ∈ Z, z ≠ 0 ∧ ∀ i ∈ s, T i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro Z - - - ⟨z, hz, hez⟩
    exact ⟨z, hz, fun h => hez (by rw [h, map_zero]), by simp⟩
  | @insert i0 s hi0 ih =>
    rintro Z hfd hZ he ⟨z0, hz0, hez⟩
    have hZ0 := hZ i0 (Finset.mem_insert_self _ _)
    obtain ⟨N, a, haZ, haN, hea⟩ :=
      fit_step (T i0) e Z hZ0 (he i0 (Finset.mem_insert_self _ _)) z0 hz0 hez
    have hfd' : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker (T i0 ^ N)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨z1, hz1, hz1ne, hz1s⟩ := ih (Z ⊓ LinearMap.ker (T i0 ^ N)) hfd'
      (fun i hi z hz => by
        refine ⟨hZ i (Finset.mem_insert_of_mem hi) z hz.1, ?_⟩
        have hk : (T i0 ^ N) z = 0 := hz.2
        show (T i0 ^ N) (T i z) = 0
        rw [← Module.End.mul_apply, ((hT i i0).pow_right N).eq.symm,
          Module.End.mul_apply, hk, map_zero])
      (fun i hi z hz => he i (Finset.mem_insert_of_mem hi) z hz.1) ⟨a, ⟨haZ, haN⟩, hea⟩
    have hex : ∃ k, (T i0 ^ k) z1 = 0 := ⟨N, hz1.2⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero, Module.End.one_apply] at this
      exact hz1ne this
    refine ⟨(T i0 ^ (Nat.find hex - 1)) z1, pow_mem' _ _ hZ0 _ _ hz1.1, Nat.find_min hex (by omega), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    · rw [← Module.End.mul_apply, ((hT i i0).pow_right _).eq, Module.End.mul_apply, hz1s i hi, map_zero]

end TF

end PositivityTheory.Rg.Cz
end
end

