module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin
section
open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

section Fock

variable {σ R : Type*} [CommRing R]

theorem fockR_eq_sum (f g : MvPolynomial σ R) (T : Finset (σ →₀ ℕ)) (hT : f.support ⊆ T) :
    fockR f g = ∑ m ∈ T, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  unfold fockR
  refine Finset.sum_subset hT fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]

theorem fockR_add_left (f₁ f₂ g : MvPolynomial σ R) : fockR (f₁ + f₂) g = fockR f₁ g + fockR f₂ g := by
  classical
  rw [fockR_eq_sum (f₁ + f₂) g (f₁.support ∪ f₂.support) MvPolynomial.support_add,
    fockR_eq_sum f₁ g _ Finset.subset_union_left, fockR_eq_sum f₂ g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockR_smul_left (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g := by
  rw [fockR_eq_sum (a • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

theorem fockR_add_right (f g₁ g₂ : MvPolynomial σ R) : fockR f (g₁ + g₂) = fockR f g₁ + fockR f g₂ := by
  unfold fockR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockR_smul_right (a : R) (f g : MvPolynomial σ R) : fockR f (a • g) = a * fockR f g := by
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockB (σ R : Type*) [CommRing R] : MvPolynomial σ R →ₗ[R] MvPolynomial σ R →ₗ[R] R :=
  LinearMap.mk₂ R fockR fockR_add_left (fun a f g => by rw [fockR_smul_left, smul_eq_mul])
    fockR_add_right (fun a f g => by rw [fockR_smul_right, smul_eq_mul])

theorem fockB_apply (f g : MvPolynomial σ R) : fockB σ R f g = fockR f g := rfl

theorem fockR_zero_left (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  simp [fockR]

theorem fockR_zero_right (f : MvPolynomial σ R) : fockR f 0 = 0 := by
  simp [fockR]

end Fock

section Words

variable {K : Type} [CommRing K] {n' k : ℕ}

theorem opWord_cons (y : Fin n' × (Fin k × Fin k)) (l : List (Fin n' × (Fin k × Fin k)))
    (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (y :: l) f = X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f) := rfl

theorem opWord_add (l : List (Fin n' × (Fin k × Fin k))) (f g : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (f + g) = opWord l f + opWord l g := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, opWord_cons, ih, map_add (f := _), mul_add]

theorem opWord_smul (l : List (Fin n' × (Fin k × Fin k))) (a : K) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (a • f) = a • opWord l f := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, ih, Derivation.map_smul, mul_smul_comm]

theorem combo_add_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G₁ G₂ : MvPolynomial (Fin n' × Fin k) K) :
    combo f (G₁ + G₂) = combo f G₁ + combo f G₂ := by
  unfold combo
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_add, smul_add]

theorem combo_smul_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (a : K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo f (a • G) = a • combo f G := by
  unfold combo
  rw [Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_smul, smul_comm]

def comboL (f : List (Fin n' × (Fin k × Fin k)) →₀ K) :
    MvPolynomial (Fin n' × Fin k) K →ₗ[K] MvPolynomial (Fin n' × Fin k) K where
  toFun := combo f
  map_add' := combo_add_fun f
  map_smul' a G := combo_smul_fun f a G

theorem combo_add (f₁ f₂ : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (f₁ + f₂) G = combo f₁ G + combo f₂ G := by
  unfold combo
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem combo_smul (a : K) (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (a • f) G = a • combo f G := by
  unfold combo
  rw [Finsupp.sum_smul_index' (h := fun (l : List (Fin n' × (Fin k × Fin k))) (c : K) => c • opWord l G)
    (fun _ => zero_smul _ _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [smul_eq_mul, mul_smul]

theorem combo_zero (G : MvPolynomial (Fin n' × Fin k) K) : combo (0 : List (Fin n' × (Fin k × Fin k)) →₀ K) G = 0 := by
  simp [combo]

end Words

theorem bilin_ext_restrict {K : Type} [CommRing K] {σ : Type*} (T : Set (σ →₀ ℕ))
    (Φ Ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K)
    (h : ∀ μ ∈ T, ∀ ν ∈ T, Φ (monomial μ 1) (monomial ν 1) = Ψ (monomial μ 1) (monomial ν 1)) :
    ∀ G ∈ restrictSupport K T, ∀ H ∈ restrictSupport K T, Φ G H = Ψ G H := by
  have e : ∀ (ρ : σ →₀ ℕ) (c : K), (monomial ρ c : MvPolynomial σ K) = c • monomial ρ 1 := fun ρ c => by
    rw [smul_monomial, smul_eq_mul, mul_one]
  intro G hG H hH
  rw [MvPolynomial.mem_restrictSupport_iff] at hG hH
  rw [G.as_sum, H.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun ν hν => ?_
  rw [e μ, e ν]
  simp only [map_smul, LinearMap.smul_apply]
  rw [h ν (hG hν) μ (hH hμ)]

theorem blockSubstitution_blockInclusion {K : Type} [CommRing K] {n' m : ℕ} (vec : Fin n' → Bool) (t : Fin n')
    (P : MvPolynomial (Fin (m + 1)) K) :
    Th0 K m vec (embS K t P) = blockEmb K t (theta K m (vec t) P) := by
  have hc : (Th0 K m vec).comp (embS K t) = (blockEmb K t).comp (theta K m (vec t)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Th0, embS, theta, blockEmb]
  exact AlgHom.congr_fun hc P

end PI.TOW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.MultidegSingle
section
open MvPolynomial

noncomputable section

namespace PI.TOW.DegW

open PI.TO PI.TOW

variable {K : Type} [Field K] {n' k : ℕ}

theorem multideg_add (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

theorem multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by
  obtain ⟨j₁, j₂⟩ := j
  by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]

theorem step_mem (t : Fin n') (a b : Fin k) (d : Fin n' → ℕ) (G : MvPolynomial (Fin n' × Fin k) K)
    (hG : G ∈ Pol K (ι := Fin n') k d) :
    X (t, a) * pderiv (t, b) G ∈ Pol K (ι := Fin n') k d := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [G.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdm : ∀ i, multideg m i = d i := hG hm
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]
  by_cases hmb : m (t, b) = 0
  · simp [hmb]
  have hle : Finsupp.single (t, b) 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i := by
    intro i
    have h1 := multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i
    rw [← hsplit, hdm i, multideg_single] at h1
    rw [multideg_add, multideg_single]
    simp only at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hexp

theorem stepDeg : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih

end PI.TOW.DegW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.NotMemVarsEmbS
section
open MvPolynomial

noncomputable section

namespace PI.TOW.LiftW

open PI.TO PI.TOW

variable {K : Type} [CommRing K] {n' k : ℕ}

theorem inj (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by
  intro a c h
  exact (Prod.mk.inj h).2

theorem pderiv_embS (t : Fin n') (b : Fin k) (W : MvPolynomial (Fin k) K) :
    pderiv (t, b) (embS K t W) = embS K t (pderiv b W) := by
  simpa [embS] using pderiv_rename (inj (k := k) t) b W

theorem notMem_vars_embS {t a : Fin n'} (h : a ≠ t) (b : Fin k) (W : MvPolynomial (Fin k) K) :
    (t, b) ∉ (embS K a W).vars := by
  intro hm
  have h2 : (t, b) ∈ W.vars.image (fun c : Fin k => (a, c)) :=
    vars_rename (fun c : Fin k => (a, c)) W hm
  rw [Finset.mem_image] at h2
  obtain ⟨c, -, hc⟩ := h2
  exact h (congrArg Prod.fst hc)

theorem pderiv_prod_ne (t : Fin n') (b : Fin k) (T : Finset (Fin n')) (ht : t ∉ T)
    (H : Fin n' → MvPolynomial (Fin k) K) : pderiv (t, b) (∏ s ∈ T, embS K s (H s)) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Derivation.leibniz]
    have hst : s ≠ t := fun e => ht (e ▸ Finset.mem_insert_self s T)
    rw [ih (fun h => ht (Finset.mem_insert_of_mem h)),
      pderiv_eq_zero_of_notMem_vars (notMem_vars_embS hst b (H s))]
    simp

theorem opWord_liftW (t : Fin n') (l : List (Fin k × Fin k)) (F : MvPolynomial (Fin k) K)
    (R : MvPolynomial (Fin n' × Fin k) K) (hR : ∀ b, pderiv (t, b) R = 0) :
    opWord (liftW t l) (embS K t F * R) = embS K t (word1 l F) * R := by
  induction l with
  | nil => simp [opWord, liftW, word1]
  | cons y l ih =>
    have e1 : opWord (liftW t (y :: l)) (embS K t F * R)
        = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R)) := by
      simp [opWord, liftW]
    have e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F) := by
      simp [word1]
    rw [e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]
    simp [embS, map_mul, rename_X]
    ring

theorem opWord_append (l₁ l₂ : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (l₁ ++ l₂) f = opWord l₁ (opWord l₂ f) := by
  simp [opWord, List.foldr_append]

theorem main_list (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by
  classical
  induction ts with
  | nil => simp [opWord]
  | cons t ts ih =>
    rw [List.nodup_cons] at hts
    rw [List.flatMap_cons, opWord_append, ih hts.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase Finset.univ
        (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]
    simp only [if_neg hts.1, List.mem_cons, true_or, if_true]
    rw [opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ t := Finset.ne_of_mem_erase hs
    simp [hne]

theorem stepLift : StepLift := by
  intro K _ n' k w F
  have h := main_list w F (List.finRange n') (List.nodup_finRange n')
  simpa [concatW, List.mem_finRange] using h

end PI.TOW.LiftW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.StepMonoFactor
section
open MvPolynomial

noncomputable section

namespace PI.TOW.MonoW

open PI.TO PI.TOW

theorem stepMonoFactor : StepMonoFactor := by
  intro K _ n' k μ
  simp only [embS, rename_monomial]
  suffices hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by
    rw [← MvPolynomial.monomial_sum_one, ← hμ]
  ext ⟨t, c⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · rw [Finsupp.mapDomain_apply_of_injective (fun a b h => by simpa using h)]
    simp [partS]
  · intro t' _ ht'
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨c', hc'⟩
    exact ht' (congrArg Prod.fst hc')
  · simp

end PI.TOW.MonoW
end
end

