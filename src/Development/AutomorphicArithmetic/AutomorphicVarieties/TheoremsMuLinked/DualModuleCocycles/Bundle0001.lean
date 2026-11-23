module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ChQuot
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.chQuot :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), ∃ (E' : Type) (_ : Ring E') (_ : Algebra A E') (π : E →ₐ[A] E') (D' : Det n A E'), Function.Surjective π ∧ D'.pull π = D ∧ D'.IsCH ∧ ∀ y, π y = 0 → y ∈ D.ker := by
  intro n A E _ _ _ D
  let π : E →ₐ[A] D.CH.ringCon.Quotient := RingCon.mkₐ A D.CH.ringCon
  have hmem : ∀ x, π x = 0 ↔ x ∈ D.CH := fun x => by
    rw [← map_zero π]
    exact (RingCon.eq _)
  have hsurj : Function.Surjective π := fun q => Quotient.exists_rep q
  have hk : ∀ y, π y = 0 → y ∈ D.ker := fun y hy => UpperTheory.V.CA.d_ch_ker D ((hmem y).1 hy)
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D π hsurj hk
  refine ⟨_, _, _, π, D', hsurj, hD', ?_, hk⟩
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := ((UpperTheory.V.CA.d_pull D' π).2.2.2 hsurj).2 y hy
  rw [hD'] at hx
  rw [TwoSidedIdeal.mem_bot, hmem]
  exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DerPow
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem x_loc {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (x : R →ₐ[O] O) (y : R) (hy : y ∈ maximalIdeal R) : x y ∈ maximalIdeal O := by
  intro hu
  have h2 : IsUnit (y - algebraMap O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem der_pow {O R X : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [AddCommGroup X] [Module O X] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (h : IsDer x δ) (k : ℕ) :
    ∀ a ∈ maximalIdeal R ^ (k + 1), x a ∈ maximalIdeal O ^ (k + 1) ∧
      δ a ∈ (maximalIdeal O ^ k • ⊤ : Submodule O X) := by
  induction k with
  | zero =>
    intro a ha
    rw [zero_add, pow_one] at ha
    refine ⟨by simpa using x_loc x a ha, by simp⟩
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
    · obtain ⟨h1, h2⟩ := ih b hb
      have h3 := x_loc x c hc
      refine ⟨?_, ?_⟩
      · rw [map_mul, pow_succ _ (k + 1)]
        exact Ideal.mul_mem_mul h1 h3
      · rw [h b c]
        refine Submodule.add_mem _ (Submodule.smul_mem_smul h1 Submodule.mem_top) ?_
        rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul h3 h2
    · rw [map_add (f := _), map_add (f := _)]
      exact ⟨Ideal.add_mem _ hb.1 hc.1, Submodule.add_mem _ hb.2 hc.2⟩

theorem UpperTheory.V.Th.Coc.lcDer :
    ∀ {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] (m : ℕ), (∀ f : Γ → O, AdicCont (maximalIdeal O) f → IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ m) (f g)) ∧ ∀ (x : R →ₐ[O] O) (δ : R →ₗ[O] Om O m), IsDer x δ → ∀ f : Γ → R, AdicCont (maximalIdeal R) f → IsLocallyConstant fun g => δ (f g) := by
  intro O R Γ _ _ _ _ _ _ m
  refine ⟨fun f hf => hf m, fun x δ h f hf => ?_⟩
  have hk : ∀ a ∈ maximalIdeal R ^ (m + 1), δ a = 0 := fun a ha => by
    refine Submodule.smul_induction_on (p := fun z => z = 0) (der_pow x δ h m a ha).2 (fun r hr z _ => ?_)
      (fun u v hu hv => by rw [hu, hv, add_zero])
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  have h1 := hf (m + 1)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  intro g
  filter_upwards [h1 g] with g' hg
  rw [← sub_eq_zero, ← map_sub]
  exact hk _ (Ideal.Quotient.eq.1 hg)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMSmulOne
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {n : ℕ}

end SlopeTestRemainingChoices

private theorem dualM_mul_dualM {X : Type} [CommRing X] {n : ℕ} (A B A' B' : Matrix (Fin n) (Fin n) X) :
    dualM A B * dualM A' B' = dualM (A * A') (A * B' + B * A') := by
  ext i j
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem UpperTheory.V.Th.Coc.rel :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G H : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X) (φ : H → G) (ψ : Fin n → H → R) (g : Fin n → H), IsLift x δ (repR x ρ) τ c d → repR x ρ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → d (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → (List.ofFn fun i => dualM (bar X (ρ (φ (g i)))) (d (MonoidAlgebra.single (φ (g i)) 1)) - (TrivSqZeroExt.inl (algebraMap O X (x (ψ i (g i)))) + TrivSqZeroExt.inr (c • δ (ψ i (g i))) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0 := by
  intro O R X _ _ _ _ _ n G H _ x δ ρ τ c d φ ψ g hL h1 h2
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hd1 : d 1 = 0 := by
    have := hL.mul 1 1
    simp only [mul_one, map_one, hbar1, one_mul] at this
    have h' : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h'
  have hrep : ∀ (k : G) (r : R), repR x ρ (MonoidAlgebra.single k r) = x r • ρ k := by
    intro k r
    simp [repR, GDet.repAlg]
  have hs : ∀ r : R, MonoidAlgebra.single (1 : G) r = r • (1 : MonoidAlgebra R G) := by
    intro r
    simp [MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  let Φ : MonoidAlgebra R G →* Matrix (Fin n) (Fin n) (DualNumber X) :=
    { toFun := fun a => dualM (bar X (repR x ρ a)) (d a)
      map_one' := by
        ext i j
        · by_cases hij : i = j <;> simp [dualM, hbar1, Matrix.one_apply, hij]
        · by_cases hij : i = j <;> simp [dualM, hd1, Matrix.one_apply, hij]
      map_mul' := by
        intro a b
        rw [dualM_mul_dualM, hL.mul, map_mul]
        simp [bar, Matrix.map_mul, add_comm] }
  have key := map_list_prod Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i)))
  have hz : Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 := by
    show dualM _ _ = 0
    rw [h1, h2]
    ext i j <;> simp [dualM, bar]
  rw [hz, List.map_ofFn] at key
  rw [key]
  congr 2
  funext i
  show _ = dualM (bar X (repR x ρ (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))) (d (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))
  rw [map_sub, map_sub, hrep, hrep, hs (ψ i (g i)), hL.smul, hd1, map_one, map_one, map_one, one_smul, hbar1]
  ext a b
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagAEntry
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem UpperTheory.V.Th.Coc.flagA_full {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) {n : ℕ} (p : Fin n → P) :
    (List.ofFn fun j => φ (p j)).prod = φ (∏ j, p j) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

private theorem UpperTheory.V.Th.Coc.flagA_split {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) :
    ∀ {n : ℕ} (p : Fin n → P) (F : Fin n → M) (i : Fin n), (∀ j, j ≠ i → F j = φ (p j)) →
      (List.ofFn F).prod = φ (∏ j, if j < i then p j else 1) * F i * φ (∏ j, if i < j then p j else 1) := by
  intro n
  induction n with
  | zero => intro p F i; exact i.elim0
  | succ n ih =>
    intro p F i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      have h1 : (fun j : Fin n => F j.succ) = fun j => φ (p j.succ) := funext fun j => h _ (Fin.succ_ne_zero j)
      rw [List.ofFn_succ, List.prod_cons, h1, flagA_full φ fun j : Fin n => p j.succ]
      simp [Fin.prod_univ_succ]
    · intro h
      rw [List.ofFn_succ, List.prod_cons,
        ih (fun j => p j.succ) (fun j => F j.succ) k (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e))),
        h 0 (Fin.succ_ne_zero k).symm]
      simp [Fin.prod_univ_succ, mul_assoc]

private theorem UpperTheory.V.Th.Coc.flagA_entry {A : Type} [CommRing A] {n : ℕ} (u Z : Matrix (Fin n) (Fin n) A) (α : Fin n → A)
    (a b : Fin n) : (kS u α * Z * kT u α) a b = (kEl u α a * Z * kEl u α b) a b := by
  simp [kS, kT, Matrix.mul_apply]

theorem UpperTheory.V.Th.Coc.flagA :
    ∀ {A H : Type} [CommRing A] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) A) (ψ : Fin n → H → A) (s : H), (∀ g : Fin n → H, (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) A)).prod = 0) → (∀ a b, a ≠ b → (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ g, (∀ a b, b < a → (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ i, (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) i i = ψ i g * (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) i i := by
  intro A H _ n r ψ s hrel
  let φ : Polynomial A →* Matrix (Fin n) (Fin n) A := (Polynomial.aeval (r s)).toRingHom.toMonoidHom
  let p : Fin n → Polynomial A := fun j => Polynomial.X - Polynomial.C (ψ j s)
  have hp : ∀ j, φ (p j) = r s - ψ j s • (1 : Matrix (Fin n) (Fin n) A) := by
    intro j
    simp [φ, p, Algebra.algebraMap_eq_smul_one]
  have hk : ∀ a, kEl (r s) (fun i => ψ i s) a = φ (∏ j ∈ Finset.univ.erase a, p j) := fun a => rfl
  have hfull : φ (∏ j, p j) = 0 := by
    rw [← flagA_full φ p]
    simp only [hp]
    exact hrel fun _ => s
  have h0 : ∀ a b, a ≠ b → kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b = 0 := by
    intro a b hab
    obtain ⟨q, hq⟩ : p a ∣ ∏ j ∈ Finset.univ.erase b, p j := Finset.dvd_prod_of_mem _ (by simp [hab])
    rw [hk, hk, ← map_mul, hq, ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ a), map_mul, hfull, zero_mul]
  have h1 : ∀ g a b, b ≤ a → kEl (r s) (fun i => ψ i s) a * r g * kEl (r s) (fun i => ψ i s) b =
      ψ a g • (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) := by
    intro g a b hab
    have h := hrel (Function.update (fun _ => s) a g)
    rw [flagA_split φ p _ a (fun j hj => by rw [Function.update_of_ne hj, hp])] at h
    rw [Function.update_self, ← Finset.prod_filter, ← Finset.prod_filter] at h
    obtain ⟨q, hq⟩ : ∏ j ∈ Finset.univ.filter (· < a), p j ∣ ∏ j ∈ Finset.univ.erase a, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hj.ne]
    obtain ⟨q', hq'⟩ : ∏ j ∈ Finset.univ.filter (a < ·), p j ∣ ∏ j ∈ Finset.univ.erase b, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [(lt_of_le_of_lt hab hj).ne']
    have h2 : kEl (r s) (fun i => ψ i s) a * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
        kEl (r s) (fun i => ψ i s) b = 0 := by
      rw [hk, hk, hq, hq', mul_comm _ q, map_mul, map_mul]
      calc _ = φ q * (φ (∏ j ∈ Finset.univ.filter (· < a), p j) * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
            φ (∏ j ∈ Finset.univ.filter (a < ·), p j)) * φ q' := by simp only [mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    rw [mul_sub, sub_mul, sub_eq_zero, mul_smul_comm, mul_one, smul_mul_assoc] at h2
    exact h2
  have he : ∀ a b, (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b =
      (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) a b := by
    intro a b
    simpa using flagA_entry (r s) 1 (fun i => ψ i s) a b
  refine ⟨fun a b hab => ?_, fun g => ⟨fun a b hab => ?_, fun i => ?_⟩⟩
  · rw [he, h0 a b hab]; rfl
  · rw [flagA_entry, h1 g a b hab.le, h0 a b hab.ne', smul_zero]; rfl
  · rw [flagA_entry, h1 g i i le_rfl, he]; rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagCUpMul
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem flagC_up_mul {X : Type} [CommRing X] {n : ℕ} {A B : Matrix (Fin n) (Fin n) X}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) :
    (∀ i j, j < i → (A * B) i j = 0) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k j (lt_of_lt_of_le hij h), mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]

private theorem flagC_core {X : Type} [CommRing X] {n : ℕ} (A B S T S₁ T₁ r D : Matrix (Fin n) (Fin n) X) (d : X)
    (g a : Fin n → X) (hAS : A * S = d • (1 : Matrix (Fin n) (Fin n) X)) (hTB : T * B = d • (1 : Matrix (Fin n) (Fin n) X))
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (hg : ∀ i, A i i * B i i * g i = d * d)
    (hL : ∀ i j, j < i → (S₁ * T + S * T₁) i j = 0) (hr : ∀ i j, j < i → r i j = 0)
    (hM : ∀ i j, j < i → (S₁ * r * T + S * D * T + S * r * T₁) i j = 0)
    (hMd : ∀ i, (S₁ * r * T + S * D * T + S * r * T₁) i i = g i * a i + r i i * (S₁ * T + S * T₁) i i) :
    (∀ i j, j < i → ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i j = 0) ∧
      ∀ i, ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i i = (d * d) * a i := by
  have e1 : A * (S₁ * r * T + S * D * T + S * r * T₁) * B =
      A * S₁ * r * (T * B) + (A * S) * D * (T * B) + (A * S) * r * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : A * (S₁ * T + S * T₁) * B = A * S₁ * (T * B) + (A * S) * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have key : (d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r) =
      A * (S₁ * r * T + S * D * T + S * r * T₁) * B - A * (S₁ * T + S * T₁) * B * r := by
    rw [e1, e2, hAS, hTB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul]
    abel
  obtain ⟨m1, m2⟩ := flagC_up_mul hA hM
  obtain ⟨m3, m4⟩ := flagC_up_mul m1 hB
  obtain ⟨l1, l2⟩ := flagC_up_mul hA hL
  obtain ⟨l3, l4⟩ := flagC_up_mul l1 hB
  obtain ⟨l5, l6⟩ := flagC_up_mul l3 hr
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, m3 i j hij, l5 i j hij, sub_zero]
  · rw [Matrix.sub_apply, m4, m2, l6, l4, l2, hMd, ← hg i]
    ring

theorem UpperTheory.V.Th.Coc.flagC :
    ∀ {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (S T : Matrix (Fin n) (Fin n) O) (Δ : Fin n → O), (∀ i, Δ i ≠ 0) → (∀ a b, b < a → S a b = 0 ∧ T a b = 0) → (∀ i, S i i = Δ i ∧ T i i = Δ i) → (∀ a b, a ≠ b → (S * T) a b = 0) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (S₁ T₁ : Matrix (Fin n) (Fin n) X), (∀ a b, a ≠ b → (S₁ * bar X T + bar X S * T₁) a b = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ (r : Matrix (Fin n) (Fin n) O) (D : Matrix (Fin n) (Fin n) X) (a : Fin n → X), (∀ i j, j < i → r i j = 0) → (∀ i j, j < i → (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i j = 0) → (∀ i, (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i i = (Δ i * Δ i) • a i + r i i • (S₁ * bar X T + bar X S * T₁) i i) → (∀ i j, j < i → (c₁ • D - (bar X r * Y - Y * bar X r)) i j = 0) ∧ ∀ i, (c₁ • D - (bar X r * Y - Y * bar X r)) i i = c₁ • a i := by
  intro O _ _ n S T Δ hΔ hup hdg hST
  have hS : ∀ i j, j < i → S i j = 0 := fun i j h => (hup i j h).1
  have hT : ∀ i j, j < i → T i j = 0 := fun i j h => (hup i j h).2
  obtain ⟨d, e, hd, he⟩ : ∃ (d : O) (e : Fin n → O), d ≠ 0 ∧ ∀ i, Δ i * Δ i * e i = d :=
    ⟨∏ i, Δ i * Δ i, fun i => ∏ k ∈ Finset.univ.erase i, Δ k * Δ k,
      Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hΔ i) (hΔ i),
      fun i => Finset.mul_prod_erase Finset.univ (fun k => Δ k * Δ k) (Finset.mem_univ i)⟩
  have hG : S * T = Matrix.diagonal fun i => Δ i * Δ i := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [(flagC_up_mul hS hT).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2]
    · rw [hST i j h, Matrix.diagonal_apply_ne _ h]
  have hdet : S.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hS i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [(hdg i).1]; exact hΔ i
  have hE : ∀ i j, j < i → Matrix.diagonal e i j = 0 := fun i j h => Matrix.diagonal_apply_ne _ h.ne'
  have h1 : S * T * Matrix.diagonal e = d • (1 : Matrix (Fin n) (Fin n) O) := by
    rw [hG, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    simp only [he]
  have h2 : T * Matrix.diagonal e * S = d • (1 : Matrix (Fin n) (Fin n) O) := by
    have h3 : S.adjugate * (S * T * Matrix.diagonal e * S) = S.det • (T * Matrix.diagonal e * S) := by
      rw [Matrix.mul_assoc S, Matrix.mul_assoc S, ← Matrix.mul_assoc S.adjugate, Matrix.adjugate_mul,
        Matrix.smul_mul, Matrix.one_mul]
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul, smul_comm] at h3
    exact (smul_right_injective _ hdet h3).symm
  have hmul : ∀ (X : Type) [CommRing X] [Algebra O X] (P Q : Matrix (Fin n) (Fin n) O),
      bar X P * bar X Q = bar X (P * Q) := fun X _ _ P Q => (Matrix.map_mul).symm
  have hone : ∀ (X : Type) [CommRing X] [Algebra O X],
      bar X (d • (1 : Matrix (Fin n) (Fin n) O)) = algebraMap O X d • (1 : Matrix (Fin n) (Fin n) X) := by
    intro X _ _
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hbar : ∀ (X : Type) [CommRing X] [Algebra O X] (P : Matrix (Fin n) (Fin n) O), (∀ i j, j < i → P i j = 0) →
      ∀ i j, j < i → bar X P i j = 0 := fun X _ _ P hP i j h => by simp [hP i j h]
  refine ⟨d * d, mul_ne_zero hd hd, fun X _ _ S₁ T₁ hL =>
    ⟨-(algebraMap O X d • (T₁ * bar X (Matrix.diagonal e * S))), fun r D a hr hM hMd => ?_⟩⟩
  have := flagC_core (bar X (T * Matrix.diagonal e)) (bar X (Matrix.diagonal e * S)) (bar X S) (bar X T) S₁ T₁ (bar X r) D
    (algebraMap O X d) (fun i => algebraMap O X (Δ i * Δ i)) a (by rw [hmul, h2, hone])
    (by rw [hmul, ← Matrix.mul_assoc, h2, hone]) (hbar X _ (flagC_up_mul hT hE).1) (hbar X _ (flagC_up_mul hE hS).1)
    (fun i => by
      change algebraMap O X ((T * Matrix.diagonal e) i i) * algebraMap O X ((Matrix.diagonal e * S) i i) * _ = _
      rw [← map_mul, ← map_mul, ← map_mul, (flagC_up_mul hT hE).2,
        (flagC_up_mul hE hS).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2, ← he i]
      congr 1
      ring)
    (fun i j h => hL i j h.ne') (hbar X r hr) hM
    (fun i => by rw [hMd i, Algebra.smul_def, Algebra.smul_def]; rfl)
  rw [← map_mul, algebraMap_smul] at this
  refine ⟨this.1, fun i => ?_⟩
  rw [this.2 i, Algebra.smul_def]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.IdemDiag
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.idemDiag :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (e : Fin n → Matrix (Fin n) (Fin n) O), CompleteOrthogonalIdempotents e → (∀ i, (e i).trace = 1) → ∃ Q : GL (Fin n) O, ∀ i, ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * e i * (Q : Matrix (Fin n) (Fin n) O) = Matrix.single i i 1 := by
  intro O _ _ n e he htr
  classical
  have hmul : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (he.idem i).eq
    · exact he.ortho hij
  have hentry : ∀ i j a b, (e i * e j) a b = if i = j then e i a b else 0 := by
    intro i j a b
    rw [hmul]
    split_ifs <;> simp
  have hc : ∀ i, ∃ c, IsUnit (e i c c) := by
    intro i
    by_contra hne
    push_neg at hne
    have hmem : (e i).trace ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ (fun c _ => (IsLocalRing.mem_maximalIdeal _).mpr (hne c))
    rw [htr i] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem isUnit_one
  choose c hcu using hc
  let Qm : Matrix (Fin n) (Fin n) O := Matrix.of fun r j => e j r (c j)
  let Sm : Matrix (Fin n) (Fin n) O := Matrix.of fun i r => e i (c i) r
  have hSQ : Sm * Qm = Matrix.diagonal fun i => e i (c i) (c i) := by
    ext i j
    change (e i * e j) (c i) (c j) = _
    rw [hentry, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hdet : IsUnit (Sm * Qm).det := by
    rw [hSQ, Matrix.det_diagonal]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hcu i)
  rw [Matrix.det_mul] at hdet
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det Qm).mpr (isUnit_of_mul_isUnit_right hdet)
  refine ⟨U, fun i => ?_⟩
  have heQ : e i * Qm = Qm * Matrix.single i i 1 := by
    ext r j
    change (e i * e j) r (c j) = _
    rw [hentry, Matrix.mul_apply]
    simp only [Matrix.single_apply, Qm, Matrix.of_apply]
    split_ifs with h
    · subst h
      simp
    · simp [h]
  rw [mul_assoc, hU, heQ, ← hU, Units.inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem k0 {O G : Type} [CommRing O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O)
    (hs : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) (X : Type) [CommRing X] [Algebra O X]
    (W : Matrix (Fin n) (Fin n) X) (h : ∀ g, (bar X (ρ g) * W).trace = 0) : c₀ • W = 0 := by
  have key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0 := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp [bar]
    | add x y _ _ hx hy =>
      have e : bar X (x + y) = bar X x + bar X y := by
        ext i j
        simp [bar]
      rw [e, add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx =>
      have e : bar X (a • x) = a • bar X x := by
        ext i j
        simp only [bar]
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          Algebra.smul_def]
      rw [e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have t := key _ (hs (Matrix.single j i 1))
  have e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀) := by
    ext a b
    simp [bar, Matrix.single_apply]
    split_ifs <;> simp
  rw [e] at t
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Algebra.smul_def] using t

theorem UpperTheory.V.Th.Coc.kill0 :
    ∀ {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ W : Matrix (Fin n) (Fin n) O, (∀ g, (ρ g * W).trace = 0) → W = 0) ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (W : Matrix (Fin n) (Fin n) X), (∀ g, (bar X (ρ g) * W).trace = 0) → c₀ • W = 0 := by
  intro O G _ _ _ n ρ c₀ hc hs
  refine ⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩
  have hb : ∀ g, (bar O (ρ g) * W).trace = 0 := by
    intro g
    have e : bar O (ρ g) = ρ g := by
      ext i j
      simp [bar]
    rw [e]
    exact hW g
  have := k0 ρ c₀ hs O W hb
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftConj
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftConj :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ ρ' : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (c : O) (Q : GL (Fin n) O) (d : E →+ Matrix (Fin n) (Fin n) X), (∀ a, ρ a = (Q : Matrix (Fin n) (Fin n) O) * ρ' a * ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) → IsLift x δ ρ' τ c d → ∃ d' : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ c d' ∧ ∀ a, d' a = bar X (Q : Matrix (Fin n) (Fin n) O) * d a * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ ρ' τ c Q d hρ hL
  have hbm : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := by
    intro A B
    simp [bar, Matrix.map_mul]
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hl : bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * bar X (Q : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hbm, Units.inv_mul, hbar1]
  have hbρ : ∀ a, bar X (ρ a) = bar X (Q : Matrix (Fin n) (Fin n) O) * bar X (ρ' a) * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    rw [hρ, hbm, hbm]
  set P := bar X (Q : Matrix (Fin n) (Fin n) O) with hPdef
  set Pi := bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hPidef
  refine ⟨AddMonoidHom.mk' (fun a => P * d a * Pi) (fun a b => by rw [map_add (f := _), mul_add, add_mul]), ?_, fun a => rfl⟩
  constructor
  · intro a b
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.mul, hbρ, hbρ]
    have e1 : P * d a * Pi * (P * bar X (ρ' b) * Pi) = P * (d a * bar X (ρ' b)) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    have e2 : P * bar X (ρ' a) * Pi * (P * d b * Pi) = P * (bar X (ρ' a) * d b) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    rw [e1, e2, mul_add, add_mul]
  · intro r a
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.smul, hbρ, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  · intro a
    simp only [AddMonoidHom.mk'_apply]
    rw [Matrix.trace_mul_cycle, hl, Matrix.one_mul, hL.tr]
end

