module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RelSub
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {X : Type} [CommRing X] {a g : ℕ} {c : Fin a → Fin g → X}

private theorem rel_C (r : X) : DD.Rel c (DD.C r) (DD.C r) :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_zero : DD.Rel c 0 0 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_one : DD.Rel c 1 1 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_add {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u + u') (v + v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], by simp [a2, b2], fun k => ?_, fun j => ?_⟩
  · simp [a3, b3, mul_add, Finset.sum_add_distrib]
  · simp [a4, b4, mul_add, Finset.sum_add_distrib]

private theorem rel_neg {u : DD X a} {v : DD X g} (h : DD.Rel c u v) : DD.Rel c (-u) (-v) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨by simp [a1], by simp [a2], fun k => ?_, fun j => ?_⟩
  · simp [a3]
  · simp [a4]

private theorem rel_pair {p q : Fin a → X} {s t : Fin g → X} (h : ∀ k, p k = ∑ j, c k j * s j)
    (h' : ∀ j, t j = ∑ k, c k j * q k) : ∑ k, p k * q k = ∑ j, s j * t j := by
  simp only [h, h', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem rel_mul {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u * u') (v * v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], ?_, fun k => ?_, fun j => ?_⟩
  · have e1 := rel_pair a3 b4
    have e2 := rel_pair b3 a4
    have e3 : ∑ k, u.ep' k * u'.ep k = ∑ j, v.ep' j * v'.ep j := by
      simpa only [mul_comm] using e2
    simp only [DD.mul_eta, Finset.sum_add_distrib, e1, e3, a1, a2, b1, b2]
  · simp only [DD.mul_ep, a3, b3, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [DD.mul_ep', a4, b4, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem rel_sum {ι : Type} (s : Finset ι) (f : ι → DD X a) (f' : ι → DD X g)
    (h : ∀ i, DD.Rel c (f i) (f' i)) : DD.Rel c (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact rel_add (h i) ih

end

theorem UpperTheory.V.Pa.relSub :
    ∀ (X : Type) [CommRing X] (a g : ℕ) (c : Fin a → Fin g → X), (∀ r : X, DD.Rel c (DD.C r) (DD.C r)) ∧ (∀ u v u' v', DD.Rel c u v → DD.Rel c u' v' → DD.Rel c (u + u') (v + v') ∧ DD.Rel c (u - u') (v - v') ∧ DD.Rel c (u * u') (v * v')) ∧ (∀ u v v', DD.Rel c u v → DD.Rel c u v' → v.ep = v'.ep → v = v') ∧ ∀ (n : ℕ) (l : List (Matrix (Fin n) (Fin n) (DD X a) × Matrix (Fin n) (Fin n) (DD X g))), (∀ p ∈ l, ∀ i j, DD.Rel c (p.1 i j) (p.2 i j)) → ∀ i j, DD.Rel c ((l.map Prod.fst).prod i j) ((l.map Prod.snd).prod i j) := by
  intro X _ a g c
  refine ⟨rel_C, fun u v u' v' h h' => ⟨rel_add h h', ?_, rel_mul h h'⟩, ?_, ?_⟩
  · rw [sub_eq_add_neg, sub_eq_add_neg]
    exact rel_add h (rel_neg h')
  · rintro u v v' ⟨a1, a2, -, a4⟩ ⟨b1, b2, -, b4⟩ e
    exact DD.ext (a1.symm.trans b1) e (funext fun j => (a4 j).trans (b4 j).symm) (a2.symm.trans b2)
  · intro n l
    induction l with
    | nil =>
      intro _ i j
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact rel_one
      · exact rel_zero
    | cons p l ih =>
      intro h i j
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact rel_sum _ _ _ fun k => rel_mul (h p (List.mem_cons_self ..) i k)
        (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) k j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RfEx
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rfEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsLocalRing O] [Algebra O K] [CommRing B] [Algebra O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K), IsCplAt B (RingHom.ker f) Bh → ∃ rF : Bh →+* FractionRing (PowerSeries K), (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) ∧ RingHom.ker rF = maximalIdeal Bh := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ f h
  haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let φ : B →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)
  have hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f := by
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    ext b
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]
    exact map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap
  refine ⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hm
    have hu : IsUnit x := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
      exact hm
    exact (hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)
  · have hm := IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1
    rw [pow_one, pow_one] at hm
    rw [← hm]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingHom.mem_ker.mp ha, map_zero]
end

