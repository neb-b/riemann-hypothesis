module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaOverLift
section
open IsLocalRing

private theorem exists_field_lift {R S F K L : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Field F] [Field K] [Field L] (c : F →+* K) (d : F →+* L) (a : R →+* F) (b : S →+* K)
    (hab : b.comp (algebraMap R S) = c.comp a)
    {ι : Type} (u : ι → S) (f : ι → Polynomial R) (hu : Algebra.adjoin R (Set.range u) = ⊤)
    (hf : ∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧
      ((f i).map (d.comp a)).Splits) :
    ∃ ψ : S →+* L, ψ.comp (algebraMap R S) = d.comp a ∧
      RingHom.ker ψ = RingHom.ker b := by
  letI : Algebra F K := c.toAlgebra
  letI : Algebra F L := d.toAlgebra
  change b.comp (algebraMap R S) = (algebraMap F K).comp a at hab
  have hab' : ∀ r, b (algebraMap R S r) = algebraMap F K (a r) := fun r => RingHom.congr_fun hab r
  have hT : ∀ s ∈ Set.range (fun i => b (u i)),
      IsIntegral F s ∧ ((minpoly F s).map (algebraMap F L)).Splits := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hf i
    have h4 : Polynomial.aeval (b (u i)) ((f i).map a) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hab, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, h2, map_zero]
    refine ⟨⟨_, h1.map a, h4⟩, ?_⟩
    rw [← Polynomial.map_map] at h3
    exact h3.of_dvd ((h1.map a).map _).ne_zero (Polynomial.map_dvd _ (minpoly.dvd F _ h4))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_adjoin_of_splits hT
  have hmem : ∀ s : S, b s ∈ IntermediateField.adjoin F (Set.range (fun i => b (u i))) := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r => rw [hab']; exact IntermediateField.algebraMap_mem _ _
    | add y z _ _ hy hz => rw [map_add b]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let b' : S →+* IntermediateField.adjoin F (Set.range (fun i => b (u i))) :=
    b.codRestrict _ hmem
  refine ⟨φ.toRingHom.comp b', ?_, ?_⟩
  · ext r
    have : b' (algebraMap R S r) = algebraMap F _ (a r) := Subtype.ext (hab' r)
    change φ (b' (algebraMap R S r)) = algebraMap F L (a r)
    rw [this, AlgHom.commutes]
  · ext s
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change φ (b' s) = 0 ↔ _
    rw [map_eq_zero_iff φ φ.toRingHom.injective]
    exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.exists_lift_ker_eq :
    ∀ (R S A : Type) [CommRing R] [CommRing S] [CommRing A] [IsDomain A] [Algebra R S] (x : R →+* A)
      (ι : Type) (u : ι → S) (f : ι → Polynomial R), Algebra.adjoin R (Set.range u) = ⊤ →
      (∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧ ((f i).map x).Splits) →
      ∀ P : Ideal S, P.IsPrime → P.comap (algebraMap R S) = RingHom.ker x →
      ∃ x' : S →+* A, x'.comp (algebraMap R S) = x ∧ RingHom.ker x' = P := by
  intro R S A _ _ _ _ _ x ι u f hu hf P hP hPx
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let j : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hj : Function.Injective j := IsFractionRing.injective A (FractionRing A)
  let b : S →+* FractionRing (S ⧸ P) :=
    (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
  have hb : RingHom.ker b = P := by
    ext s
    rw [RingHom.mem_ker]
    change algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hkb : RingHom.ker (b.comp (algebraMap R S)) = RingHom.ker x := by
    rw [← RingHom.comap_ker, hb, hPx]
  have hkj : RingHom.ker (j.comp x) = RingHom.ker x := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot j).1 hj]
    rfl
  let g₁ : R ⧸ RingHom.ker x →+* FractionRing (S ⧸ P) :=
    Ideal.Quotient.lift _ (b.comp (algebraMap R S)) (fun r hr => by
      rw [← hkb] at hr; exact hr)
  let g₂ : R ⧸ RingHom.ker x →+* FractionRing A :=
    Ideal.Quotient.lift _ (j.comp x) (fun r hr => by rw [← hkj] at hr; exact hr)
  have hg₁ : Function.Injective g₁ := RingHom.lift_injective_of_ker_le_ideal _ _ hkb.le
  have hg₂ : Function.Injective g₂ := RingHom.lift_injective_of_ker_le_ideal _ _ hkj.le
  let F := FractionRing (R ⧸ RingHom.ker x)
  let a : R →+* F := (algebraMap (R ⧸ RingHom.ker x) F).comp (Ideal.Quotient.mk _)
  obtain ⟨c, h1⟩ : ∃ c : F →+* FractionRing (S ⧸ P), b.comp (algebraMap R S) = c.comp a :=
    ⟨IsFractionRing.lift hg₁, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₁ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _)).symm⟩
  obtain ⟨d, h2⟩ : ∃ d : F →+* FractionRing A, d.comp a = j.comp x :=
    ⟨IsFractionRing.lift hg₂, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₂ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _))⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_field_lift c d a b h1 u f hu (fun i =>
    ⟨(hf i).1, (hf i).2.1, by rw [h2, ← Polynomial.map_map]; exact (hf i).2.2.map j⟩)
  rw [h2] at hψ1
  rw [hb] at hψ2
  have hmem : ∀ s : S, ψ s ∈ j.range := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hm, h0, hsp⟩ := hf i
      have h4 : Polynomial.eval₂ j (ψ (u i)) ((f i).map x) = 0 := by
        rw [Polynomial.eval₂_map, ← hψ1, ← Polynomial.hom_eval₂,
          ← Polynomial.aeval_def, h0, map_zero]
      rw [hsp.eq_prod_roots_of_monic (hm.map x), Polynomial.eval₂_multiset_prod,
        Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at h4
      obtain ⟨c, -, hc⟩ := h4
      refine ⟨c, ?_⟩
      simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at hc
      exact (sub_eq_zero.1 hc).symm
    | algebraMap r => exact ⟨x r, (RingHom.congr_fun hψ1 r).symm⟩
    | add y z _ _ hy hz => rw [map_add ψ]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  choose g hg using hmem
  let x' : S →+* A :=
    { toFun := g
      map_one' := hj (by rw [hg, map_one, map_one])
      map_mul' := fun s t => hj (by rw [map_mul, hg, hg, hg, map_mul])
      map_zero' := hj (by rw [hg, map_zero, map_zero])
      map_add' := fun s t => hj (by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]) }
  refine ⟨x', ?_, ?_⟩
  · ext r
    exact hj ((hg _).trans (RingHom.congr_fun hψ1 r))
  · ext s
    rw [← hψ2, RingHom.mem_ker, RingHom.mem_ker, ← hg, map_eq_zero_iff j hj]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.exists_unit_entry {R : Type} [CommRing R] [IsLocalRing R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ a b, IsUnit (e a b) := by
  classical
  by_contra h
  push_neg at h
  have hm : ∀ a b, e a b ∈ maximalIdeal R := fun a b => (mem_maximalIdeal _).2 (h a b)
  have hmap : (1 - e).map (residue R) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [(residue_eq_zero_iff _).2 (hm a a)]
    · simp [Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]
  have hdet : IsUnit (1 - e).det := by
    have h1 : residue R (1 - e).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]
    exact (isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  apply h0
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact hu.mul_right_eq_zero.1 h2

theorem UpperTheory.V.AlgebraTools.coi_conj_single :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Matrix ι ι R), CompleteOrthogonalIdempotents f → (∀ i, f i ≠ 0) → ∃ g : GL ι R, ∀ i, (g : Matrix ι ι R) * f i * ((g⁻¹ : GL ι R) : Matrix ι ι R) = single i i 1 := by
  intro R _ _ ι _ _ f hf h0
  classical
  have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i =>
    UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)
  choose a b hu using hc
  set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP
  set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ
  have hent : ∀ (M : Matrix ι ι R) (j k : ι),
      (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k) := by
    intro M j k
    simp only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hidem : ∀ i, f i * f i = f i := fun i => (hf.idem i).eq
  have hort : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => hf.ortho hij
  have hQP : Q * P = 1 := by
    ext j k
    have h1 := hent 1 j k
    simp only [Matrix.mul_one] at h1
    rw [h1]
    by_cases hjk : j = k
    · subst hjk
      rw [hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]
    · rw [hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩
  change Q * f i * P = single i i 1
  ext j k
  rw [hent, Matrix.single_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hik : i = k
    · subst hik
      rw [hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]
    · rw [hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]
  · rw [hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
section
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DensityProd
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem sum_matrix_single_diag_one_eq_one {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] :
    ∑ i : n, Matrix.single i i (1 : F) = 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
    have he : (Finset.univ.filter fun w : n => w = u ∧ w = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨rfl, rfl⟩
      exact h rfl
    rw [he]
    simp

private theorem intertwiner_of_ker {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (ht : ∀ B : Matrix (d t) (d t) F, ∃ x ∈ S, x t = B)
    (hk : ∀ x ∈ S, x t = 0 → x s = 0) :
    ∃ V : Matrix (d s) (d t) F, V ≠ 0 ∧ ∀ x ∈ S, x s * V = V * x t := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x t = y t → x s = y s := by
    intro x hx y hy h
    have := hk (x - y) (S.sub_mem hx hy) (by rw [Pi.sub_apply, h, sub_self])
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨i0⟩ := (inferInstance : Nonempty (d t))
  choose xx hxS hxt using fun j => ht (Matrix.single j i0 (1 : F))
  choose z hzS hzt using fun j => ht (Matrix.single i0 j (1 : F))
  have hne : xx i0 s ≠ 0 := by
    intro h0
    have hx0 : ∀ j, xx j s = 0 := by
      intro j
      have := key (xx j * xx i0) (S.mul_mem (hxS j) (hxS i0)) (xx j) (hxS j)
        (by rw [Pi.mul_apply, hxt, hxt, Matrix.single_mul_single_same, one_mul])
      rw [← this, Pi.mul_apply, h0, mul_zero]
    have h1 := key (∑ j, xx j * z j) (Subalgebra.sum_mem _ fun j _ => S.mul_mem (hxS j) (hzS j)) 1 S.one_mem
      (by
        rw [Finset.sum_apply]
        simp only [Pi.mul_apply, hxt, hzt, Matrix.single_mul_single_same, one_mul, Pi.one_apply]
        exact sum_matrix_single_diag_one_eq_one)
    rw [Finset.sum_apply] at h1
    simp only [Pi.mul_apply, hx0, zero_mul, Finset.sum_const_zero, Pi.one_apply] at h1
    exact zero_ne_one h1
  obtain ⟨a, b, hab⟩ : ∃ a b, xx i0 s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨Matrix.of fun u j => xx j s u b, ?_, ?_⟩
  · intro hV
    apply hab
    have := congrFun (congrFun hV a) i0
    simpa using this
  · intro x hx
    ext u k
    have e := key (x * xx k) (S.mul_mem hx (hxS k)) (∑ j, x t j k • xx j)
      (Subalgebra.sum_mem _ fun j _ => S.smul_mem (hxS j) _) (by
        rw [Pi.mul_apply, hxt, Finset.sum_apply]
        simp only [Pi.smul_apply, hxt]
        ext p q
        by_cases hq : i0 = q <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, hq])
    have e2 := congrFun (congrFun e u) b
    simp only [Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [e2]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem separate {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (hs : ∀ B : Matrix (d s) (d s) F, ∃ x ∈ S, x s = B)
    (hk : ∃ x ∈ S, x t = 0 ∧ x s ≠ 0) : ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
  obtain ⟨x, hxS, hxt, hxs⟩ := hk
  obtain ⟨a, b, hab⟩ : ∃ a b, x s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxs (Matrix.ext h)
  choose p hpS hps using fun i => hs (Matrix.single i a (x s a b)⁻¹)
  choose q hqS hqs using fun i => hs (Matrix.single b i (1 : F))
  refine ⟨∑ i, p i * x * q i, ?_, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun i _ => S.mul_mem (S.mul_mem (hpS i) hxS) (hqS i)
  · rw [Finset.sum_apply]
    simp [Pi.mul_apply, hxt]
  · rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hps, hqs, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    ext u v
    by_cases h : u = v
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
      have he : (Finset.univ.filter fun w : d s => w = u ∧ w = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨rfl, rfl⟩
        exact h rfl
      rw [he]
      simp

theorem UpperTheory.V.AlgebraTools.density_prod :
    ∀ {F Γ : Type} [Field F] [Monoid Γ] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (ρ : ∀ s, Γ →* Matrix (d s) (d s) F), (∀ s, Submodule.span F (Set.range (ρ s)) = ⊤) → (∀ s t, s ≠ t → ∀ V : Matrix (d s) (d t) F, (∀ g, ρ s g * V = V * ρ t g) → V = 0) → Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) = ⊤ := by
  intro F Γ _ _ σ _ _ d _ _ _ ρ hspan hint
  let φ : Γ →* ((s : σ) → Matrix (d s) (d s) F) :=
    { toFun := fun g s => ρ s g
      map_one' := funext fun s => map_one (ρ s)
      map_mul' := fun g h => funext fun s => map_mul (ρ s) g h }
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra F ((s : σ) → Matrix (d s) (d s) F),
      S = Algebra.adjoin F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) := ⟨_, rfl⟩
  have hmem : ∀ g, (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F) ∈ S := by
    intro g
    rw [hSdef]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  have hsurj : ∀ s (B : Matrix (d s) (d s) F), ∃ x ∈ S, x s = B := by
    intro s B
    have hB : B ∈ Submodule.span F (Set.range (ρ s)) := by
      rw [hspan s]
      exact Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact ⟨_, hmem g, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, h1, e1⟩ := hy
      obtain ⟨x2, h2, e2⟩ := hz
      exact ⟨x1 + x2, S.add_mem h1 h2, by rw [Pi.add_apply, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, h1, e1⟩ := hy
      exact ⟨c • x1, S.smul_mem h1 c, by rw [Pi.smul_apply, e1]⟩
  have hsep : ∀ s t, s ≠ t → ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
    intro s t hst
    apply separate d S s t (hsurj s)
    by_contra hno
    push_neg at hno
    obtain ⟨V, hV0, hV⟩ := intertwiner_of_ker d S s t (hsurj t) hno
    exact hV0 (hint s t hst V fun g => hV _ (hmem g))
  have he : ∀ s, ∃ e ∈ S, e s = 1 ∧ ∀ t, t ≠ s → e t = 0 := by
    intro s
    have hT : ∀ T : Finset σ, s ∉ T → ∃ e ∈ S, e s = 1 ∧ ∀ t ∈ T, e t = 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, S.one_mem, rfl, by simp⟩
      | @insert t T htT ih =>
        intro hs
        rw [Finset.mem_insert, not_or] at hs
        obtain ⟨e, heS, hes, het⟩ := ih hs.2
        obtain ⟨y, hyS, hyt, hys⟩ := hsep s t hs.1
        refine ⟨e * y, S.mul_mem heS hyS, by rw [Pi.mul_apply, hes, hys, one_mul], ?_⟩
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [Pi.mul_apply, hyt, mul_zero]
        · rw [Pi.mul_apply, het u hu, zero_mul]
    obtain ⟨e, heS, hes, het⟩ := hT (Finset.univ.erase s) (by simp)
    exact ⟨e, heS, hes, fun t ht => het t (by simp [ht])⟩
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    choose e heS hes het using he
    choose zz hzS hzs using fun s => hsurj s (Y s)
    have hY : Y = ∑ s, zz s * e s := by
      funext u
      rw [Finset.sum_apply, Finset.sum_eq_single u]
      · rw [Pi.mul_apply, hzs, hes, mul_one]
      · intro b _ hb
        rw [Pi.mul_apply, het b u hb.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ u) h
    rw [hY]
    exact Subalgebra.sum_mem _ fun s _ => S.mul_mem (hzS s) (heS s)
  have h2 : Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) =
      Subalgebra.toSubmodule S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hmem g
    · rw [hSdef, Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      have hx' : x ∈ MonoidHom.mrange φ :=
        (Submonoid.closure_le.mpr (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_mrange.mpr ⟨g, rfl⟩)) hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hx'
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [h2, htop]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
section
open IsLocalRing MvPolynomial

namespace UpperTheory.V.AlgebraTools

variable {P : Type} [CommRing P] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_map_C (p : Ideal P) [p.IsPrime] :
    (p.map (C : P →+* MvPolynomial ι P)).IsPrime := by
  have he : p.map (C : P →+* MvPolynomial ι P) =
      RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [he]
  exact RingHom.ker_isPrime _

def relIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := Ideal.span (Set.range (z.mulVec m))

def detIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := relIdeal z m ⊔ Ideal.span {z.det}

noncomputable def lam (P : Type) [CommRing P] (c : ι) (j : ι) : MvPolynomial ι P :=
  if j = c then 1 else X j

noncomputable def chartGen (z : Matrix ι ι P) (m : ι → P) (c : ι) :
    ι ⊕ {j : ι // j ≠ c} → MvPolynomial ι P :=
  Sum.elim ((z.map C).mulVec (lam P c)) (fun j => C (m j.1) - lam P c j.1 * C (m c))

noncomputable def chartIdeal (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal (MvPolynomial ι P) :=
  Ideal.span (Set.range (chartGen z m c))

noncomputable def genKer [IsLocalRing P] (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal P where
  carrier := {f | ∃ s : MvPolynomial ι P, s ∉ (maximalIdeal P).map (C : P →+* MvPolynomial ι P) ∧
    s * C f ∈ chartIdeal z m c}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top (by
    have : (maximalIdeal P).IsPrime := inferInstance
    exact isPrime_map_C _)), by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    have hp : ((maximalIdeal P).map (C : P →+* MvPolynomial ι P)).IsPrime :=
      isPrime_map_C _
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * C (a + b) = t * (s * C a) + s * (t * C b) := by rw [map_add (f := _)]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  smul_mem' := by
    rintro r a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have : s * C (r • a) = C r * (s * C a) := by rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha

end UpperTheory.V.AlgebraTools
end

