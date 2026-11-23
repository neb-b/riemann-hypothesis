module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GrSpan
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem grSpan_mem {Λ : Type} [CommRing Λ] {σ : Type} (d : σ → ℕ)
    (J : Ideal (MvPowerSeries σ Λ)) (T : Finset σ) (hJ : ∀ s, MvPowerSeries.X s ^ d s ∈ J) :
    ∀ g : MvPowerSeries σ Λ,
      (∀ n : σ →₀ ℕ, (∀ s ∈ T, n s < d s) → MvPowerSeries.coeff n g = 0) → g ∈ J := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have h0 : g = 0 := by
      ext n
      exact hg n (by simp)
    rw [h0]
    exact J.zero_mem
  | insert t T ht ih =>
    intro g hg
    let h : MvPowerSeries σ Λ := fun n => MvPowerSeries.coeff (n + Finsupp.single t (d t)) g
    let g' : MvPowerSeries σ Λ := fun n => if n t < d t then MvPowerSeries.coeff n g else 0
    have hh : ∀ n, MvPowerSeries.coeff n h = MvPowerSeries.coeff (n + Finsupp.single t (d t)) g :=
      fun n => rfl
    have hg' : ∀ n, MvPowerSeries.coeff n g' = if n t < d t then MvPowerSeries.coeff n g else 0 :=
      fun n => rfl
    have hsplit : g = MvPowerSeries.X t ^ d t * h + g' := by
      ext n
      rw [map_add (f := _), MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, hg', hh]
      by_cases hn : d t ≤ n t
      · have hle : Finsupp.single t (d t) ≤ n := Finsupp.single_le_iff.2 hn
        rw [if_pos hle, if_neg (by omega), one_mul, tsub_add_cancel_of_le hle, add_zero]
      · have hle : ¬ Finsupp.single t (d t) ≤ n := fun h' => hn (Finsupp.single_le_iff.1 h')
        rw [if_neg hle, if_pos (by omega), zero_add]
    rw [hsplit]
    refine J.add_mem (J.mul_mem_right _ (hJ t)) (ih g' fun n hn => ?_)
    rw [hg']
    split_ifs with hnt
    · exact hg n fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs'
        · exact hnt
        · exact hn s hs'
    · rfl

private theorem grSpan_prod {Λ : Type} [CommRing Λ] {σ : Type} [Fintype σ] (a : σ → ℕ) :
    (∏ s, MvPowerSeries.X s ^ a s : MvPowerSeries σ Λ) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  classical
  simp_rw [MvPowerSeries.X_pow_eq]
  rw [Finsupp.equivFunOnFinite_symm_eq_sum]
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

private theorem grSpan_small {Λ : Type} [CommRing Λ] {σ : Type} [Fintype σ] [DecidableEq σ]
    (d : σ → ℕ) (f : MvPowerSeries σ Λ) (n : σ →₀ ℕ) (hn : ∀ s, n s < d s) :
    MvPowerSeries.coeff n (f - ∑ α : (∀ s, Fin (d s)),
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun s => (α s : ℕ)) f •
        (∏ s, MvPowerSeries.X s ^ (α s : ℕ) : MvPowerSeries σ Λ)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, sub_eq_zero]
  simp only [grSpan_prod, map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (fun s => ⟨n s, hn s⟩ : ∀ s, Fin (d s))]
  · simp [Finsupp.equivFunOnFinite_symm_coe]
  · intro β _ hβ
    rw [if_neg]
    intro h
    apply hβ
    funext s
    exact Fin.ext (by have := DFunLike.congr_fun h s; simpa using this.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (σ : Type) [Fintype σ] (d : σ → ℕ) (w : σ → MvPowerSeries σ Λ),
      (∀ s, w s - MvPowerSeries.X s ^ d s ∈ (IsLocalRing.maximalIdeal Λ).map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) →
      Submodule.span Λ (Set.range fun α : (∀ s, Fin (d s)) =>
        Ideal.Quotient.mk (Ideal.span (Set.range w)) (∏ s, MvPowerSeries.X s ^ (α s : ℕ))) = ⊤ := by
  intro Λ _ _ _ _ σ _ d w hw
  classical
  set m := IsLocalRing.maximalIdeal Λ with hm
  have hjac : m.map (algebraMap Λ (MvPowerSeries σ Λ)) ≤ Ring.jacobson (MvPowerSeries σ Λ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ring.mem_jacobson_iff]
    intro y
    have key : ∀ c : Λ, IsUnit (r * c + 1) := by
      intro c
      by_contra hu
      have h1 : r * c + 1 ∈ m := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
      have h2 : r * c ∈ m := Ideal.mul_mem_right _ _ hr
      have h3 := Ideal.sub_mem _ h1 h2
      rw [add_sub_cancel_left] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [MvPowerSeries.algebraMap_apply] using key _
  haveI hQA : IsHausdorff (m.map (algebraMap Λ (MvPowerSeries σ Λ)))
      (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)) := IsHausdorff.of_le_jacobson _ _ hjac
  haveI : IsHausdorff m (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)) :=
    IsHausdorff.of_map (S := MvPowerSeries σ Λ)
      (J := m.map (algebraMap Λ (MvPowerSeries σ Λ))) (hIJ := le_rfl)
  obtain ⟨hnak, -⟩ := UpperTheory.V.abelian₂.nakayama Λ m (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w))
  rw [← (Fintype.equivFin (∀ s, Fin (d s))).symm.surjective.range_comp]
  apply hnak
  rw [(Fintype.equivFin (∀ s, Fin (d s))).symm.surjective.range_comp, eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hJ : ∀ s, MvPowerSeries.X s ^ d s ∈
      Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) := fun s => by
    have h1 : w s ∈ Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) :=
      Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
    have h2 : w s - MvPowerSeries.X s ^ d s ∈
        Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) :=
      Ideal.mem_sup_right (hw s)
    simpa using Ideal.sub_mem _ h1 h2
  have hmem := grSpan_mem d _ Finset.univ hJ _
    (fun n hn => grSpan_small d f n (fun s => hn s (Finset.mem_univ s)))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  have hab' := hab.symm
  rw [sub_eq_iff_eq_add] at hab'
  rw [hab', map_add (f := _), map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
  · have h1 : Ideal.Quotient.mk (Ideal.span (Set.range w)) b ∈
        ((m.map (algebraMap Λ (MvPowerSeries σ Λ))) • ⊤ :
          Submodule (MvPowerSeries σ Λ) (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w))) := by
      have e : Ideal.Quotient.mk (Ideal.span (Set.range w)) b =
          b • Ideal.Quotient.mk (Ideal.span (Set.range w)) 1 := by
        rw [map_one, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
      rw [e]
      exact Submodule.smul_mem_smul hb Submodule.mem_top
    have h2 := Submodule.restrictScalars_map_smul_eq m
      (⊤ : Submodule (MvPowerSeries σ Λ) (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)))
    rw [Submodule.restrictScalars_top] at h2
    rw [← h2, Submodule.restrictScalars_mem]
    exact h1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have e := map_smul (Ideal.Quotient.mkₐ Λ (Ideal.span (Set.range w)))
      (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun s => (α s : ℕ)) f)
      (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
    rw [Ideal.Quotient.mkₐ_eq_mk] at e
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdProps
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem rename_alt {R : Type} [CommRing R] {n : ℕ} (u : Perm (Fin n)) (x : MvPolynomial (Fin n) R) :
    rename u (alt x) = Perm.sign u • alt x := by
  unfold alt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun w => ?_
  simp only [Equiv.coe_mulLeft]
  rw [Units.smul_def, map_zsmul, rename_rename, ← Perm.coe_mul, Perm.sign_mul, mul_smul, smul_smul,
    Int.units_mul_self, one_smul, Units.smul_def]

private theorem antisymmetrizer_add {R : Type} [CommRing R] {n : ℕ} (x y : MvPolynomial (Fin n) R) :
    alt (x + y) = alt x + alt y := by
  simp only [alt, map_add (f := _), smul_add, Finset.sum_add_distrib]

private theorem antisymmetrizer_symmetric_mul {R : Type} [CommRing R] {n : ℕ} (z x : MvPolynomial (Fin n) R)
    (hz : z.IsSymmetric) : alt (z * x) = z * alt x := by
  simp only [alt, map_mul, hz _, Finset.mul_sum, mul_smul_comm]

private theorem eq_of_De_mul_eq_De_mul {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p q : MvPolynomial (Fin n) R) (h : De R n * p = De R n * q) : p = q :=
  by
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    apply mul_left_cancel₀ ?_ h
    rw [hd, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective

theorem UpperTheory.V.AlgebraTools.hkDdProps :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), (∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y) ∧ (∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x) ∧
      (∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric) ∧
      ∃ D : MvPolynomial (Fin n) R →ₗ[symmetricSubalgebra (Fin n) R] symmetricSubalgebra (Fin n) R, ∀ x, (D x : MvPolynomial (Fin n) R) = dd x := by
  intro R _ _ n
  have hadd : ∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y := by
    intro x y
    apply eq_of_De_mul_eq_De_mul
    rw [mul_add, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_add]
  have hmul : ∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x := by
    intro z x hz
    apply eq_of_De_mul_eq_De_mul
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_symmetric_mul z x hz, mul_left_comm, UpperTheory.V.AlgebraTools.hkDdSpec]
  have hsym : ∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric := by
    intro x w
    apply eq_of_De_mul_eq_De_mul
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    have hw : rename w (De R n) = Perm.sign w • De R n := by
      rw [hd, AlgHom.map_det]
      have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
        ext i j
        simp [Matrix.vandermonde_apply]
      rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
    have e1 := congrArg (rename ⇑w) (UpperTheory.V.AlgebraTools.hkDdSpec R n x)
    rw [map_mul, hw, rename_alt, ← UpperTheory.V.AlgebraTools.hkDdSpec R n x,
      smul_mul_assoc] at e1
    exact (smul_left_cancel_iff _).mp e1
  refine ⟨hadd, hmul, hsym, ?_⟩
  refine ⟨{ toFun := fun x => ⟨dd x, (mem_symmetricSubalgebra _).mpr (hsym x)⟩
            map_add' := fun x y => Subtype.ext (hadd x y)
            map_smul' := fun c x => Subtype.ext ?_ }, fun x => rfl⟩
  simp only [RingHom.id_apply, Subalgebra.smul_def, SetLike.val_smul]
  exact hmul _ _ ((mem_symmetricSubalgebra _).mp c.2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualExp
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem dual_symm {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) : IsDual b a := by
  intro w
  have h2 := congrArg (rename ⇑w) (h w⁻¹)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rename_rename] at h2
  have hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id := by
    funext k
    simp
  simp only [hc, rename_id, AlgHom.id_apply] at h2
  simp_rw [mul_comm (b _)]
  rw [h2]
  by_cases hw : w = 1
  · subst hw
    simp
  · have hw' : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
    simp [hw, hw']

private theorem dual_exp {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) (x : MvPolynomial (Fin n) R) :
    ∑ i, a i * dd (b i * x) = x := by
  obtain ⟨hD, -, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  apply mul_left_cancel₀ hD
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) =
      Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x) := by
    intro y
    rw [← h y, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_assoc]
  rw [Finset.sum_congr rfl fun y _ => key y]
  simp

theorem UpperTheory.V.AlgebraTools.hkDualExp :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) R), IsDual a b →
      ∀ x, ∑ i, a i * dd (b i * x) = x ∧ ∑ i, b i * dd (a i * x) = x := by
  intro R _ _ n ι _ a b h x
  exact ⟨dual_exp h x, dual_exp (dual_symm h) x⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkInd :
    ∀ (n : ℕ) (p : Perm (Fin n) → Prop), p 1 →
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c → p w → p (swap a c * w)) → ∀ w, p w := by
  intro n p h1 hstep
  obtain ⟨hA, hB, -, -, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have red : ∀ w : Perm (Fin n), w ≠ 1 → ∃ w', invN w = invN w' + 1 ∧ (p w' → p w) := by
    intro w hw
    obtain ⟨a, c, hac, hlt⟩ := hB w hw
    have hlt' : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
      rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_right]
      exact hlt
    have hw' : swap a c * (swap a c * w) = w := swap_mul_self_mul a c w
    refine ⟨swap a c * w, ?_, fun hp => ?_⟩
    · have := (hA a c hac _ hlt').2.2
      rwa [hw'] at this
    · have := hstep a c hac _ hlt' hp
      rwa [hw'] at this
  have key : ∀ k, ∀ w : Perm (Fin n), invN w = k → p w := by
    intro k
    induction k with
    | zero =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, -⟩ := red w h
        exfalso
        omega
    | succ k ih =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, hp⟩ := red w h
        exact hp (ih w' (by omega))
  exact fun w => key _ w rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Imports
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_diag :
    ∀ (F : Filter ℕ), F ≤ atTop → ∀ P : ℕ → ℕ → Prop, (∀ j, ∀ᶠ N in F, P j N) →
      ∃ ν : ℕ → ℕ, Tendsto ν F atTop ∧ ∀ᶠ N in F, ∀ j ≤ ν N, P j N := by
  classical
  intro F hF P hP
  have hall : ∀ j, ∀ᶠ N in F, ∀ i ≤ j, P i N := fun j =>
    (Filter.eventually_all_finite (Set.finite_Iic j)).2 (fun i _ => hP i)
  refine ⟨fun N => Nat.findGreatest (fun j => ∀ i ≤ j, P i N) N, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro j
    filter_upwards [hall j, hF (eventually_ge_atTop j)] with N h1 h2
    exact Nat.le_findGreatest (P := fun j => ∀ i ≤ j, P i N) h2 h1
  · filter_upwards [hall 0] with N h1
    exact Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, P i N) (Nat.zero_le N) h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IrredIffSpan
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem irreducible_of_span_eq_top {K G ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (f : G → Matrix ι ι K) (h : Submodule.span K (Set.range f) = ⊤) (N : Submodule K (ι → K))
    (hN : ∀ g, ∀ v ∈ N, (f g).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top f h N hN

private theorem span_map_ringHom_eq_top {k K G ι : Type} [Field k] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : k →+* K) (f : G → Matrix ι ι k) (h : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span K (Set.range fun g => (f g).map φ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top φ f h

theorem UpperTheory.V.AlgebraTools.irred_iff_span :
    ∀ {k K G : Type} [Field k] [IsAlgClosed k] [Field K] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : k →+* K) (ρ : G →* Matrix ι ι k), ((∀ N : Submodule k (ι → k), (∀ g, ∀ v ∈ N, (ρ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span k (Set.range ρ) = ⊤) ∧ (Submodule.span k (Set.range ρ) = ⊤ ↔ Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤) ∧ (Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤ → ∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ((ρ g).map φ).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) := by
  intro k K G _ _ _ _ ι _ _ φ ρ
  refine ⟨⟨KStar.Schema.span_eq_top_of_irreducible ρ, fun h N hN => irreducible_of_span_eq_top ρ h N hN⟩,
    ⟨span_map_ringHom_eq_top φ ρ, fun h => ?_⟩, fun h N hN => irreducible_of_span_eq_top _ h N hN⟩
  refine KStar.Schema.span_eq_top_of_residue φ ?_ _ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp φ.injective
  · rw [← Set.range_comp]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem ker_map_power_series_quotient (R : Type) [CommRing R] (a : Ideal R) (ha : a.FG) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) := by
  classical
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨s, rfl⟩ := ha
    have hc : ∀ n, PowerSeries.coeff n f ∈ Ideal.span (s : Set R) := by
      intro n
      have := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have hc' : ∀ n, ∃ c : R → R, ∑ x ∈ s, c x * x = PowerSeries.coeff n f := by
      intro n
      obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hc n)
      exact ⟨c, by simpa [smul_eq_mul] using hc⟩
    choose c hc' using hc'
    have : f = ∑ x ∈ s, PowerSeries.mk (fun n => c n x) * PowerSeries.C x := by
      ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc' n]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mk]
    rw [this]
    refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

theorem UpperTheory.V.AlgebraTools.powerSeries_ker_map :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG →
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) ∧
      Function.Surjective (PowerSeries.map (Ideal.Quotient.mk a)) ∧
      (a.IsPrime → (a.map (PowerSeries.C : R →+* PowerSeries R)).IsPrime) ∧
      (a.map (PowerSeries.C : R →+* PowerSeries R)).comap (PowerSeries.C : R →+* PowerSeries R) = a := by
  intro R _ a ha
  have hk := ker_map_power_series_quotient R a ha
  refine ⟨hk, ?_, ?_, ?_⟩
  · intro g
    choose c hc using fun n => Ideal.Quotient.mk_surjective (I := a) (PowerSeries.coeff n g)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]
  · intro hp
    rw [← hk]
    exact RingHom.ker_isPrime _
  · rw [← hk]
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact PowerSeries.C_injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OneAddPowSubOneMem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.prime_pow_dvd_choose (l : ℕ) (hl : l.Prime) (e j s : ℕ) (hj : j ≤ e)
    (hs : s + 1 < l ^ (e - j)) : l ^ j ∣ (l ^ e).choose (s + 1) := by
  have hm : s + 1 ≤ l ^ e :=
    le_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right hl.pos (Nat.sub_le e j)))
  have hC : (l ^ e).choose (s + 1) ≠ 0 := (Nat.choose_pos hm).ne'
  have hv : (s + 1).factorization l < e - j := by
    have h1 : l ^ (s + 1).factorization l ≤ s + 1 :=
      Nat.le_of_dvd (Nat.succ_pos s) (Nat.ordProj_dvd (s + 1) l)
    exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 (lt_of_le_of_lt h1 hs)
  rw [hl.pow_dvd_iff_le_factorization hC, Nat.factorization_choose_prime_pow hl hm (Nat.succ_ne_zero s)]
  omega

theorem UpperTheory.V.AlgebraTools.one_add_pow_sub_one_mem :
    ∀ (R : Type) [CommRing R] (l : ℕ), l.Prime → ∀ (y : R) (e j k : ℕ), j ≤ e → k ≤ l ^ (e - j) →
      (1 + y) ^ l ^ e - 1 ∈ Ideal.span {y ^ k} ⊔ Ideal.span {(l : R) ^ j} := by
  intro R _ l hl y e j k hj hk
  have hN : (1 + y) ^ l ^ e - 1 =
      ∑ s ∈ Finset.range (l ^ e), y ^ (s + 1) * ((l ^ e).choose (s + 1) : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [hN]
  refine Ideal.sum_mem _ fun s _ => ?_
  by_cases hks : k ≤ s + 1
  · apply Ideal.mem_sup_left
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow y hks) _
  · apply Ideal.mem_sup_right
    rw [Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.prime_pow_dvd_choose l hl e j s hj (by omega)
    exact ⟨y ^ (s + 1) * c, by rw [hc]; push_cast; ring⟩
end

