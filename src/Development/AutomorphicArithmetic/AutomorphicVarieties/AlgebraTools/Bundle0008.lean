module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem finset_prod_dvd_of_prime_of_dvd_imp_eq {M ι : Type} [CommRing M] (f : ι → M) (y : M) (s : Finset ι)
    (hp : ∀ a ∈ s, Prime (f a)) (hn : ∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) (hd : ∀ a ∈ s, f a ∣ y) :
    ∏ a ∈ s, f a ∣ y :=
  _root_.UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq f y s hp hn hd

private def sb {n : ℕ} (i j : Fin n) : Fin n → Fin n := fun k => if k = j then i else k

private theorem dvd_sub_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y - rename (sb i j) y := by
  induction y using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p k hp =>
    have hk : (X j - X i : MvPolynomial (Fin n) R) ∣ X k - X (sb i j k) := by
      unfold sb
      split_ifs with h
      · rw [h]
      · simp
    have := dvd_add (hp.mul_right (X k)) (hk.mul_left (rename (sb i j) p))
    rw [map_mul, rename_X]
    convert this using 1
    ring

private theorem dvd_iff_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y ↔ rename (sb i j) y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    have : sb i j j = sb i j i := by simp [sb]
    rw [map_mul, map_sub, rename_X, rename_X, this, sub_self, zero_mul]
  · intro h
    have := dvd_sub_sb i j y
    rwa [h, sub_zero] at this

private theorem prime_sb {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Prime (X j - X i : MvPolynomial (Fin n) R) := by
  refine ⟨fun e => h.symm (X_injective (sub_eq_zero.1 e)), fun hu => ?_, fun a b hab => ?_⟩
  · have := (dvd_iff_sb i j (1 : MvPolynomial (Fin n) R)).1 hu.dvd
    simp at this
  · rw [dvd_iff_sb, map_mul, mul_eq_zero] at hab
    rwa [dvd_iff_sb, dvd_iff_sb]

private theorem alt_sb {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (x : MvPolynomial (Fin n) R) :
    rename (sb i j) (alt x) = 0 := by
  have hs : ∀ k, sb i j (swap i j k) = sb i j k := by
    intro k
    by_cases h1 : k = i
    · subst h1; simp [sb]
    · by_cases h2 : k = j
      · subst h2; simp [sb]
      · rw [swap_apply_of_ne_of_ne h1 h2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [alt, map_sum]
  refine Finset.sum_involution (fun w _ => swap i j * w) (fun w _ => ?_) (fun w _ _ e => ?_)
    (fun w _ => Finset.mem_univ _) (fun w _ => ?_)
  · have e : sb i j ∘ (swap i j * w : Perm (Fin n)) = sb i j ∘ w := funext fun k => hs _
    rw [Units.smul_def, Units.smul_def, map_zsmul, map_zsmul, rename_rename, rename_rename, e, Perm.sign_mul,
      Perm.sign_swap h]
    simp
  · have := mul_eq_right.1 e
    exact h (swap_eq_one_iff.1 this)
  · simp [← mul_assoc]

theorem UpperTheory.V.AlgebraTools.hkDdSpec :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (x : MvPolynomial (Fin n) R), De R n * dd x = alt x := by
  intro R _ _ n x
  have hlt : ∀ p ∈ pairs n, p.1 < p.2 := fun p hp => by simpa [pairs] using hp
  have hd : De R n ∣ alt x := by
    refine finset_prod_dvd_of_prime_of_dvd_imp_eq _ _ _ (fun p hp => prime_sb (hlt p hp).ne) (fun p hp q hq hpq => ?_)
      (fun p hp => (dvd_iff_sb _ _ _).2 (alt_sb (hlt p hp).ne x))
    rw [dvd_iff_sb, map_sub, rename_X, rename_X, sub_eq_zero] at hpq
    have e := X_injective hpq
    have h1 := hlt p hp
    have h2 := hlt q hq
    unfold sb at e
    split_ifs at e with a b b
    · exact absurd (b.trans a.symm) h2.ne
    · exact Prod.ext e a.symm
    · rw [e, b] at h2
      exact absurd h1 h2.not_gt
    · exact absurd e h2.ne'
  obtain ⟨y, hy⟩ := hd
  have h : ∃ y, De R n * y = alt x := ⟨y, hy.symm⟩
  rw [dd, dite_eq_left h]
  exact h.choose_spec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_coi :
    ∀ {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] (a : ι → R) (P : E), (∀ i j, i ≠ j → IsUnit (a i - a j)) → aeval P (∏ i, (X - C (a i))) = 0 → CompleteOrthogonalIdempotents (lag a P) ∧ (∀ i, P * lag a P i = a i • lag a P i) ∧ (∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i) ∧ ∀ y i, Commute y P → Commute y (lag a P i) := by
  intro R E ι _ _ _ _ _ a P ha hm
  have hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := fun i =>
    IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  let L : ι → R[X] := fun i =>
    C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))
  have hL : ∀ i, lag a P i = aeval P (L i) := by
    intro i
    simp only [L, lag, map_mul, aeval_C, Algebra.smul_def]
  have hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with h
    · subst h
      exact Ring.inverse_mul_cancel _ (hc i)
    · rw [Finset.prod_eq_zero (f := fun j => a k - a j)
        (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]
  have hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0 := by
    intro i
    rw [hL, ← map_mul]
    have : (X - C (a i)) * L i =
        C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j)) := by
      simp only [L]
      rw [mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    rw [this, map_mul, hm, mul_zero]
  have hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i := by
    intro q i
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))
    have hq' : q = g * (X - C (a i)) + C (q.eval (a i)) := by
      rw [mul_comm, ← hg]
      ring
    conv_lhs => rw [hq']
    rw [map_add (f := _), map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]
  have hP : ∀ i, P * lag a P i = a i • lag a P i := by
    intro i
    have := hq X i
    rwa [aeval_X, eval_X] at this
  have hcomm : ∀ y i, Commute y P → Commute y (lag a P i) := by
    intro y i hy
    rw [hL]
    generalize L i = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
    | monomial n c =>
      rw [aeval_monomial]
      exact Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm)
        (hy.pow_right n)
  have hsum : ∑ i, lag a P i = 1 := by
    have h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)
      · intro k _
        rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finsetSum]
        simp only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    obtain ⟨g, hg⟩ := h1
    have h2 := congrArg (aeval P) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero] at h2
    simp only [hL]
    exact h2.symm
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩
  · show lag a P i * lag a P i = lag a P i
    have := hq (L i) i
    rw [← hL, hLe, if_pos rfl, one_smul] at this
    exact this
  · have := hq (L i) j
    rw [← hL, hLe, if_neg hij, zero_smul] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaB
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.lemma_B_range {A H Q : Type} [CommRing A] [AddCommGroup H] [Module A H]
    [AddCommGroup Q] [Module A Q] (N : Submodule A H) (φ : H →ₗ[A] Q) (h : N ≤ LinearMap.ker φ) :
    Module.length A (LinearMap.range φ) ≤ Module.length A (H ⧸ N) := by
  refine Module.length_le_of_surjective (N.liftQ φ.rangeRestrict (by rwa [LinearMap.ker_rangeRestrict])) ?_
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective_rangeRestrict y
  exact ⟨N.mkQ x, rfl⟩

private theorem UpperTheory.V.AlgebraTools.lemma_B_sup {A Q : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    (P U V : Submodule A Q) (h : P ≤ U ⊔ V) :
    Module.length A P ≤ Module.length A U + Module.length A V := by
  have hsurj : Function.Surjective ((Submodule.inclusion (le_sup_left : U ≤ U ⊔ V)).coprod
      (Submodule.inclusion (le_sup_right : V ≤ U ⊔ V))) := by
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  calc Module.length A P ≤ Module.length A (U ⊔ V : Submodule A Q) :=
        Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
    _ ≤ Module.length A (U × V) := Module.length_le_of_surjective _ hsurj
    _ = Module.length A U + Module.length A V := Module.length_prod _ _ _

private theorem UpperTheory.V.AlgebraTools.lemma_B_le {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ m : ℕ, (⨅ s, (I ^ (m + c) • (⊤ : Submodule A M')).comap (f s)) ≤
      (⨅ s, LinearMap.ker (f s)) ⊔ I ^ m • (⊤ : Submodule A M) := by
  classical
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A (M →ₗ[A] M'))
    (Set.range fun T : Finset S => Submodule.span A (f '' (T : Set S))) ⟨_, ⟨∅, rfl⟩⟩
  have hspan : ∀ s, f s ∈ Submodule.span A (f '' (T : Set S)) := by
    intro s
    by_contra hs
    refine hT _ ⟨insert s T, rfl⟩ (lt_of_le_of_ne (Submodule.span_mono ?_) ?_)
    · apply Set.image_mono
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _
    · intro heq
      apply hs
      simp only at heq
      rw [heq]
      exact Submodule.subset_span ⟨s, by simp, rfl⟩
  have hker : ⨅ t : T, LinearMap.ker (f t) ≤ ⨅ s, LinearMap.ker (f s) := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro s
    have hle : Submodule.span A (f '' (T : Set S)) ≤
        LinearMap.ker (LinearMap.applyₗ (R := A) (M₂ := M') x) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      simpa using hx ⟨t, ht⟩
    simpa using hle (hspan s)
  let F : M →ₗ[A] (T → M') := LinearMap.pi fun t => f t
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I F
  refine ⟨c, fun m x hx => ?_⟩
  have hFx : F x ∈ I ^ (m + c) • (⊤ : Submodule A (T → M')) := by
    rw [← Finset.univ_sum_single (F x)]
    refine Submodule.sum_mem _ fun t _ => ?_
    have h1 : f t x ∈ I ^ (m + c) • (⊤ : Submodule A M') := by
      simpa using (Submodule.mem_iInf _).mp hx t
    simpa [F] using Submodule.smul_top_le_comap_smul_top (I ^ (m + c))
      (LinearMap.single A (fun _ : T => M') t) h1
  have hm := hc m hFx
  have hle : LinearMap.ker F ≤ ⨅ s, LinearMap.ker (f s) := by
    simp only [F, LinearMap.ker_pi]
    exact hker
  exact (sup_le_sup_right hle _) hm

theorem UpperTheory.V.AlgebraTools.lemma_B :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {M M' S : Type} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (f : S → M →ₗ[A] M'), ∃ e : ℕ, ∀ j : ℕ, Module.length A ((⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s)).map (maximalIdeal A ^ j • (⊤ : Submodule A M)).mkQ) ≤ ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A M) * j + e : ℕ) : ℕ∞) := by
  intro A _ _ _ M M' S _ _ _ _ _ _ f
  set K : Submodule A M := ⨅ s, LinearMap.ker (f s) with hKdef
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.lemma_B_le (maximalIdeal A) f
  obtain ⟨cK, -, hK⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) K
  obtain ⟨cM, -, hM⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) M
  refine ⟨cK + Module.finrank A M * c + cM, fun j => ?_⟩
  set P := ⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s) with hPdef
  set N := maximalIdeal A ^ j • (⊤ : Submodule A M) with hNdef
  have hQ : Module.length A (P.map N.mkQ) ≤ Module.length A (M ⧸ N) :=
    Module.length_le_of_injective (Submodule.subtype _) (Submodule.injective_subtype _)
  by_cases hj : j < c
  · refine le_trans hQ (le_trans (hM j).2 ?_)
    have h1 := Nat.mul_le_mul_left (Module.finrank A M) hj.le
    have h2 := Nat.zero_le (Module.finrank A K * j)
    exact_mod_cast (show Module.finrank A M * j + cM ≤
      Module.finrank A K * j + (cK + Module.finrank A M * c + cM) by omega)
  · push_neg at hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + c := ⟨j - c, by omega⟩
    have hP : P ≤ K ⊔ maximalIdeal A ^ m • ⊤ := hc m
    have hU : Module.length A (K.map N.mkQ) ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) := by
      refine le_trans ?_ (hK (m + c)).2
      have := UpperTheory.V.AlgebraTools.lemma_B_range (maximalIdeal A ^ (m + c) • (⊤ : Submodule A K))
        (N.mkQ ∘ₗ K.subtype) ?_
      · rwa [LinearMap.range_comp, Submodule.range_subtype] at this
      · intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_top_le_comap_smul_top _ K.subtype hx
    let g : (M ⧸ N) →ₗ[A] (M ⧸ (maximalIdeal A ^ m • (⊤ : Submodule A M))) :=
      N.liftQ (Submodule.mkQ _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right m c)))
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨N.mkQ x, rfl⟩
    have hV : (maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ = LinearMap.ker g := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)
    have hVb : Module.length A (LinearMap.ker g) ≤ ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
      have h1 := (hM (m + c)).2
      have h2 := (hM m).1
      rw [hlen] at h1
      have h3 : Module.length A (LinearMap.ker g) + ((Module.finrank A M * m : ℕ) : ℕ∞) ≤
          ((Module.finrank A M * (m + c) + cM : ℕ) : ℕ∞) :=
        le_trans (add_le_add le_rfl h2) h1
      have hfin : Module.length A (LinearMap.ker g) ≠ ⊤ := by
        intro htop
        rw [htop, top_add, top_le_iff] at h3
        exact ENat.coe_ne_top _ h3
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← ha] at h3 ⊢
      norm_cast at h3 ⊢
      rw [Nat.mul_add] at h3
      omega
    calc Module.length A (P.map N.mkQ)
        ≤ Module.length A (K.map N.mkQ) +
          Module.length A ((maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ) := by
          apply UpperTheory.V.AlgebraTools.lemma_B_sup
          rw [← Submodule.map_sup]
          exact Submodule.map_mono hP
      _ ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) + ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
          rw [hV]
          exact add_le_add hU hVb
      _ = _ := by
          push_cast
          ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimElt
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_elt :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      (∀ a : ι → G, ∃ b : G, ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ O.toSubgroup) ∧
      (∀ (a : ι → G) (b b' : G), (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ K i ⊔ O.toSubgroup) →
        (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b'⁻¹ * a i ∈ K i ⊔ O.toSubgroup) → b⁻¹ * b' ∈ limKer (U : Filter ι) K) := by
  intro G ι _ _ _ _ _ U K _
  refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by
      refine ⟨(U.map a).lim, ?_⟩
      have h' := (U.map a).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    refine ⟨b, fun O => ?_⟩
    have hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
    exact hl.eventually (hopen.mem_nhds (by simp))
  · rw [mem_limKer]
    intro O
    filter_upwards [hb O, hb' O] with i h1 h2
    have heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimKer
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem limKer_key {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) (O : OpenNormalSubgroup G) (x : G) :
    (∀ᶠ i in (U : Filter ι), x ∈ K i ⊔ O.toSubgroup) ↔
      x ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup := by
  haveI := O.isNormal'
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup := by
      refine h.mono fun i hi => ?_
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hi
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simpa using hz
    classical
    obtain ⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by
      refine ⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩
      refine hex.mono fun i hi => ?_
      simp only [dif_pos hi]
      exact hi.choose_spec
    obtain ⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by
      refine ⟨(U.map k).lim, ?_⟩
      have h' := (U.map k).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    have hlL : l ∈ limKer (U : Filter ι) K := by
      rw [mem_limKer]
      intro O'
      have hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup} :=
        O'.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
      filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2
      have heq : l = k i * (l⁻¹ * k i)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    have hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)
    have hlx : l⁻¹ * x ∈ O.toSubgroup := hC.mem_of_tendsto hl (hk.mono fun i h => h.2)
    have heq : x = l * (l⁻¹ * x) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)
  · intro h
    let S : Subgroup G :=
      { carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup}
        mul_mem' := fun ha hb =>
          Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2
        one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _
        inv_mem' := fun ha => Filter.Eventually.mono ha fun i hi => Subgroup.inv_mem _ hi }
    have hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S :=
      sup_le (fun g hg => (mem_limKer.1 hg) O)
        (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)
    exact hle h

theorem UpperTheory.V.AlgebraTools.limKer_sup :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      IsClosed (limKer (U : Filter ι) K : Set G) ∧
      (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup) ∧
      (∀ O : OpenNormalSubgroup G, limKer (U : Filter ι) K ≤ O.toSubgroup ↔ ∀ᶠ i in (U : Filter ι), K i ≤ O.toSubgroup) := by
  intro G ι _ _ _ _ _ U K _
  have h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι),
      K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup := by
    intro O
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup})
      (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
    have hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T,
        (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup) := by
      refine (Filter.eventually_all_finset T).2 (fun t _ => ?_)
      by_cases ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup
      · exact ((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht
      · have hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup :=
          fun h => ht ((limKer_key U K O t).1 h)
        exact (Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht
    filter_upwards [hev] with i hi
    ext g
    obtain ⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by
      have := hT (Set.mem_univ g)
      simp only [Set.mem_iUnion] at this
      obtain ⟨t, htT, hgt⟩ := this
      exact ⟨t, htT, hgt⟩
    have mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M) := by
      intro M hM
      have hg : g = t * (t⁻¹ * g) := by group
      rw [hg]
      exact mul_mem_cancel_right (hM hgt)
    rw [mem_iff _ le_sup_right, mem_iff _ le_sup_right]
    exact hi t htT
  have hclosed : IsClosed (limKer (U : Filter ι) K : Set G) := by
    have hset : (limKer (U : Filter ι) K : Set G) =
        ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter]
      constructor
      · intro hx O
        exact Subgroup.mem_sup_left hx
      · intro hx
        rw [mem_limKer]
        intro O
        exact (limKer_key U K O x).2 (hx O)
    rw [hset]
    exact isClosed_iInter fun O =>
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)
  refine ⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩
  · filter_upwards [h2 O] with i hi
    rw [sup_eq_right.2 h] at hi
    exact sup_eq_right.1 hi
  · intro x hx
    obtain ⟨i, hi1, hi2⟩ := ((mem_limKer.1 hx O).and h).exists
    exact (sup_le hi2 le_rfl) hi1
end

