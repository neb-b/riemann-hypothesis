module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearRelationDescendBaseField
section
namespace GlobalTheory

theorem linRelation_descend : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι]
    (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) →
    ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  intro K Ω _ _ _ ι _ V c hc hV
  obtain ⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  let b := Module.Basis.ofVectorSpace K Ω
  obtain ⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs0
    have h0 : b.repr (c s0) = 0 := Finsupp.ext h
    exact b.repr.map_eq_zero_iff.mp h0
  refine ⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩
  have h2 : ∑ s, v s • c s = 0 := by
    rw [← hV v hv]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h3 := congrArg (fun x => b.repr x j) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLowCoeffNotDvdOfCongrMul
section
open scoped BigOperators

namespace GlobalTheory

open PowerSeries


open scoped BigOperators in
open PowerSeries in
theorem _root_.GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  intro O _ _ _ ϖ hϖ D g f m₀ v nT MT hD hg hv hM hf
  classical
  have hnu : ∀ x : O, ¬ IsUnit x → ϖ ∣ x := fun x hx => by
    have hmax : x ∈ IsLocalRing.maximalIdeal O := hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
    exact hmax
  by_contra hcon
  push_neg at hcon
  have hDg : ∀ i ≤ (v + 1) * m₀, ϖ ^ (v + 1) ∣ PowerSeries.coeff i (D * g) := by
    intro i hi
    have h1 := dvd_trans (pow_dvd_pow ϖ hv) (hf i (hi.trans hM))
    have h2 := hcon i hi
    have : PowerSeries.coeff i (D * g) = PowerSeries.coeff i f - PowerSeries.coeff i (f - D * g) := by
      simp
    rw [this]
    exact dvd_sub h2 h1
  have hD' : ∃ m, m ≤ m₀ ∧ IsUnit (PowerSeries.coeff m D) := hD
  set m₁ := Nat.find hD' with hm₁
  have hm₁le : m₁ ≤ m₀ := (Nat.find_spec hD').1
  have hm₁u : IsUnit (PowerSeries.coeff m₁ D) := (Nat.find_spec hD').2
  have hlow : ∀ a < m₁, ϖ ∣ PowerSeries.coeff a D := fun a ha =>
    hnu _ fun hu => Nat.find_min hD' ha ⟨(ha.trans_le hm₁le).le, hu⟩
  have claim : ∀ j ≤ v + 1, ∀ i, i + j * m₁ ≤ (v + 1) * m₀ → ϖ ^ j ∣ PowerSeries.coeff i g := by
    intro j
    induction j with
    | zero => intro _ i _; simp
    | succ j ihj =>
      intro hj i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hsplit := (Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal (i + m₁))
          (fun p : ℕ × ℕ => PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g)
          (a := (m₁, i)) (by simp [add_comm])).symm
        rw [← PowerSeries.coeff_mul] at hsplit
        have hrest : ϖ ^ (j + 1) ∣ ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + m₁)).erase (m₁, i),
            PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g := by
          apply Finset.dvd_sum
          rintro ⟨a, b⟩ hp
          simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
          obtain ⟨hne, hab⟩ := hp
          rcases lt_trichotomy a m₁ with h | h | h
          · rw [pow_succ, mul_comm (ϖ ^ j)]
            exact mul_dvd_mul (hlow a h) (ihj (by omega) b (by nlinarith))
          · exact absurd ⟨h, by omega⟩ hne
          · exact dvd_mul_of_dvd_right (ihi b (by omega) (by nlinarith)) _
        have htot : ϖ ^ (j + 1) ∣ PowerSeries.coeff (i + m₁) (D * g) :=
          dvd_trans (pow_dvd_pow ϖ hj) (hDg _ (by nlinarith))
        rw [hsplit] at htot
        have := (dvd_add_left hrest).1 htot
        exact (hm₁u.dvd_mul_left).1 this
  exact hg (by simpa using claim (v + 1) le_rfl 0 (by simpa using Nat.mul_le_mul_left (v + 1) hm₁le))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicAevalEqZero
section
universe u_1

namespace GlobalTheory.IntegralTrace

open Polynomial

theorem exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm

theorem isIntegral_trace {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by
  obtain ⟨p, hp, hp0⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  let K := AlgebraicClosure E
  let N : Matrix (Fin n) (Fin n) K := (algebraMap E K).mapMatrix M
  have hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M
      (p.map (algebraMap (NumberField.RingOfIntegers E) E))
    rw [hp0, map_zero] at h1
    rw [IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map,
      aeval_map_algebraMap]
    exact h1
  rw [← isIntegral_algebraMap_iff (B := K)]
  have htr : algebraMap E K M.trace = N.trace := by
    simp [N, Matrix.trace]
  rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro z hz
  have hz1 : z ∈ spectrum K N := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz
  have hz2 := spectrum.subset_polynomial_aeval N
    (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩
  rw [hN] at hz2
  have hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    by_contra h
    rw [spectrum.mem_iff] at hz2
    apply hz2
    rw [sub_zero]
    exact (IsUnit.mk0 _ h).map _
  have hz4 : IsIntegral (NumberField.RingOfIntegers E) z := ⟨p, hp, by rwa [eval_map] at hz3⟩
  exact isIntegral_trans z hz4

end GlobalTheory.IntegralTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialsSpan
section
open scoped BigOperators
open Polynomial

namespace GlobalTheory.SplittingAlgebra

theorem exists_monomials_span (t : ℕ) : ∃ e : Fin t.factorial → Fin t → ℕ,
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : Fin t → A),
      (∏ c, (X - C (y c))) ∈ Polynomial.lifts (algebraMap R A) →
      ∀ a ∈ Algebra.adjoin R (Set.range y),
        ∃ cf : Fin t.factorial → R, a = ∑ k, cf k • ∏ c, y c ^ e k c := by
  induction t with
  | zero =>
    refine ⟨fun _ _ => 0, fun R A _ _ _ y _ a ha => ?_⟩
    rw [Set.range_eq_empty, Algebra.adjoin_empty, Algebra.mem_bot] at ha
    obtain ⟨r, rfl⟩ := ha
    refine ⟨fun _ => r, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    let E : Fin (t + 1).factorial ≃ Fin (t + 1) × Fin t.factorial :=
      (finCongr (Nat.factorial_succ t)).trans finProdFinEquiv.symm
    refine ⟨fun k => Fin.cons ((E k).1 : ℕ) (e (E k).2), fun R A _ _ _ y hP a ha => ?_⟩
    have hPm : (∏ c, (X - C (y c))).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hP hPm
    have hdeg : q.natDegree ≤ t + 1 := by
      rw [hqd]
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) fun c _ => natDegree_X_sub_C_le _).trans ?_
      simp
    have hq0 : aeval (y 0) q = 0 := by
      rw [← eval_map_algebraMap, hq, Fin.prod_univ_succ]
      simp
    set R1 := Algebra.adjoin R {y 0} with hR1
    have hR1s : ∀ s ∈ R1, ∃ d : Fin (t + 1) → R, s = ∑ i, d i • y 0 ^ (i : ℕ) := by
      intro s hs
      classical
      have h1 : s ∈ Subalgebra.toSubmodule R1 := hs
      rw [hR1, ← Submodule.span_range_natDegree_eq_adjoin hqm hq0] at h1
      have h2 : s ∈ Submodule.span R (Set.range fun i : Fin (t + 1) => y 0 ^ (i : ℕ)) := by
        refine Submodule.span_mono ?_ h1
        intro z hz
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact ⟨⟨i, by omega⟩, rfl⟩
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      exact ⟨d, hd.symm⟩
    have hQ : (∏ c : Fin t, (X - C (y c.succ))) ∈ Polynomial.lifts (algebraMap R1 A) := by
      let y0 : R1 := ⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩
      refine ⟨(q.map (algebraMap R R1)) /ₘ (X - C y0), ?_⟩
      rw [coe_mapRingHom, map_divByMonic _ (monic_X_sub_C _), Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq, hq, Fin.prod_univ_succ]
      have : Polynomial.map (algebraMap R1 A) (X - C y0) = X - C (y 0) := by
        simp [y0]
      rw [this, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
    have ha' : a ∈ Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ) := by
      have : Algebra.adjoin R (Set.range y) ≤
          (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ)).restrictScalars R := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨c, rfl⟩
        refine Fin.cases ?_ (fun c => ?_) c
        · exact Subalgebra.algebraMap_mem (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ))
            (⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩ : R1)
        · exact Algebra.subset_adjoin (R := R1) (s := Set.range fun c : Fin t => y c.succ) ⟨c, rfl⟩
      exact this ha
    obtain ⟨cf, hcf⟩ := he R1 A (fun c => y c.succ) hQ a ha'
    choose d hd using fun k => hR1s (cf k) (cf k).2
    refine ⟨fun k => d (E k).2 (E k).1, ?_⟩
    rw [hcf, ← E.symm.sum_comp, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, hd k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_succ]

theorem adjoin_perm_eq_top {K : Type} [Field K] {t : ℕ} (α : Fin t → K)
    (hα : Function.Injective α) (f : Equiv.Perm (Fin t) → K) :
    f ∈ Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c)) := by
  classical
  set S := Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c))
  have h1 : ∀ σ : Equiv.Perm (Fin t), (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) ∈ S := by
    intro σ
    have : (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) =
        ∏ c, aeval (fun τ : Equiv.Perm (Fin t) => α (τ c)) (Lagrange.basis Finset.univ α (σ c)) := by
      funext τ
      rw [Finset.prod_apply]
      simp only [aeval_pi_apply₂, coe_aeval_eq_eval]
      by_cases h : τ = σ
      · subst h
        rw [Pi.single_eq_same]
        exact (Finset.prod_eq_one fun c _ =>
          Lagrange.eval_basis_self hα.injOn (Finset.mem_univ _)).symm
      · rw [Pi.single_eq_of_ne h]
        obtain ⟨c, hc⟩ : ∃ c, σ c ≠ τ c := by
          by_contra hh
          push_neg at hh
          exact h (Equiv.ext fun c => (hh c).symm)
        exact (Finset.prod_eq_zero (Finset.mem_univ c)
          (Lagrange.eval_basis_of_ne hc (Finset.mem_univ _))).symm
    rw [this]
    refine Subalgebra.prod_mem _ fun c _ => ?_
    refine Algebra.adjoin_mono ?_ (aeval_mem_adjoin_singleton K _)
    rintro _ rfl
    exact ⟨c, rfl⟩
  rw [pi_eq_sum_univ' f]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (h1 σ) _

theorem coeff_prod_apply {O I : Type} [CommRing O] {t : ℕ} (y : Fin t → I → O) (i : I) (j : ℕ) :
    (∏ c, (X - C (y c))).coeff j i = (∏ c, (X - C (y c i))).coeff j := by
  have := coeff_map (p := ∏ c, (X - C (y c))) (Pi.evalRingHom (fun _ : I => O) i) j
  rw [Polynomial.map_prod] at this
  simpa using this.symm

theorem main : ∀ {O X : Type} [CommRing O] [IsDomain O] [Finite X]
    (T : Subalgebra O (X → O)) (t : ℕ) (α : X → Fin t → O),
    (∀ x, Function.Injective (α x)) →
    (∀ x y, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    (∀ j, (fun x => (∏ c, (Polynomial.X - Polynomial.C (α x c))).coeff j) ∈ T) →
    (let T' : Subalgebra O (X × Equiv.Perm (Fin t) → O) :=
        Algebra.adjoin O ((fun f : X → O => fun x' => f x'.1) '' (T : Set (X → O)) ∪
          Set.range (fun c : Fin t => fun x' => α x'.1 (x'.2 c)))
      ∃ b : Fin t.factorial → X × Equiv.Perm (Fin t) → O,
        (∀ k, b k ∈ T') ∧ ∀ f ∈ T', ∃! cf : Fin t.factorial → T,
          f = ∑ k, (fun x' => (cf k : X → O) x'.1) * b k) := by
  intro O Y _ _ _ T t α hα _ hT T'
  obtain ⟨e, he⟩ := exists_monomials_span t
  let y : Fin t → Y × Equiv.Perm (Fin t) → O := fun c x' => α x'.1 (x'.2 c)
  refine ⟨fun k => ∏ c, y c ^ e k c, fun k => ?_, fun f hf => ?_⟩
  · have hy : ∀ c, y c ∈ T' := fun c =>
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self c))
    exact Subalgebra.prod_mem _ fun c _ => Subalgebra.pow_mem _ (hy c) _
  have hind : ∀ (x : Y) (d : Fin t.factorial → O),
      (∀ σ : Equiv.Perm (Fin t), ∑ k, d k * ∏ c, α x (σ c) ^ e k c = 0) → ∀ k, d k = 0 := by
    intro x d hd k
    let K := FractionRing O
    have hi : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
    let β : Fin t → K := fun c => algebraMap O K (α x c)
    let z : Fin t → Equiv.Perm (Fin t) → K := fun c σ => β (σ c)
    have hl : (∏ c, (X - C (z c))) ∈ Polynomial.lifts (algebraMap K (Equiv.Perm (Fin t) → K)) := by
      rw [lifts_iff_coeff_lifts]
      intro j
      refine ⟨(∏ c, (X - C (β c))).coeff j, funext fun σ => ?_⟩
      rw [coeff_prod_apply, Equiv.prod_comp σ (fun c => X - C (β c))]
      rfl
    have hli : LinearIndependent K (fun k => ∏ c, z c ^ e k c) := by
      refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun g _ => ?_) ?_
      · obtain ⟨cf, hcf⟩ := he K _ z hl g (adjoin_perm_eq_top β (hi.comp (hα x)) g)
        exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨cf, hcf.symm⟩
      · simp [Fintype.card_perm]
    have := Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) (by
      funext σ
      have := congrArg (algebraMap O K) (hd σ)
      simpa [z, β, Finset.sum_apply, Finset.prod_apply, Algebra.smul_def] using this) k
    exact hi (by simpa using this)
  let φ : T →+* (Y × Equiv.Perm (Fin t) → O) :=
    Pi.ringHom fun x' => (Pi.evalRingHom (fun _ : Y => O) x'.1).comp T.val.toRingHom
  letI : Algebra T (Y × Equiv.Perm (Fin t) → O) := φ.toAlgebra
  have hl : (∏ c, (X - C (y c))) ∈
      Polynomial.lifts (algebraMap T (Y × Equiv.Perm (Fin t) → O)) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    refine ⟨⟨_, hT j⟩, funext fun x' => ?_⟩
    rw [coeff_prod_apply, Equiv.prod_comp x'.2 (fun c => X - C (α x'.1 c))]
    rfl
  have hf' : f ∈ Algebra.adjoin T (Set.range y) := by
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      rcases hg with ⟨g, hg, rfl⟩ | hg
      · exact Subalgebra.algebraMap_mem _ (⟨g, hg⟩ : T)
      · exact Algebra.subset_adjoin hg
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O T r)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨cf, hcf⟩ := he T _ y hl f hf'
  refine ⟨cf, hcf, fun cg hcg => ?_⟩
  funext k
  ext x
  refine sub_eq_zero.1 (hind x (fun k => (cg k : Y → O) x - (cf k : Y → O) x) (fun σ => ?_) k)
  have h1 : f = ∑ k, (fun x' => (cf k : Y → O) x'.1) * ∏ c, y c ^ e k c := hcf
  have h2 := congrFun (hcg.symm.trans h1) (x, σ)
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, y] at h2
  simp only [sub_mul, Finset.sum_sub_distrib, h2, sub_self]

end GlobalTheory.SplittingAlgebra
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotMemMulValuationLeOneOfNe
section
open IsDedekindDomain NumberField

namespace GlobalTheory

theorem exists_notMem_mul_valuation_le_one_of_ne : ∀ {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (𝓞 F)) {ι : Type} [Finite ι] (x : ι → F), ∃ s : 𝓞 F, s ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ≠ p → ∀ i, q.valuation F ((s : F) * x i) ≤ 1 := by
  intro F _ _ p ι _ x
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) x
  have hc : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJp : ¬ J ≤ p.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨s, hsp, fun q hq i => ?_⟩
  have hpow : ¬ p.asIdeal ^ multiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) ≤ q.asIdeal := by
    intro h
    have h1 : p.asIdeal ≤ q.asIdeal := q.isPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hpow
  have hts : t * s ∈ Ideal.span {(b : 𝓞 F)} := by
    rw [hJ]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hts
  obtain ⟨a, ha⟩ := hb i
  replace ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F (b : 𝓞 F) * x i := by
    rw [ha]; exact Algebra.smul_def _ _
  have key : algebraMap (𝓞 F) F t * ((s : F) * x i) = algebraMap (𝓞 F) F (u * a) := by
    rw [map_mul, ha, RingOfIntegers.coe_eq_algebraMap, ← mul_assoc, ← map_mul, hu, map_mul]
    ring
  have h1 : q.valuation F (algebraMap (𝓞 F) F t) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := F) (r := t)).2 htq
  have h2 : q.valuation F (algebraMap (𝓞 F) F (u * a)) ≤ 1 := q.valuation_le_one (K := F) _
  rw [← key, map_mul, h1, one_mul] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalProjectionFinite
section
namespace GlobalTheory.OrthogonalProjection

open Module

theorem exists_orthogonal_projection_finite {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  classical
  let b : Basis (Fin (finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ) :=
    LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)
  have key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0 := by
    intro w hw z hz
    have h0 : (B.flip w).comp M.subtype = 0 := by
      apply b.ext
      intro i
      simpa using hw i
    have := LinearMap.congr_fun h0 ⟨z, hz⟩
    simpa using this
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h1 : ∀ i, B (b i : W) (m : W) = 0 := by
      intro i
      have := congr_fun hm i
      simpa [T] using this
    have h2 := key m h1 m m.2
    exact Subtype.ext (hB _ h2)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : W) v)
  refine ⟨m, m.2, ?_⟩
  apply key
  intro i
  have := congr_fun hm i
  simp [T] at this
  simp [map_sub, this]

theorem exists_orth_proj : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by
  intro W _ _ B hB M _ v
  exact exists_orthogonal_projection_finite B hB M v

end GlobalTheory.OrthogonalProjection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowOfMulSelfEqZero
section
namespace GlobalTheory.OneAddPowSquareZero

theorem one_add_pow_of_mul_self_eq_zero :
    ∀ {S : Type} [inst : Ring S] (X : S), X * X = (0 : S) →
      ∀ (N : ℕ), ((1 : S) + X) ^ N = (1 : S) + (↑N : S) * X := by
  intro S _ X hX N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, add_mul, one_mul, mul_assoc, hX,
      mul_zero, add_zero, add_mul, one_mul, add_assoc]

end GlobalTheory.OneAddPowSquareZero
end

