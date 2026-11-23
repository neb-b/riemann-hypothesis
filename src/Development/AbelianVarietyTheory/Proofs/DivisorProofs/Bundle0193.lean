module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_generic_jacobian_data_of_prime (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ]
    (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime] (hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) :
    ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ),
      g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
      (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  classical
  obtain ⟨h, f, g, hgQ, hfQ, hgen, -, hmin⟩ := _root_.GlobalTheory.exists_minimal_local_generators (MvPolynomial σ Λ) Q

  set φ : MvPolynomial σ Λ →+* FractionRing (MvPolynomial σ Λ ⧸ Q) :=
    (algebraMap (MvPolynomial σ Λ ⧸ Q) (FractionRing (MvPolynomial σ Λ ⧸ Q))).comp
      (Ideal.Quotient.mk Q) with hφ
  have hφker : ∀ x, φ x = 0 ↔ x ∈ Q := by
    intro x
    rw [hφ, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective _ _)

  have hind : ∀ a : Fin h → FractionRing (MvPolynomial σ Λ ⧸ Q),
      (∀ t, ∑ j, a j * φ (MvPolynomial.pderiv t (f j)) = 0) → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial σ Λ ⧸ Q)) a
    choose c hc using fun j => RingHom.mem_rangeS.mp (hb j)
    choose a' ha' using fun j => Ideal.Quotient.mk_surjective (c j)
    have hφa : ∀ j, φ (a' j) =
        algebraMap _ (FractionRing (MvPolynomial σ Λ ⧸ Q)) (b : MvPolynomial σ Λ ⧸ Q) * a j := by
      intro j
      rw [hφ, RingHom.comp_apply, ha', hc, Algebra.smul_def]
    have hx : ∑ j, a' j * f j ∈ Q := Q.sum_mem fun j _ => Q.mul_mem_left _ (hfQ j)
    have hpd : ∀ t, MvPolynomial.pderiv t (∑ j, a' j * f j) ∈ Q := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
      refine Q.add_mem ?_ (Q.sum_mem fun j _ => Q.mul_mem_right _ (hfQ j))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hφker, map_sum]
      simp only [map_mul, hφa, mul_assoc, ← Finset.mul_sum, ha t, mul_zero]
    obtain ⟨u, hu, hux⟩ := _root_.GlobalTheory.mem_sq_localization_of_pderiv_mem Λ σ Q hQ _ hx hpd
    have haQ := hmin a' u hu hux
    funext j
    have h1 : φ (a' j) = 0 := (hφker _).mpr (haQ j)
    rw [hφa j] at h1
    exact (mul_eq_zero.mp h1).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.exists_det_ne_zero_of_rows_separating (FractionRing (MvPolynomial σ Λ ⧸ Q)) σ h
    (fun t j => φ (MvPolynomial.pderiv t (f j))) hind
  refine ⟨h, f, s, g, hgQ, hfQ, hgen, fun hdet => hs ?_⟩
  have hmat : (Matrix.of fun i j => φ (MvPolynomial.pderiv (s i) (f j))) =
      φ.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)) := by
    ext i j
    simp
  rw [hmat, ← RingHom.map_det, hφker]
  exact hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeightOneValuationsControlSubgroup
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HtVal

theorem dvr_val (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (K : Type) [Field K]
    [Algebra S K] [IsFractionRing S K] :
    ∃ w : Kˣ →* Multiplicative ℤ, ∀ x : Kˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔ (x : K) ∈ (algebraMap S K).range := by
  let v0 : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  refine ⟨(WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹, fun x => ?_⟩
  have key : 0 ≤ Multiplicative.toAdd ((WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹ x) ↔ v0.valuation K x ≤ 1 := by
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, toAdd_inv, Left.nonneg_neg_iff]
    generalize hu : WithZero.unitsWithZeroEquiv.toMonoidHom
      ((Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom) x) = u
    have hc : v0.valuation K x = (u : WithZero (Multiplicative ℤ)) := by
      rw [← hu, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
      rfl
    rw [hc, ← WithZero.coe_one (α := Multiplicative ℤ), WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]
  rw [key]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_
    have : v = v0 := by
      ext1
      exact IsLocalRing.eq_maximalIdeal v.isMaximal
    rw [this]; exact h
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact v0.valuation_le_one y

theorem exists_val (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (h1 : P.height = 1) :
    ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔
        ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
  obtain ⟨w, hw⟩ := dvr_val (Localization.AtPrime P) (FractionRing R)
  refine ⟨w, fun x => (hw x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨s, s.2, r, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) hrs
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at this
    rw [← this, hy, mul_comm]
  · rintro ⟨s, hs, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl), ?_⟩
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
      rintro rfl; exact hs P.zero_mem
    apply mul_left_cancel₀ hs0
    rw [← hr, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) s,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r, ← map_mul]
    congr 1
    rw [mul_comm]
    exact IsLocalization.mk'_spec (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl)

theorem val_eq_zero_of_notMem (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsPrime]
    (w : (FractionRing R)ˣ →* Multiplicative ℤ)
    (hw : ∀ x : (FractionRing R)ˣ, 0 ≤ Multiplicative.toAdd (w x) ↔
      ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range)
    (u : (FractionRing R)ˣ) (a : R) (ha : (u : FractionRing R) = algebraMap R _ a) (haP : a ∉ P) :
    Multiplicative.toAdd (w u) = 0 := by
  have h1 : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hp : 0 ≤ Multiplicative.toAdd (w u) := (hw u).2 ⟨1, h1, a, by rw [map_one, one_mul, ha]⟩
  have hn : 0 ≤ Multiplicative.toAdd (w u⁻¹) := (hw u⁻¹).2 ⟨a, haP, 1, by
    rw [map_one, ← ha, Units.mul_inv]⟩
  rw [map_inv, toAdd_inv] at hn
  omega

theorem exists_vals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  intro R _ _ _ _ J _ g
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
        0 ≤ Multiplicative.toAdd (w x) ↔
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range :=
    fun P _ h1 => exists_val R P h1
  choose W hW using key
  have hsurj := fun j => IsLocalization.surj (nonZeroDivisors R) (g j : FractionRing R)
  choose nd hnd using hsurj
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hd0 : ∀ j, ((nd j).2 : R) ≠ 0 := fun j => nonZeroDivisors.coe_ne_zero _
  have hn0 : ∀ j, (nd j).1 ≠ 0 := by
    intro j h
    have := hnd j
    rw [h, map_zero] at this
    exact (mul_ne_zero (g j).ne_zero ((map_ne_zero_iff _ hinj).2 (hd0 j))) this
  have hc0 : (∏ j, (nd j).1 * ((nd j).2 : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hn0 j) (hd0 j)
  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one hc0
  let T := hfin.toFinset
  let e := T.equivFin.symm
  have hmemT : ∀ i : Fin T.card, (e i : Ideal R).IsPrime ∧ (e i : Ideal R).height = 1 ∧
      (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ (e i : Ideal R) := fun i => hfin.mem_toFinset.1 (e i).2
  refine ⟨T.card, fun i => W (e i) (hmemT i).1 (hmemT i).2.1, ?_, ?_⟩
  · intro i x r hx
    refine (hW _ _ _ x).2 ⟨1, fun h => (hmemT i).1.ne_top ((Ideal.eq_top_iff_one _).2 h), r, ?_⟩
    rw [map_one, one_mul, hx]
  · intro x hx hv
    refine (fun h => ⟨h.choose, h.choose_spec.symm⟩)
      (ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (x : FractionRing R) ?_)
    intro P hP h1
    by_cases hcP : (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ P
    · obtain ⟨i, hi⟩ := e.surjective ⟨P, hfin.mem_toFinset.2 ⟨hP, h1, hcP⟩⟩
      have gen : ∀ (Q : Ideal R) (hQ : Q.IsPrime) (hQ1 : Q.height = 1), Q = P →
          0 ≤ Multiplicative.toAdd (W Q hQ hQ1 x) →
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
        rintro Q hQ hQ1 rfl h
        exact (hW Q hQ hQ1 x).1 h
      exact gen _ _ _ (congrArg Subtype.val hi) (hv i)
    · have hnP : ∀ j, (nd j).1 ∉ P ∧ ((nd j).2 : R) ∉ P := by
        intro j
        obtain ⟨k, hk⟩ : (nd j).1 * ((nd j).2 : R) ∣ ∏ j, (nd j).1 * ((nd j).2 : R) :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        refine ⟨fun h => hcP ?_, fun h => hcP ?_⟩
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_right _ h)
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_left _ h)
      have hker : Subgroup.closure (Set.range g) ≤ (W P hP h1).ker := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        let un : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ (nd j).1) ((map_ne_zero_iff _ hinj).2 (hn0 j))
        let ud : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ ((nd j).2 : R)) ((map_ne_zero_iff _ hinj).2 (hd0 j))
        have hgu : g j = un * ud⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact Units.ext (hnd j)
        have hn := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) un _ rfl (hnP j).1
        have hd := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) ud _ rfl (hnP j).2
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hgu, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hn, hd, toAdd_one]
        simp
      have h0 : W P hP h1 x = 1 := hker hx
      exact (hW P hP h1 x).1 (by rw [h0, toAdd_one])

end GlobalTheory.HtVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHeckeEigensystemDeligneSerre
section
open Matrix

namespace GlobalTheory.DeligneSerre

theorem eq_top_of_isUnit_det (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by
  set f := (σ p).charpoly with hf
  have hq : Polynomial.aeval p f ∈ m := by
    apply hker
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
  have h0 : algebraMap O R (f.coeff 0) ∈ m := by
    have h := hq
    rw [← Polynomial.X_mul_divX_add f, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (Submodule.add_mem_iff_right m (m.mul_mem_right _ hp)).1 h
  have hc : IsUnit (f.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hu
    exact isUnit_of_mul_isUnit_right hu
  exact Ideal.eq_top_of_isUnit_mem m h0 (hc.map _)

theorem eigen_ringHom (R : Type) [CommRing R] (K : Type) [Field K] (n : ℕ)
    (τ : R →+* Matrix (Fin n) (Fin n) K) (c : Fin n → K) (hc : c ≠ 0)
    (h : ∀ p, ∃ μ : K, τ p *ᵥ c = μ • c) : ∃ χ : R →+* K, ∀ p, τ p *ᵥ c = χ p • c := by
  choose μ hμ using h
  have inj : ∀ a b : K, a • c = b • c → a = b := fun a b h => smul_left_injective K hc h
  refine ⟨{ toFun := μ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hμ⟩
  · apply inj; rw [← hμ, map_one, one_mulVec, one_smul]
  · intro a b; apply inj
    rw [← hμ, map_mul, ← mulVec_mulVec, hμ b, mulVec_smul, hμ a, smul_smul, mul_comm (μ b)]
  · apply inj; rw [← hμ, map_zero, zero_mulVec, zero_smul]
  · intro a b; apply inj; rw [← hμ, map_add (f := _), add_mulVec, hμ a, hμ b, add_smul]

theorem norm_det_eq_one (K : Type) [NormedField K] [IsAlgClosed K] (n : ℕ)
    (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ μ : K, (∃ c : Fin n → K, c ≠ 0 ∧ N *ᵥ c = μ • c) → ‖μ‖ = 1) : ‖N.det‖ = 1 := by
  have hroot : ∀ μ ∈ N.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    apply h
    have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
    have hr := (Polynomial.mem_roots hne).1 hμ
    rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hr
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  rw [Matrix.det_eq_prod_roots_charpoly]
  revert hroot
  generalize N.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    rw [Multiset.prod_cons, norm_mul, hs a (Multiset.mem_cons_self a s),
      ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem norm_eigen_le_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by
  first
  | (rename_i h_1 h_3; revert l h_1 O h_3 emb hle n N c μ hc hN; exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one)
  | exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one ..)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem unitBall_prime (R : Type) [CommRing R] (l : ℕ) [Fact l.Prime] (χ : R →+* PadicAlgCl l)
    (h : ∀ p, ‖χ p‖ ≤ 1) : ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 := by
  refine ⟨{ carrier := {p | ‖χ p‖ < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_,
    fun p => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  · simp
  · intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖χ c‖ * ‖χ x‖ ≤ 1 * ‖χ x‖ := by gcongr; exact h c
      _ < 1 := by simpa using hx
  · refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ ‖χ 1‖ < 1
      simp
    · intro a b hab
      show ‖χ a‖ < 1 ∨ ‖χ b‖ < 1
      have hab' : ‖χ a‖ * ‖χ b‖ < 1 := by
        have : ‖χ (a * b)‖ < 1 := hab
        simpa [map_mul, norm_mul] using this
      by_contra hno
      push_neg at hno
      have : 1 * 1 ≤ ‖χ a‖ * ‖χ b‖ := mul_le_mul hno.1 hno.2 zero_le_one (norm_nonneg _)
      linarith

theorem core (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a)
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal R) (hm : m.IsMaximal) (hker : ∀ p, σ p = 0 → p ∈ m) :
    ∃ χ : R →+* PadicAlgCl l, (∀ p, ‖χ p‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖χ p‖ < 1) ∧
      (∀ a, χ (algebraMap O R a) = emb a) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, (σ p).map emb *ᵥ c = χ p • c := by
  classical
  let τ : R →+* Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
    (emb.mapMatrix).comp (σ : R →+* Matrix (Fin n) (Fin n) O)
  have hτ : ∀ p, τ p = (σ p).map emb := fun p => rfl
  have hcomm : ∀ p q, Commute (τ p) (τ q) := fun p q => by
    show τ p * τ q = τ q * τ p
    rw [← map_mul, ← map_mul, mul_comm]
  let X : Set (R →+* PadicAlgCl l) :=
    {χ | ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, τ p *ᵥ c = χ p • c}
  have hXfin : X.Finite := by
    have h := _root_.GlobalTheory.finite_joint_eigensystems (PadicAlgCl l) n R τ hcomm
    refine Set.Finite.of_finite_image (f := fun χ : R →+* PadicAlgCl l => (χ : R → PadicAlgCl l))
      (h.subset ?_) DFunLike.coe_injective.injOn
    rintro _ ⟨χ, ⟨c, hc, hχ⟩, rfl⟩
    exact ⟨c, hc, hχ⟩
  have hXle : ∀ χ ∈ X, ∀ p, ‖χ p‖ ≤ 1 := by
    rintro χ ⟨c, hc, hχ⟩ p
    exact norm_eigen_le_one l O emb hle n (σ p) c (χ p) hc (hχ p)
  have hP : ∀ χ ∈ X, ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 :=
    fun χ hχ => unitBall_prime R l χ (hXle χ hχ)
  choose! P hPprime hPmem using hP
  have key : ∃ χ ∈ X, m ≤ P χ := by
    by_contra hno
    push_neg at hno
    obtain ⟨p, hpm, hpX⟩ : ∃ p ∈ m, ∀ χ ∈ X, ¬ ‖χ p‖ < 1 := by
      rcases X.eq_empty_or_nonempty with hX | ⟨χ0, hχ0⟩
      · exact ⟨0, m.zero_mem, by simp [hX]⟩
      · have hns : ¬ ((m : Set R) ⊆ ⋃ χ ∈ X, (P χ : Set R)) := by
          rw [Ideal.subset_union_prime_finite hXfin χ0 χ0 (fun χ hχ _ _ => hPprime χ hχ)]
          rintro ⟨χ, hχ, hle'⟩
          exact hno χ hχ hle'
        rw [Set.not_subset] at hns
        obtain ⟨p, hpm, hp⟩ := hns
        refine ⟨p, hpm, fun χ hχ hlt => hp ?_⟩
        exact Set.mem_biUnion hχ ((hPmem χ hχ p).2 hlt)
    have hdet : ‖(τ p).det‖ = 1 := by
      apply norm_det_eq_one (PadicAlgCl l) n (τ p)
      rintro μ ⟨c, hc, hcμ⟩
      let E : Submodule (PadicAlgCl l) (Fin n → PadicAlgCl l) :=
        { carrier := {v | τ p *ᵥ v = μ • v}
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_add, ha, hb, smul_add]
          zero_mem' := by simp
          smul_mem' := by
            intro a v hv
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_smul, hv, smul_comm] }
      have hcE : c ∈ E := hcμ
      have hE : E ≠ ⊥ := fun h => hc ((Submodule.mem_bot _).1 (h ▸ hcE))
      have hstab : ∀ A ∈ Set.range τ, ∀ v ∈ E, A *ᵥ v ∈ E := by
        rintro _ ⟨q, rfl⟩ v hv
        have hv' : τ p *ᵥ v = μ • v := hv
        show τ p *ᵥ (τ q *ᵥ v) = μ • (τ q *ᵥ v)
        rw [mulVec_mulVec, (hcomm p q).eq, ← mulVec_mulVec, hv', mulVec_smul]
      obtain ⟨v, hvE, hv0, hv⟩ := _root_.GlobalTheory.matrix_exists_common_eigenvector_mem (PadicAlgCl l) n (Set.range τ)
        (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hcomm a b) E hE hstab
      obtain ⟨χ, hχ⟩ := eigen_ringHom R (PadicAlgCl l) n τ v hv0 (fun q => hv (τ q) ⟨q, rfl⟩)
      have hχX : χ ∈ X := ⟨v, hv0, hχ⟩
      have hμ : χ p = μ := by
        have h1 : τ p *ᵥ v = μ • v := hvE
        exact smul_left_injective (PadicAlgCl l) hv0 ((hχ p).symm.trans h1)
      rw [← hμ]
      exact le_antisymm (hXle χ hχX p) (not_lt.1 (hpX χ hχX))
    have hdet' : ‖emb (σ p).det‖ = 1 := by
      rw [RingHom.map_det]
      exact hdet
    exact hm.ne_top (eq_top_of_isUnit_det O R n σ m hker p hpm (hunit _ hdet'))
  obtain ⟨χ, hχX, hmP⟩ := key
  have hmeq : m = P χ := hm.eq_of_le (hPprime χ hχX).ne_top hmP
  obtain ⟨c, hc, hχc⟩ := id hχX
  refine ⟨χ, hXle χ hχX, fun p => by rw [hmeq]; exact hPmem χ hχX p, ?_, c, hc, hχc⟩
  intro a
  have h1 := hχc (algebraMap O R a)
  have h2 : τ (algebraMap O R a) *ᵥ c = emb a • c := by
    rw [hτ, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero emb)]
    ext i
    simp [mulVec_diagonal]
  exact smul_left_injective (PadicAlgCl l) hc (h1.symm.trans h2)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem exists_integral_eigensystem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  intro l _ O _ _ _ emb hinj hL I M _ _ _ _ hfin htf V _ _ j Tq hli hcomp m hm hann
  obtain ⟨L, _, hL⟩ := hL
  have hmemL : ∀ a, emb a ∈ L ∧ ‖emb a‖ ≤ 1 := by
    intro a
    have h : emb a ∈ Set.range emb := ⟨a, rfl⟩
    rw [hL] at h
    exact h
  have hle : ∀ a, ‖emb a‖ ≤ 1 := fun a => (hmemL a).2
  have hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a := by
    intro a ha
    have hne : emb a ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (emb a)⁻¹ ∈ Set.range emb := by
      rw [hL]
      refine ⟨L.inv_mem (hmemL a).1, ?_⟩
      rw [norm_inv, ha, inv_one]
    obtain ⟨b, hb⟩ := hinv
    have hab : a * b = 1 := hinj (by rw [map_mul, hb, map_one, mul_inv_cancel₀ hne])
    exact IsUnit.of_mul_eq_one b hab
  obtain ⟨n, σ, e, hσ, he_inj, he_span, he_T⟩ :=
    _root_.GlobalTheory.exists_matrices_intertwining_of_semilinear l O emb I M hfin htf V j Tq hli hcomp
  obtain ⟨χ, hχle, hχm, hχalg, c, hc, hχc⟩ :=
    core l O emb hle hunit (MvPolynomial I O) n σ m hm (fun p hp => hann p (hσ p hp))
  set θ : I → PadicAlgCl l := fun i => χ (MvPolynomial.X i) with hθ
  have hext : MvPolynomial.eval₂Hom emb θ = χ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, hχalg]
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
  have heval : ∀ p, MvPolynomial.eval₂ emb θ p = χ p := fun p =>
    congrArg (fun f : MvPolynomial I O →+* PadicAlgCl l => f p) hext
  refine ⟨θ, fun i => hχle _, fun p => by rw [heval]; exact hχm p, e c, he_span c, ?_, ?_⟩
  · intro h
    exact hc (he_inj (by rw [h, map_zero]))
  · intro i
    rw [he_T, hχc, map_smul]

end GlobalTheory.DeligneSerre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEqStatement
section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A), (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  first | (exact @GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (exact GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (intros; apply GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOneStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one : ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  first | (exact @GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (exact GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (intros; apply GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one <;> assumption)
end

