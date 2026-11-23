module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSigmaSpecPointsCoproduct
section
open AlgebraicGeometry CategoryTheory Limits

theorem UpperTheory.bijective_sigma_spec_points_coproduct :
    ∀ {I : Type} (Z : I → Scheme.{0}) (K : Type) [Field K], Function.Bijective (fun p : (Σ c, (Spec (CommRingCat.of K) ⟶ Z c)) => p.2 ≫ Sigma.ι Z p.1) := by
  intro I Z K _
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  constructor
  · rintro ⟨c, f⟩ ⟨c', f'⟩ h
    simp only at h
    have hz : (Sigma.ι Z c) (f z) = (Sigma.ι Z c') (f' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
    have hs := (sigmaι_eq_iff Z c c' (f z) (f' z)).mp hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj hs
    have hff : f = f' := (cancel_mono (Sigma.ι Z c)).mp h
    rw [hff]
  · intro f
    obtain ⟨⟨c, y⟩, hy⟩ := (sigmaMk Z).surjective (f z)
    rw [sigmaMk_mk] at hy
    have H : Set.range f ⊆ Set.range (Sigma.ι Z c) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨y, by rw [hy, Subsingleton.elim w z]⟩
    exact ⟨⟨c, IsOpenImmersion.lift (Sigma.ι Z c) f H⟩, IsOpenImmersion.lift_fac _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.DvdExponentOfPowEqLaurentMonomial
section
theorem UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O] [IsLocalRing O] (c : ℕ) (v : (LaurentPolynomial O)ˣ), (v : LaurentPolynomial O) ^ q = LaurentPolynomial.T (c : ℤ) → q ∣ c := by
  intro q _ O _ _ c v hv
  classical
  let φ : LaurentPolynomial O →+* LaurentPolynomial (IsLocalRing.ResidueField O) :=
    AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O)
  have hT : ∀ n : ℤ, φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    show AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) (AddMonoidAlgebra.single n 1) =
      AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hw : (φ v) ^ q = LaurentPolynomial.T (c : ℤ) := by
    rw [← map_pow, hv, hT]
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (φ v)
  have hpq : p ^ q = Polynomial.X ^ (c + q * n) := by
    apply Polynomial.toLaurent_injective
    rw [map_pow, hp, mul_pow, hw, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add,
      Polynomial.toLaurent_X_pow]
    congr 1
  have hdeg := congrArg Polynomial.natDegree hpq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdeg
  have h1 : q ∣ q * n + c := ⟨p.natDegree, by rw [add_comm]; exact hdeg.symm⟩
  exact (Nat.dvd_add_right (dvd_mul_right q n)).mp h1
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapDualBasisOfParameters
section
open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_dual_basis_of_parameters :
    ∀ {R : Type} [CommRing R] [Algebra ℂ R] (ev : R →ₐ[ℂ] ℂ) {d : ℕ} (t : Fin d → R) (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev b • ψ ω) → Function.Surjective ψ → (∀ l, ev (t l) = 0) → (∀ u : R, ev u = 0 → ∃ (c : R) (g : Fin d → R), ev c ≠ 0 ∧ c * u = ∑ l, g l * t l) → ∃ φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), φ (b • ω) = ev b • φ ω) ∧ (∀ l, φ (D ℂ R (t l)) = Pi.single l 1) ∧ (∀ ω, φ ω = 0 → ψ ω = 0) ∧ ∀ (u c : R) (g : Fin d → R), ev u = 0 → ev c ≠ 0 → c * u = ∑ l, g l * t l → ∀ l, ev (g l) = ev c * φ (D ℂ R u) l := by
  intro R _ _ ev d t ψ hψ hsurj ht hloc
  have key : ∀ χ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), χ (b • ω) = ev b • χ ω) →
      ∀ (u c : R) (g : Fin d → R), ev u = 0 → c * u = ∑ l, g l * t l →
      ev c • χ (D ℂ R u) = ∑ l, ev (g l) • χ (D ℂ R (t l)) := by
    intro χ hχ u c g hu hcu
    have h := congrArg (fun x => χ (D ℂ R x)) hcu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Derivation.leibniz, map_sum, map_add (f := _), hχ, hu, ht, zero_smul, add_zero] at h
    exact h
  set v : Fin d → (Fin d → ℂ) := fun l => ψ (D ℂ R (t l)) with hvdef
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro y hy
    clear hy
    obtain ⟨ω, rfl⟩ := hsurj y
    have hω : ω ∈ Submodule.span R (Set.range (D ℂ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      set u' := u - algebraMap ℂ R (ev u) with hu'
      have hDu : D ℂ R u = D ℂ R u' := by
        rw [hu', map_sub, Derivation.map_algebraMap, sub_zero]
      have hev : ev u' = 0 := by
        rw [hu', map_sub, AlgHom.commutes]
        simp
      obtain ⟨c, g, hc, hcu⟩ := hloc u' hev
      have h := key ψ hψ u' c g hev hcu
      rw [hDu]
      have : ψ (D ℂ R u') = (ev c)⁻¹ • ∑ l, ev (g l) • v l := by
        rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro l _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [hψ]
      exact Submodule.smul_mem _ _ hx
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  set bs := Module.Basis.mk hli hspan with hbs
  have hbv : ∀ l, ψ (D ℂ R (t l)) = bs l := by
    intro l
    rw [hbs, Module.Basis.mk_apply]
  have h2 : ∀ l, (bs.equivFun.toLinearMap ∘ₗ ψ) (D ℂ R (t l)) = Pi.single l 1 := by
    intro l
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hbv]
    ext j
    rw [Module.Basis.equivFun_self]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Pi.single_apply, Ne.symm hlj]
  refine ⟨bs.equivFun.toLinearMap ∘ₗ ψ, ?_, h2, ?_, ?_⟩
  · intro b ω
    simp [hψ]
  · intro ω hω
    simpa using hω
  · intro u c g hu hc hcu l
    have h := key (bs.equivFun.toLinearMap ∘ₗ ψ) (by intro b ω; simp [hψ]) u c g hu hcu
    simp only [h2] at h
    have h3 := congrFun h l
    simp [Finset.sum_apply, Pi.single_apply] at h3
    rw [← h3]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapLocalizationAway
section
open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_localization_away :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S] (f : R) [IsLocalization.Away f S] (ev : S →+* ℂ) {d : ℕ} (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev (algebraMap R S b) • ψ ω) → (∀ ω : Ω[R⁄ℂ], ψ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]), (∀ i, ev (algebraMap R S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ ψ' : Ω[S⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : S) (ω : Ω[S⁄ℂ]), ψ' (b • ω) = ev b • ψ' ω) ∧ (∀ ω : Ω[R⁄ℂ], ψ' (KaehlerDifferential.map ℂ ℂ R S ω) = ψ ω) ∧ (∀ ω : Ω[S⁄ℂ], ψ' ω = 0 → ∃ (m : ℕ) (b : Fin m → S) (ω' : Fin m → Ω[S⁄ℂ]), (∀ i, ev (b i) = 0) ∧ ω = ∑ i, b i • ω' i) := by
  intro R S _ _ _ _ _ _ f _ ev d ψ h1 h2
  letI : Module R (Fin d → ℂ) := Module.compHom (Fin d → ℂ) (ev.comp (algebraMap R S))
  have hu : ∀ x : Submonoid.powers f, ev (algebraMap R S x) ≠ 0 := fun x =>
    ((IsLocalization.map_units S x).map ev).ne_zero
  have hunit : ∀ x : Submonoid.powers f,
      IsUnit ((algebraMap R (Module.End R (Fin d → ℂ))) x) := by
    intro x
    rw [Module.End.isUnit_iff]
    refine ⟨fun v w hvw => smul_right_injective (Fin d → ℂ) (hu x) hvw,
      fun v => ⟨(ev (algebraMap R S x))⁻¹ • v, ?_⟩⟩
    show ev (algebraMap R S x) • ((ev (algebraMap R S x))⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (hu x), one_smul]
  let g : Ω[R⁄ℂ] →ₗ[R] (Fin d → ℂ) :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun b ω => h1 b ω }
  let L := IsLocalizedModule.lift (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) g hunit
  have hL : ∀ η, L (KaehlerDifferential.map ℂ ℂ R S η) = ψ η := fun η =>
    IsLocalizedModule.lift_apply _ _ _ _ η
  have hLs : ∀ (r : R) (ω : Ω[S⁄ℂ]), L (r • ω) = ev (algebraMap R S r) • L ω :=
    fun r ω => L.map_smul r ω
  have hLS : ∀ (b : S) (ω : Ω[S⁄ℂ]), L (b • ω) = ev b • L ω := by
    intro b ω
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers f) b
    have h := hLs (t : R) (b • ω)
    rw [← algebraMap_smul S (t : R) (b • ω), smul_smul, mul_comm, ht, algebraMap_smul, hLs] at h
    apply smul_right_injective (Fin d → ℂ) (hu t)
    show ev (algebraMap R S t) • L (b • ω) = ev (algebraMap R S t) • ev b • L ω
    rw [← h, ← ht, map_mul, mul_comm, mul_smul]
  have hLC : ∀ (c : ℂ) (ω : Ω[S⁄ℂ]), L (c • ω) = c • L ω := by
    intro c ω
    obtain ⟨⟨η, s⟩, hs⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
    have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
    have e1 : ev (algebraMap R S s) • L ω = ψ η := by rw [← hLs, hs', hL]
    have e2 : ev (algebraMap ℂ S c) • ψ η = c • ψ η := by
      rw [show c • ψ η = ψ (c • η) from (ψ.map_smul c η).symm, ← algebraMap_smul R c η, h1,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul S c ω, hLS]
    apply smul_right_injective (Fin d → ℂ) (hu s)
    show ev (algebraMap R S s) • ev (algebraMap ℂ S c) • L ω = ev (algebraMap R S s) • c • L ω
    rw [smul_comm (ev (algebraMap R S s)) (ev (algebraMap ℂ S c)), e1, e2,
      smul_comm (ev (algebraMap R S s)) c, e1]
  refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := hLC }, hLS, hL, ?_⟩
  intro ω hω
  change L ω = 0 at hω
  obtain ⟨⟨η, s⟩, hs⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
  have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
  have hη : ψ η = 0 := by rw [← hL, ← hs', hLs, hω, smul_zero]
  obtain ⟨m, b, ω', hb, hηeq⟩ := h2 η hη
  let u : S := IsLocalization.mk' S (1 : R) s
  have hu1 : u * algebraMap R S s = 1 := by rw [IsLocalization.mk'_spec, map_one]
  refine ⟨m, fun i => algebraMap R S (b i),
    fun i => u • KaehlerDifferential.map ℂ ℂ R S (ω' i), hb, ?_⟩
  calc ω = u • ((s : R) • ω) := by
        rw [← algebraMap_smul S (s : R) ω, smul_smul, hu1, one_smul]
    _ = u • KaehlerDifferential.map ℂ ℂ R S (∑ i, b i • ω' i) := by rw [hs', hηeq]
    _ = ∑ i, algebraMap R S (b i) • u • KaehlerDifferential.map ℂ ℂ R S (ω' i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← algebraMap_smul S (b i), smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEvalRootsSymmetricEqAlgebraMap
section
noncomputable section
open Polynomial

theorem UpperTheory.exists_eval_roots_symmetric_eq_algebraMap :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (F : MvPolynomial (Fin N) A), F.IsSymmetric → ∃ a : A, ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → MvPolynomial.aeval x F = algebraMap A S a := by
  intro A _ N g F hF
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_fin_surjective A (le_refl N) ⟨F, hF⟩
  have hPF : MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A (i + 1)) P = F := by
    rw [← MvPolynomial.esymmAlgHom_apply, hP]
  let c : Fin N → A := fun i => (-1) ^ ((i : ℕ) + 1) * g.coeff (N - ((i : ℕ) + 1))
  refine ⟨MvPolynomial.aeval c P, ?_⟩
  intro S _ _ x hg
  have key : ∀ i : Fin N, MvPolynomial.aeval x (MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)) =
      algebraMap A S (c i) := by
    intro i
    have hi := i.2
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    set s := Finset.univ.val.map x with hs
    have hcs : Multiset.card s = N := by simp [s]
    have hprod : (s.map fun t => X - C t).prod = g.map (algebraMap A S) := by
      rw [hg, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
      rfl
    have hk : N - ((i : ℕ) + 1) ≤ Multiset.card s := by omega
    have hco := Multiset.prod_X_sub_C_coeff s hk
    rw [hprod, Polynomial.coeff_map, hcs, show N - (N - ((i : ℕ) + 1)) = (i : ℕ) + 1 by omega]
      at hco
    simp only [c, map_mul, map_pow, map_neg, map_one, hco]
    rw [← mul_assoc, ← mul_pow]
    simp
  have hcomp : (MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1))) =
      MvPolynomial.aeval (fun i => algebraMap A S (c i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.aeval_X, key]
  calc MvPolynomial.aeval x F
      = ((MvPolynomial.aeval x).comp
          (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)))) P := by
        rw [← hPF]
        rfl
    _ = MvPolynomial.aeval (fun i => algebraMap A S (c i)) P := by rw [hcomp]
    _ = algebraMap A S (MvPolynomial.aeval c P) := MvPolynomial.aeval_algebraMap_apply S c P

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAway
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_away :
    ∀ {R B L B' : Type} [CommRing R] [CommRing B] [CommRing L] [CommRing B'] (e : R), IsIdempotentElem e →
        ∀ (T : Submonoid R), (∀ s ∈ T, IsIdempotentElem s) →
        ∀ [Algebra R B] [IsLocalization.Away e B] [Algebra R L] [IsLocalization T L] [Algebra L B']
          [IsLocalization.Away (algebraMap R L e) B'] (jB : B →+* B'),
        (∀ r, jB (algebraMap R B r) = algebraMap L B' (algebraMap R L r)) →
        ∃ S : Submonoid B, (∀ s ∈ S, IsIdempotentElem s) ∧ @IsLocalization B _ S B' _ jB.toAlgebra := by
  intro R B L B' _ _ _ _ e he T hT _ _ _ _ _ _ jB hj
  letI : Algebra R B' := ((algebraMap L B').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B B' := jB.toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq (fun r => (hj r).symm)
  have hloc : IsLocalization (T ⊔ Submonoid.powers e) B' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
      have h1 := (IsLocalization.map_units L ⟨y, hy⟩).map (algebraMap L B')
      have h2 := IsLocalization.map_units B'
        (⟨algebraMap R L e ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R L e))
      simp only [IsScalarTower.algebraMap_apply R L B', map_mul, map_pow] at h1 h2 ⊢
      exact h1.mul h2
    · intro z
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h1⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R L e)) z
      obtain ⟨⟨r, t⟩, h2⟩ := IsLocalization.surj T a
      refine ⟨⟨r, ⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩⟩, ?_⟩
      simp only at h1 h2 ⊢
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' r, ← h2]
      simp only [map_mul, map_pow] at h1 ⊢
      linear_combination (algebraMap L B' (algebraMap R L t)) * h1
    · intro x y hxy
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' y] at hxy
      obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R L e)) B').mp hxy
      simp only at hc
      rw [← map_pow, ← map_mul, ← map_mul, IsLocalization.eq_iff_exists T L] at hc
      obtain ⟨t, ht⟩ := hc
      refine ⟨⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩, ?_⟩
      simp only
      linear_combination ht
  have key := IsLocalization.isLocalization_of_submonoid_le B B' (Submonoid.powers e)
    (T ⊔ Submonoid.powers e) le_sup_right
  refine ⟨(T ⊔ Submonoid.powers e).map (algebraMap R B), ?_, key⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
  exact ((hT y hy).mul (he.pow n)).map (algebraMap R B)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureRangeIsLocalizationIdempotent
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

private theorem idempotent_mul_eval₂_mul_eq {A B : Type} [CommRing A] [CommRing B] (a : A →+* B) (e b : B)
    (he : IsIdempotentElem e) (p : Polynomial A) :
    e * p.eval₂ a (e * b) = e * p.eval₂ a b := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := he.pow_succ_eq i
  rw [mul_pow]
  linear_combination (a (p.coeff i) * b ^ i) * h

theorem UpperTheory.integralClosure_range_isLocalization_idempotent :
    ∀ {A B B' C C' : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
        (a : A →+* B) (jB : B →+* B') (t : C →+* B) (t' : C' →+* B') (mC : C →+* C'),
        Function.Injective t → Function.Injective t' →
        (∀ b, b ∈ t.range ↔ a.IsIntegralElem b) →
        (∀ b, b ∈ t'.range ↔ (jB.comp a).IsIntegralElem b) →
        (∀ c, jB (t c) = t' (mC c)) →
        ∀ (S : Submonoid B), (∀ s ∈ S, IsIdempotentElem s) →
        @IsLocalization B _ S B' _ jB.toAlgebra →
        mC.Flat ∧ Epi (CommRingCat.ofHom mC) := by
  intro A B B' C C' _ _ _ _ _ a jB t t' mC ht ht' hC hC' hcomm S hS hloc
  letI := jB.toAlgebra
  have h1 : ∀ s ∈ S, jB s = 1 := by
    intro s hs
    have hu : IsUnit (jB s) := IsLocalization.map_units B' (⟨s, hs⟩ : S)
    have hid : jB s * jB s = jB s * 1 := by rw [← map_mul, (hS s hs).eq, mul_one]
    exact hu.mul_left_cancel hid
  have hint : ∀ s ∈ S, s ∈ t.range := by
    intro s hs
    rw [hC]
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_one, mul_sub, mul_one, (hS s hs).eq, sub_self]
  have hsurj : Function.Surjective mC := by
    intro z
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S (t' z)
    have hbs' : t' z = jB b := by
      have h : t' z * jB s = jB b := hbs
      rw [h1 _ s.2, mul_one] at h
      exact h
    obtain ⟨p, hp, hpz⟩ := (hC' (t' z)).mp ⟨z, rfl⟩
    have hj : jB (Polynomial.eval₂ a b p) = jB 0 := by
      rw [map_zero, Polynomial.hom_eval₂, ← hbs']
      exact hpz
    obtain ⟨⟨s', hs'⟩, hs'e⟩ := (IsLocalization.eq_iff_exists S B').mp hj
    have hs'0 : s' * Polynomial.eval₂ a b p = 0 := by simpa using hs'e
    have hsb : s' * b ∈ t.range := by
      rw [hC]
      refine ⟨Polynomial.X * p, Polynomial.monic_X.mul hp, ?_⟩
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
      calc s' * b * Polynomial.eval₂ a (s' * b) p
          = b * (s' * Polynomial.eval₂ a (s' * b) p) := by ring
        _ = b * (s' * Polynomial.eval₂ a b p) := by rw [idempotent_mul_eval₂_mul_eq a s' b (hS s' hs') p]
        _ = 0 := by rw [hs'0, mul_zero]
    obtain ⟨c0, hc0⟩ := hsb
    refine ⟨c0, ht' ?_⟩
    rw [← hcomm, hc0, map_mul, h1 _ hs', one_mul, hbs']
  letI := mC.toAlgebra
  have hloc' : IsLocalization (S.comap t) C' := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      have : mC c = 1 := ht' (by rw [← hcomm, map_one]; exact h1 _ hc)
      show IsUnit (mC c)
      rw [this]
      exact isUnit_one
    · intro z
      obtain ⟨c, rfl⟩ := hsurj z
      refine ⟨(c, 1), ?_⟩
      show mC c * mC ((1 : S.comap t) : C) = mC c
      simp
    · intro x y hxy
      have hj : jB (t x) = jB (t y) := by
        rw [hcomm, hcomm]
        exact congrArg t' hxy
      obtain ⟨⟨s, hs⟩, e⟩ := (IsLocalization.eq_iff_exists S B').mp hj
      obtain ⟨cs, hcs⟩ := hint s hs
      refine ⟨⟨cs, show t cs ∈ S by rw [hcs]; exact hs⟩, ht ?_⟩
      simp only [map_mul]
      rw [hcs]
      exact e
  exact ⟨IsLocalization.flat C' (S.comap t), ConcreteCategory.epi_of_surjective _ hsurj⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsLocalizationAwayOfRangeEqBasicOpen
section
open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen :
    ∀ {U W : Scheme.{0}} [IsAffine U] (a : W ⟶ U) [IsOpenImmersion a] (t : Γ(U, ⊤)),
        Set.range a = (U.basicOpen t : Set U) →
        IsAffine W ∧ (∀ x : Γ(W, ⊤), ∃ (k : ℕ) (y : Γ(U, ⊤)), a.appTop.hom t ^ k * x = a.appTop.hom y) ∧
          ∀ y : Γ(U, ⊤), a.appTop.hom y = 0 → ∃ k : ℕ, t ^ k * y = 0 := by
  intro U W _ a _ t h
  have hr : Set.range a = Set.range (U.basicOpen t).ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let χ := IsOpenImmersion.isoOfRangeEq a (U.basicOpen t).ι hr
  have hfac : χ.hom ≫ (U.basicOpen t).ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac a _ hr
  haveI : IsAffine (U.basicOpen t) := (isAffineOpen_top U).basicOpen t
  have hW : IsAffine W := IsAffine.of_isIso χ.hom
  have happ : ∀ r, a.appTop.hom r =
      χ.hom.appTop.hom (algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) r) := by
    intro r
    rw [← hfac, Scheme.Hom.comp_appTop]
    rfl
  have hl : ∀ x, χ.inv.appTop.hom (χ.hom.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.inv_hom_id]
    simp
  have hr' : ∀ x, χ.hom.appTop.hom (χ.inv.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.hom_inv_id]
    simp
  refine ⟨hW, ?_, ?_⟩
  · intro x
    obtain ⟨⟨ℓ, m⟩, hℓ⟩ := IsLocalization.surj (Submonoid.powers t) (χ.inv.appTop.hom x)
    obtain ⟨k, hk⟩ := m.2
    have hk' : t ^ k = (m : Γ(U, ⊤)) := hk
    have hℓ' : χ.inv.appTop.hom x * algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) (t ^ k) =
        algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) ℓ := by
      rw [hk']
      exact hℓ
    refine ⟨k, ℓ, ?_⟩
    rw [happ, happ, ← hℓ']
    simp only [map_pow, map_mul, hr']
    ring
  · intro y hy
    have h0 : algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) y = 0 := by
      have h2 := congrArg χ.inv.appTop.hom ((happ y).symm.trans hy)
      rwa [hl, map_zero] at h2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) _ y).mp h0
    exact ⟨k, hk⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsOpenImmersionOfClosedImmersionFlatEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale :
    ∀ {V X T : Scheme.{0}} (v : V ⟶ X) (p : X ⟶ T), Etale p → IsClosedImmersion v → Flat (v ≫ p) → LocallyOfFinitePresentation (v ≫ p) → IsOpenImmersion v := by
  intro V X T v p hp hv hf hl
  have hv' : FormallyUnramified v := inferInstance
  have hu : FormallyUnramified (v ≫ p) :=
    MorphismProperty.comp_mem @FormallyUnramified v p hv' inferInstance
  have he : Etale (v ≫ p) := Etale.of_formallyUnramified_of_flat (v ≫ p)
  have hev : Etale v := Etale.of_comp v p
  exact IsOpenImmersion.of_flat_of_mono v
end

