module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankNormBound
section
open NumberField

namespace PositivityTheory.Xgn.AmalgamKernelBound

open Module

theorem det_eq_of_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (ι : N →ₗ[ℤ] M) (hι : Function.Injective ι) (h : finrank ℤ N = finrank ℤ M)
    (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) (hfg : ∀ x, ι (g x) = f (ι x)) :
    LinearMap.det f = LinearMap.det g := by
  obtain ⟨e⟩ : Nonempty (M ≃ₗ[ℤ] N) := ⟨LinearEquiv.ofFinrankEq M N h.symm⟩
  have hj : Function.Injective ((e : M →ₗ[ℤ] N) ∘ₗ ι) := e.injective.comp hι
  have hdet : LinearMap.det ((e : M →ₗ[ℤ] N) ∘ₗ ι) ≠ 0 := by
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hj)
  have hcomm : ((e : M →ₗ[ℤ] N) ∘ₗ ι) ∘ₗ g =
      ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ∘ₗ ((e : M →ₗ[ℤ] N) ∘ₗ ι) := by
    apply LinearMap.ext
    intro x
    simp [hfg]
  have key := congrArg LinearMap.det hcomm
  rw [LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ ι) g,
    LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ((e : M →ₗ[ℤ] N) ∘ₗ ι),
    LinearMap.det_conj] at key
  exact (mul_left_cancel₀ hdet (key.trans (mul_comm _ _))).symm

theorem det_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    LinearMap.det ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) =
      Algebra.norm ℤ a ^ finrank (𝓞 E) Λ := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := Λ)
    (le_refl (finrank (𝓞 E) Λ))
  let L : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[𝓞 E] Λ := Fintype.linearCombination (𝓞 E) v
  have hL : Function.Injective L :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  have htors : ∀ x : Λ, ∃ b : 𝓞 E, b ≠ 0 ∧ b • x ∈ LinearMap.range L := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range L)
    have h2 : finrank (𝓞 E) (LinearMap.range L) = finrank (𝓞 E) Λ := by
      rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]
    have h3 : finrank (𝓞 E) (Λ ⧸ LinearMap.range L) = 0 := by omega
    intro x
    obtain ⟨b, hb, hbx⟩ := Module.finrank_eq_zero_iff.mp h3 (Submodule.Quotient.mk x)
    refine ⟨b, hb, ?_⟩
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hbx
  let Lz : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[ℤ] Λ := L.restrictScalars ℤ
  have hLz : Function.Injective Lz := hL
  have htorsZ : ∀ x : Λ, ∃ r : ℤ, r ≠ 0 ∧ r • x ∈ LinearMap.range Lz := by
    intro x
    obtain ⟨b, hb, hbx⟩ := htors x
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hbx
    obtain ⟨r, hr, c, hc⟩ := IsAlgebraic.exists_nonzero_dvd
      (Algebra.IsIntegral.isIntegral (R := ℤ) b).isAlgebraic (mem_nonZeroDivisors_of_ne_zero hb)
    refine ⟨r, hr, LinearMap.mem_range.mpr ⟨c • y, ?_⟩⟩
    show L (c • y) = r • x
    rw [map_smul, hy, ← algebraMap_smul (𝓞 E) r x, hc, mul_comm b c, mul_smul]
  have hrankZ : finrank ℤ (Fin (finrank (𝓞 E) Λ) → 𝓞 E) = finrank ℤ Λ := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range Lz)
    have h2 := LinearMap.finrank_range_of_inj hLz
    have h3 : finrank ℤ (Λ ⧸ LinearMap.range Lz) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨r, hr, hrx⟩ := htorsZ x
      refine ⟨r, hr, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hrx
    omega
  have hfg : ∀ y, Lz (((LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a).restrictScalars ℤ) y)
      = ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (Lz y) := by
    intro y
    simp only [Lz, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    exact map_smul L a y
  have hsmul : LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a = a • LinearMap.id :=
    LinearMap.ext fun y => by simp
  rw [PositivityTheory.Xgn.AmalgamKernelBound.det_eq_of_intertwine Lz hLz hrankZ _ _ hfg,
    LinearMap.det_restrictScalars, hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fin_fun, map_pow]

theorem charpoly_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ).charpoly =
      (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly ^ finrank (𝓞 E) Λ := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_pow, LinearMap.eval_charpoly, LinearMap.eval_charpoly]
  have h1 : algebraMap ℤ (Module.End ℤ Λ) t - (LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ =
      (LinearMap.lsmul (𝓞 E) Λ (algebraMap ℤ (𝓞 E) t - a)).restrictScalars ℤ := by
    apply LinearMap.ext
    intro x
    simp [sub_smul, Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
  have h2 : algebraMap ℤ (Module.End ℤ (𝓞 E)) t - (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)) =
      Algebra.lmul ℤ (𝓞 E) (algebraMap ℤ (𝓞 E) t - a) := by
    rw [map_sub, AlgHom.commutes]
  rw [h1, h2, PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul, ← Algebra.norm_apply ℤ]

theorem corank_le {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : M →ₗ[ℤ] M) (hf : LinearMap.det f ≠ 0) :
    finrank k (LinearMap.ker (LinearMap.baseChange k f)) ≤
      padicValNat p (LinearMap.det f).natAbs := by
  classical
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hrank : finrank ℤ (LinearMap.range f) = finrank ℤ M := LinearMap.finrank_range_of_inj hinj
  obtain ⟨t, s, d, hst⟩ : ∃ (t : Module.Basis (Fin (finrank ℤ M)) ℤ M)
      (s : Module.Basis (Fin (finrank ℤ M)) ℤ (LinearMap.range f))
      (d : Fin (finrank ℤ M) → ℤ), ∀ i, (s i : M) = d i • t i :=
    ⟨_, _, _, Submodule.smithNormalFormBotBasis_def (Module.finBasis ℤ M) hrank⟩
  obtain ⟨e, he⟩ : ∃ e : M ≃ₗ[ℤ] LinearMap.range f, ∀ x, (e x : M) = f x :=
    ⟨LinearEquiv.ofInjective f hinj, fun x => LinearEquiv.ofInjective_apply f x⟩
  have hfe : f = (LinearMap.range f).subtype ∘ₗ (e : M →ₗ[ℤ] LinearMap.range f) :=
    LinearMap.ext fun x => by simp [he]
  have hD : LinearMap.toMatrix s t (LinearMap.range f).subtype = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, Submodule.subtype_apply, hst j, map_smul,
      Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, hij, Ne.symm hij]
  have hQ : IsUnit (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det := by
    have h1 : LinearMap.toMatrix s t (e.symm : LinearMap.range f →ₗ[ℤ] M) *
        LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) = 1 := by
      rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id t]
      congr 1
      exact LinearMap.ext fun x => by simp
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h2
    exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩
  have hA : LinearMap.toMatrix t t f =
      Matrix.diagonal d * LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) := by
    rw [← hD, ← LinearMap.toMatrix_comp, ← hfe]
  have hdvd : (∏ i, d i) ∣ LinearMap.det f := by
    refine ⟨(LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det, ?_⟩
    rw [← LinearMap.det_toMatrix t, hA, Matrix.det_mul, Matrix.det_diagonal]
  have hAk : LinearMap.toMatrix (Algebra.TensorProduct.basis k t) (Algebra.TensorProduct.basis k t)
      (LinearMap.baseChange k f) =
      Matrix.diagonal (fun i => algebraMap ℤ k (d i)) *
        (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).map (algebraMap ℤ k) := by
    rw [LinearMap.toMatrix_baseChange, hA, Matrix.map_mul,
      Matrix.diagonal_map (map_zero (algebraMap ℤ k))]
  have hrange : finrank k (LinearMap.range (LinearMap.baseChange k f)) =
      Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} := by
    rw [← Matrix.toLin_toMatrix (Algebra.TensorProduct.basis k t)
      (Algebra.TensorProduct.basis k t) (LinearMap.baseChange k f),
      ← Matrix.rank_eq_finrank_range_toLin, hAk, Matrix.rank_mul_eq_left_of_isUnit_det]
    · convert Matrix.rank_diagonal (fun i => algebraMap ℤ k (d i))
    · have := hQ.map (algebraMap ℤ k)
      rw [RingHom.map_det] at this
      exact this
  haveI : Module.Finite k (TensorProduct ℤ k M) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis k t)
  have hsum := LinearMap.finrank_range_add_finrank_ker (LinearMap.baseChange k f)
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis k t)] at hsum
  have hcongr : Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} =
      Fintype.card {i // ¬ (p : ℤ) ∣ d i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      rw [eq_intCast, ne_eq, CharP.intCast_eq_zero_iff k p])
  have hcompl : Fintype.card {i // ¬ (p : ℤ) ∣ d i} =
      Fintype.card (Fin (finrank ℤ M)) - Fintype.card {i // (p : ℤ) ∣ d i} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i // (p : ℤ) ∣ d i} ≤ Fintype.card (Fin (finrank ℤ M)) :=
    Fintype.card_subtype_le _
  have hpow : (p : ℤ) ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ LinearMap.det f := by
    rw [Fintype.card_subtype, ← Finset.prod_const]
    refine dvd_trans ?_ hdvd
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _
      (fun i hi => (Finset.mem_filter.mp hi).2)) ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hne : (LinearMap.det f).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hf
  have hpow' : p ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ (LinearMap.det f).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hpow
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne).mp hpow'
  omega

end PositivityTheory.Xgn.AmalgamKernelBound

theorem PositivityTheory.Xgn.kernel_rank_norm_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  intro E _ _ k _ p _ _ Λ _ _ _ _ a ha
  have hdet := PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul E Λ a
  have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  refine ⟨?_, ?_⟩
  · have h := PositivityTheory.Xgn.AmalgamKernelBound.corank_le k p
      ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (by rw [hdet]; exact pow_ne_zero _ hN)
    rw [hdet, Int.natAbs_pow] at h
    simpa only [Nat.padicValNat_def, Nat.multiplicity_pow] using h
  · rw [LinearMap.charpoly_baseChange, PositivityTheory.Xgn.AmalgamKernelBound.charpoly_lsmul,
      Polynomial.map_pow, algebraMap_int_eq]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfFixedByAutomorphisms
section
open NumberField IsDedekindDomain

namespace PositivityTheory.Xgn.FixedFieldAutomorphism

open scoped Cardinal

theorem exists_equiv {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] [Algebra R K] [Algebra R L] [FaithfulSMul R K]
    [FaithfulSMul R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ g : K ≃+* L, ∀ r, g (algebraMap R K r) = algebraMap R L r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR
    (hKL ▸ hK)
  have h3 : #s = #t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : t → L))) L]
  congr 1
  exact e'.commutes r

theorem exists_aut {R : Type} [CommRing R] [IsDomain R] (hR : #R ≤ ℵ₀) (i j : R →+* ℂ)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ g : ℂ ≃+* ℂ, ∀ r, g (i r) = j r := by
  have hC : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  exact @exists_equiv R ℂ ℂ _ _ _ _ _ _ i.toAlgebra j.toAlgebra
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ i.toAlgebra).2 hi)
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ j.toAlgebra).2 hj) hR hC rfl

end PositivityTheory.Xgn.FixedFieldAutomorphism

theorem PositivityTheory.Xgn.mem_of_fixed_by_automorphisms : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  have hFc : Cardinal.mk F ≤ Cardinal.aleph0 := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
    simpa using this
  by_cases hc : IsAlgebraic F c
  · have hint : IsIntegral F c := hc.isIntegral
    haveI : FiniteDimensional F (IntermediateField.adjoin F {c}) :=
      IntermediateField.adjoin.finiteDimensional hint
    set_option synthInstance.maxHeartbeats 200000 in
    have hE : Cardinal.mk (IntermediateField.adjoin F {c}) ≤ Cardinal.aleph0 := by
      refine (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le hFc le_rfl)
    have key : ∀ φ : IntermediateField.adjoin F {c} →ₐ[F] ℂ,
        φ = (IntermediateField.adjoin F {c}).val := by
      intro φ
      obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hE
        (IntermediateField.adjoin F {c}).val.toRingHom φ.toRingHom
        (RingHom.injective _) (RingHom.injective _)
      have h1 : g c = c := h g fun a ha => by
        have := hg (algebraMap F _ ⟨a, ha⟩)
        simpa using this
      have h2 := hg (IntermediateField.AdjoinSimple.gen F c)
      refine (IntermediateField.adjoin.powerBasis hint).algHom_ext ?_
      rw [IntermediateField.adjoin.powerBasis_gen]
      exact h2.symm.trans h1
    have hcard := AlgHom.card F (IntermediateField.adjoin F {c}) ℂ
    have h1 : Module.finrank F (IntermediateField.adjoin F {c}) = 1 := by
      rw [← hcard, Fintype.card_eq_one_iff]
      exact ⟨_, key⟩
    have h2 : c ∈ (⊥ : IntermediateField F ℂ) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 h2
    exact a.2
  · exfalso
    have hc' : ¬ IsAlgebraic F (c + 1) := fun h' => hc (by
      have := h'.isIntegral.sub (isIntegral_one (R := F))
      simpa using this.isAlgebraic)
    have hP : Cardinal.mk (Polynomial F) ≤ Cardinal.aleph0 :=
      Polynomial.cardinalMk_le_max.trans (max_le hFc le_rfl)
    obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hP
      (Polynomial.aeval (R := F) c).toRingHom (Polynomial.aeval (R := F) (c + 1)).toRingHom
      (transcendental_iff_injective.1 hc) (transcendental_iff_injective.1 hc')
    have h1 : g c = c := h g fun a ha => by
      have := hg (Polynomial.C ⟨a, ha⟩)
      simpa using this
    have h2 := hg Polynomial.X
    simp [h1] at h2
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TensorAlgebraicallyClosedDomain
section
open TensorProduct

namespace PositivityTheory.Xgn.TensorDomain

open Polynomial
open scoped IntermediateField

theorem natDegree_minpoly_eq {k F A : Type} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ (algebraMap k F).range)
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly k θ).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ)
    (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact h _ (IsIntegral.isAlgebraic y.2)
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd k θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem linearDisjoint_algebraicClosure {K Ω L : Type} [Field K] [CharZero K] [Field Ω] [Field L]
    [Algebra K Ω] [Algebra Ω L] [Algebra K L] [IsScalarTower K Ω L]
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) :
    (algebraicClosure K L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra :=
    (algebraicClosure.isAlgebraic K L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)
  let M : IntermediateField K L := halg.toIntermediateField
  haveI : FiniteDimensional K M := ‹Module.Finite K B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K M
  have hi : IsIntegral K (θ : L) := (Algebra.IsIntegral.isIntegral (R := K) θ).map M.val
  have e : K⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left
    (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := natDegree_minpoly_eq (F := Ω) h hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

theorem exists_point (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {a : A} (ha : a ≠ 0) : ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
  let S := Localization.Away a
  haveI : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  haveI : Algebra.FiniteType A S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) S
  haveI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  let ψ : (S ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(ψ.comp (Ideal.Quotient.mkₐ k m)).comp (IsScalarTower.toAlgHom k A S), ?_⟩
  have hu : IsUnit (algebraMap A S a) := IsLocalization.Away.algebraMap_isUnit a
  exact (hu.map (ψ.comp (Ideal.Quotient.mkₐ k m))).ne_zero

theorem isDomain_tensor_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (F : Type) [Field F] [Algebra k F] :
    IsDomain (F ⊗[k] A) := by
  let b := Module.Basis.ofVectorSpace k F
  let B := Algebra.TensorProduct.basis A b
  haveI : Nontrivial (A ⊗[k] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := k) (A := A) (B := F)
      (algebraMap k A).injective).nontrivial
  haveI : NoZeroDivisors (A ⊗[k] F) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hx, hy⟩ := hc
    obtain ⟨i, hi⟩ : ∃ i, B.repr x i ≠ 0 := by
      by_contra hn
      exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨j, hj⟩ : ∃ i, B.repr y i ≠ 0 := by
      by_contra hn
      exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨φ, hφ⟩ := exists_point k A (mul_ne_zero hi hj)
    let Φ : A ⊗[k] F →ₐ[k] F :=
      Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ) (AlgHom.id k F)
        fun _ _ => Commute.all _ _
    have key : ∀ z i, φ (B.repr z i) = b.repr (Φ z) i := by
      intro z i
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
      | tmul a f =>
        have h1 : Φ (a ⊗ₜ f) = φ a • f := by simp [Φ, Algebra.smul_def]
        rw [h1, map_smul]
        simp [B, Algebra.TensorProduct.basis_repr_tmul]
    have h0 : Φ x * Φ y = 0 := by rw [← map_mul, hxy, map_zero]
    apply hφ
    rw [map_mul, key, key]
    rcases mul_eq_zero.1 h0 with h | h <;> simp [h]⟩
  haveI : IsDomain (A ⊗[k] F) := NoZeroDivisors.to_isDomain _
  exact (Algebra.TensorProduct.comm k F A).toMulEquiv.isDomain

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [IsDomain (Ω ⊗[k] S)] (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem isDomain_tensor {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A]
    [Algebra K Ω] [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (F : Type) [Field F]
    [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let φ := Algebra.TensorProduct.map (AlgHom.id K N) j
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj
  haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ
  exact isDomain_tensor_of_closure K N A F

theorem isDomain_of_algClosed {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L]
    [Algebra K F] [CharZero K] (h : ∀ a : F, IsAlgebraic K a → a ∈ (algebraMap K F).range) :
    IsDomain (L ⊗[K] F) := by
  classical
  haveI : Nontrivial (L ⊗[K] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := F)
      (algebraMap K L).injective).nontrivial
  haveI : NoZeroDivisors (L ⊗[K] F) := ⟨fun {u v} huv => by
    obtain ⟨Su, rfl⟩ := TensorProduct.exists_finset u
    obtain ⟨Sv, rfl⟩ := TensorProduct.exists_finset v
    let T : Finset F := (Su ∪ Sv).image Prod.snd
    let A := Algebra.adjoin K (T : Set F)
    haveI : Algebra.FiniteType K A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset T)
    haveI := isDomain_tensor A.val Subtype.val_injective h L
    let φ := Algebra.TensorProduct.map (AlgHom.id K L) A.val
    have hφ : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := L) A.val.toLinearMap
        Subtype.val_injective
    have hr : ∀ S : Finset (L × F), S ⊆ Su ∪ Sv → (∑ q ∈ S, q.1 ⊗ₜ[K] q.2) ∈ φ.range :=
      fun S hS => sum_mem fun q hq => ⟨q.1 ⊗ₜ ⟨q.2, Algebra.subset_adjoin
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS hq)))⟩, rfl⟩
    obtain ⟨a, ha⟩ := hr Su Finset.subset_union_left
    obtain ⟨b, hb⟩ := hr Sv Finset.subset_union_right
    have ha' : φ a = _ := ha
    have hb' : φ b = _ := hb
    rw [← ha', ← hb', ← map_mul, map_eq_zero_iff _ hφ] at huv
    rw [← ha', ← hb']
    rcases mul_eq_zero.1 huv with h0 | h0
    · left; rw [h0, map_zero]
    · right; rw [h0, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end PositivityTheory.Xgn.TensorDomain

theorem PositivityTheory.Xgn.tensor_algebraically_closed_domain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  intro K Ω C _ _ _ _ _ _ h
  haveI : IsDomain (C ⊗[K] Ω) := PositivityTheory.Xgn.TensorDomain.isDomain_of_algClosed h
  exact (Algebra.TensorProduct.comm K Ω C).toMulEquiv.isDomain
end

