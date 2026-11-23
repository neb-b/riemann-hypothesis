module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem dehomogenising_eq_zero_iff : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (B : Type) [CommRing B] (π : MvPolynomial ι R →+* B) (P : Type) [AddCommGroup P] [Module B P] (ε : M →ₛₗ[π] P), π (X i) = 1 → (∀ n, ∀ y ∈ ℳ n, ε y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → ∀ y, ε y = 0 ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i B _ π P _ _ ε hπ hker y
  have hkill : ∀ w : M, ε ((X i - 1 : MvPolynomial ι R) • w) = 0 := by
    intro w
    rw [ε.map_smulₛₗ, map_sub, hπ, map_one, sub_self, zero_smul]
  constructor
  · intro hy
    obtain ⟨n₀, hn⟩ := exists_homogeneous_add_X_sub_one_smul ℳ i y
    obtain ⟨y', hy', w, rfl⟩ := hn n₀ le_rfl
    have hε : ε y' = 0 := by
      rwa [map_add, hkill, add_zero] at hy
    obtain ⟨k, hk⟩ := hker n₀ y' hy' hε
    refine ⟨w - (∑ j ∈ Finset.range k, (X i : MvPolynomial ι R) ^ j) • y', ?_⟩
    rw [smul_sub, smul_smul, mul_geom_sum, sub_smul ((X i : MvPolynomial ι R) ^ k), hk, one_smul]
    abel
  · rintro ⟨w, rfl⟩
    exact hkill w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGrading
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_xProd_pow_smul_monomial {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (j : ℕ) (m : ι →₀ ℕ) :
    ∃ m' : ι →₀ ℕ, (∀ i, m' i = m i + if i ∈ s then j else 0) ∧
      xProd R s ^ j • (monomial m 1 : MvPolynomial ι R) = monomial m' 1 := by
  refine ⟨m + ∑ i ∈ s, Finsupp.single i j, fun i => ?_, ?_⟩
  · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  · rw [smul_eq_mul, xProd, ← Finset.prod_pow, add_comm]
    simp only [X_pow_eq_monomial]
    rw [← monomial_sum_one, monomial_mul, one_mul]

theorem awayFrac_monomial_congr {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (a : ι → ℤ) {k j : ℕ} {m m' : ι →₀ ℕ}
    (hm : ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0)
    (hm' : ∀ i, (m' i : ℤ) = a i + if i ∈ s then (j : ℤ) else 0) :
    awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) =
      awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) := by
  refine awayFrac_eq_iff.2 ⟨0, ?_⟩
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R s (0 + j) m
  obtain ⟨w, hw, ew⟩ := exists_xProd_pow_smul_monomial R s (0 + k) m'
  rw [eu, ew]
  congr 2
  ext i
  have h1 := hu i
  have h2 := hw i
  have h3 := hm i
  have h4 := hm' i
  split_ifs at h1 h2 h3 h4 <;> omega

theorem exists_laurent_numerator {ι : Type} [DecidableEq ι] [Fintype ι] (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, i ∉ s → 0 ≤ a i) :
    ∃ (k : ℕ) (m : ι →₀ ℕ), ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0 := by
  refine ⟨Finset.univ.sup fun i => (a i).natAbs, Finsupp.equivFunOnFinite.symm fun i =>
    (a i + if i ∈ s then ((Finset.univ.sup fun i => (a i).natAbs : ℕ) : ℤ) else 0).toNat,
    fun i => Int.toNat_of_nonneg ?_⟩
  have hk := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  split_ifs with hi
  · omega
  · simpa using ha i hi

theorem exists_basis_grCube_polyGrading :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by
  intro ι _ _ R _ n
  have hiff : ∀ (s : Finset ι) (a : ι → ℤ),
      Finset.univ.filter (fun i => a i < 0) ⊆ s ↔ ∀ i, i ∉ s → 0 ≤ a i := by
    intro s a
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' fun i => by rw [← not_lt]; exact not_imp_not.symm
  have key : ∀ s : Finset ι, ∃ b : Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R (homLoc (polyGrading ι R) s n),
      ∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1.1 i + if i ∈ s then (k : ℤ) else 0) →
        (b a).1 = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) := by
    intro s
    choose k m hm using fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
      exists_laurent_numerator s a.1 a.2.2
    let v := fun a => awayFrac (MvPolynomial ι R) (xProd R s) (k a) (monomial (m a) 1)
    have hv : ∀ a (j : ℕ) (m' : ι →₀ ℕ),
        (∀ i, (m' i : ℤ) = a.1 i + if i ∈ s then (j : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) :=
      fun a j m' h => awayFrac_monomial_congr R s a.1 (hm a) h
    let e : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} ≃
        {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} :=
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, (hiff s a.1).2 a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, (hiff s a.1.1).1 a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨((Module.Basis.span (linearIndependent_laurentMonomial ι R s n v hv)).map
      (LinearEquiv.ofEq _ _ (span_laurentMonomial_eq_homLoc ι R s n v hv))).reindex e, fun a j m' h => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Module.Basis.span_apply]
    exact hv _ j m' h
  choose b hb using key
  refine ⟨b, fun s t h a => Subtype.ext ?_⟩
  obtain ⟨k, m, hm⟩ := exists_laurent_numerator s a.1.1 ((hiff s _).1 a.2)
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R (t \ s) k m
  change locRes X (MvPolynomial ι R) h (b s a).1 = (b t ⟨a.1, a.2.trans h⟩).1
  rw [hb s a k m hm, locRes_awayFrac X h (Finset.prod_sdiff h).symm, eu]
  refine (hb t _ k u fun i => ?_).symm
  have h1 := hu i
  have h2 := hm i
  have h3 := @h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowSmulEqAddSubOneSmul
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add (f := _), map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuot
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

open GradedHilbert Pointwise

section

variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (i : ι)

variable [Decomposition ℳ]

end


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
open Pointwise in
theorem _root_.GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) → ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i hfin
  classical
  set I : Submodule (MvPolynomial ι R) M :=
    (X i - 1 : MvPolynomial ι R) • (⊤ : Submodule (MvPolynomial ι R) M) with hIdef
  have hI : ∀ w : M, (X i - 1 : MvPolynomial ι R) • w ∈ I := fun w =>
    Submodule.smul_mem_pointwise_smul w _ ⊤ Submodule.mem_top

  have hpow : ∀ (e : ℤ) (h : M), h ∈ ℳ e → ∀ m : ℕ,
      (X i : MvPolynomial ι R) ^ m • h ∈ ℳ (e + m) ∧ h - (X i : MvPolynomial ι R) ^ m • h ∈ I := by
    intro e h he m
    refine ⟨?_, ?_⟩
    · induction m with
      | zero => simpa using he
      | succ m ih =>
        rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
        exact _root_.GlobalTheory.X_smul_mem_gr ℳ i _ _ ih
    · have h1 : (X i : MvPolynomial ι R) ^ m • h - h = (X i - 1 : MvPolynomial ι R) •
          ((∑ j ∈ Finset.range m, (X i : MvPolynomial ι R) ^ j) • h) := by
        rw [← mul_smul, mul_geom_sum, sub_smul, one_smul]
      rw [← neg_sub, h1]
      exact I.neg_mem (hI _)

  obtain ⟨G, hG⟩ := hfin.fg_top
  have hlift : ∀ q : QuotSMulTop (X i - 1 : MvPolynomial ι R) M,
      ∃ m : M, ∃ d : ℤ, m ∈ ℳ d ∧ Submodule.Quotient.mk m = q := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i m
    obtain ⟨m', hm', w, hw⟩ := hn₀ n₀ le_rfl
    refine ⟨m', n₀, hm', ?_⟩
    rw [Submodule.Quotient.eq, hw, sub_add_cancel_left]
    exact I.neg_mem (hI w)
  choose f d hfd hfq using hlift
  set T : Finset M := G.image f with hTdef
  have hspanT : ∀ y : M, ∃ s ∈ Submodule.span (MvPolynomial ι R) (T : Set M), y - s ∈ I := by
    intro y
    have hsub : (G : Set (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) ⊆ I.mkQ '' (T : Set M) := by
      intro q hq
      exact ⟨f q, Finset.mem_coe.2 (Finset.mem_image_of_mem f hq), hfq q⟩
    have hy : I.mkQ y ∈ Submodule.span (MvPolynomial ι R) (I.mkQ '' (T : Set M)) :=
      Submodule.span_mono hsub (hG ▸ Submodule.mem_top)
    rw [← Submodule.map_span] at hy
    obtain ⟨s, hs, hsy⟩ := Submodule.mem_map.1 hy
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hsy
    rw [← neg_sub]
    exact I.neg_mem hsy

  have hPadd : ∀ s t : M,
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I) →
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ t - s' ∈ I) →
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s + t - s' ∈ I := by
    rintro s t ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    obtain ⟨s', hs', hs'T, hsI⟩ := h₁ n (le_of_max_le_left hn)
    obtain ⟨t', ht', ht'T, htI⟩ := h₂ n (le_of_max_le_right hn)
    refine ⟨s' + t', add_mem hs' ht', add_mem hs'T ht'T, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem hsI htI
  have hPsmul : ∀ (p : MvPolynomial ι R) (s : M),
      (∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I) →
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ p • s - s' ∈ I := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rintro s ⟨N₀, h⟩
      refine ⟨N₀, fun n hn => ?_⟩
      obtain ⟨s', hs', hs'T, hsI⟩ := h n hn
      refine ⟨C a • s', ?_, Submodule.smul_mem _ _ hs'T, ?_⟩
      · rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
        exact (ℳ n).smul_mem a hs'
      · rw [← smul_sub]
        exact I.smul_mem _ hsI
    | add p q hp hq =>
      intro s hs
      rw [add_smul]
      exact hPadd _ _ (hp s hs) (hq s hs)
    | mul_X p j hp =>
      rintro s ⟨N₀, h⟩
      rw [mul_smul]
      refine hp _ ⟨N₀ + 1, fun n hn => ?_⟩
      obtain ⟨s', hs', hs'T, hsI⟩ := h (n - 1) (by linarith)
      refine ⟨(X j : MvPolynomial ι R) • s', ?_, Submodule.smul_mem _ _ hs'T, ?_⟩
      · have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ j (n - 1) s' hs'
        rwa [sub_add_cancel] at hmem
      · rw [← smul_sub]
        exact I.smul_mem _ hsI
  have hPspan : ∀ s ∈ Submodule.span (MvPolynomial ι R) (T : Set M),
      ∃ N₀ : ℤ, ∀ n, N₀ ≤ n → ∃ s' ∈ ℳ n, s' ∈ Submodule.span (MvPolynomial ι R) (T : Set M) ∧ s - s' ∈ I := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      refine ⟨d q, fun n hn => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = d q + m := ⟨(n - d q).toNat, by omega⟩
      obtain ⟨h1, h2⟩ := hpow (d q) (f q) (hfd q) m
      refine ⟨(X i : MvPolynomial ι R) ^ m • f q, by rw [hm]; exact h1,
        Submodule.smul_mem _ _ (Submodule.subset_span hx), h2⟩
    | zero => exact ⟨0, fun n _ => ⟨0, zero_mem _, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩⟩
    | add x y _ _ hx hy => exact hPadd x y hx hy
    | smul a x _ hx => exact hPsmul a x hx

  have hhom : ∀ (n : ℤ) (y : M), y ∈ ℳ n →
      ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
    intro n y hy
    obtain ⟨s, hs, hys⟩ := hspanT y
    obtain ⟨N₀, hN₀⟩ := hPspan s hs
    obtain ⟨s', hs', hs'T, hsI⟩ := hN₀ (max N₀ n) (le_max_left _ _)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, max N₀ n = n + m := ⟨(max N₀ n - n).toNat, by omega⟩
    obtain ⟨hy1, hy2⟩ := hpow n y hy m
    rw [← hm] at hy1
    have hdiffI : (X i : MvPolynomial ι R) ^ m • y - s' ∈ I := by
      have hsplit : (X i : MvPolynomial ι R) ^ m • y - s' =
          -(y - (X i : MvPolynomial ι R) ^ m • y) + (y - s) + (s - s') := by abel
      rw [hsplit]
      exact add_mem (add_mem (I.neg_mem hy2) hys) hsI
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hdiffI
    obtain ⟨k, hk⟩ := _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i
      (sub_mem hy1 hs') hw.symm
    refine ⟨k + m, ?_⟩
    rw [pow_add, mul_smul]
    have hkm : (X i : MvPolynomial ι R) ^ k • ((X i : MvPolynomial ι R) ^ m • y) =
        (X i : MvPolynomial ι R) ^ k • s' := by
      rw [← sub_eq_zero, ← smul_sub]
      exact hk
    rw [hkm]
    exact Submodule.smul_mem _ _ hs'T
  refine ⟨T, fun y => ?_⟩
  induction y using DirectSum.Decomposition.inductionOn ℳ with
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | homogeneous m => exact hhom _ _ m.2
  | add y z hy hz =>
    obtain ⟨k₁, hk₁⟩ := hy
    obtain ⟨k₂, hk₂⟩ := hz
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyBaseChangeGrCubeIso
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem map_xProd_pow_smul_of_X {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
  classical
  have h1 : ∀ y, ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [xProd, xProd, Finset.prod_insert ha, Finset.prod_insert ha, mul_smul, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h1, ih]

theorem nonempty_baseChange_grCube_iso : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by
  intro ι _ _ R₀ R _ _ _ N₀ _ _ _ _ 𝒩₀ _ _ N _ _ _ _ 𝒩 _ _ _ _ _ ψ n hψ hX hgr
  choose θ hθ hθe using fun s : Finset ι => GlobalTheory.exists_isBaseChange_away_xProd ι R₀ R N₀ N ψ s hψ hX
  have hg : ∀ s j, ∀ y ∈ homLoc 𝒩₀ s j, θ s y ∈ homLoc 𝒩 s j := by
    rintro s j _ ⟨k, m, hm, rfl⟩
    rw [hθe]
    exact awayFrac_mem_homLoc (hgr _ _ hm) rfl
  let η : ∀ s, homLoc 𝒩₀ s n →ₗ[R₀] homLoc 𝒩 s n := fun s =>
    { toFun := fun y => ⟨θ s y, hg s n _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (θ s) a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul (θ s) r a.1) }
  have hη : ∀ s, IsBaseChange R (η s) := fun s =>
    GlobalTheory.isBaseChange_gradedPiece R₀ R _ _ (homLoc 𝒩₀ s) (homLoc 𝒩 s) (θ s) n (η s) (hθ s) (hg s) fun _ => rfl
  have hres : ∀ {s t : Finset ι} (h : s ⊆ t) (z : homLoc 𝒩₀ s n),
      η t (homLocRes 𝒩₀ h n z) = homLocRes 𝒩 h n (η s z) := by
    rintro s t h ⟨_, k, m, hm, rfl⟩
    apply Subtype.ext
    change θ t (locRes X N₀ h (awayFrac N₀ _ k m)) = locRes X N h (θ s (awayFrac N₀ _ k m))
    rw [hθe, locRes_awayFrac X h (Finset.prod_sdiff h).symm,
      locRes_awayFrac X h (Finset.prod_sdiff h).symm, hθe]
    exact congrArg _ (map_xProd_pow_smul_of_X ψ hX (t \ s) k m)
  have key : ∀ {s t : Finset ι} (h : s ⊆ t) (x : R ⊗[R₀] homLoc 𝒩₀ s n),
      (hη t).equiv ((homLocRes 𝒩₀ h n).baseChange R x) = homLocRes 𝒩 h n ((hη s).equiv x) := by
    intro s t h x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r z =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        hres]
  exact ⟨Cube.isoMk (fun s => (hη s).equiv) fun h x => key h x⟩

end GlobalTheory
end

