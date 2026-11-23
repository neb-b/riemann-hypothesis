module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem sees_mono {n : ℕ} {R G : Type} [CommRing R] [Group G] (D : GDet n R G) (V V' : Subgroup G)
    [V.Normal] [V'.Normal] (h : V' ≤ V) (I : Ideal R) (hV : Sees D V I) : Sees D V' I := by
  intro i x y hxy
  apply hV i x y
  have h' : V' ≤ V.comap (MonoidHom.id G) := fun g hg => h hg
  have key : ∀ z : MonoidAlgebra R G, MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V) z =
      MonoidAlgebra.mapDomainRingHom R (QuotientGroup.map V' V (MonoidHom.id G) h')
        (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V') z) := by
    intro z
    simp only [MonoidAlgebra.mapDomainRingHom_apply]
    apply MonoidAlgebra.coeff_injective
    simp only [MonoidAlgebra.coeff_mapDomain]
    rw [← Finsupp.mapDomain_comp]
    rfl
  rw [key, key, hxy]

theorem UpperTheory.V.Pa.Core.phSees :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (j : ℕ), ∃ V : OpenNormalSubgroup Λ.Ph, V.toSubgroup ≤ Ph0 Λ ∧ Sees W.t.D (V.toSubgroup.subgroupOf (Ph0 Λ)) (maximalIdeal W.R ^ j) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W j
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨V, hV⟩ := dSees n W.R (Ph0 Λ) W.t.D (maximalIdeal W.R) W.t.cont j
  have hUo : IsOpen (Subtype.val '' (V : Set (Ph0 Λ))) :=
    (Λ.Ph0_open).isOpenMap_subtype_val _ V.toOpenSubgroup.isOpen
  have h1U : (1 : Λ.Ph) ∈ Subtype.val '' (V : Set (Ph0 Λ)) := ⟨1, V.one_mem, rfl⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have hHle : H.toSubgroup ≤ Ph0 Λ := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := hH hg
    exact x.2
  refine ⟨H, hHle, ?_⟩
  refine sees_mono W.t.D _ _ ?_ _ hV
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy, hxy⟩ := hH hx
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.QuotientRegularAtOfQuotientFreeOverPowerSeries
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.quotientRegularAt_of_quotient_free_over_powerSeries :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (M : Type) [AddCommGroup M] [Module R M] (a j r : ℕ) (e : (M ⧸ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ (a + 1) j)), (∀ z m, e (s z • m) = z • e m) → QRegAt M (fun a => s (MvPowerSeries.X a)) (((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) a := by
  intro Λ R σ _ _ _ _ s M _ _ a j r e he c hc α
  classical
  rw [← kjMap Λ R σ s (a + 1) j] at hc
  have hsurj := Ideal.Quotient.mk_surjective (I := kjIdeal Λ σ (a + 1) j)
  choose t ht using fun β i => hsurj (e (Submodule.Quotient.mk (c β)) i)
  have hmono : ∀ β : σ →₀ ℕ, GlobalTheory.monoVal (fun a => s (MvPowerSeries.X a)) β =
      s (GlobalTheory.monoVal MvPowerSeries.X β) := fun β => by
    simp only [GlobalTheory.monoVal, Finsupp.prod, map_prod, map_pow]
  have h0 := congrArg e ((Submodule.Quotient.mk_eq_zero _).2 hc)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← Submodule.mkQ_apply, map_sum, map_sum] at h0
  simp only [map_smul, hmono, he, Submodule.mkQ_apply] at h0
  have hL : ∀ i, t α i ∈ kjIdeal Λ σ 1 j := by
    intro i
    have h1 := congrFun h0 i
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, ← ht, Pi.zero_apply] at h1
    have h2 : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ Λ) β.1 * t β i) ∈ kjIdeal Λ σ (a + 1) j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← h1]
      rfl
    have h3 := qRegAt_mvPowerSeries Λ σ (maximalIdeal Λ ^ j) a (fun β => t β i)
      (by simpa [kjIdeal, Ideal.map_pow] using h2) α
    simpa [kjIdeal, Ideal.map_pow] using h3
  have hs := Submodule.Quotient.mk_surjective ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)
  choose m hm using fun i : Fin r => hs (e.symm (Pi.single i 1))
  have h4 : c α - ∑ i, s (t α i) • m i ∈ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.eq]
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply _ (∑ i, _), map_sum, map_sum]
    simp only [map_smul, he, Submodule.mkQ_apply, hm, AddEquiv.apply_symm_apply]
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [← ht, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hle : kjIdeal Λ σ (a + 1) j ≤ kjIdeal Λ σ 1 j := by
    unfold kjIdeal
    exact sup_le_sup_right (Ideal.pow_le_pow_right (by omega)) _
  have h5 : c α ∈ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R M) := by
    rw [← sub_add_cancel (c α) (∑ i, s (t α i) • m i)]
    refine add_mem (Submodule.smul_mono_left (Ideal.map_mono hle) h4) (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hL i)) Submodule.mem_top
  rw [kjMap, pow_one] at h5
  exact h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SplittingAlgebraNontrivialFreeGenerated
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem spCo_desc {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (a : Fin q → Fin n → L)
    (ha : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (a j i)) = (P j).map (algebraMap R L))
    (F : MvPowerSeries (Fin q × Fin n) R →ₐ[R] L)
    (hX : ∀ p, F (MvPowerSeries.X p) = a p.1 p.2 - algebraMap R L (ut p.1 p.2)) :
    ∃ F' : Sp P ut →ₐ[R] L, ∀ z, F' (Sp.mk P ut z) = F z := by
  classical
  have hC : ∀ r : R, F (MvPowerSeries.C r) = algebraMap R L r := by
    intro r
    have : (MvPowerSeries.C r : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ r := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, F.commutes]
  have hle : spIdeal P ut ≤ RingHom.ker F := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 : ∀ i, F (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)) = a j i := by
      intro i
      rw [map_add (f := _), hC, hX]
      exact add_sub_cancel _ _
    have h2 : (F : MvPowerSeries (Fin q × Fin n) R →+* L).comp MvPowerSeries.C = algebraMap R L :=
      RingHom.ext hC
    rw [← RingHom.coe_coe F, ← Polynomial.coeff_map]
    rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, h2, ← ha j]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, h1, sub_self,
      Polynomial.coeff_zero]
  exact ⟨Ideal.Quotient.liftₐ _ F fun z hz => hle hz, fun z => rfl⟩

private theorem splitting_algebra_nontrivial_free_generated (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j, (P j).Monic ∧ (P j).natDegree = n ∧
      (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) :
    Nontrivial (Sp P ut) ∧ Module.Free R (Sp P ut) ∧
      Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  classical
  obtain ⟨bas, -⟩ := mSplitAlg_basis (Fin q) n R P (fun j => (h j).1) (fun j => (h j).2.1)
  haveI : Module.Free R (MSplitAlg P n) := Module.Free.of_basis bas
  haveI : Module.Finite R (MSplitAlg P n) := Module.Finite.of_basis bas
  have hχ : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i))) =
      (P j).map (algebraMap R (ResidueField R)) := by
    intro j
    rw [ResidueField.algebraMap_eq, (h j).2.2]
  obtain ⟨χ, hχr⟩ : ∃ χ : (MSplitAlg P n) →ₐ[R] ResidueField R,
      ∀ j i, χ (MSplitAlg.root P n j i) = residue R (ut j i) :=
    ⟨MSplitAlg.lift P n _ hχ, MSplitAlg.lift_root P n _ hχ⟩
  have hχalg : ∀ r : R, χ (algebraMap R (MSplitAlg P n) r) = residue R r := by
    intro r
    rw [χ.commutes, ResidueField.algebraMap_eq]
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχalg r⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : Ideal (MSplitAlg P n), n0 = RingHom.ker χ := ⟨_, rfl⟩
  haveI : n0.IsMaximal := hn0 ▸ RingHom.ker_isMaximal_of_surjective χ hχs
  obtain ⟨hBs, hBfin, hBloc, hBcpl, hBfree, -, hBuniv⟩ := local_factor R (MSplitAlg P n) n0
  haveI := hBfin
  haveI := hBloc
  haveI : Module.Free R (Localization.AtPrime n0) := hBfree inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n0) := isNoetherian_of_tower R (inferInstance : IsNoetherian R (Localization.AtPrime n0))
  have hmem0 : ∀ y, y ∈ n0 ↔ χ y = 0 := fun y => by rw [hn0, RingHom.mem_ker]
  have hinB : ∀ y ∈ n0, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y ∈ maximalIdeal (Localization.AtPrime n0) := fun y hy =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n0) n0 y).2 hy
  have hroot : ∀ j i, MSplitAlg.root P n j i - algebraMap R (MSplitAlg P n) (ut j i) ∈ n0 := by
    intro j i
    rw [hmem0, map_sub, hχalg, hχr, sub_self]
  haveI hRR : IsCO R R := @IsCO.mk R R _ _ _ _ _ _ inferInstance ⟨fun a ha => ha⟩
    (fun x => ⟨x, by rw [Algebra.algebraMap_self, RingHom.id_apply, sub_self]; exact zero_mem _⟩)
  haveI hRB : IsCO R (Localization.AtPrime n0) := @IsCO.mk R (Localization.AtPrime n0) _ _ _ _ _ _ hBcpl hBloc (fun x => by
    obtain ⟨y, rfl⟩ := hBs x
    obtain ⟨r, hr⟩ := residue_surjective (χ y)
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← (algebraMap (MSplitAlg P n) (Localization.AtPrime n0)).map_sub y (algebraMap R (MSplitAlg P n) r)]
    apply hinB
    rw [hmem0, map_sub, hχalg, hr, sub_self])
  have hmemB : ∀ p : Fin q × Fin n, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) -
      algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) ∈ maximalIdeal (Localization.AtPrime n0) := by
    intro p
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← (algebraMap (MSplitAlg P n) (Localization.AtPrime n0)).map_sub (MSplitAlg.root P n p.1 p.2) (algebraMap R (MSplitAlg P n) (ut p.1 p.2))]
    exact hinB _ (hroot p.1 p.2)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev R R (Localization.AtPrime n0) (Fin q × Fin n) (Algebra.ofId R (Localization.AtPrime n0))
    (fun p => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2)) hmemB
  have hFX' : ∀ p : Fin q × Fin n, F (MvPowerSeries.X p) =
      algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) := hFX
  have hFC' : ∀ x : R, F (MvPowerSeries.C x) = algebraMap R (Localization.AtPrime n0) x := fun x => hFC x
  have hrootB : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i))) =
      (P j).map (algebraMap R (Localization.AtPrime n0)) := by
    intro j
    have := congrArg (Polynomial.map (algebraMap (MSplitAlg P n) (Localization.AtPrime n0))) (MSplitAlg.prod_root P n j)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rw [← this, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  obtain ⟨Φ, hΦ⟩ := spCo_desc P ut (fun j i => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i)) hrootB F hFX
  haveI : Nontrivial (Sp P ut) := Φ.toRingHom.domain_nontrivial
  haveI : IsLocalRing (Sp P ut) := IsLocalRing.of_surjective' (Sp.mk P ut).toRingHom
    (fun z => Ideal.Quotient.mk_surjective z)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (MSplitAlg P n) →ₐ[R] Sp P ut, ∀ j i, Ψ (MSplitAlg.root P n j i) = Sp.u P ut j i :=
    ⟨MSplitAlg.lift P n _ (fun j => (spRoots R q n P ut j).1), MSplitAlg.lift_root P n _ _⟩
  obtain ⟨F0, hF0X, hF0C⟩ : ∃ F0 : MvPowerSeries (Fin q × Fin n) R →ₐ[R] ResidueField R,
      (∀ p, F0 (MvPowerSeries.X p) = 0) ∧ ∀ r, F0 (MvPowerSeries.C r) = residue R r :=
    ⟨{ toRingHom := (residue R).comp MvPowerSeries.constantCoeff
       commutes' := fun r => by
         show residue R (MvPowerSeries.constantCoeff (algebraMap R (MvPowerSeries (Fin q × Fin n) R) r)) = _
         rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
           MvPowerSeries.constantCoeff_C, ResidueField.algebraMap_eq] },
     fun p => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.X p)) = 0
       rw [MvPowerSeries.constantCoeff_X, map_zero],
     fun r => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) = _
       rw [MvPowerSeries.constantCoeff_C]⟩
  have hF0X' : ∀ p : Fin q × Fin n, F0 (MvPowerSeries.X p) =
      residue R (ut p.1 p.2) - algebraMap R (ResidueField R) (ut p.1 p.2) := by
    intro p
    rw [hF0X, ResidueField.algebraMap_eq, sub_self]
  obtain ⟨χ', hχ'⟩ := spCo_desc P ut (fun j i => residue R (ut j i)) hχ F0 hF0X'
  have hχ'alg : ∀ r : R, χ' (algebraMap R (Sp P ut) r) = residue R r := by
    intro r
    rw [χ'.commutes, ResidueField.algebraMap_eq]
  have hχ's : Function.Surjective χ' := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχ'alg r⟩
  have hkerχ' : RingHom.ker χ' = maximalIdeal (Sp P ut) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ' hχ's)
  have hχΨ : χ'.comp Ψ = χ := by
    apply MSplitAlg.hom_ext
    intro j i
    rw [AlgHom.comp_apply, hΨ, hχr]
    show χ' (Sp.mk P ut _) = _
    rw [hχ', map_add (f := _), hF0C, hF0X, add_zero]
  have hcomap : Ideal.comap Ψ.toRingHom (maximalIdeal (Sp P ut)) = n0 := by
    refine Ideal.ext fun y => ?_
    rw [Ideal.mem_comap, ← hkerχ', hmem0, RingHom.mem_ker]
    show χ' (Ψ y) = 0 ↔ χ y = 0
    rw [← AlgHom.comp_apply, hχΨ]
  obtain ⟨g0, hg0⟩ := hBuniv (Sp P ut) Ψ.toRingHom hcomap
  have hg0' : ∀ y, g0 (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y := fun y => RingHom.congr_fun hg0 y
  obtain ⟨g, hg⟩ : ∃ g : (Localization.AtPrime n0) →ₐ[R] Sp P ut, ∀ y, g (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y :=
    ⟨{ g0 with
        commutes' := fun r => by
          show g0 (algebraMap R (Localization.AtPrime n0) r) = _
          rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), hg0', Ψ.commutes] }, hg0'⟩
  have hΦu : ∀ j i, Φ (Sp.u P ut j i) = algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i) := by
    intro j i
    show Φ (Sp.mk P ut _) = _
    rw [hΦ, map_add (f := _), hFC', hFX']
    exact add_sub_cancel _ _
  have hΦg : Φ.comp g = AlgHom.id R (Localization.AtPrime n0) := by
    have h1 : (Φ.comp g).comp (IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0)) = IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0) := by
      apply MSplitAlg.hom_ext
      intro j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hg, hΨ, hΦu]
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hBs x
    exact AlgHom.congr_fun h1 y
  haveI : IsCO R (MvPowerSeries (Fin q × Fin n) R) := co_mvps R R (Fin q × Fin n)
  haveI : IsCO R (Sp P ut) := co_quot R (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) (Sp.mk P ut)
    (fun z => Ideal.Quotient.mk_surjective z)
  have hmemSp : ∀ p : Fin q × Fin n, Sp.mk P ut (MvPowerSeries.X p) ∈ maximalIdeal (Sp P ut) := by
    intro p
    rw [← hkerχ', RingHom.mem_ker, hχ', hF0X]
  obtain ⟨F1, -, huniq⟩ := co_ev R R (Sp P ut) (Fin q × Fin n) (Algebra.ofId R (Sp P ut))
    (fun p => Sp.mk P ut (MvPowerSeries.X p)) hmemSp
  have hCalg : ∀ (f : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut) (x : R),
      f (MvPowerSeries.C x) = Algebra.ofId R (Sp P ut) x := by
    intro f x
    have : (MvPowerSeries.C x : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ x := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, f.commutes, Algebra.ofId_apply]
  have hX1 : ∀ p : Fin q × Fin n, ((g.comp Φ).comp (Sp.mk P ut)) (MvPowerSeries.X p) =
      Sp.mk P ut (MvPowerSeries.X p) := by
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hΦ, hFX', map_sub, AlgHom.commutes, hg, hΨ]
    exact (spRoots R q n P ut p.1).2 p.2
  have hgΦ : g.comp Φ = AlgHom.id R (Sp P ut) := by
    apply Ideal.Quotient.algHom_ext
    exact (huniq _ ⟨hCalg _, hX1⟩).trans (huniq _ ⟨hCalg _, fun p => rfl⟩).symm
  let e : Sp P ut ≃ₐ[R] (Localization.AtPrime n0) := AlgEquiv.ofAlgHom Φ g hΦg hgΦ
  refine ⟨inferInstance, Module.Free.of_equiv e.symm.toLinearEquiv, ?_⟩
  rw [eq_top_iff]
  rintro z -
  obtain ⟨y, hy⟩ := hBs (Φ z)
  have hz : Ψ y = z := by
    rw [← hg y, hy]
    exact AlgHom.congr_fun hgΦ z
  rw [← hz]
  clear hz hy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C r =>
    show Ψ (algebraMap R (MSplitAlg P n) r) ∈ _
    rw [Ψ.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | add p1 p2 h1 h2 =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem h1 h2
  | mul_X p s hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp (Algebra.subset_adjoin ⟨s, ?_⟩)
    exact (hΨ s.1 s.2).symm

theorem UpperTheory.V.Pa.Core.spCo :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R), (∀ j, (P j).Monic ∧ (P j).natDegree = n ∧ (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) → IsCO O (Sp P ut) ∧ Module.Free R (Sp P ut) ∧ Module.Finite R (Sp P ut) ∧ Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  intro O R _ _ _ _ _ q n P ut h
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  obtain ⟨hnt, hfree, hadj⟩ := splitting_algebra_nontrivial_free_generated R q n P ut h
  obtain ⟨hfin, -⟩ := BC.sp_fin R q n P ut
  haveI := hnt
  haveI := co_mvps O R (Fin q × Fin n)
  refine ⟨?_, hfree, hfin, hadj⟩
  exact co_quot O (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) ((Sp.mk P ut).restrictScalars O)
    (fun z => Ideal.Quotient.mk_surjective z)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.T3Of
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.t3Of :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (a : W.R), (∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, a - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0)) → IsApproximateAnnihilatorAtLevels m a := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m a h j
  filter_upwards [h j, Λ.U_le (Filter.eventually_ge_atTop j)] with N hN hjN
  obtain ⟨a', ha', hor⟩ := hN
  obtain ⟨hf, hρf, -⟩ := foCong l L G0 T Λ n O r B u J D A W m j N hjN
  refine ⟨(fEl (T.Nq N) W.t.U * a') ^ (A.ex + 1), ?_, ?_⟩
  · have h1 : fo W * a - fEl (T.Nq N) W.t.U * a' ∈ maximalIdeal W.R ^ j := by
      have e : fo W * a - fEl (T.Nq N) W.t.U * a' =
          (fo W - fEl (T.Nq N) W.t.U) * a + fEl (T.Nq N) W.t.U * (a - a') := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ha')
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (fo W * a) (fEl (T.Nq N) W.t.U * a') (A.ex + 1)
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  · intro x
    rw [MN.smul_def, map_pow, map_mul, hρf]
    rcases hor with h0 | h0
    · rw [h0, mul_zero, zero_pow (Nat.succ_ne_zero _), zero_smul]
    · rw [pow_succ', mul_smul]
      exact (congrArg (fun y : (A.A N).M => (fEl (T.Nq N) (A.A N).U * (m.ρ N) a') • y) (h0 x)).trans
        (smul_zero _)
end

