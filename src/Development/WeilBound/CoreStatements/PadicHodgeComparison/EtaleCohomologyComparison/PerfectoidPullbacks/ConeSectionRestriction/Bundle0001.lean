module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsIntegralNbhd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_integral_nbhd {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [Smooth q]
    (hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S)
    (x : X) : ∃ W : X.Opens, x ∈ W ∧ IsIntegral W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ q ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hsm := q.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of K))) hV hVU
  let φ : K →+* Γ(X, V) :=
    (q.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    hsm
  let := φ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hφ
  obtain ⟨r, hr, hdom⟩ := hE Γ(X, V) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxW : x ∈ X.basicOpen r := by
    rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hr
  refine ⟨X.basicOpen r, hxW, ?_⟩
  have hW : IsAffineOpen (X.basicOpen r) := hV.basicOpen r
  have : IsAffine (X.basicOpen r) := hW
  have : Nonempty (X.basicOpen r) := ⟨⟨x, hxW⟩⟩
  let := (X.presheaf.map (homOfLE <| X.basicOpen_le r).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen r
  have : IsDomain Γ(X, X.basicOpen r) := hdom _
  have : IsDomain Γ(X.basicOpen r, ⊤) :=
    (X.basicOpen r).topIso.commRingCatIsoToRingEquiv.injective.isDomain
      (X.basicOpen r).topIso.commRingCatIsoToRingEquiv
  exact isIntegral_of_isAffine_of_isDomain _

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsTmulOneEqOfIsIntegral
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem isIntegral_of_mul_self_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S}
    (he : e * e = e) : IsIntegral R e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, mul_sub, he]

theorem exists_tmul_one_eq_of_isIntegral {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Smooth P A] (t : A ⊗[P] FractionRing P)
    (ht : IsIntegral A t) : ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = t := by
  obtain ⟨u, hu⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := A)
    (B := FractionRing P)).2 ⟨t, ht⟩
  have key : ∀ u : A ⊗[P] integralClosure P (FractionRing P), ∃ a : A,
      a ⊗ₜ[P] (1 : FractionRing P) =
        ((TensorProduct.toIntegralClosure P A (FractionRing P) u : _) : A ⊗[P] FractionRing P) := by
    intro u
    induction u with
    | tmul a y =>
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp y.2
      refine ⟨p • a, ?_⟩
      change _ = a ⊗ₜ[P] (y : FractionRing P)
      rw [TensorProduct.smul_tmul, ← hp, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add (f := _), Subalgebra.coe_add]⟩
  obtain ⟨a, ha⟩ := key u
  exact ⟨a, by rw [ha, hu]⟩

theorem exists_away_isDomain_of_etale {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Etale P A] (q : Ideal A) [q.IsPrime] :
    ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical

  have hι : Function.Injective (fun a : A => a ⊗ₜ[P] (1 : FractionRing P)) := by
    have hinj : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
      IsFractionRing.injective P (FractionRing P)
    have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (Algebra.linearMap P (FractionRing P)) hinj
    intro a b hab
    apply (TensorProduct.rid P A).symm.injective
    apply h2
    simpa using hab

  obtain ⟨I, hI, Ai, hAi, hAlg, e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing P) (FractionRing P ⊗[P] A)).mp
      inferInstance
  have := Fintype.ofFinite I
  let φ : A ⊗[P] FractionRing P ≃+* (Π i, Ai i) :=
    (Algebra.TensorProduct.comm P A (FractionRing P)).toRingEquiv.trans e.toRingEquiv

  have hε : ∀ i, ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = φ.symm (Pi.single i 1) := by
    intro i
    refine exists_tmul_one_eq_of_isIntegral _ (isIntegral_of_mul_self_eq ?_)
    rw [← map_mul, ← Pi.single_mul, one_mul]
  choose a ha using hε

  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ∉ q := by
    by_contra! h
    have hsum : (∑ i, a i) ∈ q := Ideal.sum_mem q fun i _ => h i
    have h1 : (∑ i, a i) = 1 := by
      apply hι
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [TensorProduct.sum_tmul, Finset.sum_congr rfl (fun i _ => ha i), ← map_sum,
        Finset.univ_sum_single]
      exact map_one φ.symm
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).2 (h1 ▸ hsum))
  refine ⟨a i₀, hi₀, ?_⟩

  let F : A →+* Ai i₀ := (Pi.evalRingHom Ai i₀).comp
    (φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom))
  have hF : ∀ x : A, F x = φ (x ⊗ₜ[P] (1 : FractionRing P)) i₀ := fun x => rfl
  have hFg : IsUnit (F (a i₀)) := by
    rw [hF, ha, RingEquiv.apply_symm_apply, Pi.single_eq_same]
    exact isUnit_one
  let ψ : Localization.Away (a i₀) →+* Ai i₀ := IsLocalization.Away.lift (a i₀) hFg
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (a i₀)) x
    have hspec := IsLocalization.mk'_spec (Localization.Away (a i₀)) y s
    have hFy : F y = 0 := by
      have h3 := congrArg ψ hspec
      rw [map_mul, hx, zero_mul] at h3
      have h4 : ψ (algebraMap A (Localization.Away (a i₀)) y) = F y := IsLocalization.lift_eq _ _
      rw [← h4, ← h3]
    have hyg : y * a i₀ = 0 := by
      apply hι
      simp only
      have hmul : (y * a i₀) ⊗ₜ[P] (1 : FractionRing P) =
          (y ⊗ₜ[P] (1 : FractionRing P)) * (a i₀ ⊗ₜ[P] (1 : FractionRing P)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, zero_tmul]
      apply φ.injective
      rw [map_mul, ha, RingEquiv.apply_symm_apply, map_zero]
      funext k
      by_cases hk : k = i₀
      · subst hk
        simp only [Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply]
        exact hFy
      · simp [Pi.mul_apply, Pi.single_eq_of_ne hk]
    have hy0 : algebraMap A (Localization.Away (a i₀)) y = 0 := by
      have h5 := congrArg (algebraMap A (Localization.Away (a i₀))) hyg
      rw [map_mul, map_zero] at h5
      exact (IsUnit.mul_left_eq_zero (IsLocalization.Away.algebraMap_isUnit (a i₀))).1 h5
    rw [← hspec] at hy0
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units _ s)).1 hy0
  exact hψ.isDomain ψ

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IrreducibleSpaceOfConnectedOfLocally
section
set_option autoImplicit false

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem irreducibleSpace_of_connected_of_locally {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    (h : ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) : IrreducibleSpace α := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hU, hzU, hUirr⟩ := h z
    refine ⟨U, ?_, hU, hzU⟩
    have h1 : irreducibleComponent x₀ ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen isIrreducible_irreducibleComponent.2 hU
        ⟨z, hz, hzU⟩).trans (closure_mono Set.inter_subset_right)
    have h2 : closure U = irreducibleComponent x₀ := eq_irreducibleComponent hUirr.closure.2 h1
    exact subset_closure.trans h2.le
  have hclopen : IsClopen (irreducibleComponent x₀) := ⟨isClosed_irreducibleComponent, hopen⟩
  have huniv : irreducibleComponent x₀ = Set.univ := hclopen.eq_univ ⟨x₀, mem_irreducibleComponent⟩
  have hirr : IsIrreducible (Set.univ : Set α) := huniv ▸ isIrreducible_irreducibleComponent
  exact (irreducibleSpace_def α).2 hirr

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {d : ℕ}

def tpow (t : Fin d → Rˣ) (m : Fin d → ℤ) : R := ((∏ k, t k ^ m k : Rˣ) : R)

def expS (S : Finset (Fin (d + 1))) : Set (Fin d → ℤ) :=
  {m | (∀ k : Fin d, k.succ ∉ S → 0 ≤ m k) ∧ ((0 : Fin (d + 1)) ∉ S → ∑ k, m k ≤ 0)}


variable (K) in
def torusS (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) : Subalgebra K R := Algebra.adjoin K (tpow t '' expS S)

def jacS (B : Subalgebra K R) (D : Fin d → Derivation K R R) {m : ℕ} (κ : Fin m → Fin d) : AddSubgroup R :=
  AddSubgroup.closure {y | ∃ (b : B) (bs : Fin m → B), y = (b : R) * (Matrix.of fun k l => D (κ k) (bs l)).det}

end CrystallineSemistableComparison.Pb
end
end

