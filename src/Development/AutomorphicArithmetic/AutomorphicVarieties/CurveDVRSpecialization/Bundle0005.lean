module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
section
private theorem exists_element_separating_powers {G K : Type} [Group G] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l] {n : ℕ}
    (ψ : Fin n → G →* (PowerSeries K)ˣ) (N V : Subgroup G) (hV : V.index ≠ 0)
    (hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (ψ a g : PowerSeries K) =
      PowerSeries.constantCoeff (ψ b g : PowerSeries K))
    (hsep : ∀ a b, a ≠ b → ∃ g ∈ N, ψ a g ≠ ψ b g) :
    ∃ g ∈ N, g ∈ V ∧ ∀ a b, a ≠ b → ∀ m : ℕ, 0 < m → ψ a g ^ m ≠ ψ b g ^ m := by
  haveI : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C_injective (R := K)) l
  have tf : ∀ g ∈ N, ∀ a b (m : ℕ), 0 < m → (ψ a g / ψ b g) ^ m = 1 → ψ a g / ψ b g = 1 := by
    intro g hg a b m hm h
    apply Units.ext
    apply UpperTheory.V.Pr.T.oneUnitTF l _ m hm.ne'
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff ((ψ b g)⁻¹ : (PowerSeries K)ˣ).val *
          PowerSeries.constantCoeff ((ψ b g : (PowerSeries K)ˣ) : PowerSeries K) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hc : PowerSeries.constantCoeff (((ψ a g / ψ b g : (PowerSeries K)ˣ) : PowerSeries K) - 1) = 0 := by
        rw [map_sub, div_eq_mul_inv, Units.val_mul, map_mul, hred g hg a b, mul_comm, hinv, map_one, sub_self]
      rw [hc]
      exact not_isUnit_zero
    · rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  let χ : {p : Fin n × Fin n // p.1 ≠ p.2} → ↥(N ⊓ V) →* (PowerSeries K)ˣ :=
    fun p => (ψ p.1.1 / ψ p.1.2).comp (N ⊓ V).subtype
  obtain ⟨h, hh⟩ := UpperTheory.V.Pr.commonFree ↥(N ⊓ V) (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2} χ 1 one_pos
    (by
      intro p h m hm hpow
      rw [pow_one]
      exact tf h (Subgroup.mem_inf.mp h.2).1 _ _ m hm hpow)
    (by
      intro p
      obtain ⟨g, hgN, hne⟩ := hsep _ _ p.2
      obtain ⟨k, hk, -, hkV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hV g
      refine ⟨⟨g ^ k, Subgroup.mem_inf.mpr ⟨N.pow_mem hgN k, hkV⟩⟩, ?_⟩
      rw [pow_one]
      intro h1
      apply hne
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) ^ k = 1 := by
        simpa [χ, div_pow, map_pow] using h1
      exact div_eq_one.mp (tf g hgN _ _ k hk h2))
  refine ⟨h, (Subgroup.mem_inf.mp h.2).1, (Subgroup.mem_inf.mp h.2).2, ?_⟩
  intro a b hab m hm heq
  apply hh ⟨(a, b), hab⟩ m hm
  simp [χ, div_pow, heq]

theorem UpperTheory.V.Pr.niceSep :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → ∀ v, ∃ g : T.G.Gv v, T.G.φ v g ∈ U ⊓ T.G.G' ∧ UpperTheory.V.Pr.FreeRatios fun i => y.ψ v i g |> Units.map (algebraMap y.A y.Fr).toMonoidHom := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hmat hψ U hU v
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char
  haveI : CharP y.K l :=
    charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) y.K).injective l
  let N : Subgroup (T.G.Gv v) := (F.Nv (T.K.e v)).comap (T.K.lam v).toMonoidHom
  let V : Subgroup (T.G.Gv v) := U.comap (T.G.φ v)
  have hV : V.index ≠ 0 := by
    rw [Subgroup.index_ne_zero_iff_finite]
    exact Subgroup.quotient_finite_of_isOpen V (hU.preimage (T.G.φ_cont v))
  have hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (y.ψ v a g : PowerSeries y.K) =
      PowerSeries.constantCoeff (y.ψ v b g : PowerSeries y.K) := by
    intro g hg a b
    have key : ∀ i, PowerSeries.constantCoeff (y.ψ v i g : PowerSeries y.K) =
        algebraMap (IsLocalRing.ResidueField O) y.K (T.r.psib v i g : IsLocalRing.ResidueField O) :=
      fun i => congrArg Units.val (DFunLike.congr_fun (y.ψ_red v i) g)
    have hΨ : F.Ψ ((F.loc0 (T.K.e v) (T.K.lam v g) : F.del.ker) : F.Γ) = 1 :=
      T.ok.Ψ_N (T.K.e v) (T.K.lam v g) hg
    rw [key a, key b, T.K.psib, T.K.psib, T.K.chib, T.K.chib, ← T.K.lam_loc, hΨ, one_zpow, one_zpow]
  have hsep : ∀ a b, a ≠ b → ∃ g ∈ N, y.ψ v a g ≠ y.ψ v b g := by
    intro a b hab
    have hc := hnice.sep (T.K.e v) a b hab
    simp only [UpperTheory.V.Fr.NRep.Coin, not_forall] at hc
    obtain ⟨g', hg', hne⟩ := hc
    refine ⟨(T.K.lam v).symm g', ?_, ?_⟩
    · show (T.K.lam v) ((T.K.lam v).symm g') ∈ F.Nv (T.K.e v)
      simpa using hg'
    · intro heq
      apply hne
      rw [hψ] at heq
      simp only [UpperTheory.V.Pr.TwLink.twψ, MonoidHom.mul_apply, MonoidHom.comp_apply] at heq
      have h2 := congrArg Units.val (mul_right_cancel heq)
      simp [UpperTheory.V.Fr.NRep.map] at h2
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      convert h2 using 4
      all_goals exact ((T.K.lam v).apply_symm_apply g').symm
  obtain ⟨g, hgN, hgV, hfree⟩ := exists_element_separating_powers l (y.ψ v) N V hV hred hsep
  refine ⟨g, ⟨hgV, ?_⟩, ?_⟩
  · show T.G.ε ((T.G.φ v g : T.G.η.ker) : T.G.Γ) = 1
    rw [← T.K.π_eps, ← T.K.lam_loc]
    exact (Subgroup.mem_inf.mp hgN).2
  · intro a b hab m hm heq
    apply hfree a b hab m hm
    apply Units.ext
    apply IsFractionRing.injective y.A y.Fr
    have h2 := congrArg Units.val heq
    simpa [Units.val_pow_eq_pow_val, map_pow] using h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StableOf
section
open IsLocalRing UpperTheory.V.Fr

private theorem exists_field_embedding_of_domain (D : Type) [CommRing D] [IsDomain D] :
    ∃ (K : Type) (_ : Field K) (j : D →+* K), Function.Injective j := by
  set_option synthInstance.maxHeartbeats 400000 in
  exact ⟨FractionRing D, inferInstance, algebraMap D _, IsFractionRing.injective D (FractionRing D)⟩

private theorem exists_algClosed_embedding_of_field (F : Type) [Field F] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : F →+* K), Function.Injective j :=
  ⟨AlgebraicClosure F, inferInstance, inferInstance, algebraMap F _, RingHom.injective _⟩

private theorem exAlgCl0 (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : R →+* K), RingHom.ker j = P := by
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨K0, hK0, j0, hj0⟩ := exists_field_embedding_of_domain (R ⧸ P)
  obtain ⟨K, hK, hc, j, hj⟩ := exists_algClosed_embedding_of_field K0
  refine ⟨K, hK, hc, (j.comp j0).comp (Ideal.Quotient.mk P), ?_⟩
  have hinj : Function.Injective (j.comp j0) := fun a b h => hj0 (hj h)
  rw [RingHom.ker_comp_of_injective _ hinj, Ideal.mk_ker]

private theorem exAlgCl (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra O K) (j : R →ₐ[O] K), RingHom.ker (j : R →+* K) = P := by
  obtain ⟨K, hK, hc, j, hj⟩ := exAlgCl0 R P
  letI : Algebra O K := (j.comp (algebraMap O R)).toAlgebra
  exact ⟨K, hK, hc, inferInstance, ⟨j, fun _ => rfl⟩, hj⟩

private theorem ringHom_injective_of_fields {F K : Type} [Field F] [Field K] (g : F →+* K) :
    Function.Injective g :=
  RingHom.injective _

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Pr.stableOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.StableOf := by
  intro l _ O _ _ _ _ _ F n T
  unfold UpperTheory.V.Pr.Setup.StableOf
  intro Φ hΦ x L P _ hTI
  have hn := T.n23
  have hok := T.ok
  obtain ⟨K, hK, hc, _, j, hj⟩ := exAlgCl O L.R P
  let f : T.S.A →ₐ[O] K := j.comp L.ι
  have hkerf : RingHom.ker (f : T.S.A →+* K) = L.im P := by
    show RingHom.ker ((j : L.R →+* K).comp (L.ι : T.S.A →+* L.R)) =
      Ideal.comap (L.ι : T.S.A →+* L.R) P
    rw [← RingHom.comap_ker, hj]
  have hloc := (loc_rho hok hn T.S x L).2.2.1 P
  have hTIS : T.S.u.TI (RingHom.ker (f : T.S.A →+* K)) := by
    rw [hkerf]
    unfold NRep.TI NRep.OffTri at hTI ⊢
    exact ⟨⟨fun h => hTI.1.1 (hloc.1.mpr h), fun h => hTI.1.2 (hloc.2.1.mpr h)⟩,
      fun h3 h => hTI.2 h3 (hloc.2.2.mpr h)⟩
  have hirr := ((types hok hn T.S K (f : T.S.A →+* K)).1).mpr hTIS
  have hirr2 := T.K.tw_irr (NRep.map (f : T.S.A →+* K) T.S.u) hirr
  have hΦ' : T.K.IsPhi T.B T.S Φ := hΦ
  have hm := UpperTheory.V.Pr.TwLink.IsPhi.maps T.K hΦ' f
  unfold UpperTheory.V.W.Pair.Maps at hm
  have hL : RingHom.ker ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K) =
      Ideal.comap ((T.phi Φ L) : T.B.B →+* L.R) P := by
    show RingHom.ker ((j : L.R →+* K).comp ((T.phi Φ L) : T.B.B →+* L.R)) = _
    rw [← RingHom.comap_ker, hj]
  have hR : RingHom.ker (T.B.toKap (T.back Φ L P)) = (T.back Φ L P).asIdeal := by
    unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.toKap
    refine (RingHom.ker_comp_of_injective _ (ringHom_injective_of_fields _)).trans ?_
    exact Ideal.ker_algebraMap_residueField _
  unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.IsStable
  refine UpperTheory.V.CA.stable_field T.B.u.D ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K)
    (T.B.toKap (T.back Φ L P)) ?_ ⟨_, hirr2, hm.1⟩
  rw [hL, hR]
  rfl
end

