module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteVerticalGaussValuations

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  change (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
    ((algebraMap F (InfiniteAdeleRing F) t) _) = σ t
  rw [InfiniteAdeleRing.algebraMap_apply]
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp


open Classical in
noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := _root_.GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPtOrdEqAddValuation
section
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

def valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) : Ideal S where
  carrier := {a | 0 < u (a : A)}
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) (b : A)
    exact lt_of_lt_of_le (lt_min ha hb) this
  zero_mem' := by
    change 0 < u ((0 : S) : A)
    simp
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * (a : A))
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (h0 _ c.2))

theorem mem_valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl

theorem valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))

theorem addVal_eq_of_associated_loc {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3

theorem exists_pt_ord_eq_addValuation : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif (A := A) ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] (u : AddValuation A (WithTop ℤ)), (∀ a ∈ As O A, 0 ≤ u a) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a, ord ϖ ζ a = u a := by
  intro O A _ _ _ _ _ ϖ h hD u h0 hϖ h1
  haveI hP := valCentreOn_isPrime (As O A) u h0
  have hcm : ((valCentreOn (As O A) u h0).comap (algebraMap O (As O A))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤
        (valCentreOn (As O A) u h0).comap (algebraMap O (As O A)) := by
      rw [h.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
        mem_valCentreOn]
      exact hϖ
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
    rw [← this]
    infer_instance
  have hmax : (valCentreOn (As O A) u h0).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) _ hcm
  let ζ : Pts O A := ⟨valCentreOn (As O A) u h0, hmax⟩
  have hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0 := fun s hs =>
    le_antisymm (not_lt.1 hs) (h0 _ s.2)
  refine ⟨ζ, ?_⟩
  haveI : IsDVRAt ζ := hD ζ
  haveI : IsDomain (Loc ζ) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ) := IsDVRAt.isDVR
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj ζ.asIdeal.primeCompl p
  have hπ : Irreducible (algebraMap (As O A) (Loc ζ) π) := by
    have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
    have : Associated p (algebraMap (As O A) (Loc ζ) π) := ⟨ht.unit, hπt⟩
    exact this.irreducible hp
  have hπpos : 0 < u (π : A) := by
    by_contra hc
    exact hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)
  have key : ∀ a : As O A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨
      ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A) := by
    intro a
    by_cases ha : algebraMap (As O A) (Loc ζ) a = 0
    · refine Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩
      rw [addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]
      simp
    · obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine Or.inr ⟨n, ?_, ?_⟩
      · rw [vL_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def _ w hπ n hw
      · rw [addVal_eq_of_associated_loc ζ u hz a (π ^ n)
          (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]
        rw [SubmonoidClass.coe_pow, u.map_pow]
  have hϖtop : u (algebraMap O A ϖ) ≠ ⊤ := by
    intro ht
    obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
    have := congrArg u hv
    rw [u.map_mul, ht, top_add, u.map_one] at this
    exact WithTop.top_ne_zero this
  have hϖe : u (algebraMap O A ϖ) = ep ϖ ζ • u (π : A) := by
    rcases key (algebraMap O (As O A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩
    · exact absurd h2 hϖtop
    · rw [← coe_ep ζ h, Nat.cast_inj] at h2
      rw [h2]
      exact h3
  have hmtop : u (π : A) ≠ ⊤ := by
    intro ht
    apply hϖtop
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖe, hk, succ_nsmul, ht, add_top]
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hmtop
  have hM0 : 0 < M := by
    rw [← hM] at hπpos
    exact_mod_cast hπpos
  have key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨k, hk⟩ := h.denom x
    have e1 := ord_pow_smul ζ h k x
    rw [ord_of_mem ζ h hk] at e1
    have e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
    rcases key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩
    · left
      rw [h2, ENat.map_top, eq_comm, WithTop.add_eq_top] at e1
      change u (ϖ ^ k • x) = ⊤ at h3
      rw [h3, eq_comm, WithTop.add_eq_top] at e2
      exact ⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩
    · right
      rw [h2, ENat.map_natCast] at e1
      change u (ϖ ^ k • x) = _ at h3
      rw [h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul] at e2
      refine ⟨n - k * ep ϖ ζ, ?_, ?_⟩
      · generalize ord ϖ ζ x = y at e1
        cases y with
        | top => simp at e1
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e1
          rw [WithTop.coe_inj]
          linarith
      · generalize u x = y at e2
        cases y with
        | top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e2
          rw [WithTop.coe_inj]
          linarith
  have hM1 : M = 1 := by
    obtain ⟨a, ha⟩ := h1
    rcases key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩
    · rw [ha] at h3
      exact absurd h3 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h3
      exact Int.eq_one_of_mul_eq_one_left hM0.le h3.symm
  intro a
  rcases key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3, hM1, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRingHomTensorOmSOfPoint
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_ringHom_tensor_OmS_of_point :
    ∀ (K Ω K' U : Type) [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Field U] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K'] (κ : K' →+* U) (τ : Ω →+* U) (T : ReciprocityTheory.ChartRestriction.G.T0.TVar D N → K'), Algebra.trdeg K Ω = D → (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ p, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.X p)) = T p) → (∀ a : K, τ (algebraMap K Ω a) = κ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.C a)))) → (∀ i : Fin D, κ (T (i.succ, j₀)) + ∑ k, κ (T (i.succ, j₀.succAbove k)) * τ (x k) = 0) → ∃ χ : K' ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* U, (∀ a : K', χ (a ⊗ₜ 1) = κ a) ∧ ∀ ω : Ω, χ (1 ⊗ₜ algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) ω) = τ ω := by
  intro K Ω K' U _ _ _ _ _ D N j₀ x _ _ κ τ T hD hS hT hC hrel
  classical
  letI : Algebra K U := (τ.comp (algebraMap K Ω)).toAlgebra
  have hKU : ∀ a : K, algebraMap K U a = τ (algebraMap K Ω a) := fun _ => rfl
  let φ : Ω →ₐ[K] U := { τ with commutes' := fun _ => rfl }
  let g : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →+* U :=
    κ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').comp
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hg : Function.Injective g :=
    κ.injective.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').injective.comp
      (IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hgC : ∀ a : K, g (MvPolynomial.C a) = τ (algebraMap K Ω a) := fun a => (hC a).symm
  have hgX : ∀ p, g (MvPolynomial.X p) = κ (T p) := fun p => congrArg κ (hT p)
  have hind : AlgebraicIndependent K (fun p => κ (T p)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC]
        simp [hKU]
      · intro p
        rw [hgX]
        simp
    have h2 : Function.Injective (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom := this ▸ hg
    exact h2
  obtain ⟨P, ⟨hP1, hP2⟩, -⟩ :=
    GlobalTheory.existsUnique_ringHom_OmS K Ω U D N j₀ x (fun p => κ (T p)) φ hD hind hrel
  have hP1' : ∀ a : Ω, P (algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = τ a := hP1
  have key : P.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)) =
      κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K') := by
    apply IsFractionRing.ringHom_ext (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N)
    intro q
    have : P.comp (ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) (D := D) j₀ x).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC, ← hP1', ← IsScalarTower.algebraMap_apply]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
      · intro p
        rw [hgX, ← hP2]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
    rw [RingHom.comp_apply, hS]
    exact DFunLike.congr_fun this q
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) U :=
    (κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K')).toAlgebra
  let κ' : K' →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U := { κ with commutes' := fun _ => rfl }
  let P' : ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U :=
    { P with commutes' := fun r => DFunLike.congr_fun key r }
  refine ⟨(Algebra.TensorProduct.productMap κ' P').toRingHom, fun a => ?_, fun ω => ?_⟩
  · change Algebra.TensorProduct.productMap κ' P' (a ⊗ₜ 1) = κ a
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  · change Algebra.TensorProduct.productMap κ' P' (1 ⊗ₜ _) = τ ω
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    exact hP1' ω

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAndDensityAndAemeasurable
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_support_and_density_and_aemeasurable :
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite) ∧ (∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε) ∧ (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure) :=
  ⟨finite_support_admissible finite_vertical_gauss_valuations finite_zeros_poles_of_trdeg_one,
    generic_points_dense exists_algIndep_tuple_near,
    aemeasurable_finsum_section ae_eval₂_ne_zero_pi_toSphere
      (measurable_sum_embeddings_over_generic_point exists_measurable_roots_enumeration)
      existsUnique_ringHom_OmS⟩

end GlobalTheory
end

