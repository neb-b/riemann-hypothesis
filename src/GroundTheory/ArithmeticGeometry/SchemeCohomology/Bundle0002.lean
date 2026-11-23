module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem ringKrullDim_le_of_hasGoingDown {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.HasGoingDown A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  obtain ⟨P, -, hP, hlo⟩ := (maximalIdeal B).exists_ideal_le_liesOver_of_le
    (p := l.last.asIdeal) (q := maximalIdeal A) (le_maximalIdeal l.last.2.ne_top)
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  exact le_iSup_of_le L (by rw [hlen])

theorem IsRegularLocalRing.of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [IsRegularLocalRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← h]
  calc (((maximalIdeal A).map (algebraMap A B)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal A).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing
    _ = ringKrullDim A := (isRegularLocalRing_iff A).mp inferInstance
    _ ≤ ringKrullDim B := ringKrullDim_le_of_hasGoingDown

theorem isRegularLocalRing_localization_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  apply IsRegularLocalRing.of_flat_of_map_maximalIdeal (A := Localization.AtPrime p)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hmap

theorem isRegularRing_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth (R := k) (S := A)
  obtain ⟨f, hfs, hfq⟩ : ∃ f ∈ s, f ∉ q := by
    by_contra! hc
    exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
  obtain ⟨q', hq', hcomap⟩ : ∃ q' : Ideal (Localization.Away f), q'.IsPrime ∧
      q'.comap (algebraMap A (Localization.Away f)) = q := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) f).mpr hfq
    exact ⟨q.map (algebraMap A (Localization.Away f)),
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ q hq hdisj,
      IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ hq hdisj⟩
  subst hcomap
  suffices IsRegularLocalRing (Localization.AtPrime q') from
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q').toRingEquiv.symm
  have hf := hstd f hfs
  obtain ⟨n, g, -, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap k (Localization.Away f))
    (RingHom.isStandardSmooth_algebraMap.mpr hf)
  algebraize [g]
  exact isRegularLocalRing_localization_of_etale (P := MvPolynomial (Fin n) k) q'

theorem isRegularLocalRing_localization_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  have := isRegularRing_of_smooth k A
  inferInstance

theorem isRegularRing_of_smooth_field (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsRegularRing A :=
  isRegularRing_of_smooth k A

open AlgebraicGeometry CategoryTheory

theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {R : CommRingCat.{u}} [IsRegularRing R]
    (f : X ⟶ Spec R) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsm : (f.appLE ⊤ U (by simp)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have : IsRegularRing Γ(Spec R, ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  set P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hreg : IsRegularLocalRing (Localization.AtPrime P) :=
    isRegularLocalRing_localization_of_smooth Γ(Spec R, ⊤) Γ(X, U) P
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, U)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv

theorem isRegularLocalRing_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth f x

theorem isDomain_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) :=
  have := isRegularLocalRing_stalk_of_smooth_field f x
  IsRegularLocalRing.isDomain

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal RingTheory.Sequence

universe u

variable {R : Type u} [CommRing R]

theorem exists_isRegular_ofList_eq_maximalIdeal [IsRegularLocalRing R] :
    ∃ rs : List R, IsRegular R rs ∧ ofList rs = maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → ∃ rs : List S, IsRegular S rs ∧
        ofList rs = maximalIdeal S ∧ (rs.length : WithBot ℕ∞) = ringKrullDim S from H _ R rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hbot : maximalIdeal S = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hn
    refine ⟨[], IsRegular.nil S S, by simp [hbot], ?_⟩
    rw [← (isRegularLocalRing_iff S).mp inferInstance, hn]
    simp
  | succ n ih =>
    intro S _ _ hn
    have := IsRegularLocalRing.isDomain (R := S)
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      rw [this] at hn; simp at hn
    obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
    have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hB : (maximalIdeal (S ⧸ span {x})).spanFinrank = n := by
      have h1 := (isRegularLocalRing_iff S).mp inferInstance
      have h2 := (isRegularLocalRing_iff (S ⧸ span {x})).mp hreg
      rw [← h1, ← h2, hn] at hdim
      have : ((maximalIdeal (S ⧸ span {x})).spanFinrank + 1 : ℕ) = n + 1 := by exact_mod_cast hdim
      omega
    obtain ⟨rsB, hrsB, hofB, hlenB⟩ := ih (S ⧸ span {x}) hB
    let lift : S ⧸ span {x} → S := Function.surjInv Ideal.Quotient.mk_surjective
    have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
      Function.surjInv_eq Ideal.Quotient.mk_surjective
    let rs' := rsB.map lift
    have hmap : rs'.map (Ideal.Quotient.mk (span {x})) = rsB := by
      simp [rs', List.map_map, Function.comp_def, hlift]
    refine ⟨x :: rs', ?_, ?_, ?_⟩
    · rw [isRegular_cons_iff']
      refine ⟨?_, ?_⟩
      · exact fun a b h ↦ mul_left_cancel₀ hx0 h
      · rw [hmap]
        have e0 : QuotSMulTop x S ≃ₗ[S] S ⧸ span {x} :=
          Submodule.quotEquivOfEq _ _ (by
            rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
        let e : QuotSMulTop x S ≃ₗ[S ⧸ span {x}] S ⧸ span {x} :=
          LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e0
        exact (e.isRegular_congr rsB).mpr hrsB
    · have h1 : (ofList rs').map (Ideal.Quotient.mk (span {x})) =
          (maximalIdeal S).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_ofList, hmap, hofB,
          map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) h1
      simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h2
      rw [ofList_cons, sup_comm, h2, sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr hx)]
    · rw [List.length_cons, List.length_map, ← hdim, ← hlenB]
      push_cast
      rfl

open CategoryTheory Abelian

theorem hasProjectiveDimensionLT_of_forall_prime [IsNoetherianRing R] (n : ℕ) (I : Ideal R)
    (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ q)) n)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  revert hM
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    with
  | subsingleton N =>
    intro _
    have : Limits.IsZero (ModuleCat.of R N) := ModuleCat.isZero_of_subsingleton _
    have := this.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le _)
  | quotient N p e =>
    intro hN
    have hle : I ≤ p.1 := by
      intro a ha
      have h := congrArg e (hN a ha (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    have := hI p.1 p.2 hle
    exact hasProjectiveDimensionLT_of_iso e.symm.toModuleIso n
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    have k₁ : ∀ a ∈ I, ∀ m : N₁, a • m = 0 := fun a ha m ↦ hf (by rw [map_smul, hN a ha, map_zero])
    have k₃ : ∀ a ∈ I, ∀ m : N₃, a • m = 0 := fun a ha m ↦ by
      obtain ⟨m, rfl⟩ := hg m
      rw [← map_smul, hN a ha, map_zero]
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero f g (LinearMap.ext fun x ↦ hfg.apply_apply_eq_zero x))
      hfg hf hg
    exact hS.hasProjectiveDimensionLT_X₂ n (h₁ k₁) (h₃ k₃)

theorem hasProjectiveDimensionLT_residueField [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) :
    HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) := by
  obtain ⟨rs, hreg, hof, hlen⟩ := exists_isRegular_ofList_eq_maximalIdeal (R := R)
  have hrs : rs.length = d := by rw [hd] at hlen; exact_mod_cast hlen
  have h := ModuleCat.projectiveDimension_quotient_eq_length.{u} (R := R) rs hreg
  have h' : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ ofList rs))) d :=
    (projectiveDimension_le_iff _ d).mp (by rw [h, hrs])
  let e : Shrink.{u} (R ⧸ ofList rs) ≃ₗ[R] R ⧸ maximalIdeal R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hof)
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)


set_option backward.isDefEq.respectTransparency false in
theorem hasProjectiveDimensionLT_of_residueField [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by
  have hprime : ∀ p : Ideal R, p.IsPrime →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ p)) (n + 1) := by
    intro p
    induction p using WellFoundedGT.induction with
    | _ p ih =>
    intro hp
    by_cases hpm : p = maximalIdeal R
    · subst hpm; exact hk
    · have hlt : p < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm
      obtain ⟨x, hxm, hxp⟩ := Set.exists_of_ssubset hlt
      let N := R ⧸ p
      have hx0 : Ideal.Quotient.mk p x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have reg : IsSMulRegular N x := by
        intro a b h
        simp only [Algebra.smul_def] at h
        exact mul_left_cancel₀ hx0 h
      have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R N) reg
      have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x N)) (n + 1) := by
        refine hasProjectiveDimensionLT_of_forall_prime (n + 1) (p ⊔ span {x}) ?_ _ ?_
        · intro q hq hle
          exact ih q (lt_of_le_of_ne (le_sup_left.trans hle) (fun h ↦ hxp (h ▸
            hle (le_sup_right (a := p) ((span_singleton_le_iff_mem _).mp le_rfl))))) hq
        · intro a ha m
          have hann : p ⊔ span {x} ≤ Module.annihilator R (QuotSMulTop x N) := by
            refine sup_le ?_ ((span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator N x))
            intro b hb
            rw [Module.mem_annihilator]
            intro m
            obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
            obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
            rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
              Ideal.Quotient.eq_zero_iff_mem.mpr (p.mul_mem_right m hb), map_zero]
          exact Module.mem_annihilator.mp (hann ha) m
      apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton
        (ModuleCat.of R (QuotSMulTop x N)) (n + 1) (n + 2) (by omega) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : (ModuleCat.smulShortComplex (ModuleCat.of R N) x).f = x • 𝟙 (ModuleCat.of R N) := rfl
      simp only [this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext (ModuleCat.of R N) L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) hxm
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  exact hasProjectiveDimensionLT_of_forall_prime (n + 1) ⊥ (fun q hq _ ↦ hprime q hq) M
    (fun a ha m ↦ by rw [(Submodule.mem_bot R).mp ha, zero_smul])

theorem hasProjectiveDimensionLT_of_isRegularLocalRing [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) :=
  hasProjectiveDimensionLT_of_residueField d (hasProjectiveDimensionLT_residueField hd) M

end GroundTheory.Arith.SchemeCoh
end

