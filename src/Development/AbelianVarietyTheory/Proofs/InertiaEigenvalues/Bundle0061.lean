module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.NormUnits

theorem group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose S hS using fun i => Group.fg_iff.mp (hG i)
  refine Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_,
    Set.finite_iUnion fun i => (hS i).2.image _⟩
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_prod_mulSingle x]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hx : x i ∈ Subgroup.closure (S i) := by rw [(hS i).1]; trivial
  have h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i) :=
    ⟨x i, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  exact Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1

theorem isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  choose p hpm hp using hx
  refine ⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩
  rw [← aeval_def]
  apply (IsArtinianRing.equivPi A).injective
  funext J
  rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ J) ?_
  have h2 := aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h2
  rw [← h2, aeval_def]
  exact hp J

theorem units_quot_intUnits_fg : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L]
    [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) →
    ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A]
    [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  intro K hL A _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A
  have := Fintype.ofFinite (MaximalSpectrum A)

  have hfg : ∀ I : MaximalSpectrum A,
      Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hL (A ⧸ I.asIdeal)
  have hP := group_fg_pi (fun I : MaximalSpectrum A =>
    (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg
  let ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal) :=
    MonoidHom.pi fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hsurj : Function.Surjective ψ := by
    intro c
    choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)
    let e := IsArtinianRing.equivPi A
    refine ⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A)
      (MulEquiv.piUnits.symm u), ?_⟩
    funext I
    rw [← hu I]
    change QuotientGroup.mk' _ _ = _
    congr 1
    ext
    have h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal,
        Ideal.Quotient.mk I.asIdeal (e.symm z) = z I := fun z => by
      rw [← IsArtinianRing.equivPi_apply A (e.symm z) I]
      exact congrFun (e.apply_symm_apply z) I
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [h3]
    rfl
  have hker : ψ.ker ≤ intUnits K.O A := by
    intro t ht
    have hI : ∀ I : MaximalSpectrum A,
        Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal) :=
      fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)
    refine ⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1,
      NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩
    have := (hI I).2
    rwa [Units.coe_map_inv] at this
  haveI : Group.FG (Aˣ ⧸ ψ.ker) :=
    Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨QuotientGroup.mk y, rfl⟩

end GlobalTheory.UnitLemma.NormUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover
section
noncomputable section

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

def dcSetoid (Γ K : Subgroup G) : Setoid G := GlobalTheory.DoubleCosetSetoid.doubleCosetSetoid Γ K

abbrev DC (Γ K : Subgroup G) : Type _ := Quotient (dcSetoid Γ K)

def stabCard (Γ K : Subgroup G) (t : G) : ℕ := Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}

def mass (Γ K : Subgroup G) : ℚ := ∑ᶠ c : DC Γ K, ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹

theorem finite_dc_of_le {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by
  let f : DC Γ W → DC Γ K := Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
  refine Finite.of_surjective f ?_
  rintro ⟨x⟩
  exact ⟨Quotient.mk'' x, rfl⟩

theorem finite_dc_of_cover {Γ K : Subgroup G} (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ κ ∈ K, g = γ * t * κ) :
    Finite (DC Γ K) := by
  obtain ⟨T, hT⟩ := hT
  refine Finite.of_surjective (fun t : T => (Quotient.mk'' (t : G) : DC Γ K)) ?_
  rintro ⟨g⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g
  refine ⟨⟨t, ht⟩, Quotient.sound' ⟨γ, hγ, κ, hκ, e⟩⟩

theorem stabCard_pos {Γ K : Subgroup G} (t : G) (h : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    0 < stabCard Γ K t := by
  haveI := h
  haveI : Nonempty {γ : Γ // t⁻¹ * (γ : G) * t ∈ K} := ⟨⟨1, by simp [K.one_mem]⟩⟩
  exact Nat.card_pos

theorem mass_pos {Γ K : Subgroup G} [Finite (DC Γ K)]
    (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) : 0 < mass Γ K := by
  haveI := Fintype.ofFinite (DC Γ K)
  rw [mass, finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (DC Γ K)).Nonempty := ⟨Quotient.mk'' 1, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun c _ => ?_) hne
  have := stabCard_pos c.out (hfin c.out)
  positivity

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

theorem stabCard_eq {Γ K : Subgroup G} {t t' : G} (hr : (dcSetoid Γ K) t t') :
    stabCard Γ K t' = stabCard Γ K t := by
  obtain ⟨γ, hγ, κ, hκ, rfl⟩ := hr
  unfold stabCard
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨γ⁻¹ * (x.1 : G) * γ, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) x.1.2) hγ⟩, ?_⟩
      invFun := fun x => ⟨⟨γ * (x.1 : G) * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ x.1.2) (Γ.inv_mem hγ)⟩, ?_⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  · have := K.mul_mem (K.mul_mem hκ x.2) (K.inv_mem hκ)
    convert this using 1
    simp [mul_assoc]
  · have := K.mul_mem (K.mul_mem (K.inv_mem hκ) x.2) hκ
    convert this using 1
    simp [mul_assoc]

theorem stabCard_out (Γ K : Subgroup G) (x : G) :
    stabCard Γ K (Quotient.mk (dcSetoid Γ K) x).out = stabCard Γ K x :=
  (stabCard_eq (Quotient.mk_out (s := dcSetoid Γ K) x)).symm

theorem stabCard_conj (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by
  unfold stabCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

def dcConj (Γ K : Subgroup G) (h : G) : DC Γ (K.map (MulAut.conj h).toMonoidHom) ≃ DC Γ K :=
  Quotient.congr (Equiv.mulRight h) (by
    intro a b
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      rw [Subgroup.mem_map_equiv] at hκ
      refine ⟨γ, hγ, _, hκ, ?_⟩
      simp [e, MulAut.conj_symm_apply, mul_assoc]
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      refine ⟨γ, hγ, h * κ * h⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_map_equiv]
        simpa [MulAut.conj_symm_apply, mul_assoc] using hκ
      · have e' : b = γ * a * h * κ * h⁻¹ := by
          have := congrArg (· * h⁻¹) e
          simpa [mul_assoc] using this
        rw [e']
        simp [mul_assoc])

theorem mass_conj (Γ K : Subgroup G) (h : G) :
    mass Γ (K.map (MulAut.conj h).toMonoidHom) = mass Γ K := by
  unfold mass
  rw [← finsum_comp_equiv (dcConj Γ K h)]
  refine finsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    have e1 : dcConj Γ K h (Quotient.mk _ x) = Quotient.mk (dcSetoid Γ K) (x * h) := rfl
    rw [e1, stabCard_out, stabCard_out, stabCard_conj]

end GlobalTheory.UnimodMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLattice
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : Ideal.span {c} = IsLocalRing.maximalIdeal O ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [h1]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_between_mulLat (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
section
open Module

namespace GlobalTheory.Per.Sen

theorem finrank_span_image_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] {m : ℕ}
    (d : Fin m → M) (hd : LinearIndependent L d) (p : Fin m → Prop) [DecidablePred p] :
    Module.finrank L (Submodule.span L (d '' {i | p i})) = (Finset.univ.filter p).card := by
  have h := finrank_span_eq_card (hd.comp (Subtype.val : {i // p i} → Fin m) Subtype.val_injective)
  rw [Fintype.card_subtype] at h
  rw [show d '' {i | p i} = Set.range (d ∘ (Subtype.val : {i // p i} → Fin m)) by
    ext x; simp [Set.mem_image, Set.mem_range]]
  exact h

private theorem exists_eq_of_antitone_le_of_exhaustive {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (hA : Antitone A)
    (hAD : ∀ a, A a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ A a) : ∃ a, A a = D := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional D).mpr inferInstance
  have key : ∀ T : Finset M, (T : Set M) ⊆ D → ∃ a, ∀ x ∈ T, x ∈ A a := by
    intro T
    classical
    refine Finset.induction_on T ?_ ?_
    · intro _; exact ⟨0, by simp⟩
    · intro y T _ ih hT
      obtain ⟨a, ha⟩ := ih (fun z hz => hT (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hz)))
      obtain ⟨b, hb⟩ := hex y (hT (Finset.mem_coe.mpr (Finset.mem_insert_self y T)))
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hA (min_le_right a b) hb
      · exact hA (min_le_left a b) (ha x hx)
  obtain ⟨a, ha⟩ := key S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨a, le_antisymm (hAD a) ?_⟩
  rw [← hS, Submodule.span_le]
  exact fun x hx => ha x hx

private theorem exists_adapted_basis_of_finrank_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (r : ℕ) : ∀ (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M)
    (U : Multiset ℤ), Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) →
    (∀ x ∈ D, ∃ a, x ∈ A a) → (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  induction r with
  | zero =>
    intro D _ A U hr hA hAD hex hsep hU
    have hD : D = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hA0 : ∀ a, A a = ⊥ := fun a => le_bot_iff.mp (hD ▸ hAD a)
    have hU0 : U = 0 := by
      ext a
      have h := hU a
      rw [hA0 a, hA0 (a + 1), finrank_bot] at h
      rw [Multiset.count_zero]
      push_cast at h
      omega
    refine ⟨Fin.elim0, Fin.elim0, by simp [hU0], linearIndependent_empty_type, fun a => ?_⟩
    rw [hA0 a]; symm
    rw [Submodule.span_eq_bot]
    rintro x ⟨k, -, -⟩
    exact k.elim0
  | succ r ih =>
    intro D _ A U hr hA hAD hex hsep hU
    classical
    obtain ⟨a0, ha0⟩ := exists_eq_of_antitone_le_of_exhaustive D A hA hAD hex
    have hDne : D ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hr; omega
    obtain ⟨w, hwD, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDne
    obtain ⟨b, hb⟩ : ∃ b, w ∉ A b := by
      by_contra h; push Not at h; exact hw0 (hsep w h)
    have hbd : ∀ a, A a = D → a < b := by
      intro a ha; by_contra h; push Not at h
      exact hb (hA h (by rw [ha]; exact hwD))
    obtain ⟨s, hs, hsmax⟩ :=
      Int.exists_greatest_of_bdd ⟨b, fun z hz => (hbd z hz).le⟩ ⟨a0, ha0⟩
    have hBD : A (s + 1) < D :=
      lt_of_le_of_ne (hAD _) (fun h => by have := hsmax _ h; omega)
    obtain ⟨v, hvD, hvB⟩ := SetLike.exists_of_lt hBD
    have hv0 : v ≠ 0 := fun h => hvB (by rw [h]; exact Submodule.zero_mem _)
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A (s + 1) ⊔ Submodule.span L {v})
    obtain ⟨D', hD'⟩ : ∃ D' : Submodule L M, D' = A (s + 1) ⊔ (C ⊓ D) := ⟨_, rfl⟩
    have hED : A (s + 1) ⊔ Submodule.span L {v} ≤ D :=
      sup_le (hAD _) ((Submodule.span_singleton_le_iff_mem _ _).mpr hvD)
    have hD'D : D' ≤ D := by rw [hD']; exact sup_le (hAD _) inf_le_right
    have hBD' : A (s + 1) ≤ D' := by rw [hD']; exact le_sup_left
    have hvD' : v ∉ D' := by
      intro hv
      rw [hD'] at hv
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
      have hzE : z ∈ A (s + 1) ⊔ Submodule.span L {v} := by
        have : z = v - y := by rw [← hyz]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
          (Submodule.mem_sup_left hy)
      have hz0 : z = 0 := (Submodule.disjoint_def.mp hC.disjoint) z hzE hz.1
      apply hvB; rw [← hyz, hz0, add_zero]; exact hy
    have hsup : D' ⊔ Submodule.span L {v} = D := by
      rw [hD', sup_right_comm, ← sup_inf_assoc_of_le _ hED, hC.sup_eq_top, top_inf_eq]
    have hinf : D' ⊓ Submodule.span L {v} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx1) hvD'
    have : FiniteDimensional L D' := Submodule.finiteDimensional_of_le hD'D
    have : FiniteDimensional L (Submodule.span L {v}) :=
      FiniteDimensional.span_of_finite L (Set.finite_singleton v)
    have hrD' : Module.finrank L D' = r := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq D' (Submodule.span L {v})
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hv0, hr] at h
      omega
    have hlow : ∀ a, a ≤ s → A a = D := fun a ha =>
      le_antisymm (hAD a) (by rw [← hs]; exact hA ha)
    have hs_mem : 0 < U.count s := by
      have h := hU s
      rw [hs, hr] at h
      have := Submodule.finrank_lt_finrank_of_lt hBD
      rw [hr] at this
      omega
    have hU' : ∀ a : ℤ, (Module.finrank L ↥(A a ⊓ D') : ℤ) -
        Module.finrank L ↥(A (a + 1) ⊓ D') = ((U.erase s).count a : ℤ) := by
      intro a
      rcases lt_trichotomy a s with h | h | h
      · have h0 := hU a
        rw [hlow a h.le, hlow (a + 1) (by omega)] at h0
        rw [hlow a h.le, hlow (a + 1) (by omega), inf_eq_right.mpr hD'D,
          Multiset.count_erase_of_ne h.ne]
        omega
      · rw [h]
        have h0 := hU s
        rw [hs, hr] at h0
        rw [hs, inf_eq_right.mpr hD'D, inf_eq_left.mpr hBD', Multiset.count_erase_self, hrD',
          Nat.cast_sub hs_mem, Nat.cast_one]
        push_cast at h0 ⊢
        omega
      · rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD'),
          inf_eq_left.mpr ((hA (show s + 1 ≤ a + 1 by omega)).trans hBD'),
          Multiset.count_erase_of_ne h.ne']
        exact hU a
    obtain ⟨u', d', hu', hd', hspan'⟩ := ih D' (fun a => A a ⊓ D') (U.erase s) hrD'
      (fun a b h => inf_le_inf_right _ (hA h)) (fun a => inf_le_right)
      (fun x hx => by obtain ⟨a, ha⟩ := hex x (hD'D hx); exact ⟨a, Submodule.mem_inf.mpr ⟨ha, hx⟩⟩)
      (fun x hx => hsep x (fun a => (Submodule.mem_inf.mp (hx a)).1)) hU'
    have hd'D' : ∀ k, d' k ∈ D' := by
      intro k
      have h := hspan' (u' k)
      have hk : d' k ∈ Submodule.span L (d' '' {j | u' k ≤ u' j}) :=
        Submodule.subset_span ⟨k, le_refl (u' k), rfl⟩
      rw [← h] at hk
      exact (Submodule.mem_inf.mp hk).2
    refine ⟨Fin.cons s u', Fin.cons v d', ?_, ?_, ?_⟩
    · rw [Fin.univ_val_map, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu']
      exact Multiset.cons_erase (Multiset.count_pos.mp hs_mem)
    · refine linearIndependent_finCons.mpr ⟨hd', fun hv => hvD' ?_⟩
      exact (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hd'D' k)) hv
    · intro a
      by_cases has : a ≤ s
      · rw [hlow a has]
        apply le_antisymm
        · rw [← hsup, sup_le_iff]
          constructor
          · have h := hspan' a
            rw [hlow a has, inf_eq_right.mpr hD'D] at h
            rw [h]
            apply Submodule.span_mono
            rintro _ ⟨j, hj, rfl⟩
            exact ⟨j.succ, by simpa using hj, by simp⟩
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact Submodule.subset_span ⟨0, by simpa using has, by simp⟩
        · rw [Submodule.span_le]
          rintro _ ⟨k, -, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simpa using hvD
          · simpa using hD'D (hd'D' j)
      · push Not at has
        have h := hspan' a
        rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD')] at h
        rw [h]
        congr 1
        ext x
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.succ, by simpa using hj, by simp⟩
        · rintro ⟨k, hk, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp at hk; omega
          · exact ⟨j, by simpa using hk, by simp⟩

theorem adapted_basis_jumps : ∀ {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (U : Multiset ℤ) (r : ℕ),
    Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) → (∀ x ∈ D, ∃ a, x ∈ A a) →
    (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  intro L M _ _ _ D _ A U r hr hA hAD hex hsep hU
  exact exists_adapted_basis_of_finrank_jumps r D A U hr hA hAD hex hsep hU

end GlobalTheory.Per.Sen
end

