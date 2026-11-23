module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BoundsExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private def sigSub {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    Submodule R ((Σ v, X v) → R) where
  carrier := {z | ∀ v, (fun s => z ⟨v, s⟩) ∈ p v}
  add_mem' ha hb v := (p v).add_mem (ha v) (hb v)
  zero_mem' v := (p v).zero_mem
  smul_mem' c _ ha v := (p v).smul_mem c (ha v)

private def sigEquiv {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    (∀ v, p v) ≃ₗ[R] sigSub p where
  toFun f := ⟨fun x => (f x.1).1 x.2, fun v => (f v).2⟩
  invFun z v := ⟨fun s => z.1 ⟨v, s⟩, z.2 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem phi_mul {k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (φ : k →ₗ[k₀] k₀) (x : k₀) (y : k) :
    φ (algebraMap k₀ k x * y) = x * φ y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem zgl_phi {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k₀ k : Type} [Field k₀]
    [Field k] [Algebra k₀ k] (a₀ : O →+* k₀) (w : ℤ × ℤ) (z : Γ → k) (hz : z ∈ Φ.Zgl ((algebraMap k₀ k).comp a₀) w)
    (φ : k →ₗ[k₀] k₀) : (fun x => φ (z x)) ∈ Φ.Zgl a₀ w := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨h1.comp φ, fun g h => ?_, fun g h => ?_, fun h => ?_⟩
  · show φ (z (g * h)) = φ (z g) + _ * φ (z h)
    rw [h2, map_add (f := _), RingHom.comp_apply, phi_mul]
  · show φ (z g) = 0
    rw [h3 g h, map_zero]
  · show φ (z Φ.g0) = 0
    rw [h4 h, map_zero]

theorem UpperTheory.V.Ws.cocycleBounds_of_ringHom_comp :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) (k₀ k : Type) [Field k₀] [Field k] (a₀ : O →+* k₀) (j : k₀ →+* k) (d C : ℕ), Φ.Bounds a₀ d C → Φ.Bounds (j.comp a₀) d C := by
  intro O Γ _ _ _ Φ k₀ k _ _ a₀ j d C hB
  letI : Algebra k₀ k := j.toAlgebra
  change Φ.Bounds ((algebraMap k₀ k).comp a₀) d C
  refine ⟨hB.card, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · refine rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.str w hw) ?_
    rintro z ⟨hz, n, hn⟩ φ
    refine ⟨zgl_phi Φ a₀ w z hz φ, fun v => φ (n v), fun v s hs => ?_⟩
    show φ (z s) = φ (n v) - _ * φ (n v)
    rw [hn v s hs, map_sub, RingHom.comp_apply, phi_mul]
  · exact rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.even w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
  · have := rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ (d + C) (by exact_mod_cast hB.odd w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
    exact_mod_cast this
  · have h0 := hB.loc w hw
    rw [(sigEquiv _).rank_eq] at h0 ⊢
    have := rank_le_of_linearForm_comp_mem_of_rank_le _ k₀ k _ (sigSub fun v => Φ.Zloc ((algebraMap k₀ k).comp a₀) (Φ.Gv v) w) (d + C)
      (by exact_mod_cast h0) (by
        intro z hz φ v
        obtain ⟨h1, h2⟩ := hz v
        refine ⟨h1.comp φ, fun g h => ?_⟩
        have h3 := congrArg φ (h2 g h)
        rw [map_add (f := _), RingHom.comp_apply, phi_mul] at h3
        exact h3)
    exact_mod_cast this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardLocalCocyclesLeOfPlaceAbovePrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.card_localCocycles_le_of_place_above_prime :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation R (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ m, IsLocallyConstant fun g => ρ g m) → CardLe (cocOff ρ ∅) (Nat.card M ^ (2 + locDeg v)) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ R M _ _ _ _ hl A v ρ hA hv hρ
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (Dec (F := F) A) R M hl ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hc : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    simp only [hρ']
    exact (hρ m).continuous
  obtain ⟨f1, h1⟩ := local_h1_finite_mod_l hF hT hE F Ω l M A v ρ' hA hc
  obtain ⟨fz, hz⟩ := cocycle_card_euler_formula _ _ M ρ' hc f1
  rw [if_pos hv] at h1
  have h0 : 0 < Nat.card (H0 ρ') := by
    haveI : Finite (H0 ρ') := Subtype.finite
    haveI : Nonempty (H0 ρ') := ⟨0⟩
    exact Nat.card_pos
  have hZ : CardLe (Z1 ρ') (Nat.card M ^ (2 + locDeg v)) := by
    refine ⟨fz, Nat.le_of_mul_le_mul_right ?_ h0⟩
    rw [hz]
    calc Nat.card (H1 ρ') * Nat.card M
        ≤ Nat.card (H0 ρ') * Nat.card M ^ (1 + locDeg v) * Nat.card M := Nat.mul_le_mul_right _ h1
      _ = Nat.card M ^ (2 + locDeg v) * Nat.card (H0 ρ') := by ring
  have hmem : ∀ z : cocOff ρ ∅, z.1 ∈ Z1 ρ' := fun z =>
    (mem_Z1_iff_cocycle ρ' _).2 ⟨z.2.1.continuous, fun g h => by rw [hρ']; exact z.2.2.1 g h⟩
  exact hZ.of_injective (fun z => ⟨z.1, hmem z⟩) fun a b h => Subtype.ext (congrArg (fun z : Z1 ρ' => z.1) h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DecIdx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.index_cyclotomicKer_sup_decompositionGroup_ne_zero :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → ((cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A).index ≠ 0 := by
  intro Ω _ _ _ l _ p A hp hA
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hg : ∃ g ∈ Dec (F := ℚ) A, ¬ IsOfFinOrder (cycZ ℚ Ω l g) := by
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨g, hg, hf⟩ := UpperTheory.V.Base.decInf ℚ Ω l ⊤ isOpen_univ A hA
      exact ⟨g, hg.2, hf⟩
    · obtain ⟨-, -, γ, hγ, -, hc⟩ := UpperTheory.V.Chr.decCyc Ω p A hp hA
      refine ⟨γ, hγ, fun hf => ?_⟩
      obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
      have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) e
      rw [Units.val_pow_eq_pow_val, hc l hlp, Units.val_one] at h3
      have h4 : p ^ n = 1 := by exact_mod_cast h3
      exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne' h4
  obtain ⟨g, hg, hf⟩ := hg
  have hcl : IsClosed (((Dec (F := ℚ) A).map (cycZ ℚ Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
    ((isClosed_Dec (F := ℚ) A).isCompact.image (continuous_cycZ ℚ Ω l)).isClosed
  have h0 := UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder l _ hcl ⟨_, ⟨g, hg, rfl⟩, hf⟩
  have e : (cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A = ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).comap (cycZ ℚ Ω l) := by
    rw [Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  exact fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.EvenRt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.residualCharacter_complexConjugation_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (σ : G T.F Ω), IsCC σ → ∀ w ∈ [0, wPs, -wPs], T.rbU w σ = 1 := by
  intro Ω _ _ _ l _ c D hD T σ hσ w hw
  have hτ : IsCC (resQ T.F σ) := by
    unfold IsCC at *
    exact hσ
  have hconj := isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC
  have hP : D.Psi (resQ T.F σ) = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hconj
    rw [← hD.Psi_even, ← hu]
    simp only [map_mul, map_inv]
    rw [mul_comm, inv_mul_cancel_left]
  have hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ) := by
    have : D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ) := by
      unfold Raw.th
      rfl
    rw [MonoidHom.mul_apply, hP, mul_one] at this
    exact this
  have hrt : (T.fr ∅).rt w σ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
  show (Units.map _) ((T.fr ∅).rt w σ) = 1
  rw [hrt, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ShaCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical
open scoped Pointwise

theorem UpperTheory.V.Ws.tate_shafarevich_card_mod_l :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (Av : S → ValuationSubring Ω) (K : Subgroup (G F Ω)) (r : ℕ), (∀ v, IsPlaceOver (Av v) v.1) → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → XRk l 1 K r → CardLe (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l hl M _ _ _ _ _ S ρ Av K r hA hN hK hρ hX
  have hM : ∀ m : M, l • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)) l m]
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by rw [pow_one])
    rw [h0, zero_smul]
  have hB := UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow F Ω l (ZMod (l ^ 1)) M hM (ρ.comp (toGS Ω _)) K r hK hρ hX
  obtain ⟨p1, p2, -, -⟩ := UpperTheory.V.Kum.placeDict F Ω
  have hmem : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S Av) (continuous_locFam S Av) →
      (fun g => z.1 (toGS Ω _ g)) ∈ cocOff (ρ.comp (toGS Ω _)) (ineOff F Ω 1 ∩ K) := by
    intro z hz
    have hz1 : z.1 1 = 0 := by
      have := z.2.2 1 1
      rw [one_mul, map_one, Module.End.one_apply] at this
      exact left_eq_add.1 this
    have hc : ∀ a b : G F Ω, z.1 (toGS Ω _ (a * b)) = z.1 (toGS Ω _ a) + ρ (toGS Ω _ a) (z.1 (toGS Ω _ b)) :=
      fun a b => by rw [map_mul, z.2.2]
    refine ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_toGS Ω _)), hc, ?_⟩
    rintro u ⟨⟨A, -, hu⟩, huK⟩
    show z.1 (toGS Ω _ u) = 0
    by_cases hT : A = ⊤
    · subst hT
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, hz1]
    obtain ⟨v, hv⟩ := p2 A hT
    by_cases hvS : v ∈ S
    · obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hvS⟩) hv
      have hd : g⁻¹ * u * g ∈ Dec (F := F) (Av ⟨v, hvS⟩) := by
        have h : u • g • Av ⟨v, hvS⟩ = g • Av ⟨v, hvS⟩ := Ine_le_Dec _ hu
        show (g⁻¹ * u * g) • Av ⟨v, hvS⟩ = Av ⟨v, hvS⟩
        rw [mul_smul, mul_smul, h, inv_smul_smul]
      have hk : g⁻¹ * u * g ∈ K := by simpa using hN.conj_mem u huK g⁻¹
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 ((Submodule.mem_iInf _).1 hz ⟨v, hvS⟩))
      have h0 : z.1 (toGS Ω _ (g⁻¹ * u * g)) = 0 := (hm ⟨_, hd⟩).trans (sub_eq_zero.2 (hρ _ hk m))
      have h1 := hc g (g⁻¹ * u * g)
      rw [h0, map_zero, add_zero, mul_assoc, mul_inv_cancel_left, hc, hρ u huK] at h1
      exact add_eq_right.1 h1
    · have hn : u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hu⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) u = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [this, hz1]
  choose s hs using Submodule.Quotient.mk_surjective ((B1 ρ).comap (Z1 ρ).subtype)
  refine hB.of_injective (fun x => ⟨_, hmem (s x.1) ((hs x.1).symm ▸ x.2)⟩) fun x y h => ?_
  apply Subtype.ext
  rw [← hs x.1, ← hs y.1]
  congr 1
  apply Subtype.ext
  funext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrFun (congrArg Subtype.val h) g
end

