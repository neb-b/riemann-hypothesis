module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsComplexConjugationAtRealPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.LocalH1FiniteModL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem natCard_dual_eq_natCard_of_finite (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V] :
    Nat.card (Module.Dual K V) = Nat.card V := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.natCard_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]

theorem UpperTheory.V.Ws.local_h1_finite_mod_l :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ContAction ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ Nat.card (H0 ρ) * Nat.card M ^ (1 + if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v ρ hv hρ
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨_, hf1, _, _⟩ := hF F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨⟨e2⟩, _, _, _, hbij⟩ := hT F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨hEram, hEun⟩ := hE F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨e2'⟩ : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
      (MonoidHom.id _)) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
    rw [MonoidHom.comp_id]
    exact ⟨e2⟩
  haveI hfinD : Finite (Module.Dual (ZMod (l ^ 1)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ 1)) M => (f : M → ZMod (l ^ 1))) DFunLike.coe_injective
  haveI hfinT : Finite (TDual (ZMod (l ^ 1)) M) := hfinD
  have hH2 : Nat.card (H2 ρ) ≤ Nat.card M := by
    calc Nat.card (H2 ρ) = Nat.card (H2 (ρ.comp (MonoidHom.id _))) := by rw [MonoidHom.comp_id]
      _ = _ := Nat.card_eq_of_bijective _ hbij
      _ = Nat.card (Module.Dual (ZMod (l ^ 1)) ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _)))) := Nat.card_congr (LinearEquiv.congrRight e2').toEquiv
      _ = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _))) := natCard_dual_eq_natCard_of_finite _ _
      _ ≤ Nat.card (TDual (ZMod (l ^ 1)) M) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card M := natCard_dual_eq_natCard_of_finite _ _
  refine ⟨hf1, ?_⟩
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [if_pos hl, hEram hl, pow_add, pow_one (Nat.card M), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH2)
  · rw [if_neg hl, hEun hl, add_zero, pow_one (Nat.card M)]
    exact Nat.mul_le_mul_left _ hH2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.NcardPlacesDividingLeOfOrbitBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PerpTop
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cup_product_injective_comp {R Γ D M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [Group Γ] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ)
    (hρ : ContAction (ρ.comp φ)) (χ' : D →* Rˣ) (e : χ' = χ.comp φ)
    (h : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) (hρ.comp' continuous_id))) :
    Function.Injective (cupH1H1TwistedDual χ ρ φ hρ) := by
  subst e
  have e1 : (twDual χ ρ).comp φ = (twDual (χ.comp φ) (ρ.comp φ)).comp (MonoidHom.id D) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => LinearMap.ext fun m => ?_
    change ((χ (φ g) : Rˣ) : R) * y (ρ ((φ g)⁻¹) m) =
      ((χ (φ g) : Rˣ) : R) * y (ρ (φ g⁻¹) m)
    rw [map_inv φ g]
  have gen : ∀ (σ σ' : Representation R D (TDual R M)) (_ : σ = σ') h1 h2,
      Function.Injective (cupProductH1H1 σ' (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h2 hρ) →
      Function.Injective (cupProductH1H1 σ (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h1 hρ) := by
    intro σ σ' e h1 h2 h
    subst e
    exact h
  exact gen _ _ e1 _ (fun g y x => evalPair_equiv (χ.comp φ) (ρ.comp φ) g x y) h

theorem UpperTheory.V.Ws.dualSelmer_orthogonalComplement_conditions :
    LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (Av : S → ValuationSubring Ω), μ.comp (toGS Ω _) = cycMod F Ω l 1 → (∀ v, IsPlaceOver (Av v) v.1) → Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) fun _ => ⊤) = Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) := by
  intro hT F Ω _ _ _ _ _ l _ M _ _ _ _ _ S ρ hρ μ Av hμ hA
  have key : ∀ v : S, Function.Injective
      (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))) := fun v => by
    have h := (hT F Ω l 1 M (Av v) (ρ.comp (locFam S Av v)) v.1 one_pos (hA v)
      (hρ.comp' (continuous_locFam S Av v))).2.2.1.1
    exact cup_product_injective_comp μ ρ _ _ _ (by rw [← hμ]; rfl) h
  ext y
  rw [mem_Sel, Sha1, Submodule.mem_iInf]
  refine forall_congr' fun v => ?_
  rw [mem_perpCond, LinearMap.mem_ker]
  constructor
  · intro h
    apply key v
    rw [map_zero]
    exact LinearMap.ext fun x => h x trivial
  · intro h x _
    rw [h, map_zero, LinearMap.zero_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.rank_le_of_card_le_pow_card_field :
    ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] (n : ℕ), CardLe W (Nat.card k ^ n) → Module.rank k W ≤ n := by
  intro k W _ _ _ _ n hW
  obtain ⟨hfin, hle⟩ := hW
  haveI := hfin
  haveI : Module.Finite k W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k)] at hle
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hr : Module.finrank k W ≤ n := (Nat.pow_le_pow_iff_right hk).1 hle
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem exists_natCard_eq_pow_and_separating_zmod_forms (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod l) M]
    [Finite M] : ∃ (d : ℕ) (c : Fin d → M →+ ZMod l), Nat.card M = l ^ d ∧
      ∀ x y : M, (∀ i, c i x = c i y) → x = y := by
  refine ⟨Module.finrank (ZMod l) M,
    fun i => ((Module.finBasis (ZMod l) M).coord i).toAddMonoidHom, ?_, ?_⟩
  · letI : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  · intro x y h
    apply (Module.finBasis (ZMod l) M).ext_elem
    intro i
    simpa [Module.Basis.coord_apply] using h i

private theorem eq_zero_of_nsmul_eq_zero_of_coprime_torsion (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    (htor : ∀ m : M, l • m = 0) (n : ℕ) (hn : ¬ l ∣ n) (x : M) (hx : n • x = 0) : x = 0 := by
  have hcop : Nat.Coprime n l :=
    Nat.coprime_comm.mp ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr hn)
  have h := Nat.gcd_eq_gcd_ab n l
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  calc x = (1 : ℤ) • x := (one_zsmul x).symm
    _ = ((n : ℤ) * Nat.gcdA n l + (l : ℤ) * Nat.gcdB n l) • x := by rw [h]
    _ = Nat.gcdA n l • (n • x) + Nat.gcdB n l • (l • x) := by
      rw [add_smul, mul_comm (n : ℤ), mul_comm (l : ℤ), mul_smul, mul_smul, natCast_zsmul,
        natCast_zsmul]
    _ = 0 := by rw [hx, htor, smul_zero, smul_zero, add_zero]

theorem UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (r : ℕ), ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ g m = m) → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω 1 ∩ K)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ htor ρ K r hdvd hK hX
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hidx : K.index ≠ 0 := fun h => hdvd (h ▸ dvd_zero l)
  haveI : K.FiniteIndex := ⟨hidx⟩
  letI : Fintype (G F Ω ⧸ K) := Fintype.ofFinite _
  have hn : ¬ l ∣ Fintype.card (G F Ω ⧸ K) := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  have key : ∀ w : G F Ω → M, (∀ g h, w (g * h) = w g + ρ g (w h)) → (∀ k ∈ K, w k = 0) →
      (∑ q : G F Ω ⧸ K, w q.out) = 0 → w = 0 := by
    intro w hw hwK hS
    funext h
    show w h = 0
    have e1 : ∀ q : G F Ω ⧸ K, w (h * q.out) = w (h • q).out := by
      intro q
      have hq : ((h * q.out : G F Ω) : G F Ω ⧸ K) = h • q := by
        show ((h • q.out : G F Ω) : G F Ω ⧸ K) = h • q
        rw [← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hk : (h * q.out)⁻¹ * (h • q).out ∈ K :=
        QuotientGroup.eq.mp (hq.trans (QuotientGroup.out_eq' _).symm)
      have := hw (h * q.out) ((h * q.out)⁻¹ * (h • q).out)
      rw [mul_inv_cancel_left, hwK _ hk, map_zero, add_zero] at this
      exact this.symm
    have hsum : ∑ q : G F Ω ⧸ K, w (h * q.out) = ∑ q : G F Ω ⧸ K, w q.out := by
      rw [Finset.sum_congr rfl (fun q _ => e1 q)]
      exact Equiv.sum_comp (MulAction.toPerm h) (fun q : G F Ω ⧸ K => w q.out)
    have hexp : ∑ q : G F Ω ⧸ K, w (h * q.out) =
        Fintype.card (G F Ω ⧸ K) • w h + ρ h (∑ q : G F Ω ⧸ K, w q.out) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
    rw [hsum, hS, map_zero, add_zero] at hexp
    exact eq_zero_of_nsmul_eq_zero_of_coprime_torsion l M htor _ hn (w h) hexp.symm
  obtain ⟨hXfin, hXcard⟩ := hX
  obtain ⟨d, c, hM, hc⟩ := @exists_natCard_eq_pow_and_separating_zmod_forms l _ M _ (AddCommGroup.zmodModule htor) _
  have mem : ∀ z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))),
      IsLocallyConstant z.1 ∧ (∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)) ∧
        ∀ g ∈ ineOff F Ω 1 ∩ (K : Set (G F Ω)), z.1 g = 0 := fun z => z.2
  have hone : ∀ A : ValuationSubring Ω, ¬ A.valuation ((1 : ℕ) : Ω) < 1 := by
    intro A
    simp
  have coordMem : ∀ (z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))) (i : Fin d),
      (fun u : K => c i (z.1 u)) ∈ UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l) := by
    intro z i
    obtain ⟨hlc, hcoc, hvan⟩ := mem z
    have hφ : IsLocallyConstant (fun u : K => c i (z.1 u)) ∧
        (∀ a e : K, c i (z.1 ↑(a * e)) = c i (z.1 a) + c i (z.1 e)) ∧
        (∀ (A : ValuationSubring Ω) (u : K), (u : G F Ω) ∈ Ine A → c i (z.1 u) = 0) ∧
        ∀ (A : ValuationSubring Ω), A.valuation ((1 : ℕ) : Ω) < 1 → ∀ u : K, (u : G F Ω) ∈ Dec A →
          c i (z.1 u) = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hlc.comp_continuous continuous_subtype_val).comp (fun m => c i m)
      · intro a e
        rw [Subgroup.coe_mul, hcoc, hK a a.2, map_add (f := _)]
      · intro A u hu
        have hin : (u : G F Ω) ∈ ineOff F Ω 1 := by
          show ∃ A, _
          exact ⟨A, hone A, hu⟩
        rw [hvan u ⟨hin, u.2⟩, map_zero]
      · intro A hA
        exact absurd hA (hone A)
    exact hφ
  let Φ : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))) →
      (Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M :=
    fun z => (fun i => ⟨_, coordMem z i⟩, ∑ q : G F Ω ⧸ K, z.1 q.out)
  have hinj : Function.Injective Φ := by
    intro z z' hzz
    have h2 : (∑ q : G F Ω ⧸ K, z.1 q.out) = ∑ q : G F Ω ⧸ K, z'.1 q.out :=
      congrArg Prod.snd hzz
    have hKeq : ∀ k ∈ K, z.1 k = z'.1 k := by
      intro k hk
      exact hc _ _ (fun i => congrArg (fun p => (p.1 i).1 ⟨k, hk⟩) hzz)
    obtain ⟨_, hcoc, -⟩ := mem z
    obtain ⟨_, hcoc', -⟩ := mem z'
    have hw := key (fun g => z.1 g - z'.1 g)
      (by
        intro g h
        simp only [hcoc, hcoc', map_sub]
        abel)
      (by
        intro k hk
        simp [hKeq k hk])
      (by simp only [Finset.sum_sub_distrib, h2, sub_self])
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mp (congrFun hw g)
  haveI : Finite ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) := hXfin
  refine (show Finite _ ∧ Nat.card _ ≤ _ from ⟨Finite.of_injective Φ hinj, ?_⟩)
  calc Nat.card ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))
      ≤ Nat.card ((Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) ^ d * Nat.card M := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    _ ≤ (l ^ r) ^ d * Nat.card M :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hXcard _)
    _ = Nat.card M ^ (r + 1) := by
        rw [hM]
        ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.SumDeg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.sum_local_degree_above_l_le_finrank :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∑ v ∈ S, if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) ≤ Module.finrank ℚ F := by
  intro F _ _ l hl S
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)
  have hpb : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  haveI hpm : p.IsMaximal := hpp.isMaximal hpb
  have key := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at key
  rw [← key, ← Finset.sum_filter]
  set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg
  have h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v
      = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I := by
    rw [Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
  have h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_image, Finset.mem_filter] at hI
    obtain ⟨v, ⟨_, hv⟩, rfl⟩ := hI
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hle : p ≤ Ideal.under ℤ v.asIdeal := by
      rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under, Ideal.mem_comap] using hv
    have hne : Ideal.under ℤ v.asIdeal ≠ ⊤ := (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
    have heq : p = Ideal.under ℤ v.asIdeal := hpm.eq_of_le hne hle
    exact ⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩
  · intro _ _ _
    exact Nat.zero_le _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.TowerPl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.exists_injective_places_above_l_of_tower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∃ pl : T.ι → HeightOneSpectrum (𝓞 T.F), Function.Injective pl ∧ ∀ v, IsPlaceOver (T.pl v) (pl v) ∧ ((l : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal := by
  intro Ω _ _ _ l _ c D T
  haveI := T.nF
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨_, hex, hne, _⟩ := UpperTheory.V.Kum.placeDict T.F Ω
  have hpl : ∀ v, ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w :=
    fun v => hex _ (hne _ l (Fact.out : l.Prime).ne_zero (T.ovl v))
  choose pl hpl using hpl
  refine ⟨pl, ?_, fun v => ⟨hpl v, ?_⟩⟩
  · intro v w hvw
    have h1 := hpl v
    have h2 := hpl w
    rw [hvw] at h1
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
    obtain ⟨u, _, huniq⟩ := T.cover (T.pl w) (T.ovl w)
    have hv : v = u := by
      apply huniq v
      refine ⟨σ, fun x => ?_⟩
      rw [← hσ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    have hw : w = u := by
      apply huniq w
      exact ⟨1, fun x => Iff.rfl⟩
    rw [hv, hw]
  · apply (hpl v (l : 𝓞 T.F)).1
    simpa using T.ovl v
end

