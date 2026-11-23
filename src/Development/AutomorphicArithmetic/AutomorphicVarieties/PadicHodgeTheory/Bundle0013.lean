module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelCyclotomicOfOpenEmbedding
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem numField {v : ℕ} [Fact v.Prime] (K : FinExt v) {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl v) (A : ValuationSubring Ω) (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧
      K.1 = IntermediateField.adjoin ℚ_[v] (Set.range fun x : F => j (algebraMap F Ω x)) := by
  let K0 : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl
  have h0 : ∀ τ, τ ∈ GK K0 := fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff K0 rfl τ).2 fun x => by simp
  let r : GQ v →* (Ω ≃ₐ[ℚ] Ω) := (Subgroup.subtype _).comp
    (e.symm.toMonoidHom.comp ((MonoidHom.id _).codRestrict _ h0))
  have hr : ∀ τ x, τ (j x) = j (r τ x) := fun τ x => by
    have := hec (e.symm ⟨τ, h0 τ⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hrc : Continuous r := continuous_subtype_val.comp (he'.comp (continuous_id.subtype_mk _))
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hK := K.2
  have hle : K.1 ≤ IntermediateField.adjoin ℚ_[v] (j '' {a | j a ∈ K.1}) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[v] _),
      IntermediateField.le_iff_le]
    intro τ hτ
    let H : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω) := ⟨(GK K).map r,
      ((IntermediateField.fixingSubgroup_isClosed K.1).isCompact.image hrc).isClosed⟩
    have h1 : r τ ∈ H.1 := by
      rw [← InfiniteGalois.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
      intro a ha
      apply j.injective
      rw [← hr]
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
        (IntermediateField.subset_adjoin _ _ ⟨a, ?_, rfl⟩)
      change j a ∈ K.1
      rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [hr, (IntermediateField.mem_fixedField_iff _ _).1 ha _ ⟨σ, hσ, rfl⟩]
    obtain ⟨σ, hσ, hst⟩ := h1
    have : σ = τ := GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding j)
      fun x => by rw [hr, hr, hst]
    exact this ▸ hσ
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ_[v] K.1
  have hx' : IntermediateField.adjoin ℚ_[v] {(x : PadicAlgCl v)} = K.1 := by
    rw [← IntermediateField.lift_adjoin_simple, hx, IntermediateField.lift_top]
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin (hle x.2)
  have hfin : Finite (j ⁻¹' (T : Set (PadicAlgCl v))) :=
    (T.finite_toSet.preimage j.injective.injOn).to_subtype
  refine ⟨IntermediateField.adjoin ℚ (j ⁻¹' (T : Set (PadicAlgCl v))),
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z,
    le_antisymm ?_ ?_⟩
  · rw [← hx', IntermediateField.adjoin_simple_le_iff]
    refine IntermediateField.adjoin.mono _ _ _ (fun t ht => ?_) hxT
    obtain ⟨a, -, rfl⟩ := hT ht
    exact ⟨⟨a, IntermediateField.subset_adjoin _ _ ht⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    change j y ∈ K.1
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, ha, h⟩ := hT hy
      exact h ▸ ha
    | algebraMap y => rw [eq_ratCast, map_ratCast]; exact SubfieldClass.ratCast_mem _ _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

open NumberField IsDedekindDomain in
private theorem placeBelow {v : ℕ} (hv : v.Prime) (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), Formalism.ConjugateSelfDual.IsPlaceOver A w ∧
      ∀ l : ℕ, l.Prime → v ≠ l → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  have hm : ∀ x : 𝓞 F, algebraMap F Ω x ∈ A := fun x => by
    have h : IsIntegral ℤ (algebraMap F Ω x) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
    have := (Valuation.integer.integers A.valuation).mem_of_integral (x := algebraMap F Ω x) h.tower_top
    exact (A.valuation_le_one_iff _).1 this
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hm
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap F Ω x) < 1 :=
    fun x => A.valuation_lt_one_iff (f x)
  have hn : ∀ n : ℕ, (n : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f ↔ v ∣ n := fun n => by
    rw [hf, ← Int.natCast_dvd_natCast, ← GlobalTheory.PlaceBridge.val_int_lt_one_iff A hv hA]
    simp
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, fun x => (hf x).symm,
    fun l hl hvl h => hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 ((hn l).1 h))⟩
  have := (hn v).2 dvd_rfl
  rw [h, Ideal.mem_bot] at this
  exact hv.ne_zero (Nat.cast_eq_zero.1 this)

private theorem hn_transport {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (e : Γ' ≃* Γ) (he : Continuous e) (he' : Continuous e.symm) (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (h : ∀ g m, ρ' g m = ρ (e g) m) (n : ℕ)
    (hs : Subsingleton (Hn ρ (n + 1))) : Subsingleton (Hn ρ' (n + 1)) := by
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
  intro f hf hd
  obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
    (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
      funext g
      have := GlobalTheory.dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' (n + 1) f g
      rw [hd] at this
      exact this)
  refine ⟨fun x => c (fun i => e (x i)),
    hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
  funext g
  have := GlobalTheory.dn_comp_monoidHom e.toMonoidHom ρ ρ' h n c g
  rw [hcf] at this
  refine this.trans ?_
  exact congrArg f (funext fun i => e.symm_apply_apply _)

private theorem core {n : ℕ} [NeZero n] {G D M : Type} [Group G] [TopologicalSpace G] [Group D]
    [TopologicalSpace D] [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (e : G ≃* D) (he : Continuous e) (he' : Continuous e.symm)
    (χG : G →* (ZMod n)ˣ) (χ : D →* (ZMod n)ˣ) (hχ : ∀ g, χ (e g) = χG g)
    (ρ : Representation (ZMod n) G M) (σ : Representation (ZMod n) D M) (h : ∀ g m, ρ g m = σ (e g) m)
    (c : ℕ) (f1 : Finite (H1 σ)) (f2 : Finite (H2 σ)) (f3 : ∀ m, 3 ≤ m → Subsingleton (Hn σ m))
    (hj : Nonempty (H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod n] ZMod n))
    (hb : Function.Bijective (cup20 χ σ (MonoidHom.id _)))
    (hE : Nat.card (H1 σ) = Nat.card (H0 σ) * Nat.card (H2 σ) * c) :
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ m, 3 ≤ m → Subsingleton (Hn ρ m)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * c ∧
      Nat.card (H2 ρ) = Nat.card (H0dual χG ρ) := by
  obtain ⟨⟨e1⟩, ⟨e2⟩, -⟩ := GlobalTheory.contCohomology_transport_mulEquiv _ _ _ M e he he' σ ρ h
  obtain ⟨j⟩ := hj
  have h0 : H0 ρ = H0 σ := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    refine ⟨fun hm g => ?_, fun hm g => (h g m).trans (hm _)⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    exact (h g m).symm.trans (hm g)
  refine ⟨Finite.of_equiv _ e1, Finite.of_equiv _ e2, fun m hm => ?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact hn_transport e he he' σ ρ h k (f3 _ hm)
  · rw [← Nat.card_congr e1, ← Nat.card_congr e2, h0, hE]
  · have hfin : Finite (TDual (ZMod n) M) := DFunLike.finite _
    let E : H2 σ ≃ Module.Dual (ZMod n) (H0 ((twDual χ σ).comp (MonoidHom.id _))) :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight j).toEquiv
    rw [← Nat.card_congr e2, Nat.card_congr E, GlobalTheory.ZModDual.card_dual_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f : TDual (ZMod n) M => ?_)
    change (∀ g, twDual χ σ g f = f) ↔ ∀ g x, f (ρ g x) = ((χG g : (ZMod n)ˣ) : ZMod n) * f x
    constructor
    · intro hf g x
      have := congrArg (fun ψ : TDual (ZMod n) M => ψ (σ (e g) x)) (hf (e g))
      simp only [twDual_apply] at this
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hχ] at this
      rw [h, this]
    · intro hf g
      obtain ⟨g, rfl⟩ := e.surjective g
      refine DFunLike.ext _ _ fun x => ?_
      rw [twDual_apply, hχ, ← hf, h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

theorem UpperTheory.finiteLevel_cyclotomic_of_openEmbedding :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v), IsOpenEmbedding φ → FinLevelMod l G ((cyc v l).comp φ) (if v = l then φ.range.index else 0) := by
  intro P v l _ _ G _ _ _ φ hφ r hr M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨K, e, he, he', hc, -, hi, -⟩ := openField φ hφ
  have hc' : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => DFunLike.congr_fun hc g
  have hK := K.2
  by_cases hvl : v = l
  · subst hvl
    rw [if_pos rfl, hi]
    obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[v] (PadicAlgCl v) K.1
    let ε : G ≃* Formalism.GaloisCohomology.GK v K.1 := e.trans (IntermediateField.fixingSubgroupEquiv K.1)
    have hε : Continuous ε := hf.comp he
    have hε' : Continuous ε.symm := he'.comp hf'
    let σ : Representation (ZMod (v ^ r)) (Formalism.GaloisCohomology.GK v K.1) M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lfK v K.1 hK r M σ hr hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.ltK v K.1 hK r M σ hr hσ
    refine core ε hε hε' _ _ (fun g => ?_) ρ σ (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (P.leK v K.1 hK r M σ hr hσ)
    simp only [MonoidHom.comp_apply, ← hc']
    rfl
  · rw [if_neg hvl, pow_zero]
    let Ω := AlgebraicClosure ℚ
    have : IsAlgClosure ℚ Ω := AlgebraicClosure.instIsAlgClosure ℚ
    let j : Ω →+* PadicAlgCl v := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl v)).toRingHom
    let A : ValuationSubring Ω := (Valued.v (R := PadicAlgCl v)).valuationSubring.comap j
    have hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := fun x => by
      change Valued.v (j x) ≤ 1 ↔ _
      rw [PadicAlgCl.valuation_def]
      exact Iff.rfl
    have hAv : A.valuation (v : Ω) < 1 := by
      have h0 : 0 < ‖(v : PadicAlgCl v)‖ := norm_pos_iff.2 (by exact_mod_cast hv.ne_zero)
      have h1 : ((v : Ω))⁻¹ ∉ A := by
        rw [hA, map_inv₀, map_natCast, norm_inv, not_le]
        exact (one_lt_inv₀ h0).2 GlobalTheory.PlaceBridge.norm_l_lt_one
      rw [← A.valuation_le_one_iff, not_le, map_inv₀] at h1
      exact (one_lt_inv₀ (zero_lt_iff.2 (by simpa using hv.ne_zero))).1 h1
    obtain ⟨F, hF, hKF⟩ := numField K j A hA
    have : NumberField F := ⟨⟩
    have : IsAlgClosure F Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
    obtain ⟨w, hw, hwl⟩ := placeBelow hv F A hAv
    obtain ⟨d, hd, hd', hdc⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K hKF
    let ε := e.trans d.symm
    have hε : Continuous ε := hd'.comp he
    have hε' : Continuous ε.symm := he'.comp hd
    let σ : Representation (ZMod (l ^ r)) _ M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lf F Ω l r M A σ w hr hw hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.lt F Ω l r M A σ w hr hw hσ
    refine core ε hε hε' _ ((cycMod F Ω l r).comp (Subgroup.subtype _)) (fun g => Units.ext ?_) ρ σ
      (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (((P.le F Ω l r M A σ w hr hw hσ).2 (hwl l hl hvl)).trans (mul_one _).symm)
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    have : NeZero ((l : ℕ) : PadicAlgCl v) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
    have hζ' := hζ.map_of_injective j.injective
    have ha : (ε g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (ε g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (ε g : Ω ≃ₐ[F] Ω)) ζ
        hζ.pow_eq_one
    have hb : φ g (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (PadicAlgCl v) (φ g)) _
        hζ'.pow_eq_one
    have h3 : φ g (j ζ) = j ((ε g : Ω ≃ₐ[F] Ω) ζ) := by
      rw [← hdc, ← hc']
      simp [ε]
    rw [h3, ha, map_pow] at hb
    exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankPointDerivationsVanishingEqOfIsCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

section SlopeTestRemainingChoices
open MvPowerSeries

private theorem low_mem {R σ : Type} [CommRing R] [Finite σ] (m : Ideal (MvPowerSeries σ R))
    (hF : ∀ s, (MvPowerSeries.X s : MvPowerSeries σ R) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : truncTotal n g = 0) : g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.fg_idealOfVars σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    rw [hg]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem mem_sq {E σ : Type} [Field E] [Finite σ] (g : MvPowerSeries σ E)
    (h0 : MvPowerSeries.constantCoeff g = 0) (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) g = 0) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  refine low_mem _ (fun s => (mem_max _).2 (by simp)) 2 g ?_
  ext d
  rw [coeff_truncTotal_eq_ite]
  split_ifs with hd
  · have : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases this with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simpa using h0
    · obtain ⟨i, rfl⟩ : ∃ i, Finsupp.single i 1 = d := by
        have : d ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
          rw [Finsupp.range_single_one]; exact h
        exact this
      simpa using h1 i
  · simp

private theorem of_mem_sq {E σ : Type} [Field E] (g : MvPowerSeries σ E)
    (h : g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) g = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_single_mul, (mem_max _).1 ha, (mem_max _).1 hb]; simp
  · rw [map_add (f := _), ha, hb, add_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (P : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → ∀ T : Submodule E (R →ₗ[O] E), (∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧ ∀ a ∈ P, δ a = 0) → Module.finrank E ↥T = n := by
  intro O R E _ _ _ _ _ _ _ n P x φ H T hT
  classical
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hne : ∀ c : O, c ≠ 0 → algebraMap O E c ≠ 0 := fun c hc h => hc (hinj (by simpa using h))
  let D : Fin n → (R →ₗ[O] E) := fun i =>
    ((MvPowerSeries.coeff (Finsupp.single i 1) : MvPowerSeries (Fin n) E →ₗ[E] E).restrictScalars O).comp
      φ.toLinearMap
  have hD : ∀ i a, D i a = MvPowerSeries.coeff (Finsupp.single i 1) (φ a) := fun i a => rfl
  have hDT : ∀ i, D i ∈ T := fun i => (hT _).2 ⟨fun a b => by
      rw [hD, hD, hD, map_mul, coeff_single_mul, H.const, H.const], fun a ha => by
      rw [← H.ker, RingHom.mem_ker] at ha
      rw [hD, ha, map_zero]⟩

  have hex : ∀ i : Fin n, ∃ (a : R) (c : O), c ≠ 0 ∧ ∀ j, D j a = if j = i then algebraMap O E c else 0 := by
    intro i
    obtain ⟨a, c, hc, h⟩ := H.dense 2 (MvPowerSeries.X i)
    refine ⟨a, c, hc, fun j => ?_⟩
    have := of_mem_sq _ h j
    rw [map_sub, sub_eq_zero, ← hD, ← algebraMap_smul E c, map_smul, MvPowerSeries.coeff_X] at this
    rw [← this]
    simp [Finsupp.single_left_inj]
  choose a c hc ha using hex
  have h1 : ∀ δ ∈ T, δ 1 = 0 := fun δ hδ => by
    have := ((hT δ).1 hδ).1 1 1
    simpa using this
  have hker : ∀ δ ∈ T, ∀ r, (∀ i, D i r = 0) → δ r = 0 := by
    intro δ hδ r hr
    have hsub : ∀ δ ∈ T, δ (r - x r • 1) = δ r := fun δ hδ => by
      rw [map_sub, map_smul, h1 δ hδ, smul_zero, sub_zero]
    have hm : φ (r - x r • 1) ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2 := by
      refine mem_sq _ ?_ fun i => ?_
      · rw [H.const]; simp
      · rw [← hD, hsub _ (hDT i), hr]
    obtain ⟨k, hk, hmem⟩ := H.inj 2 _ hm
    have hz : ∀ s ∈ RingHom.ker x ^ 2 ⊔ P, δ s = 0 := by
      intro s hs
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hs
      rw [map_add (f := _), ((hT δ).1 hδ).2 v hv, add_zero]
      rw [pow_two] at hu
      refine Submodule.mul_induction_on hu (fun p hp q hq => ?_) (fun p q hp hq => ?_)
      · rw [RingHom.mem_ker] at hp hq
        rw [((hT δ).1 hδ).1, hp, hq]; simp
      · rw [map_add (f := _), hp, hq, add_zero]
    have := hz _ hmem
    rw [map_smul, hsub δ hδ, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this).resolve_left (hne k hk)
  let ev : T →ₗ[E] (Fin n → E) := LinearMap.pi fun i => (LinearMap.applyₗ' E (a i)).comp T.subtype
  have hev : ∀ (δ : T) i, ev δ i = (δ : R →ₗ[O] E) (a i) := fun _ _ => rfl
  have hbij : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro δ hδ
      ext r
      obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
        (fun i => D i r / algebraMap O E (c i))
      choose! b hb using hk
      have hz := hker δ δ.2 ((k : O) • r - ∑ i, b i • a i) (fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, map_smul]
        simp only [map_smul, ha, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Algebra.smul_def, Algebra.smul_def, hb j (Finset.mem_univ _), Algebra.smul_def]
        have := hne _ (hc j)
        field_simp
        ring)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, map_smul] at hz
      simp only [map_smul, ← hev, hδ, Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero] at hz
      rw [Algebra.smul_def] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hne k (nonZeroDivisors.coe_ne_zero k))
    · intro v
      refine ⟨∑ j, (v j / algebraMap O E (c j)) • ⟨D j, hDT j⟩, ?_⟩
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
      simp only [hev, Submodule.coe_smul, LinearMap.smul_apply, ha, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [smul_eq_mul, div_mul_cancel₀ _ (hne _ (hc i))]
  rw [(LinearEquiv.ofBijective ev hbij).finrank_eq]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCohomologyFiniteAndGrowthOfFinGen
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

open ReciprocityTheory.Coh in
private theorem latGrow_bound {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ)
    (hF : Cx.FinGen (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) 2) (k : ℕ) :
    ∃ C : ℕ, ∀ m : ℕ,
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat ≤
        m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) + C ∧
      m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) ≤
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat := by
  let L : TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρ, cont := h }
  refine ⟨(length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H k))).toNat +
    (length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H (k + 1)))).toNat, fun m => ?_⟩
  let C : TRep ℤ_[l] G := { V := _, rho := redRep ρ m, cont := contAction_redRep h m }
  have hc : Continuous (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) :=
    continuous_const_smul ((l : ℤ_[l]) ^ m)
  let i : Pair L L := Pair.ofMap (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) hc
    fun g x => (map_smul (ρ g) ((l : ℤ_[l]) ^ m) x).symm
  let p : Pair L C := Pair.ofMap (lSub l (Fin n → ℤ_[l]) m).mkQ (continuous_mkQ _) fun _ _ => rfl
  have hl : (l : ℤ_[l]) ^ m ≠ 0 := pow_ne_zero _ PadicInt.irreducible_p.ne_zero
  have hA : admitted i p := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · refine (hc.isClosedEmbedding ?_).isEmbedding
      exact smul_right_injective (Fin n → ℤ_[l]) hl
    · exact LinearMap.exact_map_mkQ_range _
    · exact ⟨Function.surjInv (lSub l (Fin n → ℤ_[l]) m).mkQ_surjective,
        continuous_of_discreteTopology (α := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m),
        Function.surjInv_eq _⟩
  have hR := (rankLen_holds ℤ_[l] (l : ℤ_[l]) PadicInt.irreducible_p L.coch C.coch i.hom p.hom m 2
    (fun _ _ => rfl) (admissibility_holds _ _ _ _ _ i p hA) hF).2.2 k
  exact ⟨hR.1.trans (add_assoc _ _ _).le, hR.2⟩

private theorem latGrow_card {l : ℕ} [Fact l.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[l] M]
    [AddCommGroup N] [Module ℤ_[l] N] [Finite N] (e : M ≃ₗ[ℤ_[l]] N) {a b : ℕ}
    (h : (length ℤ_[l] M).toNat ≤ b ∧ a ≤ (length ℤ_[l] M).toNat) :
    l ^ a ≤ Nat.card N ∧ Nat.card N ≤ l ^ b := by
  obtain ⟨k, hk, hc⟩ := UpperTheory.V.Kum.lenOfCard l N
  rw [e.length_eq, hk, ENat.toNat_coe] at h
  rw [hc]
  have hp : 0 < l := (Fact.out : l.Prime).pos
  exact ⟨Nat.pow_le_pow_right hp h.2, Nat.pow_le_pow_right hp h.1⟩

open ReciprocityTheory.Coh in
theorem UpperTheory.lattice_cohomology_finite_and_growth_of_finGen :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 → (∀ m, Finite (H1 (redRep ρ m)) ∧ Finite (H2 (redRep ρ m))) → Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧ Grows l (fun m => Nat.card ↥(H0 (redRep ρ m))) (finrank ℤ_[l] ↥(H0 ρ)) ∧ Grows l (fun m => Nat.card (H1 (redRep ρ m))) (finrank ℤ_[l] (H1 ρ)) ∧ Grows l (fun m => Nat.card (H2 (redRep ρ m))) (finrank ℤ_[l] (H2 ρ)) := by
  intro l _ G _ _ _ n ρ h hF hfin
  obtain ⟨-, ⟨e₀, -⟩, ⟨e₁, -⟩, e₂, -⟩ :=
    low_holds ℤ_[l] G ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)
  have hq := fun m => low_holds ℤ_[l] G ({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G)
  haveI := hF.1 1
  haveI := hF.1 2
  refine ⟨Module.Finite.equiv e₁, Module.Finite.equiv e₂, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 0
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, ⟨q, -⟩, -⟩ := hq m
    rw [e₀.finrank_eq] at hC
    haveI : Finite (H0 (redRep ρ m)) := inferInstance
    exact latGrow_card (N := H0 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 1
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, ⟨q, -⟩, -⟩ := hq m
    rw [e₁.finrank_eq] at hC
    haveI := (hfin m).1
    exact latGrow_card (N := H1 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 2
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, -, q, -⟩ := hq m
    rw [e₂.finrank_eq] at hC
    haveI := (hfin m).2
    exact latGrow_card (N := H2 (redRep ρ m)) q (hC m)
end

