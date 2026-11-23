module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0010
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

private theorem int_mem (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

omit [NumberField L] in
private theorem int_mem' (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  exact int_mem A (RingOfIntegers.isIntegral_coe x).algebraMap

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  classical
  let f : 𝓞 L →+* A :=
    { toFun := fun x => ⟨algebraMap L Ω (x : L), int_mem' A x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔
      A.valuation (algebraMap L Ω (x : L)) < 1 := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hv : ∀ y : 𝓞 K, algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) y : 𝓞 L) : L) =
      algebraMap K Ω (y : K) := by
    intro y
    rw [IsScalarTower.algebraMap_apply K L Ω]
    congr 1
  obtain ⟨y, hyv, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hyP : algebraMap (𝓞 K) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap f := by
    rw [hmem, hv]
    exact (hA y).mpr hyv
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, Ideal.comap_isPrime f _, ?_⟩, ?_, ?_⟩
  · intro h
    rw [h, Ideal.mem_bot] at hyP
    apply hy0
    have h1 : algebraMap K Ω (y : K) = 0 := by
      rw [← hv, hyP]
      simp
    have h2 : (y : K) = 0 := (map_eq_zero_iff _ (algebraMap K Ω).injective).mp h1
    exact_mod_cast h2
  · intro x
    exact (hmem x).symm
  · refine ⟨Ideal.ext fun z => ?_⟩
    change z ∈ v.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) z ∈ (IsLocalRing.maximalIdeal A).comap f
    rw [hmem, hv]
    exact (hA z).symm

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
private theorem coe_res_smul (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) :=
  AlgEquiv.restrictNormal_commutes σ L (x : L)

private theorem res_frob {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal] {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  have hq : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) = normV v := by
    rw [← h.over]
    rfl
  intro x
  rw [hq]
  refine (hw _).mp ?_
  simp only [MulSemiringAction.toAlgHom_apply, map_sub, map_pow, coe_res_smul]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (int_mem' A x))

end SlopeTestRemainingChoices

open GroundTheory.Global in
theorem UpperTheory.V.Kum.artFrob :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω), IsPlaceOver A v → IsFrob (F := K) A (normV v) σ → artCl K Ω σ = primeCl v := by
  intro K Ω _ _ _ _ _ A v σ hA hσ
  haveI := IsAlgClosure.isAlgClosed K (K := Ω)
  obtain ⟨w, hw, hlo⟩ := place_between (L := hilbertClassField K Ω) hA
  have hf := res_frob hw hσ
  have h2 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(hilbertClassField K Ω/K) w.asIdeal
  have hin := hf.mul_inv_mem_inertia h2
  have hcard : Nat.card (Ideal.inertia Gal(hilbertClassField K Ω/K) w.asIdeal) = 1 := by
    rw [natCard_inertia v w]
    exact (isUnramifiedIn_iff_ramificationIdx K (hilbertClassField K Ω) v).mp
      ((isUnramifiedEverywhere_hilbertClassField K Ω).1 v) w hlo
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot, mul_inv_eq_one] at hin
  unfold artCl primeCl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq,
    hilbertClassFieldArtinEquiv_mk0 K Ω v w]
  exact hin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (b : 𝓞 Ω) : A.valuation (b : Ω) ≤ 1 := by
  have h : IsIntegral A (b : Ω) := b.isIntegral_coe.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_cen {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∃ Q : Ideal (𝓞 Ω), Q.IsPrime ∧ ∀ b : 𝓞 Ω, b ∈ Q ↔ A.valuation (b : Ω) < 1 := by
  let f : 𝓞 Ω →+* A := (algebraMap (𝓞 Ω) Ω).codRestrict A fun b => (A.valuation_le_one_iff _).1 (int_le A b)
  exact ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun b => A.valuation_lt_one_iff (f b)⟩

open GroundTheory.Global in
private theorem restrict_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) [NumberField L] [IsGalois E L] (hL : IsUnramifiedEverywhere E L)
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) (hg : ∀ x, A.valuation x ≤ 1 → A.valuation (g x - x) < 1) :
    AlgEquiv.restrictNormalHom L g = 1 := by
  obtain ⟨Q, hQ, hmem⟩ := exists_cen A
  have hc : ∀ x : 𝓞 L, AlgEquiv.restrictNormalHom L g • x - x ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_comap, map_sub, hmem]
    have := hg _ (int_le A (algebraMap (𝓞 L) (𝓞 Ω) x))
    have e : ((algebraMap (𝓞 L) (𝓞 Ω) (AlgEquiv.restrictNormalHom L g • x) : 𝓞 Ω) : Ω) =
        g (algebraMap (𝓞 L) (𝓞 Ω) x : 𝓞 Ω) := AlgEquiv.restrictNormal_commutes g L x
    rwa [← e] at this
  by_cases hP : Q.under (𝓞 L) = ⊥
  · have h0 : ∀ x : 𝓞 L, AlgEquiv.restrictNormalHom L g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x := fun x =>
      congrArg (algebraMap (𝓞 L) L) (sub_eq_zero.1 ((Submodule.mem_bot _).1 (hP.le (hc x))))
    ext1 y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
    rw [map_div₀, h0, h0, AlgEquiv.one_apply]
  · let w : HeightOneSpectrum (𝓞 L) := ⟨_, inferInstance, hP⟩
    have hwv : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 E) w).asIdeal := ⟨rfl⟩
    have hram := (isUnramifiedIn_iff_ramificationIdx E L _).1
      (hL.1 _) w hwv
    have hI : w.asIdeal.inertia (L ≃ₐ[E] L) = ⊥ := by
      rw [← Subgroup.card_eq_one, natCard_inertia (HeightOneSpectrum.under (𝓞 E) w) w, hram]
    exact Subgroup.mem_bot.1 (hI ▸ hc)

open GroundTheory.Global in
private theorem restrict_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) [NumberField L] [IsGalois E L] (hL : IsUnramifiedEverywhere E L)
    (g : Ω ≃ₐ[E] Ω) (j : Ω →+* ℂ) (hj : ∀ x, j (g x) = starRingEnd ℂ (j x)) :
    AlgEquiv.restrictNormalHom L g = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let j₀ : L →+* ℂ := j.comp (algebraMap _ Ω)
  have hE : ComplexEmbedding.IsReal (j₀.comp (algebraMap E _)) := by
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hj (algebraMap E Ω y)).symm.trans (congrArg j (g.commutes y))
  have hu := hL.2 _ (InfinitePlace.mk j₀) rfl
  rw [InfinitePlace.isUnramified_iff, InfinitePlace.comap_mk, ← InfinitePlace.not_isReal_iff_isComplex,
    InfinitePlace.isReal_mk_iff, InfinitePlace.isReal_mk_iff] at hu
  have hr := ComplexEmbedding.isReal_iff.1 (hu.resolve_right fun h => h hE)
  apply j.injective
  rw [hj]
  exact DFunLike.congr_fun hr ⟨x, hx⟩

theorem UpperTheory.V.Kum.artIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ (A : ValuationSubring Ω), ∀ g ∈ Ine (F := K) A, artCl K Ω g = 1) ∧ ∀ c : G K Ω, IsConjOm c.toRingEquiv → artCl K Ω c = 1 := by
  intro K Ω _ _ _ _ _
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : NumberField (GroundTheory.Global.hilbertClassField K Ω) := NumberField.of_module_finite K _
  have hL := GroundTheory.Global.isUnramifiedEverywhere_hilbertClassField K Ω
  refine ⟨fun A g hg => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom _ g) = 1
    rw [restrict_ine _ hL A g hg.2, map_one]
  · show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom _ c) = 1
    rw [restrict_conj _ hL c j hj, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open CompanionTheory.PlaceDict in
private theorem exists_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [Algebra.IsAlgebraic E Ω] (L : IntermediateField E Ω) [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ A : ValuationSubring Ω, (cen A).IsMaximal ∧ (cen A).under (𝓞 L) = w.asIdeal := by
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  exact ⟨A, hQ, hw⟩

open CompanionTheory.PlaceDict in
private theorem lift_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  obtain ⟨A, hm, hw⟩ := exists_over L w
  obtain ⟨φ, h1, h2⟩ := lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact (hw.ge (hτ x) :)
  obtain ⟨h3, h4⟩ := of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

private theorem exists_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (L : IntermediateField E Ω) (j₀ : L →+* ℂ)
    (hE : ComplexEmbedding.IsReal (j₀.comp (algebraMap E L))) :
    ∃ c : Ω ≃ₐ[E] Ω, IsConjOm c.toRingEquiv ∧ ∀ x : L, c x = x → starRingEnd ℂ (j₀ x) = j₀ x := by
  let _ : Algebra L ℂ := j₀.toAlgebra
  let _ : Algebra E ℂ := (j₀.comp (algebraMap E L)).toAlgebra
  have : IsScalarTower E L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := E) L
  let j : Ω →ₐ[L] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j₁ : Ω →ₐ[E] ℂ := j.restrictScalars E
  let j₂ : Ω →ₐ[E] ℂ :=
    { (starRingEnd ℂ).comp j₁.toRingHom with
      commutes' := fun y => by
        show starRingEnd ℂ (j₁ (algebraMap E Ω y)) = _
        rw [j₁.commutes]
        exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hE) y }
  let _ : Algebra Ω ℂ := j₁.toRingHom.toAlgebra
  have : IsScalarTower E Ω ℂ := IsScalarTower.of_algebraMap_eq fun y => (j₁.commutes y).symm
  have hc : ∀ x, j₁ (j₂.restrictNormal' Ω x) = starRingEnd ℂ (j₁ x) := fun x => j₂.restrictNormal_commutes Ω x
  refine ⟨j₂.restrictNormal' Ω, ⟨j₁.toRingHom, hc⟩, fun x hx => ?_⟩
  have := hc x
  rw [hx] at this
  have e : j₁ x = j₀ x := j.commutes x
  rw [← e]
  exact this.symm

open GroundTheory.Global IntermediateField in
private theorem hilbert_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] [IsAlgClosed Ω] (H : Subgroup (Ω ≃ₐ[E] Ω)) (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hcm : commutator (Ω ≃ₐ[E] Ω) ≤ H) (hI : ∀ A : ValuationSubring Ω, Ine (F := E) A ≤ H)
    (hc : ∀ c : Ω ≃ₐ[E] Ω, IsConjOm c.toRingEquiv → c ∈ H) :
    (hilbertClassField E Ω).fixingSubgroup ≤ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hfix : (fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  generalize fixedField H = L at hfix
  subst hfix
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite _).1 ho
  have : IsGalois E L := (InfiniteGalois.normal_iff_isGalois _).1 (Subgroup.Normal.of_commutator_le _ hcm)
  have : NumberField L := NumberField.of_module_finite E _
  have hker : ∀ g ∈ L.fixingSubgroup, AlgEquiv.restrictNormalHom L g = 1 := fun g hg => by
    rw [← MonoidHom.mem_ker, restrictNormalHom_ker]
    exact hg
  have : IsAbelianGalois E L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) a
        obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) b
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact hker _ (hcm (Subgroup.commutator_mem_commutator trivial trivial))⟩ }
  refine fixingSubgroup_le ((le_hilbertClassField_iff E Ω L).2 ⟨fun v => ?_, fun v w hw => ?_⟩)
  · rw [isUnramifiedIn_iff_ramificationIdx]
    intro w hw
    rw [← natCard_inertia v w, Subgroup.card_eq_one, eq_bot_iff]
    intro τ hτ
    obtain ⟨A, φ, h1, h2⟩ := lift_ine L w τ hτ
    rw [Subgroup.mem_bot, ← h1]
    exact hker _ (hI A h2)
  · rw [InfinitePlace.isUnramified_iff, ← InfinitePlace.not_isReal_iff_isComplex, ← w.mk_embedding,
      InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, InfinitePlace.isReal_mk_iff, or_iff_not_imp_right, not_not]
    intro hE
    obtain ⟨c, hc', h⟩ := exists_conj L w.embedding hE
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact h y ((mem_fixingSubgroup_iff _ _).1 (hc c hc') _ y.2)

theorem UpperTheory.V.Kum.artKer :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (C : Type) [CommGroup C] (χ : G K Ω →* C), IsOpen (χ.ker : Set (G K Ω)) → (∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker) →
    (∀ c : G K Ω, IsConjOm c.toRingEquiv → χ c = 1) → (artCl K Ω).ker ≤ χ.ker := by
  intro K Ω _ _ _ _ _ C _ χ ho hI hc g hg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  refine hilbert_le χ.ker ho (Abelianization.commutator_subset_ker χ) hI hc ?_
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
  exact (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm.map_eq_one_iff.1 hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.artSurj :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Function.Surjective (artCl K Ω) ∧ IsLocallyConstant (artCl K Ω) := by
  intro K Ω _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set L := GroundTheory.Global.hilbertClassField K Ω
  have hL : IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker : Set (G K Ω)) := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isOpen L
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker ≤ (artCl K Ω).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L x) = 1
    rw [hx, map_one]
  have hopen : IsOpen ((artCl K Ω).ker : Set (G K Ω)) := Subgroup.isOpen_mono hker hL
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω
      (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω y)
    refine ⟨σ, ?_⟩
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L σ) = y
    rw [hσ, MulEquiv.symm_apply_apply]
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ g, artCl K Ω g = y
    · obtain ⟨g, rfl⟩ := hy
      have : (artCl K Ω) ⁻¹' {artCl K Ω g} = (fun x => g⁻¹ * x) ⁻¹' ((artCl K Ω).ker : Set (G K Ω)) := by
        ext x
        rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]
      rw [this]
      exact hopen.preimage (continuous_const_mul g⁻¹)
    · push_neg at hy
      have : (artCl K Ω) ⁻¹' {y} = ∅ := by
        ext x
        simp [hy x]
      rw [this]
      exact isOpen_empty
end

