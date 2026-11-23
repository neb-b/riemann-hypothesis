module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquiv
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransport

open scoped Pointwise

section Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']

theorem valuation_le_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y ≤ 1 ↔ A'.valuation (φ y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
  exact ValuationSubring.mem_comap

theorem valuation_lt_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y < 1 ↔ A'.valuation (φ y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_eq_zero_iff _ φ.injective]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀]

variable [NumberField E] [NumberField E'] (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') {σ : G E Ω} {τ : G E' Ω'}

theorem mem_Dec_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Dec (F := E') A') :
    σ ∈ Dec (F := E) (A'.comap φ.toRingHom) := by
  have hx : ∀ x, σ x ∈ A'.comap φ.toRingHom ↔ x ∈ A'.comap φ.toRingHom := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show φ (σ x) ∈ A' ↔ φ x ∈ A'
    rw [h]
    exact apply_mem_iff_of_mem_Dec hτ (φ x)
  show σ • A'.comap φ.toRingHom = A'.comap φ.toRingHom
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hx, mul_inv_apply]

theorem isFrob_comap (h : ∀ z, φ (σ z) = τ (φ z)) {q : ℕ} (hτ : IsFrob (F := E') A' q τ) :
    IsFrob (F := E) (A'.comap φ.toRingHom) q σ := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, map_pow, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

theorem mem_Ine_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Ine (F := E') A') :
    σ ∈ Ine (F := E) (A'.comap φ.toRingHom) := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

end Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']

theorem exists_conj (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (τ : G E' Ω') : ∃ σ : G E Ω, ∀ z, φ (σ z) = τ (φ z) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun x => ?_, fun z => ?_⟩
  · show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
    rw [hφ, AlgEquiv.commutes, ← hφ, φ.symm_apply_apply]
  · show φ (φ.symm (τ (φ z))) = τ (φ z)
    exact φ.apply_symm_apply _

theorem isPlaceOver_comap [NumberField E] [NumberField E'] (φ : Ω ≃+* Ω')
    (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) {A' : ValuationSubring Ω'}
    (hA : IsPlaceOver A' w) : IsPlaceOver (A'.comap φ.toRingHom) v := by
  intro x
  rw [valuation_lt_one_comap, hφ, ← hwv, Ideal.mem_comap, ← hA (algebraMap (𝓞 E) (𝓞 E') x)]
  rfl

theorem normV_eq_pow [NumberField E] [NumberField E'] {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

end GlobalTheory.ArtinTransport

namespace GlobalTheory.ArtinTransport

theorem chi_artin_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ _ φ hφ art art' ha ha' ρ hρ B _ χ v w hwv hχ
  obtain ⟨A', hA'⟩ := exists_isPlaceOver (F := E') Ω' w
  have hA : IsPlaceOver (A'.comap φ.toRingHom) v := isPlaceOver_comap φ hφ hwv hA'

  have hI : ∀ ι ∈ Ine (F := E) (A'.comap φ.toRingHom), χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v _ hA (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨τ, hτ, e⟩ := (ha'.ine w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    rw [← e, hρ τ σ hσ]
    exact hI σ (mem_Ine_comap A' φ hσ hτ)
  · obtain ⟨τ, hτ, e⟩ := (ha'.frob w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ₀, hσ₀, e₀⟩ := (ha.frob v _ hA _).mp ⟨ϖ, hϖ, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    have hσi : ∀ z, φ (σ⁻¹ z) = τ⁻¹ (φ z) := by
      intro z
      have h1 : τ (τ⁻¹ (φ z)) = τ (φ (σ⁻¹ z)) := by
        rw [mul_inv_apply, ← hσ, mul_inv_apply]
      exact (τ.injective h1).symm
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hF : IsFrob (F := E) (A'.comap φ.toRingHom) (normV v ^ f) σ := by
      rw [← normV_eq_pow hwv]
      exact isFrob_comap A' φ hσ hτ
    have hm := hI _ (inv_mul_mem_Ine_of_isFrob (GlobalTheory.FrobRestrict.isFrob_pow hσ₀ f) hF)
    rw [← e, hρ _ _ hσi, ← e₀, map_inv, map_inv, map_inv, map_inv, inv_pow, inv_inj]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    exact (inv_mul_eq_one.mp hm).symm

end GlobalTheory.ArtinTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH0LevelRepEq
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem card_ker_eq_card_quot_range {O : Type} [CommRing O] {N : Type} [AddCommGroup N] [Module O N]
    [Finite N] (f : N →ₗ[O] N) :
    Nat.card (LinearMap.ker f) = Nat.card (N ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card (N ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr (f.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [h3] at h1
  rw [h1] at h2
  nlinarith [h2]

def invariantsOfKilledLevelEquiv {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O) :
    ReciprocityTheory.Gal.H0 (levRep ρ c) ≃
      LinearMap.ker (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) where
  toFun x := ⟨⟨x.1.val, fun g => by
      have h : levRep ρ c g x.1 = x.1 := x.2 g
      have := congrArg Lev.val h
      rwa [levRep_val] at this⟩, by
      apply Subtype.ext
      show c • x.1.val = 0
      exact Lev.smul_val x.1⟩
  invFun y := ⟨Lev.mk y.1.1 (by
      have h : (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) y.1 = 0 := y.2
      exact congrArg Subtype.val h), by
      show ∀ g, _
      intro g
      apply Lev.ext
      rw [levRep_val, Lev.val_mk]
      exact y.1.2 g⟩
  left_inv x := by
    apply Subtype.ext
    apply Lev.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem card_H0_level_rep : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ c hfin
  rw [Nat.card_congr (invariantsOfKilledLevelEquiv ρ c)]
  exact card_ker_eq_card_quot_range _

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernelStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_unramified_outside_vanish_on_kernel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  first | exact @GlobalTheory.UnramCocycle.vanish_on_NS | exact GlobalTheory.UnramCocycle.vanish_on_NS | (intros; apply GlobalTheory.UnramCocycle.vanish_on_NS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem contAction_levRepZ_of_isLocallyConstant
    {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (hloc : ∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) :
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, x₀⟩
  have hx := hloc x₀.val (Lev.smul_val x₀)
  refine ⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀},
    (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, x⟩ ⟨hg, hx'⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst hx'
  apply Lev.ext
  show (levRep ρ c g x).val = (levRep ρ c g₀ x).val
  rw [levRep_val, levRep_val]
  exact hg

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterIsLocallyConstantModPow
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem cyclotomic_isLocallyConstant_mod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ) (hε : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) (N : ℕ) :
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  have hp : p.Prime := Fact.out
  have hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.ne_zero
  haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)
  have hint : IsIntegral K ζ := (hζ.isIntegral (pow_pos hp.pos N)).tower_top
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O) := by
    intro σ τ h
    obtain ⟨a, ha, ha'⟩ := hε σ N ζ hζ.pow_eq_one
    obtain ⟨b, hb, hb'⟩ := hε τ N ζ hζ.pow_eq_one
    have hab : ζ ^ a = ζ ^ b := by rw [← ha, ← hb, h]
    have hmod : a ≡ b [MOD p ^ N] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab
    obtain ⟨c, hc⟩ := hmod.dvd
    have hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O) := by
      have := congrArg (Int.cast : ℤ → O) hc
      push_cast at this
      exact this
    rw [Ideal.Quotient.eq]
    have e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) =
        (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a) := by ring
    rw [e, hc']
    exact Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro τ hτ
    apply key
    have h1 : (σ⁻¹ * τ) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)
    have h2 := congrArg σ h1
    simpa using h2

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPowNeOneOfMovesRoot
section
open ReciprocityTheory.Gal
namespace GlobalTheory.ShapeNeg

theorem int_dvd_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime)
    [IsLocalRing O] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0) (n : ℕ) (z : ℤ)
    (hz : (z : O) ∈ Ideal.span {(p : O) ^ n}) : (p : ℤ) ^ n ∣ z := by
  have hd : z.gcd ((p : ℤ) ^ n) ∣ p ^ n := by
    have := Int.gcd_dvd_right (a := z) (b := (p : ℤ) ^ n)
    have h2 : ((z.gcd ((p : ℤ) ^ n) : ℕ) : ℤ) ∣ ((p ^ n : ℕ) : ℤ) := by push_cast; exact this
    exact_mod_cast h2
  obtain ⟨m, hm, hgm⟩ := (Nat.dvd_prime_pow hp).1 hd
  rcases lt_or_eq_of_le hm with hlt | heq
  · exfalso
    have hb := Int.gcd_eq_gcd_ab z ((p : ℤ) ^ n)
    rw [hgm] at hb
    have hmem : ((p : O) ^ m) ∈ Ideal.span {(p : O) ^ n} := by
      have : (((p ^ m : ℕ) : ℤ) : O) = (z : O) * (z.gcdA ((p : ℤ) ^ n) : O)
          + ((p : O) ^ n) * (z.gcdB ((p : ℤ) ^ n) : O) := by
        rw [hb]; push_cast; ring
      have e : (((p ^ m : ℕ) : ℤ) : O) = (p : O) ^ m := by push_cast; ring
      rw [← e, this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz)
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    have hsplit : (p : O) ^ n = (p : O) ^ m * (p : O) ^ (n - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_assoc] at hc
    have h1 : (p : O) ^ (n - m) * c = 1 := by
      have hne : (p : O) ^ m ≠ 0 := pow_ne_zero _ hp0
      have := mul_left_cancel₀ hne (hc.symm.trans (mul_one _).symm)
      exact this
    have hu : IsUnit ((p : O) ^ (n - m)) := isUnit_iff_exists_inv.2 ⟨c, h1⟩
    rw [isUnit_pow_iff (Nat.sub_ne_zero_of_lt hlt)] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  · have := Int.gcd_dvd_left (a := z) (b := (p : ℤ) ^ n)
    rw [hgm, heq] at this
    exact_mod_cast this

theorem cyc_char_pow_ne_one : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 →
    ∀ ε : Formalism.GaloisCohomology.GK p K →* Oˣ, (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ k : ℕ,
    (∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ) →
    ∃ σ : Formalism.GaloisCohomology.GK p K, ε σ ^ k ≠ 1 := by
  intro p hpF K O _ _ _ hpm hp0 ε hcyc k ⟨σ, n, ζ, hζ, hne⟩
  refine ⟨σ, fun hk => hne ?_⟩
  obtain ⟨a, ha, hmem⟩ := hcyc (σ ^ k) n ζ hζ
  rw [map_pow, hk, Units.val_one] at hmem
  have hz : (((a : ℤ) - 1 : ℤ) : O) ∈ Ideal.span {(p : O) ^ n} := by
    have := (Ideal.neg_mem_iff _).2 hmem
    push_cast
    convert this using 1; ring
  obtain ⟨t, ht⟩ := int_dvd_of_mem_span_pow hpF.out hpm hp0 n _ hz
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hpF.out.ne_zero)] at hζ
    exact zero_ne_one hζ
  rw [ha, ← zpow_natCast, show (a : ℤ) = 1 + (p : ℤ) ^ n * t by omega, zpow_add₀ hζ0, zpow_mul,
    zpow_one]
  have : ζ ^ ((p : ℤ) ^ n) = 1 := by
    rw [show ((p : ℤ) ^ n) = ((p ^ n : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, hζ]
  rw [this, one_zpow, mul_one]

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | exact GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLtCommutatorMemOfNeTopStatement
section
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  first | exact @GlobalTheory.exists_lt_commutator_mem_of_ne_top | exact GlobalTheory.exists_lt_commutator_mem_of_ne_top | (intros; apply GlobalTheory.exists_lt_commutator_mem_of_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.FinPlaceApproxPos

theorem exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.FinPlaceApprox.approx_target F T t M
  set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  set d : ℕ := Ideal.absNorm J with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hdJ : ((d : ℤ) : 𝓞 F) ∈ J := by
    simpa [hd] using Ideal.absNorm_mem J
  have hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M := fun v hv =>
    Ideal.prod_le_inf.trans (Finset.inf_le hv)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  refine ⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩
  · have hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M := by
      apply hJv v hv
      have : ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F) := by push_cast; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hdJ
    have hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ)) := by
      have : ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F) := by simp
      rw [this, HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
    have : a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)
  · have h1 : φ a₀ ≥ -B := by
      have := hB ⟨φ, rfl⟩
      have := neg_abs_le (φ a₀)
      simp only at *
      linarith
    have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    have hNB : B < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil B) (by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [map_add (f := _), map_natCast]
    push_cast
    nlinarith

theorem approxpos_target : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M

end GlobalTheory.FinPlaceApproxPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem KO_divisible_by_uniformiser : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]

end GlobalTheory
end

