module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKExp

theorem muPow_smul_crisVal_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hEM : y ∈ D.toPhiMod.EM η := hyY.1
  obtain ⟨-, hLA⟩ := _root_.GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm
  obtain ⟨c, hc⟩ := hLA
  have hU := ((_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ).2.2.2.1
  obtain ⟨z, hz⟩ := ((_root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩
  have hC := ((_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := rfl
  have hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n := by
    intro n
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
    intro n
    rw [hpow, e1]
    exact (hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef
  obtain ⟨u, hu⟩ := hunit (H + η)
  have hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀)
      ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i))) := by
    refine ⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩
    rw [← hu, smul_smul, Units.mul_inv, one_smul]
  have hb0 := hC _ _ _ hb hval
  have hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i)) := by
    rw [hb0, ← hu, smul_smul, Units.mul_inv, one_smul]
  set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'
  have hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c' := by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hc', map_mul]
  rw [hL] at hz
  have hcmp := R.cmp c' z hz
  refine ⟨z, ?_⟩
  rw [← hcmp]
  have e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m := by
    rw [hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]
    ring_nf
  have e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m := by
    first
    | rw [e2, map_mul]
    | rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]; ring_nf
  rw [e3, mul_smul, hmain, ← map_smul]
  congr 1
  funext i
  simp [hc', map_mul]

end GlobalTheory.BKExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfMemInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_sub_lt_one_of_mem_inertia {l : ℕ} [Fact l.Prime] (K : FinExt l) (σ : ↥(GK K)) (hσ : σ ∈ IK K) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  unfold IK at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ h => exact h
  | one => intro x _; simp
  | mul σ τ _ _ hσ hτ =>
    intro x hx
    have h1 : ‖(τ : GQ l) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have e : ((σ * τ : ↥(GK K)) : GQ l) x - x
        = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))
  | inv σ _ hσ =>
    intro x hx
    have h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have h2 := hσ _ h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev] at h2
    rw [Subgroup.coe_inv]
    exact h2

theorem noTower : NoTower := by
  classical
  intro l _ K N hanti hopen hpow hroot hchar
  have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
  have hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen _
  have hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k := fun k σ =>
    Subgroup.mem_map_iff_mem (GK K).subtype_injective
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.PMon.Ram.noTowerQ_holds l (fun k => (N k).map (GK K).subtype)
    (fun i j hij => Subgroup.map_mono (hanti hij))
    (fun k => hGK.isOpenMap_subtype_val _ (hopen k))
    (by
      rintro k _ ⟨σ, hσ, rfl⟩
      exact ⟨σ ^ l, hpow k σ hσ, rfl⟩)
    (by
      rintro j _ ⟨σ, hσ, rfl⟩ h
      exact ⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)
    (by
      intro r
      obtain ⟨k₀, hk₀⟩ := hchar r
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨ι, hι, x, a, h1, h2⟩ := hk₀ k hk
      have key := fun i => _root_.GlobalTheory.PMon.Ram.approx_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i)
        (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by
          rintro _ ⟨σ, hσ, rfl⟩
          have := h1 i σ hσ
          simpa using this)
      choose y b hy hb using key
      refine ⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩
      rintro _ ⟨σ, hσ, rfl⟩ h
      refine ⟨σ, h2 σ hσ fun i => ?_, rfl⟩
      have := hb i _ (h i)
      simpa using this)
  refine ⟨k, fun j σ hσ => ?_⟩
  exact (hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSup
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.RayCompositum

open GlobalTheory.NT GlobalTheory.FieldSize GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.RayMaximal

variable {K : Type} [Field K] [NumberField K]

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem heckeIdeal_comp_restrictNormalHom {L M : Type} [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L] [IsGalois K M] {𝔪 : Ideal (𝓞 K)}
    (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → _root_.GlobalTheory.NT.UnramIn M 𝔭)
    (χ : Gal(L/K) →* ℂˣ) {I : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hI : IsCoprime I 𝔪) :
    _root_.GlobalTheory.NT.heckeIdeal M (χ.comp (AlgEquiv.restrictNormalHom L)) I =
      _root_.GlobalTheory.NT.heckeIdeal L χ I := by
  unfold _root_.GlobalTheory.NT.heckeIdeal
  refine finprod_congr fun 𝔭 => ?_
  by_cases hc : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors = 0
  · simp [hc]
  · have hdvd : 𝔭.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI0 𝔭.irreducible).1 hc
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔪 := by
      intro h
      rw [Ideal.dvd_iff_le] at hdvd h
      exact 𝔭.isPrime.ne_top (top_unique ((Ideal.isCoprime_iff_sup_eq.1 hI).ge.trans (sup_le hdvd h)))
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NT.exists_isFrob M 𝔭
    have hu := hM 𝔭 hnd
    rw [_root_.GlobalTheory.NT.heckeVal_of_unramIn M _ hu hσ,
      _root_.GlobalTheory.NT.heckeVal_of_unramIn L χ (_root_.GlobalTheory.RayMaximal.unramIn_of_tower hu)
        (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal hσ)]
    rfl

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem not_isUnit_natCast_of_prime' {F : Type} [Field F] [NumberField F] {q : ℕ}
    (hq : q.Prime) : ¬ IsUnit ((q : 𝓞 F)) := by
  intro h
  have h' := h.map (Algebra.norm ℤ)
  rw [show ((q : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (q : ℤ) by simp, Algebra.norm_algebraMap] at h'
  have hn : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h'
  have := hq.two_le
  omega

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem isCoprime_of_le_right {R : Type} [CommRing R] {I J J' : Ideal R}
    (h : IsCoprime I J) (hJ : J ≤ J') : IsCoprime I J' := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact top_unique (h.ge.trans (sup_le_sup_left hJ _))

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem mem_of_mul_mem_of_isCoprime_span {R : Type} [CommRing R] {J : Ideal R} {y z : R}
    (h : IsCoprime (Ideal.span {y}) J) (hyz : y * z ∈ J) : z ∈ J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hi
  have : z = c * (y * z) + z * j := by linear_combination (-z) * hij
  rw [this]
  exact J.add_mem (J.mul_mem_left _ hyz) (J.mul_mem_left _ hj)

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem exists_rayPair_inf_of_rayPair (hu : ∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1)
    {𝔞 𝔟 : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 𝔞 ≤ Ideal.span {(q : 𝓞 K)}) (hb : 𝔟 ≤ Ideal.span {(q : 𝓞 K)}) {I : Ideal (𝓞 K)}
    {α β α' β' : 𝓞 K} (h₁ : _root_.GlobalTheory.NT.RayPair 𝔞 α β) (e₁ : I * Ideal.span {β} = Ideal.span {α})
    (h₂ : _root_.GlobalTheory.NT.RayPair 𝔟 α' β') (e₂ : I * Ideal.span {β'} = Ideal.span {α'}) :
    ∃ γ δ, _root_.GlobalTheory.NT.RayPair (𝔞 ⊓ 𝔟) γ δ ∧ I * Ideal.span {δ} = Ideal.span {γ} := by
  obtain ⟨hα0, hβ0, hαc, hβc, hd, hpos⟩ := h₁
  obtain ⟨hα0', hβ0', hαc', hβc', hd', hpos'⟩ := h₂
  have hqtop : Ideal.span {(q : 𝓞 K)} ≠ ⊤ := fun h =>
    not_isUnit_natCast_of_prime' hq (Ideal.span_singleton_eq_top.1 h)
  have hspan : Ideal.span {α * β'} = Ideal.span {α' * β} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      ← e₁, ← e₂]
    ring
  obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  have key : α * β' = α' * β := by
    rcases hu u with rfl | rfl
    · simpa using hu'
    · exfalso
      have hneg : α' * β = -(α * β') := by rw [← hu']; simp
      have h2mem : 2 * α * β' ∈ Ideal.span {(q : 𝓞 K)} := by
        have : 2 * α * β' = β' * (α - β) - β * (α' - β') := by linear_combination hneg
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (ha hd)) (Ideal.mul_mem_left _ _ (hb hd'))
      have h2 : IsCoprime (Ideal.span {(2 : 𝓞 K)}) (Ideal.span {(q : 𝓞 K)}) := by
        rw [Ideal.isCoprime_span_singleton_iff]
        have hz : IsCoprime ((2 : ℕ) : ℤ) (q : ℤ) :=
          Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
        simpa using hz.map (Int.castRingHom (𝓞 K))
      have hc : IsCoprime (Ideal.span {2 * α * β'}) (Ideal.span {(q : 𝓞 K)}) := by
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
        exact (h2.mul_left (isCoprime_of_le_right hαc ha)).mul_left (isCoprime_of_le_right hβc' hb)
      apply hqtop
      rw [Ideal.isCoprime_iff_sup_eq] at hc
      rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h2mem)] at hc
  have hdb : α - β ∈ 𝔟 := by
    refine mem_of_mul_mem_of_isCoprime_span hβc' ?_
    have : β' * (α - β) = β * (α' - β') := by linear_combination key
    rw [this]
    exact 𝔟.mul_mem_left _ hd'
  have hda : α' - β' ∈ 𝔞 := by
    refine mem_of_mul_mem_of_isCoprime_span hβc ?_
    have : β * (α' - β') = β' * (α - β) := by linear_combination -key
    rw [this]
    exact 𝔞.mul_mem_left _ hd
  obtain ⟨i, hi, a₀, ha₀, hia⟩ := Ideal.isCoprime_iff_exists.1 hβc
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hi
  obtain ⟨i', hi', b₀, hb₀, hib⟩ := Ideal.isCoprime_iff_exists.1 hβc'
  obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hi'
  set δ : 𝓞 K := β * r + a₀ * (β' * r') with hδdef
  set γ : 𝓞 K := α * r + a₀ * (α' * r') with hγdef
  have hδ1 : δ - 1 ∈ 𝔞 ⊓ 𝔟 := by
    have : δ - 1 = -(a₀ * b₀) := by linear_combination hia + a₀ * hib
    rw [this]
    exact (Ideal.neg_mem_iff _).2 ⟨𝔞.mul_mem_right _ ha₀, 𝔟.mul_mem_left _ hb₀⟩
  have hγδ : γ - δ ∈ 𝔞 ⊓ 𝔟 := by
    have : γ - δ = r * (α - β) + a₀ * r' * (α' - β') := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ⟨hd, hdb⟩) (Ideal.mul_mem_left _ _ ⟨hda, hd'⟩)
  have hγ1 : γ - 1 ∈ 𝔞 ⊓ 𝔟 := by
    have : γ - 1 = (γ - δ) + (δ - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ hγδ hδ1
  have hne : ∀ x : 𝓞 K, x - 1 ∈ 𝔞 ⊓ 𝔟 → x ≠ 0 := by
    rintro x hx rfl
    apply hqtop
    rw [Ideal.eq_top_iff_one]
    have h1 := hx.1
    rw [zero_sub] at h1
    exact ha ((Ideal.neg_mem_iff _).1 h1)
  have hδ0 := hne δ hδ1
  have hγ0 := hne γ hγ1
  have hmul : γ * β = α * δ := by
    simp only [hγdef, hδdef]
    linear_combination (-(a₀ * r')) * key
  refine ⟨γ, δ, ⟨hγ0, hδ0, _root_.GlobalTheory.Mem.RayNo.isCoprime_span hγ1, _root_.GlobalTheory.Mem.RayNo.isCoprime_span hδ1,
    hγδ, fun φ => ?_⟩, ?_⟩
  · have hφ : φ (γ : K) * φ (β : K) = φ (α : K) * φ (δ : K) := by
      have := congrArg (fun z : 𝓞 K => φ (z : K)) hmul
      simpa using this
    have hδφ : φ (δ : K) ≠ 0 := (map_ne_zero φ).2 (by exact_mod_cast hδ0)
    have hβφ : φ (β : K) ≠ 0 := (map_ne_zero φ).2 (by exact_mod_cast hβ0)
    have hδ2 : 0 < φ (δ : K) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hδφ))
    have hβ2 : 0 < φ (β : K) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hβφ))
    have h1 : 0 < (φ (γ : K) * φ (δ : K)) * φ (β : K) ^ 2 := by
      rw [show (φ (γ : K) * φ (δ : K)) * φ (β : K) ^ 2 = (φ (α : K) * φ (β : K)) * φ (δ : K) ^ 2 by
        linear_combination (φ (δ : K) * φ (β : K)) * hφ]
      exact mul_pos (hpos φ) hδ2
    nlinarith
  · have hβI : Ideal.span {β} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hβ0
    apply mul_right_cancel₀ hβI
    rw [mul_assoc, mul_comm (Ideal.span {δ}), ← mul_assoc, e₁, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, hmul]


set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.RayCompositum.fieldRange_sup_eq_top : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁]
    [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) →
    ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} →
    𝔟 ≤ Ideal.span {(q : 𝓞 K)} → _root_.GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → _root_.GlobalTheory.FieldSize.IsRay H₁ 𝔞 →
    _root_.GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  intro K H H₁ H₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu 𝔞 𝔟 _ _ q hq hq2 haq hbq hH hH₁ hH₂ f₁ f₂
  letI : Algebra H₁ H := f₁.toRingHom.toAlgebra
  haveI : IsScalarTower K H₁ H := IsScalarTower.of_algebraMap_eq fun x => (f₁.commutes x).symm
  letI : Algebra H₂ H := f₂.toRingHom.toAlgebra
  haveI : IsScalarTower K H₂ H := IsScalarTower.of_algebraMap_eq fun x => (f₂.commutes x).symm
  have hres : ∀ {E : Type} [Field E] [Algebra K E] [Algebra E H] [IsScalarTower K E H] [Normal K E]
      (f : E →ₐ[K] H), (∀ y, algebraMap E H y = f y) → ∀ σ : Gal(H/K),
      (∀ x ∈ f.fieldRange, σ x = x) → AlgEquiv.restrictNormalHom E σ = 1 := by
    intro E _ _ _ _ _ f hf σ hσ
    ext y
    rw [AlgEquiv.one_apply]
    apply f.injective
    have h := AlgEquiv.restrictNormal_commutes σ E y
    rw [hf, hf] at h
    change f (σ.restrictNormal E y) = f y
    rw [h]
    exact hσ _ ⟨y, rfl⟩
  have hfix : ∀ σ : Gal(H/K), (∀ x ∈ f₁.fieldRange ⊔ f₂.fieldRange, σ x = x) → σ = 1 := by
    intro σ hσ
    have r₁ := hres f₁ (fun _ => rfl) σ fun x hx => hσ x (le_sup_left (a := f₁.fieldRange) hx)
    have r₂ := hres f₂ (fun _ => rfl) σ fun x hx => hσ x (le_sup_right (b := f₂.fieldRange) hx)
    obtain ⟨I, hI0, hIc, hχ⟩ := _root_.GlobalTheory.FieldSize.RayDegree.exists_ideal hH σ
    unfold _root_.GlobalTheory.FieldSize.IsRay at hH hH₁ hH₂
    have hIa : IsCoprime I 𝔞 := by
      rw [Ideal.isCoprime_iff_sup_eq] at hIc ⊢
      exact top_unique (hIc.ge.trans (sup_le_sup_left inf_le_left _))
    have hIb : IsCoprime I 𝔟 := by
      rw [Ideal.isCoprime_iff_sup_eq] at hIc ⊢
      exact top_unique (hIc.ge.trans (sup_le_sup_left inf_le_right _))
    have t₁ : ∀ χ : Gal(H₁/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal H₁ χ I = 1 := by
      intro χ
      rw [← heckeIdeal_comp_restrictNormalHom hH.1 χ hI0 hIc, hχ]
      simp [r₁]
    have t₂ : ∀ χ : Gal(H₂/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal H₂ χ I = 1 := by
      intro χ
      rw [← heckeIdeal_comp_restrictNormalHom hH.1 χ hI0 hIc, hχ]
      simp [r₂]
    obtain ⟨α, β, hp₁, he₁⟩ := (hH₁.2.2 I hI0 hIa).1 t₁
    obtain ⟨α', β', hp₂, he₂⟩ := (hH₂.2.2 I hI0 hIb).1 t₂
    obtain ⟨γ, δ, hp, he⟩ := exists_rayPair_inf_of_rayPair hu hq hq2 haq hbq hp₁ he₁ hp₂ he₂
    have hall := (hH.2.2 I hI0 hIc).2 ⟨γ, δ, hp, he⟩
    apply _root_.GlobalTheory.RayMaximal.eq_of_forall_char
    intro χ
    have h := hall χ
    rw [hχ χ] at h
    rw [map_one]
    exact Units.val_eq_one.1 h
  have hbot : (f₁.fieldRange ⊔ f₂.fieldRange).fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact hfix σ fun x hx => hσ ⟨x, hx⟩
  rw [← IsGalois.fixedField_fixingSubgroup (f₁.fieldRange ⊔ f₂.fieldRange), hbot,
    IntermediateField.fixedField_bot]

end GlobalTheory.RayCompositum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminant
section
noncomputable section

namespace GlobalTheory.JSW

theorem jacobi_trudi_det_pad_zeros {A : Type*} [CommRing A] (h : ℕ → A) (h0 : h 0 = 1) {m n : ℕ} (hmn : m ≤ n)
    (l : Fin m → ℕ) : jtDet n h (padTo hmn l) = jtDet m h l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold jtDet
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun i j : Fin (m + k) =>
    if ((padTo hmn l i : ℤ) - i + j) < 0 then 0 else h (((padTo hmn l i : ℤ) - i + j).toNat)).submatrix
      finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply, padTo]
    have hj := j.2
    simp
    omega
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hM, Matrix.toBlocks₂₂, padTo, h0]
    · intro i j hij
      simp only [hM, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right, padTo]
      have : (j : ℕ) < i := hij
      simp
      omega
  have h11 : M.toBlocks₁₁ = Matrix.of fun i j : Fin m =>
      if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat) := by
    ext i j
    simp [hM, Matrix.toBlocks₁₁, padTo]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h22, h11, mul_one]

theorem schur_padTo_eq_jtDet {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ) :
    schur n (padTo hmn l) = jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  rw [schur_eq_jtDet]
  exact jacobi_trudi_det_pad_zeros _ (MvPolynomial.hsymm_zero _ _) hmn l

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameFrobeniusIsUnitDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem isUnit_map_of_mul_eq_smul {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (g : R →+* D)
    (M M' : Matrix (Fin d) (Fin d) R) (r : R) (h : M * M' = r • (1 : Matrix (Fin d) (Fin d) R)) (hr : IsUnit (g r)) :
    IsUnit (M.map g) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 : M.map g * M'.map g = g r • (1 : Matrix (Fin d) (Fin d) D) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hr.pow d)

theorem wseed_F_frob_XZ_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  intro l _ K bk τ d ρ s Ψ Z hΨ hZ
  have hl := isUnit_l_disc l (X : bk.S) bk.ρ₀
  rw [Matrix.map_mul]
  refine IsUnit.mul ?_ (IsUnit.mul ?_ ?_)
  · refine isUnit_map_of_mul_eq_smul _ s.F s.F' _ s.F_mul ?_
    rw [map_pow, map_natCast]
    exact hl.pow _
  · have e : Ψ.comp (toDisc l (X : bk.S) bk.ρ₀) = (toDisc l (X : bk.S) bk.ρ₀).comp (frobS l bk.a) :=
      RingHom.ext hΨ.ext
    rw [Matrix.map_map, show (⇑Ψ ∘ ⇑(toDisc l (X : bk.S) bk.ρ₀)) = ⇑(Ψ.comp (toDisc l (X : bk.S) bk.ρ₀)) from rfl, e]
    refine isUnit_map_of_mul_eq_smul _ s.X s.X' _ s.X_mul ?_
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
    exact (hl.pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  · exact hZ.map (Ψ.mapMatrix)

end GlobalTheory.BKLim

end
end

