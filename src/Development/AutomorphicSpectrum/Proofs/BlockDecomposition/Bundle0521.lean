module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCompactCoverByUnitScalings
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.SphereCover

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K]

theorem exists_sphere {T : Type} [AddCommGroup T] [Module K T] [Module.Finite K T]
    [TopologicalSpace T] [IsModuleTopology K T] (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) (A : Set T) (hA : IsCompact A) :
    ∃ (P : Set T) (k : ℕ), IsCompact P ∧ IsOpen P ∧ (0 : T) ∉ P ∧
      ∀ X ∈ A, X ≠ 0 → ∃ (i : ℕ), ∃ Y ∈ P, X = (π ^ ((i : ℤ) - k)) • Y := by
  haveI : ContinuousAdd T := IsModuleTopology.toContinuousAdd K T
  haveI : ContinuousSMul K T := IsModuleTopology.toContinuousSMul K T
  let c : T ≃ₗ[K] (Fin (Module.finrank K T) → K) := (Module.finBasis K T).equivFun
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  obtain ⟨C, hC⟩ : ∃ C, ∀ X ∈ A, ‖c X‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hA.image hc).isBounded.exists_norm_le
    exact ⟨C, fun X hX => hC _ ⟨X, hX, rfl⟩⟩
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < (‖π‖⁻¹) ^ k :=
    pow_unbounded_of_one_lt C ((one_lt_inv₀ hπ).2 h1)
  have himg : c.symm '' Metric.sphere 0 1 = c ⁻¹' Metric.sphere 0 1 := by
    ext X
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hX
      exact ⟨c X, hX, by simp⟩
  refine ⟨c.symm '' Metric.sphere 0 1, k, (isCompact_sphere _ _).image hc', ?_, ?_, ?_⟩
  · rw [himg]
    exact (IsUltrametricDist.isClopen_sphere 0 one_ne_zero).isOpen.preimage hc
  · rw [himg]
    simp
  · intro X hX hX0
    have hw : c X ≠ 0 := by simpa using hX0
    obtain ⟨l, hl⟩ : ∃ l, c X l ≠ 0 := Function.ne_iff.1 hw
    haveI : Nonempty (Fin (Module.finrank K T)) := ⟨l⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup (Finset.univ) Finset.univ_nonempty
      (fun i => ‖c X i‖₊)
    have hnorm : ‖c X‖ = ‖c X m‖ := by
      rw [← coe_nnnorm, Pi.nnnorm_def, hm, coe_nnnorm]
    have hm0 : c X m ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact hw (norm_eq_zero.1 hnorm)
    obtain ⟨j, hj⟩ := hv _ hm0
    rw [← hnorm] at hj
    have hjk : -(k : ℤ) ≤ j := by
      have : ‖π‖ ^ j ≤ ‖π‖ ^ (-(k : ℤ)) := by
        rw [← hj, zpow_neg, zpow_natCast, ← inv_pow]
        exact ((hC X hX).trans hk.le)
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hπ h1).1 this
    have hY : ‖c ((π ^ (-j)) • X)‖ = 1 := by
      rw [map_smul, norm_smul, norm_zpow, hj, ← zpow_add₀ hπ.ne']
      simp
    refine ⟨(j + k).toNat, (π ^ (-j)) • X, ?_, ?_⟩
    · rw [himg]
      simpa using hY
    · have : (((j + k).toNat : ℕ) : ℤ) - k = j := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [this, smul_smul, ← zpow_add₀ h0]
      simp

end Abstract

section Cover

variable {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
  [Algebra K R] [Module.Finite K R] [TopologicalSpace R] [IsModuleTopology K R]

theorem linearIndependent_of_ne_zero (hR : IsField R) {M : ℕ} {X : Fin 1 → Fin M → R}
    (hX : X ≠ 0) : LinearIndependent R X := by
  haveI : IsDomain R := hR.isDomain
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : X 0 ≠ 0 := fun h => hX (funext fun p => by
    obtain rfl : p = 0 := Subsingleton.elim _ _
    exact h)
  obtain ⟨l, hl⟩ : ∃ l, X 0 l ≠ 0 := Function.ne_iff.1 h0
  have h1 := congrFun hg l
  simp only [Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right hl

theorem exists_cover (hR : IsField R) (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) {M : ℕ} (hM : 2 ≤ M)
    (A : Set (Fin 1 → Fin M → R)) (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → R)) (u : ι → Rˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → R | LinearIndependent R X} ∧
      Summable (fun i => ‖Algebra.norm K (u i : R)‖₊ ^ (M - 1)) ∧
      A ∩ {X : Fin 1 → Fin M → R | LinearIndependent R X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → R) (p : Fin 1) (k : Fin M) => (u i : R) * X p k) '' P := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨P, k, hPc, hPo, hP0, hcov⟩ := exists_sphere π h0 h1 hv A hA
  let w : Kˣ := Units.mk0 π h0
  let u : ℕ → Rˣ := fun i => Units.map (algebraMap K R).toMonoidHom (w ^ ((i : ℤ) - k))
  have hu : ∀ i : ℕ, (u i : R) = algebraMap K R (π ^ ((i : ℤ) - k)) := fun i => by
    change algebraMap K R ((w ^ ((i : ℤ) - k) : Kˣ) : K) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨ℕ, inferInstance, P, u, hPc, hPo, ?_, ?_, ?_⟩
  · intro X hX
    exact linearIndependent_of_ne_zero hR fun h => hP0 (h ▸ hX)
  · have hd : 0 < Module.finrank K R := Module.finrank_pos
    have hπ : 0 < ‖π‖₊ := nnnorm_pos.2 h0
    have hlt : ‖π‖₊ < 1 := by exact_mod_cast h1
    set e : ℕ := Module.finrank K R * (M - 1) with he
    have he0 : e ≠ 0 := Nat.mul_ne_zero hd.ne' (by omega)
    have hq : ‖π‖₊ ^ e < 1 := pow_lt_one₀ hπ.le hlt he0
    have hs := (NNReal.summable_geometric hq).mul_left ((‖π‖₊ ^ (-(k : ℤ))) ^ e)
    refine hs.congr fun i => ?_
    rw [hu, Algebra.norm_algebraMap, nnnorm_pow, nnnorm_zpow, sub_eq_add_neg,
      zpow_add₀ hπ.ne', zpow_natCast, he]
    ring
  · rintro X ⟨hXA, hXf⟩
    have hX0 : X ≠ 0 := by
      intro h
      have h2 : LinearIndependent R X := hXf
      exact h2.ne_zero 0 (by rw [h]; rfl)
    obtain ⟨i, Y, hY, hXY⟩ := hcov X hXA hX0
    refine Set.mem_iUnion.2 ⟨i, Y, hY, ?_⟩
    rw [hXY]
    funext p l
    simp [hu, Algebra.smul_def]

end Cover

theorem exists_uniformizer {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ a : Fv F v, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    decide
  refine ⟨ϖ, hϖ0, Valued.toNormedField.norm_lt_one_iff.2 h1, fun a ha => ?_⟩
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hn : ‖a * ϖ ^ k‖ = 1 := le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hu.le)
    (not_lt.1 fun h => (Valued.toNormedField.norm_lt_one_iff.1 h).ne hu)
  have hϖn : ‖ϖ‖ ≠ 0 := norm_ne_zero_iff.2 hϖ0
  refine ⟨-k, ?_⟩
  rw [norm_mul, norm_zpow] at hn
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hn

theorem coverF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ h M hM v hF A hA
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : ProperSpace (Fv F v) := GlobalTheory.CompanionTheory.DictLoc.properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨π, h0, h1, hv⟩ := exists_uniformizer v
  exact exists_cover hF π h0 h1 hv hM A hA

end GlobalTheory.CompanionTheory.WeilSiegel.SphereCover
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTPer

theorem map_subst_comm {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) {F G : PowerSeries A}
    {F' : PowerSeries B} (hF' : PowerSeries.map h F = F')
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0)
    (hs : PowerSeries.subst G F = PowerSeries.subst F G) :
    PowerSeries.subst (PowerSeries.map h G) F' = PowerSeries.subst F' (PowerSeries.map h G) := by
  subst hF'
  have h2 := congrArg (MvPowerSeries.map h) hs
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)] at h2
  exact h2


open GlobalTheory.CompanionTheory.LTHodge.CharEx GroundTheory.LocalField GroundTheory.LocalField.FormalGroup ValuativeRel in
theorem exists_series_comm : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  intro l _ K π hπ a
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let e : ↥(OL K) ≃+* 𝒪[↥K.1] := intEquiv K
  let es : 𝒪[↥K.1] →+* ↥(OL K) := (e.symm : 𝒪[↥K.1] →+* ↥(OL K))
  have hp : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hf := isLubinTateSeries_ltPoly (e π)
  have hm := map_ltSeries K hp
  have hes : (intEquiv K).symm (e π) = π := e.symm_apply_apply π
  rw [hes] at hm
  have hF : PowerSeries.map es (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = ltSeries π := by
    rw [← hm]
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  have hF0 : PowerSeries.constantCoeff (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = 0 :=
    hf.constantCoeff_eq_zero
  let h := lubinTateHom hp hf hf (e a)
  have h0 : PowerSeries.constantCoeff h.toPowerSeries = 0 := h.constantCoeff_eq_zero
  have h1 : PowerSeries.coeff 1 h.toPowerSeries = e a := coeff_one_lubinTateHom hp hf hf (e a)
  have hs := subst_lubinTateHom hp hf hf (e a)
  refine ⟨PowerSeries.map es h.toPowerSeries, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
    exact e.symm_apply_apply a
  · exact map_subst_comm es hF hF0 h0 hs

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
section
noncomputable section

open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def LocConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  (∀ x ∈ twCent θ d, ∀ y ∈ twCent θ d, x * y = y * x) ∧
  (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0) ∧
  {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
    ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite ∧
  (∀ y : G, twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent θ d) ∧
    (twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ d)) ≠ 0)

def UnitConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  f = (K : Set G).indicator 1 ∧ d ∈ K ∧ cptPart (twCent θ d) ≤ K ∧
    ∀ y, y⁻¹ * d * θ y ∈ K → ∃ t ∈ twCent θ d, ∃ k ∈ K, y = t * k

end Generic

section Split

variable {H : Type} [Group H]

def swTw (σ : H →* H) : H × H →* H × H :=
  (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom

theorem mem_twCent_swTw (σ : H →* H) (hσ : ∀ g, σ (σ g) = g) (d d' : H) (g : H × H) :
    g ∈ twCent (swTw σ) (d, d') ↔
      g.1 ∈ twCent (MonoidHom.id H) (d * σ d') ∧ g.2 = d' * σ g.1 * d'⁻¹ := by
  obtain ⟨g₁, g₂⟩ := g
  show (g₁, g₂) * (d, d') = (d, d') * (σ g₂, σ g₁) ↔ g₁ * (d * σ d') = d * σ d' * g₁ ∧ g₂ = d' * σ g₁ * d'⁻¹
  simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have e : g₂ = d' * σ g₁ * d'⁻¹ := by rw [← h₂]; group
    refine ⟨?_, e⟩
    rw [← mul_assoc, h₁, e]
    simp only [map_mul, map_inv, hσ]
    group
  · rintro ⟨h₁, rfl⟩
    refine ⟨?_, by group⟩
    simp only [map_mul, map_inv, hσ]
    have : g₁ * d = d * σ d' * g₁ * (σ d')⁻¹ := by
      rw [← h₁]; group
    rw [this]; group

end Split

section Place

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E]

def sgP (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thetaGL a (RingHom.id _)).prodMap (thetaGL b (RingHom.id _))

def ratW (n : ℕ) (w : Pl E) : GL (Fin n) E →* GLw n w := GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))

end Place

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Nondeg

theorem box_subset_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    (box m s : Set (Fin m → k)) ⊆ box m t := fun x hx j =>
  le_trans (show valuation k (x j) ≤ valuation k (s : k) from hx j) h

theorem exists_unit_bound {k : Type} [Field k] [ValuativeRel k] {W : Type} {S : Set W} (hS : S.Finite)
    (τ : W → kˣ) (t : kˣ) :
    ∃ u : kˣ, valuation k (t : k) ≤ valuation k (u : k) ∧
      ∀ w ∈ S, valuation k (τ w : k) ≤ valuation k (u : k) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨t, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨u, h1, h2⟩ := ih
    rcases le_total (valuation k (u : k)) (valuation k (τ a : k)) with h | h
    · refine ⟨τ a, h1.trans h, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact le_rfl
      · exact (h2 w hw).trans h
    · refine ⟨u, h1, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact h
      · exact h2 w hw

theorem exists_large_unit {k : Type} [Field k] [ValuativeRel k] (c r t₀ : kˣ) :
    ∃ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) ∧
      valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
  · refine ⟨c * r⁻¹, h, ?_⟩
    have e : c * (c * r⁻¹)⁻¹ = r := by simp
    rw [e]
  · refine ⟨t₀, le_rfl, ?_⟩
    have e : ((c * t₀⁻¹ : kˣ) : k) = ((c * r⁻¹ : kˣ) : k) * ((t₀⁻¹ : kˣ) : k) * (r : k) := by
      push_cast
      field_simp
    have e1 : valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul]
      simp
    rw [e, map_mul, map_mul]
    calc valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k)
        ≤ valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k) := by gcongr
      _ = valuation k (r : k) := by rw [e1, one_mul]

theorem continuous_wt_mul_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) {n : ℕ} {V V' : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T) (v : V) (v' : V') :
    Continuous fun x => wt ψ n x * coef T B v v' x := by
  refine Continuous.mul ?_ (continuous_coef T B hT v v')
  have h : Continuous fun x : Fin (n + 1) → k => ψ (-x (Fin.last n)) :=
    hψ.comp (continuous_apply _).neg
  exact continuous_subtype_val.comp h

end GlobalTheory.CompanionTheory.MirPair.Nondeg

namespace GlobalTheory.CompanionTheory.MirPair


open GlobalTheory.CompanionTheory.MirPair.Nondeg in
theorem exists_evVal_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hinv hnd v hv
  obtain ⟨r₁, hr₁, hfix⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₂, hr₂, hlat⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.ShearLat.main (k := k) (n := n) 1
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r : kˣ, valuation k (r : k) < 1 ∧
      valuation k (r : k) ≤ valuation k (r₁ : k) ∧ valuation k (r : k) ≤ valuation k (r₂ : k) := by
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h | h
    · exact ⟨r₁, hr₁, le_rfl, h⟩
    · exact ⟨r₂, hr₂, h, le_rfl⟩
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero ν ψ T B hψ hT hnd v hv
  obtain ⟨t, htt₀, htc⟩ := exists_large_unit c r t₀
  obtain ⟨v', hv'⟩ := ht₀ t htt₀
  by_contra hno
  push_neg at hno
  have hev : ∀ w : V', ∃ τ : kˣ, ∀ u : kˣ, valuation k (τ : k) ≤ valuation k (u : k) →
      JJ ν ψ T B (box (n + 1) u : Set (Fin (n + 1) → k)) v w = 0 := by
    intro w
    obtain ⟨A, hA⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.exists_evVal ν ψ c T T' B s hψ hc hT hT' hinv v w
    have h0 : A = 0 := hno w A hA
    obtain ⟨τ, hτ⟩ := hA
    exact ⟨τ, fun u hu => (hτ u hu).trans h0⟩
  choose τ hτ using hev
  obtain ⟨u, htu, hu⟩ := exists_unit_bound (GlobalTheory.T.shear_orbit_box_finite_of_isSmooth T' hT' v' r hr) τ t
  have hz : ∀ b ∈ box (n + 1) (c * t⁻¹), ∫ x in (box (n + 1) u : Set (Fin (n + 1) → k)),
      ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = 0 := by
    intro b hb
    have hbr : b ∈ (box (n + 1) r : Set (Fin (n + 1) → k)) := box_subset_of_valuation_le htc hb
    have hlast : valuation k (b (Fin.last n)) < 1 :=
      lt_of_le_of_lt (show valuation k (b (Fin.last n)) ≤ valuation k (r : k) from hbr _) hr
    rw [_root_.GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear ν ψ T T' B s hψ hT hinv b _ v v' hlast
      (hfix b (box_subset_of_valuation_le hrr₁ hbr)) ?_]
    · exact hτ _ u (hu _ ⟨b, hbr, rfl⟩)
    · intro x
      have h := hlat b (box_subset_of_valuation_le hrr₂ hbr) u x
      simpa using h
  have hm : MeasurableSet (box (n + 1) u : Set (Fin (n + 1) → k)) := by
    rw [coe_box]
    exact MeasurableSet.univ_pi fun _ => (isOpen_cball u).measurableSet
  have hfin := setIntegral_inter_box_of_twists ν ψ c hψ hc (n + 1) t
    (box (n + 1) u : Set (Fin (n + 1) → k)) (fun x => wt ψ n x * coef T B v v' x) 0
    (isCompact_box _ _) hm (continuous_wt_mul_coef ψ hψ T B hT v v') hz
  rw [Set.inter_eq_right.2 (box_subset_of_valuation_le htu)] at hfin
  exact hv' hfin

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt

theorem integrable_isSchwartzBruhat_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.continuous_integrable σ hCM dx hdx hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt
end
end

