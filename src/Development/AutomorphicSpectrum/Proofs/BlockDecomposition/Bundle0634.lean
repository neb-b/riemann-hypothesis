module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open scoped TensorProduct NumberField.AdeleRing WithZero

noncomputable section
namespace GlobalTheory.CompanionTheory.CMDelta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_delta (h : IsCMExt F E σ) :
    ∃ (δ : E) (d : F), δ ≠ 0 ∧ σ δ = -δ ∧ algebraMap F E d = δ ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have hne := GlobalTheory.LFun.InertChart.conj_ne h
  obtain ⟨e, he⟩ : ∃ e, σ e ≠ e := by
    by_contra hn
    push Not at hn
    exact hne hn
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => he (congrArg (fun t : E ≃ₐ[F] E => t e) hs)
  have hfix : ∀ t : E ≃ₐ[F] E, t ((e - σ e) ^ 2) = (e - σ e) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  exact ⟨e - σ e, d, sub_ne_zero.2 (Ne.symm he), by rw [map_sub, hσ]; ring, hd⟩

theorem val_square (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {δ : E} {d : F} (hd : algebraMap F E d = δ ^ 2)
    (w : HeightOneSpectrum (𝓞 E)) :
    w.valuation E δ ^ 2 = (below F w).valuation F d := by
  have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h1 := valued_completionMap (below F w) w (algebraMap F _ d)
  rw [completionMap_algebraMap, hram, pow_one, IsScalarTower.algebraMap_apply F E (w.adicCompletion E),
    HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion] at h1
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply] at h1
  rw [← h1, hd, map_pow]

theorem valued_alg {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply]

theorem exists_finIdele {d : F} (hd0 : d ≠ 0) :
    ∃ (X : (FiniteAdeleRing (𝓞 F) F)ˣ), ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ),
      v.valuation F d = WithZero.exp (2 * k) → Valued.v ((X : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp k := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.valuation_exists_uniformizer F
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (v.valuation F d) / 2
  have hev : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    have h1 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d).2
    have h2 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
    filter_upwards [h1, h2] with v a b
    have a' : v.valuation F d ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 a
      exact (valued_alg v d).symm.le.trans this
    have b' : v.valuation F d⁻¹ ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 b
      exact (valued_alg v d⁻¹).symm.le.trans this
    have : v.valuation F d = 1 := by
      rw [map_inv₀] at b'
      exact le_antisymm a' ((inv_le_one₀ (zero_lt_iff.2 (by simpa using hd0))).1 b')
    simp [n, this]
  let f : ℤ → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun s v =>
    (algebraMap F (v.adicCompletion F) (π v)) ^ (s * n v)
  have hfmem : ∀ s : ℤ, ∀ᶠ v in Filter.cofinite, f s v ∈ v.adicCompletionIntegers F := fun s => by
    filter_upwards [hev] with v hv
    simp [f, hv, one_mem]
  let X (s : ℤ) : FiniteAdeleRing (𝓞 F) F := ⟨f s, hfmem s⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (π v) ≠ 0 := fun v h => by
    have := valued_alg v (π v)
    rw [h, map_zero, hπ v] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨⟨X (-1), X 1, ?_, ?_⟩, fun v k hk => ?_⟩
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f (-1) v * f 1 v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f 1 v * f (-1) v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · change Valued.v (f (-1) v) = _
    have hn : n v = k := by
      simp only [n]
      rw [hk, WithZero.log_exp]
      omega
    simp only [f, hn]
    rw [map_zpow₀, valued_alg, hπ]
    rw [← WithZero.exp_zsmul]
    simp

theorem exists_infIdele {d : F} (hd0 : d ≠ 0) (hr : NumberField.IsTotallyReal F) :
    ∃ T : (InfiniteAdeleRing F)ˣ, ∀ v : InfinitePlace F,
      (T : InfiniteAdeleRing F) v ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨
      (T : InfiniteAdeleRing F) v ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v := by
  have key : ∀ v : InfinitePlace F, ∃ t : v.Completion, t ≠ 0 ∧
      (t ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨ t ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v) := by
    intro v
    have hv : v.IsReal := NumberField.IsTotallyReal.isReal v
    let f := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have ha : algebraMap F (InfiniteAdeleRing F) d v ≠ 0 :=
      (map_ne_zero (algebraMap F v.Completion)).2 hd0
    set a := algebraMap F (InfiniteAdeleRing F) d v with hadef
    have hfa : f a ≠ 0 := (map_ne_zero f).2 ha
    refine ⟨f.symm (Real.sqrt |f a|), ?_, ?_⟩
    · exact (map_ne_zero f.symm).2 (Real.sqrt_ne_zero'.2 (abs_pos.2 hfa))
    · rw [← map_pow, Real.sq_sqrt (abs_nonneg _)]
      rcases abs_choice (f a) with h | h
      · left; rw [h]; simp
      · right; rw [h, map_neg]; simp
  choose t ht0 ht using key
  refine ⟨⟨t, fun v => (t v)⁻¹, ?_, ?_⟩, ht⟩
  · funext v; exact mul_inv_cancel₀ (ht0 v)
  · funext v; exact inv_mul_cancel₀ (ht0 v)

theorem bDel : PositivityTheory.RgEis.So.BDel := by
  intro F E _ _ _ _ _ σ χ c hcm hU _ _
  obtain ⟨δ, d, hδ0, hσ, hd⟩ := exists_delta hcm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hδ0 (pow_eq_zero_iff (two_ne_zero) |>.1 hd.symm)
  obtain ⟨X, hX⟩ := exists_finIdele hd0
  obtain ⟨T, hT⟩ := exists_infIdele hd0 hcm.1
  let α : IdeleGroup F := MulEquiv.prodUnits.symm (T, X)
  let δu : Eˣ := Units.mk0 δ hδ0
  let A := PositivityTheory.RgEis.adCM σ χ
  let ν := PositivityTheory.RgEis.So.nuCM F E
  let u := Units.map A.i.toMonoidHom δu * (Units.map ν.toMonoidHom α)⁻¹
  have hνe : ∀ z, PositivityTheory.RgEis.eqv F E (ν z) = adeleMap F E z := fun z => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (z ⊗ₜ 1) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, one_mul]
  have hie : ∀ e, PositivityTheory.RgEis.eqv F E (A.i e) = algebraMap E 𝔸[E] e := fun e => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (1 ⊗ₜ e) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, mul_one]
  have hdec : A.i δ = ν α * u := by
    change A.i δ = ν α * (A.i δ * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1)
    have : ν α * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1 = 1 := Units.mul_inv (Units.map ν.toMonoidHom α)
    rw [mul_left_comm, this, mul_one]
  set y := PositivityTheory.RgEis.eqv F E u with hy
  set y' := PositivityTheory.RgEis.eqv F E ((u⁻¹ : (_)ˣ) : _) with hy'
  have h1 : adeleMap F E α * y = algebraMap E 𝔸[E] δ := by
    rw [← hνe, hy, ← map_mul, ← hdec, hie]
  have h2 : y * y' = 1 := by
    rw [hy, hy', ← map_mul, Units.mul_inv, map_one]
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y.2 w) = 1 := by
    intro w
    have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hw0 : w.valuation E δ ≠ 0 := by simpa using hδ0
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w.valuation E δ = WithZero.exp k :=
      ⟨WithZero.log (w.valuation E δ), (WithZero.exp_log hw0).symm⟩
    have hsq := val_square hU hd w
    have hval : (below F w).valuation F d = WithZero.exp (2 * k) := by
      rw [← hsq, hk, ← WithZero.exp_nsmul]
      simp
    have hX' := hX (below F w) k hval
    have hA : Valued.v ((adeleMap F E α).2 w) = WithZero.exp k := by
      change Valued.v (completionMap (below F w) w ((X : FiniteAdeleRing (𝓞 F) F) (below F w))) = _
      rw [valued_completionMap, hram, pow_one, hX']
    have hc : (adeleMap F E α).2 w * y.2 w = algebraMap E (w.adicCompletion E) δ :=
      congrArg (fun z : 𝔸[E] => z.2 w) h1
    have hv := congrArg Valued.v hc
    rw [map_mul, hA, show Valued.v (algebraMap E (w.adicCompletion E) δ) = w.valuation E δ from valued_alg w δ, hk] at hv
    exact mul_left_cancel₀ (WithZero.exp_ne_zero (a := k)) (hv.trans (mul_one _).symm)
  have hfin' : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y'.2 w) = 1 := by
    intro w
    have hc : y.2 w * y'.2 w = 1 := congrArg (fun z : 𝔸[E] => z.2 w) h2
    have hv := congrArg Valued.v hc
    rwa [map_mul, hfin w, one_mul, map_one] at hv
  have hinf : ∀ w : InfinitePlace E, ‖y.1 w‖ = 1 := by
    intro w
    set D : w.Completion := algebraMap E (InfiniteAdeleRing E) δ w with hD
    have hD0 : D ≠ 0 := (map_ne_zero (algebraMap E w.Completion)).2 hδ0
    set v := w.comap (algebraMap F E) with hv
    set Aw : w.Completion := (adeleMap F E α).1 w with hAw
    have hAsq : Aw ^ 2 = D ^ 2 ∨ Aw ^ 2 = -D ^ 2 := by
      obtain ⟨g, hg⟩ : ∃ g : v.Completion →+* w.Completion, ∀ x : InfiniteAdeleRing F,
          GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) x w = g (x v) :=
        ⟨_, fun x => GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w⟩
      have hAw' : Aw = g ((T : InfiniteAdeleRing F) v) := hg _
      have hm : g (algebraMap F (InfiniteAdeleRing F) d v) = D ^ 2 := by
        have := congrFun (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := E) d) w
        rw [hg, hd, map_pow] at this
        exact this
      rcases hT v with h | h
      · left; rw [hAw', ← map_pow, h, hm]
      · right; rw [hAw', ← map_pow, h, map_neg, hm]
    have hnorm : ‖Aw‖ = ‖D‖ := by
      have : ‖Aw‖ ^ 2 = ‖D‖ ^ 2 := by
        rcases hAsq with h | h
        · rw [← norm_pow, h, norm_pow]
        · rw [← norm_pow, h, norm_neg, norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    have hc : Aw * y.1 w = D := congrArg (fun z : 𝔸[E] => z.1 w) h1
    have hn := congrArg norm hc
    rw [norm_mul, hnorm] at hn
    exact mul_left_cancel₀ (norm_ne_zero_iff.2 hD0) (hn.trans (mul_one _).symm)
  have hint : ∀ z : 𝔸[E], (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z.2 w) = 1) → z ∈ PositivityTheory.RgEis.intAd E := by
    intro z hz
    refine (Subring.mem_iInf).2 fun w => ?_
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (hz w).le
  have hφ : ∀ w : InfinitePlace E, ‖(InfinitePlace.Completion.extensionEmbedding w) (y.1 w)‖ = 1 := fun w => by
    rw [← hinf w]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
  refine ⟨δu, α, u, hσ, hdec, hint y hfin, hint y' hfin', fun w => hφ w⟩

end GlobalTheory.CompanionTheory.CMDelta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentity
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem integrable_starLoc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ μ hμ ν hν Q hQ
  obtain ⟨hLC, hSC, hT2, -, -, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTR, -, hSC2, -, -, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)
  haveI := hTR
  haveI := hSC2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  haveI : SecondCountableTopology (HermR (Af F) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (HermR (Af F) σ n) := inferInstance
  obtain ⟨U, hUo, hUc, hUp⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic F E σ hCM M J n ψ hψ μ hμ Q hQ
  obtain ⟨C, t, ht, hb⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.finite_bound F E σ hCM M J hJ n ψ hψ μ hμ Q hQ
  obtain ⟨τ, hτ, hc⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open F E σ hCM n U hUo t ht
  have hs : (n : ℝ) < (M : ℝ) / 2 := by
    have : ((2 * n : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hsum := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow F E σ n (U.comap (hermIn (Af F) σ n)) t ht τ hτ hc
    (fun c => ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖) (fun _ => norm_nonneg _)
    (fun c l hl => by
      show ‖_‖ = ‖_‖
      rw [map_add (f := _), hUp _ _ hl]) C ((M : ℝ) / 2) hb (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow F E σ hCM n _ hs)
  exact _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic _ _ ν U hUo hUc (hermIn (Af F) σ n) (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite F E σ hCM n U hUo) _ (fun g u hu => hUp g u hu) hsum

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtEx

theorem continuous_of_decomp {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace X]
    {Q : Subgroup Γ} (hQ : IsClosed (Q : Set Γ)) {C : Set Γ} (hC : IsCompact C) (H : Γ → X) (δ : Q → X)
    (hδ : Continuous δ) (hI : ∀ g, ∃ p ∈ Q, ∃ k ∈ C, g = p * k)
    (hH : ∀ (p : Q), ∀ k ∈ C, H ((p : Γ) * k) = δ p) : Continuous H := by
  rw [continuous_iff_isClosed]
  intro F hF
  have hQF : IsClosed ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) :=
    hQ.isClosedMap_subtype_val _ (hF.preimage hδ)
  have heq : H ⁻¹' F = Set.image2 (· * ·) ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) C := by
    ext g
    constructor
    · intro hg
      obtain ⟨p, hp, k, hk, rfl⟩ := hI g
      refine Set.mem_image2.mpr ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      have h1 := hH ⟨p, hp⟩ k hk
      simp only [Set.mem_preimage] at hg ⊢
      rw [← h1]
      exact hg
    · intro hg
      obtain ⟨x, ⟨q, hq, rfl⟩, k, hk, rfl⟩ := Set.mem_image2.mp hg
      simp only [Set.mem_preimage] at hq ⊢
      rw [hH q k hk]
      exact hq
  rw [heq]
  exact hQF.mul_right_of_isCompact hC

variable {D : D7} {n : ℕ}

def delta : P D n →* ℝ≥0 :=
  (absA D).comp (Matrix.GeneralLinearGroup.det.comp HeightExists.leviBlock)

theorem continuous_delta : Continuous (delta (D := D) (n := n)) := by
  have hA : Continuous (absA D) := GlobalTheory.Doubling.continuous_absE
  exact hA.comp (HeightExists.continuous_detGL.comp HeightExists.continuous_leviBlock)

theorem absA_pos (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem delta_eq {p : G D n} (hp : p ∈ P D n) {a : GL (Fin n) (AE D)} (ha : blkA (mat p) = a.1) :
    delta (⟨p, hp⟩ : P D n) = absA D (Matrix.GeneralLinearGroup.det a) := by
  have hl : HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n) = a := by
    ext1
    exact ha
  show absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n))) = _
  rw [hl]

theorem height_eq {H : G D n → ℝ≥0} (hH : IsHeight H) (p : P D n) {k : G D n} (hk : k ∈ K D n) :
    H ((p : G D n) * k) = delta p := by
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA p.2
  rw [hH p p.2 a ha k hk, ← delta_eq p.2 ha]

theorem isHt_of_isHeight {H : G D n → ℝ≥0} (hH : IsHeight H) : PositivityTheory.Rg.Rsw.IsHt H := by
  refine ⟨continuous_of_decomp HeightExists.isClosed_P HeightExists.isCompact_K H delta continuous_delta
    (Iwasawa.exists_mul D n) (fun p k hk => height_eq hH p hk), ?_, ?_⟩
  · intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [height_eq hH ⟨p, hp⟩ hk]
    obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
    rw [delta_eq hp ha]
    exact absA_pos _
  · intro q hq a ha g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [← mul_assoc, height_eq hH ⟨q * p, (P D n).mul_mem hq hp⟩ hk, height_eq hH ⟨p, hp⟩ hk,
      ← delta_eq hq ha]
    exact map_mul delta (⟨q, hq⟩ : P D n) ⟨p, hp⟩

theorem htExist : PositivityTheory.Rg.Rsw.HtExist := by
  intro D n
  refine ⟨?_, (K D n : Set (G D n)), HeightExists.isCompact_K, fun g => ?_⟩
  · obtain ⟨H, hH⟩ := exists_height D n
    exact ⟨H, isHt_of_isHeight hH⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    exact ⟨p, hp, k, hk, rfl⟩

end GlobalTheory.CompanionTheory.HtEx

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnit
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CoefWeight

theorem continuous_norm_coefChar : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  intro D n ψ hψ β
  refine ⟨?_, fun b => hψ.2.1 _⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold GlobalTheory.StdUnn.halfTr
  exact hψ.1.comp ((continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)

end GlobalTheory.CompanionTheory.CoefWeight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

def lowC (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inl j))

def lowD (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

def InCell (e : AE D) (g : G D p) : Prop := ∃ y : Mx D p p, mm y (lowC g) = e • (1 : Mx D p p)

def IsB (e : AE D) (g : G D p) (x : hermS D p e) : Prop := InCell e g ∧ mm (lowC g) x.1.1 = e • lowD g


end GlobalTheory.CompanionTheory.MuC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_cuspidal_permutation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr x hx)), ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  first | exact @GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | exact GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | (intros; apply GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_jacquet_segment : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL (k := k)) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | exact GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | (intros; apply GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec <;> assumption)
end

