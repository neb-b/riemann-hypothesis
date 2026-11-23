module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealPosAtOneOfRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmLocalCharacterValueBounded
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugationSymmetry
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.InputsHecke
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeRatio

section Standard

open HeckeCharacterZeroLocus.ThmBIn GlobalTheory.LFun GlobalTheory.HeckeOne GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange
open Formalism.L2.Host (HChar)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_conj_prime (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle)
    (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) :
    ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, normP (c P) = normP P) ∧
      (∀ P, (c P).under (𝓞 F) = P.under (𝓞 F)) ∧ ∀ P, chiAt σ χ (c P) = starRingEnd ℂ (chiAt σ χ P) := by
  obtain ⟨c, hcc, hN, hmem, hund, hinv, hint, hidem⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  have hsd := GlobalTheory.ideleChar_conj_eq_inv_of_trivial_on_base F E σ hσ χ hF
  have hun := GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ χ
  have hram : ∀ P, IsUnramAt σ χ P → IsUnramAt σ χ (c P) := by
    rintro P ⟨e, f, he, hz⟩
    refine ⟨cA σ e, f, hidem P e f he, fun z h1 h2 h3 => ?_⟩
    have h4 : χ (Units.map (cA σ).toMonoidHom z) = 1 := by
      apply hz
      · change cA σ (z : AE F E) = e * cA σ (z : AE F E) + (1 - e)
        have := congrArg (cA σ) h1
        rwa [map_add, map_mul, map_sub, map_one, hinv] at this
      · exact (hint _).2 h2
      · exact (hint _).2 h3
    rw [hsd z (Units.map (cA σ).toMonoidHom z) rfl] at h4
    exact inv_eq_one.1 h4
  have hunif : ∀ P x, IsUnifIdele σ P x → IsUnifIdele σ (c P) (Units.map (cA σ).toMonoidHom x) := by
    rintro P x ⟨e, f, ϖ, he, h1, h2, h3⟩
    have hy : ((RingOfIntegers.mapRingHom σ.toRingHom ϖ : 𝓞 E) : E) = σ ϖ := rfl
    refine ⟨cA σ e, f, RingOfIntegers.mapRingHom σ.toRingHom ϖ, hidem P e f he,
      ((hmem P _ _ hy).1).2 h1, fun h => h2 (((hmem P _ _ hy).2).1 h), ?_⟩
    change cA σ (x : AE F E) = _
    rw [h3, map_add (f := _), map_mul, map_sub, map_one, GlobalTheory.cA_incA_apply, hy]
  refine ⟨c, hN, fun P => ((hund P (c P)).2 (Or.inr rfl)).symm, fun P => ?_⟩
  by_cases hP : IsUnramAt σ χ P
  · obtain ⟨x, hx⟩ := (hun P).1
    rw [(hun P).2.1 hP x hx, (hun (c P)).2.1 (hram P hP) _ (hunif P x hx),
      hsd x (Units.map (cA σ).toMonoidHom x) rfl, Circle.coe_inv_eq_conj]
  · have hP' : ¬ IsUnramAt σ χ (c P) := fun h => hP (by simpa [hcc] using hram _ h)
    simp [chiAt, hP, hP']

def toH (χ : UnitaryHeckeChar E) : HChar E := toHChar χ.toHom ⟨χ.continuous_toHom, χ.map_principal⟩

theorem unrAt_toH (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    (toH χ).UnrAt P ↔ χ.IsUnramifiedAt P :=
  forall₂_congr fun _ _ => ⟨fun h => Circle.ext (congrArg Units.val h),
    fun h => (congrArg Circle.toUnits h).trans (map_one _)⟩

theorem val_toH (χ : UnitaryHeckeChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.IsUnramifiedAt P) :
    (((toH χ).val P : ℂˣ) : ℂ) = χ.valueAt P :=
  (χ.valueAt_eq h (Formalism.L2.Host.unif_spec P)).symm

theorem eulerFactor_toH (χ : UnitaryHeckeChar E) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.CMVal.eulerFactor (toH χ) s P = χ.eulerFactor P s := by
  unfold GlobalTheory.CMVal.eulerFactor UnitaryHeckeChar.eulerFactor
  split_ifs with h
  · rw [val_toH χ ((unrAt_toH χ P).1 h)]
  · rw [χ.valueAt_of_ramified fun h' => h ((unrAt_toH χ P).2 h'), zero_mul, sub_zero, inv_one]

theorem eq_zero_of_npow (H : GlobalTheory.Published.HeckeLPartialContinuation) {z : ℂ} (hz : z.re = 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), npow P (-z) = 1) : z = 0 := by
  obtain ⟨Z, hZ, h1, h2⟩ := (H E ∅ Set.finite_empty).2
  have e : ∀ s : ℂ, zetaOff (K := E) ∅ (s + z) = zetaOff (K := E) ∅ s := fun s => by
    simp only [zetaOff, eulerProd, locL, neg_add, LFun.npow_add, h, mul_one]
  have k := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.eq_of_eqOn_re (f := fun s => Z s * (s + z - 1)) (g := fun s => Z (s + z) * (s - 1))
    (hZ.mul (by fun_prop)) ((hZ.comp (by fun_prop)).mul (by fun_prop)) fun s hs => by
      rw [h1 s hs, h1 (s + z) (by simpa [hz] using hs), e]; ring
  have k1 := congrFun k 1
  simp only [sub_self, mul_zero, add_sub_cancel_left] at k1
  exact (mul_eq_zero.1 k1).resolve_left (h2 1 (by simp))

theorem exists_entire_pos (H : GlobalTheory.Published.HeckeLPartialContinuation) (hσ : IsCMExt F E σ)
    (χ : (AE F E)ˣ →* Circle) (hχ : IsHeckeChar F E χ) (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) (hne : χ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 E) → Prop)
    (hp : ∀ P, p P ↔ P.under (𝓞 F) ∉ S) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // p P} => lfac σ χ P.1 s) (Λ s)) ∧
      ∀ n : ℕ, 1 ≤ n → (Λ n).im = 0 ∧ 0 < (Λ n).re := by
  obtain ⟨c, hN, hU, hc⟩ := exists_conj_prime hσ χ hF
  obtain ⟨χ, rfl, -⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isHeckeChar_iff hσ χ).1 hχ
  have hu : (toH χ).IsUnitary := isUnitary_toHChar _ _
  have hnp : ¬ ∃ t : ℝ, IsNormPow (toH χ) t := by
    rintro ⟨t, ht⟩
    rw [isNormPow_iff] at ht
    have hv : ∀ P, chiAt σ (pull F χ) P = npow P (-((t : ℂ) * Complex.I)) := fun P => by
      rw [chiAt_eq hσ, ← val_toH χ ((unrAt_toH χ P).1 (ht ▸ unrAt_normChar t P)), ht, val_normChar]
      rfl
    have h0 : (t : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 := eq_zero_of_npow (E := E) H (by simp) fun P => by
      have e1 : npow (c P) (-((t : ℂ) * Complex.I)) = npow P (-((t : ℂ) * Complex.I)) :=
        congrArg (fun n : ℕ => (n : ℂ) ^ (-((t : ℂ) * Complex.I))) (hN P)
      have e2 := hc P
      rw [hv, hv, e1] at e2
      rw [neg_add, LFun.npow_add]
      nth_rewrite 2 [e2]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_npow]
      simp
    have ht0 : t = 0 := by simpa using congrArg Complex.im h0
    rw [ht0, normChar_zero] at ht
    refine hne ((pull_eq_one_iff hσ χ).2 (UnitaryHeckeChar.ext (MonoidHom.ext fun x => Circle.ext ?_)))
    exact congrArg (fun ψ : HChar E => ((ψ.1 x : ℂˣ) : ℂ)) ht
  obtain rfl : p = fun P => P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} :=
    funext fun P => propext (hp P)
  have hT : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}.Finite := by
    have := Filter.mem_cofinite.1 (tendsto_under F E S.finite_toSet.compl_mem_cofinite)
    exact this.subset fun P hP h => h hP
  obtain ⟨Λ, hΛ, h1, h2⟩ := (H E _ hT).1 _ hu hnp
  have hprod : ∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}} =>
      lfac σ (pull F χ) P.1 s) (Λ s) := fun s hs => by
    have k := (converges_heckeFam {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} hu hs).hasProd
    simp only [locL_heckeFam, eulerFactor_toH, ← lfac_eq hσ] at k
    rw [h1 s hs]
    exact k
  obtain ⟨k1, k2⟩ := eulerProduct_eq_exp_and_pos {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}}
    (fun P => normP P.1) (fun P => chiAt σ (pull F χ) P.1) (fun P => GlobalTheory.LFun.one_lt_absNorm P.1)
    (fun P => (GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ _ P.1).2.2)
    (fun t ht => (UnitaryHeckeChar.summable_absNorm_rpow ht).subtype _)
  have hpos : ∀ s : ℂ, 1 < s.re → s.im = 0 → (Λ s).im = 0 ∧ 0 < (Λ s).re := fun s hs hs0 => by
    rw [(hprod s hs).unique (k1 s hs).2]
    exact k2 (c.subtypeEquiv fun P => by simp only [Set.mem_ofPred_eq, hU]) (fun P => hN P.1) (fun P => hc P.1) s hs hs0
  refine ⟨Λ, hΛ, hprod, fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | hlt
  · simpa using real_pos_at_one_of_right Λ hΛ.continuous.continuousAt (h2 1 (by simp)) hpos
  · exact hpos n (by simpa using hlt) (by simp)

end Standard

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S w ↔ w.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hw
    obtain ⟨x, hx, hy⟩ := h _ hw
    exact hy (algebraMap _ _ x) rfl hx
  · intro h u hu
    have : ¬ u.asIdeal ≤ (w.under (𝓞 D.host.F)).asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (w.under _).isPrime.ne_top hle) ▸ hu)
    obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 this
    refine ⟨x, hx, fun y hy hw => hx' ?_⟩
    obtain rfl : y = algebraMap _ _ x := RingOfIntegers.ext hy
    exact hw

theorem isPrimeIdem_eq : IsPrimeIdem (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem D.sp.cm.sig := rfl

theorem isUnifIdele_eq : Mi.IsUnifIdele (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig := by
  funext P x
  unfold Mi.IsUnifIdele HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele
  rw [isPrimeIdem_eq]
  rfl

theorem isUnramAt_eq : Mi.IsUnramAt (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig := by
  funext χ P
  unfold Mi.IsUnramAt HeckeCharacterZeroLocus.ThmBIn.IsUnramAt
  rw [isPrimeIdem_eq]
  rfl

theorem lfac_eq (χ : (AE D)ˣ →* Circle) : Mi.lfac χ = HeckeCharacterZeroLocus.ThmBIn.lfac D.sp.cm.sig χ := by
  funext P s
  have key : ∀ (A A' : Prop) (U U' : (AE D)ˣ → Prop), A = A' → U = U' →
      (open Classical in if h : A ∧ ∃ x, U x then ((χ h.2.choose : Circle) : ℂ) else 0) =
      (open Classical in if h : A' ∧ ∃ x, U' x then ((χ h.2.choose : Circle) : ℂ) else 0) := by
    rintro _ _ _ _ rfl rfl
    rfl
  have e0 := key (Mi.IsUnramAt χ P) (HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig χ P) (Mi.IsUnifIdele P)
    (HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig P) (by rw [isUnramAt_eq]) (by rw [isUnifIdele_eq])
  have e : Mi.chiAt χ P = HeckeCharacterZeroLocus.ThmBIn.chiAt D.sp.cm.sig χ P := by
    unfold Mi.chiAt HeckeCharacterZeroLocus.ThmBIn.chiAt
    exact e0
  unfold Mi.lfac HeckeCharacterZeroLocus.ThmBIn.lfac
  rw [e]
  rfl

theorem heckeRatioPos_of_partialContinuation (H : GlobalTheory.Published.HeckeLPartialContinuation) (D : D7) : HeckeRatioPos D := by
  rintro μ μ' hμ hμ' hF hF' ⟨τ, e, e', h1, h2, hne⟩ t
  have hχ : IsHeckeChar D (μ * μ'⁻¹) := ⟨hμ.1.mul hμ'.1.inv, fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hμ'.2 x, inv_one, mul_one]⟩
  have hχF : ∀ a, (μ * μ'⁻¹) (idF D a) = 1 := fun a => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hF a, hF' a, inv_one, mul_one]
  have hχ1 : μ * μ'⁻¹ ≠ 1 := fun h => by
    obtain rfl := mul_inv_eq_one.1 h
    exact hne (neg_injective (GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 h2))
  have key := exists_entire_pos H (Formalism.IndefR.ThmB.InputsHecke.isCMExt D) (μ * μ'⁻¹) hχ hχF hχ1
  refine ⟨?_, fun S => ?_⟩
  · obtain ⟨Λ, a1, a2, a3⟩ := key ∅ (fun _ => True) fun P => by simp
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact (Equiv.subtypeUnivEquiv (p := fun _ => True) fun _ => trivial).hasProd_iff.1 (a2 s hs)
  · obtain ⟨Λ, a1, a2, a3⟩ := key S (OffS D S) (offS_iff S)
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact a2 s hs

theorem heckeRatioPos (D : D7) : HeckeRatioPos D :=
  heckeRatioPos_of_partialContinuation GlobalTheory.Published.HeckeLPartialContinuation_holds D

end GlobalTheory.HeckeRatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZero
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology Set Filter
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CosetIntegralZero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

def cosetAvg (H : Subgroup G) (ν : Measure H) (ψ : G → ℝ) (g : G) : ℝ :=
  ∫ u : H, ψ ((u : G)⁻¹ * g) ∂ν

theorem cosetAvg_mul [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (ψ : G → ℝ) (u : H) (g : G) : cosetAvg H ν ψ ((u : G) * g) = cosetAvg H ν ψ g := by
  unfold cosetAvg
  rw [← integral_mul_left_eq_self (fun v : H => ψ ((v : G)⁻¹ * ((u : G) * g))) u]
  congr 1; ext v
  simp [mul_inv_rev, mul_assoc]

theorem continuous_cosetAvg [LocallyCompactSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous (cosetAvg H ν ψ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨t, t_comp, ht⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (((↑) : H → G) ⁻¹' (t • (tsupport ψ)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (t_comp.smul_set hψc.inv)
  have A : ContinuousOn (cosetAvg H ν ψ) t := by
    apply continuousOn_integral_of_compact_support hk
    · exact (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * (x : G), ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

theorem cosetAvg_pos [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {g : G} (hg : ψ g ≠ 0) : 0 < cosetAvg H ν ψ g := by
  have C : Continuous (fun u : H => ψ ((u : G)⁻¹ * g)) := by fun_prop
  apply (integral_pos_iff_support_of_nonneg (fun u => hψ0 _) ?_).2
  · apply C.isOpen_support.measure_pos ν
    exact ⟨1, by simpa using hg⟩
  · apply C.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((show IsCompact (tsupport ψ) from hψc).image (f := fun k => g * k⁻¹) (by fun_prop))) ?_
    intro u hu
    by_contra h
    exact hu ⟨(u : G)⁻¹ * g, subset_tsupport _ h, by simp⟩

theorem integrable_prod_of_bound [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    {P : H × G → ℂ} (hP : Continuous P) {C : ℝ} (hC : ∀ z, ‖P z‖ ≤ C) {S : Set H} {M : Set G}
    (hS : IsCompact S) (hM : IsCompact M) (hPS : ∀ u g, P (u, g) ≠ 0 → u ∈ S ∧ g ∈ M)
    {w : G → ℂ} (hw : LocallyIntegrable w μ) :
    Integrable (fun z : H × G => P z * w z.2) (ν.prod μ) := by
  have hSi : Integrable (S.indicator (fun _ => (1:ℝ))) ν :=
    (integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet
  have hMi : Integrable (fun g => C * ‖M.indicator w g‖) μ :=
    ((hw.integrableOn_isCompact hM).integrable_indicator hM.measurableSet).norm.const_mul C
  refine (hSi.mul_prod hMi).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact hP.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  · obtain ⟨u, g⟩ := z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (u, g))
    by_cases h : P (u, g) = 0
    · simp only [h, zero_mul, norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC0 (norm_nonneg _))
    · obtain ⟨hu, hg⟩ := hPS u g h
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hg, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

theorem integral_cosetAvg_mul_eq [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] [SFinite ν]
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ1 : ∀ g, |ψ g| ≤ 1) {F w : G → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hw : LocallyIntegrable w μ) (hinv : ∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) :
    ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  have hS : IsCompact (((↑) : H → G) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) '' (tsupport F ×ˢ tsupport ψ))) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (((show IsCompact (tsupport F) from hFc).prod (show IsCompact (tsupport ψ) from hψc)).image (by fun_prop))
  have I1 : Integrable (fun z : H × G => ((ψ ((z.1 : G)⁻¹ * z.2) : ℂ) * F z.2) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport F) from hFc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ ((u : G)⁻¹ * g) ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F g ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨(g, (u : G)⁻¹ * g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h2⟩
  have I2 : Integrable (fun z : H × G => ((ψ z.2 : ℂ) * F ((z.1 : G) * z.2)) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport ψ) from hψc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ g ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F ((u : G) * g) ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨((u : G) * g, g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h1⟩
  calc ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ
      = ∫ g, ∫ u : H, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only [cosetAvg, mul_assoc]
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ u : H, ∫ g, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂μ ∂ν :=
        (integral_integral_swap (f := fun (u : H) (g : G) => (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g) I1).symm
    _ = ∫ u : H, ∫ g, (ψ g : ℂ) * F ((u : G) * g) * w g ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        conv_lhs => rw [← integral_mul_left_eq_self _ (u : G)]
        refine integral_congr_ae ?_
        filter_upwards [hinv u u.2] with g hg
        simp only [inv_mul_cancel_left, hg]
    _ = ∫ g, ∫ u : H, (ψ g : ℂ) * F ((u : G) * g) * w g ∂ν ∂μ :=
        integral_integral_swap (f := fun (u : H) (g : G) => (ψ g : ℂ) * F ((u : G) * g) * w g) I2
    _ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1; ext u; ring

theorem integral_mul_eq_zero_of_coset_integral_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure]
    (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f →
    LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) →
    (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  intro G _ _ _ _ _ _ _ _ H hH ν _ μ _ f w hf hfc hw hinv hzero
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨ψ₀, hψ1, -, hψc, hψ01⟩ := exists_continuous_one_zero_of_isCompact
    (show IsCompact (tsupport f) from hfc) isClosed_empty (Set.disjoint_empty _)
  have hJc : Continuous (cosetAvg H ν ψ₀) := continuous_cosetAvg H hH ν ψ₀.continuous hψc
  have hJpos : ∀ g ∈ tsupport f, 0 < cosetAvg H ν ψ₀ g := fun g hg =>
    cosetAvg_pos H hH ν ψ₀.continuous hψc (fun x => (hψ01 x).1) (by rw [hψ1 hg]; simp)
  set F : G → ℂ := fun g => f g / (cosetAvg H ν ψ₀ g : ℂ) with hFdef
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ tsupport f
    · exact hf.continuousAt.div (Complex.continuous_ofReal.comp hJc).continuousAt
        (by exact_mod_cast (hJpos g hg).ne')
    · have : F =ᶠ[𝓝 g] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hg] with x hx
        simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
      exact continuousAt_const.congr this.symm
  have hFc : HasCompactSupport F :=
    hfc.mono fun g hg h => hg (by simp [hFdef, h])
  have hFJ : ∀ g, (cosetAvg H ν ψ₀ g : ℂ) * F g * w g = f g * w g := by
    intro g
    by_cases h : f g = 0
    · simp [hFdef, h]
    · have hJ : (cosetAvg H ν ψ₀ g : ℂ) ≠ 0 := by exact_mod_cast (hJpos g (subset_tsupport _ h)).ne'
      rw [hFdef, mul_div_cancel₀ _ hJ]
  have hFH : ∀ g, ∫ u : H, F ((u : G) * g) ∂ν = 0 := by
    intro g
    simp only [hFdef, cosetAvg_mul H ν ψ₀ _ g]
    rw [integral_div, hzero g, zero_div]
  have key := integral_cosetAvg_mul_eq H hH ν μ ψ₀.continuous hψc
    (fun g => by rw [abs_le]; constructor <;> linarith [(hψ01 g).1, (hψ01 g).2]) hF hFc hw hinv
  simp only [hFJ, hFH, mul_zero, integral_zero] at key
  exact key

end GlobalTheory.CosetIntegralZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalFactorUnitary

variable {D : D7}

theorem actO_gAt_of_wAt_eq_zero (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : wAt p u = 0) : actO S T (gAt S p g) (gAt T p h) u = u := by
  obtain ⟨hsplit, hcomm⟩ := (_root_.GlobalTheory.PlaceComponent.gAt_laws D).2 S T p g h u
  have hz : idem D p • actO S T g h u = 0 := by
    rw [← wAt_eq_smul, hcomm, hu]
    unfold actO
    simp
  have hrest : (1 - idem D p) • u = u := by
    rw [sub_smul, one_smul, ← wAt_eq_smul, hu, sub_zero]
  rw [hsplit, hz, hrest, zero_add]

theorem compAt_mt_gAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : Place D) (g : GA D V) (τ : D.what₂.Tau)
    (hτ : Sum.inr τ ≠ p) : compAt θ τ (Formalism.L2.Theta.mt V (gAt V p g)) = 1 := by
  have h0 : (θ τ) ((infPart D) (idem D p)) = 0 := by
    obtain ⟨-, -, -, hfin, -, -, hinf⟩ := _root_.GlobalTheory.PlaceTensor.idem_spec D
    rcases p with v | τ'
    · rw [(hfin v).1, map_zero]
    · have hne : τ' ≠ τ := fun e => hτ (by subst e; rfl)
      exact (hinf θ hθ τ).2 τ' hne
  unfold compAt
  rw [((_root_.GlobalTheory.PlaceComponent.gAt_laws D).1 V p g).1]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, h0, zero_mul, zero_add, sub_zero, one_mul]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLocal_om_gAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT hW hθ p f hf g h
  unfold IsLocal IsLatVac IsFockVacAt at hf ⊢
  obtain ⟨hth, ⟨hdbl, hhalf⟩, hfock⟩ := hf
  have hoff : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun v => Sum.inl v ≠ p), wAt p u = 0 := fun u hu =>
    (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu p).2.2 (fun _ hv => hv)
  refine ⟨hW.om_pres _ f hth, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have hw2 : wAt p (2 • u) = 0 := by
      rw [wAt_eq_smul, smul_comm, ← wAt_eq_smul, hoff u hu, smul_zero]
    have key := hW.om_heis (gAt S p g) (gAt T p h) (2 • u) f hth
    rw [hdbl u hu, actO_gAt_of_wAt_eq_zero S T p g h (2 • u) hw2] at key
    exact key.symm
  · intro e he u hu hu'
    have key := hW.om_heis (gAt S p g) (gAt T p h) u f hth
    rw [hhalf e he u hu hu', actO_gAt_of_wAt_eq_zero S T p g h u (hoff u hu)] at key
    exact key.symm
  · intro τ hτ z
    have hT1 : compAt θ τ (Formalism.L2.Theta.mt T (gAt T p h)) = 1 := compAt_mt_gAt hθ T p h τ hτ
    have hS1 : compAt θ τ (Formalism.L2.Theta.mt S (gAt S p g)⁻¹) = 1 := by
      rw [← gAt_inv]
      exact compAt_mt_gAt hθ S p g⁻¹ τ hτ
    have e1 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ z hth
    have e2 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ (cplxO (sS τ) (sT τ) z) hth
    rw [hT1, hS1, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have hz := hfock τ hτ z
    unfold annih at hz ⊢
    rw [← e1, ← e2, ← map_smul, ← map_add (f := _), hz, map_zero]

end GlobalTheory.LocalFactorUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadraticStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w → UnrAt μ w → val μ w ^ 2 = 1 := by
  first | exact @GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | exact GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | (intros; apply GlobalTheory.LFun.val_sq_eq_one_of_isInertAt <;> assumption)
end

