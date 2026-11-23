module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportHfun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CharIndep
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

noncomputable section

namespace UpperTheory.ConvolutionTheory.C.CharIndepProof

open GlobalTheory.OpTrace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem isLocallyConstant_of_right {U : Subgroup G} (hUo : IsOpen (U : Set G)) {f : G → ℂ}
    (hf : ∀ k ∈ U, ∀ x, f (x * k) = f x) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (U : Set G), hUo.preimage (continuous_const_mul _), by simp [U.one_mem],
    fun x hx => ?_⟩
  have := hf _ hx g
  simpa using this

private theorem isIntegralOp_smoothOp (m : Measure G) [IsFiniteMeasureOnCompacts m] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsIntegralOp m ρ f (smoothOp ρ m f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := m) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := m) hf hc l v]
    simp only [smul_eq_mul]

private theorem smoothOp_eq_levOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke U f) {v : V} (hv : v ∈ fixed ρ U) :
    smoothOp ρ m f v = (m.real (U : Set G) : ℂ) • GlobalTheory.BCT.levOp ρ U U f LinearMap.id v := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  rw [GlobalTheory.TwTrLevel.levOp_apply ρ U U f LinearMap.id v hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  rw [finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by rw [h0, zero_smul]))]
  refine GlobalTheory.OpTrace.eq_of_forall_dual fun l => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hρ.map_smoothOp hlc hf.1 l v,
    GlobalTheory.HaarSum.integral_eq_sum_cosets m U hUo hUc.measure_ne_top (fun g => f g • l (ρ g v)) ?_ hs.toFinset ?_,
    map_smul, map_sum]
  · simp
  · intro x s hs'
    rw [(hf.2 s hs' x).2, map_mul, Module.End.mul_apply, (mem_fixed.1 hv) s hs']
  · intro q hq
    have : f q.out = 0 := by simpa using hq
    simp [this]

private theorem finRankTrace_smoothOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ)
    [FiniteDimensional ℂ (fixed ρ U)] {f : G → ℂ} (hf : GlobalTheory.BCT.IsHecke U f) :
    finRankTrace (smoothOp ρ m f) = (m.real (U : Set G) : ℂ) * GlobalTheory.BCT.twTr ρ U U f LinearMap.id := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hW : ∀ x, smoothOp ρ m f x ∈ fixed ρ U :=
    hρ.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
  have hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ U U f LinearMap.id v ∈ fixed ρ U := fun v hv =>
    GlobalTheory.TwTrLevel.levOp_mem_fixed ρ (MonoidHom.id G) (fun _ => rfl) LinearMap.id (fun _ => rfl) U U hUo
      (fun _ h => h) f hf v hv
  rw [finRankTrace_eq _ (fixed ρ U) hW, GlobalTheory.BCT.twTr, dite_eq_left hmem, ← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun v => Subtype.ext ?_
  simpa using smoothOp_eq_levOp m hUo hUc hρ hf v.2

end UpperTheory.ConvolutionTheory.C.CharIndepProof

open UpperTheory.ConvolutionTheory.C.CharIndepProof GlobalTheory.OpTrace in
theorem UpperTheory.ConvolutionTheory.C.charIndep :
    UpperTheory.ConvolutionTheory.C.CharIndep := by
  classical
  intro G _ _ _ _ _ _ _ _ m _ _ U hU ι _ σ c hfd hc i₀ hi₀
  obtain ⟨hUc, hUo⟩ := hU
  have hfx : ∀ i, fixed (σ i).ρ U = fixedVectors (σ i).ρ U := fun i =>
    Submodule.ext fun v => GlobalTheory.OpTrace.mem_fixed
  haveI hfd' : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ U) := fun i => by rw [hfx i]; exact hfd i
  let S : Setoid ι := ⟨fun i j => Nonempty ((σ i).ρ.Equiv (σ j).ρ),
    ⟨fun i => ⟨Representation.Equiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩
  let mk : ι → Quotient S := Quotient.mk S
  let r : Quotient S → ι := Quotient.out
  haveI : Fintype (Quotient S) := Fintype.ofFinite _
  have hmkr : ∀ q, mk (r q) = q := fun q => Quotient.out_eq q
  have hr : ∀ i, Nonempty ((σ i).ρ.Equiv (σ (r (mk i))).ρ) := fun i =>
    (Quotient.exact (hmkr (mk i))).elim fun e => ⟨e.symm⟩
  let c' : Quotient S → ℂ := fun q => ∑ i with mk i = q, c i
  have hvol : (m.real (U : Set G) : ℂ) ≠ 0 := by
    have h1 : m (U : Set G) ≠ 0 := (hUo.measure_pos m ⟨1, U.one_mem⟩).ne'
    have h2 : m.real (U : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hUc.measure_ne_top⟩
    exact_mod_cast h2
  have key : ∀ f, GlobalTheory.BCT.IsHecke U f →
      ∑ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥},
        c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id = 0 := by
    intro f hf
    have hlc : IsLocallyConstant f := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
    have hW : ∀ i x, smoothOp (σ i).ρ m f x ∈ fixed (σ i).ρ U := fun i =>
      (σ i).smooth.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
    have hfr : ∀ i, FiniteDimensional ℂ (LinearMap.range (smoothOp (σ i).ρ m f)) := fun i =>
      Submodule.finiteDimensional_of_le (S₂ := fixed (σ i).ρ U) (by rintro _ ⟨x, rfl⟩; exact hW i x)
    let s : ι → ℂ := fun i => finRankTrace (smoothOp (σ i).ρ m f)
    have h0 := hc f s ⟨hlc, hf.1⟩ (fun u hu g => hf.2 u hu g) (fun i =>
      ⟨_, isIntegralOp_smoothOp m (σ i).smooth hlc hf.1, hfr i, rfl⟩)
    have hconst : ∀ i, s i = s (r (mk i)) := fun i => by
      obtain ⟨e⟩ := hr i
      haveI := hfr i
      exact ((finRankTrace_eq_of_equiv e.toLinearEquiv (T := smoothOp (σ i).ρ m f)
        (T' := smoothOp (σ (r (mk i))).ρ m f)
        ((σ i).smooth.map_smoothOp_of_intertwining (σ (r (mk i))).smooth hlc hf.1 e.toLinearEquiv.toLinearMap
          (fun g v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v))).2).symm
    have hzero : ∀ q, ¬ fixed (σ (r q)).ρ U ≠ ⊥ → s (r q) = 0 := fun q hq => by
      have hb : fixed (σ (r q)).ρ U = ⊥ := not_not.1 hq
      have hW' : ∀ x, smoothOp (σ (r q)).ρ m f x ∈ (⊥ : Submodule ℂ (σ (r q)).V) := fun x => hb ▸ hW (r q) x
      show finRankTrace _ = 0
      rw [finRankTrace_eq _ ⊥ hW', Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
    have h1 : ∑ q, c' q * s (r q) = 0 := by
      rw [← h0, ← Finset.sum_fiberwise (s := Finset.univ) (g := mk)]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hconst i, (Finset.mem_filter.1 hi).2]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun q => fixed (σ (r q)).ρ U ≠ ⊥),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun q : {q // ¬ fixed (σ (r q)).ρ U ≠ ⊥} => c' q * s (r q))
        (fun q _ => by rw [hzero q q.2, mul_zero]), add_zero] at h1
    have h2 : ∀ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥}, c' q * s (r q) =
        (m.real (U : Set G) : ℂ) * (c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id) := fun q => by
      show c' q * finRankTrace _ = _
      rw [finRankTrace_smoothOp m hUo hUc (σ (r q)).smooth hf]
      ring
    simp only [h2, ← Finset.mul_sum] at h1
    exact (mul_eq_zero.1 h1).resolve_left hvol
  have hli := GlobalTheory.HeckeTraceIndep.twTr_linearIndependent G U hUo hUc U ⟨hUo, le_rfl, fun _ h => h⟩
    {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥} (fun q => σ (r q)) (fun q => ⟨hfd' _, q.2⟩)
    (fun q q' h => Subtype.ext (by rw [← hmkr q, ← hmkr q']; exact Quotient.sound h))
    (fun q => c' q) key
  have hq : fixed (σ (r (mk i₀))).ρ U ≠ ⊥ := by
    obtain ⟨e⟩ := hr i₀
    rw [← hfx i₀] at hi₀
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hi₀
    refine (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv v, mem_fixed.2 fun k hk => ?_, ?_⟩
    · have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap k v
      rw [mem_fixed.1 hv k hk] at this
      exact this.symm
    · simpa using hv0
  have hfin := hli ⟨mk i₀, hq⟩
  have hset : {i | Nonempty ((σ i).ρ.Equiv (σ i₀).ρ)} =
      ↑(Finset.univ.filter fun i => mk i = mk i₀) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  rw [hset, finsum_mem_coe_finset]
  exact hfin
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

section Abs

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [Module ℂ V]

private theorem mem_orbit_iff (I : Subgroup G) (x g : G) :
    (g : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ I) = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ I) = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

private theorem hk_sum (ρ : Representation ℂ G V) (I : Subgroup G) (x : G)
    (h : (MulAction.orbit I (x : G ⧸ I)).Finite) (v : UpperTheory.V.Hi.fixd ρ I) :
    (UpperTheory.V.AlgebraTools.hk ρ I x v : V) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply ℂ G V ρ I I x h).1 v, UpperTheory.V.Hi.dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem hasTrace_hk (m : Measure G) [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant]
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {I : Subgroup G} (hIo : IsOpen (I : Set G))
    (hIc : IsCompact (I : Set G)) (hm : m I = 1) (x : G) (hx : UpperTheory.V.AlgebraTools.FinOrb I I x)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} 1)
      (LinearMap.trace ℂ _ (UpperTheory.V.AlgebraTools.hk ρ I x)) := by
  classical
  have hx' : (MulAction.orbit I (x : G ⧸ I)).Finite := hx
  set D : Set G := {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} with hD
  let C : G ⧸ I → Set G := fun q => (fun g => q.out⁻¹ * g) ⁻¹' (I : Set G)
  have hC : ∀ q g, g ∈ C q ↔ (g : G ⧸ I) = q := fun q g => by
    show q.out⁻¹ * g ∈ I ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hIo.preimage (continuous_const.mul continuous_id)
  have hCc : ∀ q, IsCompact (C q) := fun q => (Homeomorph.mulLeft q.out⁻¹).isCompact_preimage.2 hIc
  have hCm : ∀ q, m (C q) = 1 := fun q => by rw [← hm]; exact measure_preimage_mul m _ _
  have hU : D = ⋃ q ∈ Set.Finite.toFinset hx', C q := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, hC, exists_prop, exists_eq_right']
    exact (mem_orbit_iff I x g).symm
  have hDc : IsCompact D := by
    rw [hU]
    exact (Set.Finite.toFinset hx').isCompact_biUnion fun q _ => hCc q
  have hDm : MeasurableSet D := by
    rw [hU]
    exact Finset.measurableSet_biUnion _ fun q _ => (hCo q).measurableSet
  have hI : ∀ a ∈ I, ∀ g ∈ D, a * g ∈ D := by
    rintro a ha _ ⟨b, hb, c, hc, rfl⟩
    exact ⟨_, mul_mem ha hb, c, hc, by simp only [mul_assoc]⟩
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp m hρ hDc hDm
  have e : ∀ φ : G → ℂ, (fun g => D.indicator (1 : G → ℂ) g * φ g) = D.indicator φ := fun φ => by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  have hfix : ∀ v, A v ∈ UpperTheory.V.Hi.fixd ρ I := fun v a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, hI a ha g h]
    · have : a * g ∉ D := fun h' => h (by simpa using hI _ (inv_mem ha) _ h')
      simp [h, this]
  have hres : ∀ w : UpperTheory.V.Hi.fixd ρ I, A w = UpperTheory.V.AlgebraTools.hk ρ I x w := fun w => by
    rw [hk_sum ρ I x hx', ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, (hA w l).2, map_sum]
    have hsub : ∀ q ∈ Set.Finite.toFinset hx', C q ⊆ D := fun q hq => by
      rw [hU]
      exact Set.subset_biUnion_of_mem (u := C) hq
    conv_lhs => rw [hU]
    rw [integral_biUnion_finset _ (fun q _ => (hCo q).measurableSet)
      (fun p _ q _ hpq => Set.disjoint_left.2 fun g hp hq => hpq (((hC p g).1 hp).symm.trans ((hC q g).1 hq)))
      (fun q hq => (hA w l).1.mono_set (hsub q hq))]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hconst : ∀ g ∈ C q, l (ρ g w) = l (ρ q.out w) := fun g hg => by
      have h1 : q.out⁻¹ * g ∈ I := hg
      have h2 : g = q.out * (q.out⁻¹ * g) := by group
      rw [h2, map_mul, Module.End.mul_apply, w.2 _ h1]
    rw [setIntegral_congr_fun (hCo q).measurableSet hconst, setIntegral_const, measureReal_def, hCm]
    simp
  have hle : LinearMap.range A ≤ UpperTheory.V.Hi.fixd ρ I := by
    rintro _ ⟨v, rfl⟩
    exact hfix v
  refine ⟨A, fun v l => ?_, Submodule.finiteDimensional_of_le hle, ?_⟩
  · rw [e, integral_indicator hDm, integrable_indicator_iff hDm]
    exact hA v l
  haveI := Submodule.finiteDimensional_of_le hle
  let j := Submodule.inclusion hle
  let s : UpperTheory.V.Hi.fixd ρ I →ₗ[ℂ] LinearMap.range A := A.rangeRestrict ∘ₗ (UpperTheory.V.Hi.fixd ρ I).subtype
  have h1 : UpperTheory.V.AlgebraTools.hk ρ I x = j ∘ₗ s := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact (hres w).symm
  have h2 : A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
      (fun v _ => LinearMap.mem_range_self A v) = s ∘ₗ j := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rfl
  rw [h1, h2]
  exact (LinearMap.trace_comp_comm' s j).symm

end Abs

section Eig

private theorem exists_powerSums {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (hT : IsUnit T) :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ W ∧
      ∀ j : ℕ, LinearMap.trace ℂ W (T ^ j) = (Z.map (· ^ j)).sum := by
  obtain ⟨u, rfl⟩ := hT
  let R : Representation ℂ (Multiplicative ℤ) W := (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨E, -, hE⟩ := GlobalTheory.IwahoriTraceProof.exists_exponents (G := Multiplicative ℤ) _ W R rfl
  have hR : ∀ j : ℕ, R (Multiplicative.ofAdd 1 ^ j) = (u : Module.End ℂ W) ^ j := fun j => by
    rw [map_pow]
    congr 1
  refine ⟨E.map fun χ => ((χ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ), ?_, ?_, fun j => ?_⟩
  · intro h
    obtain ⟨χ, -, h⟩ := Multiset.mem_map.1 h
    exact (χ (Multiplicative.ofAdd 1)).ne_zero h
  · have h1 := hE 1
    rw [map_one, Module.End.one_eq_id, LinearMap.trace_id] at h1
    have h2 : (Module.finrank ℂ W : ℂ) = (E.card : ℂ) := by
      rw [h1]
      simp
    rw [Multiset.card_map]
    exact (Nat.cast_injective h2).symm
  · rw [← hR, hE, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun χ _ => ?_
    simp

end Eig

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem dom_pow (a : Fin n → ℤ) (ha : Antitone a) (h0 : (GLnLocal.uniformizer F : F) ≠ 0) :
    UpperTheory.V.AlgebraTools.Dom fun i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i := by
  intro i j hij
  have hp : 0 < ValuativeRel.valuation F (GLnLocal.uniformizer F : F) := GLnLocal.valuation_uniformizer_pos F
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ hp (GLnLocal.valuation_uniformizer_lt_one F)).2 (ha hij)

private theorem iw_local [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (m : Measure (GL (Fin n) F)) [m.IsHaarMeasure] {I : Subgroup (GL (Fin n) F)}
    (hI : UpperTheory.V.AlgebraTools.iwC F n ⊤ = I) (hm : m I = 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (hIo : IsOpen (I : Set (GL (Fin n) F)))
    (hIc : IsCompact (I : Set (GL (Fin n) F))) (ν : Fin n → ℤ) (hν : Antitone ν)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ (UpperTheory.V.Hi.fixd ρ I) ∧
      ∀ j : ℕ, HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * Cartan.diagPow F n (j • ν) * b} 1)
        (Z.map (· ^ j)).sum := by
  subst hI
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := GLnLocal.uniformizer_ne_zero F
  let t : (Fin n → ℤ) → Fin n → Fˣ := fun a i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i
  have hdiag : ∀ a, Cartan.diagPow F n a = diagT F (Fin n) (t a) := fun a => by
    ext i j
    rw [val_diagT]
    simp [t, Cartan.diagPow]
  have ht : ∀ a b, t (a + b) = t a * t b := fun a b => by
    funext i
    simp [t, _root_.zpow_add]
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul F n ⊤ ℂ V ρ
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard F : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.2 (GlobalTheory.SplitWeil.one_lt_resCard F).ne_bot).isUnit
  let T := UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t ν))
  have hdom : ∀ a, Antitone a → UpperTheory.V.AlgebraTools.Dom (t a) := fun a ha => dom_pow a ha h0
  have hTu : IsUnit T := hunit hq _ (hdom ν hν)
  have hone : UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t 0)) = 1 := by
    have hd0 := hdom 0 (fun _ _ _ => le_rfl)
    have h1 := hmul _ _ hd0 hd0
    rw [← ht, add_zero] at h1
    exact (hunit hq _ hd0).mul_left_cancel (h1.trans (mul_one _).symm)
  have hpow : ∀ j : ℕ, UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t (j • ν))) = T ^ j := by
    intro j
    induction j with
    | zero => simpa using hone
    | succ j ih =>
      have hj : Antitone (j • ν) := fun a b hab => by
        simpa using mul_le_mul_of_nonneg_left (hν hab) (Int.natCast_nonneg j)
      rw [pow_succ, ← ih, hmul _ _ (hdom _ hj) (hdom _ hν), ← ht, succ_nsmul]
  obtain ⟨Z, hZ0, hZc, hZ⟩ := exists_powerSums T hTu
  refine ⟨Z, hZ0, hZc, fun j => ?_⟩
  have h := hasTrace_hk m hρ hIo hIc hm (diagT F (Fin n) (t (j • ν))) ((UpperTheory.V.AlgebraTools.heckePairIwC F n ⊤).1 _)
  rw [hpow, hZ, ← hdiag] at h
  exact h

end Loc

theorem UpperTheory.ConvolutionTheory.C.iwPow :
    UpperTheory.ConvolutionTheory.C.IwPow := by
  intro K _ _ n w _ _ m _ hm σ ν hν hfd
  haveI : FiniteDimensional ℂ (UpperTheory.V.Hi.fixd σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin n))) := hfd
  exact iw_local m (UpperTheory.V.AlgebraTools.memIwC _ n ⊤).2.1 hm σ.ρ σ.smooth (GLnLocal.isOpen_iwahori _ _)
    (GLnLocal.isCompact_iwahori _ _) ν hν
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) : UnitaryRep (Gw n w) (LL μ) :=
  (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)

theorem locU_apply (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (g : Gw n w) : locU μ w g = rhoL μ w g := rfl

theorem fixU_locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) :
    fixU (locU μ w) J = fixL μ w J := by
  ext v
  simp only [mem_fixU, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h _ (Subgroup.mem_map_of_mem _ hu)

end UpperTheory.ConvolutionTheory.C.Sf
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.GM
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def sphOff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ v ∉ P, fixL μ v (GLnLocal.integralGL (v.adicCompletion K) n)

def levOn (P : Finset (Pl K)) (U : ∀ v : Pl K, Subgroup (Gw n v)) : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
  levF fun v => if v ∈ P then U v else GLnLocal.integralGL (v.adicCompletion K) n

def FixLev : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), fixF μ (levOn P U) = sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v)

def OfinProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (mf : Measure (AdelicGLn.FiniteAdelicGL K n)) [mf.IsHaarMeasure], mf (AdelicGLn.integralFiniteGL K n) = 1 →
    ∀ (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
      (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (e : TF K n),
      Function.Injective w → (∀ i, (m i).IsHaarMeasure ∧ m i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
      (∀ i, Test (φ i)) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ x, e x = if ∀ v ∉ Finset.univ.image w, finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then
        ∏ i, φ i (finAt (w i) (finEmb K n x)) else 0) →
      Ofin μ mf e = (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))

def EigAdm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (x : ℝ), x ≠ 0 → ∀ (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), (∀ v ∈ P, CO (U v)) →
    FiniteDimensional ℂ ↥(eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v))

def TermF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (V : Submodule ℂ (LL μ))
      (τ : ∀ v : Pl F, SmIrr (Gw n v)) (x : ℝ), IsSummand μ V → 0 < x → (∀ v ∈ insert q S, Occurs μ V v (τ v)) →
      ∃ N : ℕ, (0 < N ↔ eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥) ∧
        ∀ (L : Loc σ n q w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → Antitone e → IsSideF L ν a e 𝔣 →
        ∀ (j : ℕ) (sq : ℂ) (s : Pl F → ℂ), HasTrace (m q) (τ q).ρ ((iwCoset q (j • e)).indicator 1) sq →
          (∀ v ∈ S, HasTrace (m v) (τ v).ρ (L.f v) (s v)) →
          trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = κ * x * N * sq * ∏ v ∈ S, s v

end UpperTheory.ConvolutionTheory.C
end
end

