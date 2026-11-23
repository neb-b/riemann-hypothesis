module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0005
public import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayTensConvRealSmoothT
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsSumTensOfIsLeftSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.HopfExpansion

section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem setInt_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → E) (y : G) {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T) (h : ∀ x, x ∈ S ↔ y * x ∈ T) :
    ∫ x in S, f (y * x) ∂m = ∫ x in T, f x ∂m := by
  rw [← integral_indicator hS, ← integral_indicator hT, ← integral_mul_left_eq_self (T.indicator f) y]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((h x).1 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((h x).2 h'))]

private theorem avg (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (u v : H) :
    ∫ j in (J : Set G), ⟪u, π j v⟫_ℂ ∂m = ⟪u, prj W v⟫_ℂ := by
  have hmeas : MeasurableSet (J : Set G) := hJo.measurableSet
  have hint : IntegrableOn (fun j => π j v) (J : Set G) m :=
    (π.continuous_orbit v).continuousOn.integrableOn_compact' hJ hmeas
  have hcl : IsClosed (W : Set H) := by
    have : (W : Set H) = ⋂ j ∈ J, {v | π j v = v} := by
      ext v
      simp [hW]
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (π j).continuous continuous_id
  have hA : (∫ j in (J : Set G), π j v ∂m) ∈ W := by
    rw [hW]
    intro j₀ hj₀
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    have := setInt_shift m (fun j => π j v) j₀ hmeas hmeas (fun x => by
      simp [Subgroup.mul_mem_cancel_left J hj₀])
    simpa [UnitaryRep.map_mul_apply] using this
  have hin : ∀ w ∈ W, ⟪w, ∫ j in (J : Set G), π j v ∂m⟫_ℂ = ⟪w, v⟫_ℂ := by
    intro w hw
    rw [← integral_inner hint w]
    have : ∀ j ∈ (J : Set G), ⟪w, π j v⟫_ℂ = ⟪w, v⟫_ℂ := by
      intro j hj
      rw [UnitaryRep.inner_map_right, (hW w).1 hw _ (J.inv_mem hj)]
    rw [setIntegral_congr_fun hmeas this]
    simp [Measure.real, hm]
  have hP : prj W v = ∫ j in (J : Set G), π j v ∂m := by
    change W.topologicalClosure.starProjection v = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hA) ?_
    intro w hw
    rw [hcl.submodule_topologicalClosure_eq] at hw
    rw [inner_sub_left, ← inner_conj_symm, ← inner_conj_symm _ w, hin w hw]
    simp
  rw [hP, integral_inner hint u]

private theorem main (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (x : G) (u v : H) :
    ⟪u, (∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}, π c.out) (prj W v)⟫_ℂ =
      ∫ g, Set.indicator {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} 1 g * ⟪u, π g v⟫_ℂ ∂m := by
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJo
  set S : Set (G ⧸ J) := {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} with hSdef
  have hSfin : S.Finite := by
    have e : S = (fun k : G => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hJ.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete
  set D : Set G := {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} with hDdef
  let P : G ⧸ J → Set G := fun c => QuotientGroup.mk ⁻¹' {c}
  have hPo : ∀ c, IsOpen (P c) := fun c => (isOpen_discrete {c}).preimage QuotientGroup.continuous_mk
  have hPmem : ∀ (c : G ⧸ J) (h : G), h ∈ (J : Set G) ↔ c.out * h ∈ P c := by
    intro c h
    have : (QuotientGroup.mk (c.out * h) : G ⧸ J) = c ↔ h ∈ J := by
      conv_lhs => rhs; rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simp
    exact this.symm
  have hD : D = ⋃ c ∈ hSfin.toFinset, P c := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨QuotientGroup.mk (a * x), ⟨a, ha, rfl⟩, ?_⟩
      change (QuotientGroup.mk (a * x * b) : G ⧸ J) = QuotientGroup.mk (a * x)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using J.inv_mem hb
    · rintro ⟨c, ⟨k, hk, rfl⟩, hg⟩
      have hg' : (QuotientGroup.mk g : G ⧸ J) = QuotientGroup.mk (k * x) := hg
      have := QuotientGroup.eq.1 hg'.symm
      exact ⟨k, hk, _, this, by group⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact Finset.measurableSet_biUnion _ fun c _ => (hPo c).measurableSet
  have hcont : Continuous fun g => ⟪u, π g v⟫_ℂ := continuous_const.inner (π.continuous_orbit v)
  have hPint : ∀ c, IntegrableOn (fun g => ⟪u, π g v⟫_ℂ) (P c) m := by
    intro c
    have e : P c = (fun h => c.out * h) '' (J : Set G) := by
      ext g
      constructor
      · intro hg
        refine ⟨c.out⁻¹ * g, (hPmem c _).2 (by simpa using hg), by simp⟩
      · rintro ⟨h, hh, rfl⟩
        exact (hPmem c h).1 hh
    have hc : IsCompact (P c) := by
      rw [e]
      exact hJ.image (continuous_const.mul continuous_id)
    exact hcont.continuousOn.integrableOn_compact' hc (hPo c).measurableSet
  have hind : (fun g => D.indicator (1 : G → ℂ) g * ⟪u, π g v⟫_ℂ) = D.indicator fun g => ⟪u, π g v⟫_ℂ := by
    ext g
    by_cases hg : g ∈ D <;> simp [hg]
  rw [hind, integral_indicator hDm, hD, integral_biUnion_finset _ (fun c _ => (hPo c).measurableSet) ?_
    (fun c _ => hPint c), finsum_mem_eq_finite_toFinset_sum _ hSfin, ContinuousLinearMap.sum_apply, inner_sum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← setInt_shift m (fun g => ⟪u, π g v⟫_ℂ) c.out hJo.measurableSet (hPo c).measurableSet (hPmem c)]
    rw [UnitaryRep.inner_map_right, ← avg π m J hJ hJo hm W hW]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [UnitaryRep.map_mul_apply]
    exact (UnitaryRep.inner_map_right π _ _ _).symm
  · intro c _ d _ hcd
    refine Set.disjoint_left.2 fun g hg hg' => hcd ?_
    exact (hg : _ = c).symm.trans hg'

end
end UpperTheory.ConvolutionTheory.C.HopfExpansion

theorem UpperTheory.ConvolutionTheory.C.hopOloc :
    UpperTheory.ConvolutionTheory.C.HopOloc := by
  intro K _ _ n μ _ w _ _ m _ J x hJ hm u v
  let φ : Gw n w →* normOneGL (K := K) (n := n) := (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)
  have hφ : Continuous φ := MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom φ hφ
  have hπ : ∀ x, π x = rhoL μ w x := fun _ => rfl
  have hW : ∀ v, v ∈ fixL μ w J ↔ ∀ j ∈ J, π j v = v := by
    intro v
    simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
    constructor
    · intro h j hj
      simpa [hπ, rhoL] using h _ ⟨j, hj, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      simpa [hπ, rhoL] using h j hj
  exact HopfExpansion.main π m J hJ.1 hJ.2 hm (fixL μ w J) hW x u v
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.C.olocEx :
    UpperTheory.ConvolutionTheory.C.OlocEx := by
  intro K _ _ n μ _ w _ _ m _ φ hφ
  have hL : MemLp φ 1 m := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom
    ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)
  refine ⟨π.integrated m hL.toLp, fun u v => ?_, fun T hT => ?_⟩
  · have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
  · refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    rw [hT u v, UnitaryRep.inner_integrated]
    have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private lemma powSum_eq_count (s : Multiset ℂ) (S : Finset ℂ) (h : ∀ z ∈ s, z ∈ S) (j : ℕ) :
    (s.map (· ^ j)).sum = ∑ z ∈ S, (s.count z : ℂ) * z ^ j := by
  classical
  rw [Finset.sum_multiset_map_count]
  have hsub : s.toFinset ⊆ S := fun z hz => h z (Multiset.mem_toFinset.1 hz)
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]
  · intro z _ hz
    have : s.count z = 0 := Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)
    simp [this]

private def powHom (z : ℂ) : Multiplicative ℕ →* ℂ where
  toFun n := z ^ n.toAdd
  map_one' := by simp
  map_mul' a b := by simp [pow_add]

private lemma powHom_injective : Function.Injective powHom := by
  intro a b h
  have := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simpa [powHom] using this

theorem UpperTheory.ConvolutionTheory.C.powIndep :
    UpperTheory.ConvolutionTheory.C.PowIndep := by
  classical
  intro ι _ c Z hZ hev ζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Finset ℂ := Finset.univ.biUnion fun i => (Z i).toFinset
  let a : ℂ → ℂ := fun z => ∑ i, c i * ((Z i).count z : ℂ)
  have hmem : ∀ i, ∀ z ∈ Z i, z ∈ S := fun i z hz =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩
  have key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0 := by
    intro j hj
    have h0 := hN j hj
    simp only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [a, Finset.sum_mul, mul_assoc]
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)
  have lin : LinearIndependent ℂ (fun z : S => (powHom z : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powHom z)
      (powHom_injective.comp Subtype.val_injective)
  rw [Fintype.linearIndependent_iff] at lin
  have hb := lin (fun z => a z * (z : ℂ) ^ N) (by
    funext n
    have := key (N + n.toAdd) (Nat.le_add_right _ _)
    rw [← Finset.sum_coe_sort S] at this
    simpa [powHom, pow_add, mul_assoc, Finset.sum_apply] using this)
  have ha : a ζ = 0 := by
    by_cases hζ : ζ ∈ S
    · have := hb ⟨ζ, hζ⟩
      exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (Z i).count ζ = 0 := Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)
      simp [this]
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Multiset.filter_eq', Multiset.card_replicate]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem tens_sum_left {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n) {ι : Type} (s : Finset ι)
    (f : ι → TI K n) (e : TF K n) : tens (∑ i ∈ s, f i) e = ∑ i ∈ s, tens (f i) e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 0 e).2.2.2.2 (0 : ℂ)).1
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn (f i) e).2.2.1, ih]

theorem UpperTheory.ConvolutionTheory.C.smoothDecay :
    UpperTheory.ConvolutionTheory.C.SmoothDecay := by
  intro K _ _ n μ _ a ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact UpperTheory.cuspDecay_of_rank_zero K μ a
  obtain ⟨U, hU, m, F, e, hF, he, rfl⟩ := UpperTheory.exists_sum_tens_of_isLeftSmooth K n hn a ha
  refine UpperTheory.cuspDecay_finset_sum K n μ (Fin m) _ fun j => ?_
  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ι, _, κ, γ, hκ, hFj⟩ := UpperTheory.exists_sum_conv_real_smoothT K n ν (F j) (hF j)
  rw [hFj, tens_sum_left hn Finset.univ (fun i => conv ν (κ i) (γ i)) (e j)]
  exact UpperTheory.cuspDecay_finset_sum K n μ ι _ fun i =>
    UpperTheory.cuspDecay_tens_conv_real_smoothT K n hn μ ν (κ i) (γ i) (e j) U hU (hκ i).1 (hκ i).2 (he j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem prj_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  simp only [prj, ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

private theorem rhoL_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) {k : GL (Fin n) (w.adicCompletion K)} (hk : k ∈ J) :
    rhoL μ w k ∘L prj (fixL μ w J) = prj (fixL μ w J) := by
  ext1 v
  have hle : (fixL μ w J).topologicalClosure ≤
      LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id := by
    apply Submodule.topologicalClosure_minimal
    · unfold fixL fixF rhoL
      exact iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)
    · exact isClosed_eq (rhoL μ w k).continuous continuous_id
  exact hle (Submodule.starProjection_apply_mem _ v)

private theorem hop_one {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Hop μ w J 1 = prj (fixL μ w J) := by
  have hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} =
      {QuotientGroup.mk 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using hk)
    · rintro rfl
      exact ⟨1, J.one_mem, rfl⟩
  unfold Hop
  rw [hs, finsum_mem_singleton]
  apply rhoL_prj
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))
  rw [hh, one_mul]
  exact h.2

theorem UpperTheory.ConvolutionTheory.C.uiwPow :
    UpperTheory.ConvolutionTheory.C.UiwPow := by
  intro K _ _ n μ _ w ν hν j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]
end

