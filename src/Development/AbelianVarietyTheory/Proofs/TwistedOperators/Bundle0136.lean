module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralEqZeroOfNormalisedCosetIntegrals
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Orb

theorem isMulRightInvariant_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun x : G => x * g) = fun x => g * x := funext fun x => IsMulCommutative.is_comm.comm x g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

section Weight

variable {H : Type} [Group H]

theorem exists_nt_mul {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (p q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((p.1 : H) * p.2) * ((q.1 : H) * q.2) :=
  ⟨(p.1 * ⟨(p.2 : H) * q.1 * (p.2 : H)⁻¹, hnorm _ p.2.2 _ q.1.2⟩, p.2 * q.2), by simp [mul_assoc]⟩

theorem exists_nt_inv {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((q.1 : H) * q.2)⁻¹ :=
  ⟨(⟨(q.2 : H)⁻¹ * (q.1 : H)⁻¹ * (q.2 : H)⁻¹⁻¹, hnorm _ (inv_mem q.2.2) _ (inv_mem q.1.2)⟩, q.2⁻¹), by
    simp only [Subgroup.coe_inv, inv_inv, mul_inv_rev]; group⟩

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_weight_nt (T N : Subgroup H) (hT : IsClosed (T : Set H)) (hN : IsClosed (N : Set H))
    (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hj : Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2))
    (dt : Measure T) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] :
    ∃ β : H → ℝ≥0∞, Measurable β ∧ (∀ x, β x ≠ ∞) ∧ (∀ n ∈ N, ∀ x, β (n * x) = β x) ∧
      ∀ x, ∫⁻ t : T, β (t * x) ∂dt = 1 := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  set j : N × T → H := fun p => (p.1 : H) * p.2 with hjdef
  have hjc : Continuous j := hj.continuous
  let K := CompactExhaustion.choice H
  let W : ℕ → Set H := fun k => interior (K (k + 1))
  have hWo : ∀ k, IsOpen (W k) := fun k => isOpen_interior
  let U : ℕ → Set H := fun k => {x | ∃ p : N × T, j p * x ∈ W k}
  have hUfwd : ∀ k q x, x ∈ U k → j q * x ∈ U k := by
    rintro k q x ⟨p, hp⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    obtain ⟨s, hs⟩ := exists_nt_mul hnorm p r
    refine ⟨s, ?_⟩
    have e : j s * (j q * x) = j p * x := by
      rw [show j s = j p * j r from hs, show j r = (j q)⁻¹ from hr]; group
    rw [e]; exact hp
  have hU : ∀ k q x, j q * x ∈ U k ↔ x ∈ U k := by
    refine fun k q x => ⟨fun h => ?_, hUfwd k q x⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    have := hUfwd k r _ h
    rwa [show j r = (j q)⁻¹ from hr, inv_mul_cancel_left] at this
  have hUo : ∀ k, IsOpen (U k) := fun k => by
    have : U k = ⋃ p : N × T, (fun x => j p * x) ⁻¹' W k := by ext x; simp [U]
    rw [this]
    exact isOpen_iUnion fun p => (hWo k).preimage (continuous_const_mul _)
  have hcov : ∀ x, ∃ k, x ∈ U k := fun x => by
    obtain ⟨k, hk⟩ := K.exists_mem x
    exact ⟨k, (1, 1), by simpa [j] using K.subset_interior_succ k hk⟩
  let P : ℕ → Set H := disjointed U
  have hPm : ∀ k, MeasurableSet (P k) := MeasurableSet.disjointed fun k => (hUo k).measurableSet
  have hP : ∀ k q x, j q * x ∈ P k ↔ x ∈ P k := fun k q x => by
    simp only [P, disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff, hU]
  have hPcov : ∀ x, ∃ k, x ∈ P k := fun x => by
    have : x ∈ ⋃ k, P k := by rw [iUnion_disjointed]; exact mem_iUnion.2 (hcov x)
    exact mem_iUnion.1 this
  have hPd : ∀ k k' x, x ∈ P k → x ∈ P k' → k = k' := fun k k' x h h' => by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed U hne) h h'
  let h : H → ℝ≥0∞ := fun x => ∑' k, (P k).indicator ((W k).indicator 1) x
  have hh : Measurable h := Measurable.tsum fun k =>
    (measurable_one.indicator (hWo k).measurableSet).indicator (hPm k)
  have hval : ∀ k x, x ∈ P k → ∀ q, h (j q * x) = (W k).indicator 1 (j q * x) := by
    intro k x hx q
    have hx' := (hP k q x).2 hx
    refine (tsum_eq_single k fun k' hk' => ?_).trans (indicator_of_mem hx' _)
    exact indicator_of_notMem (fun h' => hk' (hPd _ _ _ h' hx')) _
  let g : H → ℝ≥0∞ := fun x => ∫⁻ n : N, h (n * x) ∂dn
  let I : H → ℝ≥0∞ := fun x => ∫⁻ t : T, g (t * x) ∂dt
  have hg : Measurable g := measurable_fiber hh
  have hI : Measurable I := measurable_fiber hg
  have hgN : ∀ n ∈ N, ∀ x, g (n * x) = g x := fun n hn x => by
    simpa [g, mul_assoc] using lintegral_mul_right_eq_self (μ := dn) (fun m : N => h (m * x)) ⟨n, hn⟩
  have hIN : ∀ n ∈ N, ∀ x, I (n * x) = I x := fun n hn x => by
    refine lintegral_congr fun t => ?_
    have e : (t : H) * (n * x) = ((t : H) * n * (t : H)⁻¹) * (t * x) := by group
    rw [e, hgN _ (hnorm _ t.2 _ hn)]
  have hIT : ∀ s ∈ T, ∀ x, I (s * x) = I x := fun s hs x => by
    simpa [I, mul_assoc] using lintegral_mul_right_eq_self (μ := dt) (fun t : T => g (t * x)) ⟨s, hs⟩
  have hIprod : ∀ x, I x = ∫⁻ p, h (j p * x) ∂(dn.prod dt) := fun x => by
    rw [lintegral_prod_symm (fun p => h (j p * x)) (hh.comp (hjc.measurable.mul_const x)).aemeasurable]
    simp [I, g, j, mul_assoc]
  have hcpt : ∀ k x, IsCompact ((fun y => y * x) ⁻¹' K (k + 1)) := fun k x => by
    have := (Homeomorph.mulRight x).isCompact_preimage.2 (K.isCompact (k + 1))
    simpa using this
  have hIpos : ∀ x, I x ≠ 0 ∧ I x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set E := (fun p => j p * x) ⁻¹' W k with hEdef
    have hE : IsOpen E := (hWo k).preimage (hjc.mul continuous_const)
    have e : I x = dn.prod dt E := by
      rw [hIprod, ← lintegral_indicator_one hE.measurableSet]
      exact lintegral_congr fun p => by rw [hval k x hk p]; rfl
    obtain ⟨p, hp⟩ := disjointed_subset U k hk
    refine ⟨e ▸ hE.measure_ne_zero _ ⟨p, hp⟩, e ▸ ?_⟩
    refine (measure_mono (μ := dn.prod dt) (s := E) (t := j ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))) ?_).trans_lt
      (hj.isCompact_preimage (hcpt k x)).measure_lt_top |>.ne
    intro q hq
    exact interior_subset (s := K (k + 1)) hq
  have hgfin : ∀ x, g x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set C : Set N := (↑) ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))
    have hC : IsCompact C := hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hcpt k x)
    refine ne_of_lt (lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := dn)))
    rw [← lintegral_indicator_one hC.measurableSet]
    refine lintegral_mono fun n => ?_
    have e : h ((n : H) * x) = (W k).indicator 1 ((n : H) * x) := by
      simpa [j] using hval k x hk (n, 1)
    rw [e]
    by_cases hn : (n : H) * x ∈ W k
    · rw [indicator_of_mem hn, indicator_of_mem (show n ∈ C from interior_subset (s := K (k + 1)) hn)]; exact le_rfl
    · rw [indicator_of_notMem hn]; exact zero_le
  refine ⟨fun x => g x * (I x)⁻¹, hg.mul hI.inv, fun x => ENNReal.mul_ne_top (hgfin x)
    (ENNReal.inv_ne_top.2 (hIpos x).1), fun n hn x => by simp only [hgN n hn, hIN n hn], fun x => ?_⟩
  have e : ∀ t : T, g (t * x) * (I (t * x))⁻¹ = g (t * x) * (I x)⁻¹ := fun t => by rw [hIT _ t.2]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hIpos x).1)]
  exact ENNReal.mul_inv_cancel (hIpos x).1 (hIpos x).2

end Weight

theorem quotInt_eq_zero_of_integral_coset_eq_zero : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T →
    (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) →
    ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure]
    [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ →
    Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  intro H _ _ _ _ _ _ _ _ T N hT hN hc hnorm hj dh _ dt _ dn _ _ φ hφ hφT hint h0
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_of_isMulCommutative dt
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨β, hβm, hβf, hβN, hβ1⟩ := exists_weight_nt T N hT hN hnorm hj dt dn
  have hν : quotMeas T dt dh = (dh.withDensity β).map (mk T) :=
    (isQuotMeasure_quotMeas dt dh hT).eq_map hβm hβ1
  have hlt : ∀ᵐ x ∂dh, β x < ∞ := .of_forall fun x => lt_top_iff_ne_top.2 (hβf x)
  have hD : Measurable (descend T φ) := measurable_descend hφT hφ
  have hcomp : descend T φ ∘ mk T = φ := funext hφT.descend_mk
  have hφβ : Integrable φ (dh.withDensity β) := by
    rw [hν] at hint
    have := (integrable_map_measure hD.aestronglyMeasurable measurable_mk.aemeasurable).1 hint
    rwa [hcomp] at this
  have hF : Integrable (fun x => (β x).toReal • φ x) dh :=
    (integrable_withDensity_iff_integrable_smul' hβm hlt).1 hφβ
  have e1 : quotInt T dt dh φ = ∫ x, (β x).toReal • φ x ∂dh := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable hD.aestronglyMeasurable,
      ← integral_withDensity_eq_integral_toReal_smul hβm hlt]
    exact integral_congr_ae (.of_forall fun x => hφT.descend_mk x)
  have hW := (weil_integral (dt := dn) hN hF).2
  have e2 : (fun x => ∫ n : N, (β (n * x)).toReal • φ (n * x) ∂dn) = fun _ => (0 : ℂ) := funext fun x => by
    have e : ∀ n : N, (β (n * x)).toReal • φ (n * x) = (β x).toReal • φ (n * x) := fun n => by
      rw [hβN _ n.2 x]
    simp_rw [e]
    rw [integral_smul, h0 x, smul_zero]
  rw [e1, ← hW.2, e2]
  simp [quotInt, descend]

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacuumLine

open GlobalTheory.FockCompare GlobalTheory.VacUnique

private theorem selfDual_isFullLattice {D : D7} {V : HSp D}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ) :
    Submodule.IsFullLattice D.host.E Λ := by
  refine { toIsLattice := hΛ.1, span_eq_top := ?_ }
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  -- Clear the denominators of the pairings with a finite generating set for Λ.
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have hscaled := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy'
  simpa only [smul_smul, inv_mul_cancel₀ ha0, one_smul] using hscaled

theorem eq_smul_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb f hf hlat hfock
  have hne : f₀ ≠ 0 := GlobalTheory.PlaceTensor.base_ne_zero hb
  obtain ⟨hS, hT, dS, dT, hψ, hθ, ht₀, hl₀, hF₀, -⟩ := hb
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  obtain ⟨ρ, hρc, hρ1, hρ2⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ hρc hρ1 hρ2
  obtain ⟨hdual, hdec, heig⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ dS dT
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have key : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u f = ε • f ∧ heisO ψ S T u f₀ = ε • f₀ := by
    intro u hu
    obtain ⟨ε, hε, h⟩ := heig f hlat u hu
    exact ⟨ε, hε, h f hlat, h f₀ hl₀⟩
  have ext : ∀ w, ∃ z : RW T S, ∃ a : ℂ, f w = a * f (iotaW σ T S z) ∧ f₀ w = a * f₀ (iotaW σ T S z) := by
    intro w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp hσ hdec w
    obtain ⟨ε, -, h1, h2⟩ := key u hu
    refine ⟨z, ψ (-symplOH S T (ratW T S γ) (iotaW σ T S z + u)) * ε, ?_, ?_⟩
    · rw [hf.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h1 z]; ring
    · rw [ht₀.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h2 z]; ring
  have hN : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ :=
    GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
      (selfDual_isFullLattice dS) (selfDual_isFullLattice dT)
  have hLd := _root_.GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ Λ hψ hinf hdual hdec hN
  obtain ⟨hJ, hanti, hinv, hpos⟩ := _root_.GlobalTheory.RealSymplForm.form_alt_inv_def D S T sS sT hS hT
  classical
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv).choose else 1
  have hc : ∀ v, ‖c v‖ = 1 := by
    intro v
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψn, one_mul]
      rcases (key _ hv).choose_spec.1 with h | h <;> rw [h] <;> simp
    · simp
  have hfd := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T sS sT f hf hfock
  have hfd₀ := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T sS sT f₀ ht₀ hF₀
  have hspan : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := GlobalTheory.FockCompare.span_piW_ratW_eq_top D θ σ hσ T S
    simpa [GlobalTheory.VacUnique.piW_ratW hθ] using this
  have hli := _root_.GlobalTheory.VacuumLine.not_linearIndependent (RW T S) (jO S T sS sT) (omO S T) hJ hanti hinv hpos
    (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (GlobalTheory.VacUnique.infRat_injective S T) hspan
    (Λ.comap (finRat S T)) (fun x => by simpa using hN x) (fun x => by simpa using hLd x) c hc
    ![fun z => f₀ (iotaW σ T S z), fun z => f (iotaW σ T S z)]
    (Fin.forall_fin_two.2 ⟨hfd₀.1, hfd.1⟩) ?fock ?quasi
  case fock => exact Fin.forall_fin_two.2 ⟨hfd₀.2, hfd.2⟩
  case quasi =>
    intro k v hv z
    have hv' : finRat S T (-v) ∈ Λ := by
      rw [map_neg]
      exact Λ.neg_mem (AddSubgroup.mem_comap.1 hv)
    have hcv : c v = ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv').choose := by
      simp only [c, dif_pos hv']
    obtain ⟨-, h1, h2⟩ := (key _ hv').choose_spec
    have e1 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ hf v h1 z
    have e2 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ ht₀ v h2 z
    have ho : (omO S T z (infRat S T v) : ℂ) = ((-omO S T (infRat S T v) z : ℝ) : ℂ) := by rw [hanti]
    rw [hcv, ho]
    fin_cases k
    · exact e2
    · exact e1
  rw [LinearIndependent.pair_iff] at hli
  push_neg at hli
  obtain ⟨s, t, hst, hne0⟩ := hli
  have hpt : ∀ z, s * f₀ (iotaW σ T S z) + t * f (iotaW σ T S z) = 0 := fun z => by
    have := congrFun hst z
    simpa using this
  by_cases ht : t = 0
  · exfalso
    have hs : s ≠ 0 := fun hs => hne0 hs ht
    apply hne
    funext w
    obtain ⟨z, a, -, h2⟩ := ext w
    have := hpt z
    rw [ht, zero_mul, add_zero] at this
    rw [h2, (mul_eq_zero.1 this).resolve_left hs]
    simp
  · refine ⟨-s / t, ?_⟩
    funext w
    obtain ⟨z, a, h1, h2⟩ := ext w
    have := hpt z
    rw [Pi.smul_apply, smul_eq_mul, h1, h2, div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination a * this

end GlobalTheory.VacuumLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff char_fin_add)
open scoped nonZeroDivisors

namespace GlobalTheory.SplitUnram

variable {F : Type} [Field F] [NumberField F]

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (h : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have h1 : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := fun x => by
    rw [h, mul_comm, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
      rw [eq_intCast]
      exact_mod_cast this.symm
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩
  have h2 : ∀ x : F, x ∈ codiff F ↔
      ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := fun x => by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    simp_rw [h1, Algebra.traceForm_apply]
    constructor
    · intro H a
      rw [mul_comm]
      exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · intro H a ha
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [mul_comm]
      exact H a
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [h2]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hc x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (p : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 F)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [not_dvd_differentIdeal_iff]
  apply Ideal.ramificationIdx_eq_one_iff.1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal hb]
  by_contra hne
  rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
  exact h2 (by simpa using hne)

theorem count_codiff_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    FractionalIdeal.count F v (codiff F) = 0 := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv,
    not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 v.irreducible).1 h)] at h1
  simpa using h1

theorem not_mem_sq_of_ext {E : Type} [Field E] [NumberField E] [Algebra F E] {p : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) : (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro hv
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 hQv.over.le
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv
  rw [Ideal.map_pow, map_natCast] at h1
  have h2 : (p : 𝓞 E) ∈ Q ^ 2 := Ideal.pow_right_mono hle 2 h1
  exact h ⟨Q, hQ.isPrime, hb⟩ (Ideal.pow_le_self two_ne_zero h2) h2

end GlobalTheory.SplitUnram

end
end

