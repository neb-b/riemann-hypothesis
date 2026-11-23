module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.LFun.SatBoundGL

private theorem mem_adicCompletionIntegers_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    letI := GlobalTheory.LocalData.complRel w
    x ∈ Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ↔ x ∈ w.adicCompletionIntegers E := by
  letI := GlobalTheory.LocalData.complRel w
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using h x 1


open ValuativeRel in
theorem resCard_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    GlobalTheory.SplitWeil.resCard (w.adicCompletion E) = Ideal.absNorm w.asIdeal := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w

  let e : Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ≃+* w.adicCompletionIntegers E :=
    { toFun := fun x => ⟨x.1, (mem_adicCompletionIntegers_iff w x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (mem_adicCompletionIntegers_iff w y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv, Formalism.UG.P.tjcosets_card_residue w]
  rfl

theorem norm_le_of_hasSatGL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro hT E _ _ w n V _ _ ρ B hirr hun hsat b hb
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨hsph, hvec⟩ := hsat

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hsph
  have hG : LGrp.HasSatakeGL ρ B := GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL hirr (hvec x hx hx0)
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ ρ B).mp hG
  have hR := hT (w.adicCompletion E) n V ρ α hirr.1 hirr.2 ((GlobalTheory.LGrp.isUnitarisable_iff ρ).mp hun) ?_ hα
  · rw [← hαB] at hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
    have hi := (hR i).2
    rwa [resCard_completion] at hi
  · unfold GlobalTheory.SmGL.IsSpherical
    exact (GlobalTheory.LGrp.isSpherical_iff ρ _).mp hG.2

end GlobalTheory.LFun.SatBoundGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OntoPartAtOfZeroOrInjAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes GlobalTheory.Hk3 GlobalTheory.SplitHeckeAdj

namespace GlobalTheory.LiftOntoCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Abstract

variable {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* H}
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup H} {χ : J →* ℂˣ} {Φ : H → W}

theorem mem_adForms_iff : Φ ∈ Bridge.AdForms ι ρ J χ ↔
    (∀ γ u, Φ (ι γ * u) = ρ γ (Φ u)) ∧ ∀ u k (hk : k ∈ J), Φ (u * k) = (χ ⟨k, hk⟩ : ℂ) • Φ u :=
  ⟨fun h => ⟨fun γ u => by simpa using h γ u 1, fun u k hk => by simpa using h 1 u ⟨k, hk⟩⟩,
    fun h γ u k => by rw [h.2 _ _ k.2, h.1]⟩

theorem eq_of_dual {x y : W} (h : ∀ ℓ : W →ₗ[ℂ] ℂ, ℓ x = ℓ y) : x = y :=
  sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by rw [map_sub, h ℓ, sub_self])

end Abstract

section General

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V)

variable {c}

theorem hasType_form {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {Φ : Bridge.Gf V → W}
    (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
    (ℓ : W →ₗ[ℂ] ℂ) : HasType V β (flag1L L) fun g => ℓ (Φ (fin V g)) := fun κ hκ g =>
  (congrArg (fun u => ℓ (Φ u)) ((fin V).map_mul g κ)).trans
    ((congrArg ℓ ((mem_adForms_iff.1 hΦ).2 (fin V g) _ ((mem_J V β L hκ.1).2 hκ))).trans (ℓ.map_smul _ _))

theorem forall_fin {p : Bridge.Gf V → Prop} (h : ∀ g ∈ GfC V, p (fin V g)) (u : Bridge.Gf V) : p u :=
  (fin_lift V u).elim fun g hg => hg.2 ▸ h g hg.1

theorem hkF_mem {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {w : Pl D.host.E}
    (a : List ℤ →₀ ℂ) (h3 : ∀ Φ, HasType V β (flag1L L) Φ → HasType V β (flag1L L) (hk V w a Φ))
    {Φ : Bridge.Gf V → W} (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    hkF V w a Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ := by
  have hc : ∀ (ℓ : W →ₗ[ℂ] ℂ) g, hk V w a (fun g => ℓ (Φ (fin V g))) g = ℓ (hkF V w a Φ (fin V g)) := fun ℓ g => by
    rw [GlobalTheory.LevOp.hk_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hkF, Finsupp.sum, map_sum, LinearMap.map_smul, smul_eq_mul, heckeLin_apply, MonoidHom.map_mul]
  refine mem_adForms_iff.2 ⟨fun γ u => ?_, fun u k => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [hkF, Finsupp.sum, mul_assoc, (mem_adForms_iff.1 hΦ).1, map_sum, LinearMap.map_smul]
  · refine forall_fin (p := fun k => ∀ hk : k ∈ (levEnv V β L).J,
      hkF V w a Φ (u * k) = ((levEnv V β L).χ ⟨k, hk⟩ : ℂ) • hkF V w a Φ u) (fun κ hκ hk => ?_) k
    refine forall_fin (p := fun u => hkF V w a Φ (u * fin V κ) = ((levEnv V β L).χ ⟨fin V κ, hk⟩ : ℂ) • hkF V w a Φ u)
      (fun g _ => eq_of_dual fun ℓ => ?_) u
    have := h3 _ (hasType_form hΦ ℓ) κ ((mem_J V β L hκ).1 hk) g
    rw [hc, hc, MonoidHom.map_mul] at this
    exact this.trans (ℓ.map_smul _ _).symm

theorem one_notMem (w : Pl D.host.E) (n : ℕ) : ((1 ^ n : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  rw [one_pow, Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top

end General

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offS_iff_good (t : T) (w : Pl D.host.E) : OffS D (badS R t) w ↔ Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold badS
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_opsV (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (i : Fin D.R.m) (t : T) : ∃ h, IsOpsV R i t h := by
  have key : ∀ w a, ∃ s : Module.End ℂ (R.HV i t).H, Good R t w → ∀ x, (R.HV i t).e (s x) = hkF (Vc D i) w a ((R.HV i t).e x) := by
    intro w a
    by_cases hw : Good R t w
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    refine (hL.βV i).elim fun n hn => ?_
    have h3 := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (flag1L (R.datVt i t)) hn w (one_notMem w n) hw).2.2.1 a
    exact (GlobalTheory.DefiniteOps.exists_lift (R.HV i t) _ _ (hM.HV i t)
      (opOf (GlobalTheory.DefiniteOps.rtr (fin (Vc D i)) (R.cV i).W) w a)
      fun Φ hΦ => GlobalTheory.DefiniteOps.hkF_eq (Vc D i) w a Φ ▸ hkF_mem a h3 hΦ).imp
      fun s hs _ x => (hs x).trans (GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).symm
  choose h hh using key
  exact ⟨h, fun w hw c x => hh w c hw x⟩

section Levels

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Levels

section Compare

variable (R) (F : Face D A)

variable {R}

variable (R)

end Compare

end GlobalTheory.LiftOntoCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMeasureModulus
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.ParabModulus

section General

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

noncomputable def prodMul (μM μN : Measure G) : Measure G := (μM.prod μN).map (fun z => z.1 * z.2)

theorem lintegral_prodMul (μM μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂prodMul μM μN = ∫⁻ m, ∫⁻ u, f (m * u) ∂μN ∂μM := by
  rw [prodMul, lintegral_map hf measurable_mul]
  exact lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable

theorem measurable_inner (μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    Measurable fun m => ∫⁻ u, f (m * u) ∂μN :=
  Measurable.lintegral_prod_right' (f := fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul)

theorem prodMul_left_fst (M : Subgroup G) (μM μN : Measure G) [SFinite μN]
    (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM) (s : G) (hs : s ∈ M) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iM s hs) _ (measurable_inner μN f hf)
  simpa only [mul_assoc] using this

theorem prodMul_left_snd (M N : Subgroup G) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m⁻¹ * u * m ∈ N)
    (μM μN : Measure G) [SFinite μN] (h1 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (s : G) (hs : s ∈ N) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  refine lintegral_congr_ae (aM.mono fun m hm => ?_)
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iN _ (hnorm m hm s hs)) (fun u => f (m * u))
    (hf.comp (measurable_const_mul m))
  show ∫⁻ u, f (s * (m * u)) ∂μN = ∫⁻ u, f (m * u) ∂μN
  rw [← this]
  refine lintegral_congr fun u => ?_
  rw [show m * (m⁻¹ * s * m * u) = s * (m * u) by group]

theorem prodMul_facts (M N P : Subgroup G) (hM : IsClosed (M : Set G)) (hN : IsClosed (N : Set G))
    (hPm : MeasurableSet (P : Set G)) (hMN : ∀ m ∈ M, m ∈ N → m = 1)
    (hMP : ∀ m ∈ M, ∀ u ∈ N, m * u ∈ P) (hdec : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ N, p = m * u)
    (μM μN : Measure G) [SigmaFinite μN] [IsFiniteMeasureOnCompacts μM] [IsFiniteMeasureOnCompacts μN]
    (hM0 : μM ≠ 0) (hN0 : μN ≠ 0) (h1 : μM (M : Set G)ᶜ = 0) (h2 : μN (N : Set G)ᶜ = 0) :
    prodMul μM μN (P : Set G)ᶜ = 0 ∧ SigmaFinite (prodMul μM μN) ∧
      ∃ T : Set G, MeasurableSet T ∧ prodMul μM μN T ≠ 0 ∧ prodMul μM μN T ≠ ⊤ := by
  set ρ₀ := prodMul μM μN with hρ₀
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h2
  have hP0 : ρ₀ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ₀, lintegral_prodMul _ _ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    rw [Set.indicator_of_notMem (show m * u ∉ (P : Set G)ᶜ from fun h => h (hMP m hm u hu))]
    simp
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ M) * (compactCovering G i ∩ N) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hM).mul ((isCompact_compactCovering G i).inter_right hN)
  have uniq : ∀ i, ∀ m ∈ M, ∀ u ∈ N, m * u ∈ Q i → m ∈ compactCovering G i ∧ u ∈ compactCovering G i := by
    rintro i m hm u hu ⟨m', ⟨hm'C, hm'M⟩, u', ⟨hu'C, hu'N⟩, e⟩
    have e : m' * u' = m * u := e
    have e' : m'⁻¹ * m = u' * u⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * u) * u⁻¹ := by group
        _ = m'⁻¹ * (m' * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group
    have h := hMN _ (M.mul_mem (M.inv_mem hm'M) hm) (by rw [e']; exact N.mul_mem hu'N (N.inv_mem hu))
    have hm' : m = m' := (inv_mul_eq_one.1 h).symm
    rw [h] at e'
    have hu' : u = u' := (mul_inv_eq_one.1 e'.symm).symm
    exact ⟨hm' ▸ hm'C, hu' ▸ hu'C⟩
  have hQ1 : ∀ i, ρ₀ (Q i) < ⊤ := by
    intro i
    have hC := isCompact_compactCovering G i
    rw [← lintegral_indicator_one (hQc i).measurableSet, hρ₀,
      lintegral_prodMul _ _ _ (measurable_one.indicator (hQc i).measurableSet)]
    calc _ ≤ ∫⁻ m, (compactCovering G i).indicator (fun _ => μN (compactCovering G i)) m ∂μM := by
          refine lintegral_mono_ae ?_
          filter_upwards [aM] with m hm
          by_cases hmC : m ∈ compactCovering G i
          · rw [Set.indicator_of_mem hmC, ← lintegral_indicator_one hC.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aN] with u hu
            by_cases hq : m * u ∈ Q i
            · simp [Set.indicator_of_mem hq, Set.indicator_of_mem (uniq i m hm u hu hq).2]
            · simp [Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem hmC]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aN] with u hu
            rw [Set.indicator_of_notMem (fun h => hmC (uniq i m hm u hu h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hC.measurableSet]
          exact ENNReal.mul_lt_top hC.measure_lt_top hC.measure_lt_top
  have hS : ⋃ i, (Q i ∪ (P : Set G)ᶜ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    by_cases hg : g ∈ P
    · obtain ⟨m, hm, u, hu, rfl⟩ := hdec g hg
      obtain ⟨i, hi⟩ := exists_mem_compactCovering m
      obtain ⟨k, hk⟩ := exists_mem_compactCovering u
      exact ⟨max i k, Or.inl (Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hm⟩
        ⟨compactCovering_subset G (le_max_right _ _) hk, hu⟩)⟩
    · exact ⟨0, Or.inr hg⟩
  have hS1 : ∀ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_union_le _ _) (by rw [hP0, add_zero]; exact hQ1 i)
  have sf : SigmaFinite ρ₀ := ⟨⟨⟨fun i => Q i ∪ (P : Set G)ᶜ, fun _ => trivial, hS1, hS⟩⟩⟩
  have huniv : ρ₀ Set.univ ≠ 0 := by
    rw [hρ₀, prodMul, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (fun h => hM0 (Measure.measure_univ_eq_zero.1 h))
      (fun h => hN0 (Measure.measure_univ_eq_zero.1 h))
  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact huniv (by rw [← hS]; exact measure_iUnion_null h)
  refine ⟨hP0, sf, Q i, (hQc i).measurableSet, fun h => hi ?_, (hQ1 i).ne⟩
  exact measure_union_null h hP0

theorem eq_smul_of_left_inv (P : Subgroup G) (hPm : MeasurableSet (P : Set G)) (ρ ρ₀ : Measure G)
    [SigmaFinite ρ] [SigmaFinite ρ₀] (h0 : ρ (P : Set G)ᶜ = 0) (h0' : ρ₀ (P : Set G)ᶜ = 0)
    (hi : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ) (hi' : ∀ s ∈ P, ρ₀.map (fun g => s * g) = ρ₀)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ₀ T ≠ 0) (hT1 : ρ₀ T ≠ ⊤) :
    ∃ c : ENNReal, ρ = c • ρ₀ := by
  have hemb : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hPm
  haveI : MeasurableMul₂ P := ⟨Measurable.subtype_mk
    ((hemb.measurable.comp measurable_fst).mul (hemb.measurable.comp measurable_snd))⟩
  haveI : MeasurableInv P := ⟨Measurable.subtype_mk hemb.measurable.inv⟩
  have hmap : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (τ.comap Subtype.val).map (Subtype.val : P → G) = τ := by
    intro τ h
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem h
  have hinv : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (∀ s ∈ P, τ.map (fun g => s * g) = τ) →
      (τ.comap (Subtype.val : P → G)).IsMulLeftInvariant := by
    intro τ h hτ
    refine ⟨fun s => ?_⟩
    rw [← hemb.comap_map ((τ.comap Subtype.val).map (fun g => s * g)),
      Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : P → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap τ h, hτ s s.2]
  haveI := hinv ρ h0 hi
  haveI := hinv ρ₀ h0' hi'
  haveI : SigmaFinite (ρ.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ h0]; infer_instance)
  haveI : SigmaFinite (ρ₀.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ₀ h0']; infer_instance)
  have hT' : ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) = ρ₀ T := by
    rw [← hmap ρ₀ h0', Measure.map_apply hemb.measurable hT, hmap ρ₀ h0']
  set c : ENNReal := ρ.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) /
    ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) with hc
  have key : ρ.comap (Subtype.val : P → G) = c • ρ₀.comap (Subtype.val : P → G) :=
    measure_eq_div_smul (ρ.comap (Subtype.val : P → G)) (ρ₀.comap (Subtype.val : P → G))
      (s := Subtype.val ⁻¹' T) (by rw [hT']; exact hT0) (by rw [hT']; exact hT1)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← hmap ρ h0, key]
  rw [Measure.map_smul, hmap ρ₀ h0']
  exact hemb.measurable.aemeasurable

end General

end GlobalTheory.ParabModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometry
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

theorem trace_mul_star_eq_sum (z z' : Fld P) :
    ∑ i, ∑ j, σ ((powB P).repr z' i) * gramOne P i j * (powB P).repr z j =
      Algebra.trace E (Fld P) (z * star' P z') := by
  have hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i) := by
    conv_lhs => rw [← (powB P).sum_repr z']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (powB P).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]
  ring

theorem isIsom_coordEquiv : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k],
    IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  intro F E _ _ _ σ r P k _ _ y y'
  simp only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
    | tmul a' z' =>
      have e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e := fun e => rfl
      have e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z' := rfl
      have e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j := fun i j => rfl
      have e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w := fun b w => rfl
      simp only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum,
        trace_mul_star_eq_sum]
      rw [mul_comm a' a]

end GlobalTheory.TrUnitLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatticeHalves

theorem splitLattice : ∀ D : D7, SplitLattice D := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨a, haA, ha0, hmax⟩, ⟨b, hbA, hb0, hbmax⟩⟩ := _root_.GlobalTheory.SplitIdealMax.exists_max_both D v φ e he
  refine ⟨⟨a, haA, ha0, hmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩,
    ⟨b, hbA, hb0, hbmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact _root_.GlobalTheory.SplitHomBound.hbound D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := _root_.GlobalTheory.SplitHomOnto.honto D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact _root_.GlobalTheory.SplitAdjBound.adjCo_bound D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := _root_.GlobalTheory.ConjHalfOnto.conj_half_onto D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbA hb0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩

end GlobalTheory.SplitLatticeHalves
end

