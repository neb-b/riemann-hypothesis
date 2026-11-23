module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LiftFactorization
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
public import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.GlobalTwistedTraceBound
section
noncomputable section

open NumberField MeasureTheory Matrix Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB (thetaA)
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

private theorem trace_range {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (i : U →ₗ[ℂ] V) (B : V →ₗ[ℂ] U) (F : Submodule ℂ U) [FiniteDimensional ℂ F] (hB : ∀ v, B v ∈ F) :
    FiniteDimensional ℂ (LinearMap.range (i ∘ₗ B)) ∧
      trOn F (B ∘ₗ i) = LinearMap.trace ℂ (LinearMap.range (i ∘ₗ B))
        ((i ∘ₗ B).restrict fun x _ => LinearMap.mem_range_self (i ∘ₗ B) x) := by
  have hle : LinearMap.range B ≤ F := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hle
  haveI hfin : FiniteDimensional ℂ (LinearMap.range (i ∘ₗ B)) := by
    rw [LinearMap.range_comp]
    infer_instance
  refine ⟨hfin, ?_⟩
  let a : LinearMap.range (i ∘ₗ B) →ₗ[ℂ] LinearMap.range B := B.rangeRestrict ∘ₗ (LinearMap.range (i ∘ₗ B)).subtype
  let b : LinearMap.range B →ₗ[ℂ] LinearMap.range (i ∘ₗ B) :=
    (i ∘ₗ (LinearMap.range B).subtype).codRestrict _ (by
      rintro ⟨_, v, rfl⟩
      exact ⟨v, rfl⟩)
  let p : F →ₗ[ℂ] LinearMap.range B := B.rangeRestrict ∘ₗ i ∘ₗ F.subtype
  have h0 : ∀ x ∈ F, (B ∘ₗ i) x ∈ F := fun x _ => hB _
  have e1 : (B ∘ₗ i).restrict h0 = Submodule.inclusion hle ∘ₗ p := by
    ext x
    rfl
  have e2 : p ∘ₗ Submodule.inclusion hle = a ∘ₗ b := by
    ext x
    rfl
  have e3 : b ∘ₗ a = (i ∘ₗ B).restrict fun x _ => LinearMap.mem_range_self (i ∘ₗ B) x := by
    ext x
    rfl
  rw [trOn, dif_pos h0, e1, LinearMap.trace_comp_comm', e2, LinearMap.trace_comp_comm', e3]

private theorem trOn_smul {U : Type} [AddCommGroup U] [Module ℂ U] (F : Submodule ℂ U) (c : ℂ) (f : U →ₗ[ℂ] U)
    (hf : ∀ x ∈ F, f x ∈ F) : trOn F (c • f) = c * trOn F f := by
  have h : ∀ x ∈ F, (c • f) x ∈ F := fun x hx => F.smul_mem c (hf x hx)
  have e : (c • f).restrict h = c • f.restrict hf := by
    ext x
    rfl
  rw [trOn, trOn, dif_pos h, dif_pos hf, e, map_smul, smul_eq_mul]

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_theta (π : CuspSub E n) (hθ : ThetaFix π) :
    ∃ t : π.V →ₗ[ℂ] π.V, ∀ ψ g, (t ψ).1.1 g = ψ.1.1 (thetaA E n g) := by
  choose f hf hfe using hθ.2
  refine ⟨⟨⟨fun ψ => ⟨f ψ.1 ψ.2, hf ψ.1 ψ.2⟩, fun a b => ?_⟩, fun c a => ?_⟩, fun ψ g => hfe ψ.1 ψ.2 g⟩
  · refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f (a + b).1 (a + b).2).1 g = (f a.1 a.2).1 g + (f b.1 b.2).1 g
    rw [hfe, hfe, hfe]
    rfl
  · refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f (c • a).1 (c • a).2).1 g = c * (f a.1 a.2).1 g
    rw [hfe, hfe]
    rfl

private theorem integrable_hecke (π : CuspSub E n) {K : Subgroup (GL (Fin n) (Af E))}
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) (ψ : π.V)
    (x : GA E n) : Integrable (fun g => h g * ψ.1.1 (x * finGL E n g)) μf := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hh.1.mul_right
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
  have hS : IsOpen {k | finRep E n k ψ.1 = ψ.1} := (π.cusp ψ.1 ψ.2).1.level
  have ho : IsOpen ((fun y => g⁻¹ * y) ⁻¹' ((K : Set (GL (Fin n) (Af E))) ∩ {k | finRep E n k ψ.1 = ψ.1})) :=
    (hKo.inter hS).preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (x := g) (by simp [K.one_mem])] with y hy
  have e1 : h y = h g := by simpa using hh.2 1 K.one_mem _ hy.1 g
  have e2 : ψ.1.1 (x * finGL E n g * finGL E n (g⁻¹ * y)) = ψ.1.1 (x * finGL E n g) :=
    congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n (g⁻¹ * y) ψ.1 = ψ.1 from hy.2)
  rw [mul_assoc, ← map_mul, mul_inv_cancel_left] at e2
  rw [e1, e2]

private theorem exists_hecke (hM : HeckeMem) (π : CuspSub E n) {K : Subgroup (GL (Fin n) (Af E))}
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (D : Rl π K μf) {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ S : π.V →ₗ[ℂ] D.U, ∀ ψ, (D.i (S ψ)).1.1 = heckeOp μf h ψ.1.1 := by
  have hex : ∀ ψ : π.V, ∃ u, (D.i u).1.1 = heckeOp μf h ψ.1.1 := fun ψ => by
    obtain ⟨-, -, ψ', -, h1, h2⟩ := hM E n π K hKo hKc μf h hh ψ
    obtain ⟨u, rfl⟩ := (D.rng ψ').2 h2
    exact ⟨u, h1⟩
  choose f hf using hex
  refine ⟨⟨⟨f, fun a b => D.inj ?_⟩, fun c a => D.inj ?_⟩, hf⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [map_add (f := _)]
    change (D.i (f (a + b))).1.1 x = (D.i (f a)).1.1 x + (D.i (f b)).1.1 x
    rw [hf, hf, hf, heckeOp, heckeOp, heckeOp,
      ← integral_add (integrable_hecke π hKo μf hh a x) (integrable_hecke π hKo μf hh b x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_add (h g) (a.1.1 _) (b.1.1 _)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [map_smul]
    change (D.i (f (c • a))).1.1 x = c * (D.i (f a)).1.1 x
    rw [hf, hf, heckeOp, heckeOp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_left_comm (h g) c (a.1.1 _)

end Conc

end UpperTheory.V.Z.GSp4Splitting

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in
theorem UpperTheory.V.Z.Mult.Pi.twisted_trace_global_bound_of_archimedean :
    AvgEx → UpperTheory.V.Z.Mult.Pi.AbsGlobA → LowIso → HeckeMem → RlEx → RlPair → RlChar → RlK → RlTheta → RlComm → RlHecke → RlSimple → RlFin → RlLow → UpperTheory.V.Z.Mult.Pi.OpFormA → UpperTheory.V.Z.Mult.Pi.GlobalTwistedTraceBound := by
  intro hAvg hAbs hLow hM hEx hPair hChar hK hTh hComm hHk hSim hFin hRL hOp
  intro E _ _ _ n _ _ μC _ _ _ μf _ μ _
  obtain ⟨c₂, hc₂, hOp⟩ := hOp E n μC μf μ
  refine ⟨‖c₂‖ * (2 ^ n) ^ Fintype.card (InfinitePlace E), mul_pos (norm_pos_iff.2 hc₂) (by positivity), ?_⟩
  intro hn π hreg hθ lam hlam hch K hKo hKc hKθ hfix
  classical
  obtain ⟨D⟩ := hEx E n hn π hθ K hKo hKc hKθ μf
  replace hPair := hPair E n hn π hθ K hKo hKc hKθ μf D
  replace hChar := hChar E n hn π hθ K hKo hKc hKθ μf D
  replace hK := hK E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hsq, hiso, hT⟩ := hTh E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hc1, hc2, hc3⟩ := hComm E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hadj, htw⟩ := hHk E n hn π hθ K hKo hKc hKθ μf D
  replace hSim := hSim E n hn π hθ K hKo hKc hKθ μf D
  replace hFin := hFin E n hn π hθ K hKo hKc hKθ μf D fun w => lefE n (lam w)
  replace hRL := hRL E n hn π hθ K hKo hKc hKθ μf D hreg
  replace hOp := hOp hn π hθ K hKo hKc hKθ D lam hch
  have hnt : Nontrivial D.U := by
    obtain ⟨ψ, hψ, hψ0, hψK⟩ := hfix
    obtain ⟨u, hu⟩ := (D.rng ⟨ψ, hψ⟩).2 hψK
    refine nontrivial_of_ne u 0 fun h0 => hψ0 ?_
    rw [h0, map_zero] at hu
    exact (congrArg Subtype.val hu).symm
  letI : MeasurableSpace (Un n) := borel _
  haveI : BorelSpace (Un n) := ⟨rfl⟩
  let ν : Measure (Un n) := Measure.haarMeasure ⊤
  have hν : ν Set.univ = 1 := Measure.haarMeasure_self (K₀ := ⊤)
  have hloc : ∀ w, IsLoc (infOf (lam w)) (D.E1 w) (D.E2 w) (D.σ w) D.Θ := fun w =>
    ⟨hPair w, (hChar w (lam w) (hch w)).1, (hChar w (lam w) (hch w)).2, (hK w).2, (hK w).1, hsq, hiso, (hT w).1, (hT w).2⟩
  choose P hP using fun w => hAvg n ν D.U (D.σ w) (hK w).1 (lefE n (lam w)) (lefT n (lam w))
  obtain ⟨Y, c₁, hc₁, hYf, hY0, hYR, hYΘ, hYs, hPF, htr⟩ := hAbs n (InfinitePlace E) lam hlam (fun w => lefE n (lam w))
    (fun w => lefT n (lam w)) (fun w => isLefK_model (lam w) (hlam w)) ν hν D.U D.E1 D.E2 D.σ D.Θ P _ D.R hloc hP hc1 hc2 hc3
    hadj (fun h => (htw h).imp fun _ h' => h'.2) hsq hSim hnt hFin
    (fun w => hLow n (lam w) (hlam w) _ _ (isLefK_model (lam w) (hlam w)) D.U _ _ _ _ (hloc w)
      (hRL hnt w (lam w) (hlam w) (hch w)))
  have hop := hOp ν hν P hP
  let j : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hj : Function.Injective j := Subtype.val_injective.comp D.inj
  let e : Y ≃ₗ[ℂ] Y.map j := Submodule.equivMapOfInjective j hj Y
  have he : ∀ y : Y, ((e y : Y.map j) : Sm E n) = (D.i y).1 := fun _ => rfl
  let ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ (Y.map j) := fun h =>
    if hh : IsHeckeF K h then e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) else 0
  have hρ : ∀ h (hh : IsHeckeF K h), ρ h = e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) := fun h hh => dif_pos hh
  have hmul : ∀ f g : Module.End ℂ Y, e.conj f * e.conj g = e.conj (f * g) := fun f g => (e.conj_comp g f).symm
  refine ⟨Y.map j, ρ, e.conj (D.Θ.restrict hYΘ), c₂ * c₁, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [norm_mul, hc₁], ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact (D.i u).2
  · intro h0
    refine hY0 ((Submodule.eq_bot_iff _).2 fun y hy => hj ?_)
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h0 _ ⟨y, hy, rfl⟩
  · rintro _ ⟨u, -, rfl⟩
    exact (D.rng (D.i u)).1 ⟨u, rfl⟩
  · intro h hh y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hρ h hh, LinearEquiv.conj_apply_apply, e.symm_apply_apply, he, he]
    exact D.hR ⟨h, hh⟩ y
  · intro W hW
    rcases hYs ((W.comap e.toLinearMap).map Y.subtype) (Submodule.map_subtype_le _ _) (by
      rintro ⟨h, hh⟩ _ ⟨y, hy, rfl⟩
      refine ⟨(D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩) y, ?_, rfl⟩
      have := hW h hh (e y) hy
      rwa [hρ h hh, LinearEquiv.conj_apply_apply, e.symm_apply_apply] at this) with h0 | h1
    · refine Or.inl ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
      obtain ⟨y, rfl⟩ := e.surjective y
      have : (y : D.U) = 0 := (Submodule.eq_bot_iff _).1 h0 _ ⟨y, hy, rfl⟩
      exact (congrArg e (show y = 0 from Subtype.ext this)).trans e.map_zero
    · refine Or.inr (Submodule.eq_top_iff'.2 fun y => ?_)
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨z, hz, hzy⟩ : (y : D.U) ∈ (W.comap e.toLinearMap).map Y.subtype := h1.symm ▸ y.2
      rw [← show z = y from Subtype.ext hzy]
      exact hz
  · rw [hmul]
    have : D.Θ.restrict hYΘ * D.Θ.restrict hYΘ = 1 :=
      LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun hsq y.1)
    rw [this]
    exact e.conj_id
  · intro h hh
    obtain ⟨⟨h', hh'⟩, rfl, hc⟩ := htw ⟨h, hh⟩
    rw [hρ h hh, hρ _ hh', hmul, hmul]
    exact congrArg e.conj (LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun hc y.1))
  · intro k val T hk h hh
    obtain ⟨t, ht⟩ := exists_theta π hθ
    obtain ⟨S, hS⟩ := exists_hecke hM π hKo hKc μf D hh
    set Q : Module.End ℂ D.U := ((univ : Finset (InfinitePlace E)).toList.map P).prod with hQ
    set a : ℂ := c₂ * ∏ w, val w (infOf (lam w)) with ha
    haveI := hFin
    obtain ⟨hf, htrL⟩ := trace_range D.i (a • (Q ∘ₗ S ∘ₗ t)) (⨅ w, isoSp (D.σ w) (lefE n (lam w)))
      fun v => Submodule.smul_mem _ _ (hPF _)
    refine ⟨D.i ∘ₗ (a • (Q ∘ₗ S ∘ₗ t)), fun ψ x => ?_, hf, ?_⟩
    · have h1 := hop k val T hk h hh (t ψ) (S (t ψ)) (hS _) x
      simp only [ht] at h1
      rw [h1, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      rfl
    · have h2 : (a • (Q ∘ₗ S ∘ₗ t)) ∘ₗ D.i = a • (Q * D.R ⟨h, hh⟩ * D.Θ) := by
        refine LinearMap.ext fun u => ?_
        have h3 : t (D.i u) = D.i (D.Θ u) := Subtype.ext (Subtype.ext (funext fun g => by rw [ht, D.hΘ]))
        have h4 : S (D.i (D.Θ u)) = D.R ⟨h, hh⟩ (D.Θ u) := D.inj (Subtype.ext (Subtype.ext (by rw [hS, D.hR])))
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply, h3, h4]
      have h5 : ∀ y ∈ Y, (D.R ⟨h, hh⟩ * D.Θ) y ∈ Y := fun y hy => hYR _ _ (hYΘ y hy)
      have h6 : LinearMap.trace ℂ (Y.map j) (ρ h * e.conj (D.Θ.restrict hYΘ)) = trOn Y (D.R ⟨h, hh⟩ * D.Θ) := by
        rw [hρ h hh, hmul, LinearMap.trace_conj', trOn, dif_pos h5]
        rfl
      rw [← htrL, h2, trOn_smul _ a (Q * D.R ⟨h, hh⟩ * D.Θ) (fun x _ => hPF _), htr, h6, ha]
      ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.OpFormA
section
noncomputable section

open NumberField MeasureTheory Measure
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (G)

namespace UpperTheory.V.Z.GSp4Splitting

section Iter

variable {X Γ U ι : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [AddCommGroup U] [Module ℂ U]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem prod_cs {κ : Type} [Fintype κ] (e : κ → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) :
    Continuous (fun y : κ → X => ∏ v, e v (y v)) ∧ HasCompactSupport (fun y : κ → X => ∏ v, e v (y v)) := by
  refine ⟨continuous_finsetProd _ fun v _ => (he v).1.comp (continuous_apply v), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (he v).2.isCompact) fun y hy => ?_
  obtain ⟨v, hv⟩ := not_forall.1 (mt Set.mem_univ_pi.2 hy)
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

private theorem iter_fin (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (m : ℕ) :
    ∀ (s : Fin m → ι) (u : U) (g : Γ),
      ∫ y : Fin m → X, (∏ i, e (s i) (y i)) * Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod) ∂(Measure.pi fun _ => μ) =
        (∏ i, val (s i)) * Φ ((List.ofFn fun i => P (s i)).prod u) g := by
  induction m with
  | zero =>
    intro s u g
    simp [Measure.pi_of_empty (fun _ : Fin 0 => μ)]
  | succ m ih =>
    intro s u g
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hl : Continuous fun y : Fin (m + 1) → X => (List.ofFn fun i => j (s i) (y i)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => (hj _).comp (continuous_apply i)
    have hF : Integrable (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) (Measure.pi fun _ => μ) :=
      ((prod_cs (fun i => e (s i)) fun i => he _).1.mul ((hΦ u).comp (continuous_const.mul hl))).integrable_of_hasCompactSupport
        (prod_cs (fun i => e (s i)) fun i => he _).2.mul_right
    rw [← (hmp.symm _).integral_comp']
    refine (integral_prod _ (((hmp.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF)).trans ?_
    have hin : ∀ t : X, ∫ z : Fin m → X, (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm (t, z))
          ∂(Measure.pi fun _ => μ) = (∏ i : Fin m, val (s i.succ)) *
            (e (s 0) t * Φ ((List.ofFn fun i : Fin m => P (s i.succ)).prod u) (g * j (s 0) t)) := by
      intro t
      have e1 : ∀ z : Fin m → X, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0).symm (t, z) = Fin.cons t z :=
        fun z => Fin.insertNth_zero' t z
      simp only [e1, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
      simp only [← mul_assoc g, mul_assoc (e (s 0) t)]
      rw [integral_const_mul, ih (fun i => s i.succ) u (g * j (s 0) t)]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall hin)).trans ?_
    rw [integral_const_mul, hloc, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    ring

private theorem iter_list [Fintype ι] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (l : List ι) (hl : l.Nodup) (hm : ∀ v, v ∈ l)
    (u : U) (g : Γ) :
    ∫ y : ι → X, (∏ v, e v (y v)) * Φ u (g * (l.map fun v => j v (y v)).prod) ∂(Measure.pi fun _ => μ) =
      (∏ v, val v) * Φ ((l.map P).prod u) g := by
  classical
  let σ : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l hl hm
  have hσ : ∀ {β : Type} (f : ι → β), (List.ofFn fun i => f (σ i)) = l.map f := fun f => by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) σ
  have key := iter_fin μ e he j hj Φ hΦ val P hloc _ σ u g
  rw [hσ P, Equiv.prod_comp σ val] at key
  rw [← key, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ∀ i, MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ y (σ i) = y i := fun i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ y i
  beta_reduce
  rw [← hσ, ← Equiv.prod_comp σ]
  simp only [e1]

end Iter

private theorem prod_single {ι M : Type} [DecidableEq ι] [Monoid M] (y : ι → M) :
    ∀ l : List ι, l.Nodup → ∀ w, (l.map fun v => (Pi.mulSingle v (y v) : ι → M)).prod w = if w ∈ l then y w else 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hl w
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.2]
    by_cases h : w = a
    · subst h
      simp [hl.1]
    · simp [h]

private theorem split_two {X Y K : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (e : X × Y ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ]
    (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = c * ∫ x, ∫ y, f (e (x, y)) ∂mY ∂mX := by
  let em : X × Y ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  haveI : IsHaarMeasure ((mX.prod mY).map e) := ContinuousMulEquiv.isHaarMeasure_map _ e
  haveI : LocallyCompactSpace K := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology K := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  have h := isMulLeftInvariant_eq_smul μ ((mX.prod mY).map e)
  have hpos := haarScalarFactor_pos_of_isHaarMeasure μ ((mX.prod mY).map e)
  generalize haarScalarFactor μ ((mX.prod mY).map e) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun f hf hs => ?_⟩
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine (integral_map_equiv em f).trans ?_
  exact integral_prod (fun z => f (e z))
    ((hf.comp e.continuous).integrable_of_hasCompactSupport (hs.comp_homeomorph e.toHomeomorph))

private theorem hecke_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : Γ → ℂ) (hh : ∀ k ∈ K, ∀ g, h (g * k) = h g) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (fun x => g⁻¹ * x) ⁻¹' (K : Set Γ) ∈ nhds g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  refine continuousAt_const.congr (f := fun _ => h g) (Filter.mem_of_superset hn fun x hx => ?_)
  have := hh _ hx g
  simpa using this.symm


open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG in
private def split0 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* PositivityTheory.Rg.BcB.E.H E n 0 where
  toFun p := (splitGA n p, 1)
  invFun g := (splitGA n).symm g.1
  left_inv p := by simp
  right_inv g := Prod.ext (by simp) (Subsingleton.elim _ _)
  map_mul' p q := by simp
  continuous_toFun := (splitGA n).continuous.prodMk continuous_const
  continuous_invFun := (splitGA n).symm.continuous.comp continuous_fst

end UpperTheory.V.Z.GSp4Splitting

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH PositivityTheory.Rg.BcB.CG.lc_G PositivityTheory.Rg.BcB.CG.sc_G PositivityTheory.Rg.BcB.CG.lc_GLf
  PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles PositivityTheory.Rg.BcB.CG.borelSpaceH in
open PositivityTheory.Rg.BcB.CG in
theorem UpperTheory.V.Z.Mult.Pi.opFormA :
    LocAct → UpperTheory.V.Z.Mult.Pi.OpFormA := by
  intro hL E _ _ _ n _ _ μC _ _ _ μf _ μ _
  classical
  haveI : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μC) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := split_two (split0 E n) μ (Measure.pi fun _ : InfinitePlace E => μC) μf
  refine ⟨c, hc0, fun hn π hθ K hKo hKc hKθ D lam hch _ _ ν _ hν P hP k val T hk h hh ψ u hu x => ?_⟩
  set e : InfinitePlace E → G n → ℂ := fun w => phiOf (lefE n (lam w)) (lefT n (lam w)) (k w) with he
  have hecs : ∀ w, Continuous (e w) ∧ HasCompactSupport (e w) := fun w =>
    PositivityTheory.Rg.BcB.F.F0.phiOf_cs μC _ _ _ _ _ (hk w)
  have hhc : Continuous h := hecke_cont K hKo h fun k hk g => by simpa using hh.2 1 K.one_mem k hk g
  have hcont : ∀ φ : π.V, Continuous φ.1.1 := fun φ => DiscreteGroups.T1.G.continuous_of_mem π φ.2
  have hphi : ∀ p : (InfinitePlace E → G n) × GL (Fin n) (Af E), phiProd lam k h (split0 E n p) = (∏ w, e w (p.1 w)) * h p.2 := by
    intro p
    have e1 : ∀ w, infAt E n w (split0 E n p).1 = p.1 w := fun w => gInf_splitGA n p w
    have e2 : finOf E n (split0 E n p).1 = p.2 := gFin_splitGA n p
    simp only [phiProd, e1, e2, he]
  have hphi' : phiProd lam k h = (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2) ∘
      (split0 E n).symm.toHomeomorph := by
    funext y
    obtain ⟨p, rfl⟩ := (split0 E n).surjective y
    rw [hphi]
    exact (congrArg (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2)
      ((split0 E n).symm_apply_apply p)).symm
  have hpc : Continuous (phiProd lam k h) := by
    rw [hphi']
    exact (((prod_cs e hecs).1.comp continuous_fst).mul (hhc.comp continuous_snd)).comp (Homeomorph.continuous _)
  have hps : HasCompactSupport (phiProd lam k h) := by
    rw [hphi']
    refine HasCompactSupport.comp_homeomorph ?_ _
    refine HasCompactSupport.intro ((prod_cs e hecs).2.isCompact.prod hh.1.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h1 | h1
    · rw [show (∏ w, e w (p.1 w)) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun y : InfinitePlace E → G n => ∏ v, e v (y v)) h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  rw [hc (fun y => phiProd lam k h y * ψ.1.1 (x * y.1))
    (hpc.mul ((hcont ψ).comp (continuous_const.mul continuous_fst))) hps.mul_right, mul_assoc]
  congr 1
  let j : InfinitePlace E → G n → GA E n := fun w t => infP n (Pi.mulSingle w t)
  let l := (Finset.univ : Finset (InfinitePlace E)).toList
  let ih : (InfinitePlace E → G n) →* GA E n := MonoidHom.mk' (infP n) (infinitePart_mul n)
  have hjl : ∀ y : InfinitePlace E → G n, (l.map fun v => j v (y v)).prod = infP n y := by
    intro y
    have e1 : (l.map fun v => (Pi.mulSingle v (y v) : InfinitePlace E → G n)).prod = y := by
      funext w
      rw [prod_single y l (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (map_list_prod ih _).symm
    rw [List.map_map]
    rfl
  have hj : ∀ w, Continuous (j w) := fun w => (continuous_infP n).comp (continuous_mulSingle (A := fun _ => G n) w)
  have key := iter_list μC e hecs j hj (fun u => (D.i u).1.1) (fun u => hcont _) (fun w => val w (infOf (lam w))) P
    (fun w u g => by
      have := hL E n hn π hθ K hKo hKc hKθ μf D w (lam w) (hch w) ν hν μC _ _ (P w) (hP w) (k w) (val w) (T w) (hk w) u g
      simp only [along_val] at this
      exact this) l (Finset.nodup_toList _) (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) u x
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hjl, hu, heckeOp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [hphi, mul_assoc, mul_assoc x]
  rfl
end
end

