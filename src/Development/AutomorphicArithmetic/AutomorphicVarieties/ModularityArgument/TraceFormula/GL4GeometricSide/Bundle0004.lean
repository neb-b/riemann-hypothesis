module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.SumRefine
section
noncomputable section

open NumberField Matrix Finset
open GlobalTheory.CuspRep
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Avg

variable {K M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]

private theorem exists_avg [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (ρ : K →* Module.End ℂ M)
    (hs : ∀ m, IsOpen {k | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ m k, ρ k (P m) = P m) ∧ (∀ m, (∀ k, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ k m, T (ρ k m) = ρ k (T m)) → ∀ m, T (P m) = P (T m) :=
  _root_.UpperTheory.Reformulated.B.ExistsAverage.exists_avg ρ hs

end Avg

section Core

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem fin_op (π : CuspSub E n) (g k : GL (Fin n) (Af E)) (x : π.V) :
    π.finPart g (π.op (.fin k) x) = π.finPart (g * k) x :=
  Subtype.ext (by
    show finRep E n g (finRep E n k x.1) = finRep E n (g * k) x.1
    rw [map_mul, Module.End.mul_apply])

private theorem lie_fin (π : CuspSub E n) (X : Lie E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.lie X) (π.finPart g x) = π.finPart g (π.op (.lie X) x) :=
  Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) x.1)

private theorem cpt_fin (π : CuspSub E n) (c : Kinf E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.cpt c) (π.finPart g x) = π.finPart g (π.op (.cpt c) x) :=
  Subtype.ext (by
    have h := congrArg (rt E n) (infGL_comm (Unitary.toUnits c) g)
    rw [map_mul, map_mul] at h
    exact LinearMap.congr_fun h x.1)

private theorem eop_fin (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) (g : GL (Fin n) (Af E)) (x : π.V) :
    PositivityTheory.S2.Clozel.EopV π τ i j (π.finPart g x) = π.finPart g (PositivityTheory.S2.Clozel.EopV π τ i j x) := by
  simp only [PositivityTheory.S2.Clozel.EopV, LinearMap.smul_apply, LinearMap.sub_apply, lie_fin, map_smul, map_sub]

private theorem core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    (v0 ψ : π.V) (hv0 : v0 ≠ 0) (hfix : ∀ k ∈ K, π.finPart k v0 = v0) (hψ : ψ ≠ 0) :
    ∃ v : π.V, v ≠ 0 ∧ (∀ k ∈ K, π.finPart k v = v) ∧ ∀ (T : Module.End ℂ π.V) (c : ℂ),
      (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → T ψ = c • ψ → T v = c • v := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let ρ : K →* Module.End ℂ π.V := MonoidHom.comp π.finPart K.subtype
  have hρ : ∀ (k : K) m, ρ k m = π.finPart k.1 m := fun _ _ => rfl
  have hs : ∀ m, IsOpen {k : K | ρ k m = m} := fun m => by
    have h1 := (π.cusp m.1 m.2).1.level
    convert h1.preimage continuous_subtype_val using 1
    ext k
    exact Subtype.ext_iff
  obtain ⟨P, hPinv, hPfix, hPT⟩ := exists_avg ρ hs
  have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) →
      ∀ m, T (P m) = P (T m) := fun T hT => hPT T fun k m => hT k.1 m
  let W0 : Submodule ℂ π.V := ⨅ g, LinearMap.ker (P ∘ₗ π.finPart g)
  have mem : ∀ x, x ∈ W0 ↔ ∀ g, P (π.finPart g x) = 0 := fun x => by
    simp [W0, Submodule.mem_iInf]
  have stable : _root_.GlobalTheory.CuspRep.IsStable (W0.map π.V.subtype) := by
    rintro o _ ⟨x, hx, rfl⟩
    refine ⟨π.op o x, ?_, rfl⟩
    have hx' := (mem x).1 hx
    refine (mem _).2 fun g => ?_
    cases o with
    | fin k => rw [fin_op]; exact hx' _
    | cpt c => rw [← cpt_fin, ← hcomm _ (fun g x => cpt_fin π c g x), hx', map_zero]
    | lie X => rw [← lie_fin, ← hcomm _ (fun g x => lie_fin π X g x), hx', map_zero]
  rcases π.irred _ (Submodule.map_subtype_le _ _) stable with h | h
  · have hn : ψ ∉ W0 := fun hm => by
      have h1 : ψ.1 ∈ W0.map π.V.subtype := ⟨ψ, hm, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      exact hψ (Subtype.ext h1)
    rw [mem] at hn
    push_neg at hn
    obtain ⟨g, hg⟩ := hn
    refine ⟨P (π.finPart g ψ), hg, fun k hk => hPinv _ ⟨k, hk⟩, fun T c hT hc => ?_⟩
    rw [hcomm T hT, hT, hc, map_smul, map_smul]
  · exfalso
    have h1 : v0.1 ∈ W0.map π.V.subtype := by
      rw [h]
      exact v0.2
    obtain ⟨y, hy, e⟩ := h1
    have hy0 : y = v0 := Subtype.ext e
    subst hy0
    have h2 := (mem y).1 hy 1
    rw [map_one, Module.End.one_apply, hPfix y fun k => hfix k.1 k.2] at h2
    exact hv0 h2

end Core

theorem rlLow : HeckeMem → LowType → RlLow := by
  intro _ hL
  unfold RlLow ForRl
  intro E _ _ _ n hn π _ K _ hKc _ _ _ μf _ D hreg hnt w lam hanti hch
  obtain ⟨ν, ψ, hψ, hψ0, hk, hc⟩ := hL E n hn π hreg w lam hanti hch
  obtain ⟨u0, hu0⟩ := exists_ne (0 : D.U)
  have hv0 : D.i u0 ≠ 0 := fun e => hu0 (D.inj (by rw [e, map_zero]))
  have hfix0 : ∀ k ∈ K, π.finPart k (D.i u0) = D.i u0 := fun k hk' =>
    Subtype.ext ((D.rng (D.i u0)).1 ⟨u0, rfl⟩ k hk')
  let ψ' : π.V := ⟨ψ, hψ⟩
  have hψ' : ψ' ≠ 0 := fun e => hψ0 (congrArg Subtype.val e)
  obtain ⟨v, hv, hfix, hT⟩ := core π K hKc (D.i u0) ψ' hv0 hfix0 hψ'
  obtain ⟨u, hu⟩ := (D.rng v).2 fun k hk' => congrArg Subtype.val (hfix k hk')
  have hune : u ≠ 0 := fun e => hv (by rw [← hu, e, map_zero])
  let T : Fin n → Fin n → Module.End ℂ π.V := fun a b =>
    PositivityTheory.S2.Clozel.EopV π w.embedding a b - PositivityTheory.S2.Clozel.EopV π (ComplexEmbedding.conjugate w.embedding) b a
  have hTval : ∀ a b (x : π.V), (T a b x).1 = eopW w true a b x.1 - eopW w false b a x.1 := fun a b x => by
    simp [T, eopW, GlobalTheory.CompanionTheory.ClozelPurity.EopV_val]
  have hTc : ∀ a b g (x : π.V), T a b (π.finPart g x) = π.finPart g (T a b x) := fun a b g x => by
    simp only [T, LinearMap.sub_apply, eop_fin, map_sub]
  have hTu : ∀ a b, D.i (kF (D.E1 w) (D.E2 w) a b u) = T a b v := fun a b => Subtype.ext (by
    rw [hTval, ← hu]
    simp only [kF, LinearMap.add_apply, map_add (f := _), Submodule.coe_add, D.hE1, D.hE2]
    abel)
  have hmem : u ∈ hwSp (D.E1 w) (D.E2 w) ν := by
    refine ⟨fun a => D.inj ?_, fun a b hab he => D.inj ?_⟩
    · have h1 : T a a ψ' = (ν a : ℂ) • ψ' := Subtype.ext (by
        rw [hTval]
        exact hk.1 a)
      rw [hTu, hT _ _ (hTc a a) h1, map_smul, hu]
    · have h1 : T a b ψ' = (0 : ℂ) • ψ' := Subtype.ext (by
        rw [hTval, zero_smul]
        exact hk.2 a b hab he)
      rw [hTu, hT _ _ (hTc a b) h1, zero_smul, map_zero]
  exact ⟨ν, fun e => hune (by
    have h1 := hmem
    rw [e, Submodule.mem_bot] at h1
    exact h1), hc⟩

end UpperTheory.V.Z.GSp4Splitting
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ThetaFixedGlobalCharacter
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
theorem UpperTheory.V.Z.GSp4Splitting.exists_global_hecke_theta_lift :
    AvgEx → AbsGlob → LowIso → HeckeMem → RlEx → RlPair → RlChar → RlK → RlTheta → RlComm → RlHecke → RlSimple → RlFin → RlLow → OpForm → ThetaFixedGlobalCharacter := by
  intro hAvg hAbs hLow hM hEx hPair hChar hK hTh hComm hHk hSim hFin hRL hOp
  intro E _ _ _ n hn π hreg hθ lam hlam hch K hKo hKc hKθ hfix _ _ μC _ _ _ μf _ μ _
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
  replace hOp := hOp E n hn π hθ K hKo hKc hKθ μf D lam hch
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
  obtain ⟨c₂, hc₂, hop⟩ := hOp ν hν μC μ P hP
  let j : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hj : Function.Injective j := Subtype.val_injective.comp D.inj
  let e : Y ≃ₗ[ℂ] Y.map j := Submodule.equivMapOfInjective j hj Y
  have he : ∀ y : Y, ((e y : Y.map j) : Sm E n) = (D.i y).1 := fun _ => rfl
  let ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ (Y.map j) := fun h =>
    if hh : IsHeckeF K h then e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) else 0
  have hρ : ∀ h (hh : IsHeckeF K h), ρ h = e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) := fun h hh => dif_pos hh
  have hmul : ∀ f g : Module.End ℂ Y, e.conj f * e.conj g = e.conj (f * g) := fun f g => (e.conj_comp g f).symm
  refine ⟨Y.map j, ρ, e.conj (D.Θ.restrict hYΘ), c₂ * c₁, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_,
    mul_ne_zero hc₂ hc₁, ?_⟩
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
      rw [show y = 0 from Subtype.ext this, e.map_zero]
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

