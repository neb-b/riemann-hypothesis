module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSelfDualLatticeFixedFunctionsLine
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatVacLine

theorem vacuum_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hψ hsd θ hθ φ₀ hφSB hφ0 hφ φ hψSB hψ'
  set Λ := latAtV G.V G.W v with hΛ
  set co := G.M.co with hco
  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  classical
  let χ : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E))
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin a × Fin (a + a') → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ Λ, Acts (evFin F v) (co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E))
          ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • f)) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l := AddSubgroup.mem_map.mp hl
    obtain ⟨r, hr, x₀, hx₀⟩ := _root_.GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    have key := _root_.GlobalTheory.LatVac.heis_at_local_identity v co B.ψ h.choose f _ (hAt _ h.choose_spec.1) (hA _ h.choose_spec.1) r hr x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.T.tensorLattice_localDarbouxCoords_bounded G.V G.W v co hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice
  have hsd' := _root_.GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ Λ hAt hsd
  have hfill := _root_.GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hψ x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact _root_.GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) χ φ₀ φ (loc φ₀ hφSB hφ) (loc φ hψSB hψ')
    hφ0 hfill

end GlobalTheory.LatVacLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first | exact @GlobalTheory.HTensSplitPair.hTens_split_pair | exact GlobalTheory.HTensSplitPair.hTens_split_pair | (intros; apply GlobalTheory.HTensSplitPair.hTens_split_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesHolds
section
open Matrix GlobalTheory.HolDS

namespace GlobalTheory.HolDS

theorem holomorphicDiscreteSeries_holds : GlobalTheory.Published.HolomorphicDiscreteSeries := by
  intro n ε lam hHC hHol H _ _ σ hDS
  obtain ⟨hc, hnt, hU, hI, -⟩ := id hDS
  haveI := hc
  haveI := hnt
  obtain ⟨D, E, hK⟩ := _root_.GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds n ε H σ hU hI
  have low := _root_.GlobalTheory.HolDS.lowKSub_kMod n ε H σ D E lam hHC hHol hDS hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun μ S hS => _root_.GlobalTheory.kType_weight_in_cone_over_lowK n ε H σ D E lam hHC hHol hDS hK μ S hS
  · exact fun v hv => _root_.GlobalTheory.HdSmooth.kFinite_smoothVec n ε H σ hU hI v hv
  · intro Z hZ v hv
    let vD : D := ⟨v, low.1 hv⟩
    have hx : vD ∈ (Formalism.MainNotions.S.lowKSub ε lam σ).comap D.subtype := hv
    have h0 : (∑ a, ∑ b, Z a b • E a b vD : D) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : ε a = false ∧ ε b = true
      · rw [low.2.2.2 b a hab.2 hab.1 vD hx, smul_zero]
      · rw [hZ a b hab, zero_smul]
    change GlobalTheory.SmVec.dRepC (Formalism.REAL.Jm ε) σ Z (vD : H) = 0
    rw [_root_.GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum n ε H σ D E hK Z vD,
      h0, Submodule.coe_zero]
  · intro v
    rw [_root_.GlobalTheory.HolDS.raisingSpan_eq_span_words n ε H σ D E hK _ low.1, _root_.GlobalTheory.kfin_span_raising_words_lowK n ε H σ D E lam hHC hHol hDS hK,
      Submodule.map_top, Submodule.range_subtype]
    exact (hK.mem v).symm

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookPlusLeMainTerm
section
noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopBound

theorem idem_apply {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  have h1 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem le_eigenvalue {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T S : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (m l : ℝ)
    (hS : ∀ y, S y = e (T y)) (hee : ∀ y, e (e y) = e y) (hadj : ∀ x, e x = x → ∀ y, ⟪x, e y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hm : ∀ u, m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2) (x : Y) (hx : x ≠ 0) (hl : 0 < l)
    (h : S (LinearMap.adjoint S x) = (l : ℂ) • x) : m ≤ l := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hex : e x = x := by
    refine smul_right_injective Y hl' ?_
    show (l : ℂ) • e x = (l : ℂ) • x
    rw [← map_smul, ← h, hS, hee]
  have h1 : LinearMap.adjoint S x = LinearMap.adjoint T x := ext_inner_right ℂ fun f => by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hS, hadj x hex]
  have h2 : ‖LinearMap.adjoint T x‖ ^ 2 = l * ‖x‖ ^ 2 := by
    have h3 : ⟪LinearMap.adjoint S x, LinearMap.adjoint S x⟫_ℂ = (l : ℂ) * ⟪x, x⟫_ℂ := by
      rw [LinearMap.adjoint_inner_left, h, inner_smul_right]
    rw [h1, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ((‖LinearMap.adjoint T x‖ ^ 2 : ℝ) : ℂ) = ((l * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h3
    exact_mod_cast h4
  have h5 := hm x
  rw [h2] at h5
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem scalar_of_ne_bot {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (U U' : Y →ₗ[ℂ] X)
    (hU : U' = U) (P P' : Submodule ℂ Y) (hP : P' = P) (m m' : ℝ) (hm : m ≤ m')
    (h : P' ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ x ∈ P', T (U' x) = (l : ℂ) • x) ∧ m' ≤ Real.log l) :
    ∃ l : ℝ, Real.exp m ≤ l ∧ ∀ y ∈ P, T (U y) = (l : ℂ) • y := by
  subst hU hP
  by_cases hc : P' = ⊥
  · refine ⟨_, le_rfl, fun y hy => ?_⟩
    have h0 : y = 0 := (Submodule.eq_bot_iff _).1 hc y hy
    rw [h0, map_zero, map_zero, smul_zero]
  · obtain ⟨l, hl, h1, h2⟩ := h hc
    exact ⟨l, (Real.le_log_iff_exp_le hl).1 (hm.trans h2), h1⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


include R in
theorem hookPlus_le_mainTerm (i : Fin D.R.m) : GlobalTheory.LiftLower.hookPlus D i ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm D i (sg0 D A) := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm GlobalTheory.LiftLower.hookPlus GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.aPlAt
  simp only [hl]
  have hp : ∀ n a, (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) := fun n a => by
    have : 0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a := GlobalTheory.Survey.LevelVectorSizeBounds.hookProd_pos _
    exact_mod_cast this
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (lt_of_lt_of_le one_pos (hp _ _)) ?_
  exact le_mul_of_one_le_right (zero_le_one.trans (hp _ _)) (hp _ _)

end GlobalTheory.LowTopBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLaw
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertRhoLaw

theorem darboux_rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w w' : W) (Φ : (κ → R) → ℂ) :
    d.rho ψ w (d.rho ψ w' Φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2

theorem darboux_rho_zero {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (Φ : (κ → R) → ℂ) :
    d.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem eq_of_tens_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r 0 ≠ 0) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (0 + z) = r 0 := hr 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.InertRhoLaw

namespace GlobalTheory.InertRhoLaw

theorem rho_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hEq, -, -, -, -, -⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hA : ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)),
      G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R) =
        tens (evFin F v) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R :=
    fun x m => hρ x m R (hR _ m.2)
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (Submodule.zero_mem _)).1
  refine ⟨?_, fun x y => ?_⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    rw [← hA 0 m, map_zero, darboux_rho_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    have e1 := hA x (ρ y m)
    have e2 := hA y m
    have e3 := hA (x + y) m
    have hl := darboux_rho_rho G.M'.co B.ψ (κ x) (κ y) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)
    rw [e2, e1, ← map_add (f := _), e3] at hl
    dsimp only [cA, incM] at hl
    rw [← hEq x y] at hl
    rw [Module.End.mul_apply, hl, LinearMap.smul_apply, Submodule.coe_smul]
    funext z
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.InertRhoLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecompositionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.InertTwoFac.twoFac | exact GlobalTheory.InertTwoFac.twoFac | (intros; apply GlobalTheory.InertTwoFac.twoFac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplecticStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | exact GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | (intros; apply GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridgeVac

theorem acts_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => by
    simpa only [hz, Pi.smul_apply, Pi.zero_apply] using
      GlobalTheory.LatVac.at_liftV v (y i - evFin F v (x₀ i)) u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem evFin_half_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
    have h1 : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
      have := congrArg (evFin F v) (invOf_mul_self (2 : AF F))
      rwa [map_mul, map_ofNat, map_one] at this
    have h2 : algebraMap F (Fv F v) (2 : F)⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    have h20 : (2 : Fv F v) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    exact mul_right_cancel₀ h20 (h1.trans h2.symm)
  rw [e]
  exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v h

theorem vac_locVac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hLat, _⟩ := hC
  obtain ⟨hSB, hne, θ, _, hfix⟩ := hTr.geo.hM'.vac v
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hTr.base.inert v w hin).1
  have hb := evFin_half_mem v h2
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v (G.M'.vac v) hSB
  refine ⟨⟨G.M'.vac v, hSB⟩, rfl, fun h => hne (congrArg Subtype.val h), fun u hu => ?_⟩
  have hγ : κ u ∈ latAtV G.V' G.W v := (hLat u).1 hu
  have hone := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v θ
    (⅟(2 : AF F)) hb (κ u) hγ (κ u) hγ
  have h1 := hfix (κ u) hγ
  rw [hone, one_smul] at h1
  apply Subtype.ext
  exact acts_eq v hr hx₀ _ _ _ (hρ u ⟨G.M'.vac v, hSB⟩) h1

end GlobalTheory.InertBridgeVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtendsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_injective_extends : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  first | exact @GlobalTheory.EvInj.ei_injective | exact GlobalTheory.EvInj.ei_injective | (intros; apply GlobalTheory.EvInj.ei_injective <;> assumption)
end

