module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.ThetaLiftIndependence.FinalThetaLiftAMFKIndep
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfHyp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColShiftVacEqSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.LastVertexVac
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem colPt_mem_GfC (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (colPt S t g).1 ∈ GfC _ ∧ (colPt S t g).2 ∈ GfC _ := by
  refine ⟨?_, ?_⟩
  · show (1 : GA D _) ∈ GfC _
    exact one_mem _
  · exact (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).2

theorem latMove (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    (hlat : ∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) :
    ∀ u, u ∈ stdLat S (.top t (lastIx D)) ↔ ∃ u₀ ∈ stdLat S (.top t (lastIx D)), u = actO _ _ (colPt S t g).1 (colPt S t g).2 u₀ := by
  intro u
  constructor
  · intro hu
    refine ⟨actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ u, (hlat u).2 hu, ?_⟩
    have := GlobalTheory.WeilVacMove.actO_inv_actO (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ u
    rw [inv_inv, inv_inv] at this
    exact this.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    refine (hlat _).1 ?_
    rw [GlobalTheory.WeilVacMove.actO_inv_actO]
    exact hu₀

theorem om_vac_top (S : GridChoice W U) (t : T) (j : Fin D.R.m)
    (q : GA D (G.V (.top (j : ℕ))) × GA D (G.V (.top ((j : ℕ) + 1)))) (hq1 : q.1 ∈ GfC _) (hq2 : q.2 ∈ GfC _)
    (hΛ : ∀ u, u ∈ stdLat S (.top t (j : ℕ)) ↔ ∃ u₀ ∈ stdLat S (.top t (j : ℕ)), u = actO _ _ q.1 q.2 u₀) :
    ∃ c : ℂ, W.om (.top t (j : ℕ)) q (S.Z.vac (.top t (j : ℕ))) = c • S.Z.vac (.top t (j : ℕ)) := by
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := defPair_top t j
  have hIn : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := inRange_top t j
  have hn := hp.nodes
  have hvac : IsVacO W.ψ W.θ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (W.cart (.top (j : ℕ))) (W.cart (.top ((j : ℕ) + 1)))
      (colLat (S.N.fr (.top (j : ℕ))) : Set _) (colLat (S.N.fr (.top ((j : ℕ) + 1))) : Set _) (S.Z.vac (.top t (j : ℕ))) :=
    S.Z.vac_is _ hp
  have hW : IsWeilDatumO W.ψ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (G.chrS (.top t (j : ℕ))) (G.chrT (.top t (j : ℕ)))
      (W.om (.top t (j : ℕ))) := W.om_is _ hIn
  have hmove : IsVacO W.ψ W.θ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (W.cart (.top (j : ℕ))) (W.cart (.top ((j : ℕ) + 1)))
      (colLat (S.N.fr (.top (j : ℕ))) : Set _) (colLat (S.N.fr (.top ((j : ℕ) + 1))) : Set _)
      (W.om (.top t (j : ℕ)) (q.1, q.2) (S.Z.vac (.top t (j : ℕ)))) :=
    GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ q.1 q.2
      (fun τ => by rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC _ _ _ hq1, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC _ _ _ hq2, Matrix.mul_one, Matrix.one_mul])
      hΛ _ hvac
  have hS1 : (G.V (.top (j : ℕ))).SigOK := hn.1.sigOK G
  have hS2 : (G.V (.top ((j : ℕ) + 1))).SigOK := hn.2.sigOK G
  have hC1 : ∀ τ, IsCartanInv (gramAt D (G.V (.top (j : ℕ))) τ) (W.cart (.top (j : ℕ)) τ) := fun τ => W.cart_is _ hn.1.inRange τ
  have hC2 : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) (W.cart (.top ((j : ℕ) + 1)) τ) :=
    fun τ => W.cart_is _ hn.2.inRange τ
  have hD1 : IsSelfDualC (G.V (.top (j : ℕ))) (colLat (S.N.fr (.top (j : ℕ)))) := S.N.selfDual hn.1
  have hD2 : IsSelfDualC (G.V (.top ((j : ℕ) + 1))) (colLat (S.N.fr (.top ((j : ℕ) + 1)))) := S.N.selfDual hn.2
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 W.θ_is _ _ _ _ hS1 hS2 hC1 hC2 _ _ hD1 hD2 _ _ hvac hmove
  exact ⟨c, hc⟩

theorem colShift_vac_eq_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)),
    (∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) →
    ∃ c : ℂ, colShift S t g (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D)) := by
  intro D T L sc G W U S t g hlat
  obtain ⟨hx, hy⟩ := colPt_mem_GfC S t g
  rw [colShift_eq]
  exact om_vac_top S t (lastIx D) (colPt S t g) hx hy (latMove S t g hlat)

end GlobalTheory.LastVertexVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConclOfDownIntertwines
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.KappaLevels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]


omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ H] in
theorem inner_of_normSq (u : E →ₗ[ℂ] H) (n : ℝ) (h : ∀ x, ‖u x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : E) :
    ⟪u x, u y⟫_ℂ = (n : ℂ) * ⟪x, y⟫_ℂ := by
  have h' : ∀ z, ((‖u z‖ : ℝ) : ℂ) ^ 2 = (n : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 := fun z => by exact_mod_cast h z
  have e1 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (u x) (u y)
  have e2 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) x y
  rw [← map_smul, ← map_add (f := _), ← map_add (f := _), ← map_sub, ← map_sub] at e1
  rw [e1, e2]
  have h1 := h' (x + y)
  have h2 := h' (x - y)
  have h3 := h' (x - (RCLike.I : ℂ) • y)
  have h4 := h' (x + (RCLike.I : ℂ) • y)
  simp only [Complex.coe_algebraMap]
  rw [h1, h2, h3, h4]
  ring

theorem iota_adjoint_transport {E' H' : Type} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (Θ : E →ₗ[ℂ] H) (ι : E' →ₗ[ℂ] H')
    (V : Submodule ℂ E') (uA : E' →ₗ[ℂ] E) (uE : H' →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ x, ‖uE x‖ ^ 2 = n * ‖x‖ ^ 2) (hι : ∀ x ∈ V, uE (ι x) = Θ (uA x)) (y : H')
    (hy : LinearMap.adjoint Θ (uE y) ∈ V.map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ) ∘ₗ LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ))) y = a • y := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨z, hz, hzw⟩ := hy
  have key : ∀ u ∈ V, ⟪u, z⟫_ℂ = ⟪ι u, y⟫_ℂ := fun u hu => by
    apply mul_left_cancel₀ hne
    rw [← inner_of_normSq uA _ nA, ← inner_of_normSq uE _ nE, hzw, hι u hu, LinearMap.adjoint_inner_right]
  have hQ : z ∈ V ⊓ (V ⊓ LinearMap.ker ι)ᗮ := by
    refine ⟨hz, (Submodule.mem_orthogonal _ _).2 fun u hu => ?_⟩
    rw [key u hu.1, LinearMap.mem_ker.1 hu.2, inner_zero_left]
  have hb : LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ)) y = ⟨z, hQ⟩ := by
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, Submodule.coe_inner]
    exact (key u u.2.1).symm
  have hinj : Function.Injective uE := (injective_iff_map_eq_zero uE).2 fun y hy => by
    have := nE y
    rw [hy, norm_zero, zero_pow two_ne_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this.symm).resolve_left hn.ne'))
  apply hinj
  rw [LinearMap.comp_apply, hb, map_smul, ← ha, ← hzw]
  exact hι z hz

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable {R F}

end GlobalTheory.KappaLevels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExIoY

theorem ex_ioY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ioY := by
  intro hDS hHC hCR hCW D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  have hE : R.ex_ItY := _root_.GlobalTheory.Chain.ExItY.ex_ItY_holds hDS hHC D G Pl0 T A Ks R hL hF hM hH hW
  have hI : R.chain_ItY := fun t k hk => (hW.ItY k hk).1 (hE k hk) t
  have hS : GlobalTheory.Chain.StepsOK R :=
    GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hLw : GlobalTheory.Chain.LawsOK R := _root_.GlobalTheory.Chain.SourceLaw.lawsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hY := GlobalTheory.Chain.ioYSt_of_ioPair D G Pl0 T A Ks R (_root_.GlobalTheory.Chain.IoLift.ioPair_onObjects hDS hHC hCR hCW D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ hS hLw hM.νY hM.νY' hI
  exact fun t k hk => hY t k hk

end GlobalTheory.Chain.ExIoY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRangeRestrictEq
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftEquivariance

theorem commutes_adjoint {G E E' : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hρ' : ∀ g x, ‖ρ' g x‖ = ‖x‖)
    (f : E →ₗ[ℂ] E') (hf : Commutes ρ ρ' f) : Commutes ρ' ρ (LinearMap.adjoint f) := by
  intro g y
  have i1 : ∀ u v, inner ℂ (ρ g u) (ρ g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ g) (hρ g)).inner_map_map u v
  have i2 : ∀ u v, inner ℂ (ρ' g u) (ρ' g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ' g) (hρ' g)).inner_map_map u v
  refine ext_inner_left ℂ fun x => ?_
  have e : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e, i1, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, hf g, i2]

section Generic

variable {Γ Gf W G : Type} [Group Γ] [Group Gf] [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem translate_indep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) {F : Gf → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) (κ κ' : l.Q) (hk : ((κ⁻¹ * κ' : l.Q) : Gf) ∈ l.J) (h : Gf) :
    (((l.ch κ')⁻¹ : ℂˣ) : ℂ) • F (h * κ') = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ) := by
  have e := hF 1 (h * κ) ⟨_, hk⟩
  have e1 : ι 1 * (h * κ) * ((κ⁻¹ * κ' : l.Q) : Gf) = h * κ' := by simp [mul_assoc]
  have e2 : l.χ ⟨_, hk⟩ = (l.ch κ)⁻¹ * l.ch κ' := by
    rw [← l.ch_J, ← map_inv, ← map_mul]
  simp only at e
  rw [e1, e2, map_one, Module.End.one_apply] at e
  rw [e, smul_smul, ← Units.val_mul, mul_comm (l.ch κ)⁻¹, inv_mul_cancel_left]

theorem exists_rep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) (M : HMod (Gf → W))
    (hinj : Function.Injective M.e) (hM : ∀ x, M.e x ∈ Bridge.AdForms ι ρ l.J l.χ)
    (hT : ∀ (κ : l.Q) (x : M.H), ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖)
    (red : l.Q →* G) (hs : Function.Surjective red) (hker : ∀ κ, red κ = 1 → (κ : Gf) ∈ l.J) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧
      ∀ κ x h, M.e (π (red κ) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := by
  choose s hs using hs
  choose T hT hn using hT
  have key : ∀ κ x h, M.e (T (s (red κ)) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := fun κ x h => by
    rw [hT, ← Units.val_inv_eq_inv_val]
    exact translate_indep ι ρ l (hM x) κ _ (hker _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])) h
  let L : G → M.H →ₗ[ℂ] M.H := fun g =>
    { toFun := T (s g)
      map_add' := fun x y => hinj (funext fun h => by
        rw [map_add (f := _), Pi.add_apply, hT, hT, hT, map_add (f := _), Pi.add_apply, smul_add])
      map_smul' := fun a x => hinj (funext fun h => by
        rw [map_smul, Pi.smul_apply, hT, hT, map_smul, Pi.smul_apply, smul_comm]; rfl) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g x => hn _ x, key⟩
  · ext x
    refine hinj (funext fun h => ?_)
    have := key 1 x h
    rw [map_one] at this
    exact this.trans (by simp)
  · ext x
    refine hinj (funext fun h => ?_)
    have := key (s g * s g') x h
    rw [map_mul, hs, hs] at this
    refine this.trans ?_
    show _ = M.e (T (s g) (T (s g') x)) h
    rw [hT, hT, smul_smul, map_mul, Subgroup.coe_mul, mul_assoc]
    simp [mul_comm]

end Generic

variable {D : D7}

theorem mem_parLev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) : Formalism.UG.bc (swapAE D) x.1 ∈ parLev D.sp.cm V.gram β L := by
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flagL L) := h
  exact h1.1

theorem mem_J {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) (h1 : rTup β L (Formalism.UG.bc (swapAE D) x.1) = 1) : x ∈ (levEnv V β L).J := by
  have h2 : rTup β L (Formalism.UG.bc (swapAE D) x.1) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := Subgroup.mem_bot.2 h1
  have h3 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flag1L L) := ⟨mem_parLev h, h2⟩
  exact h3

theorem rTup_bc_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x y : Bridge.Gf V}
    (hx : x ∈ (levEnv V β L).Q) (hy : y ∈ (levEnv V β L).Q) :
    rTup β L (Formalism.UG.bc (swapAE D) (x * y).1) =
      rTup β L (Formalism.UG.bc (swapAE D) x.1) * rTup β L (Formalism.UG.bc (swapAE D) y.1) := by
  rw [Subgroup.coe_mul, map_mul]
  exact rTup_mul (mem_parLev hx) (mem_parLev hy)

def redHom (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    (levEnv V β L).Q →* G0 L.Pg L.r :=
  MonoidHom.mk' (fun κ => rTup β L (Formalism.UG.bc (swapAE D) κ.1.1)) fun a b => rTup_bc_mul a.2 b.2

theorem redHom_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : (levEnv V β L).Q}
    {g₀ : G0 L.Pg L.r} : LiftsTo V β L κ g₀ ↔ redHom V β L κ = g₀ := Iff.rfl

theorem exists_transRep (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r) (hs : ∀ g, ∃ κ, LiftsTo V β L κ (eG g)) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧ IsTransRep V β L eG M π := by
  have hred : ∀ κ g, LiftsTo V β L κ (eG g) → (eG.symm.toMonoidHom.comp (redHom V β L)) κ = g := fun κ g h =>
    eG.symm_apply_eq.2 (redHom_eq.1 h)
  have h1 : ∀ x, M.e x ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ :=
    fun x => hM.2.1.le ⟨x, rfl⟩
  have h2 := ClassSumTranslate.translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (ClassSumTranslate.levEnv_normal V β L) (fun q => ClassSumTranslate.norm_levFn V β L _) hy M hM
  have h3 : Function.Surjective (eG.symm.toMonoidHom.comp (redHom V β L)) := fun g => (hs g).imp fun κ h => hred κ g h
  have h4 : ∀ κ, (eG.symm.toMonoidHom.comp (redHom V β L)) κ = 1 → (κ : Bridge.Gf V) ∈ (levEnv V β L).J := fun κ h =>
    mem_J κ.2 (redHom_eq.2 (eG.symm.injective (h.trans (map_one eG.symm).symm)))
  refine (exists_rep (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L) M hM.1 h1 h2 _ h3 h4).imp
    fun π hπ => ⟨hπ.1, fun g x => ⟨hs g, fun κ hκ h => ?_⟩⟩
  exact (congrArg (fun g' => M.e (π g' x) h) (hred κ g hκ)).symm.trans (hπ.2 κ x h)

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_fin_lift (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = x :=
  exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 x

theorem ch_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem exists_adelic_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → W}
    (h : IsTranslate V β L g₀ F F') :
    ∃ κ, IsLevelLift V β L g₀ κ ∧ ∀ x, F' x = (levChi V β (flagL L) κ)⁻¹ • F (x * (finHom V).rangeRestrict κ) := by
  refine h.1.elim fun q hl => (exists_fin_lift V q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have hl1 : rTup β L (Formalism.UG.bc (swapAE D) q.1.1) = g₀ := hl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq q).symm)
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ mem_parLev q.2
  refine ⟨⟨hk.1, hp, (congrArg (rTup β L) e1).trans hl1⟩, fun x => (h.2 q hl x).trans ?_⟩
  exact congrArg₂ (fun (a : ℂ) (z : Bridge.Gf V) => a • F (x * z))
    ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)) hk.2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.LiftEquivariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.AAUnit

theorem aa_unit : ∀ (D : D7) (w : Pl D.host.E), ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
  intro D w h2qd hN
  have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => h2qd (by
    rw [Nat.cast_mul]; exact w.asIdeal.mul_mem_right _ h)
  refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
  · rw [GlobalTheory.FunObj.Good.valued_alg]
    exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
  · rw [GlobalTheory.FunObj.Good.valued_alg]
    exact GlobalTheory.FunObj.Good.valuation_nat hN

end GlobalTheory.AAUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.IdemSubDiff

variable {D : D7} [DecidableEq (Pl D.host.E)]

theorem comp_sum {es : Pl D.host.E → AE D} {S : Finset (Pl D.host.E)}
    (h : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) :
    infPart D (∑ PP ∈ S, es PP) = 0 ∧
      ∀ w, cpt (D := D) w (toEAf D (∑ PP ∈ S, es PP)) = if w ∈ S then 1 else 0 := by
  refine ⟨?_, fun w => ?_⟩
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) (h Q hQ)).1
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum, GlobalTheory.FunObj.Comparison₂.hom_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
      exact (cpt_of_isIdemAt (h w hw)).1
    · exact Finset.sum_eq_zero fun Q hQ => (cpt_of_isIdemAt (h Q hQ)).2 w fun h' => hw (h' ▸ hQ)

theorem isIdemSum_sdiff : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)},
    IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  intro D _ e e₀ P P₀ h h0 hsub
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  obtain ⟨i0, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h0
  obtain ⟨j0, d⟩ := comp_sum hes
  rw [← he] at j0 d
  have hes0 : ∀ PP ∈ P₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP := fun PP hPP => hes PP (hsub hPP)
  obtain ⟨k0, k⟩ := comp_sum hes0
  have he0 : e₀ = ∑ PP ∈ P₀, es PP := by
    refine GlobalTheory.FunObj.ae_ext (by rw [i0, k0]) fun w => ?_
    rw [k w]
    split_ifs with hw
    · exact c1 w hw
    · exact c0 w hw
  have hdiff : e - e₀ = ∑ PP ∈ P \ P₀, es PP := by
    rw [he, he0, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hmul : e * (e - e₀) = e - e₀ := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, d w]
    by_cases hw : w ∈ P
    · rw [if_pos hw, one_mul]
    · have hw0 : w ∉ P₀ := fun h' => hw (hsub h')
      rw [if_neg hw, c0 w hw0, zero_mul, sub_zero]
  have horth : e₀ * (e - e₀) = 0 := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero, RingHom.map_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_zero, d w]
    by_cases hw0 : w ∈ P₀
    · rw [c1 w hw0, if_pos (hsub hw0), sub_self, mul_zero]
    · rw [c0 w hw0, zero_mul]
  refine ⟨⟨⟨es, fun PP hPP => hes PP (Finset.mem_sdiff.1 hPP).1, hdiff⟩, ?_⟩, horth⟩
  have h1 : (e - e₀) * cA D (e - e₀) = ((e - e₀) * cA D (e - e₀)) * (e * cA D e) := by
    conv_lhs => rw [← hmul]
    rw [map_mul]
    ring
  rw [h1, hc, mul_zero]

end GlobalTheory.IdemSubDiff
end
end

