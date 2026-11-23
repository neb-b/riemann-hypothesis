module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterRunWithLawsAndPinsAtSpecialPrime
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.RunOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val_eq (D : D7) (y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ((cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  have h : D.conjF = D.sp.cm.sig :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin sigR
  rw [h]
  rfl

theorem xi_det_of_isDetRoot {D : D7} {xi de : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (h : XiTilde xi de)
    (V : Formalism.BasicNotions.TH.HSp D) (g : Formalism.L2.Theta.GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.IsDetRoot V g x) :
    xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom V g)) =
      de (Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x) := by
  rw [← GlobalTheory.AntiCycRead.quo_of_isDetRoot D V g x hx, ← h]
  congr 1
  apply GlobalTheory.AntiCycRead.quo_eq_of
  have e : (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) =
      ((Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := rfl
  rw [e, ← cjFin_val_eq, ← Units.val_mul, div_mul_cancel]

theorem exists_run_pins : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ hC l hl

  obtain ⟨δ, hδdef⟩ : ∃ δ : Formalism.L2.Host.HChar D.host.E, δ = if l = D.host.pde then (R2 p).C.del else (R2 p).C.del' :=
    ⟨_, rfl⟩
  have hδ : Formalism.L2.Host.IsDelta (H := D.host) l δ := by
    rcases hl with rfl | rfl
    · rw [hδdef, if_pos rfl]; exact (R2 p).C.isDel
    · rw [hδdef, if_neg D.host.pde_ne.symm]; exact (R2 p).C.isDel'
  have hδv : ∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D := by
    intro x
    by_cases h : l = D.host.pde
    · rw [hδdef, if_pos h]; exact hC.delVal x
    · rw [hδdef, if_neg h]; exact hC.delVal' x
  obtain ⟨χ, de, hχ, hd, hfin⟩ := GlobalTheory.TameFinitePart.exists_xiRec D l δ hl hδ hδv
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D l := by
    rcases hl with rfl | rfl
    exacts [hC.field₁, hC.field₂]

  obtain ⟨Pk, hPk⟩ := hC.oneHalf
  obtain ⟨P, hP, hPv⟩ : ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((l : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ PP ∈ placesOver (R2 p) ((R2 p).mu v) (ownAt D v),
        P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
    by_cases hex : ∃ v ∈ (R2 p).twPl, ownAt D v = l
    · obtain ⟨v, hv, hvl⟩ := hex
      refine ⟨Pk l, by rw [← hvl]; exact (hPk v hv).1, fun w hw hwl PP hPP => ?_⟩
      have := (hPk w hw).2 PP hPP
      rwa [hwl] at this
    · have hlp : l.Prime := by
        rcases hl with rfl | rfl
        exacts [D.host.pde_prime, D.host.pde'_prime]
      obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hlp
      exact ⟨P, hP, fun w hw hwl => absurd ⟨w, hw, hwl⟩ hex⟩

  have hJ : LawsJ p.T := (fw2 p).laws
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D p.T.toCore hC.laws hC.rank hF.kpsi
  have hcan : T.Q.Canon := by
    have e : T.toCore.Q = p.T.toCore.Q := congrArg (fun C => C.Q) hTc
    rw [show T.Q = p.T.Q from e]
    exact hC.canon
  obtain ⟨dd, TF, hTF, -, hJ', hxi, hh, hcov⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiRec D p.T T hJ hT hTc hcan l hF P hP de hd
  obtain ⟨r, rfl⟩ : ∃ r : GlobalTheory.RealIndexBound.RunData p.T, r.full = TF := by
    rw [← hJ']
    exact ⟨GlobalTheory.RealIndexBound.RunData.of TF, rfl⟩
  have hInR : ∀ i : Fin D.R.m, InR D ((i : ℕ) + 1) := fun i => ⟨Nat.le_add_left _ _, i.2⟩
  refine ⟨r, hTF, fun i => (hcov _ (hInR i)).1, fun j n hj => (hcov j hj).2 n, ?_, ?_⟩
  · intro i γ₀ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.2.1 γ₀ hγ
    rw [xi_det_of_isDetRoot hxi _ _ _ hx]
    exact hd.rat _ x rfl
  · intro v hv hvl i
    letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hvl]
      exact (hcov _ (hInR i)).2 _
    · intro PP hPP
      rw [hh]
      exact hPv v hv hvl PP hPP
    · have hδv' : (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = δ := by
        unfold ownAt at hvl
        unfold Formalism.L2.Host.CharFrame.delAt
        by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
        · rw [if_pos h] at hvl ⊢
          rw [hδdef, ← hvl, if_neg D.host.pde_ne.symm]
        · rw [if_neg h] at hvl ⊢
          rw [hδdef, ← hvl, if_pos rfl]
      refine ⟨χ, hδv' ▸ hχ, fun g x hx => ?_⟩
      rw [xi_det_of_isDetRoot hxi _ _ _ hx]
      exact hfin x _ rfl

end GlobalTheory.RunOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleClassesRationalLiftFormsLevel
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameOf

theorem finite_classes_of_pres {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) :
    ∃ T : Finset G, ∀ g, ∃ γ ∈ ι.range, ∃ s ∈ T, ∃ κ ∈ presJ P, g = γ * s * κ := by
  classical
  have hf : (Set.range P.y).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun g => ?_⟩
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := P.reps g
  exact ⟨ι γ, ⟨γ, rfl⟩, P.y c, hf.mem_toFinset.2 ⟨c, rfl⟩, k, k.2, e⟩

theorem classesAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T),
    ClassesAt p j t := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t
  exact finite_classes_of_pres (p.R.B.L j t).pres

end GlobalTheory.FrameOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfRangeAddInfKer
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadOnRec

theorem finrank_inf_range_add_inf_ker {K M : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (e : M →ₗ[K] M) (he : ∀ x, e (e x) = e x) (V : Submodule K M) (hV : ∀ x ∈ V, e x ∈ V) :
    finrank K (V ⊓ LinearMap.range e : Submodule K M) + finrank K (V ⊓ LinearMap.ker e : Submodule K M) = finrank K V := by
  let f : V →ₗ[K] V := e.restrict hV
  have h1 : (LinearMap.range f).map V.subtype = V ⊓ LinearMap.range e := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨hV x x.2, x, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨⟨e z, hy⟩, ⟨⟨e z, hy⟩, Subtype.ext (he z)⟩, rfl⟩
  have h2 : (LinearMap.ker f).map V.subtype = V ⊓ LinearMap.ker e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hk, rfl⟩
  rw [← h1, ← h2, Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  exact LinearMap.finrank_range_add_finrank_ker f

theorem finrank_eq_of_bij {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Bijective f) (p : Submodule K M) (q : Submodule K N) (h : ∀ x, x ∈ p ↔ f x ∈ q) :
    finrank K p = finrank K q := by
  have e : p.map f = q := by
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    constructor
    · rintro ⟨x', hx', e'⟩
      exact hf.1 e' ▸ (h x').1 hx'
    · intro hy
      exact ⟨x, (h x).2 hy, rfl⟩
  rw [← e]
  exact (Submodule.equivMapOfInjective f hf.1 p).finrank_eq

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance runAlgBad {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}

theorem mem_eig_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ F.P0 F.ψ0⁻¹ ph y) (ha : ActionPin h fw ι ℓ)
    (hG : R.IsGrp F) (hinc : F.P0 ≤ inc.range) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ GlobalTheory.OnTies.toForms h fw ι z x ∈ GlobalTheory.CovTop.spType R F ι := by
  have hb := GlobalTheory.OnTies.toForms_bijective h fw ι z
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ ∀ u : O.U, O.ρ i u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ i g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW ι).ρ (inc g) (GlobalTheory.OnTies.toForms h fw ι z x) =
        (((R.FW ι).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • GlobalTheory.OnTies.toForms h fw ι z x :=
    fun g hg => by
      rw [← t.rho_eq_of_actionPin ha, GlobalTheory.OnCoord.chi_eq_one hG ι hg, one_mul, ← t.ψ_eq g hg, ← map_smul, hb.1.eq_iff]
  refine e1.trans ⟨fun hx => ?_, fun hx u => ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := hinc hg
    exact (e2 u hg).1 (hx ⟨u, t.U_eq.ge hg⟩)
  · exact (e2 u (t.U_eq.le u.2)).2 (hx ⟨inc u, t.U_eq.le u.2⟩)

end General

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] runAlgBad

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

end Point

end GlobalTheory.BadOnRec

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedNeBotOfEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.FixedKOneTransport

theorem fixed_ne_bot_of_equiv {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (f : G →* G') (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V')
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' (f g) (e v)) (H : Subgroup G) (H' : Subgroup G')
    (hH : H' ≤ H.map f) (h : GlobalTheory.PRep.fixed ρ H ≠ ⊥) : GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine fun hb => hv0 (e.injective ?_)
  have hmem : e v ∈ GlobalTheory.PRep.fixed ρ' H' := by
    intro h'
    obtain ⟨g, hg, hfg⟩ := hH h'.2
    have hgv : ρ g v = v := by simpa using hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← hfg, ← he, hgv]
  rw [hb] at hmem
  simpa using hmem

open ValuativeRel

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def integerEquiv (i : k ≃+* k') (hi : Continuous i) : 𝒪[k] ≃+* 𝒪[k'] :=
  (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (GlobalTheory.LocalFieldIso.map_integer i hi))

theorem kOne_le_map (i : k ≃+* k') (hi : Continuous i) (n : Type) [Fintype n] [DecidableEq n] :
    GlobalTheory.SplitWeil.KOne k' n ≤ (GlobalTheory.SplitWeil.KOne k n).map (Matrix.GeneralLinearGroup.map i.toRingHom) := by
  rintro _ ⟨a', ha', rfl⟩
  set u := integerEquiv i hi
  let ψ : 𝓀[k'] →+* 𝓀[k] := IsLocalRing.ResidueField.map (u.symm : 𝒪[k'] →+* 𝒪[k])
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.map (u.symm : 𝒪[k'] →+* 𝒪[k]) a'),
    ⟨_, ?_, rfl⟩, ?_⟩
  · simp only [SetLike.mem_coe, MonoidHom.mem_ker] at ha' ⊢
    have h1 : Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])
        (Matrix.GeneralLinearGroup.map (u.symm : 𝒪[k'] →+* 𝒪[k]) a') =
        Matrix.GeneralLinearGroup.map ψ (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k']) a') := by
      ext p q
      simp [ψ]
    rw [h1, ha', map_one]
  · ext p q
    simp only [u]
    exact congrArg Subtype.val ((integerEquiv i hi).apply_symm_apply _)

end GlobalTheory.FixedKOneTransport

theorem GlobalTheory.FixedKOneTransport.fixed_kOne_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'),
    Continuous i → ∀ (x : GlobalTheory.LocGL.IrrGL (k := k)) (x' : GlobalTheory.LocGL.IrrGL (k := k')), GlobalTheory.LocLanglands.RepRel i x x' →
      GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' H hx
  rw [← GlobalTheory.LocLanglands.FieldCompat.cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel _ H
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  refine GlobalTheory.FixedKOneTransport.fixed_ne_bot_of_equiv (Matrix.GeneralLinearGroup.map i.toRingHom) x.rep
    π'.cl.rep.ρ (e.trans φ.toLinearEquiv) (fun g v => ?_) _ _ (GlobalTheory.FixedKOneTransport.kOne_le_map i hi _) hx
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, h2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cjE_cjE (φ : E →+* Formalism.ConjugateSelfDual.Qbar l) : ExpFrame.cj (cj φ) = φ := by
  ext x
  simp only [ExpFrame.cj, RingHom.comp_apply]
  exact congrArg φ (IsCMField.complexConj_apply_apply E x)

theorem isHalf_cj {ι : Type} {inc : ι → (E →+* Formalism.ConjugateSelfDual.Qbar l)} (h : IsHalf inc) : IsHalf fun τ => ExpFrame.cj (inc τ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩
  · have := congrArg ExpFrame.cj hab
    simpa only [cjE_cjE] using this
  · simp only [cjE_cjE] at e
    exact e.symm
  · obtain ⟨τ, hτ | hτ⟩ := h3 i
    · exact ⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩
    · exact ⟨τ, Or.inl hτ⟩

end GlobalTheory.HalfLabels

namespace GlobalTheory.HalfLabels

theorem exists_aut {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K] (ι i : E →+* K) :
    ∃ σ : E ≃ₐ[ℚ] E, i = ι.comp (σ : E →+* E) := by
  let _ : Algebra E K := ι.toAlgebra
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let φ : E →ₐ[ℚ] K := i.toRatAlgHom
  refine ⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩
  ext x
  have h := AlgHom.restrictNormal_commutes φ E x
  exact h.symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isHalf_lab (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf (incOf D e0 false) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι
  have hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := fun τ => rfl
  have hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) =
      ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E) := by
    intro g
    have hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj :=
      map_mul (D.host.gal).symm g (D.R.cc)
    ext x
    rw [hs]
    show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))
    congr 2
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) →
      g = g' := by
    intro g g' h
    have : D.host.sigmaOf g = D.host.sigmaOf g' := AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)
    exact (D.host.gal).symm.injective this
  refine ⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩
  · rw [hinc, hinc] at h
    exact D.eTau.injective (Subtype.ext (hinj _ _ h))
  · rw [hinc, hinc, hcc] at h
    have e := hinj _ _ h
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)
  · obtain ⟨σ, hσ⟩ := exists_aut ι i
    have hσg : D.host.sigmaOf (D.host.gal σ) = σ :=
      (D.host.gal).symm_apply_apply σ
    by_cases hg : D.host.gal σ ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩
      rw [hinc, Equiv.apply_symm_apply, hσ, hσg]
    · have hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi := by
        by_contra h'
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')
      refine ⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩
      rw [hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]

theorem halfAt_all (D : D7) (l : ℕ) : HalfAt D l := by
  intro _ e0 b
  cases b
  · exact isHalf_lab D (l := l) e0
  · exact isHalf_cj (isHalf_lab D e0)

end GlobalTheory.HalfLabels

end
end

