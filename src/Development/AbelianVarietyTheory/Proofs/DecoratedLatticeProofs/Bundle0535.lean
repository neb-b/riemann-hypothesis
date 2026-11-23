module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.FamInhab

open GlobalTheory.Fam.Inhab

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem cp_iff (t : T) (j : ℕ) (F : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) : F ∈ CP R P t j ↔ F ∈ R.CC t j ∧
    ∀ (p : P.H) κ, IsLevelLift (Yc D j) (R.βY j) (R.datYt t j R.triv) p.1 κ → ∀ w g,
      (levChi _ (R.βY j) (flagL (R.datYt t j R.triv)) κ)⁻¹ * F w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F w g :=
  GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff D R.θ (Yc D j) _ (R.MY j) (R.βY j) (R.datYt t j R.triv) P F

theorem cxp_iff (t : T) (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : F ∈ CXP R P t ↔
    F ∈ MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)) ∧
    ∀ (p : P.H) κ, IsLevelLift D.sp.X' R.βX (R.datXt t) p.1 κ → ∀ w g,
      (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ * F w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F w g :=
  GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff D R.θ D.sp.X' _ R.MX R.βX (R.datXt t) P F

theorem ioY_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (k : ℕ)
    (hk : k + 1 < D.R.m) (F : R.CC t (k + 1)) (hF : F.1 ∈ CP R P t (k + 1)) : (R.ioY t k F).1 ∈ CP R P t k := by
  have hk' : k < D.R.m := by omega
  refine (cp_iff P t k _).2 ⟨(R.ioY t k F).2, fun p κ hκ w g => ?_⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t (k + 1) hk p.1
  exact step_eigen (L := R.datYt t k R.triv) (L' := R.datYt t (k + 1) R.triv) (io := R.ioY t k) (It := R.ItY k) hm.inf hCR
    (hc.ωY t k hk) (hc.ptY t k hk) rfl (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t k hk') (hc.ItY t k hk).ne
    (fun U w => (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ U.2 w).1) (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t (k + 1) hk)
    (hc.ioY t k (by omega)) hκ hκ' (GlobalTheory.StepVecLaw.stepVec_lifts R hl hm.inf hc.ωY hc.vY t k hk p.1 κ κ' hκ hκ') F
    (((cp_iff P t (k + 1) _).1 hF).2 p κ' hκ') w g

theorem pred_lt : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega

theorem lifts_top (hl : R.toLevCh.Is A.μ0) (t : T) : LiftsExist D.sp.X' R.βX (R.datXt t) := by
  obtain ⟨c, hβ⟩ := hl.βX
  exact _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hβ (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1 (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2

theorem ioX_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) : (R.ioX t F).1 ∈ CP R P t (D.R.m - 1) := by
  refine (cp_iff P t _ _).2 ⟨(R.ioX t F).2, fun p κ hκ w g => ?_⟩
  refine (lifts_top hl t p.1).elim fun κ' hκ' => ?_
  have h1 : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) := ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have h2 := GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hm.HX t).2.1
  have h3 := ((cxp_iff P t _).1 hF).2 p κ' hκ'
  have h4 := GlobalTheory.StepLaw.last_step_law R hl hm.inf hc.ωX hc.vX t p.1 κ κ' hκ hκ'
  exact step_eigen (L := R.datYt t (D.R.m - 1) R.triv) (L' := R.datXt t) (io := R.ioX t) (It := R.ItX) hm.inf hCR
    (hc.ωX t) (hc.ptX t) rfl (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t _ pred_lt) (hc.ItX t).ne h2 h1
    (hc.ioX t) hκ hκ' h4 F h3 w g

include R in
theorem finite_H : Finite P.H := by
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  infer_instance

theorem rankY {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := GlobalTheory.Chain.StepVac.rank_Yc hj

theorem sd {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ :=
  ⟨GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h, h.elim fun _ hc => hc.1⟩

theorem vec_lev (hl : R.toLevCh.Is A.μ0) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} {sT : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) sT (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) χ (R.Q t) (R.xiR t) f₀ f) :
    ∃ f', IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) sT (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) χ (R.Q t) (R.xiR t) f₀ f' :=
  GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ _ _ _ _ _ _ _ _ _ _ _ _ (sd (hl.βY k hk)).1 (sd hβ).1 (sd (hl.βY k hk)).2 (sd hβ).2
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 (hf.2.imp fun _ h => h.1) f₀ hf.1

def vXT (R : RealDat D A Ks) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : WO (Yc D (j + 1)) D.sp.X' → ℂ :=
  Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) (idx_top h)

def itXT (R : RealDat D A Ks) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    PolF D D.sp.X'.rank (Yc D (j + 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (j + 1)) :=
  Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX (idx_top h)

theorem top_weil (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).2 (omT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO R.ψ (Yc D n) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') (R.ωX t) e) := by
    intro n e; subst e; exact hc.ωX t
  rw [show j + 1 + 1 = D.R.m from h]
  exact key _ (idx_top h)

theorem top_vec (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) (vXT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX (R.βY n) R.βX
      (R.datYt t n R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) R.vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) e) := by
    intro n e; subst e; exact hc.vX t
  exact key _ (idx_top h)

theorem top_io (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (omT R t j h)) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1)))
      (cart R.MX) (onb (R.MY (j + 1))) (onb R.MX) (vXT R t j h)) (itXT R j h) _ _ (ioXT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), Lift.IsIo (R.νX t) (R.fdX t)
      (thetaKO (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') (R.ωX t) e))
      (pureTensorO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (onb (R.MY n)) (onb R.MX)
        (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) e))
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e) _ _
      (Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) (R.ioX t) e) := by
    intro n e; subst e; exact hc.ioX t
  exact key _ (idx_top h)

theorem top_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) :
    (ioXT R t j h F).1 ∈ CP R P t (j + 1) := by
  have key : ∀ n (e : D.R.m - 1 = n), ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
      (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1 ∈ CP R P t n := by
    intro n e; subst e; exact ioX_mem P hCR hl hm hc t F hF
  exact key _ (idx_top h)

theorem rank_top {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : D.sp.X'.rank = D.R.r + (j + 1 + 1) * D.R.t := by
  rw [show j + 1 + 1 = D.R.m from h]; exact D.sp.X'_rank

def restr {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {A A' : Submodule ℂ X} {B B' : Submodule ℂ Y}
    (f : A' →ₗ[ℂ] B') (h : A ≤ A') (hm : ∀ x : A', x.1 ∈ A → (f x).1 ∈ B) : A →ₗ[ℂ] B :=
  LinearMap.codRestrict B (B'.subtype ∘ₗ f ∘ₗ Submodule.inclusion h) fun x => hm _ x.2

theorem restr_coe {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {A A' : Submodule ℂ X}
    {B B' : Submodule ℂ Y} (f : A' →ₗ[ℂ] B') (h : A ≤ A') (hm : ∀ x : A', x.1 ∈ A → (f x).1 ∈ B) (x : A) :
    (restr f h hm x).1 = (f ⟨x.1, h x.2⟩).1 := rfl

theorem exists_core {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (V₀ W₀ : HSp D) {χV χW : (AE D)ˣ →* Circle} {om : Om V W}
    (hom : IsWeilDatumO ψ V W χV χW om) (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) :
    ∃ om₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ :=
  GlobalTheory.Unf.Inhab.exists_weil hom.std V₀ W₀ hom.hecS hom.hecT (Formalism.L2.Theta.resEta_parity hom.resS hV)
    (Formalism.L2.Theta.resEta_parity hom.resT hW)

def mkStep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (V₀ W₀ : HSp D) {χV χW : (AE D)ˣ →* Circle} {om : Om V W}
    (hom : IsWeilDatumO ψ V W χV χW om) (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) (vW : Vol W) (ρ σ : ℕ) :
    Step ψ V V₀ W W₀ ρ σ :=
  ⟨χV, χW, om, (exists_core V₀ W₀ hom hV hW).choose, hom, (exists_core V₀ W₀ hom hV hW).choose_spec, vW,
    (GlobalTheory.Unf.Inhab.nonempty_volM D W.rank ρ).some, (GlobalTheory.Unf.Inhab.nonempty_volM D σ V₀.rank).some,
    (GlobalTheory.Unf.Inhab.nonempty_volU D ρ).some⟩

theorem cxp_le (hT : Formalism.IndefR.RecTie.TopMultH R) (t : T) : CXP R P t ≤ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) :=
  fun F hF => (hT t).ge ((cxp_iff P t F).1 hF).1

theorem cp_le (t : T) (j : ℕ) : CP R P t j ≤ R.CC t j := fun F hF => ((cp_iff P t j F).1 hF).1

theorem even_idx {j ρ : ℕ} (h : j + 2 * ρ + 2 = D.R.m) : Even j := by
  obtain ⟨a, ha⟩ := D.R.m_even
  exact ⟨a - ρ - 1, by omega⟩

def rowOf (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t : T) : RowCh R P u g t where
  vP j := if h : j + 1 < D.R.m then (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose else 0
  vT j h := (vec_lev P hl t (j + 1) (by omega) hl.βX (top_vec hc t j h)).choose
  sBF j ρ h := mkStep _ _ (hc.ωY t j (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes j ρ h).d) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j ρ h).d)
    (g.vol (j + 1)) ρ ρ
  sFB j σ h := mkStep _ _ (hc.ωY t (j + 1) (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j (σ + 1) h).d)
    (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes (j + 1 + 1) σ (idx_step h)).d) (g.vol (j + 1 + 1)) (σ + 1) σ
  io j := if h : j + 1 < D.R.m then restr (R.ioY t j) (cp_le P t (j + 1)) (ioY_mem P hCR hl hm hc t j h) else 0
  ioT j h := restr (ioXT R t j h) (cxp_le P hT t) (top_mem P hCR hl hm hc t j h)

theorem rowOf_is (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t : T) : (rowOf P hCR hl hm hc hT u g t).Is := by
  exact {
    vP j h := by
      have e : (rowOf P hCR hl hm hc hT u g t).vP j = (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose :=
        dite_eq_left h
      rw [e]
      exact (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose_spec
    vT j h := (vec_lev P hl t (j + 1) (by omega) hl.βX (top_vec hc t j h)).choose_spec
    sBF j ρ h := by
      have ho : Odd (j + 1) := (even_idx h).add_one
      refine ⟨rfl, rfl, ?_, ?_⟩
      · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)).1 = _
        rw [Lift.chrStep, ite_eq_left ho]
      · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)).2 = _
        rw [Lift.chrStep, ite_eq_left ho]
    sFB j σ h := by
      have ho : ¬ Odd (j + 1 + 1) := Nat.not_odd_iff_even.2 (even_idx h).add_one.add_one
      refine ⟨rfl, rfl, ?_, ?_⟩
      · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).1 = _
        rw [Lift.chrStep, ite_eq_right ho]
      · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).2 = _
        rw [Lift.chrStep, ite_eq_right ho]
    io j h F := by
      have e : (rowOf P hCR hl hm hc hT u g t).io j = restr (R.ioY t j) (cp_le P t (j + 1)) (ioY_mem P hCR hl hm hc t j h) :=
        dite_eq_left h
      rw [e]
      exact ⟨cp_le P t (j + 1) F.2, restr_coe _ _ _ F⟩
    ioT j h F := ⟨cxp_le P hT t F.2, restr_coe (ioXT R t j h) (cxp_le P hT t) (top_mem P hCR hl hm hc t j h) F⟩
  }

theorem rowOf_same (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t t' : T) :
    (rowOf P hCR hl hm hc hT u g t).Same (rowOf P hCR hl hm hc hT u g t') :=
  ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {At : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C At Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {K}

end Read

end GlobalTheory.Fam.FamInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.RNrmProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rNrm_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG
  have hL := hG.core.lev
  have hC := hG.core.chain
  have hQ : R.Q A.μ0 = ∅ := GlobalTheory.ChainTw.RModel.Q_base R hL
  have hm := D.R.two_le_m
  intro t
  refine ⟨fun k hk m X hX => ?_, fun m X hX => ?_⟩
  · obtain ⟨c, hc⟩ := hL.βY k (by omega)
    obtain ⟨c', hc'⟩ := hL.βY (k + 1) hk
    have h1 := hC.vY t k hk
    have h2 := hC.vY A.μ0 k hk
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k) :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hrk : (Yc D k).rank + D.R.t = (Yc D (k + 1)).rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), GlobalTheory.Chain.StepVac.rank_Yc (by omega)]; ring
    have key := _root_.GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors D R.ψ R.θ (Yc D k) (Yc D (k + 1)) _ _ _ _ _ _ (R.vac k) m X hb hX hc.1 hc'.1
      D.R.r D.R.t k D.R.t (r_le_Y k) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi (k + 1)) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega)]
    congr 4
    simp
  · obtain ⟨c, hc⟩ := hL.βY (D.R.m - 1) (by omega)
    obtain ⟨c', hc'⟩ := hL.βX
    have h1 := hC.vX t
    have h2 := hC.vX A.μ0
    rw [LevCh.datYt, hQ] at h2
    rw [LevCh.datYt] at h1
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX :=
      ⟨GlobalTheory.Chain.VacVec.cart_isCartanInv _, GlobalTheory.Chain.VacVec.cart_isCartanInv _,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩,
        GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c', hc'⟩, h1.1⟩
    have hX' : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    have hrk : (Yc D (D.R.m - 1)).rank + D.R.t = D.sp.X'.rank := by
      rw [GlobalTheory.Chain.StepVac.rank_Yc (by omega), hX']
      obtain ⟨n, hn⟩ : ∃ n, D.R.m = n + 1 := ⟨D.R.m - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel]; ring
    have key := _root_.GlobalTheory.TwistNorm.chainStep_twisted_normSq_eq_untwisted_mul_localFactors D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' _ _ _ _ _ _ R.vacX m X hb hX hc.1 hc'.1
      D.R.r D.R.t (D.R.m - 1) D.R.t (r_le_Y _) hrk R.Pg (R.Q t) (GlobalTheory.ChainTw.RModel.disjoint_Pg_Q R.toLevCh hL t)
      (hG.guard.2 t) R.chi (R.chi D.R.m) (R.xiR t) (R.xiR A.μ0) _ _ h1 h2
    rw [key]
    congr 1
    refine Finset.prod_congr rfl fun PP _ => ?_
    unfold volOne
    rw [hX']
    congr 4
    simp

end GlobalTheory.ChainTw.RNrmProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem GlobalTheory.ChainTw.rChain_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, RChain R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  exact GlobalTheory.ChainTw.RModel.rChain R hG.core.lev hG.core.models hG.core.chain h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexMulMeasureAdelicLevelSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section

open scoped Pointwise

namespace GlobalTheory.LevelIndexMeasure

theorem relIndex_mul_measure_preimage {G Q R : Type*} [Group G] [Group Q] [Group R] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (φ : G →* Q) (ψ : G →* R) (N : Subgroup G) (hN : ∀ n ∈ N, ψ n = 1)
    (H₁ H₀ : Subgroup Q) (h10 : H₁ ≤ H₀) (hsurj : H₀ ≤ N.map φ) (hfi : H₁.relIndex H₀ ≠ 0) (E : Set R)
    (hS : MeasurableSet (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E)) :
    (H₁.relIndex H₀ : ℝ≥0∞) * μ (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E) = μ (φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E) := by
  haveI : (H₁.subgroupOf H₀).FiniteIndex := ⟨hfi⟩
  obtain ⟨s, hs, -⟩ := (H₁.subgroupOf H₀).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hl : ∀ a : s, ∃ n ∈ N, φ n = ((a.val : H₀) : Q) := fun a => hsurj a.val.2
  choose lift hlN hlφ using hl
  set S₁ := φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E
  have hU : (⋃ a : s, lift a • S₁) = φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, S₁, smul_eq_mul]
    constructor
    · rintro ⟨a, y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [map_mul, hlφ]; exact H₀.mul_mem a.val.2 (h10 hy1)
      · rw [map_mul, hN _ (hlN a), one_mul]; exact hy2
    · rintro ⟨hx1, hx2⟩
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨φ x, hx1⟩
      refine ⟨b, (lift b)⁻¹ * x, ⟨?_, ?_⟩, by group⟩
      · have e : ((b : H₀) : Q) * ((h : H₀) : Q) = φ x := congrArg Subtype.val hbh
        rw [map_mul, map_inv, hlφ, ← e, inv_mul_cancel_left]
        exact Subgroup.mem_subgroupOf.mp h.2
      · rw [map_mul, map_inv, hN _ (hlN b), inv_one, one_mul]; exact hx2
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => lift a • S₁) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y1, ⟨hy1, -⟩, rfl⟩ ⟨y2, ⟨hy2, -⟩, he⟩
    apply hab
    simp only [smul_eq_mul] at he
    have he' := congrArg φ he
    rw [map_mul, map_mul, hlφ, hlφ] at he'
    have hh1' : (⟨φ y1, h10 hy1⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy1
    have hh2' : (⟨φ y2, h10 hy2⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy2
    have e : (a.val : H₀) * ⟨φ y1, h10 hy1⟩ = (b.val : H₀) * ⟨φ y2, h10 hy2⟩ := Subtype.ext he'.symm
    have := (hs.existsUnique ((a.val : H₀) * ⟨φ y1, h10 hy1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H₁.relIndex H₀ : ℝ≥0∞) * μ S₁ = ∑' a : s, μ (lift a • S₁) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, lift a • S₁) := (measure_iUnion hdisj fun a => hS.const_smul _).symm
    _ = _ := by rw [hU]

end GlobalTheory.LevelIndexMeasure

namespace GlobalTheory.LevelIndexMeasure

variable {D : D7}

theorem relIndex_mul_measure_levelSet : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) [ν.IsMulLeftInvariant] (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (E : Set (GinfC V)), K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} → MeasurableSet E → (K₁.relIndex K₀ : ℝ≥0∞) * ν ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ν ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) := by
  intro D V ν _ K₁ K₀ E h10 h0U hfi hK₁ hE
  obtain ⟨i1, -, -, -, i5, -, -, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable
  have hsurj : K₀ ≤ (GfC V).map (Lev.finE V) := by
    rw [← GlobalTheory.FunObj.map_levA V h0U]
    exact Subgroup.map_mono inf_le_left
  exact relIndex_mul_measure_preimage ν (Lev.finE V) (GlobalTheory.AutMult.toInf V) (GfC V)
    (fun n hn => (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V n).2 hn) K₁ K₀ h10 hsurj hfi E (hK₁.inter (hmeas hE))

end GlobalTheory.LevelIndexMeasure
end
end

