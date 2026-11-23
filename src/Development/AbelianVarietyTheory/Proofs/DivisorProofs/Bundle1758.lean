module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleSeriesEqPhaseThetaKO
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
noncomputable section

namespace GlobalTheory.AdTh.VecSeries
open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap


set_option maxHeartbeats 2000000 in
theorem singleSeries_eq_phase_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → IoExt R → ∀ (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i), IsWeilTw R i χ ω → ∀ (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q Ω φ' → ∀ (ka : ℂ), GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → ∀ (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : GlobalTheory.Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → ∀ (h : GA D (Vc D i)) (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ (g γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → singleSeries R i ω φ' h ((O i).c0' y) w g = ka * thetaKO ω h (γ * g) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hOP hE χ ω hω Q Ω φ' hφ ka hka P y hy X g' Dc vr hM hp hv h w hw g γ hγ
  have hθ : IsInfFam R.θ := hR.models.inf
  have hstd := hOP.2.lift.std
  have hPr := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i A.μ0 hstd
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ', h0⟩, e, -, hth⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ' hθ hth h0.theta

  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ P',
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f P' =
        pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f
          (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)) P') := by
    intro f hf P'
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (R.BV i) _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hBV τ)) f hf P'
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i A.μ0)) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)

  have hlt : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧
      ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨
        (ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧
          ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1)) := by
    intro ℓ
    have hP := hT.j.pins
    have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
      unfold Datum.mult
      rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
    obtain ⟨h1, h2⟩ := GlobalTheory.AdTh.Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
    obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
    refine ⟨g2.trans h1, ?_⟩
    rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
    · rw [e1, Sum.elim_inl] at g3
      exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
    · rw [e1, Sum.elim_inr] at g3
      exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

  have hio := hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 y
  have hpol : MvPolynomial.rename (fun ℓ => vr (Dc.eL ℓ)) (MvPolynomial.map (inC (O i).c') ((O i).io y)) =
      MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    rw [hy, MvPolynomial.rename_rename]
    exact congrArg (MvPolynomial.rename _) (MvPolynomial.map_map _ _ _)

  have hS : (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b))) (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y)) =
      ka • MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    apply hinj
    rw [map_smul, ← hsub _ f1, ← hpol]
    exact hio

  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) :=
    GlobalTheory.FockTheta.ptStable D R.ψ R.θ hψ hθ _ _ _ _ _ _ φ' _ hthφ
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → thetaKO ω h g f = thetaKO ω h (γ * g) f := fun f hf => by
    have e1 : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  have hsm : ∀ k f, thetaKO ω h k (ka • f) = ka * thetaKO ω h k f := fun k f => by
    rw [thetaKO, thetaKO, map_smul]
    rfl
  show thetaKO ω h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) φ' (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y))) = _
  rw [hsub _ hthφ, hS, map_smul, hsm, hmove _ hth]

end GlobalTheory.AdTh.VecSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem conjugateReadingsVanishing_splitPart : BarTie (fw2 p) := p.bar


set_option maxHeartbeats 2000000 in
theorem thetaRowData_pins_splitPart (i : Fin D.R.m) : OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i :=
  ⟨(p.pins i).1, { (p.pins i).2 with lift := { (p.pins i).2.lift with }, tuple := fun t => { (p.pins i).2.tuple t with } }⟩

theorem phaseCompatible_splitPart_of_liftUniformisation (hU : p.R.toRealDat.LUnif) (i : Fin D.R.m) :
    PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have h := p.phase i hU
  have he : phEff p.R = fun _ => 1 := funext fun j => p.phEff_one j
  rw [he] at h
  exact h

end

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SqTop.CondExpo

theorem levelLe_of_le {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)}
    {a b : ℕ} (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

theorem expAt_succ {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (h : χ.LevelLe v (n + 1)) (h' : ¬ χ.LevelLe v n) : GlobalTheory.CMVal.ExpAt χ v (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.SqTop.CondExpo


open GlobalTheory.SqTop.CondExpo in
theorem GlobalTheory.SqTop.CondExpo.expo_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hμ := L.C.isMu0 j
  have enu : nuH G t i j = L.C.mu0 j * L.xiH t * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, div_eq_mul_inv]
  have echi : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [enu, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

  have hW : ∀ v ∈ G.pl.S0, GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) (SqNum.condExp G.pl v) := by
    intro v hv
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · subst h0
      rw [SqNum.condExp, if_pos rfl]
      refine expAt_succ (n := 0) ?_ ?_
      · rw [enu]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul (G.ch.lev0 _ k1 k2 _ hu).1.inv
      · intro h
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
    · have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
      rw [SqNum.condExp, if_neg h0]
      have hl := G.ch.lev1 _ k1 k2 (G.pl.w v) (by rw [hu]; exact h1)
      refine expAt_succ (n := 1) ?_ ?_
      · rw [enu]
        exact ((levelLe_of_le (hμ.tame _) (by omega)).mul (levelLe_of_le (hL.xi_tame t _) (by omega))).mul hl.1.inv
      · intro h
        apply hl.2
        rw [echi]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul h.inv

  have hQ : ∀ w ∈ twPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w 1 := by
    intro w hw
    have hw' : w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
      simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
      exact ⟨hw.1.resolve_left hw.2, hw.2⟩
    have hS1 : w.under (𝓞 D.host.F) ∉ S1 D := fun h => by
      refine hw'.2 ?_
      rw [G.pl.w_Q t w hw'.1 h]
      exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
      (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t w hw'.1) hS1
    refine expAt_succ (n := 0) ?_ ?_
    · rw [enu]
      exact ((hμ.tame _).mul (hL.xi_tame t _)).mul
        (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 w hS0) 1).inv
    · intro h
      exact GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j w hw ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  have cW : ∀ v ∈ G.pl.S0, c (G.pl.w v) = SqNum.condExp G.pl v := fun v hv =>
    (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))).unique (hW v hv)
  have cQ : ∀ w ∈ twPl G t, c w = 1 := fun w hw =>
    (hc w (Finset.mem_filter.1 hw).1).unique (hQ w hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [cW v hv, SqNum.condExp]
      split_ifs <;> omega
    · rw [cQ w (Finset.mem_filter.2 ⟨hw, h⟩)]
  · rw [modul, modT, ← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0)]
    have e1 : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.W0 := by
      ext w
      simp only [Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union]
      tauto
    have e2 : (locPl G t).filter (fun w => w ∉ G.pl.W0) = twPl G t := rfl
    rw [e1, e2]
    congr 1
    · rw [Places.W0, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
      exact Finset.prod_congr rfl fun v hv => by rw [cW v hv]
    · exact Finset.prod_congr rfl fun w hw => by rw [cQ w hw, pow_one]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHermitianFormInertPointEqLocalFormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  first | exact @GlobalTheory.InertTens.hTens_kap_eq_locH | exact GlobalTheory.InertTens.hTens_kap_eq_locH | (intros; apply GlobalTheory.InertTens.hTens_kap_eq_locH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireLift

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  ext v
  simp [postOn]

theorem thetaFireL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireL (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hLev hGrp hMod hThP hv0 IL μ hμ i x
  have hfm : ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) ∈ LinearMap.range (R.extV i (tupT μ)) ⊓
      RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false)))
        (levChi _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false))) := (IL.jMt μ hμ i x).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm
      ⟨((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : R.extV i (tupT μ) y = ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (hinj i (tupT μ))).apply_symm_apply _)
  have hM := _root_.GlobalTheory.ThetaLevelP.thF_mem_level R F hLev hMod hThP hv0 false i (tupT μ) y (by rw [hyf]; exact hfm.2)
  refine ⟨PiTensorProduct.lift (R.thF i (tupT μ) y), ?_, ?_, ?_⟩
  · exact Submodule.mem_map_of_mem hM
  · rw [← hy]; rfl
  · have hG : R.eWf i (sg0 D A) ∘ₗ PiTensorProduct.lift (R.thF i (tupT μ) y) ∈
        (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).map
          (PiTensorProduct.lift : MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap := by
      rw [← lift_postOn]
      exact Submodule.mem_map_of_mem (GlobalTheory.GoodProjLevel.proj_mem_good R hLev hGrp.record hv0 i _ _ hM)
    exact hG

end GlobalTheory.ThetaFireLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformTransportedWeilContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaTransportCont

theorem thetaTr_om_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) w := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom Φ hΦ w
  choose g h hh hg using fun p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) =>
    _root_.GlobalTheory.WeilPairPartner.pair_partner D S T JA JB ξ hA hB p.1 p.2
  have hθ : Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) :=
    ⟨_root_.GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, _root_.GlobalTheory.ThetaLevel.thetaTr_level D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ,
      _root_.GlobalTheory.ThetaTrCont.continuous_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, _root_.GlobalTheory.ThetaSmooth.contDiff_thetaTr_real D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ⟩
  have hhU : ∀ p, matHom T (h p) = p.1.1 := fun p => Units.ext (hh p)
  have hgU : ∀ p, (matHom S (g p))⁻¹.1 = p.2.1.1ᵀ := by
    intro p
    apply Units.inv_eq_of_mul_eq_one_right
    change mt S (g p) * _ = 1
    rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
  have hcH' : Continuous fun p => matHom T (h p) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun p => matHom T (h p)) = fun p => p.1.1.1 := funext fun p => hh p
      rw [e]
      exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    · have e : (fun p => (matHom T (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
      rw [e]
      exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
  have hcG' : Continuous fun p => matHom S (g p) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun p => matHom S (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
      rw [e]
      exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    · have e : (fun p => (matHom S (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
      rw [e]
      exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
  have hcH : Continuous h := continuous_induced_rng.2 hcH'
  have hcG : Continuous g := continuous_induced_rng.2 hcG'
  have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) w =
      ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w := fun p =>
    congrFun (hom p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
  exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm

end GlobalTheory.ThetaTransportCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThreeRLtGOfParams
section
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.BigOn

theorem three_r_lt_g_of_params (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (k : Fin 2) :
    3 * D.R.r < D.host.g k := by
  obtain ⟨Y, hY1, -, -, hY4⟩ := P.g_Y
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b
    have := Real.add_one_le_exp L.sc.L
    linarith
  have hmk := D.R.m_add_three_le_k
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hkb : (2 : ℝ) * D.R.k ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hpow : (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 = ((D.R.k : ℝ) * L.sc.b) ^ 8 := by ring
  have h7 : (2 : ℝ) ^ 7 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) 7
  have hbig : (6 : ℝ) * D.R.k < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    rw [← hpow]
    have : (2 : ℝ) * D.R.k * 2 ^ 7 ≤ (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
      mul_le_mul hkb h7 (by norm_num) (by positivity)
    nlinarith
  have hr' : ((3 * D.R.r : ℕ) : ℝ) ≤ 6 * D.R.k := by
    have : 3 * D.R.r ≤ 6 * D.R.k := by omega
    exact_mod_cast this
  have hg : ((3 * D.R.r : ℕ) : ℝ) < (D.host.g k : ℝ) := by
    linarith [(hY4 k).1]
  exact_mod_cast hg

end GlobalTheory.BigOn
end
end

