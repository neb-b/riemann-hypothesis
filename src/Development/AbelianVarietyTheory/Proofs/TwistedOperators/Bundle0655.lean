module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetDatumVectorFiniteHeisenbergCombination
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.DictFree

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable def conjQ : Qbar →+* Qbar where
  toFun x := ⟨starRingEnd ℂ x, by
    have h : IsAlgebraic ℚ (x : ℂ) := (mem_algebraicClosure_iff).1 x.2
    exact (mem_algebraicClosure_iff).2
      (h.algHom ((Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →ₐ[ℚ] ℂ))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

noncomputable def oppQ {T : Type} : Pair T → (Qbar →+* Qbar)
  | .chi _ _ => conjQ
  | .core _ => conjQ
  | _ => RingHom.id _

theorem oppQ_coe {T : Type} (p : Pair T) (x : Qbar) : ((oppQ p x : Qbar) : ℂ) = opp p (x : ℂ) := by
  cases p <;> rfl

theorem opp_opp {T : Type} (p : Pair T) (z : ℂ) : opp p (opp p z) = z := by
  cases p <;> simp [opp]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem jetTab_comb {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    (B : VertexFrames G) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) {n : ℕ}
    (a : Fin n → ℂ) (w : Fin n → WO (G.pS p) (G.pT p)) (hw : ∀ i, (w i).map (infPart D) = 0)
    (X : FinPt G p.small) (Y : FinPt G p.big) (mon : Formalism.L2.Ker.DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) :
    jetTab W B p (∑ i, a i • heisO W.ψ _ _ (w i) f) X Y mon = ∑ i, a i * jetTab W B p (heisO W.ψ _ _ (w i) f) X Y mon := by
  have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf n a w hw (monomial (mon.mapDomain (fvar G p)) 1)).1
  have h2 : ∀ i, heisO W.ψ _ _ (w i) (pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f
      (monomial (mon.mapDomain (fvar G p)) 1)) = pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p)
      (G.onT B p) (heisO W.ψ _ _ (w i) f) (monomial (mon.mapDomain (fvar G p)) 1) := fun i => by
    have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
      (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf 1 (fun _ => 1) (fun _ => w i) (fun _ => hw i)
      (monomial (mon.mapDomain (fvar G p)) 1)).1
    simpa using this
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO]
  rw [← h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← h2, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem differentiable_U {D : D7} (Tr : Tor D) {N N' : ℕ} (s : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.U D Tr s G) := by
  unfold Formalism.MainNotions.TaylorLogMetric.U Formalism.MainNotions.TaylorLogMetric.Hf
  fun_prop

end GlobalTheory.DictFree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPtAtPlace


set_option maxHeartbeats 1000000 in
theorem exists_splitPt_cpt : ∀ (D : D7) (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → D.host.F = maximalRealSubfield D.host.E → ∃ p : GlobalTheory.FinPl.SplitPt D (Kw w), p.e = e ∧ p.v = w.under (𝓞 D.host.F) ∧ ∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a)) := by
  intro D w e he hF
  obtain ⟨s, hsw⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D w
    (GlobalTheory.OffBad.isSplitPl_of_isSplit D w (GlobalTheory.DivPtLocal.isSplit_of_isIdemAt D w e he))
  subst hsw
  obtain ⟨p, c, hpl, hc, hci, hπ⟩ := _root_.GlobalTheory.SplitLocPlace.exists_place D s hF
  obtain ⟨q, hq⟩ := GlobalTheory.PlaceSplitPt.exists_splitPt p
  have hqe : q.e = p.e := by rw [← hq]; rfl
  have hqpr : ∀ a, q.pr a = p.π a := fun a => by rw [← hq]; rfl
  have hpe : Formalism.L2.NTheta.IsIdemAt p.e s.w := ⟨p.split, hpl.2.2⟩
  have hee : p.e = e := GlobalTheory.LocMod.PinInhab.idem_unique hpe he
  refine ⟨q, hqe.trans hee, GlobalTheory.LocMod.PinInhab.v_eq_under q (hqe ▸ hpe), fun a => ?_⟩
  rw [hqpr, hπ]
  have key := GlobalTheory.SplitFrameW.cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (Lev.swapAE D))
    (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci (GlobalTheory.NJoin.tensCast hF (finPart D a))
  rw [← key]
  have hcast : GlobalTheory.NJoin.tensCast hF = GlobalTheory.Mem.R3.swapCast hF := rfl
  rw [hcast, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.SplitPtAtPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

private theorem B_update_mul_eq_mul {X : ℕ → Type} (B : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (j : ℕ)
    (a : (∀ i, X i) → X j → ℂ) (R : (∀ i, X i) → ℂ)
    (ha : ∀ u x, a (Function.update u j x) = a u) (hR : ∀ u x, R (Function.update u j x) = R u)
    (u : ∀ i, X i) :
    B j (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) (u j) =
      B j (a u) (u j) * R u := by
  have hfun : (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) =
      R u • a u := by
    funext x
    rw [ha, hR, Function.update_self, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prod_op {X : ℕ → Type} (A : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (n : ℕ) :
    ∃ Tc : ((∀ j, X j) → ℂ) →ₗ[ℂ] ((∀ j, X j) → ℂ), ∀ (C : ∀ j, X j → X (j + 1) → ℂ) (g : (∀ j, X j) → ℂ),
      (∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g u = g u') →
      (fun u : ∀ j, X j => (∏ k ∈ Finset.range n,
          A (2 * k) (fun x => A (2 * k + 1) (C (2 * k) x) (u (2 * k + 1))) (u (2 * k))) * g u) =
        Tc (fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) := by
  classical

  let op : ∀ j, ((∀ i, X i) → ℂ) →ₗ[ℂ] ((∀ i, X i) → ℂ) := fun j =>
    { toFun := fun F u => A j (fun x => F (Function.update u j x)) (u j)
      map_add' := fun F G => by
        funext u
        have e : (fun x => (F + G) (Function.update u j x)) =
            (fun x => F (Function.update u j x)) + (fun x => G (Function.update u j x)) := rfl
        rw [e, map_add (f := _)]
        rfl
      map_smul' := fun c F => by
        funext u
        have e : (fun x => (c • F) (Function.update u j x)) = c • (fun x => F (Function.update u j x)) := rfl
        rw [e, map_smul]
        rfl }
  induction n with
  | zero => exact ⟨LinearMap.id, fun C g _ => by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T ∘ₗ op (2 * n) ∘ₗ op (2 * n + 1), fun C g hg => ?_⟩

    obtain ⟨R, hRR⟩ : ∃ R : (∀ j, X j) → ℂ,
        R = fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u := ⟨_, rfl⟩
    have hR : ∀ j, 2 * n ≤ j → j < 2 * n + 2 → ∀ (u : ∀ i, X i) x, R (Function.update u j x) = R u := by
      intro j hj1 hj2 u x
      subst hRR
      dsimp only
      congr 1
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact hg _ _ fun i hi => Function.update_of_ne (by omega) _ _

    obtain ⟨g', hgG⟩ : ∃ g' : (∀ j, X j) → ℂ,
        g' = fun u => A (2 * n) (fun x => A (2 * n + 1) (C (2 * n) x) (u (2 * n + 1))) (u (2 * n)) * g u :=
      ⟨_, rfl⟩
    have hg' : ∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g' u = g' u' := by
      intro u u' h
      subst hgG
      dsimp only
      rw [h (2 * n) le_rfl, h (2 * n + 1) (by omega), hg u u' fun j hj => h j (by omega)]

    have h1 : op (2 * n + 1) (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
        fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u := by
      have hF : (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
          fun u => (fun w : ∀ j, X j => C (2 * n) (w (2 * n))) u (u (2 * n + 1)) * R u := by
        funext u
        subst hRR
        simp only [Finset.prod_range_succ]
        ring
      rw [hF]
      funext v
      refine B_update_mul_eq_mul A (2 * n + 1) (fun w => C (2 * n) (w (2 * n))) R ?_ (hR _ (by omega) (by omega)) v
      intro w x
      show C (2 * n) (Function.update w (2 * n + 1) x (2 * n)) = C (2 * n) (w (2 * n))
      rw [Function.update_of_ne (by omega)]

    have h2 : op (2 * n) (fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u) =
        fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g' u := by
      funext v
      have e := B_update_mul_eq_mul A (2 * n) (fun w x => A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))) R
        (fun w y => by
          funext x
          show A (2 * n + 1) (C (2 * n) x) (Function.update w (2 * n) y (2 * n + 1)) = A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))
          rw [Function.update_of_ne (by omega)])
        (hR _ le_rfl (by omega)) v
      refine e.trans ?_
      subst hRR hgG
      dsimp only
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, ← hT C g' hg']
    funext u
    subst hgG
    simp only [Finset.prod_range_succ]
    ring

noncomputable def combLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem exists_comb_op : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ => ?_⟩⟩
  intro c
  obtain ⟨Tc, hTc⟩ := exists_prod_op (X := fun j => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
    (fun j => combLin ch.W.ψ _ _ (c.1 j)) (D.R.m / 2)
  refine ⟨Tc, fun C => ?_⟩
  exact hTc C (fun _ => ∏ i, (1 : SchRow ch.G) i ((0 : RowPt ch.G) i)) fun _ _ _ => rfl

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.PlcAtW

variable {D : D7}


open Classical in
theorem cpt_atPl_self (w : Pl D.host.E) (x : Kw w) : cpt w (toEAf D (atPl w x)) = x := by
  rw [(atPl_spec w x).2 w, Pi.single_eq_same]

theorem atPl_zero (w : Pl D.host.E) : atPl w (0 : Kw w) = 0 := by
  have h := atPl_add w 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def atPlHom (w : Pl D.host.E) : Kw w →+ AE D where
  toFun := atPl w
  map_zero' := atPl_zero w
  map_add' := atPl_add w

theorem atPl_cpt (w : Pl D.host.E) (a : AE D) : atPl w (cpt w (toEAf D a)) = atPl w 1 * a := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [(atPl_spec w _).1, map_mul, (atPl_spec w 1).1, zero_mul]
  · rw [(atPl_spec w _).2 Q, map_mul, map_mul, (atPl_spec w 1).2 Q]
    by_cases hQ : Q = w
    · subst hQ
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne hQ, Pi.single_eq_of_ne hQ, zero_mul]

theorem valuation_le_of_inv_mul {k : Type} [Field k] [ValuativeRel k] (u : kˣ) (b : k)
    (h : ValuativeRel.valuation k (((u⁻¹ : kˣ) : k) * b) ≤ 1) :
    ValuativeRel.valuation k b ≤ ValuativeRel.valuation k (u : k) := by
  have hne : ValuativeRel.valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h
  calc ValuativeRel.valuation k b
      = ValuativeRel.valuation k (u : k) * ((ValuativeRel.valuation k (u : k))⁻¹ * ValuativeRel.valuation k b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
    _ = _ := mul_one _

theorem cpt_atPl_mul (w : Pl D.host.E) (x : Kw w) (z : AE D) :
    cpt w (toEAf D (atPl w x * z)) = x * cpt w (toEAf D z) := by
  rw [map_mul, map_mul, cpt_atPl_self]

theorem valuation_cpt_le_one (w : Pl D.host.E) (x : AE D) (h : finPart D x ∈ intAE D) :
    ValuativeRel.valuation (Kw w) (cpt w (toEAf D x)) ≤ 1 := by
  have h2 := ((GlobalTheory.StdFrames.comp_toAd D).int x).1 h w
  have h3 : cpt w (toEAf D x) ∈ (ValuativeRel.valuation (Kw w)).integer :=
    (GlobalTheory.FinPl.SplitPoint.mem_integer_iff D.host.E w _).2 h2
  exact h3

end GlobalTheory.PlcAtW

open scoped TensorProduct

namespace GlobalTheory.PlcAtW

variable {D : D7}


open scoped Topology in
theorem continuous_cpt_toEAf (w : Pl D.host.E) : Continuous fun a : AE D => cpt w (toEAf D a) := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero (Kw w)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  let f : AE D →+ Kw w := ((cpt w).comp (toEAf D)).toAddMonoidHom
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine (IsValuativeTopology.hasBasis_nhds_zero (Kw w)).tendsto_right_iff.2 fun γ _ => ?_
  have hϖ : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) < 1 := by
    rw [isUnif_unifAt w]
    exact ValuativeRel.uniformizer_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ γ
  set u : (Kw w)ˣ := unifAt w ^ n
  have hu : ValuativeRel.valuation (Kw w) (u : Kw w) < γ := by
    simpa [u, Units.val_pow_eq_pow_val, map_pow] using hn
  have hU : {z : AE D | finPart D (atPl w ((u⁻¹ : (Kw w)ˣ) : Kw w) * z) ∈ intAE D} ∈ 𝓝 (0 : AE D) := by
    refine IsOpen.mem_nhds (h1.preimage (hfc.comp (continuous_const.mul continuous_id))) ?_
    simp only [Set.mem_setOf_eq, mul_zero, map_zero]
    exact zero_mem _
  filter_upwards [hU] with z hz
  have h3 := valuation_cpt_le_one w _ hz
  rw [cpt_atPl_mul] at h3
  exact (valuation_le_of_inv_mul u _ h3).trans_lt hu

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

variable {D : D7}

theorem continuous_atPl (w : Pl D.host.E) : Continuous (atPl (D := D) w) := by
  classical
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, -, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  have ht : Function.Bijective (toAd D) :=
    ⟨GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D), GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)⟩
  let R : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    RingEquiv.ofBijective ((toAd D).comp (Formalism.IndefR.Lev.swapAE D)) (ht.comp hs)
  have hfin : ∀ y, finPart D (e.symm (0, y)) = y := fun y => by
    rw [← (he _).2, RingEquiv.apply_symm_apply]
  have hR : Continuous R.symm := by
    refine GlobalTheory.AdeleBaseChange.continuous_symm_finite D.host.F D.host.E R fun y => ?_
    have key := (GlobalTheory.StdFrames.comp_toAd D).int (e.symm (0, y))
    rw [hfin] at key
    have e1 : ((toAd D).comp (toEAf D)) (e.symm (0, y)) = R y := by
      show toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, y)))) = toAd D (Formalism.IndefR.Lev.swapAE D y)
      rw [hfin]
    rw [e1] at key
    exact key
  have hform : ∀ x, atPl w x = e.symm (0, R.symm (singleV D.host.E w x)) := fun x => by
    refine ae_ext ?_ fun Q => ?_
    · rw [(atPl_spec w x).1, ← (he _).1, RingEquiv.apply_symm_apply]
    · rw [(atPl_spec w x).2 Q]
      show _ = toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, R.symm (singleV D.host.E w x))))) Q
      rw [hfin]
      show _ = R (R.symm (singleV D.host.E w x)) Q
      rw [RingEquiv.apply_symm_apply]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same]
        exact (RestrictedProduct.single_eq_same _ _ _).symm
      · rw [Pi.single_eq_of_ne hQ]
        exact (RestrictedProduct.single_eq_of_ne _ _ hQ).symm
  rw [funext hform]
  exact hes.comp (continuous_const.prodMk (hR.comp (GlobalTheory.FinPl.SplitPoint.continuous_single_at D.host.E w)))

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

theorem exists_plc : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  intro D w e he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_singleton]
  have h := hes w (Finset.mem_singleton_self w)
  have he1 := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h
  refine ⟨{ e := es w
            split := h.1
            π := (cpt w).comp (toEAf D)
            ι := atPlHom w
            π_ι := cpt_atPl_self w
            ι_π := fun a => by
              show atPl w (cpt w (toEAf D a)) = es w * a
              rw [atPl_cpt, ← he1]
            cont_π := continuous_cpt_toEAf w
            cont_ι := continuous_atPl w }, ⟨h, fun _ => rfl, fun _ => rfl⟩, rfl⟩

end GlobalTheory.PlcAtW

end
end

