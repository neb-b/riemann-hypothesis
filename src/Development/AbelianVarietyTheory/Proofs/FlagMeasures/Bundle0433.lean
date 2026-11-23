module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularFrameChangeFromLinearAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0431
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0430
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhase
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermPhase

theorem exists_termFrame_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u'), ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ := by
  intro D X Y u u' t
  exact t.rep.2.2.2.2.2.1

theorem psiInf_exp : ∀ {E : Type} [Field E] [NumberField E] (g : ℕ) (x y : E), Complex.exp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (x / g) : ℚ) : ℂ))) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ ∧ Formalism.L2.SG.PairVal.psiInf g (x - y) = Formalism.L2.SG.PairVal.psiInf g x * (Formalism.L2.SG.PairVal.psiInf g y)⁻¹ := by
  intro E _ _ g x y
  refine ⟨?_, ?_⟩
  · have hx : x / (g : E) = ((g : ℚ)⁻¹) • x := by
      rw [Algebra.smul_def, div_eq_inv_mul]
      simp
    rw [Formalism.L2.SG.PairVal.psiInf, ← Complex.exp_neg, hx, LinearMap.map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  · simp only [Formalism.L2.SG.PairVal.psiInf, map_sub]
    rw [← div_eq_mul_inv, ← Complex.exp_sub]
    congr 1
    push_cast
    ring

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hg0, hcg⟩ := _root_.GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hlat := _root_.GlobalTheory.HL.term_lat_isLattice D X Y u u' _ F00 F'0 FP G c t₀ ρ
  have hU := hMv.2.1
  have hU' := hMv.2.2.1

  have hext : ∀ (N : G.GLV) p, ∃ m : (G.S p).GLV, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m :=
    fun N p => ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 N).exists

  have key : ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ →
      ∃ N N' : G.GLV, (∀ b, N (G.f b) = ∑ a, U a b • G.f a) ∧
        (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) ∧
        ∀ p (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m →
          (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' →
          (G.S p).IsTerm ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) ∧
            (G.S p).om ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) =
              (G.S p).psi m * ((G.S p).psi' m')⁻¹ := by
    intro ξ hξ
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    obtain ⟨hBl, hBd, -⟩ := _root_.GlobalTheory.unitri_mul_inv_sgUp U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd
    obtain ⟨⟨N, hN⟩, -⟩ := _root_.GlobalTheory.HL.UniExt.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U
      (fun i j h => (hU i j).1 h) (fun i => (hU i i).2 rfl)
    obtain ⟨-, ⟨N', hN'⟩⟩ := _root_.GlobalTheory.HL.UniExt.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G
      (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) hBl hBd
    refine ⟨N, N', hN, hN', ?_⟩
    intro p m m' hm hm'
    obtain ⟨t, d, hto, hlatEq, hf, hf'⟩ := _root_.GlobalTheory.HL.MovedTermLoc.main D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U'
      hMv p ξ hξ N N' hN hN' m m' hm hm'
    obtain ⟨h1, -⟩ := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
      D.R.rS D.R.k (FP p) (G.S p) (c.c p)
    obtain ⟨hT, hom, -⟩ := h1 d t hto
    rw [hlatEq] at hT hom
    have : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
    have : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
    have hd := (_root_.GlobalTheory.HL.DatumOf.main ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L p) D.R.rS D.R.k (G.S p)).1 _ _ hT
    rw [hd] at hT hom
    have hpsi := _root_.GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
      (c.c p) d t hto m m' hf hf'
    exact ⟨hT, hom ▸ hpsi⟩

  have hsig : ∀ x, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]
    exact (Formalism.BasicNotions.bridge_star_holds _ D.host x).symm
  have hprod := fun (n : G.GLV) (m : ∀ p, (G.S p).GLV)
      (hx : ∀ p, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p n (m p)) =>
    GlobalTheory.HL.PhaseProduct.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G D.sp.cm hsig
      (fun p => Units.mk0 (Y.δ p) (Y.agree p).2.1) (gS D) hg0
      (fun p y => (Y.agree p).2.2.2.2.1 y)
      (fun p => hcg p) n m hx
  obtain ⟨ξ₀, hξ₀⟩ := exists_termFrame_admissibilityWitness D X Y u u' t₀
  refine ⟨⟨hlat, fun p => ?_⟩, ?_⟩
  · obtain ⟨N, N', -, -, hloc⟩ := key ξ₀ hξ₀
    obtain ⟨m, hm⟩ := hext N p
    obtain ⟨m', hm'⟩ := hext N' p
    exact (hloc p m m' hm hm').1
  · intro ξ hξ
    obtain ⟨N, N', hN, hN', hloc⟩ := key ξ hξ
    choose m hm using hext N
    choose m' hm' using hext N'
    obtain ⟨hP, -, hfin⟩ := hprod N m hm
    obtain ⟨-, hP', hfin'⟩ := hprod N' m' hm'
    have hom : G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) =
        ∏ᶠ p, ((G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹) :=
      finprod_congr fun p => (hloc p (m p) (m' p) (hm p) (hm' p)).2
    have hs1 : (Function.mulSupport fun p => (G.S p).psi (m p)).Finite :=
      hfin.subset fun p hp => Or.inl hp
    have hs2 : (Function.mulSupport fun p => ((G.S p).psi' (m' p))⁻¹).Finite :=
      hfin'.subset fun p hp => Or.inr fun h => (Function.mem_mulSupport.1 hp) (by simp [h])
    rw [hom, finprod_mul_distrib hs1 hs2, finprod_inv_distrib, hP, hP',
      (_root_.GlobalTheory.SlocCoef.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U N).1 hN,
      (_root_.GlobalTheory.SlocCoef.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G _ N').2 hN',
      (psiInf_exp (gS D) _ 0).1, (psiInf_exp (gS D) _ 0).1, inv_inv]
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    rw [(_root_.GlobalTheory.unitri_mul_inv_sgUp U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd).2.2,
      (psiInf_exp (gS D) _ _).2, mul_assoc]

end GlobalTheory.HL.MovedTermPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEq
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.DatEq

theorem row_eq_iff_datOf_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hA := _root_.GlobalTheory.HL.datOf_dcoset D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hI := _root_.GlobalTheory.IotaGraph.iotaCompat_iff_graph D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hD := Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t₀ t hl.symm hl'.symm
  have hrow : ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) ↔
      iotaOf Y.TR (Y.cs u) (Y.cs u') t₀ = iotaOf Y.TR (Y.cs u) (Y.cs u') t := by
    show ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t) : Rw _ _ Y.TR) =
        (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t₀) ↔ _
    constructor
    · intro h
      exact (congrArg (fun r => r.2.2) h).symm
    · intro h
      rw [h]
      ext <;> simp [hl, hl']
  rw [hrow, hD, hI]
  constructor
  · intro h
    funext p
    exact Prod.ext (hA p).1 (Prod.ext (hA p).2 (h p))
  · intro h p
    exact congrArg (fun d => (d p).2.2) h

end GlobalTheory.HL.DatEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingIdentityMatchedFamilyClosedTerms
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.Tied

theorem infinite_finPl (K : Type) [Field K] [NumberField K] : Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

section Scale

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_scale₂ (H : HermSp M V) (c d : E) (x y : V) :
    H.h (c • x) (d • y) = M.L.cj d * c * H.h x y := by
  rw [H.h_smul_left, H.h_herm (d • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  ring

theorem dl_scale₂ (H : HermSp M V) {r : ℕ} (s s' : Fin (r + 1) → E) (f f' : Fin (r + 1) → V) (l : ℕ)
    (hl : l ≤ r + 1) :
    H.Dl (fun a => s a • f a) (fun b => s' b • f' b) l =
      (∏ i : Fin l, M.L.cj (s (Fin.castLE hl i)) * s' (Fin.castLE hl i)) * H.Dl f f' l := by
  unfold HermSp.Dl
  rw [dite_eq_left hl, dite_eq_left hl]
  have hsub : (H.Zhat (fun a => s a • f a) (fun b => s' b • f' b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => M.L.cj (s (Fin.castLE hl i))) *
        (H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => s' (Fin.castLE hl i)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, HermSp.Zhat, Matrix.of_apply, h_scale₂]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Scale

theorem dl_bcP (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (l : ℕ) :
    (locH Z p).Dl (fun a => baseChange₂ D p (frame F a)) (fun b => baseChange₂ D p (frame F' b)) l =
      (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Loc.HermSp.Zhat,
      Formalism.MainNotions.S.Zhat, Matrix.of_apply]
    exact baseChangeAt_form Z.M p (Z.hcj p) _ _
  · simp

theorem gval_ne_of_locGv (D : D7) (Z : LocDat D) (p : PlF D) (u u' : D.what₂.Word)
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (P : LocNG.FPair (locH Z p) D.R.rS) (hP : GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') P)
    (hG : P.Gv ≠ 0) : Gval F F' ≠ 0 := by
  intro h0
  apply hG
  obtain ⟨hA, hB, hT, hT'⟩ := hP
  have hs : ∀ (f : Fin (D.R.rS + 1) → (VS D).V),
      GlobalTheory.LocOver.scaled Z p f = fun a => frFac Z.δ p a • baseChange₂ D p (f a) := fun _ => rfl
  have hD : ∀ l (hl : l ≤ D.R.rS + 1),
      (locH Z p).Dl (GlobalTheory.LocOver.scaled Z p (frame F)) (GlobalTheory.LocOver.scaled Z p (frame F')) l =
        (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i)) *
          (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
    intro l hl
    rw [hs (frame F), hs (frame F'), dl_scale₂ _ _ _ _ _ l hl, dl_bcP]
  have hlast : frFac Z.δ p (Fin.last D.R.rS) = 1 := by
    simp [frFac]
  have hc : (∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (frFac Z.δ p (Fin.castLE le_rfl i)) *
      frFac Z.δ p (Fin.castLE le_rfl i)) =
      ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)) *
        frFac Z.δ p (Fin.castLE (Nat.le_succ _) i) := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id]
    rw [hlast, map_one, mul_one, mul_one]
    rfl
  unfold LocNG.FPair.Gv Loc.HermSp.Gdet Loc.HermSp.normE
  rw [hA, hB, hT, hT', hD _ le_rfl, hD _ (Nat.le_succ _), hc]
  have hG0 : Gflag F.fl F'.fl = 0 := h0
  unfold Gflag at hG0
  have hι := congrArg (D.s.atP p).ιE hG0
  rw [map_zero] at hι
  simp only [map_sub, map_mul, map_natCast] at hι
  have hcj : ∀ z, (Z.M p).L.cj ((D.s.atP p).ιE z) = (D.s.atP p).ιE (star z) := cj_iota (Z.hcj p)
  simp only [map_mul, hcj, map_natCast]
  set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)) *
        frFac Z.δ p (Fin.castLE (Nat.le_succ _) i)
  dsimp only [Tu]
  linear_combination (c * (Z.M p).L.cj c) * hι

theorem wt_self {D : D7} {Z : LocDat D} {p : PlF D} {P : LocNG.FPair (locH Z p) D.R.rS} (d : LocNG.Datum P) :
    LocNG.Datum.wt d d = 1 := by
  simp [LocNG.Datum.wt, LocNG.volRel, Subgroup.relIndex_self]

theorem unfold_tied : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), ClsRow TS cls → (∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH (zOf Y) p) D.R.rS, Based (zOf Y) FP (Tu D u) (Tu D u') F F' → LocClosed F F' (zOf Y) FP TS) → ∀ (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl (NuC D)), FamTie TS cls (nmlOf Y u u') γ Fm → ∃ V0, OrbitFamilyIdentityAt Fm V0 := by
  intro D X Y u u' Cl TS cls hCls hLC γ Fm hT
  obtain ⟨w, F00, F'0, F'1, hγ, hD, hV0, hn, hZ, hFP, hOm, hPr, hStd, ht0, hPtm, hΛ, hdat, hgen⟩ := hT
  subst hγ
  haveI := infinite_finPl D.host.F
  obtain ⟨p0, hp0⟩ : ∃ p, p ∉ Fm.P := by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (α := PlF D) (Fm.P.finite_toSet.subset fun p _ => h p)
  have hBased : Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F00 F'0 := fun p => hFP p
  have hG : Gval F00 F'0 ≠ 0 := by
    refine gval_ne_of_locGv D (zOf Y) p0 u u' F00 F'0 (Fm.FP p0) (hBased p0) ?_
    obtain ⟨-, ⟨-, y, -, hy⟩, -⟩ := hPr p0 hp0
    intro h0
    rw [h0, zero_mul] at hy
    exact zero_ne_one hy
  have hLC' := hLC F00 F'0 w hZ hG Fm.FP hBased
  have hRel : ∀ p, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (_root_.GlobalTheory.LocBaseRel.atBase_relG D (zOf Y) u u' w F00 F'0 hZ hG p).2 _ (hBased p)
  obtain ⟨Λ₀, hΛl, hΛ₀⟩ := hΛ
  have hterm0 : ∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ := by
    intro p
    by_cases hp : p ∈ Fm.P
    · exact hPtm p hp
    · exact ⟨_, hΛ₀ p hp⟩
  have hΛfin : ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧
      τ.abelian₂ = lattice₂ D (zOf Y).M p Λ}.Finite := by
    refine ⟨Λ₀, hΛl, Fm.P.finite_toSet.subset fun p hp => ?_⟩
    by_contra hp'
    exact hp ⟨_, hΛ₀ p hp', rfl⟩
  obtain ⟨V1, hV1, hmass⟩ := _root_.GlobalTheory.Unfold.mass_genus_local_weights D X Y u u' F00 F'0 w hZ hG (zOf Y) Fm.FP hBased hRel Fm.d0 hterm0 hΛfin
  have hΛ' : ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, p ∉ Fm.P →
      ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ :=
    ⟨Λ₀, hΛl, fun p hp => ⟨_, hΛ₀ p hp, rfl⟩⟩
  have hdat' : ∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
      ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
        ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν →
          (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2 := by
    intro c ν
    have h := hdat c ν
    refine ⟨fun h0 => ?_, fun d h1 => ?_⟩
    · rw [h0] at h; exact h
    · rw [h1] at h; exact h
  refine ⟨V1, hV1, ?_⟩
  intro d hd
  let dd : Dat (zOf Y) Fm.FP := fun p => if hp : p ∈ Fm.P then (d ⟨p, hp⟩).1 else Fm.d0 p
  have hdd1 : ∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1 := fun p hp => by simp [dd, hp]
  have hdd2 : ∀ p, p ∉ Fm.P → dd p = Fm.d0 p := fun p hp => by simp [dd, hp]
  obtain ⟨hddT, hsum⟩ := _root_.GlobalTheory.Unfold.GenusRows.rows_mass_genus D X Y u u' F00 F'0 w hZ hG TS cls Fm hBased hCls hLC' hD hStd hΛ' hdat' d hd
    dd hdd1 hdd2
  have hfin : {p | dd p ≠ Fm.d0 p}.Finite :=
    Fm.P.finite_toSet.subset fun p hp => by
      by_contra hp'
      exact hp (hdd2 p hp')
  rw [hsum, hmass dd hddT hfin]
  congr 2
  rw [finprod_eq_prod_of_mulSupport_subset (s := Fm.P)]
  · rw [← Finset.prod_attach]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hdd1 p.1 p.2]
    rfl
  · intro p hp
    by_contra hp'
    exact hp (by simp only [hdd2 p hp', wt_self])

end GlobalTheory.Unfold.Tied
end

