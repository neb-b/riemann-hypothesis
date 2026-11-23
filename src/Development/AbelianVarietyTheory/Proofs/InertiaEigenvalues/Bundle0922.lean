module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralTranslateUniformisationCuspFormNeZe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.IdemResLift


set_option maxHeartbeats 800000 in
theorem exists_int_lift : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  intro D Q es hI hc Y
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hI i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have horth : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hI i hi) (hI j hj) (hx i hi j hj) (hx j hj i hi) hji
  have hfix : ∀ j ∈ Q, (∑ i ∈ Q, es i) * es j = es j := by
    intro j hj
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i hi hij => by rw [mul_comm]; exact horth j hj i hi hij)
      (fun h => absurd hj h), h1 j hj]
  choose a ha using fun P : Pl D.host.E => Ideal.Quotient.mk_surjective (Y P)
  have hint : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)).1
  have hmem : ∀ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)
      ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP => Subring.mul_mem _ (hint P hP) (Subtype.property _)
  let T : ∀ P, P ∈ Q → Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    ⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)
  refine ⟨∑ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D),
    Subring.sum_mem _ hmem, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [← mul_assoc, ← RingHom.map_mul (toEAf D), hfix P hP]
  · intro P hP
    have hN : (⟨_, Subring.sum_mem _ hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ x ∈ Q.attach, T x.1 x.2 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (Finset.sum_attach Q (fun P => toEAf D (es P) *
        ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D))).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hN, map_sum, Finset.sum_eq_single ⟨P, hP⟩]
    · obtain ⟨h, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)
      show resS D.host.F P (⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)) = Y P
      rw [map_mul, resS_oToS, ha, h1, one_mul]
    · rintro ⟨P', hP'⟩ - hne
      have hne' : P' ≠ P := fun h => hne (Subtype.ext h)
      show resS D.host.F P (⟨toEAf D (es P'), hint P' hP'⟩ * oToS D.host.F D.host.E (a P')) = 0
      rw [map_mul, GlobalTheory.TameProd.resS_idem_eq_zero (hI P' hP') hne', zero_mul]
    · intro h; exact absurd (Finset.mem_attach Q _) h

end GlobalTheory.IdemResLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaSeriesRationalVectorNeZeroOfCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SeriesTie.RatNe

theorem thetaKO_sum' {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (x : GA D S) (g : GA D T)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ : ι → WO S T → ℂ) :
    thetaKO om x g (∑ k ∈ s, c k • φ k) = ∑ k ∈ s, c k * thetaKO om x g (φ k) := by
  unfold thetaKO
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

theorem ser_sum {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (w : ι → (R.cV i).W) :
    ser R i t f u h (∑ k ∈ s, a k • w k) g = ∑ k ∈ s, a k * ser R i t f u h (w k) g := by
  unfold ser
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [map_smul]
  exact thetaKO_sum' _ _ _ _ _ _

theorem exists_rat_of_ser_ne {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {K' : Type} [Field K'] (σ' : K' →+* ℂ) (ψ : K' →+* D.what₂.LL) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i σ' c0' c) (w : VsV D i K')
    (hne : ser R i t f u h (c0' w) g ≠ 0) :
    ∃ (v : VsV D i D.what₂.LL) (x : VsV D i ℂ),
      (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) m = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) ∧
      ser R i t f u h (c x) g ≠ 0 := by
  classical
  have hw' : c0' w = ∑ b, σ' ((bVV K' (lamV D i)).repr w b) • c0' (bVV K' (lamV D i) b) := by
    conv_lhs => rw [← (bVV K' (lamV D i)).sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ]
  rw [hw', ser_sum] at hne
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hb' := right_ne_zero_of_mul hb
  obtain ⟨P, hP⟩ := bVVfun_int K' (lamV D i) b
  have hvmem : MvPolynomial.map (Int.castRingHom D.what₂.LL) P ∈ VV D.what₂.LL (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV ψ (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show ψ.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  have hxmem : MvPolynomial.map (Int.castRingHom ℂ) P ∈ VV ℂ (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV σ' (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show σ'.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  refine ⟨⟨_, hvmem⟩, ⟨_, hxmem⟩, fun m => ⟨((AddMonoidAlgebra.coeff P m : ℤ) : ℚ), ?_⟩, ?_, ?_⟩
  · show AddMonoidAlgebra.coeff (MvPolynomial.map (Int.castRingHom D.what₂.LL) P) m = _
    rw [MvPolynomial.coeff_map]
    simp
  · show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map D.what₂.embLL (MvPolynomial.map (Int.castRingHom D.what₂.LL) P)
    rw [MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]
  · rwa [hc (bVV K' (lamV D i) b) ⟨_, hxmem⟩ (by
      show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map σ' ((bVV K' (lamV D i) b : VV K' (lamV D i)) : Pol K' D.what₂.Tau (Vc D i).rank)
      rw [bVV_coe, hP, MvPolynomial.map_map, RingHom.ext_int (σ'.comp (Int.castRingHom K')) (Int.castRingHom ℂ)])]

end GlobalTheory.SeriesTie.RatNe

namespace GlobalTheory.SeriesTie.RatNe

set_option maxHeartbeats 2000000 in
open GlobalTheory.OneMapAll in
theorem exists_ser_rat_ne : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → IoExt Rl.toRealDat → ∀ (j : Fin D.R.m), OMPins T Rl.toRealDat κ v₀ O j → OneMapRow0 T Rl.toRealDat κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)), (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) ∧ (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧ h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl F κ v₀ O hnV hC hFW hIo j hP hrow hne c hc u hu
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow
  have hA1 : cuspOver (O j) (κ j) ≠ ⊥ := _root_.GlobalTheory.BaseChangeNonzero.cuspOver_ne_bot D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow hne
  obtain ⟨g0, ⟨hg0, x, hx, hsum⟩, hg0ne⟩ : ∃ g0 ∈ {g | g ∈ cuspOver (O j) (κ j) ∧ ∃ x, (O j).Plc () x ∧ IsSum (O j) () x g},
      g0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hA1 (eq_bot_iff.2 (hspan.trans ((Submodule.span_le).2 fun g hg => ?_)))
    rw [SetLike.mem_coe, hcon g hg]
    exact Submodule.zero_mem _
  have hrow' := hrow
  obtain ⟨cc, ph, hO⟩ := hrow'
  obtain ⟨-, ⟨-, -, -, hcc, hph, z, hz, hR⟩, -⟩ := hO
  obtain ⟨ze, -, ⟨m, hm, hze⟩, hR⟩ := hR ()
  have hid := (hR x hx).2 g0 ((mem_cusp _ _ _ _ _ _).1 hg0).1 hsum
  obtain ⟨q, hq⟩ : ∃ q, jFn (Wc D j) (inC (O j).c') (rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')))
      (O j).dict (O j).mu (actLev (O j).c' (O j).lev2 z g0) q ≠ 0 :=
    _root_.GlobalTheory.MovedUnifNe.exists_jFn_actLev_ne D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow g0 hg0 hg0ne z hz
  have hth : (O j).thAd () x q ≠ 0 := by
    intro h0
    have e := hid q
    rw [h0, mul_zero] at e
    have hze0 : ze ≠ 0 := fun h => by simp [h, hm.ne'] at hze
    have hcc0 : cc ((O j).dict q.out).1 ≠ 0 := fun h => by simpa [h] using hcc ((O j).dict q.out).1
    have hl : ((lieFac (T.toCore.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (κ j)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hze0 hcc0) hl) hq) e.symm
  obtain ⟨hLL, hPins⟩ := hP
  obtain ⟨hs, J', hRep, -, hTh, hPlc⟩ := (hPins.tuple ()).reps
  obtain ⟨x₀, hpl⟩ := (hPlc x).1 hx
  have e1 := hTh _ x hpl
  rw [e1] at hth
  have hv : (fun ρ => (u ρ : (Rl.toRealDat.MW j (sg0 D A3.A)).sm ρ)) = v₀ j (sg0 D A3.A) := funext hu
  have hcls := GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core D Γ Pl0 T0 A3.A T.Q.c.F Rl.toRealDat F hC j A3.A.μ0 (O j).c'.F
    (inC (O j).c') (O j).c0' ((O j).Cl' ()) hs ((O j).bad ()) J' ((O j).Lh ()) ((O j).gam ()) ((O j).vol ()) hPins.lift.std hRep
    _ x hpl u q.out
  rw [hv] at hcls
  change Rl.toRealDat.thF j A3.A.μ0 (jVx Rl.toRealDat j A3.A.μ0 x₀) (v₀ j (sg0 D A3.A)) q.out ≠ 0 at hth
  rw [hcls] at hth
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hth
  have hk' : ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u (hs k) ((O j).c0' (x k)) q.out ≠ 0 := right_ne_zero_of_mul hk
  have hsurj : Function.Surjective (O j).jL := by
    intro a
    have ha : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hLL ▸ a.2
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 ha
    refine ⟨y, Subtype.ext ?_⟩
    have := RingHom.congr_fun hPins.lift.field y
    exact this.trans hy
  let ψ : (O j).c'.F →+* D.what₂.LL := (RingEquiv.ofBijective (O j).jL ⟨(O j).jL.injective, hsurj⟩).symm.toRingHom
  obtain ⟨v, x', hv1, hv2, hv3⟩ := exists_rat_of_ser_ne Rl.toRealDat j A3.A.μ0 _ u (hs k) q.out (inC (O j).c') ψ (O j).c0' c hc
    (x k) hk'
  exact ⟨v, x', hs k, q.out, hv1, hv2, (hRep.2.2.2.2.2.2 k).1.1, hv3⟩

end GlobalTheory.SeriesTie.RatNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegers
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory

theorem exists_uniformiser_family_host :
    ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  intro D
  have h : ∀ PP : Pl D.host.E, ∃ x : 𝓞 D.host.E, x ∈ PP.asIdeal ∧ x ∉ PP.asIdeal ^ 2 := by
    intro PP
    have hlt : PP.asIdeal ^ 2 < PP.asIdeal :=
      Ideal.pow_lt_self _ PP.ne_bot PP.isPrime.ne_top 2 le_rfl
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  choose f hf using h
  exact ⟨f, hf⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FixBaseSmall

theorem host_mem (D : D7) (hgal : IsGalois ℚ D.LL0) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ x ∈ (embLL0 D).fieldRange := by
  let e : D.host.E →+* ↥D.LL0 := D.embE.codRestrict D.LL0 fun y => D.hostField_le_fixedField y
  have hsp := Normal.splits hgal.to_normal (e x)
  have hmin : minpoly ℚ (e x) = minpoly ℚ x := minpoly.algHom_eq e.toRatAlgHom e.injective x
  rw [hmin] at hsp
  have himg := Polynomial.Splits.image_rootSet hsp (embLL0 D).toRatAlgHom
  have hx : φ x ∈ (minpoly ℚ x).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x), ?_⟩
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom x (minpoly ℚ x)
    rw [minpoly.aeval, map_zero] at this
    exact this
  rw [← himg] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact ⟨y, hy⟩

theorem core_mem {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (hLaws : LawsJ T) (ha : AlgTie T) (j : Fin D.R.m) (a : T.Q.c.F) : (a : ℂ) ∈ (embLL0 D).fieldRange := by
  refine ⟨S.kKs ((YS.fi j).eK.symm a), ?_⟩
  have h1 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hLaws.pins.2.2.1
  change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm a) : ↥D.LL0) : D.what₂.LL) = (a : ℂ)
  rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h1 a

theorem three_le_mod (D : D7) : 3 ≤ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have h2 := D.host.pde_prime.two_le
  have h3 := D.host.pde'_prime.two_le
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
  omega

theorem fixesCurve_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : ℂ ≃+* ℂ)
    (N : ℕ) (hN : N ≠ 0) (h : GlobalTheory.CompRat.FixesCurve H τ N) : GlobalTheory.CompRat.FixesCurve H τ 1 := by
  obtain ⟨C, ι, hpb, hact⟩ := h
  refine ⟨C, ι, hpb, fun a => ?_⟩
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have key := hact ((N : ℤ) * a.1, (N : ℤ) * a.2)
  have e1 : GlobalTheory.CompRat.wC H ((N : ℤ) * a.1, (N : ℤ) * a.2) = (N : ℂ) * GlobalTheory.CompRat.wC H a := by
    simp only [GlobalTheory.CompRat.wC]; push_cast; ring
  rw [e1] at key
  have e2 : GlobalTheory.CompRat.wC H (1, 0) * ((N : ℂ) * GlobalTheory.CompRat.wC H a) / (N : ℂ) =
      GlobalTheory.CompRat.wC H (1, 0) * GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  have e3 : (N : ℂ) * GlobalTheory.CompRat.wC H a / (N : ℂ) = GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  rw [e2, e3] at key
  exact key

theorem curve_fix (hRF : GlobalTheory.NT.RayField) (D : D7) (T : CoreJ D) (hLaws : LawsJ T)
    (hRay : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1 := by
  set N := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' with hNdef
  have hN := three_le_mod D
  let Fc : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange
  let σ : Fc →+* ℂ := Fc.val.toRingHom
  have hRay' : RayIn D N σ.fieldRange := by
    obtain ⟨L, i1, i2, i3, i4, h1, jj, h2, h3⟩ := hRay
    refine ⟨L, i1, i2, i3, i4, h1, jj, h2, fun x => ?_⟩
    obtain ⟨y, hy⟩ := h3 x
    exact ⟨⟨jj x, ⟨y, hy⟩⟩, rfl⟩
  have hC := GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hLaws.pins.1 N hN Fc σ hRay'
  have hfix := hC τ fun z hz => by
    obtain ⟨y, hy⟩ := hz
    exact hτ z ⟨y, hy⟩
  exact fixesCurve_one T.Q.H τ N (by omega) hfix

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

theorem split_mem (D : D7) (C : Formalism.L2.Host.CharFrame D) (hV : Formalism.L2.Host.ValLL0 D C) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ∈ (embLL0 D).fieldRange := by
  have hu : (C.mu0 i).UnrAt P := (C.isMu0 i).unr P fun k hk => hP (by
    simp only [Formalism.L2.Host.OverP] at hk
    fin_cases k
    · push_cast; exact Ideal.mul_mem_right _ _ hk
    · push_cast; exact Ideal.mul_mem_left _ _ hk)
  have he : C.eta.UnrAt P := C.isEta.unr P
  obtain ⟨y1, hy1⟩ := hV.mu0 i P hu
  obtain ⟨y2, hy2⟩ := hV.eta P he
  refine ⟨y1 * y2⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hy1, hy2]
  have hN : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot)
  have hNn : (0 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero hNn]; exact hN
  have hc : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((1 / 2 : ℝ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hNn, Real.sqrt_eq_rpow,
      Real.rpow_neg hNn, Complex.ofReal_inv]
  have hval : (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) = (((C.mu0 i).val P : ℂˣ) : ℂ) * (((C.eta).val P : ℂˣ) : ℂ)⁻¹ := by
    show ((((C.mu0 i).val P * (C.eta.val P)⁻¹ : ℂˣ)) : ℂ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hval]
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one, hc]
  have hne : (((C.eta).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hs' : ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

theorem fixBase_of_fixes : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (τ : ℂ ≃+* ℂ), (∀ z ∈ (embLL0 D).fieldRange, τ z = z) → FixBase T Rl.toRealDat j τ := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ hLaws hCore hFW hTie hgal hVal hRay hroots j τ hτ
  refine ⟨fun a => hτ _ (core_mem T Rl cG S YS hLaws hTie.alg j a), fun φ x => hτ _ (host_mem D hgal φ x),
    curve_fix hRF D T hLaws hRay τ hτ, fun P hP => hτ _ (split_mem D Rl.C hVal j P hP),
    fun PP hPP x => hτ _ (_root_.GlobalTheory.TypeChar.chi_mem_smallField D Γ Pl0 I0 T0 A3 T Rl cG S YS F hLaws hCore hgal hVal hroots j PP hPP x)⟩

end GlobalTheory.FixBaseSmall
end
end

