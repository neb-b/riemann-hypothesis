module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
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
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)

theorem GlobalTheory.PlaceRead.evaluates_of_lunif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : Formalism.L2.Pj.CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugationScaledCoordsIntegralFormsTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceConj

theorem conj_lat : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  intro D j B hB hlam Φ κ hκ0 hval hκ τ hτ ψ ψ' hψ hψ' hcc hf
  have huq := GlobalTheory.CoefLatConj.existsUnique_eq Φ hB hlam hκ0 hval hκ
  have hinj : Function.Injective Φ := fun x y hxy => (huq (Φ x) (hval x)).unique rfl hxy
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hinj)
  have hπx : ∀ x, π (Φ x) = x := fun x => LinearMap.congr_fun hπ x
  have hπv : ∀ P ∈ B.valSpace, Φ (π P) = P := fun P hP => by
    obtain ⟨x, rfl, -⟩ := huq P hP
    rw [hπx]
  let C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j :=
    { toFun := fun F h => Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)))
      map_add' := fun F G => by
        funext h
        simp only [Pi.add_apply, map_add (f := _), smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Pi.smul_apply, map_smul, map_smulₛₗ, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hC : ∀ F h, C F h = Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h))) := fun _ _ => rfl
  have hconjAt : ∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) := fun F hF h =>
    ⟨π (F h), GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)), rfl, (hπv _ (hF h)).symm, hC F h⟩
  refine ⟨C, fun F hF => ⟨hconjAt F hF, fun h0 => ?_⟩, fun O hO => ?_⟩
  · funext h
    have e := congrFun h0 h
    rw [hC, Pi.zero_apply, ← map_zero Φ] at e
    have e1 := hinj e
    have hc : τ κ / κ ≠ 0 := div_ne_zero ((map_ne_zero _).2 hκ0) hκ0
    rw [smul_eq_zero] at e1
    have e2 : π (F h) = 0 := by
      rcases e1 with e1 | e1
      · exact absurd e1 hc
      · have := congrArg (GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j)) e1
        rwa [GlobalTheory.CoefLatConj.mapVV_symm_mapVV, map_zero] at this
    rw [Pi.zero_apply, ← hπv _ (hF h), e2, map_zero]
  · have hτ' : ∀ a, τ.symm (embLL0 D a) = embLL0 D a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hO' : IsCoefRing (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) :=
      ⟨hO.emb, fun a => Subring.mem_map.2 ⟨_, hO.int a, hτ _⟩⟩
    have hOO : (O.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = O := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    ext F'
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hFv : ∀ h, F h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF).1).1
      exact GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) O hO τ hτ ψ ψ' hψ hψ' hcc hf
        F (C F) (hconjAt F hFv) hF
    · intro hF'
      have hF'v : ∀ h, F' h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF').1).1
      let F : Amb D j := fun h => Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))
      have hFm : F ∈ B.mtLat (embLL0 D) (labLL0 D) O ψ := by
        have key := GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) hO'
          τ.symm hτ' ψ' ψ hψ' hψ hcc.symm hf.symm F' F
          (fun h => ⟨π (F' h), GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)), rfl, (hπv _ (hF'v h)).symm, rfl⟩) hF'
        rwa [hOO] at key
      refine ⟨F, hFm, funext fun h => ?_⟩
      rw [hC]
      change Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j)
        (π (Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))))) = F' h
      rw [hπx, map_smulₛₗ (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j))]
      have e3 := GlobalTheory.CoefLatConj.mapVV_symm_mapVV (lamV D j) τ.symm (π (F' h))
      rw [RingEquiv.symm_symm] at e3
      rw [e3, smul_smul]
      have : τ κ / κ * (τ (τ.symm κ / κ)) = 1 := by
        rw [map_div₀, RingEquiv.apply_symm_apply]
        have : τ κ ≠ 0 := (map_ne_zero _).2 hκ0
        field_simp
      rw [RingHom.coe_coe, this, one_smul, hπv _ (hF'v h)]

end GlobalTheory.PlaceConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSbLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_sb_raw (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (YS : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG (ratDatR Rl cG kKs hk) YS)
    (hX : NExpHeckeRowX Rl cG _ YS H fun _ => LinearMap.id) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hne : Nonempty D.ntw.Tw)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) :
    ∃ Sb' : Finset (PlE D.host), Sb ⊆ Sb' ∧ (∀ i, Sb' ⊆ D.ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low D Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd Rl cG kKs hk Sb' H.hL := by
  classical
  obtain ⟨i₀⟩ := hne
  refine ⟨(D.ntw.S0 i₀).filter (fun P => ∀ i, P ∈ D.ntw.S0 i), fun P hP => Finset.mem_filter.2 ⟨hSb i₀ hP, fun i => hSb i hP⟩,
    fun i P hP => (Finset.mem_filter.1 hP).2 i, ?_, ?_⟩
  · intro P hP
    have hall : ∀ i, P ∈ D.ntw.S0 i := by
      intro i
      rw [Nat.cast_mul, Nat.cast_mul] at hP
      rcases P.isPrime.mem_or_mem hP with h | h
      · exact hS02 i h
      · rcases P.isPrime.mem_or_mem h with h | h
        · exact D.ntw.placesOver_subset_exceptional i 0 h
        · exact D.ntw.placesOver_subset_exceptional i 1 h
    exact Finset.mem_filter.2 ⟨hall i₀, hall⟩
  · intro j k P α Rr h1 h2 hd x
    have hi' : ∃ i', P ∉ D.ntw.S0 i' := by
      by_contra hc
      push_neg at hc
      exact hd.offS (Finset.mem_filter.2 ⟨hc i₀, hc⟩)
    obtain ⟨i', hi'⟩ := hi'
    obtain ⟨-, -, -, -, hso, -, -, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i') Rl.Sb P (hS0c i') (hS02 i') (hS0b i') hd.split hi'
    have hj : (idxOf D j : ℕ) + 1 = j := by simp only [idxOf]; omega
    let y : (ratDatR Rl cG kKs hk).WL ((idxOf D j : ℕ) + 1) := (YS.fi (idxOf D j)).e.symm x
    have hy : (YS.fi (idxOf D j)).e y = x := LinearEquiv.apply_symm_apply _ _
    have key : ∀ n (hn : n = j) (z : (ratDatR Rl cG kKs hk).WL n), HEq z x → HEq (H.hL n k P z) (H.hL j k P x) := by
      intro n hn z hz
      subst hn
      rw [eq_of_heq hz]
    have h3 : HEq ((YS.fi (idxOf D j)).e (H.hL ((idxOf D j : ℕ) + 1) k P y)) (H.hL j k P x) :=
      (hfi _ _).trans (key _ hj y ((hy ▸ hfi _ y).symm))
    have ht := hX.tie (idxOf D j) k P hd.split hso ⟨i', hi'⟩ hd.odd hd.le α Rr hd.elt hd.reps y rfl
    rw [eq_of_heq h3, hy] at ht
    exact ht

end Raw

end GlobalTheory.HeckeSbLayer

namespace GlobalTheory.HeckeSbLayer

end GlobalTheory.HeckeSbLayer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem exists_extend_fractionRing {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (e : FractionRing A →+* ℂ) :
    ∃ ε : FractionRing B →+* ℂ, ε.comp (algebraMap A (FractionRing B)) = e.comp (algebraMap A (FractionRing A)) := by
  letI : Algebra A ℂ := (e.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2
    (e.injective.comp (IsFractionRing.injective A (FractionRing A)))
  haveI : FaithfulSMul A (FractionRing B) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B _
  let φ : FractionRing B →ₐ[A] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem exists_extends_and_emb : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  intro D c w ρ hρ
  haveI := c.Oe_fin w
  refine ⟨exists_extend_fractionRing (c.Oe_inj w) (ρ.ek (c.twI w) (c.sd w) (c.k' w)), fun hT ε hε x => ?_⟩
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w))
    ((if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have h0 : (if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x * algebraMap _ _ z = algebraMap _ _ y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have h1 := congrArg ε (hT.embedding_baseField_condition w x y z hz0 h0)
  have key : ∀ t : D.ntw.O (c.twI w), ε (algebraMap (c.Oe w) (FractionRing (c.Oe w))
      (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap _ (D.ntw.Ok (c.twI w) (c.k' w)) t))) =
      ρ.eO (c.twI w) (c.sd w) t := fun t => by
    rw [← IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), hε.apply, hρ.ek_e]
  rw [map_mul, key, key] at h1
  rw [← hρ.e_LL0 (c.twI w) (c.sd w) x]
  let m : FractionRing (D.ntw.O0 (c.twI w)) →+* FractionRing (D.ntw.O (c.twI w)) := IsFractionRing.map (D.ntw.O_inj (c.twI w))
  have hm : ∀ t, ρ.e (c.twI w) (c.sd w) (m (algebraMap _ _ t)) =
      ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) t) := fun t =>
    congrArg (ρ.e (c.twI w) (c.sd w)) (IsLocalization.map_eq _ t)
  have h2 := congrArg (fun t => ρ.e (c.twI w) (c.sd w) (m t)) h0
  simp only [map_mul, hm] at h2
  have hne : ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) ≠ 0 := by
    rw [← hm]
    exact (map_ne_zero _).2 ((map_ne_zero m).2 hz1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end GlobalTheory.PlaceRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfUniformiserFrameMatrixPrescribedReduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HalfFrameLift

theorem exists_half_redM_frMapO : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP), ∃ u : WO S T, IsHalf e u ∧ IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP := by
  intro D S T βS βT Q e he ϖ hϖ y
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  subst hsum
  choose N hN hNe hNr using fun (i : Fin T.rank) (j : Fin S.rank) =>
    _root_.GlobalTheory.IdemResLift.exists_int_lift D Q es hes hc (fun PP => y PP i j)
  set e := ∑ PP ∈ Q, es PP with he_def
  let z : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of N
  let A : Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
    ((βT.val : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) * z : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) *
      ((βS⁻¹).val : Matrix (Fin S.rank) (Fin S.rank) (EAf D))
  choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (A i j)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hinv : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ', map_one]
  let u : WO S T := Matrix.of fun i j => e * incA D (ϖ : D.host.E)⁻¹ * w i j
  have key : frMapO S T βS βT (u.map fun v => incA D (ϖ : D.host.E) * v) = z := by
    have hmap : (u.map fun v => incA D (ϖ : D.host.E) * v).map (toEAf D) = toEAf D e • A := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, u, Matrix.of_apply]
      rw [← hw i j, ← map_mul]
      congr 1
      linear_combination (e * w i j) * hinv
    unfold frMapO
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, z, Matrix.of_apply]
    exact hNe i j
  refine ⟨u, fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · show e * (e * incA D (ϖ : D.host.E)⁻¹ * w i j) = e * incA D (ϖ : D.host.E)⁻¹ * w i j
    rw [← mul_assoc, ← mul_assoc, hee]
  · rw [key]; exact fun i j => hN i j
  · rw [key]
    funext i j
    exact (dif_pos (hN i j)).trans (hNr i j PP hPP)

end GlobalTheory.HalfFrameLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem unit_of_unitOff : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  intro O _ _ _ ε N t hN ⟨ht0, n, h1, h2⟩
  have hε : Function.Injective ε := ε.injective
  have key : ∀ s : FractionRing O, IsIntegral ℤ (ε s) → ∃ a : O, algebraMap O (FractionRing O) a = s := by
    intro s hs
    letI : Algebra ℤ (FractionRing O) := Ring.toIntAlgebra _
    have hs' : IsIntegral ℤ s := (isIntegral_algHom_iff (ε.toIntAlgHom) hε).mp hs
    have hO : IsIntegral O s := by
      have := IsIntegral.map_of_comp_eq (Int.castRingHom O) (RingHom.id (FractionRing O)) (RingHom.ext_int _ _) hs'
      simpa using this
    exact IsIntegrallyClosed.isIntegral_iff.mp hO
  have ht : t ≠ 0 := by rintro rfl; simp at ht0
  obtain ⟨a, ha⟩ := key (((N : FractionRing O)) ^ n * t) (by simpa [map_mul, map_pow, map_natCast] using h1)
  obtain ⟨b, hb⟩ := key (((N : FractionRing O)) ^ n * t⁻¹) (by simpa [map_mul, map_pow, map_natCast, map_inv₀] using h2)
  have hN' : (N : FractionRing O) ≠ 0 := by
    have := (hN.map (algebraMap O (FractionRing O))).ne_zero
    simpa using this
  have hab : a * b = (N : O) ^ (2 * n) := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_pow, map_natCast]
    field_simp
    ring
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ hN.pow _)
  have hinv : algebraMap O (FractionRing O) ((hN.unit⁻¹ : Oˣ) : O) = (N : FractionRing O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (FractionRing O)) N, ← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨hua.unit * hN.unit⁻¹ ^ n, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, hinv, ha]
  rw [mul_comm (_ ^ n) t, mul_assoc, ← mul_pow, mul_inv_cancel₀ hN', one_pow, mul_one]

end GlobalTheory.PlaceRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceFix

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

end GlobalTheory.PlaceFix
end

