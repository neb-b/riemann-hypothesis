module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Lean

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.CuspCoreDatumTransportOfSamePre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

theorem UpperTheory.cuspCoreDatum_transport_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∃ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
              HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  clear hmu hlaws hcore
  have key : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ),
      ∃ v : (R'.MW i σ).Vec, HEq v (z.geo.v₀ i (σ.comp ι)) := by
    intro i σ
    have hs := ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, -⟩, -⟩ := hs
    clear hR
    generalize R'.MW i σ = M' at h1 h2 h3 h4 h5 h6 h7 ⊢
    obtain @⟨H, nacg, ips, sg, lam, ep, fr, enum, ds, fu, fg⟩ := M'
    dsimp only at h1 h2 h3 h4 h5 h6 h7
    ( (
  have e : @Eq (type_of% (H)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).H) :))) (H) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H)) (H) ((((z.R.MW i (σ.comp ι)).H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
    ( (
  have e : @Eq (type_of% (nacg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).nacg) :))) (nacg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nacg)) (nacg) ((((z.R.MW i (σ.comp ι)).nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
    ( (
  have e : @Eq (type_of% (ips)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ips) :))) (ips) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ips)) (ips) ((((z.R.MW i (σ.comp ι)).ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
    ( (
  have e : @Eq (type_of% (sg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).σ) :))) (sg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (sg)) (sg) ((((z.R.MW i (σ.comp ι)).σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
    ( (
  have e : @Eq (type_of% (lam)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).lam) :))) (lam) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (lam)) (lam) ((((z.R.MW i (σ.comp ι)).lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
    ( (
  have e : @Eq (type_of% (ep)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ε) :))) (ep) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ep)) (ep) ((((z.R.MW i (σ.comp ι)).ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
    ( (
  have e : @Eq (type_of% (fr)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).fr) :))) (fr) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fr)) (fr) ((((z.R.MW i (σ.comp ι)).fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
    exact ⟨(by with_unfolding_all exact ((z.geo.v₀ i (σ.comp ι)) :)), (by with_unfolding_all exact ((HEq.refl (z.geo.v₀ i (σ.comp ι))) :))⟩
  choose v hv using key
  refine ⟨v, fun i i' hi σ' => ?_⟩
  have e : i = i' := Fin.ext hi
  subst e
  exact hv i σ'
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.CuspFormCoordsIdentificationOfSamePre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

private theorem exEquiv (LL LL' Ks C : Type) [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] (alg' : Algebra Ks LL')
    [AddCommGroup C] [Module Ks C]
    (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) (n n' : ℕ)
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK))
    (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x')
    (e : C ≃ₗ[Ks] WK) :
    ∃ e' : C ≃ₗ[Ks] WK', ∀ (φ : C) (φ' : C), HEq φ' φ → CrdOver ι (e φ).1 (e' φ').1 := by
  have hn : n = n' := (honto 0 WK'.zero_mem).choose_spec.1
  refine ⟨e.trans (GeoFW.baseChangeEquiv ι hι hn WK WK' hmem honto), fun φ φ' h => ?_⟩
  cases h
  exact GeoFW.baseChangeEquiv_crdOver ι hι hn WK WK' hmem honto (e φ)

private theorem moved (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T')
    (hPre : B'.toPre = B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt)
    (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL)
    (halg : ∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ))
    (hH : HEq core'.Q.H z.core.Q.H) (hl : HEq core'.Q.l z.core.Q.l) (hc : HEq core'.Q.c z.core.Q.c)
    (hDw : HEq core'.Q.Dw z.core.Q.Dw) (hXo : HEq core'.Q.Xo z.core.Q.Xo) (hU : HEq core'.U z.core.U)
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y)
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (k' : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1))
    (a1 : HEq k'.aP (z.geo.κ i).aP) (a2 : HEq k'.aM (z.geo.κ i).aM) (a3 : k'.n = (z.geo.κ i).n) (n' : ℕ) :
    letI := alg'; ∀ (WK' : Submodule core'.Q.c.F (Fin n' → (w'.st Z').toD7.what₂.LL)),
      (∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ (z.R.FW i).WK)) →
      (∀ x' ∈ WK', ∃ x : Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL, CrdOver ι x x') →
      ∃ e' : core'.cuspA ((i' : ℕ) + 1) (wtA k') k'.n ≃ₗ[core'.Q.c.F] WK',
        ∀ φ φ', HEq φ' φ → CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' φ' : WK').1 := by
  intro WK' hmem honto
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((@Fin.ext _ i ((i')) ((hii))) : _))
  clear hii
  subst e
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  dsimp only at hH hl hc hDw hXo hU
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((z.core.Q.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((z.core.Q.H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((z.core.Q.l) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((z.core.Q.l))) (((hl)))).symm : _))
  clear (hl)
  subst e))
  ( (
  have e : @Eq (type_of% (c')) ((by with_unfolding_all exact ((z.core.Q.c) :))) (c') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (c')) (c') (((z.core.Q.c))) (((hc)))).symm : _))
  clear (hc)
  subst e))
  ( (
  have e : @Eq (type_of% (Dw')) ((by with_unfolding_all exact ((z.core.Q.Dw) :))) (Dw') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Dw')) (Dw') (((z.core.Q.Dw))) (((hDw)))).symm : _))
  clear (hDw)
  subst e))
  ( (
  have e : @Eq (type_of% (Xo')) ((by with_unfolding_all exact ((z.core.Q.Xo) :))) (Xo') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Xo')) (Xo') (((z.core.Q.Xo))) (((hXo)))).symm : _))
  clear (hXo)
  subst e))
  ( (
  have e : @Eq (type_of% (U')) ((by with_unfolding_all exact ((z.core.U) :))) (U') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (U')) (U') (((z.core.U))) (((hU)))).symm : _))
  clear (hU)
  subst e))
  obtain ⟨aP, aM, hP, hM, nn, hnn⟩ := k'
  dsimp only at a1 a2 a3
  ( (
  have e : @Eq (type_of% (aP)) ((by with_unfolding_all exact (((z.geo.κ i).aP) :))) (aP) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (aP)) (aP) ((((z.geo.κ i).aP))) (((a1)))).symm : _))
  clear (a1)
  subst e))
  ( (
  have e : @Eq (type_of% (aM)) ((by with_unfolding_all exact (((z.geo.κ i).aM) :))) (aM) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (aM)) (aM) ((((z.geo.κ i).aM))) (((a2)))).symm : _))
  clear (a2)
  subst e))
  subst a3
  letI := z.alg
  have halg2 : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) =
      @algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ ((by with_unfolding_all exact (alg' :))) y := fun y =>
    (w'.st Z').toD7.what₂.embLL.injective ((hι _).trans ((by with_unfolding_all exact (((z.alg_eq y).trans ((by with_unfolding_all exact ((halg ((y))).symm : _))) : _ = (w'.st Z').toD7.what₂.embLL (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ ((by with_unfolding_all exact (alg' :))) y)) :))))
  exact (by with_unfolding_all exact ((exEquiv (w.st Z).toD7.what₂.LL (w'.st Z').toD7.what₂.LL z.core.Q.c.F
    (z.core.cuspA ((i : ℕ) + 1) (wtA (z.geo.κ i)) (z.geo.κ i).n) ((by with_unfolding_all exact (alg' :))) ι ((by with_unfolding_all exact (halg2 :))) (z.R.nW i) n'
    (z.R.FW i).WK ((by with_unfolding_all exact (WK' :))) ((by with_unfolding_all exact (hmem :))) ((by with_unfolding_all exact (honto :))) (z.geo.fw.e i)) :))

private theorem exIdx (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T')
    (hPre : B'.toPre = B.toPre) (Z : w.Lt) (Z' : w'.Lt) (i' : Fin (w'.st Z').toD7.R.m) :
    ∃ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i' := by
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  exact (by with_unfolding_all exact ((⟨i', rfl⟩ : ∃ i : Fin (w'.st Z').toD7.R.m, (i : ℕ) = i') :))

theorem UpperTheory.cuspFormCoords_identification_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
          ∃ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι κ' hκ
  have h0 := fun i i' hii => ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.1
  have key := fun i i' hii => moved B B' f f' T T' w w' hPre Z hX Wt z Z' core' alg' halg hcore.1 hcore.2.1 hcore.2.2.1
    hcore.2.2.2.1 hcore.2.2.2.2.1 hcore.2.2.2.2.2.1 ι hι i i' hii (κ' i') (hκ i i' hii).1 (hκ i i' hii).2.1 (hκ i i' hii).2.2
    (R'.nW i') (R'.FW i').WK (h0 i i' hii).1 (h0 i i' hii).2
  have hex := exIdx B B' f f' T T' w w' hPre Z Z'
  refine ⟨fun i' => (key _ i' (hex i').choose_spec).choose, fun i i' hii => ?_⟩
  have hi : (hex i').choose = i := Fin.ext ((hex i').choose_spec.trans hii.symm)
  subst hi
  exact (key _ i' (hex i').choose_spec).choose_spec
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.ExtVecPairingIndepOfBaseSamePre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section

private def UpperTheory.HasUnitPureTensorPairing {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S) {V : HSp D} (c : CoefA V)
    {P : Type} [AddCommGroup P] [Module ℂ P] (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] P) (Δ : P) (v : M.Vec) : Prop :=
  ∃ (u : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, (u ρ : M.sm ρ) = v ρ) ∧ ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ u) w = Δ

private theorem UpperTheory.isExtVec_of_same_model {D : D7} {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S')
    (hMM : GeoTies.ModelSame M M') (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : IsExtVec M v → IsExtVec M' v' := by
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  exact id

private theorem UpperTheory.hasUnitPureTensorPairing_imp_of_heq {D : D7} {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S')
    (hMM : GeoTies.ModelSame M M') (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) {V : HSp D} (c c' : CoefA V)
    (h1 : HEq c'.W c.W) (h2 : HEq c'.nW c.nW) (h3 : HEq c'.iW c.iW)
    {P : Type} [AddCommGroup P] [Module ℂ P] (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] P) (io' : LowT M' →ₗ[ℂ] c'.W →ₗ[ℂ] P)
    (hio : HEq io' io) (Δ : P) :
    ((∃ u, IsExtVec M u ∧ UpperTheory.HasUnitPureTensorPairing M c io Δ u) → UpperTheory.HasUnitPureTensorPairing M c io Δ v) →
      ((∃ u, IsExtVec M' u ∧ UpperTheory.HasUnitPureTensorPairing M' c' io' Δ u) → UpperTheory.HasUnitPureTensorPairing M' c' io' Δ v') := by
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  obtain ⟨Y, ρ⟩ := c
  obtain ⟨Y', ρ'⟩ := c'
  dsimp only at h1 h2 h3
  cases h1
  cases h2
  cases h3
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  have hio' : io' = io := eq_of_heq hio
  subst hio'
  exact id

end

theorem UpperTheory.extVecPairing_indep_of_base_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
              HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) →
          ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), Formalism.IndefR.FWT.IsChosenExtremalVector R'.toRealDat i σ (v₀' i σ) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι v₀' hv i' σ'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb := z.geo.fw.hv₀ i (σ'.comp ι)
  have hall := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  have hcl := (hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hMM : GeoTies.ModelSame (z.R.MW i (σ'.comp ι)) (R'.MW i' σ') :=
    ⟨hcl.1.1, hcl.1.2.1, hcl.1.2.2.1, hcl.1.2.2.2.1, hcl.1.2.2.2.2.1, hcl.1.2.2.2.2.2.1, hcl.1.2.2.2.2.2.2.1⟩
  have c1 := hall.1
  have c2 := hall.2.2.1
  have c3 := hall.2.2.2.1
  have hio := hall.2.2.2.2.2.1
  have hv1 := hv i i' hi σ'
  have hs' : sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A = (w'.st Z').toD7.what₂.embLL :=
    sgAt_mk _ R'.toRealDat.hv0
  have hs : sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
    sgAt_mk _ z.R.toRealDat.hv0
  clear hcl hall hRS hv hc halg
  generalize v₀' i' σ' = v' at hv1 ⊢
  generalize z.geo.v₀ i (σ'.comp ι) = v at hv1 hb
  have hσ : σ' = sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A →
      σ'.comp ι = sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A := fun h => by
    rw [h, hs', hs]
    exact RingHom.ext hι
  generalize σ'.comp ι = s at hMM v hv1 hb hσ
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) s) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i s).H :))) ((by with_unfolding_all exact ((z.R.MW i s).nacg :))) ((by with_unfolding_all exact ((z.R.MW i s).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i s).σ :))) ((by with_unfolding_all exact ((z.R.MW i s).lam :))) ((by with_unfolding_all exact ((z.R.MW i s).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i s).fr :))) ((by with_unfolding_all exact ((z.R.MW i s).enum :))) ((by with_unfolding_all exact ((z.R.MW i s).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i s).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i s).fr_gram :)))
  let u₀ : M₀.Vec := (by with_unfolding_all exact (v :))
  refine ⟨UpperTheory.isExtVec_of_same_model M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :))) u₀ v' ((by with_unfolding_all exact (hv1 :))) ((by with_unfolding_all exact (hb.1 :))), fun h => ?_⟩
  have h0 := hσ h
  have hb2 := hb.2 h0
  subst h
  subst h0
  let c₀ : CoefA (Vc (w'.st Z').toD7 i') :=
    @CoefA.mk _ _ (z.R.cV i).W (z.R.cV i).nW (z.R.cV i).iW (z.R.cV i).fW ((by with_unfolding_all exact ((z.R.cV i).ρ :)))
  let io₀ : LowT M₀ →ₗ[ℂ] c₀.W →ₗ[ℂ] PolF (w'.st Z').toD7 (Wc (w'.st Z').toD7 i').rank (Vc (w'.st Z').toD7 i').rank :=
    (by with_unfolding_all exact ((z.R.ioP i) :))
  exact (by with_unfolding_all exact ((UpperTheory.hasUnitPureTensorPairing_imp_of_heq M₀ (R'.MW i' _) ((hMM)) u₀ v' ((hv1)) c₀ (R'.cV i') ((c1)) ((c2)) ((c3))
    io₀ (R'.ioP i') ((hio)) (RealDat.Delta i') ((hb2))) : _))
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.PointEquivFamilyTransportOfSamePre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

private theorem ex_equiv_moved {m : ℕ} {L : Type} (P P' Q : Fin m → L → Type) (h : ∀ i, HEq (P' i) (P i))
    (e : ∀ i la, P i la ≃ Q i la) :
    ∃ e' : ∀ i la, P' i la ≃ Q i la, ∀ (i i' : Fin m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
      HEq (e' i' la' y') (e i la y) := by
  obtain rfl : P' = P := funext fun i => eq_of_heq (h i)
  refine ⟨e, fun i i' hi la la' hla y' y hy => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  cases hla
  cases hy
  rfl

theorem UpperTheory.pointEquiv_family_transport_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∃ (pt' : ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)), (R'.FW i).Pt la ≃ core'.PtM ((i : ℕ) + 1) la),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
              HEq (pt' i' la' y') (z.geo.fw.pt i la y)) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hH hL Xg tr R' hR hmu ι hι
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hH
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := core'
  have e1 : H = z.core.Q.H := eq_of_heq h1; subst e1
  have e2 : l = z.core.Q.l := eq_of_heq h2; subst e2
  have e3 : c = z.core.Q.c := eq_of_heq h3; subst e3
  have e4 : Dw = z.core.Q.Dw := eq_of_heq h4; subst e4
  have e5 : Xo = z.core.Q.Xo := eq_of_heq h5; subst e5
  letI := z.alg
  exact (by with_unfolding_all exact (ex_equiv_moved (fun i => (z.R.FW i).Pt) (fun i => (R'.FW i).Pt) (fun i la => z.core.PtM ((i : ℕ) + 1) la)
    (fun i => ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.2.2.2.1) z.geo.fw.pt :))
end

