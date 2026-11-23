module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Transport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.Places

theorem sel_eq_of_conj {X : Formalism.L2.Col.Fields} (hX : X.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hs : Formalism.L2.Col.IsSel X sel) {u u' : HeightOneSpectrum (𝓞 X.F)}
    (h : letI := X.starE; ∀ c ∈ (sel u).asIdeal, ∃ c' ∈ (sel u').asIdeal, (c' : X.E) = star (c : X.E)) : sel u = sel u' := by
  have hle : u.asIdeal ≤ u'.asIdeal := fun y hy => by
    rw [← hs u] at hy
    rw [← hs u']
    obtain ⟨c', hc', e⟩ := h _ hy
    have : c' = algebraMap (𝓞 X.F) (𝓞 X.E) y := RingOfIntegers.ext (e.trans (hX.star_F (y : X.F)))
    rw [this] at hc'
    exact hc'
  rw [HeightOneSpectrum.ext (u.isMaximal.eq_of_le u'.isPrime.ne_top hle)]

theorem unrAt_mul_iff {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v ↔ χ.UnrAt v :=
  forall₂_congr fun x hx => by
    change (χ.loc v x * χ'.loc v x = 1 ↔ χ.loc v x = 1)
    rw [h' x hx, mul_one]

def delAt {P : Pre} (f : Top.Fr P) (n : ℕ) : HChar P.host.E := if n = P.host.pde then f.del' else f.del

def OverDel {P : Pre} (Q : HeightOneSpectrum (𝓞 P.host.E)) : Prop :=
  ((P.host.pde : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ((P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal

theorem unrAt_xiTw_iff {B : Base} (T : TwDat B) (f : Top.Fr B.toPre) (v : B.places.Pl) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : OverDel (P := B.toPre) Q) : (T.xiTw f v).UnrAt Q ↔ (delAt f (B.places.resChar v)).UnrAt Q := by
  refine unrAt_mul_iff ?_
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := (T.psi_tw v).2.2.2 Q h
  rcases hQ with hQ | hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde
    · exact hnot (Or.inr (Or.inr (Or.inl e)))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde_prime e (Ideal.absNorm_mem _) hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde'
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde'_prime e (Ideal.absNorm_mem _) hQ

theorem transport {P P' : Pre} (h : P' = P) {f : Top.Fr P} {f' : Top.Fr P'} (hf : HEq f' f)
    {sel : HeightOneSpectrum (𝓞 P.host.F) → HeightOneSpectrum (𝓞 P.host.E)}
    {sel' : HeightOneSpectrum (𝓞 P'.host.F) → HeightOneSpectrum (𝓞 P'.host.E)} (hs : HEq sel' sel) (n : ℕ)
    {Q' : HeightOneSpectrum (𝓞 P'.host.E)} (h1 : OverDel Q') (h2 : ¬ (delAt f' n).UnrAt Q') (h3 : ∃ u, sel' u = Q') :
    ∃ Q : HeightOneSpectrum (𝓞 P.host.E), HEq Q Q' ∧ OverDel Q ∧ ¬ (delAt f n).UnrAt Q ∧ ∃ u, sel u = Q := by
  subst h
  cases hf
  cases hs
  exact ⟨Q', HEq.rfl, h1, h2, h3⟩

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem exists_of_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {t : TupU w.I (usedOf w.I T Wt)} {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : Q ∈ z.R.Q t) : (∃ v ∈ Wt, ¬ (T.xiTw f v).UnrAt Q) ∧ ∃ u, w.I.sel u = Q := by
  have hr := (z.lev.is.Q_ram t Q).2 (Or.inl hQ)
  have hq : Q ∈ w.I.Q (ixOf w.I (usedOf w.I T Wt) t) := (iff_of_eq (congrArg (Q ∈ ·) (z.lev.Q t))).1 hQ
  refine ⟨?_, (w.I.exists_of_mem_Q hq).imp fun u hu => hu.2.1⟩
  rcases (mem_range_ixOf w.I).1 ⟨t, rfl⟩ with h | ⟨v, hv, h⟩
  · rw [h, w.I.twistPrimes_reference_tuple_eq_empty] at hq
    exact absurd hq (Finset.notMem_empty _)
  · refine ⟨v, hv, fun hu => hr ?_⟩
    have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans (h.trans (congrArg (T.xiTw · v) w.C_eq))
    exact (iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).2 hu

theorem exists_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {v : B.places.Pl} (hv : v ∈ Wt) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hr : ¬ (T.xiTw f v).UnrAt Q) (hu : ∃ u, w.I.sel u = Q) : ∃ t, Q ∈ z.R.Q t := by
  obtain ⟨a, ha⟩ : T.xiTw f v ∈ Set.range w.I.xi := by
    rw [w.xi_range]
    exact Or.inr ⟨v, rfl⟩
  obtain ⟨t, ht⟩ := (mem_range_ixOf w.I (U := usedOf w.I T Wt) (a := a)).2
    (Or.inr ⟨v, hv, ha.trans (congrArg (T.xiTw · v) w.C_eq.symm)⟩)
  have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans ((congrArg w.I.xi ht).trans ha)
  refine ⟨t, ?_⟩
  rcases (z.lev.is.Q_ram t Q).1 (fun h => hr ((iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).1 h)) with
    h | ⟨Q₁, h, hc⟩
  · exact h
  · obtain ⟨u₁, -, rfl, -⟩ := w.I.exists_of_mem_Q ((iff_of_eq (congrArg (Q₁ ∈ ·) (z.lev.Q t))).1 h)
    obtain ⟨u, rfl⟩ := hu
    exact (iff_of_eq (congrArg (· ∈ z.R.Q t) (sel_eq_of_conj hX w.ok.sel_ok hc))).1 h

theorem plCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), PlCl (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' i' t' Q' hQ hD
  have h1 : Q' ∈ x'.m.z.R.Q t' := hQ
  obtain ⟨⟨v', hv', hr⟩, hu⟩ := exists_of_mem_Q x'.m.z h1
  have hD' : OverDel (P := B'.toPre) Q' := by
    have h2 := (iff_of_eq (congrArg (Q' ∈ ·) ((Dof x').ntw.pD_eq i'))).1 hD
    split_ifs at h2
    · exact Or.inr h2
    · exact Or.inl h2
  obtain ⟨Q, hh, h2, h3, h4⟩ := transport l.enl.1 l.fr l.sel (B'.places.resChar v') hD'
    (fun h => hr ((unrAt_xiTw_iff T' f' v' hD').2 h)) hu
  rw [← GlobalTheory.Mem.Top.TwChar.resChar_plUnder l.enl v'] at h3
  obtain ⟨t, ht⟩ := exists_mem_Q x.m.z ((GlobalTheory.HeightCounting.Up.CopyEx.mem_Wt_iff l.enl l.ext v').2 hv')
    (fun h => h3 ((unrAt_xiTw_iff T f _ h2).1 h)) h4
  exact ⟨t, Q, ht, hh⟩

end GlobalTheory.HeightCounting.SerMove.Places

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedEqDatTw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Mem.R3

theorem dat_ext_heq {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {d₁ d₂ : Dat X I hX T Wt} (hXg : d₁.Xg = d₂.Xg) (htr : d₁.tr = d₂.tr)
    (hcore : d₁.core = d₂.core) (hR : HEq d₁.R d₂.R) (hcG : HEq d₁.cG d₂.cG) (hgeo : HEq d₁.geo d₂.geo) : d₁ = d₂ := by
  cases d₁ with
  | @mk Xg tr core alg alg_eq R cG geo pins lev idG good mu fieldValues_mem_fixedField Ks_le =>
  cases d₂ with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le_LL0' Ks_le' =>
  dsimp only at hXg htr hcore hR hcG hgeo
  subst hXg htr hcore
  have halg : alg = alg' := Algebra.algebra_ext _ _ fun y => X.B.embLL.injective ((alg_eq y).trans (alg_eq' y).symm)
  subst halg
  cases eq_of_heq hR
  cases eq_of_heq hcG
  cases eq_of_heq hgeo
  rfl

end GlobalTheory.Mem.R3

namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw

theorem coreJ_coreJ {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) (T : Formalism.L2.Pj.CoreJ a.D) :
    coreJ (a := b) c (coreJ b T) = coreJ c T := (by with_unfolding_all exact ((Eq.refl (coreJ c T)) :))

theorem moved_eq_datTw : ∀ {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T} {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (N : TwNew (GlobalTheory.HeightCounting.Up.Dof x)) (m : GlobalTheory.Mem.R3.Rw.Moved (GlobalTheory.HeightCounting.Up.oTw x N)), m.Copy → HEq m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq m.z.cG x.m.z.cG → HEq m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → m.z = GlobalTheory.HeightCounting.Up.datTw x N := by
  intro K B f T w P x N m hc hR hcG hgeo
  have h1 : x.m.z.core = coreJ (a := P.Z₀) x.o.Z P.z.core := (by with_unfolding_all exact ((eq_of_heq x.copy.core) :))
  have h2 : m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core := (by with_unfolding_all exact ((eq_of_heq hc.core) :))
  have h3 : coreJ (a := x.o.Z) (oTw x N).Z x.m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core :=
    (congrArg (coreJ (a := x.o.Z) (oTw x N).Z) h1).trans (coreJ_coreJ _ _ _)
  have h4 : HEq (datTw x N).cG x.m.z.cG := (by with_unfolding_all exact ((HEq.refl x.m.z.cG) :))
  exact dat_ext_heq (d₁ := m.z) (d₂ := datTw x N) ((by with_unfolding_all exact ((m.Xg.trans x.m.Xg.symm) :))) ((by with_unfolding_all exact ((m.tr.trans x.m.tr.symm) :)))
    ((by with_unfolding_all exact ((h2.trans h3.symm) :))) ((by with_unfolding_all exact (hR :))) (hcG.trans h4.symm) ((by with_unfolding_all exact (hgeo :)))

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

section Gen

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem eigAd_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {Sb eig} (h : EigAd Y Sb eig)
    (v : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) → (R.HW i (sg0 D A3.A)).H) (H : ∀ i y, Y.mj.eW i y = v i y)
    (i : Fin D.R.m) (σ k P α Rr) (hd : HkDat R Sb i k P α Rr) (hg : D.nd.goodRow σ) (y) (hy : y ∈ D.what₂.isot (i.1 + 1) σ) :
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (v i y)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (v i y) := by
  rw [← H]
  exact h i σ k P α Rr hd hg y hy

end Gen

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}

abbrev RdTw (x : St P) (N : TwNew (Dof x)) : Type 1 :=
  R3.Read (datTw x N).R.toRealDat (datTw x N).F.lv2 (sideTw x N).p0

def jMtB (Y : RdTw x N) (μ h i y) : type_of% (x.r.Y.IL.jMt μ h i y).1 := (by with_unfolding_all exact ((Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))

def mtAd (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) {M : MtFam (Dof x)} (a : MtAd x.r.Y M) :
    MtAd Y ((fun μ j h1 h2 => { M μ j h1 h2 with })) where
  PV i := ⟨(by with_unfolding_all exact ((a.PV ((i))).ψ : _)), (by with_unfolding_all exact ((a.PV ((i))).inj : _)), (by with_unfolding_all exact ((a.PV ((i))).into : _)), (by with_unfolding_all exact ((a.PV ((i))).onto : _))⟩
  std := (by with_unfolding_all exact (a.std :))
  eW := (by with_unfolding_all exact (a.eW :))
  read μ h i y g := (by with_unfolding_all exact (((a.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))).trans
    (congrFun (H ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (((a.PV ((i))).ψ ((g))) : _))))) :))
  rat := (by with_unfolding_all exact (a.rat :))
  wt := (by with_unfolding_all exact (a.wt :))
  id := (by with_unfolding_all exact (a.id :))

def eWB (Y : RdTw x N) (i y) : type_of% (x.r.Y.mj.eW i y) := (by with_unfolding_all exact ((Y.mj.eW ((i)) ((y))) : _))

theorem hkDat {Sb i k Q α Rr} (h : HkDat (datTw x N).R Sb i k Q α Rr) :
    HkDat x.m.z.R ((Sb)) ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigAd (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) {Sb eig} (h : EigAd x.r.Y Sb eig) :
    EigAd Y ((Sb)) ((eig)) := fun i σ k Q α Rr hd hg y hy =>
  (by with_unfolding_all exact ((eigAd_of h (((eWB Y))) ((H)) ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((hkDat hd))) ((hg)) ((y)) ((hy))) : _))

def ratInTw (n : InRat x.r.Y x.m.z.cG) : RatIn (w.st (oTw x N).Z).toD7
    (ratDatR (datTw x N).R (datTw x N).cG n.kKs n.hk) where
  Sb := n.In.Sb
  rho := n.In.rho
  chi := n.In.chi
  ks := n.In.ks
  fd := n.In.fd
  mk_fg := n.In.mk_fg
  hL := n.In.hL
  hs := n.In.hs
  hL_zero := n.In.hL_zero
  θ := n.In.θ
  θ_ne := n.In.θ_ne
  eig := n.In.eig
  span := (by with_unfolding_all exact ((ratIn N n.In).span : _))
  hL_int := (by with_unfolding_all exact ((ratIn N n.In).hL_int : _))

def inRat (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) (n : InRat x.r.Y x.m.z.cG) : InRat Y (datTw x N).cG where
  kKs := (by with_unfolding_all exact (n.kKs :))
  hk := (by with_unfolding_all exact (n.hk :))
  In := (by with_unfolding_all exact ((ratInTw (N := N) n) :))
  rat :=
    { hecke := fun j k Q α Rr h1 h2 hd y => (by with_unfolding_all exact ((n.rat.hecke j k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) h1 ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact ((hkDat hd) :))) ((by with_unfolding_all exact (y :)))) :))
      eig := (by with_unfolding_all exact ((eigAd Y H n.rat.eig) :))
      Sb_le := (by with_unfolding_all exact (n.rat.Sb_le :))
      lvl := (by with_unfolding_all exact (n.rat.lvl :))
      psi := (by with_unfolding_all exact (n.rat.psi :)) }

def inMt (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) (n : InMt x.r.Y (cfOf x) w.I.xi (QOf P)) :
    InMt Y (⟨(cfOf x).P, (cfOf x).W, (cfOf x).mu0, (cfOf x).eta, (cfOf x).chiPsi, (cfOf x).del, (cfOf x).del', (cfOf x).isMu0, (cfOf x).isEta, (cfOf x).isChi, (cfOf x).isDel, (cfOf x).isDel'⟩) w.I.xi (QOf P) where
  M := (fun μ j h1 h2 => { n.M μ j h1 h2 with })
  ad := (by with_unfolding_all exact ((mtAd Y H n.ad) :))
  mt :=
    { prod := by with_unfolding_all exact n.mt.prod
      para := by with_unfolding_all exact n.mt.para
      uni := by with_unfolding_all exact n.mt.uni
      hyp := by with_unfolding_all exact n.mt.hyp
      wt := by with_unfolding_all exact n.mt.wt
      rat := by with_unfolding_all exact n.mt.rat
      int := by with_unfolding_all exact n.mt.int
      full := by with_unfolding_all exact n.mt.full }

end GlobalTheory.HeightCounting.Up.LiTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadCell
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValDelta

theorem exists_gal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) (χ : HChar E) {n : ℕ} (hn : 0 < n) (hχ : χ.OrderDvd n) :
    ∃ r : G E Ω →* ℂˣ, Continuous r ∧ GlobalTheory.GalToHecke.IsHeckeOf art r χ := by
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab E Ω →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  refine ⟨c.comp (GlobalTheory.HeckeGal.toAb E Ω), hcc.comp continuous_quot_mk, fun x σ hσ => ?_⟩
  show χ.1 x = c (GlobalTheory.HeckeGal.toAb E Ω σ)
  rw [← hσ, hc]

variable {D : D7}

theorem delta_tame (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) : ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.delta i σ ^ 15 = 1 := by
  refine ⟨fun h => ?_, fun A hA σ hσ => ?_⟩
  · have h1 := D.ntw.delta_tame i P hP
    have h2 : Ideal.absNorm P.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
      rwa [Ideal.absNorm_span_natCast] at this
    have h3 : Nat.Coprime (Ideal.absNorm P.asIdeal) 15 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
      rfl
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
  · have h1 := pow_card_eq_one' (x := (⟨D.ntw.delta i σ, σ, hσ, rfl⟩ : (Ine (F := D.host.E) A).map (D.ntw.delta i)))
    rw [D.ntw.delta_15 i P hP A hA] at h1
    exact congrArg Subtype.val h1

theorem read_of_side {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) (y : D.ntw.O0 i)
    (x : ↥D.LL0) (h : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = (if b then D.ntw.emb0 i else D.ntw.emb0b i) x) :
    e (NX.ofO0 D i k y) = embLL0 D x := by
  rw [← he x, GlobalTheory.SeriesTie.sideEmb, RingHom.comp_apply, ← h]
  simp only [NX.toKk, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem delta_isHeckeOf (cf : CharFrame D) (hR : DeltaRead D cf) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) :
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp
      (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) (cf.delAt (D.ntw.l i)) := by
  obtain ⟨n, hn, hord⟩ : ∃ n, 0 < n ∧ (cf.delAt (D.ntw.l i)).OrderDvd n := by
    unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨r, hr, hH⟩ := exists_gal ha _ hn hord
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hc : Continuous ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' _ (Subgroup.isOpen_mono (fun g hg => ?_) hker)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  suffices h : (Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r by
    rw [h]; exact hH
  refine GlobalTheory.GalChar.eq_of_frob ha hc hr ?_
  filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero,
    GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
  obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
  have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
    rw [hx, Units.val_inv_eq_inv_val]
  have hrv : r σ = ((cf.delAt (D.ntw.l i)).val v)⁻¹ := by rw [hH.val_eq ha hu hA hσ, inv_inv]
  rw [hrv]
  cases b
  · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
    have h1 := read_of_side he _ x⁻¹ (hd.trans (D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar).symm)
    show Units.map _ ((D.ntw.delta i σ)⁻¹) = _
    rw [map_inv, inv_inj]
    apply Units.ext
    refine h1.trans ?_
    show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
    rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
  · apply Units.ext
    exact (read_of_side he _ x hd).trans hx

theorem tameVal_delta (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) {i : D.ntw.Tw} {b : Bool}
    {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) (a : 𝓞 D.host.E)
    (y : D.host.Eˣ) (hu : a ∉ P.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    IsUnitAt P (atFin P y) ∧ e (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then 1 else -1) a).1) =
      (((cf.delAt (D.ntw.l i)).locK P y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have hA : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P - 1 by omega)
  have hxu : IsUnitAt P (atFin P y) := by
    show Valued.v (((y : D.host.E) : P.adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  refine ⟨hxu, ?_⟩
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    P _ hA ϖ hϖ1 hϖ2 π hπ (atFin P y) a hxu (by simp [atFin, hy])
  obtain ⟨h15, hord⟩ := delta_tame i hP
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep (D.ntw.delta i) P _ 15 (D.ntw.delta_open i) h15
    (fun A hA σ hσ => ⟨1, by rw [pow_one, hord A hA σ hσ]⟩) _ a hu
    (GlobalTheory.TameResRead.tameRep_zpow hA hσI hϖ1 hϖ2 hπ hu hσval _)]
  have h1 := delta_isHeckeOf cf hR ha he _ σ hσart.symm
  have h2 : D.ntw.delta i (σ ^ (if b then (1 : ℤ) else -1)) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ := by
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  rw [h2]
  exact (congrArg Units.val h1).symm

end GlobalTheory.LevCmp.ValDelta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsClassSetPresentationCoefficientMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem rowsClassPresLink : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) :=
  GlobalTheory.T.coefficient_map_level_character_equivariant

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  first | exact @GlobalTheory.LevCmp.reading_sidePl_emb | exact GlobalTheory.LevCmp.reading_sidePl_emb | (intros; apply GlobalTheory.LevCmp.reading_sidePl_emb <;> assumption)
end

