module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def iotaR (R : RealDat3 D A3 Ks) (i : Fin D.R.m) :
    (Fin (R.nW i) → D.what₂.LL) →ₛₗ[sg0 D A3.A] Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) :=
  (R.HW i (sg0 D A3.A)).e.comp ((R.FW i).j (sg0 D A3.A))

theorem iotaR_apply (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (v : Fin (R.nW i) → D.what₂.LL) :
    iotaR R i v = (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) v) := rfl

variable {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem readW_mem_goodW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    GlobalTheory.EigRows.readW Y i y ∈ GlobalTheory.EigRows.goodW R F i := by
  obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (Y.IL.jMj i y).2
  have h' : a = GlobalTheory.EigRows.readW Y i y :=
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
      (e.trans (GlobalTheory.EigRows.lift_readW Y i y).symm)
  exact h' ▸ ha

theorem goodW_le_parts (Y : Read (A3 := A3) R F X0) (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (i : Fin D.R.m) (n : ℕ) (hn : (i : ℕ) + 1 = n) :
    GlobalTheory.EigRows.goodW R F i ≤ ⨆ σ ∈ {σ | D.what₂.isot n σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i) := by
  subst hn
  intro z hz
  obtain ⟨y, rfl⟩ := GlobalTheory.EigRows.exists_readW Y i hz
  have hy : y ∈ ⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ := by
    rw [(hI _ (Nat.le_add_left 1 i) i.2).submodule_iSup_eq_top]; trivial
  have key : (⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ) ≤ (⨆ σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i)).comap (GlobalTheory.EigRows.readW Y i) := by
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
    · rw [h0]; exact bot_le
    · intro u hu
      exact Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem
        (show σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ} from ⟨h0, hG _ (Nat.le_add_left 1 i) i.2 σ h0⟩)
        (Submodule.mem_map_of_mem hu)))
  exact key hy

end Real

end GlobalTheory.EigSpanDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingInjective
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def HkAd (X : RealSide D) (Sb : Finset (PlE D.host))
    (hL : ∀ j : ℕ, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (X.R.nW (NX.idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat X.R Sb (NX.idxOf D j) k P α Rr → ∀ x,
    evidence X (NX.idxOf D j) (hL j k P x) =
      hkNorm X.R (NX.idxOf D j) k P • Mult.heckeOn (model X (NX.idxOf D j)) Rr (evidence X (NX.idxOf D j) x)

def HkLaw (D : D7) (S : NX.RatDat D.ntw)
    (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) : Prop :=
  ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (hL j) (hs j h1 h2) k P (eF i j b h1 h2 x)

def LowIn (D : D7) : Prop := ∀ i, ∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i)

theorem HkAd.at {X : RealSide D} {Sb hL} (H : HkAd X Sb hL) (j : Fin D.R.m)
    (f : (Fin (X.R.nW (NX.idxOf D ((j : ℕ) + 1))) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL) (hf : ∀ x, HEq (f x) x)
    {k P α Rr} (hd : HkDat X.R Sb j k P α Rr) (x) :
    evidence X j (f (hL ((j : ℕ) + 1) k P x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
  have key : ∀ (a : Fin D.R.m), a = j → ∀ (u : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW a) → D.what₂.LL)
      (f : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL), (∀ x, HEq (f x) x) →
      (∀ α Rr, HkDat X.R Sb a k P α Rr → ∀ x, evidence X a (u x) = hkNorm X.R a k P • Mult.heckeOn (model X a) Rr (evidence X a x)) →
      ∀ x, evidence X j (f (u x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
    intro a haj
    subst haj
    intro u f hf hu x
    rw [eq_of_heq (hf _), eq_of_heq (hf _)]
    exact hu α Rr hd x
  exact key _ (NX.idxOf_succ D j) _ f hf (fun α Rr hd => H _ k P α Rr (Nat.le_add_left _ _) j.2 hd) x

theorem reading_injective (X : RealSide D) (j : Fin D.R.m) : Function.Injective (evidence X j) := by
  refine (X.char.models.HW j _).1.comp ((injective_iff_map_eq_zero _).2 fun x hx => by_contra fun h0 => ?_)
  exact ((X.unif j (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem fiOfEq_heq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (x) : HEq ((fiOfEq X hab).e x) x := by
  subst hab; rfl

theorem exists_hkDat (X : RealSide D) (hl : LowIn D) {Sb} (hSb : OverSet D Sb (lowAll D)) {i : D.ntw.Tw} {v : PlE D.host}
    (hv : v ∉ D.ntw.S0 i) (hsp : IsSplitPl D.host v) : v ∉ Sb ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ (j : Fin D.R.m) (k : ℕ), k ≤ D.R.r → ∃ α Rr, HkDat X.R Sb j k v α Rr := by
  have hlow : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun p hp hm => hv (hl i p hp hm)
  have hgP : ∀ kk : Fin 2, ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll])
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  have h1 : v ∉ Sb := fun hh => hv (hSb.subset (hl i) hh)
  have h2 := hlow 2 (by simp [lowAll, Formalism.L2.lowPr])
  refine ⟨h1, h2, fun j k hk => ?_⟩
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam j hso hk
  exact ⟨α, Rc, hsp, h1, h2, hk, ha, hR⟩

theorem units_cast {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) {u : Aˣ} {v : Bˣ} (hu : HEq v u) :
    ringCast h hi (u : A) = v := by
  subst h; cases hi; cases hu; rfl

section Law

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {kKs hk}
  (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
  (hl : LowIn D) (hl' : LowIn D') {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
  {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL')


include hfi hl hl' hSb hSb' H H' in
theorem hk_intertwine {i : D.ntw.Tw} {i' : D'.ntw.Tw} (j : Fin D.R.m) (k : ℕ) {P : PlE D.host} {P' : PlE D'.host} (hP : HEq P P')
    (p0 : P ∉ D.ntw.S0 i) (p1 : P' ∉ D'.ntw.S0 i') (p2 : IsSplitPl D'.host P') (p3 : k ≤ D'.R.r)
    (y : ((NX.ratDatR X.R X.cG kKs hk).A ((j : ℕ) + 1)).WK) (hy) :
    ((ks h m YS j).φ ⟨hL ((j : ℕ) + 1) k P y.1, hy⟩).1 = hL' ((j : ℕ) + 1) k P' ((ks h m YS j).φ y).1 := by
  obtain ⟨q1, q2, q3⟩ := (place_geo h.gal.R h.gal.host).2 P P' hP
  obtain ⟨α', R', hd'⟩ := (exists_hkDat X' hl' hSb' p1 p2).2.2 (h.cm j) k p3
  obtain ⟨r1, r2, -⟩ := exists_hkDat X hl hSb p0 (q1.2 p2)
  obtain ⟨α, R, ha0, hR0, hF⟩ := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).2.2 _ _ (m.βW j (h.cm j) rfl) _ _ m.Pg P P' hP
    k α' R' hd'.elt hd'.reps
  have e0 := H.at j (YS.fi j).e (hfi j) ⟨q1.2 p2, r1, r2, by rw [h.gal.R]; exact p3, ha0, hR0⟩ y.1
  have e0' := H'.at (h.cm j) (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e (fiOfEq_heq X' _) hd' ((ks h m YS j).φ y).1
  have hnV : D.R.nV = D'.R.nV := by rw [h.gal.R]
  have e1 : hkNorm X.R j k P = hkNorm X'.R (h.cm j) k P' := by
    unfold hkNorm
    rw [q3 _ _ (m.Cmu0 j (h.cm j) rfl), q2, hnV]
  have e2 := hecke_sameMap h m j hF (read_move h m YS j ⟨_, hy⟩) (read_move h m YS j y) (e0.trans (congrArg (· • _) e1))
  exact (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e.injective (reading_injective X' _ (e2.trans e0'.symm))


include hfi hl hl' hSb hSb' H H' in
theorem hkLaw_move (hsup) {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c) :
    HkLaw D' (dat h m YS) (tie h m YS hsup).eF hL' hs' c' := by
  intro i' j b h1 h2 k P' x p1 p2 p3
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
  generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
  have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
    eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
  have p0 : P ∉ D.ntw.S0 (back h i') := fun hh => p1 ((r3 P P' hP).1.1 hh)
  change eFm h m YS i' (n + 1) b h1 h2 _ = _ • hkF D' (dat h m YS) i' (n + 1) b (hL' (n + 1)) (hs' (n + 1) h1 h2) k P'
    (eFm h m YS i' (n + 1) b h1 h2 _)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
    L _ _ b _ _ k P x p0 (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2) (by rw [h.gal.R]; exact p3), fmOf_smul]
  refine congrArg₂ (· • ·) ?_ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs' (n + 1) h1 h2 k P')
    (fun y => hk_intertwine h m YS hfi hl hl' hSb hSb' H H' ⟨n, lt_m h h2⟩ k hP p0 p1 p2 p3 y _) _)
  rw [map_pow, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact congrArg (fun z => algebraMap _ _ z ^ k) (units_cast _ _ (hc _ _ b _ _ hi hP))

end Law

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

theorem occ_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {Φ : Type}
    {rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r} (h : Reps y F rep) : y.occ F = {ρ | ∃ π, (rep π).Iso ρ} := by
  refine Set.ext fun ρ => ⟨h.all ρ, fun ⟨π, hi⟩ => ?_⟩
  obtain ⟨b, hb⟩ := h.mem π
  refine ⟨b, ?_⟩
  unfold principalLevelFrame.isotE at hb ⊢
  rw [← principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hi)]
  exact hb

theorem rep_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S S' U : Set (Formalism.L2.NG.FinTyp L n)} (e : S = U) (e' : S' = U)
    {c : Formalism.L2.Col.FinTypCls S} {c' : Formalism.L2.Col.FinTypCls S'} {ρ : Formalism.L2.NG.FinTyp L n}
    (h : (Formalism.L2.Col.finTypRep S c).Iso ρ) (h' : (Formalism.L2.Col.finTypRep S' c').Iso ρ) :
    Formalism.L2.Col.finTypRep S c = Formalism.L2.Col.finTypRep S' c' := by
  subst e e'
  exact congrArg _ (Formalism.L2.Col.finTypRep_inj (Formalism.L2.NG.IsoRep.trans h (Formalism.L2.NG.IsoRep.symm (Formalism.L2.Col.finTypRep _ c').stable h')))

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}


set_option maxHeartbeats 2000000 in
theorem rep_pin {o : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin) (π : q.p.Φ) :
    ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (q.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (q.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((π)))) (Formalism.L2.Col.finTypRep S c) := by
  have e : ((by with_unfolding_all exact (m.t.rep :)) : type_of% q.t.rep) = q.t.rep := eq_of_heq ((by with_unfolding_all exact (hco.rep :)))
  have h1 := occ_iff m.t.reps
  have h2 := congrArg (fun P : type_of% m.y.PY => principalLevelFrame.OccRows m.z.R.θ P (m.z.R.MY 0)
    (fun b => levS _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b)))
    (fun b => levChi _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b))) (fun _ => m.z.R.toRealDat.e0)) r.PY
  have h3 := h2.trans h1
  have h4 := hp.rep ((by with_unfolding_all exact (π :)))
  rw [← e]
  have h5 : ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st o.Z).toD7.host.E (w.st o.Z).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (m.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (m.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((by with_unfolding_all exact (π :))))) (Formalism.L2.Col.finTypRep S c) := ⟨_, r.Y.eFT π, h3, h4, HEq.rfl⟩
  exact (by with_unfolding_all exact (h5 :))


set_option maxHeartbeats 2000000 in
theorem repOf_heq {o o' : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin)
    {m' : Moved o'} (hco' : m'.Coh) {s' : Side0 o'} (r' : ReadPk m' s') (hp' : r'.Pin) :
    HEq (GlobalTheory.HeightCounting.repOf r'.Y) (GlobalTheory.HeightCounting.repOf r.Y) := by
  have h : ∀ π : q.p.Φ, ((by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r'.Y ((π))) : _)) : Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r) =
      (by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r.Y ((π))) : _)) := fun π => by
    obtain ⟨S, c, h1, h2, h3⟩ := rep_pin hco r hp π
    obtain ⟨S', c', h1', h2', h3'⟩ := rep_pin hco' r' hp' π
    exact eq_of_heq ((by with_unfolding_all exact ((h3'.trans ((heq_of_eq (rep_eq h1' h1 h2' h2)).trans h3.symm)) :)))
  exact (by with_unfolding_all exact ((heq_of_eq (funext h)) :))

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem ringOfIntegers_equiv_bar_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  intro E _ _ _ H τ a
  have hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E) := by
    exact MulEquivClass.map_nonZeroDivisors τ
  let τE : E ≃+* E := IsLocalization.ringEquivOfRingEquiv E E τ hM
  have hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E) := by
    intro x
    exact IsLocalization.ringEquivOfRingEquiv_eq hM x
  obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  rw [← hτE, H.bar_eq, H.bar_eq, ← hτE]
  apply ψ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1
  rw [h1, h2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def flagRoot {H : Host E} (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw h; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw h; omega⟩)

def flagMap {H : Host E} (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (flagRoot Dw)

def flagLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem flagLin_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    flagLin ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [flagLin, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def schubGam {H : Host E} (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (fibrePoint Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem schubGam_apply {H : Host E} (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    schubGam Dw P = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (flagMap Dw (chernRoots Dw.mult P * fibrePoint Dw.mult)) := by
  simp [schubGam, flagLin_apply]

def admitted (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P, Θ (GlobalTheory.PointChern.relPoly τ k * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Θ ((X (τ, 0) - 1) * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (X (τ, k) * P) = 0) ∧
  (∀ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) →
    Θ (monomial d 1) = 0)

end GlobalTheory.Schubert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan

theorem genRank_le_of_inRCone_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) →
    genRank v ≤ genRank γ := by
  intro O _ bar ψ X _ _ _ m n γ v hγ hbal hnn hcone
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hk : ∀ j, ∃ k : ℕ, 0 < k ∧ ((k : ℤ) • v j) ∈ Submodule.span ℤ (Set.range γ) := by
    intro j
    obtain ⟨c, hc, e⟩ := hcone j
    have hl := apply_eq_of_toReal_eq e ℓ
    have hlin := (linearOn_iff ψ γ).1 hγ.linear c hc
    rw [← e, evalR_toReal] at hlin
    have heq : (N : ℝ) * ψ.evalZ (v j) = ℓ (v j) := by
      rw [hl, hlin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i]; ring
    obtain ⟨k, c', hk, hc'⟩ := h3 (v j) (hbal j) (hnn j) heq
    refine ⟨k, hk, ?_⟩
    rw [natCast_zsmul, hc']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose k hkpos hkmem using hk
  set K : ℕ := ∏ j, k j with hKdef
  have hK : 0 < K := Finset.prod_pos fun j _ => hkpos j
  set S := Submodule.span ℤ (Set.range γ) with hS
  have hle : Submodule.span ℤ (Set.range v) ≤ S.comap ((K : ℤ) • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr⟩ : k j ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show ((K : ℤ) • LinearMap.id) (v j) ∈ S
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hr, Nat.cast_mul, mul_comm, mul_smul]
    exact S.smul_mem _ (hkmem j)
  let f : Submodule.span ℤ (Set.range v) →ₗ[ℤ] S :=
    (((K : ℤ) • LinearMap.id).comp (Submodule.span ℤ (Set.range v)).subtype).codRestrict S fun x => hle x.2
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    apply Subtype.ext
    refine LinearMap.ext₂ fun a b => ?_
    have e2 := LinearMap.congr_fun₂ e a b
    simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul] at e2
    exact mul_left_cancel₀ (by exact_mod_cast hK.ne') e2
  haveI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  exact LinearMap.finrank_le_finrank_of_injective hf

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' :=
  isStarOf_of_cover _root_.GlobalTheory.StarCover.star_cover

end GlobalTheory.PolFan.StarCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem valLL0_colW {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
  subst C_eq
  exact val _ _ _ _ _ _

end GlobalTheory.HeightCounting.Up
end

