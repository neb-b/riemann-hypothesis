module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMeas

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_sub_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ v - v) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ v) := by
  have e3 : (frGL β y).1 = β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem mem_princGL_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ GlobalTheory.Grid.princGL β I ↔ x ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v - v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  rw [GlobalTheory.Grid.mem_princGL, ← stabilizer_eq_stabilizer_lattice F E n Λ β hfr]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨y, rfl⟩, fun v hv => ?_⟩
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I, frame_sub_eq]
    intro i
    have hw := (hfr v).1 hv
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun k => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hw k) ⟨_, hy i k, GlobalTheory.LevRedTriv.coe_sub_one_apply y i k⟩
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, rfl, fun i j => ?_⟩
    have h1 := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I _).1 (h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hfr j)) i
    have e : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [frame_sub_eq, e, Matrix.mulVec_single_one] at h1
    obtain ⟨s, hs, e⟩ := h1
    have : s = (y.1 - 1) i j := Subtype.ext (e.trans (GlobalTheory.LevRedTriv.coe_sub_one_apply y i j).symm)
    exact this ▸ hs

theorem princ_eq_congLev [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) :
    UA hc J ⊓ GlobalTheory.Grid.princGL β I = congLev hc J Λ I := by
  ext x
  rw [Subgroup.mem_inf, mem_princGL_iff hfr, mem_congLev]

end General

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

open GlobalTheory.GridJoin

theorem exists_measDat {D : D7} (N : GlobalTheory.Grid.Node D) {V : HSp D} (hsp : SameSp V N.V)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hlat : HEq N.Λ Λ) (hfr : IsFrame N.β N.Λ)
    (I : Ideal (𝓞 D.host.E)) {ν : Measure (GA D V)} {fd : Set (GA D V)}
    (hm : Lev.IsMeasFD V (congLev D.sp.cm V.gram Λ I) ν fd) :
    ∃ md : N.MeasDat, HEq md.ν ν ∧ HEq md.fd fd ∧ md.Is False (N.princ I) := by
  obtain ⟨L, h1, h2, e⟩ := hsp
  obtain ⟨V', S, M, Λ', β⟩ := N
  simp only at e hlat hfr ⊢
  subst e
  obtain rfl := eq_of_heq hlat
  refine ⟨⟨ν, fd⟩, HEq.rfl, HEq.rfl, fun h => h.elim, fun _ => ?_⟩
  unfold GlobalTheory.Grid.Node.princ
  rw [princ_eq_congLev _ _ hfr]
  exact hm

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

theorem measCol_of_choice : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
    (G : GlobalTheory.Grid.GridPre R), G.IsMeas → GlobalTheory.GridJoin.SpMatch G ch.W →
    (∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ) → ch.M.IsRow →
    ∃ (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat),
      (GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).IsMeas ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).ν (ch.M.ν (.grid i 0))) ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).fd (ch.M.fd (.grid i 0))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch G hG hsp hfr hrow
  have H : ∀ i, ∃ md : (G.V i 0).MeasDat, i ≤ D.R.m → HEq md.ν (ch.M.ν (.grid i 0)) ∧
      HEq md.fd (ch.M.fd (.grid i 0)) ∧ md.Is False ((G.V i 0).princ (G.lvl R)) := by
    intro i
    by_cases hi : i ≤ D.R.m
    · have hN := hsp.vert i 0 hi (Nat.zero_le _)
      have hr := hrow.row i hi
      have hne : GlobalTheory.ChiGrid.Node.neg D.R.m (.grid i 0) ≠ 0 := by
        simp only [GlobalTheory.ChiGrid.Node.neg, Nat.sub_zero]
        have := D.R.two_le_m
        omega
      unfold Vol.IsAt at hr
      rw [if_neg hne] at hr
      obtain ⟨md, h1, h2, h3⟩ := exists_measDat (G.V i 0) hN.sp hN.lat (hfr i hi) _ hr
      exact ⟨md, fun _ => ⟨h1, h2, hsp.lvl ▸ h3⟩⟩
    · exact ⟨G.measCol i, fun h => absurd h hi⟩
  choose f hf using H
  refine ⟨f 0, fun i j => match j with | 0 => f (i + 1) | j + 1 => G.mV i (j + 1),
    ⟨fun i hi => ?_, fun i j hi hj => hG.vert i j hi hj, hG.P, hG.X⟩, fun i hi => ?_, fun i hi => ?_⟩
  · cases i <;> exact (hf _ hi).2.2
  · cases i <;> exact (hf _ hi).1
  · cases i <;> exact (hf _ hi).2.1

end GlobalTheory.ColMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPairWeilLatticeIffStandardOfHalf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem locPl_over {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.1 hw with hw0 | hwQ
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw0
    exact Or.inl ((G.pl.under_w hv).symm ▸ hv)
  · exact Or.inr ⟨w, hwQ, rfl⟩

private theorem kill_lemma' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}
    (N : Std G Set.univ) {t : T} {e : AE D} (he : IsIdemSum e (locPl G t)) (p : Pair T) {X : Node}
    (hX : DefNode D.R.m X) : ∃ a : AE D, e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 :=
  exists_kill N (Set.mem_univ t) (FinDatum.ind G t p (locPl G t) (locPl_over G t) e he) hX

theorem mem_pairLat_iff_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  intro D T L sc G W S t p hp e he x hx
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hXS : DefNode D.R.m (.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
    have hXT : DefNode D.R.m (.grid i D.R.m) := ⟨by omega, rfl⟩
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.chi i D.R.m) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.chi i D.R.m) hXT
    refine (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) D.R.m)).1) (S.N.u (.grid i D.R.m)).1
      ?_ ?_ hT1 hT2 ha hb ?_ hhb hx).symm
    · intro v hv
      have h := hS1 v hv
      rw [← mt_negGA] at h
      exact h
    · intro v hv
      have h := hS2 v hv
      rw [← mt_negGA, map_inv] at h
      exact h
    · unfold SuppAt at hga ⊢
      rw [← mt_negGA] at hga
      exact hga
  | top t' j =>
    have hXS : DefNode D.R.m (.top j) := by simp only [DefPair] at hp; show j ≤ D.R.m; omega
    have hXT : DefNode D.R.m (.top (j + 1)) := hp
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.top t' j) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.top t' j) hXT
    exact (mem_latO_iff_of_half _ _ hS1 hS2 hT1 hT2 ha hb hga hhb hx).symm
  | mu _ _ _ => exact hp.elim
  | core _ => exact hp.elim

end GlobalTheory.StdHalfLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemISupJointEigenspacesInfOfStableSubmodule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem mem_iSup_jointEigen_inf_of_stable : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F G P C hFG hadd hsmul hPG hFP hdec
  have hF0 : ∀ i, F i 0 = 0 := by
    intro i
    have := hsmul i 0 0 G.zero_mem
    simpa using this
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℂ) → Submodule ℂ E,
      ∀ c x, x ∈ V c ↔ (x ∈ G ∧ ∀ i, F i x = c i • x) :=
    ⟨fun c =>
      { carrier := {h | h ∈ G ∧ ∀ i, F i h = c i • h}
        add_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨G.add_mem hx hy, fun i => ?_⟩
          rw [hadd i x hx y hy, hx' i, hy' i, smul_add]
        zero_mem' := ⟨G.zero_mem, fun i => by rw [hF0 i, smul_zero]⟩
        smul_mem' := by
          rintro a x ⟨hx, hx'⟩
          refine ⟨G.smul_mem a hx, fun i => ?_⟩
          rw [hsmul i a x hx, hx' i]
          exact smul_comm _ _ _ }, fun c x => Iff.rfl⟩
  have hVG : ∀ c, V c ≤ G := fun c x hx => ((hV c x).1 hx).1
  have hSG : ∀ s : Finset (ι → ℂ), (⨆ c ∈ s, V c) ≤ G := fun s => iSup₂_le fun c _ => hVG c
  have hmemS : ∀ (s : Finset (ι → ℂ)) c, c ∈ s → V c ≤ ⨆ c ∈ s, V c := fun s c hc =>
    le_iSup₂_of_le (f := fun c (_ : c ∈ s) => V c) c hc le_rfl
  have hT : ∀ (i : ι) (b : ℂ) (s : Finset (ι → ℂ)), ∀ z ∈ ⨆ c ∈ s, V c,
      F i z - b • z ∈ ⨆ c ∈ s, V c := by
    intro i b s
    obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ E,
        ∀ v, v ∈ M ↔ (v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c) :=
      ⟨{ carrier := {v | v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c}
         add_mem' := by
           rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
           refine ⟨G.add_mem hx hy, ?_⟩
           have : F i (x + y) - b • (x + y) = (F i x - b • x) + (F i y - b • y) := by
             rw [hadd i x hx y hy, smul_add]; abel
           rw [this]; exact Submodule.add_mem _ hx' hy'
         zero_mem' := ⟨G.zero_mem, by simp [hF0 i]⟩
         smul_mem' := by
           rintro a x ⟨hx, hx'⟩
           refine ⟨G.smul_mem a hx, ?_⟩
           have : F i (a • x) - b • (a • x) = a • (F i x - b • x) := by
             rw [hsmul i a x hx, smul_sub, smul_comm b a x]
           rw [this]; exact Submodule.smul_mem _ a hx' }, fun v => Iff.rfl⟩
    have hle : (⨆ c ∈ s, V c) ≤ M := iSup₂_le fun c hc v hv => by
      rw [hM]
      obtain ⟨hvG, hv'⟩ := (hV c v).1 hv
      refine ⟨hvG, ?_⟩
      rw [hv' i, ← sub_smul]
      exact hmemS s c hc ((V c).smul_mem _ hv)
    intro z hz
    exact ((hM z).1 (hle hz)).2
  have hB : ∀ (a : ι → ℂ) (s : Finset (ι → ℂ)), a ∉ s → ∀ y ∈ V a, ∀ z ∈ ⨆ c ∈ s, V c,
      y + z ∈ P → y ∈ P := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      intro _ y _ z hz hyz
      simp at hz
      rw [hz, add_zero] at hyz; exact hyz
    | insert b t hbt ih =>
      intro ha y hy z hz hyz
      rw [Finset.mem_insert, not_or] at ha
      obtain ⟨hab, hat⟩ := ha
      rw [Finset.iSup_insert, Submodule.mem_sup] at hz
      obtain ⟨zb, hzb, zt, hzt, rfl⟩ := hz
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
      obtain ⟨hyG, hy'⟩ := (hV a y).1 hy
      obtain ⟨hzbG, hzb'⟩ := (hV b zb).1 hzb
      have hztG := hSG t hzt
      have hP1 : F i (y + (zb + zt)) - b i • (y + (zb + zt)) ∈ P :=
        P.sub_mem (hFP i _ hyz) (P.smul_mem _ hyz)
      have heq : F i (y + (zb + zt)) - b i • (y + (zb + zt))
          = (a i - b i) • y + (F i zt - b i • zt) := by
        rw [hadd i y hyG _ (G.add_mem hzbG hztG), hadd i zb hzbG zt hztG, hy' i, hzb' i]
        simp only [smul_add, sub_smul]; abel
      rw [heq] at hP1
      have hy2 : (a i - b i) • y ∈ V a := (V a).smul_mem _ hy
      have h3 := ih hat _ hy2 _ (hT i (b i) t zt hzt) hP1
      have hne : a i - b i ≠ 0 := sub_ne_zero.2 hi
      have h4 := P.smul_mem (a i - b i)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  have hspan : ∀ c, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h} = V c := fun c =>
    le_antisymm (Submodule.span_le.2 fun x hx => (hV c x).2 hx)
      fun x hx => Submodule.subset_span ((hV c x).1 hx)
  have hmain : ∀ s : Finset (ι → ℂ), ∀ x ∈ P, x ∈ ⨆ c ∈ s, V c →
      x ∈ ⨆ c ∈ s, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx; simpa using hx
    | insert a s has ih =>
      intro x hxP hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hyP : y ∈ P := hB a s has y hy z hz hxP
      have hzP : z ∈ P := by
        have := P.sub_mem hxP hyP; simpa using this
      rw [Finset.iSup_insert]
      exact Submodule.mem_sup.2 ⟨y, Submodule.subset_span ⟨hyP, ((hV a y).1 hy).2⟩, z, ih z hzP hz, rfl⟩
  intro x hx
  have h := hdec x (hPG hx)
  simp only [hspan] at h
  exact hmain C x hx h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaEx

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem


set_option maxHeartbeats 1000000 in
theorem mem_splitOff_of_suppSplit : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  classical
  intro D V Q s hs
  obtain ⟨g, hg⟩ := s
  let P : GA D V → Prop := fun x => ∃ h : x ∈ GfC V, (⟨x, h⟩ : GfC V) ∈ splitOff V Q
  have h1 : P 1 := ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := fun x y ⟨hx, mx⟩ ⟨hy, my⟩ =>
    ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ mx my⟩
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, P (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    refine ⟨GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}, Subgroup.subset_closure ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, ?_, ?_⟩⟩
    · intro q hq v' ε' hε' heq
      have hε : ε' = pairA D.host.F 0 (GlobalTheory.LocalApprox.indA D.host.F {v}) :=
        hinj (heq.symm.trans ((he.2.2).trans (hpl v)))
      obtain ⟨α, hα, hα1, hα0⟩ := hε'
      have hαv : α = GlobalTheory.LocalApprox.indA D.host.F {v} := congrArg Prod.snd (hα.symm.trans hε)
      have hvv : v' = v := by
        by_contra hne
        have := hα0 v (Ne.symm hne)
        rw [hαv, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)] at this
        exact one_ne_zero this
      subst hvv
      intro hqm
      refine hv'.2 ?_
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hk' : ((∏ q ∈ Q, q : ℕ) : 𝓞 D.host.F) = (q : 𝓞 D.host.F) * (k : 𝓞 D.host.F) := by
        rw [hk, Nat.cast_mul]
      rw [hk']
      exact Ideal.mul_mem_right _ _ hqm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ t : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), t ⊆ he2.toFinset →
      P (GlobalTheory.LocalApprox.cutAt V g t) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v t h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  obtain ⟨_, hm⟩ := hgS ▸ key _ subset_rfl
  exact hm

end GlobalTheory.MovedKappaEx
end

