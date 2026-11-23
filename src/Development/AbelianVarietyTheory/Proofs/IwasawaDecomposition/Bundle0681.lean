module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Extension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ListCarry
open GlobalTheory.Mem.R3.Tr GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.TwInputs.Move


open Classical in
def movePl {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L)
    (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (v : HeightOneSpectrum (𝓞 D.host.F))
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hv : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (hS : v ∉ S1 D)
    (hu : u.under (𝓞 D.host.F) = v) (hs : ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e u) : Places L where
  v0 := v
  basePlace_over_qZero := hv
  w := Function.update P.w v u
  w_over x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hu
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_over x (Finset.mem_insert_of_mem hx)
  w_split x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_split x (Finset.mem_insert_of_mem hx)
  w_g x k hx := by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      fin_cases k
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact P.w_g x k hx
  w_de p hp := (P.w_de p hp).imp fun 𝔭 h x hx => by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      rcases hp with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx)))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact h x hx
  w_Q t PP hP h := by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem h hS)]
    exact P.w_Q t PP hP h
  levelPlace_ne_basePlace t PP hP e := by
    subst e
    refine h4 t PP hP ?_
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((q0 D : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hv
    rwa [map_natCast] at this

theorem movePl_w {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L) (h4 v u hv hS hu hs) :
    (movePl P h4 v u hv hS hu hs).w v = u := by
  simp only [movePl, Function.update_self]

theorem listPin_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    (hj : HEq D.ntw.jL D'.ntw.jL) (hs : HEq D.ntw.s2 D'.ntw.s2) (hX : HEq D.ntw.Xv D'.ntw.Xv) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D' ≠ D'.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D' : ℕ) : 𝓞 D'.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D' Lc' CF b := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h.gal
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.set
  have b1 := h.sp
  have b2 := h.Tau
  have b3 := h.instTau
  have b4 := h.eTau
  have b5 := h.hc
  cases D'
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst a1; subst a2; subst a3; subst b1
  rename Rows.Data _ => rows'
  cases rows'
  dsimp only at b2 b3 b4 b5
  subst b2; subst b3; subst b4; subst b5
  rename NData _ _ _ => N'
  cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => X'
  cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hj; subst hs; subst hX
  obtain ⟨G, hF, hT⟩ := hp
  have hmu := eq_of_heq hmu
  have hd := eq_of_heq hd
  have hd' := eq_of_heq hd'
  have h0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  obtain ⟨P₀⟩ := hP fun k e => h0 ((S1_mem_OmF D).2 (by
    have e' : q0 D = D.host.g k := e
    have := G.pl.basePlace_over_qZero
    rw [e'] at this
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  have hm : G.pl.v0 ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)
  let P : Places Lc' := movePl P₀ h4 G.pl.v0 (G.pl.w G.pl.v0) G.pl.basePlace_over_qZero h0 (G.pl.under_w hm) ((G.pl.w_split G.pl.v0 hm))
  have hw : P.w P.v0 = G.pl.w G.pl.v0 := movePl_w ..
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA _).2 I' Lc' P ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices _ I' Lc' _ _ (GlobalTheory.ChiGrid.colY_isV _ I' Lc' μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  let X : Chars P 1 := ⟨G.ch.chiH, (G.ch.chi), (G.ch.chi_eq), (G.ch.triv), (G.ch.inf), (G.ch.unr),
    (G.ch.lev1), (G.ch.wild), (G.ch.lev0)⟩
  refine ⟨⟨P, X, V⟩, ⟨fun i a c v hv => ?_, fun v hv => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨y, hy⟩ := hF.values i a c v hv
    exact ⟨e.symm y, by rw [← h.embLL0_eq, e.apply_symm_apply]; exact hy⟩
  · obtain ⟨z, hz⟩ := hF.roots v hv
    exact ⟨e.symm z, hz.map_of_injective (f := e.symm) e.symm.injective⟩
  · obtain ⟨t0, j, t1, t2⟩ := hT i ((h.inW1 i i HEq.rfl).2 hi)
    have hl : ∀ l a c, (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).lam0 l a c = (lamOf G).lam0 l a c := fun l a c => by
      change Lc'.C.mu0 a * (if l = D.host.pde then Lc'.C.del' else Lc'.C.del) * _ = _
      rw [hmu, hd, hd']
      rfl
    have hw' : (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).w0 = (lamOf G).w0 := hw
    refine ⟨by rw [hw']; exact t0, j, fun x => ?_, ?_⟩
    · exact (congrArg j (h.embLL0_eq x).symm).trans ((t1 (e x)).trans (congrArg _ (eq_of_heq (h.emb0 i i HEq.rfl x))))
    · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, hw']
      exact t2

theorem twistPlaces_not_over_leastSplitAuxiliaryPrime {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) : ∀ t, ∀ PP ∈ z.R.toRealDat.toLevCh.Q t,
      ((q0 (w.st Z).toD7 : ℕ) : 𝓞 (w.st Z).toD7.host.E) ∉ PP.asIdeal := by
  intro t PP hP hq
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

theorem fr_heq {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f'.mu0 f.mu0 ∧ HEq f'.del f.del ∧ HEq f'.del' f.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem lev_fr {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    HEq x.m.z.R.toRealDat.toLevCh.C.mu0 f.mu0 ∧ HEq x.m.z.R.toRealDat.toLevCh.C.del f.del ∧
      HEq x.m.z.R.toRealDat.toLevCh.C.del' f.del' := by
  rw [(GlobalTheory.HeightCounting.Up.ListModel.lev_at_state x).1]
  obtain ⟨h1, h2, h3⟩ := fr_heq rfl (heq_of_eq w.C_eq)
  exact ⟨(h1), (h2), (h3)⟩

theorem listPin_copyN {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e)
    {D'' : D7} (hD : D'' = N.toD7) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D'' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D'' ≠ D''.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D'' : ℕ) : 𝓞 D''.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D'' Lc' CF b := by
  subst hD
  exact listPin_copy h.cp h.jL h.s2 h.Xv hL hmu hd hd' hP h4 hp

end GlobalTheory.HeightCounting.Up.ListCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem evLgG_gridA_of_exGrid : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := by
  classical
  intro h
  obtain ⟨CF0, hCF⟩ := h
  refine ⟨CF0, fun CF hC => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF eps CF hC
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩
  have hS := fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) =>
    hx K.s hKe hKx P f Ξ hΞ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    simp at hz
  · intro B f F F₀ Ξ z hz
    by_cases hΞ : Ξ.Finite
    · simp only [dif_pos hΞ] at hz
      exact (Classical.choose_spec (hS B f Ξ hΞ)).1 z hz
    · simp [dif_neg hΞ] at hz
  · intro B f T _ hHas _ _ C W V S N G
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    have hspec := (Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2
    refine hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_
    intro z hz
    have h2 := hHas.2 z
    simp only [dif_pos hfin] at h2
    exact h2 hz

end GlobalTheory.Mem.LiteralAutomorphy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddChar
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

noncomputable section

namespace GlobalTheory.ResidueChar

@[reducible] def unitsDivC : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnitC {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend_subring {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDivC
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnitC ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add (f := _)] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnitC] using e

theorem red_eq_zero_of_lt_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) < 1) : red y = 0 := by
  by_contra h
  set n : ℕ := (-(red y)⁻¹ : ZMod p).val with hn
  have hnc : ((n : ℕ) : ZMod p) = -(red y)⁻¹ := ZMod.natCast_zmod_val _
  set z : v.adicCompletionIntegers K := 1 + y * (n : v.adicCompletionIntegers K) with hz
  have hred : red z = 0 := by
    rw [hz, map_add (f := _), map_one, map_mul, map_natCast, hnc, mul_neg, mul_inv_cancel₀ h, add_neg_cancel]
  have hlt : Valued.v ((y * (n : v.adicCompletionIntegers K) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 := by
    have hn1 : Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
    rw [Subring.coe_mul, map_mul]
    calc Valued.v (y : v.adicCompletion K) * Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K)
        ≤ Valued.v (y : v.adicCompletion K) * 1 := by gcongr
      _ = Valued.v (y : v.adicCompletion K) := mul_one _
      _ < 1 := hy
  have hz1 : Valued.v ((z : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    rw [hz, Subring.coe_add, Subring.coe_one]
    rw [Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hlt
  have hu : IsUnit z := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).2 hz1
  have hu' : IsUnit (red z) := hu.map red
  rw [hred] at hu'
  exact not_isUnit_zero hu'

theorem exists_addChar_completion_lift_residue : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  intro K _ _ v p _ red ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend_subring (v.adicCompletionIntegers K).toSubring
    (ψ'.compAddMonoidHom red.toAddMonoidHom)
  refine ⟨ψ₀, fun x hx => ?_, ?_, fun x => h x⟩
  · have hx1 : x ∈ v.adicCompletionIntegers K :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : red ⟨x, hx1⟩ = 0 := red_eq_zero_of_lt_one v p red ⟨x, hx1⟩ hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    have hy' : ((y.val : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
    let x : v.adicCompletionIntegers K := (y.val : v.adicCompletionIntegers K)
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : v.adicCompletion K) = ψ₀ ((x : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red x) ≠ 1
    rw [show red x = y by simp only [x, map_natCast, hy']]
    exact hy

end GlobalTheory.ResidueChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_coefficientMap_liftPresentation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  first | exact @GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | exact GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | (intros; apply GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoe
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

namespace GlobalTheory.ReadingEmb

theorem exists_ringHom_complex_extending (A : Type) [Field A] (hA : Cardinal.mk A ≤ Cardinal.continuum)
    (K : Type) [Field K] [NumberField K] (i : K →+* A) (s : K →+* ℂ) :
    ∃ ι : A →+* ℂ, ∀ x, ι (i x) = s x := by
  haveI : CharZero A := (RingHom.charZero_iff i.injective).1 inferInstance
  let B := FractionRing (MvPolynomial ℝ A)
  have hB : Cardinal.mk B = Cardinal.continuum := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hA,
      max_eq_left Cardinal.aleph0_le_continuum]
  let C := AlgebraicClosure B
  have hC : Cardinal.mk C = Cardinal.continuum := by
    refine le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max B C).trans
      (max_le hB.le Cardinal.aleph0_le_continuum)) ?_
    rw [← hB]
    exact Cardinal.mk_le_of_injective (algebraMap B C).injective
  let j : A →+* C := (algebraMap B C).comp ((algebraMap (MvPolynomial ℝ A) B).comp MvPolynomial.C)
  haveI : CharZero C := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e, he⟩ := GlobalTheory.algClosed_continuum_ringEquiv_complex_extending C hC K (j.comp i) s
  exact ⟨e.toRingHom.comp j, fun x => he x⟩

theorem mk_le_of_finite (R S : Type) [CommRing R] [AddCommGroup S] [Module R S] [Module.Finite R S]
    (h : Cardinal.mk R ≤ Cardinal.continuum) : Cardinal.mk S ≤ Cardinal.continuum := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk R ^ (n : Cardinal) ≤ Cardinal.continuum ^ (n : Cardinal) := Cardinal.power_le_power_right h
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero (Cardinal.natCast_le_aleph0)
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem exists_complex_emb : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  intro D F i k b v ρ
  haveI := D.ntw.lPrime i
  have h1 : Cardinal.mk (D.ntw.Ok i k) ≤ Cardinal.continuum := by
    have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
      Subtype.val_injective.comp (F.eOk i k).injective
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]
  haveI := ρ.fin
  have h2 : Cardinal.mk ρ.Oe ≤ Cardinal.continuum := mk_le_of_finite (D.ntw.Ok i k) ρ.Oe h1
  exact exists_ringHom_complex_extending (FractionRing ρ.Oe) (by rw [Cardinal.mk_fractionRing]; exact h2)
    D.what₂.LL ρ.emb D.what₂.embLL

end GlobalTheory.ReadingEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricCharacterGridList_kept_localizedStage : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  intro K B f T w P x L cDep h
  with_unfolding_all
    exact @GlobalTheory.HeightCounting.Fin3.listPin_datL K B f T w P x L cDep h
end

