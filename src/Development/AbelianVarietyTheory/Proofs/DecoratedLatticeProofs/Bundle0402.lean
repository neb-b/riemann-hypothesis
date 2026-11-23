module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwisted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.TwResid

theorem phiT_tw {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1)))
    (hp : TC.PtOf k p.1.1) (hpN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (hp' : TC.PtOf k' p'.1.1) (hpN' : p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)))
    (hq : TC.PtOf (y * k) q.1.1) (hq' : TC.PtOf (y' * k') q'.1.1) :
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      Formalism.L2.Col.phiT B.fields.K p.1.1.deco.1 p'.1.1.deco.1 x₀ = Formalism.L2.Col.phiT B.fields.K q.1.1.deco.1 q'.1.1.deco.1 x := by
  refine ⟨∏ P ∈ (B.primes X).vT u, Ideal.absNorm P.asIdeal,
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot), fun M₀ hM x x₀ h => ?_⟩
  exact GlobalTheory.Transport.LevelDatum.phiT_eq B.fields.K (B.R.N_pos i) (B.R.N_pos (i + 1)) hp hpN hp' hpN' hq hq' x x₀
    fun P hP r s => lt_of_le_of_lt (h P hP r s) (GlobalTheory.Transport.LevelDatum.val_natCast_lt hM hP)

theorem xiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hok : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ)
    (hi : i + 1 ≤ B.R.m)
    (b : Idx I.sel (I.tup a) (I.idx a) i) (b' : Idx I.sel (I.tup a) (I.idx a) (i + 1))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p → cosetIn q' = cosetIn p' →
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ∀ r s,
        Valued.v (adAt B.host.F P
          ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B (B.R.N (i + 1))).1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E))
          ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
          (y.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
          ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
        Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)) →
      xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' x₀ =
        xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' q q' x := by
  intro B X I l hok u a i hi b b' p q p' q' k y k' y' hk hN hk' hN' hq hq' hc hc'
  obtain ⟨M1, hM1, H1⟩ := phiT_tw I u a i p q p' q' k y k' y' hk hN hk' hN' hq hq'
  have Hent := _root_.GlobalTheory.Transport.EntryAny.entry_transport_any I hok l u a
  have Hcp := _root_.GlobalTheory.Transport.TwistCpl.psiAt_transport_tw I hok l u a
  have Hlast := _root_.GlobalTheory.Transport.LastTw.locTop_transport_tw I l hok u a
  have hrowT : ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) ∧
        ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a), GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ :=
    fun M₀ x x₀ hx => ⟨fun P hP => hx P (Finset.mem_union_left _ hP), fun P => hx P.1 (Finset.mem_union_right _ P.2)⟩
  by_cases h2 : i + 2 < B.R.m
  · have hlt : i < B.R.m := by omega
    have hlt' : i + 1 < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hent i h2 (b.get hlt) (b'.get hlt') P p q p' q' k y k' y' hk hN hk' hN' hq hq'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_left h2, dite_eq_left h2]
    unfold Formalism.L2.Col.XiEntry
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  by_cases h3 : i + 2 = B.R.m
  · have hlt : i < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hcp i h3 (b.get hlt) P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_right h2, dite_eq_right h2, dite_eq_left h3, dite_eq_left h3]
    unfold Formalism.L2.Col.XiCpl1
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  · have h4 : i + 1 = B.R.m := by omega
    have h2m := B.R.two_le_m
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    choose Mf hMf Hf using fun P => Hlast n h4 P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    rw [xiAt_last _ _ _ _ _ h4, xiAt_last _ _ _ _ _ h4]
    unfold xiOver
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)

theorem tw_resid_datum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi c c' g g' hg hg' hy hy'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 (A.chOf i c)
  have hb' := hA.base (i + 1) hi (A.chOf (i + 1) c')
  have hr := hA.rep i hi0 c
  have hr' := hA.rep (i + 1) hi c'
  have hq := (hA.reads i hi0).pt c
  have hq' := (hA.reads (i + 1) hi).pt c'
  obtain ⟨M₀, hM₀, h2⟩ := xiAt_transport_tw I l hok u a i hi (A.b0 i (A.chOf i c)) (A.b0 (i + 1) (A.chOf (i + 1) c'))
    (A.p0 i (A.chOf i c)) ((I.stp u a i).rep c) (A.p0 (i + 1) (A.chOf (i + 1) c')) ((I.stp u a (i + 1)).rep c')
    (A.kb i (A.chOf i c)) (((A.K i hi0 (A.chOf i c)).y ⟨c, rfl⟩).1)
    (A.kb (i + 1) (A.chOf (i + 1) c')) (((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1)
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 (hq.of_extTo hQ hd0) (hq'.of_extTo hQ hd0) hr.2 hr'.2
  refine ⟨d * M₀, Nat.mul_pos hd hM₀, fun γ γ₀ v hv _ hγ => ?_⟩
  have hc := h1 g g' _ _ hy hy' M₀ γ γ₀ v hv hγ
  refine congrArg B.embLL ((h2 _ _ hc).trans ?_)
  rw [← hr.1, ← hr'.1]
  rfl

end GlobalTheory.AdForm.TwResid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ChartLevRead

theorem exists_finM_GfC {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (Lev.finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem levData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat), ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)), (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧ (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧ (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) := by
  intro B X I l Z i hi T bad cl stab _ lat K
  refine ⟨GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev, ?_⟩
  have huniq : ∀ κ κ' : K.lev.U, κ.1.1 = κ'.1.1 → κ = κ' := fun κ κ' h => Subtype.ext (Units.ext h)
  let φ : (GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev : Subgroup _) → K.lev.U :=
    fun g => (Subgroup.mem_inf.1 g.2).2.choose
  have hφ : ∀ g, (φ g).1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := fun g => (Subgroup.mem_inf.1 g.2).2.choose_spec
  let Φ : (GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev : Subgroup _) →* K.lev.U :=
    MonoidHom.mk' φ (fun a b => huniq _ _ (by
      show (φ (a * b)).1.1 = (φ a).1.1 * (φ b).1.1
      rw [hφ, hφ, hφ]
      exact StabMove.finM_mul _ _ a.1 b.1))
  choose h hG hh using fun c => exists_finM_GfC _ (rankN (I.rec7 l Z) i hi) (K.y c)
  refine ⟨K.lev.chi.comp Φ, h, fun g => ?_, fun g κ hκ => ?_, fun c => ⟨hG c, hh c⟩⟩
  · rw [Subgroup.mem_inf]; rfl
  · show K.lev.chi (φ g) = K.lev.chi κ
    exact congrArg K.lev.chi (huniq (φ g) κ ((hφ g).trans hκ.symm))

end GlobalTheory.ChartLevRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevConj

variable {D : D7}

theorem mem_idAt_of_eq {P : Pl D → Prop} {v : Pl D} (hv : P v) {a : AE D} (ha : a ∈ idAt D (· = v)) : a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (by rw [hw]; exact hv)⟩⟩

theorem latV_supp_iff (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (by rw [hw]; exact hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => mem_idAt_of_eq hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          exact h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem moves_at_of_moves {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) {g : GA D S} (h : Moves S g L L P) : Moves S g L L (· = v) := by
  intro y hy
  rw [← latV_supp_iff S L hL hv y hy, ← latV_supp_iff S L hL hv _ (GlobalTheory.FinPl.KOpen.supp_mulVec S _ g hy)]
  exact h y fun i => mem_idAt_of_eq hv (hy i)

end GlobalTheory.LevConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

namespace GlobalTheory.AdForm.ChiCont


set_option maxHeartbeats 2000000 in
theorem chi_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u a Ch A hA i hi β
  obtain ⟨n, hn, hfin⟩ := hA.fin i hi β
  let Vs : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) :=
    {v | ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)}
  have hVs : Vs.Finite := by
    have e : Vs = ⋃ P : SBof I a, {v | Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)} := by
      ext v; simp [Vs]
    rw [e]
    refine Set.finite_iUnion fun P => Set.Subsingleton.finite ?_
    intro v hv w hw
    exact HeightOneSpectrum.ext (hv.trans hw.symm)
  have hbad : ∀ v ∈ A.bad i, v ∈ Vs := fun v hv => _root_.GlobalTheory.Mem.Col2.AdT.exists_SBof_over_sub I hI hP l Z a v (hA.bad_le i hi v hv)
  have hker := GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
    (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev Vs hVs hbad (by
    rintro v ⟨P, hv⟩
    obtain ⟨N, hN⟩ := GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace I hI hP l Z a (B.T u) i hi (A.bad i) (A.K i hi β).lev n hn hfin P v hv
    have h2 := GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) ((I.rec7 l Z).R.N i) N
      (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    exact h2.mono fun w hw x hx hxw => hN x hx w hw hxw)

  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  haveI : IsTopologicalGroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let Φ : A.U i β →* GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    (GlobalTheory.ClassSumLevel.finGLHom ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)).comp (A.U i β).subtype
  have hΦc : Continuous Φ := (GlobalTheory.ClassSumLevel.continuous_finGLHom _ _).comp continuous_subtype_val
  have ht : Tendsto Φ (nhds 1) (nhds 1) := by
    have := hΦc.tendsto 1
    rwa [map_one] at this
  have hev : ∀ᶠ g in nhds (1 : A.U i β), (1 : ℂˣ) = A.chi i β g := by
    filter_upwards [ht.eventually hker] with g hg
    obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
    rw [hA.chi i hi β g κ hκ]
    exact (hg κ (Units.ext (hκ.trans rfl))).symm
  have hχ : Continuous (A.chi i β) := by
    refine continuous_of_continuousAt_one (A.chi i β) ?_
    exact continuousAt_const.congr hev
  exact Units.continuous_val.comp hχ

end GlobalTheory.AdForm.ChiCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem natInv_mem_adicIntegers (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((T : F)⁻¹) ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (T : F) = 1 := by
    have : (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h2, map_inv₀, h1, inv_one]

theorem natInv_smul_mem_intAf (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) (α : Af F) (h1 : α ∈ intAf F) (h2 : ∀ w, w ≠ v → evalV F w α = 0) :
    ((T : F)⁻¹ : F) • α ∈ intAf F ∧ ∀ w, w ≠ v → evalV F w (((T : F)⁻¹ : F) • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · change evalV F w _ ∈ w.adicCompletionIntegers F
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      rw [Algebra.smul_def]
      exact mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)
    · rw [h2 w hw, smul_zero]; exact zero_mem _
  · rw [map_smul, h2 w hw, smul_zero]

theorem smul_pairA_zero (F : Type) [Field F] [NumberField F] (t : F) (α : Af F) :
    t • pairA F 0 α = pairA F 0 (t • α) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact Prod.ext (mul_zero _) rfl

theorem pairA_zero_tmul_smul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (t : F) (α : Af F) (c : E) :
    pairA F 0 α ⊗ₜ[F] (t • c) = pairA F 0 (t • α) ⊗ₜ[F] c := by
  rw [← smul_pairA_zero, TensorProduct.smul_tmul]

theorem idV_natInv_mul_le (D : D7) (𝔠 : FI D) (T : ℕ) (v : Pl D) (h : ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    idV (FractionalIdeal.spanSingleton _ ((T : D.host.E)⁻¹) * 𝔠) v ≤ idV 𝔠 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨c, hc, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 ha
  have e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c := by
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  obtain ⟨g1, g2⟩ := natInv_smul_mem_intAf D.host.F T v h α h1 h2
  refine AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩
  rw [e]
  exact pairA_zero_tmul_smul D.host.F D.host.E _ α c

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumListConsEqIdempotentTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.PutIn

theorem datJ_cons : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι), i ∉ J → (∀ j ∈ J, (p i).e * (p j).e = 0) → GlobalTheory.FinPl.PutIn.datJ p α β Ψ (i :: J) = GlobalTheory.FinPl.PutIn.tens (p i).e (GlobalTheory.FinPl.PutIn.datJ p α β Ψ J) (extFun (α i) (β i) (Ψ i)) := by
  intro D k _ _ _ _ ι p n n' _ _ _ _ S T α β Ψ i J _ horth
  funext t
  have he : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact horth j hj
  have hii : (p i).e * (p i).e = (p i).e := (p i).split.1

  have hhalf : IsHalf (eSum p (i :: J)) t ↔ IsHalf (eSum p J) (t - (p i).e • t) := by
    rw [eSum_cons]
    constructor
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero]
      linear_combination this
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero] at this
      linear_combination this
  have hself : IsHalf (p i).e ((p i).e • t) := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hii]
  have hrdi : rd (α i) (β i) ((p i).e • t) = rd (α i) (β i) t := by
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, pr_e]
  have hrdj : ∀ j ∈ J, rd (α j) (β j) (t - (p i).e • t) = rd (α j) (β j) t := by
    intro j hj
    have h0 : (p j).pr (p i).e = 0 := pr_of_mul_eq_zero (p j) (by rw [mul_comm]; exact horth j hj)
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_sub, h0]
  have hprod : (J.map fun j => Ψ j (rd (α j) (β j) (t - (p i).e • t))).prod = (J.map fun j => Ψ j (rd (α j) (β j) t)).prod := by
    congr 1
    exact List.map_congr_left fun j hj => by rw [hrdj j hj]
  simp only [datJ, tens, extFun, if_pos hself, hrdi, List.map_cons, List.prod_cons]
  by_cases h : IsHalf (eSum p J) (t - (p i).e • t)
  · rw [if_pos (hhalf.2 h), if_pos h, hprod, mul_comm]
  · rw [if_neg (fun h' => h (hhalf.1 h')), if_neg h, zero_mul]

end GlobalTheory.FinPl.PutIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_component_ringHom_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | exact GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | (intros; apply GlobalTheory.FinPl.SplitPhi.exists_ringHom_int <;> assumption)
end

