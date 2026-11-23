module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGeometricMeasureVolume
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MeasCommon

open scoped ENNReal NNReal

theorem common_measure : ∀ (D : D7) (V : HSp D) (T : Type) (K : T → Subgroup (GL (Fin V.rank) (Lev.EAf D))) (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop), (∀ ρ m, good ρ m → m.IsHaarMeasure) → ∀ (μf : Measure (GfC V)), μf.IsHaarMeasure → ∀ (ν : T → Measure (GA D V)), (∀ t, Lev.IsMeasLevW V (K t) good (ν t)) → ∃ ν₀ : Measure (GA D V), ν₀.IsHaarMeasure ∧ ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 ∧ μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ ∧ μf {k | Lev.finE V k.1 ∈ K t} • ν t = ν₀ := by
  intro D V T K good hgood μf hμf ν hν
  haveI : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  obtain ⟨μR, μi, hR, hprod⟩ := _root_.GlobalTheory.AdelicHaarProd.haar_prod D V μf hμf
  obtain ⟨hdec, hfin⟩ := _root_.GlobalTheory.AdelicSplitParts.split_parts D V
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨μR, hR, fun t => isEmptyElim t⟩
  obtain ⟨⟨θ, hθ⟩, hθall⟩ := (hν t₀).2
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := hAall A hA
  obtain ⟨B, hBm, hB0, hBT⟩ := _root_.GlobalTheory.haar_box_prod_finite_pos D.what₂.Tau (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) m
    (fun ρ => hgood ρ _ (hm ρ))
  haveI hνH : ∀ t, (ν t).IsHaarMeasure := fun t => (hν t).1
  let S : Set (GinfC V) := {a | ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) (a : GA D V)}
  have key : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) * (μi S * μf {k | Lev.finE V k.1 ∈ K t}) = ∏ ρ, m ρ (B ρ) := by
    intro t
    haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hbox := (((hν t).2.2 θ hθ).2 A hA).2 m hm B hBm
    have hset : {h : GA D V | Lev.finE V h ∈ K t ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} =
        {h | ∃ a ∈ S, ∃ k ∈ {k : GfC V | Lev.finE V k.1 ∈ K t}, h = (a : GA D V) * k} := by
      ext h
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, k, hk, rfl⟩ := hdec h
        obtain ⟨e1, e2⟩ := hfin a ha k hk
        refine ⟨⟨a, ha⟩, fun ρ => ?_, ⟨k, hk⟩, ?_, rfl⟩
        · obtain ⟨b, hb, hb'⟩ := h2 ρ
          exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
        · show Lev.finE V k ∈ K t
          rw [← e1]; exact h1
      · rintro ⟨a, ha, k, hk, rfl⟩
        obtain ⟨e1, e2⟩ := hfin a.1 a.2 k.1 k.2
        refine ⟨by rw [e1]; exact hk, fun ρ => ?_⟩
        obtain ⟨b, hb, hb'⟩ := ha ρ
        exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
    rw [e, hset, Measure.smul_apply, hprod] at hbox
    rw [← hbox, ENNReal.smul_def, smul_eq_mul]
  have hc0 : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ 0 := fun t => by
    haveI : (ν t).IsHaarMeasure := (hν t).1
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure (ν t) μR).ne'
  have hcT : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ ⊤ := fun t => ENNReal.coe_ne_top
  have hX0 : μi S ≠ 0 := fun h0 => hB0 (by rw [← key t₀, h0, zero_mul, mul_zero])
  have hY0 : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 := fun t h0 => hB0 (by rw [← key t, h0, mul_zero, mul_zero])
  have hXT : μi S ≠ ⊤ := fun h0 => hBT (by rw [← key t₀, h0, ENNReal.top_mul (hY0 t₀), ENNReal.mul_top (hc0 t₀)])
  have hYT : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ := fun t h0 =>
    hBT (by rw [← key t, h0, ENNReal.mul_top hX0, ENNReal.mul_top (hc0 t)])
  refine ⟨((∏ ρ, m ρ (B ρ)) / μi S) • μR, ?_, fun t => ⟨hY0 t, hYT t, ?_⟩⟩
  · exact Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.2 ⟨hB0, hXT⟩).ne' (ENNReal.div_ne_top hBT hX0)
  · haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hv : μf {k | Lev.finE V k.1 ∈ K t} * ((ν t).haarScalarFactor μR : ℝ≥0∞) = (∏ ρ, m ρ (B ρ)) / μi S := by
      rw [ENNReal.eq_div_iff hX0 hXT, ← key t]
      ring
    rw [← hv]
    conv_lhs => rw [e]
    ext s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_assoc]

noncomputable def volOf {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : Vol V :=
  ⟨μ, (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose, h,
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose_spec⟩

@[simp] theorem volOf_μ {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : (volOf μ h).μ = μ := rfl

theorem measures_common : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (b : ∀ j, GA D (Yc D j)), (∀ j, j ≤ D.R.m → (a.x j).Is) → ∃ m : YMeas y, GeoMeas (pk W) (mkGeo m b) ∧ (commOf (pk W) u (mkGeo m b)).VolLast := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y b _
  have hM : (pk W).IsModels := hP.bot.hyp.2.2.2.1.models
  have hm2 := D.R.two_le_m
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V =>
    (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have hf : ∀ j, ∃ μ : Measure (GfC (Yc D j)), μ.IsHaarMeasure := fun j =>
    (_root_.GlobalTheory.HaarExist.haar_exists D (Yc D j)).1
  choose μf hμf using hf
  obtain ⟨μT, hμT⟩ := (_root_.GlobalTheory.HaarExist.haar_exists D D.sp.X').1
  choose ρJ hρJ using fun j ρ h => ((_root_.GlobalTheory.HaarExist.haar_exists D (Yc D (j + 1))).2 _ _ (y.jac j ρ h).d).1
  choose ρB hρB using fun j ρ h => ((_root_.GlobalTheory.HaarExist.haar_exists D (Yc D j)).2 _ _ (y.bes j ρ h).d).2 _ _ (y.bes j ρ h).o
  have hc : ∀ k, ∃ ν₀ : Measure (GA D (Yc D k)), ν₀.IsHaarMeasure ∧ (k < D.R.m → ∀ t,
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ 0 ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ ⊤ ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} •
        (pk W).νY t k = ν₀) := by
    intro k
    by_cases hk : k < D.R.m
    · have hw : ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D k).sig (tauE D ρ)).1 ((Yc D k).sig (tauE D ρ)).2) → Prop,
          (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧ ∀ t, Lev.IsMeasLevW (Yc D k)
            (Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)) good ((pk W).νY t k) := by
        by_cases hk' : k + 1 < D.R.m
        · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ h => h.1, fun t => (hM.νY t k hk').1⟩
        · obtain rfl : k = D.R.m - 1 := by omega
          exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ h => h.1, fun t => (hM.νY' t).1⟩
      obtain ⟨good, hg, hw⟩ := hw
      obtain ⟨ν₀, h1, h2⟩ := common_measure D (Yc D k) _ _ good hg (μf k) (hμf k) _ hw
      exact ⟨ν₀, h1, fun _ => h2⟩
    · exact ⟨_, (Classical.choice (GlobalTheory.Unf.VolExist.nonempty_vol (Yc D k))).haar, fun h => absurd h hk⟩
  choose ν₀ hν₀H hν₀ using hc
  obtain ⟨ν₀T, hν₀TH, hν₀T⟩ := common_measure D D.sp.X' _
    (fun t => Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t))
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1) μT hμT (fun t => (pk W).νX t)
    (fun t => (hM.νX t).1)
  have hLH : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).IsHaarMeasure :=
    fun j h => _root_.GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure D _ _ _ _ (a.x (j + 1)).vol.haar
  let vS : ∀ j, Vol (Yc D (j + 1)) := fun j => if h : j + 2 * 0 + 2 = D.R.m then volOf _ (hLH j h)
    else volOf (ν₀ (j + 1)) (hν₀H (j + 1))
  have hvS1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (vS j).μ = Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ := by
    intro j h; simp only [vS, dif_pos h, volOf_μ]
  have hvS2 : ∀ j, ¬ (j + 2 * 0 + 2 = D.R.m) → (vS j).μ = ν₀ (j + 1) := by
    intro j h; simp only [vS, dif_neg h, volOf_μ]
  let vol : ∀ k, Vol (Yc D k) := fun k => Nat.casesOn (motive := fun k => Vol (Yc D k)) k (volOf (ν₀ 0) (hν₀H 0)) vS
  let κ : ℕ → ℝ := fun k => Nat.casesOn (motive := fun _ => ℝ) k 1 fun j => if h : j + 2 * 0 + 2 = D.R.m then
    ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) else 1
  have hκ1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), κ (j + 1) =
      ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) := by
    intro j h; simp only [κ, dif_pos h]
  have hκ2 : ∀ k, k + 1 ≠ D.R.m → κ k = 1 := by
    intro k hk
    cases k with
    | zero => rfl
    | succ j => simp only [κ, dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)]
  have hκpos : ∀ k, 0 < κ k := by
    intro k
    by_cases hk : k + 1 = D.R.m
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h : j + 2 * 0 + 2 = D.R.m := by omega
      rw [hκ1 j h]
      haveI := hLH j h
      haveI := hν₀H (j + 1)
      exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
    · rw [hκ2 k hk]; exact one_pos
  have hset : ∀ k (β : GL (Fin (Yc D k).rank) (Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D k).rank),
      ({g : GfC (Yc D k) | g.1 ∈ levS _ β Ld} : Set (GfC (Yc D k))) =
        {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram β Ld} := by
    intro k β Ld; ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  refine ⟨⟨vol, volOf ν₀T hν₀TH, μf, μT, ρJ, ρB, κ⟩, ⟨hμf, hμT, hρJ, hρB, hκpos, ?_, ?_⟩, ?_⟩
  · intro t j hj
    have hX := hν₀ (j + 1) hj t
    show (vS j).μ = _
    rw [GlobalTheory.Fam.volLev, if_pos hj]
    change (vS j).μ = ENNReal.ofReal (κ (j + 1) * (μf (j + 1) {g | g.1 ∈ levS _ ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)}).toReal) • (pk W).νY t (j + 1)
    rw [hset]
    obtain ⟨hX0, hXT, hXe⟩ := hX
    generalize μf (j + 1) {g | Lev.finE (Yc D (j + 1)) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)} = X at hX0 hXT hXe ⊢
    by_cases hL : j + 2 * 0 + 2 = D.R.m
    · rw [hvS1 j hL, hκ1 j hL]
      haveI := hLH j hL
      haveI := hν₀H (j + 1)
      have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ) (ν₀ (j + 1))
      generalize (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) = c at e ⊢
      rw [e, ← hXe, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXT, mul_smul]
      ext s _
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    · rw [hvS2 j hL, hκ2 (j + 1) (by omega), one_mul, ENNReal.ofReal_toReal hXT, hXe]
  · intro t
    obtain ⟨hX0, hXT, hXe⟩ := hν₀T t
    show ν₀T = _
    rw [GlobalTheory.Fam.volLev, if_neg (by omega)]
    change ν₀T = ENNReal.ofReal (κ D.R.m * (μT {k | k.1 ∈ levS _ (pk W).βX ((pk W).datXt t)}).toReal) • (pk W).νX t
    rw [hκ2 D.R.m (by omega), one_mul]
    have hs : {g : GfC D.sp.X' | g.1 ∈ levS _ (pk W).βX ((pk W).datXt t)} =
        {g | Lev.finE D.sp.X' g.1 ∈ Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)} := by
      ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [hs, ENNReal.ofReal_toReal hXT, hXe]
  · intro j h
    exact hvS1 j h

end GlobalTheory.MeasCommon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.CellLevels

variable {D : D7}

private theorem congGrp_mono' (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  unfold congGrp at hg ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  rw [← Ideal.Quotient.factor_comp_mk h, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, map_one]

private theorem idAt_mono_decorated_lattice {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro x hx
  unfold idAt at hx ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem grpAt_le_of_imp (V : HSp D) {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : grpAt V P ≤ grpAt V P' := by
  unfold grpAt
  exact congGrp_mono' V (idAt_mono_decorated_lattice h)

def commProd {G : Type*} [Group G] (A B : Subgroup G) (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [mul_assoc, ← mul_assoc b, h b hb a' ha']; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [_root_.mul_inv_rev, h _ (B.inv_mem hb) _ (A.inv_mem ha)]⟩

private theorem idAt_inf_le_idAt_and (P P' : Pl D → Prop) : idAt D P ⊓ idAt D P' ≤ idAt D (fun p => P p ∧ P' p) := by
  intro x hxx
  have hx := (Ideal.mem_inf.1 hxx).1
  have hx' := (Ideal.mem_inf.1 hxx).2
  unfold idAt at hx hx' ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx hx' ⊢
  refine ⟨hx.1, fun w => ?_⟩
  by_cases hp : P w.1
  · exact hx'.2 ⟨w.1, fun h' => w.2 ⟨hp, h'⟩⟩
  · exact hx.2 ⟨w.1, hp⟩

private theorem congGrp_inf_le_congGrp_inf (V : HSp D) (I J : Ideal (AE D)) : congGrp V I ⊓ congGrp V J ≤ congGrp V (I ⊓ J) := by
  intro g hg
  have hI := (Subgroup.mem_inf.1 hg).1
  have hJ := (Subgroup.mem_inf.1 hg).2
  unfold congGrp at hI hJ ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hI hJ ⊢
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have eI := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hI i j
  have eJ := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hJ i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] at eI eJ ⊢
  split_ifs at eI eJ ⊢ with hij
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩

private theorem mem_grpAt_and_of_mem_grpAt (V : HSp D) {P P' : Pl D → Prop} {g : GA D V} (h : g ∈ grpAt V P) (h' : g ∈ grpAt V P') :
    g ∈ grpAt V (fun p => P p ∧ P' p) := by
  unfold grpAt at h h' ⊢
  exact congGrp_mono' V (idAt_inf_le_idAt_and P P') (congGrp_inf_le_congGrp_inf V _ _ ⟨h, h'⟩)

private theorem inK_congr_of_iff {V : HSp D} {L : Lat V} {P P' : Pl D → Prop} (h : ∀ p, P p ↔ P' p) (κ : GA D V) :
    InK V L P κ ↔ InK V L P' κ := by
  rw [show P = P' from funext fun p => propext (h p)]

private theorem mem_grpAt_of_inK {V : HSp D} {L : Lat V} {P : Pl D → Prop} {κ : GA D V} (h : InK V L P κ) : κ ∈ grpAt V P := by
  unfold InK at h
  exact h.1

theorem levels : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  intro D V L gP Q JG hL hdisj hJle hJc hJo
  obtain ⟨-, -, -, hQcle, -, -, -, -, hKQ, -⟩ := _root_.GlobalTheory.FinPl.SetCut.grp_split D V Q
  obtain ⟨-, -, -, -, hPcomm, ⟨e, he⟩, -, -, -, -⟩ := _root_.GlobalTheory.FinPl.SetCut.grp_split D V gP
  have hQP : ∀ p, p ∈ Q → p ∉ gP := fun p hp => Finset.disjoint_left.mp hdisj hp

  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hKQ L hL (· ∈ Q)

  obtain ⟨⟨K₃, hK₃, hK₃c, hK₃o⟩, -⟩ := hKQ L hL (fun p => p ∉ gP ∧ p ∉ Q)
  have hpq : ∀ p, (p ∉ gP ∧ p ∈ Q) ↔ p ∈ Q := fun p => ⟨And.right, fun h => ⟨hQP p h, h⟩⟩

  have hsplit : ∀ κ, InK V L (· ∉ gP) κ ↔
      ∃ a b, InK V L (· ∈ Q) a ∧ InK V L (fun p => p ∉ gP ∧ p ∉ Q) b ∧ κ = a * b := by
    intro κ
    refine ((hKQ L hL (· ∉ gP)).2 κ).trans ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).1 ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).2 ha, hb, rfl⟩
  have hK₁le : K₁ ≤ grpAt V (· ∈ Q) := fun g hg => mem_grpAt_of_inK ((hK₁ g).1 hg)
  have hK₃le : K₃ ≤ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := fun g hg => mem_grpAt_of_inK ((hK₃ g).1 hg)
  have hJQ : grpAt V (· ∈ gP) ≤ grpAt V (· ∉ Q) := grpAt_le_of_imp V fun p hp hq => hQP p hq hp

  have hc : ∀ b ∈ JG, ∀ a ∈ K₃, b * a = a * b := fun b hb a ha =>
    hPcomm b (hJle hb) a (grpAt_le_of_imp V (fun p hp => hp.1) (hK₃le ha))
  have hmem : ∀ g, g ∈ commProd K₃ JG hc ↔ ∃ a ∈ K₃, ∃ b ∈ JG, g = a * b := fun g => Iff.rfl
  refine ⟨K₁, commProd K₃ JG hc, hK₁, hK₁le, ?_, hK₁c, ?_, hK₁o, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hmem g).1 hg
    exact mul_mem (grpAt_le_of_imp V (fun p hp => hp.2) (hK₃le ha)) (hJQ (hJle hb))
  · have hset : (commProd K₃ JG hc : Set (GA D V)) =
        (fun p : GA D V × GA D V => p.1 * p.2) '' ((K₃ : Set (GA D V)) ×ˢ (JG : Set (GA D V))) := by
      ext g
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [hset]
    exact (hK₃c.prod hJc).image continuous_mul
  ·
    obtain ⟨φ, hφc, hφ, hφ1⟩ : ∃ φ : grpAt V (· ∉ Q) → grpAt V (· ∈ gP) × grpAt V (· ∉ gP),
        Continuous φ ∧ (∀ g : grpAt V (· ∉ Q), (g : GA D V) = ((φ g).1 : GA D V) * (φ g).2) ∧ φ 1 = 1 := by
      refine ⟨fun g => e.symm ⟨g, hQcle g.2⟩, ?_, ?_, ?_⟩
      · exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      · intro g
        rw [← he, Homeomorph.apply_symm_apply]
      · rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [he]
        simp

    have h3 : ∀ g : grpAt V (· ∉ Q), ((φ g).2 : GA D V) ∈ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := by
      intro g
      have e2 : ((φ g).2 : GA D V) = ((φ g).1 : GA D V)⁻¹ * g := by
        rw [hφ g, inv_mul_cancel_left]
      refine mem_grpAt_and_of_mem_grpAt V (φ g).2.2 ?_
      rw [e2]
      exact mul_mem (inv_mem (hJQ (φ g).1.2)) g.2
    obtain ⟨ψ, hψc, hψ⟩ : ∃ ψ : grpAt V (· ∉ Q) → grpAt V (fun p => p ∉ gP ∧ p ∉ Q),
        Continuous ψ ∧ ∀ g : grpAt V (· ∉ Q), (ψ g : GA D V) = (φ g).2 :=
      ⟨fun g => ⟨(φ g).2, h3 g⟩, (continuous_subtype_val.comp (continuous_snd.comp hφc)).subtype_mk _, fun _ => rfl⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hU : ψ ⁻¹' ((K₃.subgroupOf (grpAt V (fun p => p ∉ gP ∧ p ∉ Q)) : Subgroup _) :
        Set (grpAt V (fun p => p ∉ gP ∧ p ∉ Q))) ∩
        (fun g => (φ g).1) ⁻¹' ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) ∈
        nhds (1 : grpAt V (· ∉ Q)) := by
      refine IsOpen.mem_nhds ((hK₃o.preimage hψc).inter (hJo.preimage (continuous_fst.comp hφc))) ⟨?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ, hφ1]
        exact K₃.one_mem
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hφ1]
        exact JG.one_mem
    refine Filter.mem_of_superset hU ?_
    rintro g ⟨h1, h2⟩
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ] at h1
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf] at h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmem]
    refine ⟨(φ g).2, h1, (φ g).1, h2, ?_⟩
    rw [hφ g]
    exact hPcomm _ (φ g).1.2 _ (φ g).2.2
  · intro g
    rw [hmem]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, (hK₃ a).1 ha, b, hb, rfl⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      exact ⟨κ, (hK₃ κ).2 hκ, k, hk, rfl⟩
  · intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨κ, hκ, k, hk, rfl⟩ := (hmem b).1 hb
      exact ⟨a * κ, (hsplit _).2 ⟨a, κ, (hK₁ a).1 ha, (hK₃ κ).1 hκ, rfl⟩, k, hk, (mul_assoc a κ k).symm⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := (hsplit κ).1 hκ
      exact ⟨a, (hK₁ a).2 ha, b * k, (hmem _).2 ⟨b, (hK₃ b).2 hb, k, hk, rfl⟩, mul_assoc a b k⟩

end GlobalTheory.CellLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


set_option maxHeartbeats 2000000 in
open GlobalTheory.FinPl.FrameLat in
theorem exists_normOneAt_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k) (hc₀ : c₀ ≠ 0) :
    ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  have hf : ∀ x : k, (p.e + cA D p.e) * p.sec x = p.sec x := fun x => (idem_iff p _).1 (sec_mem_idAt p x)
  have hcf : ∀ x : k, (p.e + cA D p.e) * cA D (p.sec x) = cA D (p.sec x) :=
    fun x => (idem_iff p _).1 (csec_mem_idAt (p := p) x)
  have hee : p.e * cA D p.e = 0 := p.split.2.1
  have hce : cA D p.e * p.e = 0 := cAe_mul_e p
  have hecs : ∀ x : k, p.e * cA D (p.sec x) = 0 := by
    intro x
    rw [← e_mul_sec p x, map_mul, ← mul_assoc, hee, zero_mul]
  have hsc : ∀ x y : k, p.sec x * cA D (p.sec y) = 0 := by
    intro x y
    rw [← e_mul_sec p x, mul_comm p.e, mul_assoc, hecs, mul_zero]
  have hprc : ∀ x : k, p.pr (cA D (p.sec x)) = 0 := by
    intro x
    have h1 : p.sec (p.pr (cA D (p.sec x))) = 0 := by rw [p.sec_pr, hecs]
    have h2 := congrArg p.pr h1
    rwa [p.pr_sec, map_zero] at h2
  have hcc : ∀ z : AE D, cA D (cA D z) = z := fun z => cA_cA z
  have he1 : p.sec 1 = p.e := sec_one p
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = p.e + cA D p.e := ⟨_, rfl⟩
  have hfm : f ∈ idAt D (· = p.v) := hfdef ▸ sum_mem_idAt p
  have hff : f * f = f := by
    have := (idem_iff p f).1 hfm; rwa [← hfdef] at this
  have hf' : ∀ x : k, f * p.sec x = p.sec x := fun x => hfdef ▸ hf x
  have hcf' : ∀ x : k, f * cA D (p.sec x) = cA D (p.sec x) := fun x => hfdef ▸ hcf x

  obtain ⟨u, hu⟩ : ∃ u : AE D, u = 1 - f := ⟨_, rfl⟩
  have huf : u * f = 0 := by rw [hu, sub_mul, one_mul, hff, sub_self]
  have hus : ∀ x : k, u * p.sec x = 0 := by intro x; rw [← hf' x, ← mul_assoc, huf, zero_mul]
  have hucs : ∀ x : k, u * cA D (p.sec x) = 0 := by intro x; rw [← hcf' x, ← mul_assoc, huf, zero_mul]
  have huu : u * u = u := by nth_rewrite 2 [hu]; rw [mul_sub, mul_one, huf, sub_zero]
  have hcu : cA D u = u := by
    rw [hu, hfdef, map_sub, map_one, map_add (f := _), hcc, add_comm]
  refine ⟨u + p.sec c₀ + cA D (p.sec c₀⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have hconj : cA D (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) = u + cA D (p.sec c₀) + p.sec c₀⁻¹ := by
      rw [map_add (f := _), map_add (f := _), hcu, hcc]
    show _ * cA D _ = 1
    rw [hconj]
    have e1 : p.sec c₀ * p.sec c₀⁻¹ = p.e := by rw [← sec_mul p, mul_inv_cancel₀ hc₀, he1]
    have e2 : cA D (p.sec c₀⁻¹) * cA D (p.sec c₀) = cA D p.e := by
      rw [← map_mul (cA D), ← sec_mul p, inv_mul_cancel₀ hc₀, he1]
    have s1 : p.sec c₀ * u = 0 := by rw [mul_comm (p.sec c₀) u]; exact hus _
    have s2 : cA D (p.sec c₀⁻¹) * u = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) u]; exact hucs _
    have s3 : cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) (p.sec c₀⁻¹)]; exact hsc _ _
    have s4 : p.sec c₀ * cA D (p.sec c₀) = 0 := hsc _ _
    have expand : (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) * (u + cA D (p.sec c₀) + p.sec c₀⁻¹)
        = u * u + u * cA D (p.sec c₀) + u * p.sec c₀⁻¹ + p.sec c₀ * u + p.sec c₀ * cA D (p.sec c₀)
          + p.sec c₀ * p.sec c₀⁻¹ + cA D (p.sec c₀⁻¹) * u + cA D (p.sec c₀⁻¹) * cA D (p.sec c₀)
          + cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ := by ring
    rw [expand, huu, hucs, hus, s1, s4, e1, s2, e2, s3, hu, hfdef]
    ring
  · have : u + p.sec c₀ + cA D (p.sec c₀⁻¹) - 1 = -f + p.sec c₀ + cA D (p.sec c₀⁻¹) := by rw [hu]; ring
    rw [this]
    refine add_mem (add_mem (neg_mem hfm) (sec_mem_idAt p _)) (csec_mem_idAt (p := p) _)
  · rw [map_add (f := _), map_add (f := _), hprc, add_zero, hu, hfdef, map_sub, map_one, map_add (f := _), ← he1, hprc, p.pr_sec, p.pr_sec]
    ring

end GlobalTheory.Core.Mi.LatMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  first | exact @GlobalTheory.ChartsAll.exists_charts | exact GlobalTheory.ChartsAll.exists_charts | (intros; apply GlobalTheory.ChartsAll.exists_charts <;> assumption)
end

