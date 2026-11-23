module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0079
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIndexPlaceEqOfReadsStdOfMem
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoPlace
end GlobalTheory.XGeoPlace
theorem GlobalTheory.XGeoPlace.exists_index_place_eq_of_readsStd_of_mem : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (PP : Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (_ : MeasurableSpace k) (_ : BorelSpace k) (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP ∧ q.v = PP.under (𝓞 (I.rec7 l Z).host.F) ∧ q.UnitAA ∧ valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u PP hPP
  have hC := hW.pk.bot.hyp.2.2.2.1
  have hnc : ¬ Lev.IsConjPl PP PP := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl (_root_.GlobalTheory.Fam.pk_z W) W.Q.F.lv2 hC.lev hC.grp PP hg PP hg
    · exact (hC.lev.Q_pl t PP ht).2 PP ht
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hnc
  obtain ⟨k, _, _, _, _, q, hqe, hqv, hint, -⟩ := GlobalTheory.LocMod.SplitCompl.exists_place _ PP e he
  obtain ⟨ℓ, hℓ, hℓP, h2q, hd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal ∧
      (B.host.QS * B.host.q).Coprime ℓ ∧ B.host.d.Coprime ℓ := by
    rcases hPP with hg | ⟨t, ht⟩
    · have hgg := hW.lev.1.1 PP hg
      rw [Nat.cast_mul] at hgg
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((B.host.g i : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rcases PP.isPrime.mem_or_mem hgg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hc : (B.host.g i).Coprime (B.host.QS * B.host.q * B.host.d) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.g_cond i, Nat.gcd_one_left]
      refine ⟨B.host.g i, B.host.g_prime i, hi, (hc.coprime_dvd_right ⟨B.host.d, rfl⟩).symm,
        (hc.coprime_dvd_right (Dvd.intro_left _ rfl)).symm⟩
    · have hoff := (hC.lev.Q_off t PP ht).1
      obtain ⟨ℓ, hℓ, hℓP⟩ := GlobalTheory.XGeoPlace.exists_prime_mem_pl PP
      have key : ∀ m : ℕ, m ∣ B.host.QS * B.host.q * B.host.d * (I.rec7 l Z).sp.T → m.Coprime ℓ := fun m hm =>
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdv =>
          hoff (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (hdv.trans hm)) hℓP))
      exact ⟨ℓ, hℓ, hℓP, key _ ⟨B.host.d * (I.rec7 l Z).sp.T, by ring⟩, key _ ⟨B.host.QS * B.host.q * (I.rec7 l Z).sp.T, by ring⟩⟩
  have hv : (ℓ : 𝓞 (I.rec7 l Z).host.F) ∈ q.v.asIdeal := by
    rw [hqv, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
    exact hℓP
  have hcc : (Ideal.absNorm (I.rec7 l Z).host.ccK).Coprime ℓ := by
    show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _
  have hU : q.UnitAA := GlobalTheory.SeeSaw.StdOff.unitAA_of q hℓ hv h2q hd hcc
  have hT : (((B.T u : ℕ)) : 𝓞 (I.rec7 l Z).host.E) ∉ PP.asIdeal := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact Formalism.L2.Col.T_notMem_vGs l.pr u ⟨PP, (hW.lev.2.1 PP).1 hg⟩
    · exact (hC.lev.Q_off t PP ht).2 u
  set π : 𝓞 (I.rec7 l Z).host.E := X.piT u with hπdef
  have hπ : π ∉ PP.asIdeal := fun h => hT (by
    have h2 := PP.asIdeal.mul_mem_left (B.fields.conjO ((B.primes X).piT u)) h
    have h3 : (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) ∈ PP.asIdeal := by
      rw [mul_comm]
      exact h2
    rw [l.pr.piT_norm u] at h3
    exact h3)
  have hπ0 : (π : (I.rec7 l Z).host.E) ≠ 0 := fun h0 => hπ (by
    rw [show π = 0 from RingOfIntegers.coe_injective (by simpa using h0)]
    exact zero_mem _)
  have e1 : (GlobalTheory.XGeoStd.piE I l Z u) = (π : (I.rec7 l Z).host.E) := rfl
  have hin1 := (hint (π : (I.rec7 l Z).host.E)).2 ⟨π, 1, fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hin2 := (hint (π : (I.rec7 l Z).host.E)⁻¹).2 ⟨1, π, hπ, by simp [hπ0]⟩
  have hinv : (GlobalTheory.LocMod.ofSplit q).pr ((π : (I.rec7 l Z).host.E)⁻¹) = ((GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E))⁻¹ := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _ = (((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _)⁻¹
    exact map_inv₀ _ _
  have hne : (GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E) ≠ 0 := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) (π : (I.rec7 l Z).host.E) ≠ 0
    exact (map_ne_zero _).2 hπ0
  rw [hinv] at hin2
  rw [Valuation.mem_integer_iff] at hin1 hin2
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, borel k, @BorelSpace.mk _ _ (borel k) rfl, q, hqe ▸ he, hqv, hU, ?_⟩
  rw [e1]
  rw [map_inv₀] at hin2
  exact le_antisymm hin1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hne))).1 hin2)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocXStd
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
set_option maxHeartbeats 4000000 in
theorem exists_locX_std_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX) (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((_root_.GlobalTheory.Fam.pk_z W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (_root_.GlobalTheory.Fam.pk_z W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _
  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]
end GlobalTheory.XGeoStd.Frames
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgOfSerAlg
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
      ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
        ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_of_serAlg_alt (hS : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt) : _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine hS.imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf => ?_⟩
  obtain ⟨n, z, g, hz, hsum⟩ := hx0 x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hp.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  refine exists_algExp p.nexp p.v₀ hρ _ j _ hU hW (Z.vec j) hK _ z g hz ?_
  rw [← hsum, ← hf]
  exact (smul_inv_smul₀ hN.1 _).symm
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerRefAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∃ ν₀ : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν₀ ∧ RatBase (rdAt p w j hρ ν₀) ∧
    ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
      P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
        ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
          ν₀ • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
theorem serAlg_of_serRef_scaleRoot (hR : _root_.GlobalTheory.BigOn.Exp.SerRefAlt) (hS : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis) : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.SerRefAlt _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hR hS).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨ν₀, hN₀, hR₀, hexp⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0
  obtain ⟨n, z, g, hz, hsum⟩ := hexp s h P hd hP
  by_cases hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, ?_⟩
    rw [hθ, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨m, hm0, hpow⟩ := a2 hm w hw j ρ ρ hρ hρ ν₀ ν hpin hpin ⟨rfl, rfl, rfl, rfl, rfl⟩ hN₀ hN hR₀ hR0 s h P hd hP hθ
    have h0 : ν₀ ≠ 0 := hN₀.1
    have hζ : (ν / ν₀) ^ m = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ h0)]
    refine ⟨n, fun k => ν / ν₀ * z k, g, fun k => ?_, ?_⟩
    · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
      exact (hmem _).1 (mul_mem ((hmem _).2 (isAlgebraic_of_pow_eq_one hm0 hζ)) ((hmem _).2 (hz k)))
    · conv_lhs => rw [← div_mul_cancel₀ ν h0]
      rw [mul_smul, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.FlatVal
variable {D : D7} {L : SizeData₂ D}
theorem flat_val_alt : _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  intro hF
  refine Closed.imp (Closed.and hF (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩
  obtain ⟨x0, h⟩ := h1.and h2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨a, b⟩ := h x hx hle ι p hp
  have hN := b i
  have hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _ := a i hi Y hY
  have hT := p.fw.laws
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hpos := Inhab.rank_pos _ hT.pins _ hj
  refine ⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩
  · rw [hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]
    have e : ∀ u v : ℝ, -u - v + u = -v := fun u v => by ring
    rw [e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)
  · exact (GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1
      fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)
end GlobalTheory.CovTop.FlatVal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBase
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFree
theorem free_base_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  have hpq : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (p.fw.laws.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hun : ∀ (g : (p.F.lv2.lvl false).P) (x : (p.T.Q.Dw ((i : ℕ) + 1)).La),
      (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) :=
    fun g x => mem_smul_top_of_coprime _ _ (by rw [sup_comm]; exact p.T.Q.l.coprime) _
      (_root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple p i PP A M hR hi hG hW hH hF g) x
  exact _root_.GlobalTheory.FreeLev.free_of_unip D.host.E p.T.Q.H (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
    (p.F.lv2.lvl false).P (fun g => (p.O i).lev (g : p.P.Gp)) D.R.r (D.host.g 0) (D.host.g 1)
    (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)}) (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)})
    hpq (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
    (sup_span_ne_top _ (D.host.g_prime 0) (by rw [hM]; exact dvd_mul_right _ _))
    (sup_span_ne_top _ (D.host.g_prime 1) (by rw [hM]; exact dvd_mul_left _ _))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    le_sup_left le_sup_left (fun g x => Submodule.smul_mono_left le_sup_left (hun g x))
    (fun g x => Submodule.smul_mono_left le_sup_left (hun g x)) (_root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram p i PP A M hR hi hG hW hH hF)
end GlobalTheory.DefFree
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoOfFrames
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QGeoAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.QGeoAt
open GlobalTheory.QGeoAt in
theorem GlobalTheory.QGeoAt.geo_of_frames_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), _root_.GlobalTheory.Fam.QAllAlt W PP → ∀ (l : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP), LocY l y v.N (_root_.GlobalTheory.Fam.pk_z W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b v hv hτ hNT PP hPP l hY hFX hFT
  obtain ⟨⟨ψk, hchar, hcond⟩, ⟨ν, hν⟩, hϖ⟩ := _root_.GlobalTheory.T.local_character_conductor_one_exists_alt W u hW a PP (Or.inr hPP) l
  obtain ⟨ϖ, hunif, hcompl⟩ := hϖ hPP
  refine ⟨{
    k := l.k
    ν := ν
    unitVol := hν
    q := l.q
    idem := l.idem
    unit := l.unit
    ψk := ψk
    char := hchar
    cond := hcond
    ϖ := ϖ
    unif := hunif
    compl := hcompl
    s := l.s
    hs := l.hs
    FX := l.FX
    FT := l.FT
    FM := l.FM
    FY := hY.FY
    sc := hY.sc
    sc_ne := fun j h => by simpa [h] using hY.sc_unit j
    sc_step := hY.sc_step
    bes := hY.bes
    jac := hY.jac
    z₀ := fun r => (ofSplit l.q).pr (a.ζ₀ r)
    last := l.last
    tau := fun h => by rw [hτ]; exact hY.tau h
    latX := l.latX
    latM := l.latM
    latY := hY.latY
    latT := by rw [hNT]; exact l.latT
    gl := fun j d hd => glOf (ofSplit l.q) _ (hY.FY j d hd)
    gl_loc := fun j d hd g => glOf_loc (ofSplit l.q) _ (hY.FY j d hd) g
    frame := fun j d hd => by
      obtain ⟨e, he, hm⟩ := hY.frame j d hd
      refine ⟨e, he, ?_⟩
      simpa using hm
    frameTop := l.frameTop }, hFX, hFT, rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostNStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRange_kapAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @_root_.GlobalTheory.FrameOf.kapSt_alt | exact _root_.GlobalTheory.FrameOf.kapSt_alt | (intros; apply _root_.GlobalTheory.FrameOf.kapSt_alt <;> assumption)
end
end

