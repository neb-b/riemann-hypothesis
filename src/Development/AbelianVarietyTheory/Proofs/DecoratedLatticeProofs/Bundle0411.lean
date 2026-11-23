module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbTopBlock

theorem iXm_entry {D : D7}
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (i : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) :
    iXm D i b = if (i : ℕ) = b then 1 else 0 := by
  have hP' : D.sp.X'.rank = D.R.N D.R.m - 1 := rankP D
  have hN' : (D.sp.X D.R.m).rank = D.R.N D.R.m := rankN D D.R.m le_rfl
  have hb : (b : ℕ) < D.sp.X'.rank := by have := b.2; omega
  have hb2 : (b : ℕ) < (D.sp.X D.R.m).rank := by have := b.2; omega
  have key : D.sp.iX' (D.sp.X'.frame ⟨b, hb⟩) = (D.sp.X D.R.m).frame ⟨b, hb2⟩ := hi _ _ rfl
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  have hs : (D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm
      (Pi.single b 1) = D.sp.X'.frame ⟨b, hb⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    ext j
    simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, key]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.EmbTopBlock

namespace GlobalTheory.EmbTopBlock

theorem piT_coe_ne_zero {B : GlobalTheory.Mem.Base} (X : PreX B.toPre) (u : B.Word) : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
  intro h0
  have hn := X.piT_norm u
  rw [h0, zero_mul] at hn
  have hT : B.T u = 0 := by exact_mod_cast hn.symm
  have h1 := X.T_gt u
  have h2 := X.a_gt
  rw [hT] at h1
  have h3 := h2.trans h1
  exact (Nat.not_lt_zero _) (by exact_mod_cast h3)

theorem isBlock_infM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  intro B X I _hOk hP l Z u θ _hθ emb hN hemb k τ
  obtain ⟨h1, h2⟩ := hemb k
  let q : AE (I.rec7 l Z) →+* ℂ := (θ τ).comp (infPart (I.rec7 l Z))
  let p : (I.rec7 l Z).host.E →+* ℂ := q.comp (incA (I.rec7 l Z))
  let G : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ := infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ
  let G' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) ℂ := infM θ _ (rankP (I.rec7 l Z)) k τ
  let J : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m - 1)) ℂ := (iXm (I.rec7 l Z)).map p
  have hF : J = Matrix.of (fun (i : Fin (B.R.N B.R.m)) (a : Fin (B.R.N B.R.m - 1)) => if (i : ℕ) = a then (1 : ℂ) else 0) := by
    ext i a
    show p (iXm (I.rec7 l Z) i a) = if (i : ℕ) = a then (1 : ℂ) else 0
    rw [iXm_entry (D := I.rec7 l Z) hP.iX i a]
    split_ifs <;> simp
  have e1 : G * J = J * G' := by
    have := congrArg (fun M => Matrix.map M q) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    exact this
  rw [hF] at e1
  have e2 : G *ᵥ (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) = fun a => p (TC.z0 X u a) := by
    funext i
    have := congrArg q (congrFun h2 i)
    exact (RingHom.map_mulVec q _ _ i).symm.trans this
  have hc0 : p ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (map_ne_zero p).2 (piT_coe_ne_zero X u)
  have hz : (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) =
      p ((X.piT u : 𝓞 B.host.E) : B.host.E) •
        (fun i : Fin (B.R.N B.R.m) => if (i : ℕ) = B.R.N B.R.m - 1 then (1 : ℂ) else 0) := by
    funext i
    simp only [TC.z0, Pi.smul_apply, smul_eq_mul]
    have := i.2
    by_cases h : (i : ℕ) + 1 = B.R.N B.R.m
    · rw [if_pos h, if_pos (by omega), mul_one]
    · rw [if_neg h, if_neg (by omega), mul_zero]
      exact map_zero p
  rw [hz, Matrix.mulVec_smul] at e2
  have e2' := smul_right_injective _ hc0 e2
  exact TC.BlockMatrixCriteria.isBlock_of_entries rfl rfl hN G G' _ _ (fun _ _ => rfl) (fun _ _ => rfl) e1 e2'

end GlobalTheory.EmbTopBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepChartBasePointCarriesStdPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.Mem.Col2.TopBase

theorem sel_under_of_mem_QE {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) {b : I.ι}
    {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q b) : I.sel (P.under (𝓞 B.fields.F)) = P := by
  unfold ColIn.Q Formalism.L2.Col.QE at hP
  split_ifs at hP with h
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hP
    congr 1
    exact HeightOneSpectrum.ext (hI.sel_ok w)
  · simp at hP

theorem topBase_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {C : Type} (chOf : (I.stp u a B.R.m).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a B.R.m).Cl → TC.GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) (k : C → TC.GA B (B.R.N B.R.m)), I.Reads u a B.R.m chOf Lb U chi y st k → (∀ β, I.TopPt l Z u a (k β)) → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m, TC.PtOf (k β) q) ∧ ∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1 := by
  intro B X I hI hP l Z u a C chOf Lb U chi y st k hR hTop β
  have hPr := (base_fields_primes_ok B X).2.1
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    rw [Formalism.L2.Col.rank_X'_eq]
    have h1 := B.R.two_le_m
    have h2 : 1 ≤ B.R.t := B.R.t_odd.pos
    have h3 : 2 ≤ B.R.m * B.R.t := le_trans h1 (Nat.le_mul_of_pos_right _ h2)
    omega⟩
  refine ⟨⟨_, GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z (hTop β)⟩, fun P hP hPa => ?_⟩
  obtain ⟨b, hb⟩ := (ColIn.mem_SQ I).1 hP
  have hq := (TwistPrimes.twist_primes_away I hI).2 u b P hb
  have hsP := sel_under_of_mem_QE I hI hb
  refine GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P (hR.k_off β _ ?_ ?_ (Or.inr ?_))
  · exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv I hI hPr u b ⟨P, hb⟩
  · rintro ⟨P', hP', hv⟩
    have hsP' := sel_under_of_mem_QE I hI hP'
    apply hPa
    have e : P' = P := by rw [← hsP', ← hsP]; exact congrArg I.sel hv
    exact e ▸ hP'
  · intro j hj
    have hv : P.under (𝓞 B.host.F) ∈ Formalism.L2.Col.plUnder B.fields.F (B.primes X).vGs := by
      refine (Formalism.L2.Col.plUnder_vGs B.sp.cm hPr _).2 ?_
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
    obtain ⟨w, hw, hov⟩ := hv
    have hovP : Formalism.L2.Col.IsOver (P.under (𝓞 B.host.F)) P := rfl
    rcases Formalism.L2.Col.rll_over_cases B.sp.cm hovP hov with e | e
    · exact hq.1.2.1 (e ▸ hw)
    · exact hq.1.2.2.2.1 (e ▸ hw)

end GlobalTheory.Mem.Col2.TopBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocAgree

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem latV_congr (S : HSp D) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w ↔ P' w) :
    latV S L P = latV S L P' :=
  le_antisymm (latV_mono S L fun w => (h w).1) (latV_mono S L fun w => (h w).2)

theorem latV_le_of_int_smul_on (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (R : Pl D → Prop) (hR : ∀ v, R v → ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L R ≤ latV S M R := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : R w
    · have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
        have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)
        have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
        have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
          map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
        exact h2.trans (h4 ▸ h1)
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_le_finite (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) (T : Finset (Pl D)) :
    latV S L (fun p => P p ∧ p ∈ T) ≤ latV S N (fun p => P p ∧ p ∈ T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact latV_le_of_int_smul_on S L N d hd hLN _ fun v hv => absurd hv.2 (Finset.notMem_empty v)
  | insert a T' ha ih =>
    intro z hz
    have hs := GlobalTheory.FinPlLoc.latV_idAt hz
    obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L _ {a} hs).1 hz
    rw [mem_latV_iff_parts S N _ {a} hs]
    constructor
    · by_cases hPa : P a
      · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∈ ({a} : Finset (Pl D))) ↔ w = a := by
          intro w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨⟨hPa, Or.inl rfl⟩, rfl⟩
        rw [latV_congr S L hiff, hP a hPa] at h1
        rw [latV_congr S N hiff]
        exact h1
      · refine latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h1
        exact absurd (Finset.mem_singleton.1 hv.2 ▸ hv.1.1) hPa
    · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∉ ({a} : Finset (Pl D))) ↔ (P w ∧ w ∈ T') := by
        intro w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hw, h | h⟩, hne⟩
          · exact absurd h hne
          · exact ⟨hw, h⟩
        · rintro ⟨hw, h⟩
          exact ⟨⟨hw, Or.inr h⟩, fun e => ha (e ▸ h)⟩
      rw [latV_congr S L hiff] at h2
      rw [latV_congr S N hiff]
      exact ih h2

theorem latV_le_of_local (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) : latV S L P ≤ latV S N P := by
  classical
  set T := (finite_places_int (D := D) d hd).toFinset
  intro y hy
  have hs := GlobalTheory.FinPlLoc.latV_idAt hy
  obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L P T hs).1 hy
  rw [mem_latV_iff_parts S N P T hs]
  refine ⟨latV_le_finite S L N d hd hLN P hP T h1, latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h2⟩
  intro hmem
  exact hv.2 ((Set.Finite.mem_toFinset _).2 hmem)

theorem latV_eq_of_local : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop),
    Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E N →
    (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) →
    GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L N hL.fg hN.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le N L hN.fg hL.span_eq_top
  exact le_antisymm (latV_le_of_local S L N d₁ hd₁ h₁ P hP)
    (latV_le_of_local S N L d₂ hd₂ h₂ P fun w hw => (hP w hw).symm)

end GlobalTheory.FinPl.LocAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceSep

variable {D : D7}

theorem natCast_mem_of_under_eq {PP PP' : Pl D.host.E}
    (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  rw [h] at h1
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP'.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (u : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem twist_prime {gp : Fin 2 → ℕ} {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces gp Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ gp i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP hP
  refine ⟨q, hq, ?_, hne⟩
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ PP.asIdeal) = q from hc] at this

theorem g_mem_of_div (P : Formalism.L2.Host.PiBar D.host) {k : Fin 2} {w : Pl D.host.E} (hw : P.Div k w) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 := P.pb_over k
  rw [← hw] at h1
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at this

end GlobalTheory.Fam.PlaceSep


open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev

  have mixed : ∀ A B : Pl D.host.E, A ∈ (pk W).Pg → QAll W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeNotMemPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem levelPrime_not_mem_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → (∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal) → ∀ PP : Pl D.host.E, PP ∈ (pk W).Pg ∨ QAll W PP → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP hg PP hPP
  rcases hPP with h | ⟨t, ht⟩
  · intro hm
    apply hg PP h
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    rw [Ideal.mem_comap, map_natCast]
    exact hm
  · exact (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  first | exact @GlobalTheory.HaarFJInt.prodRFJ_preimage_KO | exact GlobalTheory.HaarFJInt.prodRFJ_preimage_KO | (intros; apply GlobalTheory.HaarFJInt.prodRFJ_preimage_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tuplePlace_under_not_mem_tP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, QAll W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas _ _ _ _ _ _ _ _ htP _ _ _ _ FY sc _ PP hQ hmem
  obtain ⟨t, ht⟩ := hQ
  apply (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u
  have h1 := (htP _).1 hmem
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast] at h1
  exact h1

end GlobalTheory
end

