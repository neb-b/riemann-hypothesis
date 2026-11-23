module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfConjMemOfPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqAdFormsOfValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual Cols levPlus mem_cols)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

section Generic

variable {G Γ W Cl ι : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Finite Cl]


open Classical in
theorem eq_adForms_of_values (ιG : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (y : Cl → G)
    (hdec : ∀ g, ∃ (γ : Γ) (c : Cl) (k : J), g = ιG γ * y c * k) (S : Submodule ℂ (G → W))
    (hS : S ≤ Bridge.AdForms ιG ρ J 1) (w : ι → W) (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hsingle : ∀ c i, ∃ s ∈ S, ∀ c', s (y c') = if c' = c then w i else 0) : S = Bridge.AdForms ιG ρ J 1 := by
  classical
  have : Fintype Cl := Fintype.ofFinite _
  refine le_antisymm hS fun F hF => ?_
  let ev : (G → W) →ₗ[ℂ] (Cl → W) := LinearMap.pi fun c => LinearMap.proj (y c)
  have hev : ∀ f c, ev f c = f (y c) := fun _ _ => rfl
  have hinj : ∀ f ∈ Bridge.AdForms ιG ρ J 1, ev f = 0 → f = 0 := by
    intro f hf h0
    funext g
    obtain ⟨γ, c, k, rfl⟩ := hdec g
    have h1 : f (y c) = 0 := congrFun h0 c
    have h2 := hf γ (y c) k
    rw [h2, h1, map_zero, smul_zero]
    rfl
  have hsurj : S.map ev = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    rw [← Finset.univ_sum_single f]
    refine Submodule.sum_mem _ fun c _ => ?_
    have hfc : f c ∈ Submodule.span ℂ (Set.range w) := by rw [hw]; trivial
    have e : Pi.single c (f c) = LinearMap.single ℂ (fun _ : Cl => W) c (f c) := rfl
    rw [e]
    refine Submodule.mem_comap.1 (((Submodule.span_le (p := (S.map ev).comap (LinearMap.single ℂ (fun _ : Cl => W) c))).2 ?_) hfc)
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsv⟩ := hsingle c i
    refine Submodule.mem_comap.2 ⟨s, hs, funext fun c' => ?_⟩
    rw [hev, hsv]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  obtain ⟨s, hs, hse⟩ : ev F ∈ S.map ev := by rw [hsurj]; trivial
  have h0 : F - s = 0 := hinj _ (sub_mem hF (hS hs)) (by rw [map_sub, hse, sub_self])
  rwa [sub_eq_zero.1 h0]

end Generic

section Reps

variable {T' : Type} {L : LevCh D T'} {sc : Consts} {G : GridData L sc}

theorem exists_gf_reps (rp : ClassReps G) :
    ∃ y : G.ClPlus → Bridge.Gf (G.V (.top 0)),
      (∀ c, Formalism.UG.bc (Lev.swapAE D) ((y c : Bridge.Gf (G.V (.top 0))) : GL _ _) = (rp.x c : GLf G)) ∧
      ∀ g : Bridge.Gf (G.V (.top 0)), ∃ (γ : GQ (G.V (.top 0))) (c : G.ClPlus) (k : levPlus G),
        g = Bridge.ratF (G.V (.top 0)) γ * y c * k := by
  obtain ⟨hfin, -, -, -, hcl⟩ := GlobalTheory.DefFree.AdelCls.adelic_classes D (G.V (.top 0))
  choose h _ hh using fun c => hfin (rp.x c)
  refine ⟨fun c => (finHom (G.V (.top 0))).rangeRestrict (h c), fun c => ?_, fun g => ?_⟩
  · have := congrArg Subtype.val (hh c)
    exact this
  · have hg0 : ∃ h0 : GA D (G.V (.top 0)), finHom (G.V (.top 0)) h0 = g.1 := g.2
    obtain ⟨h0, hg⟩ := hg0
    have hc : GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) =
        GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0 := by
      show (Quotient.mk'' (GlobalTheory.DefFree.finU (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0))) :
        Cl D.sp.cm (G.V (.top 0)).gram G.Kplus) = _
      rw [hh]
      exact rp.classRepresentative_mk _
    have hx := (hcl G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) h0).1 hc
    obtain ⟨γ, hγ, hx⟩ := hx
    obtain ⟨κ, hκ, k, hk, e⟩ := hx
    have hκ' : (finHom (G.V (.top 0))).rangeRestrict κ ∈ levPlus G := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.top 0)) κ) ∈ G.Kplus
      exact hκ.2
    refine ⟨⟨γ, hγ⟩, GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0, ⟨_, hκ'⟩, Subtype.ext ?_⟩
    have hk1 : finHom (G.V (.top 0)) k = 1 := hk
    show g.1 = finHom (G.V (.top 0)) γ * finHom (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) *
      finHom (G.V (.top 0)) κ
    have e2 := congrArg (finHom (G.V (.top 0))) e
    simp only [map_mul (finHom (G.V (.top 0))), hk1, mul_one] at e2
    exact hg.symm.trans e2


open Classical in
theorem span_colOf_psi {θ : InfFam D} (hθ : IsInfFam θ) (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (Φ : G.Datum) :
    Submodule.span ℂ ((fun a => colOf θ (psi rp e a)) '' {a | datumOf e a = Φ}) = Cols G θ := by
  classical
  obtain ⟨y, hy, hdec⟩ := exists_gf_reps rp
  have hspan : Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)
      (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (bVV D.what₂.LL (LaP G) i))) = ⊤ := by
    have := congrArg (Submodule.map (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap)
      (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (LaP G))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this
  refine eq_adForms_of_values (W := (coefPlus G θ).W) (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ
    (levPlus G) y hdec _ ?_ _ hspan fun c i => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    exact colOf_mem hθ (psi_left _ _ a) fun g _ hk => psi_right _ _ a g hk
  · refine ⟨colOf θ (psi rp e (e.symm ((Φ, c), i))), Submodule.subset_span ⟨_, ?_, rfl⟩, fun c' => ?_⟩
    · show (e (e.symm ((Φ, c), i))).1.1 = Φ
      rw [Equiv.apply_symm_apply]
    · unfold colOf psi
      rw [hy c', Equiv.apply_symm_apply, rp.gridClassReps_delta_apply_rep (ClassReps.neat rp)]
      by_cases h : c' = c <;> simp [h] <;> rfl

end Reps

variable (ch : Choice R)

theorem span_col_eq_cols (Φ : ch.G.Datum) :
    Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}) = Cols ch.G ch.W.θ :=
  span_colOf_psi ch.W.θ_is ch.rp ch.e Φ

end GlobalTheory.RowTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem cT_mul_entry {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (U J W : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (Formalism.UG.cT σ U * J * W) a b = Formalism.UG.hform σ J (fun i => U i a) (fun i => W i b) := by
  unfold Formalism.UG.cT Formalism.UG.hform
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem over_g {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) {Q : Pl D.host.E}
    (hQ : Q ∈ R.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
  have hmem : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (Q.under (𝓞 D.host.K)).asIdeal := by
    rw [show Q.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hmem
  · exact Ideal.mul_mem_left _ _ hmem

theorem exists_frame_redIs : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL _
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    rw [show (Yc D 0).rank = D.R.rankY 0 from D.sp.Y_rank 0 (Nat.zero_le _)]
    have hm := D.R.m_even
    have h2 := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rankY Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    obtain ⟨c, hc⟩ := hm
    omega
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hG := (GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one hβ₀)).1
  have hint : ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank),
      ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ}
        (f : Fin m → Formalism.L2.SG.HidaSetting.VA I) (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
      subst h
      exact hf a
    have cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J)
        (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
        cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
      subst h
      exact hv
    have flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ)
        (e f : Fin ρ → M) (b : Fin k → M) (z : M) (he : ∀ a, e a ∈ S)
        (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
        flagV ρ k n e f b z i ∈ S := by
      unfold flagV
      split_ifs
      exacts [he _, hb _, hz, hf _, h0]
    intro PP i j
    have hF : IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hβ₀ ▸ GlobalTheory.StdFrames.isFrame_lat β₀
    have hLf := GlobalTheory.KgFrame.Lf_eq D
    have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
        Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro v hv
      rw [hLf] at hv
      exact (hF v).1 hv i
    set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf}
    have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
      show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      exact zero_mem _
    obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
    have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
    have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
    have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
    have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
    have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
    constructor
    · change Matrix.mulVec (β₀⁻¹).val (flagAt X h PP j) i ∈ _
      apply key
      unfold flagAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
    · change Matrix.mulVec (β₀⁻¹).val (pairAt X h PP j) i ∈ _
      apply key
      unfold pairAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j
  have hdet : ∀ Q ∈ R.Pg,
      Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (flagAt X h Q)).det) = 1 := by
    intro Q hQ
    have hg := over_g R hL hQ
    refine _root_.GlobalTheory.SeeConjRead.DetUnit.det_unit β₀ (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) (colMat (pairAt X h Q))
      (colMat (flagAt X h Q)) Q (fun a => sgnD D.R.rS D.R.k a) hG (fun i j => (hint Q i j).2)
      (fun i j => (hint Q i j).1) ?_ ?_
    · intro a
      unfold sgnD
      split_ifs <;> simp
    · intro a b
      rw [cT_mul_entry]
      change SmallAt Q (hY D (pairAt X h Q a) (flagAt X h Q b) - _)
      by_cases hc : GlobalTheory.StdFrames.cpt Q (ewT X h) = 1
      · rw [pairAt, flagAt, if_pos hc, if_pos hc]
        exact _root_.GlobalTheory.SeeConjRead.flagV_pair_table (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (_root_.GlobalTheory.SeeConjRead.pairTable_of_cpt_one X h Q hg hc) a b
      · rw [pairAt, flagAt, if_neg hc, if_neg hc]
        exact _root_.GlobalTheory.SeeConjRead.flagV_pair_table (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (_root_.GlobalTheory.SeeConjRead.pairTable_rev X h Q hg hc) a b
  obtain ⟨β, hβ, hred⟩ := _root_.GlobalTheory.SeeConjRead.exists_lift_redIs β₀ R.Pg (flagAt X h) (fun Q _ i j => (hint Q i j).1) hdet
  refine ⟨β, ?_, hred⟩
  rw [hβ₀, ← hβ]
  exact GlobalTheory.StdFrames.isFrame_lat β

end GlobalTheory.SeeConjRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7}

theorem prod_eq_inf (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) = P.inf fun w => w.asIdeal ^ d w :=
  (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun _ _ _ _ hne h => hne h).symm

theorem prod_ne_bot (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem idem_mem_OA {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : toEAf D e ∈ OA D := by
  obtain ⟨-, e1, e2⟩ := cpt_idemSum he
  refine (mem_OA_iff _).2 fun w => ?_
  by_cases hw : w ∈ P
  · rw [e1 w hw]; exact one_mem _
  · rw [e2 w hw]; exact zero_mem _

theorem one_sub_idem_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (d : Pl D.host.E → ℕ) :
    (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w) := by
  obtain ⟨-, e1, -⟩ := cpt_idemSum he
  refine mem_idS_of_v_le (w := fun w => w) (prod_ne_bot P d) (prod_eq_inf P d) fun w hw => ?_
  show Valued.v (cpt (D := D) w (1 - toEAf D e)) ≤ _
  rw [RingHom.map_sub, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
  exact zero_le'

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_map (hx : IsHalf e x) : x.map (toEAf D) = toEAf D e • x.map (toEAf D) :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← RingHom.map_mul, hx i j]

theorem fr_half (hx : IsHalf e x) (i : Fin T.V.rank) (j : Fin S.V.rank) :
    fr T.β S.β (x.map (toEAf D)) i j = toEAf D e * fr T.β S.β (x.map (toEAf D)) i j := by
  have h1 : fr T.β S.β (x.map (toEAf D)) i j = fr T.β S.β (toEAf D e • x.map (toEAf D)) i j := by
    rw [← half_map hx]
  rw [fr_smul, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

variable {S T : GlobalTheory.Grid.Node D}

theorem frMapO_eq_fr (x : WO S.V T.V) : frMapO S.V T.V S.β T.β x = fr T.β S.β (x.map (toEAf D)) := by
  unfold frMapO fr
  rfl

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

theorem alg_one {R : Type} [CommRing R] {s t A A' X Y E eS : R} (hs : s = E * (X - Y)) (ht : t = Y - A') (ha : A = A')
    (he : eS = E) (hx : X = E * X) : s + eS * t - (1 - eS) * A + A = X := by
  subst hs ht ha he
  linear_combination -hx

theorem alg_two {R : Type} [CommRing R] {s t A X eS : R} (h : s + eS * t - (1 - eS) * A + A = X) :
    X - A = s + eS * t - (1 - eS) * A := by
  rw [← h]; ring

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) := by
  rw [mul_sub, hx]; rfl

theorem fr_half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : fr T.β S.β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr T.β S.β (x.map (toEAf D)) i j - fr T.β S.β (y.map (eToEAf D)) i j) := by
  have h : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, half_sub hx, RingHom.map_mul, RingHom.map_sub]; rfl
  rw [h, fr_smul, fr_sub]; rfl

theorem sub_mem_hatMx {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ)
    (he : IsIdemSum e P) (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x)
    (h : ∀ i j, ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I) :
    x - e • (x₀.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ) := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  refine (mem_hatMx_iff hS hT _ _).2 ⟨fun i j => by rw [half_sub hx, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩
  obtain ⟨hX, h'⟩ := h i j
  refine ⟨⟨toEAf D e, idem_mem_OA he⟩ * (⟨_, hX⟩ - a i j), Ideal.mul_mem_left _ _ h', ?_⟩
  refine Eq.trans ?_ (fr_half_sub hx x₀.1 i j).symm
  exact congrArg (toEAf D e * ·) (congrArg₂ (· - ·) rfl (ha i j))

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}


set_option maxHeartbeats 1000000 in
theorem frMapO_sub_mem {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ) (eS : OA D)
    (heS : eS.1 = toEAf D e) (he1 : 1 - eS ∈ idS D.host.F I)
    (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x) (y : homLat S.Λ T.Λ)
    (hyx : y.1 - x₀.1 ∈ I • homLat S.Λ T.Λ)
    (hz : x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ))
    (i : Fin T.V.rank) (j : Fin S.V.rank) : ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I := by
  obtain ⟨s, hs, hs'⟩ := ((mem_hatMx_iff hS hT _ _).1 hz).2 i j
  obtain ⟨t, ht, ht'⟩ := fr_mem_idS hS hT hyx i j
  have hs'' := hs'.trans (fr_half_sub hx y.1 i j)
  have hyA : t.1 = fr T.β S.β (y.1.map (eToEAf D)) i j - fr T.β S.β (x₀.1.map (eToEAf D)) i j := by
    rw [ht', Matrix.map_sub _ (RingHom.map_sub _), fr_sub, Matrix.sub_apply]
  have hz0 : s.1 + eS.1 * t.1 - (1 - eS.1) * (a i j).1 + (a i j).1 = fr T.β S.β (x.map (toEAf D)) i j :=
    alg_one hs'' hyA (ha i j) heS (fr_half hx i j)
  have hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have hz1 : ((s + eS * t - (1 - eS) * a i j + a i j : OA D) : EAf D) = fr T.β S.β (x.map (toEAf D)) i j := by
      simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
      exact hz0
    rw [frMapO_eq_fr, ← hz1]
    exact (s + eS * t - (1 - eS) * a i j + a i j).2
  refine ⟨hX, ?_⟩
  have : (⟨_, hX⟩ : OA D) - a i j = s + eS * t - (1 - eS) * a i j := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
    rw [frMapO_eq_fr]
    exact alg_two hz0
  rw [this]
  exact sub_mem (add_mem hs (Ideal.mul_mem_left _ _ ht)) (Ideal.mul_mem_right _ _ he1)

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D}


set_option maxHeartbeats 1000000 in
theorem cosetInd_eq_of {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ)
    (hT : IsFrame T.β T.Λ) (he : IsIdemSum e P) (he1 : (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F I)
    (κ : Cos S.Λ T.Λ I) (x₀ : homLat S.Λ T.Λ) (hx₀ : Cos.mk I x₀ = κ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (c : Coset S T I)
    (hc : ∀ i j, cmpS D.host.F I (c i j) = Ideal.Quotient.mk (idS D.host.F I) (a i j)) :
    cosetInd S T e I c = cosInd e κ := by
  funext x
  have key : IsHalf e x → (InCosetOf S T I c x ↔ ∃ y : homLat S.Λ T.Λ, Cos.mk I y = κ ∧
      x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ)) := by
    intro hx
    have hq : ∀ i j (hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        Ideal.Quotient.mk (idS D.host.F I) ⟨_, hX⟩ = cmpS D.host.F I (c i j) ↔ (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I :=
      fun i j hX => by rw [hc i j, Ideal.Quotient.eq]
    constructor
    · intro h
      exact ⟨x₀, hx₀, sub_mem_hatMx hS hT he x₀ a ha hx fun i j => ⟨(h i j).1, (hq i j _).1 (h i j).2⟩⟩
    · rintro ⟨y, hy, hz⟩ i j
      obtain ⟨hX, h'⟩ := frMapO_sub_mem hS hT _ rfl he1 x₀ a ha hx y (sub_mem_of_mk_eq (hy.trans hx₀.symm)) hz i j
      exact ⟨hX, (hq i j hX).2 h'⟩
  have hiff : (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ cosSet e κ :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  by_cases h : x ∈ cosSet e κ
  · rw [if_pos (hiff.2 h), Set.indicator_of_mem h]; rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem cosInd_eq_cosetInd : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he κ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : homLat S.Λ T.Λ, Cos.mk (∏ w ∈ P, w.asIdeal ^ d w) x₀ = κ :=
    Submodule.Quotient.mk_surjective _ κ
  have hA : ∀ i j, ∃ s : OA D, s.1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j := fun i j => by
    obtain ⟨s, -, hs⟩ := fr_mem_idS hS hT (𝔪 := ⊤) (y := x₀.1) (by rw [Submodule.top_smul]; exact x₀.2) i j
    exact ⟨s, hs⟩
  choose a ha using hA
  choose c hc using fun i j => cmpS_surj (F := D.host.F) _ (prod_ne_bot P d)
    (Ideal.Quotient.mk (idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w)) (a i j))
  exact ⟨fun i j => c i j, cosetInd_eq_of hS hT he (one_sub_idem_mem he d) κ x₀ hx₀ a ha _ fun i j => hc i j⟩

end GlobalTheory.CosToCoset
end
end

