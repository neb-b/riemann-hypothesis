module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0752
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem smul_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B X Bi : Matrix n n R) :
    c • (B * X * Bi) = B * (c • X) * Bi := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem smul_one_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B Bi : Matrix n n R)
    (h : B * Bi = 1) : B * (c • (1 : Matrix n n R)) * Bi = c • (1 : Matrix n n R) := by
  rw [← smul_conj, Matrix.mul_one, h]

theorem suppAt_inv_of {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have h := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv hg) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.sub_apply]
  linear_combination (-1 : AE D) * h

theorem chart_idem_one {D : D7} {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v} {ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hL : LevChart e PP v φ ι) : φ (toEAf D e) = 1 := by
  have h0 : φ (toEAf D e - 1) = 0 := by
    rw [hL.2.1, mul_sub, mul_one, ← map_mul, he.1.1, sub_self]
  rwa [map_sub, map_one, sub_eq_zero] at h0


set_option maxHeartbeats 1000000 in
theorem exists_supp_rdAdj_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  intro D S T βS βT e PP v φ ι he hL γ
  have hfin : GlobalTheory.LevSplit.finSw D = toEAf D := rfl
  have h1 : φ (toEAf D e) = 1 := chart_idem_one he hL
  choose M hM using fun i j => hL.1 (γ.val i j)
  choose M' hM' using fun i j => hL.1 ((γ⁻¹).val i j)
  set A : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M with hA
  set A' : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M' with hA'
  have eA : A.map φ = γ.val := Matrix.ext hM
  have eA' : A'.map φ = (γ⁻¹).val := Matrix.ext hM'
  set c := toEAf D e with hc
  have hAA : c • (A * A') = c • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    ext i j
    have hm : (A * A').map φ = (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) := by
      rw [Matrix.map_mul, eA, eA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hz : φ ((A * A') i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) i j) = 0 := by
      rw [map_sub]
      have := congrFun (congrFun hm i) j
      rw [Matrix.map_apply] at this
      rw [this, ← Matrix.map_apply (f := φ), Matrix.map_one φ (map_zero φ) (map_one φ), sub_self]
    have := (hL.2.1 _).1 hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at this
    exact this
  have hb : (βT⁻¹).val * βT.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hb' : βT.val * (βT⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmm : GlobalTheory.LevSplit.finSw D e • ((βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val)) =
      GlobalTheory.LevSplit.finSw D e • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    rw [hfin, ← hc]
    have : (βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val) = βT.val * (A * A') * (βT⁻¹).val := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (βT⁻¹).val βT.val, hb, Matrix.one_mul]
    rw [this, smul_conj, hAA, smul_one_conj _ _ _ hb']
  obtain ⟨g₀, hs, hg₀⟩ := GlobalTheory.ParahoricLift.split_lift_fin T he.1 _ _ hmm
  rw [hfin, ← hc] at hg₀
  have hX : ((βT⁻¹).val * (Formalism.L2.Theta.mt T g₀).map (toEAf D) * βT.val).map φ = γ.val := by
    have hfe : (Formalism.L2.Theta.mt T g₀).map (toEAf D) = (finE T g₀).val := rfl
    have h2 : c • ((βT⁻¹).val * (finE T g₀).val * βT.val) = c • A := by
      rw [smul_conj, hg₀, ← smul_conj]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [hb, Matrix.mul_one, ← Matrix.mul_assoc, hb, Matrix.one_mul]
    rw [hfe, ← eA]
    refine Matrix.ext fun i j => ?_
    show φ _ = φ _
    have := congrArg φ (congrFun (congrFun h2 i) j)
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul] using this
  refine ⟨g₀⁻¹, suppAt_inv_of hs, fun x => ?_⟩
  rw [rdAdj, rdAdj, GlobalTheory.TranslateAdj.frMapAdj_actO_inv, Matrix.map_mul, hX]

end GlobalTheory.DownLift.SplitCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise
noncomputable section
namespace GlobalTheory.InertFixVal

theorem exists_mem_Ine_lift_int {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₂]
    exact h x)
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral
    (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

def primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M] [Algebra M Ω] :
    Ideal (𝓞 M) :=
  Ideal.comap (((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring fun x =>
    mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom)) (IsLocalRing.maximalIdeal A)

theorem mem_primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M]
    [Algebra M Ω] (x : 𝓞 M) : x ∈ primeUnder A M ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := by
  rw [primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem ramificationIdx_eq_one {K Ω L : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (hw : IsPlaceOver A w)
    (hI : ∀ σ ∈ Ine (F := K) A, ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) :
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let M : Type := N
  haveI : FiniteDimensional K M := inferInstance
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : IsGalois K M := IsGalois.normalClosure K L Ω
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let P : Ideal (𝓞 M) := primeUnder A M
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPv : P.under (𝓞 K) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hv x]
    congr! 2
  have hPw : P.under (𝓞 L) = w.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hw x]
    congr! 2
  haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩
  refine ⟨hwv, ?_⟩
  have hv0 := v.ne_bot
  have hw0 := w.ne_bot
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
  have := v.isMaximal
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hv0
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[L] M) w.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[K] M)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[L] M)] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal P

  have hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[K] M), ∀ x : L, τ (algebraMap L M x) = algebraMap L M x := by
    intro τ hτ x
    obtain ⟨σ, hσ, hστ⟩ := exists_mem_Ine_lift_int A M τ fun y => by
      have := (mem_primeUnder A M _).1 (hτ y)
      have e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M) := rfl
      rw [← map_sub, ← e]
      exact this
    apply (algebraMap M Ω).injective
    rw [← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]
  let f : P.toAddSubgroup.inertia (M ≃ₐ[K] M) → P.toAddSubgroup.inertia (M ≃ₐ[L] M) := fun τ =>
    ⟨{ (τ : M ≃ₐ[K] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    exact DFunLike.congr_fun (congrArg Subtype.val hab) y
  have h4 := Nat.card_le_card_of_injective f hf
  rw [h1, h2, h3] at h4
  have hpos : 0 < P.ramificationIdx (𝓞 K) := h1 ▸ Nat.card_pos
  rw [h3] at hpos
  have ha : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hb : P.ramificationIdx (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hle : w.asIdeal.ramificationIdx (𝓞 K) ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : 2 * P.ramificationIdx (𝓞 L) ≤ w.asIdeal.ramificationIdx (𝓞 K) * P.ramificationIdx (𝓞 L) :=
      Nat.mul_le_mul_right _ hc
    omega
  omega

end GlobalTheory.InertFixVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  first | exact @GlobalTheory.SplitStabFrame.finE_mem_St_of_split | exact GlobalTheory.SplitStabFrame.finE_mem_St_of_split | (intros; apply GlobalTheory.SplitStabFrame.finE_mem_St_of_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroup
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

theorem finite_not_ine_le_of_isOpen : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) →
    {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  intro Ω _ k _ _ _ _ N hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff k Ω (N : Set (G k Ω))).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional k L := hL
  refine (GlobalTheory.InertiaAlmostAll.finite_ramified k Ω L).subset ?_
  rintro w ⟨B, hB, h⟩
  exact ⟨B, hB, fun h' => h fun x hx => hLN (h' hx)⟩

end GlobalTheory.DelGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D), cA D f = f → ∀ k : GA D W, SuppF W f k → ∀ x x' : WO V W, (∀ a b, f * x a b = f * x' a b) → (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  first | exact @GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | exact GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | (intros; apply GlobalTheory.LocDisj.frMapAdj_mul_frame_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftOther

theorem proj_eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    s.proj z = (Algebra.TensorProduct.lift s.i (AlgHom.id (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)))
      (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.SplitLift.proj_tmul, GlobalTheory.InertUmax.compAt_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem loc_eq_one_of_compAt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x : GAf L n) (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1) : s.loc n x = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  have e := congrFun (congrFun h a) b
  simp only [Matrix.map_apply] at e
  change s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) a b) = (1 : Matrix (Fin n) (Fin n) _) a b
  rw [proj_eq_comp, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLiftN_map' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcs : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (r q : ℕ) (g : GL (Fin r) (ZMod q))
    (M : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hM : IsLiftAt s r q g M) :
    IsLiftN g (Matrix.GeneralLinearGroup.map c.toRingHom M) := by
  have hv := GlobalTheory.SplitConjVal.valuation_eq s c hc hcs
  intro a b
  have h := hM a b
  split_ifs at h ⊢ with hab
  · rw [GlobalTheory.BlockConj.valued_lt_one_iff_w]
    have e : (Matrix.GeneralLinearGroup.map c.toRingHom M).val a b -
        (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : s.w.adicCompletion L) =
        c (M.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val :
          s.v.adicCompletion (maximalRealSubfield L))) := by
      rw [map_sub, map_natCast]; rfl
    rw [e, hv]; exact h
  · change c (M.val a b) = 1
    rw [h, map_one]
  · change c (M.val a b) = 0
    rw [h, map_zero]

end GlobalTheory.LiftOther

namespace GlobalTheory.LiftOther

theorem gPl_finite (D : D7) : (PendOf.gPl D).Finite := by
  classical
  choose S hS using GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D
  refine (Set.finite_range fun kv => (S kv).v).subset ?_
  rintro w ⟨kv, hkv⟩
  refine ⟨kv, HeightOneSpectrum.ext ?_⟩
  rw [← (S kv).w_under, hS kv]
  exact hkv

theorem over_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : NG.OverPl s.w w) : s.v = w :=
  HeightOneSpectrum.ext (s.w_under.symm.trans h)

theorem map_inv_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : GAf L n) : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [← Matrix.map_mul]; rfl

theorem map_inv_mul_self {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : GAf L n) : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  rw [← map_inv_mul, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LiftOther
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceUnderIsPlaceOver
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.DelGlob.placeUnder_isPlaceOver {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {u : HeightOneSpectrum (𝓞 L)} (hu : IsPlaceOver A u) : IsPlaceOver A (u.under (𝓞 K)) := fun x => by
  have e : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    rfl
  rw [← e, hu]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.wachOperatorProduct_shift_mem_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW F Cm hN l _ K LL hA
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) :=
    hN.2.2.2.2.2.2.2.2.1 l K 1 LL hA.2.2
  obtain ⟨hRg, hRu, hCr⟩ :=
    _root_.GlobalTheory.ExpansionsOdd.main D HW F Cm hN l K LL hA
  have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
    fun hb V _ _ _ _ _ ρ hc =>
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc
  intro T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine GlobalTheory.wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
end

