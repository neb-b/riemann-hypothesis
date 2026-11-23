module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockLiftIdentityMemUnipotentLevelCharacterOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniLevelLift

theorem main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r q : ℕ), 1 < q → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ → NG.LevelUni J χ s r ψ₀ ξ → ∀ p : GAf L n, TrivOutside {s.v} p → IsLiftAt s r q (1 : GL (Fin r) (ZMod q)) (s.loc n p) → ∃ h : p ∈ J, χ ⟨p, h⟩ = 1 := by
  intro L _ _ _ n J χ s r q hq ψ₀ ξ hψ hU p hp hL
  haveI : Fact (1 < q) := ⟨hq⟩
  set h := s.loc n p with hh
  have hone : ∀ i j : Fin r, ((((1 : GL (Fin r) (ZMod q)) : Matrix (Fin r) (Fin r) (ZMod q)) i j).val :
      s.v.adicCompletion (maximalRealSubfield L)) = if i = j then 1 else 0 := by
    intro i j
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [ZMod.val_one, Nat.cast_one]
    · rw [ZMod.val_zero, Nat.cast_zero]
  have hent : ∀ a b : Fin n, Valued.v ((h.val - 1) a b) < 1 ∧
      (¬ (a.val < r ∧ b.val < r) → h.val a b = if a = b then 1 else 0) := by
    intro a b
    have := hL a b
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dite_eq_left hab, hone] at this
      refine ⟨?_, fun h' => absurd hab h'⟩
      convert this using 3
      rw [Matrix.sub_apply, Matrix.one_apply]
      by_cases e : a = b
      · subst e; simp
      · have e' : (⟨a.val, hab.1⟩ : Fin r) ≠ ⟨b.val, hab.2⟩ := fun h2 => e (Fin.ext (by simpa using congrArg Fin.val h2))
        rw [if_neg e, if_neg e']
    · rw [dite_eq_right hab] at this
      refine ⟨?_, fun _ => this⟩
      rw [Matrix.sub_apply, this, Matrix.one_apply]
      simp
  have hK : h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) :=
    (GlobalTheory.FixedAtSplit.mem_KOne_iff' h).2 fun a b => (hent a b).1
  have hKi := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 (inv_mem hK)
  have hint : ∀ (y c : s.v.adicCompletion (maximalRealSubfield L)), Valued.v (y - c) < 1 → Valued.v c ≤ 1 →
      Valued.v y ≤ 1 := by
    intro y c h1 h2
    have := Valuation.map_add_le Valued.v (le_of_lt h1) h2
    rwa [sub_add_cancel] at this
  have hone' : ∀ a b : Fin n, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) ≤ 1 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have huni : NG.UniRT s r h := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact (hent a b).1
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact hKi a b
    · have hne : a ≠ b := fun e => by rw [e] at ha; omega
      rw [(hent a b).2 (by omega), if_neg hne, map_zero]; exact zero_lt_one
    · have hne : a ≠ b := fun e => by rw [e] at hlt; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · subst he
      have := (hent a a).1
      rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hpJ : p ∈ J := (hU.mem p hp).2 huni
  have hdet : NG.detDD s r h = 1 := by
    have hm : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1) = 1 := by
      ext a b
      rw [Matrix.of_apply, (hent a.1 b.1).2 (by have := a.2; omega), Matrix.one_apply]
      simp only [Subtype.ext_iff]
    unfold NG.detDD
    rw [hm, Matrix.det_one]
  have hchr := hU.chr p hpJ hp 1 (by rw [Units.val_one, hdet])
  have hsup : ψ₀ (NG.supDiag s r h) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := fun e => by rw [e] at hab; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  refine ⟨hpJ, Units.ext ?_⟩
  rw [hchr, hsup, map_one, one_mul, Units.val_one]

end GlobalTheory.UniLevelLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

section Op

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def opP (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (c : WO S T →₀ ℂ) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  ∑ y ∈ c.support, c y • (GlobalTheory.SplitScalar.heisL ψ S T y * om (1, h))

theorem opP_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (c : WO S T →₀ ℂ) (h : GA D T)
    (f : WO S T → ℂ) : opP ψ S T om c h f = comb ψ S T c (om (1, h) f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, GlobalTheory.SplitScalar.heisL_apply, comb,
    Finsupp.sum]

theorem opP_comm {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) {e : AE D} {c : WO S T →₀ ℂ}
    (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {B : Module.End ℂ (WO S T → ℂ)} (hB : CommAt ψ S T e B)
    (hBh : ∀ f, IsThetaFunO ψ S T f → B (om (1, h) f) = om (1, h) (B f)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    B (opP ψ S T om c h f) = opP ψ S T om c h (B f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, (hB _ (hpres _ _ hf)).2 y (hc y hy), hBh f hf]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {y : WO S T} (hy : IsHalf e y) : y.map (infPart D) = 0 :=
  Matrix.ext fun a b => by
    rw [Matrix.map_apply, ← hy a b, RingHom.map_mul, he, zero_mul]
    rfl

theorem opP_theta {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) (hψ : IsStdChar D ψ (-1)) {e : AE D}
    (he : infPart D e = 0) {c : WO S T →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opP ψ S T om c h f) := by
  rw [opP_apply, comb, Finsupp.sum]
  exact theta_sum _ _ f hf fun y hy =>
    theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_half he (hc y hy)) (hpres _ _ hf))

end Op

end GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert


set_option maxHeartbeats 800000 in
theorem placeOp_keep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv h hh c hc f hT hCl hL
  have hW := hω i t
  obtain ⟨-, -, hcA, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hε := (hfin v).2.2
  have hεe := placeIdem_eq hε
  have hinf := (hfin v).1
  have hce := hcA (.inl v)
  have hpres := hW.om_pres

  have hk : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
      R.ωP i t (κ⁻¹, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ⁻¹, 1) φ) ∧
      R.ωP i t (κ, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ, 1) φ) := by
    intro κ hs φ hφ
    have h1 := suppF_of_drop hs hε
    rw [hεe] at h1
    have h2 := (suppGroup _ (1 - idem D (.inl v))).inv_mem h1
    have hcomm : ∀ k : GA D (Vc D i), ∀ ψ', R.ωP i t (k, 1) (R.ωP i t (1, h) ψ') = R.ωP i t (1, h) (R.ωP i t (k, 1) ψ') := by
      intro k ψ'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        one_mul, mul_one, one_mul]
    exact ⟨opP_comm hpres hc h (commAt_om hW h2) (fun ψ' _ => hcomm _ ψ') hφ,
      opP_comm hpres hc h (commAt_om hW h1) (fun ψ' _ => hcomm _ ψ') hφ⟩
  have hth := opP_theta hpres hW.std hinf hc h hT.1
  rw [← opP_apply]
  refine ⟨⟨hth, fun κ hκ hs => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hth, fun c' hc' h0 => ?_⟩⟩
  · rw [(hk κ hs f hT.1).2, hT.2 κ hκ (suppIn_of_drop hs), map_smul]
  · obtain ⟨w, hw, how⟩ := hov
    have h0 := hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
    unfold avgW at h0 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h0, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : mirC R i PP a tr z g = 0
    · rw [hg, zero_mul, zero_smul, zero_smul, map_zero]
    · rw [map_smul, (hk (κ g) (hsup g hg) f hT.1).1]
  ·
    have hu : ∀ u ∈ c'.support, ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
        heisO R.ψ _ _ u (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (heisO R.ψ _ _ u φ) := by
      intro u hu φ hφ
      have hoff := hc' u hu
      have he0 : idem D (.inl v) • u = 0 := Matrix.ext fun a b => by
        rw [Matrix.smul_apply, smul_eq_mul, ← hεe]
        exact hoff.2 v hv _ hε a b
      have hact : actO (Vc D i) (Wc D i) 1 h u = u := by
        have hM : Formalism.L2.Theta.mt (Wc D i) h - 1 = idem D (.inl v) • (Formalism.L2.Theta.mt (Wc D i) h - 1) :=
          Matrix.ext fun a b => (hh a b).symm
        rw [actO, inv_one, mt_one, Matrix.mul_one]
        conv_lhs => rw [← sub_add_cancel (Formalism.L2.Theta.mt (Wc D i) h) 1]
        rw [Matrix.add_mul, Matrix.one_mul, hM, Matrix.smul_mul, ← Matrix.mul_smul, he0, Matrix.mul_zero, zero_add]
      have := opP_comm hpres hc h (commAt_heis hW.std hce hoff.1 he0)
        (fun ψ' hψ' => by rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, hW.om_heis _ _ _ _ hψ', hact]) hφ
      rwa [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply] at this
    have h1 := hL.2 c' hc' h0
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h1, map_finsuppSum]
    refine Finset.sum_congr rfl fun u hu' => ?_
    dsimp only
    rw [map_smul, hu u hu' f hT.1]

end GlobalTheory.DownLift.GenSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem universalPart_caseA :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →
      UnusedSlot80.UniversalComponentCaseA D HW F Cm :=
  fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenformStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, DownEig R i t := by
  first | exact @GlobalTheory.DownEigen.downEig | exact GlobalTheory.DownEigen.downEig | (intros; apply GlobalTheory.DownEigen.downEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SatakeLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero (h := h) = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

end GlobalTheory.LocLanglands.SatakeLaw

namespace GlobalTheory.LocLanglands.SatakeLaw

theorem sat_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ),
    HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro h1 h2 h3 h4 h5 h6 E Ω _ _ _ _ _ A w h a ha e rc H x α hα
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified h1 h2 h3 h4 h5 h6 (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.LocLanglands.SatakeLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingProdIrrSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.BCen.SuppEmbed

theorem exists_embedding_prodIrr_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ (t : ℕ) (x : Fin t → IrrGL (k := k)) (hx : ∑ a, (x a).1 = n) (φ : π.IntertwiningMap (prodIrr x hx)),
      (∀ a, (x a).IsCusp) ∧ Function.Injective φ ∧ ∀ s, HasSupport π s ↔ Finset.univ.val.map x = s := by
  intro k _ _ _ _ n V _ _ π hs hi
  obtain ⟨t, x, hx, hc, φ, hφ⟩ :=
    GlobalTheory.CompanionTheory.SubEmb.subEmbedding_of_stage GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k n V π hs hi
  have hsupp : HasSupport π (Finset.univ.val.map x) :=
    hasSupport_of_isSubquotient hi hc (.of_injective φ hφ)
  refine ⟨t, x, hx, φ, hc, hφ, fun s => ⟨fun h => ?_, fun h => h ▸ hsupp⟩⟩
  exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds hsupp h

end GlobalTheory.BCen.SuppEmbed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

theorem GlobalTheory.InertHeckeTransfer.exists_lift_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  obtain ⟨f, hfS, hf0, U0, hfixU0, hU0, heig⟩ := hα
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  have hfU : ∀ g, ∀ κ ∈ U0, f (g * κ) = f g := fun g κ hκ => congrFun (hfixU0 κ hκ) g
  refine ⟨φ, hφU, fun h => hlam ?_, GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed L n F U hD.1 v w hw U0 hU0 Dv.σw b hbK p hp φ hφU
    (fun g κ hκ => by rw [hφ', hφ', hfU g κ hκ]), fun h hh => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv L n F v w hw Dv hs
  have hbP : b ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := hbK
  let D0 : InertDatum L n v w := ⟨e, Dv.σw, Dv.ϖ, b, he1, Dv.unram, he2, hbP, hbJ⟩
  have hloc : ∀ y, D0.loc y = b⁻¹ * cLoc w (F.j y) * b := by
    intro y
    show b⁻¹ * _ * b = _
    congr 2
    refine Units.ext (Matrix.ext fun s t => ?_)
    rw [F.loc]
    exact he3 _
  have hbi := hh.1
  have hh' := _root_.GlobalTheory.SatInd.guMap_comp_mem_hecke (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) n h hh
  have heig0 : heckeFunI L n U0 D0 h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
    rw [GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv D0 U0 π.W h hbi f, heig _ hh',
      _root_.GlobalTheory.SatInvAuto.satU_guMap_self (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) Dv.ϖ _ n (n / 2)
        Dv.unram (by omega) (by omega) h hbi α]
  have htr := GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints L n F v w hw D0 U0 hU0 b hbK p hp hloc h hh π.W f hfixU0 lam φ hφ'
  have hvecU : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ ∈ U := by
    unfold GlobalTheory.LFun.heckeVec
    by_cases hfin : (Function.support fun c : (locU n w) ⧸ ((Formalism.UG.KU Dv.σw n).comap p) =>
        h (p c.out) • ((RU L n).comp (locU n w).subtype) c.out φ).Finite
    · rw [finsum_eq_sum _ hfin]
      exact U.sum_mem fun c _ => U.smul_mem _ (hD.1.stable _ _ hφU)
    · rw [finsum_of_infinite_support hfin]
      exact U.zero_mem
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem hvecU (U.smul_mem _ hφU))) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  rw [Pi.sub_apply, Pi.smul_apply, htr g, heig0, hφ', Pi.smul_apply, map_smul, smul_eq_mul, sub_self]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChangeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  first | exact @GlobalTheory.HeckeBorelChange.hkRelFr_frBor | exact GlobalTheory.HeckeBorelChange.hkRelFr_frBor | (intros; apply GlobalTheory.HeckeBorelChange.hkRelFr_frBor <;> assumption)
end

