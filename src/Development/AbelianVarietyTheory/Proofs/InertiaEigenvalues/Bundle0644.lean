module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLOfEPowSmulMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftRealPointsEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenInfEquiv

theorem representation_inv_mul_left_translate {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H) (w : W) :
    ρ (γ * h)⁻¹ (ρ γ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_right_translate_inv_mul {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (u h : H) (w : W) :
    ρ u (ρ (h * u)⁻¹ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ext_apply' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext φ h = c.ρ h⁻¹ (φ ((finHom V).rangeRestrict h)) := rfl

theorem ext_left' {V : HSp D} (c : CoefA V) (J : Subgroup (Formalism.IndefR.Bridge.Gf V)) (χ : J →* ℂˣ)
    (φ : Formalism.IndefR.Bridge.Gf V → c.W)
    (hφ : φ ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ J χ) (γ : GA D V) (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext φ (γ * h) = c.ext φ h := by
  have h1 := hφ ⟨γ, hγ⟩ ((finHom V).rangeRestrict h) 1
  simp only [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h1
  have h2 : φ ((finHom V).rangeRestrict γ * (finHom V).rangeRestrict h) = c.ρ γ (φ ((finHom V).rangeRestrict h)) := h1
  rw [ext_apply', ext_apply', map_mul (finHom V).rangeRestrict, h2]
  exact representation_inv_mul_left_translate c.ρ γ h _

theorem ext_inf' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (u : GA D V) (hu : u ∈ GinfC V)
    (h : GA D V) : c.ρ u (c.ext φ (h * u)) = c.ext φ h := by
  have e1 : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    have h1 : finHom V u = 1 := hu
    show finHom V (h * u) = finHom V h
    rw [map_mul, h1, mul_one]
  rw [ext_apply', ext_apply', e1]
  exact representation_right_translate_inv_mul c.ρ u h _

theorem om_left' {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (H : IsWeilDatumO ψ S T' χS χT om) (γ : GA D S)
    (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T') (f : WO S T' → ℂ) (hf : IsThetaFunO ψ S T' f) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have e : ((γ * h, g) : GA D S × GA D T') = (γ, (1 : GA D T')) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact H.om_aut _ hγ _ (Subgroup.one_mem _) _ (H.om_pres _ _ hf)

theorem om_right' {S T' : HSp D} (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (u h : GA D S)
    (g : GA D T') (f : WO S T' → ℂ) : thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have e : ((h * u, g) : GA D S × GA D T') = (h, g) * (u, (1 : GA D T')) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem mem_of_hmodIs {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : M.Is V ip) (x : M.H) : M.e x ∈ V := h.2.1 ▸ ⟨x, rfl⟩

end GlobalTheory.DownLift.GenInfEquiv


open GlobalTheory.DownLift.GenInfEquiv in
theorem GlobalTheory.DownLift.downInt_realEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y u hu f hf l g
  have hM : R.IsModels := hG.core.models
  have hν := hM.νV i t
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Vc D i)
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Vc D i)
  haveI : (R.νV i t).IsHaarMeasure := hν.1.1
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (Vc D i) _ hν.1.1
  have hx := mem_of_hmodIs _ _ _ (hM.HV i t) y
  have hW := (hP i t).datum
  let Ψ : GA D (Vc D i) → ℂ := fun h =>
    thetaKO (R.ωP i t) h g f * (l ∘ₗ (R.cV i).ρ u) ((R.cV i).ext ((R.HV i t).e y) h)
  have hL : ∀ γ ∈ GQ (Vc D i), ∀ h, Ψ (γ * h) = Ψ h := by
    intro γ hγ h
    exact congrArg₂ (fun a b => a * (l ∘ₗ (R.cV i).ρ u) b) (om_left' hW γ hγ h g f hf)
      (ext_left' (R.cV i) _ _ _ hx γ hγ h)
  have hR : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (u, 1) f) * l (R.extV i t y h) = Ψ (h * u) := by
    intro h
    exact congrArg₂ (fun a b => a * l b) (om_right' (R.ωP i t) u h g f).symm
      (ext_inf' (R.cV i) ((R.HV i t).e y) u hu h).symm
  have key := (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D i)) (R.νV i t) _ hν.2 Ψ hL u).2
  have e1 : downInt R i t y (R.ωP i t (u, 1) f) l g = ∫ h in R.fdV i t, Ψ (h * u) ∂(R.νV i t) := by
    unfold downInt
    exact integral_congr_ae (Filter.Eventually.of_forall hR)
  have e2 : downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g = ∫ h in R.fdV i t, Ψ h ∂(R.νV i t) := rfl
  rw [e1, e2, key]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WPre

theorem map_smul_hom {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S] {m n : Type*}
    (f : F) (c : R) (M : Matrix m n R) : (c • M).map f = f c • M.map f :=
  Matrix.ext fun i j => by simp

theorem smul_cancel {R : Type*} [CommRing R] {m n : Type*} {c : R} (hc : IsUnit c) {M M' : Matrix m n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

end GlobalTheory.BKLim.WPre

namespace GlobalTheory.BKLim


open GlobalTheory.BKLim.WPre in
theorem exists_pre_of_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  intro l _ K bk τ hτ d ρ hρ s
  classical
  obtain ⟨Y, Z, b, A, A', hYu, hZu, hWZ, hAA', hφY⟩ := GlobalTheory.T.exists_finiteHeight_breuilKisin_lattice_semistable l K bk τ hτ d ρ hρ s
  obtain ⟨htu, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  obtain ⟨hmaps, hgal, -, h0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i0, hi0⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  have hinj : Function.Injective bk.iA := GlobalTheory.BSP.SeedAsm.iA_injective bk
  obtain ⟨u, hu⟩ := htu
  set n := s.N with hn
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  set T : Matrix (Fin d) (Fin d) (WCb l) := (u⁻¹ ^ n : (WCb l)ˣ) • Y.map (inclW l) with hT
  have hYT : Y.map (inclW l) = t ^ n • T := by
    rw [hT, Units.smul_def, smul_smul, ← hu, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have htn : IsUnit (t ^ n) := by rw [← hu]; exact (Units.isUnit u).pow n

  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hφT : e ^ n • T.map (frobW l) = T * A.map bk.evW := by
    have h1 := congrArg (fun M => Matrix.map M (inclW l)) hφY
    simp only [Matrix.map_mul] at h1
    have h2 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [GlobalTheory.Prism.frobW_inclW]
    rw [h2, hYT, show (A.map bk.ev).map (inclW l) = A.map bk.evW from rfl] at h1
    apply smul_cancel htn
    calc t ^ n • e ^ n • T.map (frobW l) = (t ^ n • T).map (frobW l) := by
          rw [map_smul_hom, map_pow, hft, mul_pow, mul_comm, smul_smul]
      _ = t ^ n • (T * A.map bk.evW) := by rw [h1, Matrix.smul_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
    intro g hg
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ h0 (g : GQ l)
    obtain ⟨hGfix, hGW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR
    have hGZ : (Z.map i0).map G = Z.map i0 := by
      exact Matrix.ext fun i j => hGfix i0 hi0 _
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = (Y.map bk.iA).map G := by
      exact Matrix.ext fun i j => (hG.ext _).symm
    have hA1 : (τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map bk.iA =
        (Per.σA (g : GQ l) τ ^ n • Y).map bk.iA := by
      rw [map_smul_hom, map_smul_hom, Matrix.map_mul, hYG, ← hWZ i0 hi0, Matrix.map_mul, hGZ, map_pow, map_pow,
        show ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA = R from Matrix.ext fun i j => rfl, ← Matrix.mul_assoc,
        ← Matrix.smul_mul, hGW, Matrix.smul_mul, ← hG.ext]
    have hA2 : τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
        Per.σA (g : GQ l) τ ^ n • Y := by
      refine Matrix.ext fun i j => hinj ?_
      have := congrFun (congrFun hA1 i) j
      simpa only [Matrix.map_apply] using this
    have hA3 := congrArg (fun M => Matrix.map M (inclW l)) hA2
    simp only [map_smul_hom, Matrix.map_mul, map_pow] at hA3
    have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
      exact Matrix.ext fun i j => (inclWA l).commutes _
    have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      exact Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
    rw [hz, hg', hYT, map_smul_hom, map_pow, ht, GlobalTheory.Prism.galW_inclW] at hA3
    have hsu : IsUnit (inclW l (Per.σA (g : GQ l) τ) ^ n) := (hστ _).pow n
    apply smul_cancel (htn.mul hsu)
    have e1 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • (zW (ρ g) * T.map (galW l (g : GQ l))) =
        t ^ n • (zW (ρ g) * (inclW l (Per.σA (g : GQ l) τ) ^ n • T.map (galW l (g : GQ l)))) := by
      rw [Matrix.mul_smul, smul_smul]
    have e2 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • T = inclW l (Per.σA (g : GQ l) τ) ^ n • t ^ n • T := by
      rw [smul_smul, mul_comm]
    rw [e1, e2]
    exact hA3
  refine ⟨n + b, Pre.mk T ?_ (bk.E ^ b • A) (bk.E ^ (2 * n) • A') ?_ ?_ hfix, Y, Z, hYT, hZu, hWZ⟩
  · rw [hT]; exact hYu.smul _
  · rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  · rw [map_smul_hom, Matrix.mul_smul, ← hφT, pow_add, mul_comm, ← smul_smul, map_pow]

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem exists_pack_isOfType : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), (∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H) → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∃ Pk : Pack a ϖ η H T, Pk.D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) := by
  intro hBS hF l _ a e _ _ ϖ LL _ _ hl Pl AI hstd η H Sig U hU T hT
  obtain ⟨F⟩ := GlobalTheory.nonempty_crysBKFunctorOL_of_bhattScholze hBS l a e ϖ LL Pl AI hstd
  let B := F.obj (resF T (ϖ.field a)) hT.crys
  let I : Ident (thetaW a LL) ϖ B.P T := Ident.ofRes B.I
  have hBK : IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) :=
    B.isBK
  obtain ⟨C, hC, hTay⟩ := GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin hBS l a e ϖ LL hl (Fin B.n) B.P T I hBK
  obtain ⟨⟨jB, hcmp⟩, -⟩ := _root_.GlobalTheory.CrisComparison.main l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (Fin B.n) B.P T I
  have hhor := GlobalTheory.T.galois_fixes_crystalline_image_descentDatum l a e ϖ LL hl (Fin B.n) B.P T I jB hcmp C hC hTay
  obtain ⟨hst, hinf⟩ := GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed l a e ϖ LL (Fin B.n) B.P T I hBK
  have hK7 := GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule hBS l a e ϖ LL (Fin B.n) B.P T I hBK
  obtain ⟨⟨Δ, hΔ⟩, hLA⟩ := GlobalTheory.T.exists_galoisDescentDatum_and_stable l a e ϖ LL (Fin B.n) B.P T I hinf hK7
  obtain ⟨hEN, hjU⟩ := _root_.GlobalTheory.NgalFil.ENStable_and_jumps hF l a e ϖ LL hl (Fin B.n) B.P T I jB Pl AI hstd hcmp hhor
  have hj : B.P.jumps ⊆ (U : Set ℤ) := hjU _ hT.jumps
  have hIcc : B.P.jumps ⊆ Set.Icc (-(η : ℤ)) H := fun i hi => hU i (hj hi)
  obtain ⟨hlow, hup⟩ := (GlobalTheory.BK.PhiMod.jumps_subset_Icc_iff _ _ l e a (Fin B.n) B.P η H).1 hIcc
  have hch := _root_.GlobalTheory.CharsDesc.chars_subset_sig l a e ϖ LL hl (Fin B.n) B.P T I jB Δ Pl AI hstd hcmp hhor hΔ Sig hT.type
  let D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin B.n) η H :=
    { toPhiMod := B.P
      desc := Δ
      nabla_mem := fun m hm => hC ▸ C.mem_MM m hm
      EN_mem := hEN
      lower := hlow
      upper := hup }
  let R : GalDat (thetaW a LL) ϖ (sQ l) D T :=
    { I := I
      jB := jB
      cmp := hcmp
      desc := hΔ
      stable := hLA hst
      horiz := hhor }
  exact ⟨⟨B.n, D, R, hBK⟩, ⟨hch, hj⟩⟩

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceOff

open Formalism.HermitianLattices.Ext.L3

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isConjPl_iff (D : D7) (P Q : PlE D.host) :
    IsConjPl D.host P Q ↔ ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ conjO D.host.E x ∈ Q.asIdeal := by
  constructor
  · intro h x
    exact h x (conjO D.host.E x) (by rw [conjO_coe, star_eq_hostConj])
  · intro h x y hy
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    subst this
    exact h x

noncomputable def conjPl (D : D7) (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (conjO D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : conjO D.host.E x ∈ P.asIdeal.comap (conjO D.host.E) := by
      rw [Ideal.mem_comap, conjO_conjO]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjO_conjO (K := D.host.E) x, this, map_zero]

theorem mem_conjPl (D : D7) (P : PlE D.host) (x : 𝓞 D.host.E) :
    x ∈ (conjPl D P).asIdeal ↔ conjO D.host.E x ∈ P.asIdeal := Iff.rfl

theorem conjPl_conjPl (D : D7) (P : PlE D.host) : conjPl D (conjPl D P) = P := by
  ext x
  rw [mem_conjPl, mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl (D : D7) (P : PlE D.host) : IsConjPl D.host P (conjPl D P) := by
  rw [isConjPl_iff]
  intro x
  rw [mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl' (D : D7) (P : PlE D.host) : IsConjPl D.host (conjPl D P) P := by
  rw [isConjPl_iff]
  intro x
  rfl

theorem conjIdeal_eq (D : D7) (P : PlE D.host) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl D P).asIdeal :=
  conjIdeal_eq_comap _

theorem isSplitPl_iff (D : D7) (P : PlE D.host) :
    IsSplitPl D.host P ↔ ∃ x : 𝓞 D.host.E, x ∈ P.asIdeal ∧ conjO D.host.E x ∉ P.asIdeal := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h _ (by rw [conjO_coe, star_eq_hostConj])⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    rw [this]; exact h

theorem conjPl_ne_of_split (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    (conjPl D P).asIdeal ≠ P.asIdeal := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  intro he
  apply hcx
  rw [← mem_conjPl, he]
  exact hx

theorem isSplitPl_conjPl (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    IsSplitPl D.host (conjPl D P) := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  rw [isSplitPl_iff]
  refine ⟨conjO D.host.E x, ?_, ?_⟩
  · rw [mem_conjPl, conjO_conjO]; exact hx
  · rw [mem_conjPl, conjO_conjO]; exact hcx

theorem exists_conj_off (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E))
    (P : PlE D.host)
    (hS0 : ∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0)
    (h2 : placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)))
    (hb : ∀ Q ∈ Sb, Q ∈ S0) (hP : IsSplitPl D.host P) (hPS : P ∉ S0) :
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  have hP'S : conjPl D P ∉ S0 := fun h => hPS (hS0 _ _ h (isConjPl_conjPl' D P))
  have hne := conjPl_ne_of_split D hP
  refine ⟨conjPl D P, isConjPl_conjPl D P, isSplitPl_conjPl D hP, hP'S, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [conjIdeal_eq]; exact hne, fun h => hPS (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq] at he
    have : Q = conjPl D P := HeightOneSpectrum.ext he
    exact hP'S (this ▸ hb Q (by exact_mod_cast hQ))
  · refine ⟨by rw [conjIdeal_eq, conjPl_conjPl]; exact hne.symm,
      fun h => hP'S (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq, conjPl_conjPl] at he
    have : Q = P := HeightOneSpectrum.ext he
    exact hPS (this ▸ hb Q (by exact_mod_cast hQ))
  · exact fun h => hPS (h2 h)
  · exact fun h => hP'S (h2 h)

end GlobalTheory.ConjPlaceOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicFrameLagrangianFirstSummand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem conjTranspose_gram_mul_apply {D : D7} {n s t : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E)
    (A : Matrix (Fin n) (Fin s) D.host.E) (B : Matrix (Fin n) (Fin t) D.host.E) (a : Fin s) (c : Fin t) :
    (Aᴴ * G * B) a c = star (fun k => A k a) ⬝ᵥ G.mulVec (fun k => B k c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem exists_isoFrame_comap_inl : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
    ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  intro D W Y hY
  set I₁ := Y.1.comap (LinearMap.inl D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)) with hI₁
  have hpos : 0 < Module.finrank D.host.E I₁ :=
    Nat.pos_of_ne_zero fun h => hY (Submodule.finrank_eq_zero.mp h)
  let b := Module.finBasisOfFinrankEq D.host.E I₁ rfl
  have hsp : Submodule.span D.host.E (Set.range (I₁.subtype ∘ b)) = I₁ := by
    have h := congrArg (Submodule.map I₁.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  let I : Matrix (Fin W.rank) (Fin (Module.finrank D.host.E I₁)) D.host.E :=
    Matrix.of fun a j => (b j : Fin W.rank → D.host.E) a
  have hT : I.transpose = I₁.subtype ∘ b := by
    funext j a
    rfl
  refine ⟨_, I, ⟨hpos, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact b.linearIndependent.map' I₁.subtype (Submodule.ker_subtype I₁)
  · rw [GlobalTheory.MixModel.cT_sig]
    refine Matrix.ext fun a c => ?_
    rw [conjTranspose_gram_mul_apply, Matrix.zero_apply]
    have ha : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b a : Fin W.rank → D.host.E) ∈ Y.1 := (b a).2
    have hc : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b c : Fin W.rank → D.host.E) ∈ Y.1 := (b c).2
    have h := Y.2.2 _ ha _ hc
    simp only [LinearMap.inl_apply, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h
    exact h
  · rw [hT]
    exact hsp

end GlobalTheory.RawLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | exact GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | (intros; apply GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le <;> assumption)
end

