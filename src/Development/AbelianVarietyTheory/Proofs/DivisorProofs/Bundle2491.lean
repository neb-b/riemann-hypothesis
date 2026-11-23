module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleIsoOfWeilPairingEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.biIso_of_weil : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  intro A _ _ g hA hs P P' hP hP1 hP2 hPs hP' hP'1 hP'2 hP's e La _ Q EF he hQ hker hW hW'
  obtain ⟨Λ, hd, hf, hk⟩ := _root_.GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hs (𝟙 _) e he
  obtain ⟨L₀, u₀, hu₀⟩ := _root_.GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨M, hM, hPM⟩ := _root_.GlobalTheory.BiRoot.exists_lbIso_lam_of_birigid_symm A g hA hs P hP hP1 hP2 hPs
  obtain ⟨M', hM', hPM'⟩ := _root_.GlobalTheory.BiRoot.exists_lbIso_lam_of_birigid_symm A g hA hs P' hP' hP'1 hP'2 hP's
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  obtain ⟨u', Hm', χ', hue', hF'⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M' hM'
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _

  have key : ∀ (M : LB A.left) (P : LB (G2 A).left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), M.IsLB → P.IsLB → u.ex = e → GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      LBIso P (cubeLB A ![fst A A, snd A A] M) →
      (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
      ∀ a b : La, ((Q a) ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star (Q b))).im = (EF a b : ℝ) := by
    intro M P u Hm χ hM hP hue hF hPM hW a b
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    obtain ⟨ud, χd, hude, hFd⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
    have mem : ∀ x : La, Q x ∈ ud.Λ := fun x => (ud.ker _).1 (by rw [hude, hue]; exact (hker _).2 ⟨x, rfl⟩)
    refine _root_.GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq _ _ fun k hk => ?_
    have h1 := hW k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h2 := _root_.GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA _ (pull_isLB hLM _) g ud _ χd hFd k (Q a) (Q b)
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk (mem a) (mem b) rfl
    rw [hude, hue] at h2
    have hiso : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left)
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).pull (𝟙 A : A ⟶ A).left) := by
      refine LBIso.trans (pull_isLB hP _) (pull_isLB hLM _) (pull_isLB (pull_isLB hLM _) _)
        (GlobalTheory.RigidBundleGlue.LBIso.pull hPM _) ?_
      exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id (pull_isLB hLM _)
    have h3 := GlobalTheory.PeriodObject.weilIs_of_lbIso GlobalTheory.globalFns_holds hA (pull_isLB hP _)
      (pull_isLB hLM _) hiso h2
    have := GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) A _ (pull_isLB hP _) ℂ (𝟙 _) k _ _ _ _ h1 h3
    have := congrArg Units.val this
    simpa using this.symm
  have hH : Hm = Hm' := by
    have e2 := _root_.GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span g ((2 : ℂ) • Hm) ((2 : ℂ) • Hm') (Set.range Q) ?_ ?_
    · have := congrArg (fun X => (1 / 2 : ℂ) • X) e2
      simpa [smul_smul] using this
    · have hR : Set.range Q = (Λ : Set (Fin g → ℂ)) := by
        ext z
        rw [SetLike.mem_coe, ← hk, hker]
        rfl
      rw [hR]; exact hf
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [key M P u Hm χ hM hP (hue.trans hu₀) hF hPM hW a b,
        key M' P' u' Hm' χ' hM' hP' (hue'.trans hu₀) hF' hPM' hW' a b]
  subst hH
  have hlam := _root_.GlobalTheory.TorusRM.lbIso_lam_of_same_form g A hA hp M M' u u' Hm χ χ' hM hM' (hue'.trans hue.symm) hF hF'
  exact LBIso.trans hP hL hP' hPM (LBIso.trans hL hL' hP' hlam (LBIso.symm hPM'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BiKill

open GlobalTheory.CechPic

theorem lam_lam_diag {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (a b : T ⟶ A) :
    lam (lam (cls M hM) (𝟙 A) (𝟙 A)) a b = 2 • lam (cls M hM) a b := by
  have e : ∀ h : T ⟶ A, pull h.left (lam (cls M hM) (𝟙 A) (𝟙 A)) = lam (cls M hM) h h := fun h =>
    by rw [pull_lam, Category.comp_id]
  have hr : ∀ x y z : T ⟶ A, lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [lam_comm, lam_mul_left hM hΘ, lam_comm _ y, lam_comm _ z]
  change pull (a * b).left _ - pull a.left _ - pull b.left _ + pull (1 : T ⟶ A).left _ = _
  rw [e, e, e, e, lam_mul_left hM hΘ, hr, hr, lam_one_left, lam_comm _ b a, two_smul]
  abel

theorem kernel_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  intro A _ _ g hA hg P hP h1 h2 hsw hamp n hn T x hx
  obtain ⟨M, hM, hPM⟩ := _root_.GlobalTheory.BiRoot.exists_lbIso_lam_of_birigid_symm A g hA hg P hP h1 h2 hsw
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ A hA M hM
  have hcube : (cubeLB A ![fst A A, snd A A] M).IsLB := LB.isLB_linComb hM _ _
  have hcP : cls P hP = lam (cls M hM) (fst A A) (snd A A) :=
    ((cls_eq_iff hP hcube).2 hPM).trans (cls_cube_two hM _ _ hcube)
  have hpullP : ∀ {Y : Over (Sp ℂ)} (a b : Y ⟶ A) (h : (P.pull (lift a b).left).IsLB),
      cls _ h = lam (cls M hM) a b := by
    intro Y a b h
    rw [cls_pull hP, hcP, pull_lam, lift_fst, lift_snd]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hcL : cls _ hL = lam (cls M hM) (𝟙 A) (𝟙 A) := hpullP _ _ hL
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨u, Hm, χ, -, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  obtain ⟨Q, ψ, ρ, N, hN, hψ, hρ, e₁, e₂, e₃⟩ :=
    GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL hAH
  have hlamM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hlamL : (abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).IsLB := LB.isLB_linComb hL _ _
  have hker : ∀ {Y : Over (Sp ℂ)} (y : Y ⟶ A),
      (∃ t : (P.pull (lift (snd A Y ≫ y) (fst A Y)).left).Gen, t.IsGen) →
      GlobalTheory.RealMult.HasGen ((abelian₂ A M).pull (lift (fst A Y) (snd A Y ≫ y)).left) ∧
      GlobalTheory.RealMult.HasGen ((abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).pull (lift (fst A Y) (snd A Y ≫ y)).left) := by
    intro Y y ht
    have h0 : lam (cls M hM) (fst A Y) (snd A Y ≫ y) = 0 := by
      rw [lam_comm, ← hpullP _ _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).2 ht
    refine ⟨(cls_eq_zero_iff (pull_isLB hlamM _)).1 ?_, (cls_eq_zero_iff (pull_isLB hlamL _)).1 ?_⟩
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hM]
      exact h0
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hL, hcL, lam_lam_diag hM hΘ, h0, smul_zero]
  have hk : x ^ (N * N) = 1 :=
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL Q ψ ρ N hψ hρ e₁ e₂ e₃ T x (hker x hx).2
  have key := GlobalTheory.torsion_point_comp_eq_one A hA M ((𝟙 A) ^ n) (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_)
    T x hk (hker x hx).1
  · rwa [MonObj.comp_pow, Category.comp_id] at key
  · rw [MonObj.comp_pow, Category.comp_id]
    refine hn y ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    rw [hpullP, lam_comm, ← GlobalTheory.RealMult.Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamM _)]
    exact (cls_eq_zero_iff _).2 hy

end GlobalTheory.BiKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTransport

theorem cech_of_logKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hks K _ _ P hU hb y' hU' hy' hev A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hred := _root_.GlobalTheory.EpsRedFr.epsRed_tangent_frX E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  obtain ⟨ι, ι', h1, h2, h3, h4, h5, h6⟩ :=
    _root_.GlobalTheory.FramedTransport.exists_model_pullback E H Dw l Xo c TF U n e v K P hU hb y' hy' hred A A' π π' i ub hi hπ hπ' hiπ hub
  have hint : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ LogKS.interior TF.Y := by
    intro x _
    exact ⟨(frX P).base x, rfl⟩
  exact _root_.GlobalTheory.CechKS.isCechKS_of_isKS E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U n v D.1 Θ hv.1 hks K (frX P ≫ TF.Y.j) hU hint
    (y' ≫ TF.Y.j) hU' hev A A' ι ι' i _ hi h1 h2 h3
    (fun a => by simpa using h4 (e.symm a).1 (e.symm a).2) _ h6 h5

end GlobalTheory.CechTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultipleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralShortSeriesTranslate_frameConstant_multiple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  first | exact @GlobalTheory.HeartFrame.central_short_series_frame | exact GlobalTheory.HeartFrame.central_short_series_frame | (intros; apply GlobalTheory.HeartFrame.central_short_series_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.MatChar

theorem charMap_matrix : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq c hc a f m hf hm hfq u χ
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  obtain ⟨-, hone, hmul⟩ := GlobalTheory.Poinc.Eq8.torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U
  have huniq : ∀ (β : G.left ⟶ G₀.left) (ρ ρ' : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) β ρ →
      TorMatch U₀ U (RingHom.id V₁) β ρ' → ρ = ρ' := fun β ρ ρ' =>
    GlobalTheory.Poinc.Eq8.torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) β Function.injective_id ρ ρ'
  have hinv : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p⁻¹).left (-ρ) := by
    intro p _ ρ hp
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U p⁻¹ inferInstance
    have h1 := hmul p p⁻¹ ρ ρ' hp hρ'
    rw [mul_inv_cancel] at h1
    have h2 : ρ + ρ' = 0 := huniq _ _ _ h1 hone
    have h3 : ρ' = -ρ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    rwa [← h3]
  have hnpow : ∀ (p : G ⟶ G₀) (ρ : D₀.toPre.X →+ D.toPre.X) (n : ℕ), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p ^ n).left (n • ρ) := by
    intro p ρ n hp
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hone
    | succ n ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ _ ih hp
  have hzpow : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X) (k : ℤ),
      TorMatch U₀ U (RingHom.id V₁) p.left ρ → TorMatch U₀ U (RingHom.id V₁) (p ^ k).left (k • ρ) := by
    intro p _ ρ k hp
    cases k with
    | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]; exact hnpow p ρ n hp
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, negSucc_zsmul, ← smul_neg]
      exact hnpow _ _ (n + 1) (hinv p ρ hp)
  have hprod : ∀ (n : ℕ) (g : Fin n → (G ⟶ G₀)) (r : Fin n → (D₀.toPre.X →+ D.toPre.X)),
      (∀ i, TorMatch U₀ U (RingHom.id V₁) (g i).left (r i)) →
      TorMatch U₀ U (RingHom.id V₁) (List.ofFn g).prod.left (∑ i, r i) := by
    intro n
    induction n with
    | zero => intro g r _; rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]; exact hone
    | succ n ih =>
      intro g r h
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact hmul _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hright : TorMatch U₀ U (RingHom.id V₁) (f ≫ q u).left (∑ v, a u v • c v) := by
    rw [hfq u]
    exact hprod 8 _ _ fun v => haveI := hq v; hzpow (q v) (c v) (a u v) (hc v)
  have hleft := GlobalTheory.Poinc.Eq8.torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q u).left
    V₁ hB G hG D P U (RingHom.id V₁) f.left Function.injective_id (fun _ hk => hk) (c u) m (hc u)
    (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V₁ hB G hG D P U f hf m hm)
  rw [RingHom.id_comp, ← Over.comp_left] at hleft
  have e := huniq _ _ _ hleft hright
  have e' := DFunLike.congr_fun e χ
  simpa using e'

end GlobalTheory.Poinc.MatChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finsetSum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartTransitionMapsDescendOverlaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem chart_transition_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ (i j : J) (V : U.left.Opens), (∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j)) → ∃ τ : V.toScheme ⟶ U.left, ∀ (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ V.toScheme), a ≫ e i = b ≫ e j → v ≫ V.ι = a ≫ pullback.fst _ _ → v ≫ τ = b ≫ pullback.fst _ _ := by
  intro R _ _ _ _ S X π hπ hs hS U hU J e he hkey i j V hV
  have hpb0 : IsPullback (pullback.fst U.hom π ∣_ V) (pullback.fst U.hom π ⁻¹ᵁ V).ι V.ι
      (pullback.fst U.hom π) := isPullback_morphismRestrict _ _
  have hpb : IsPullback (pullback.fst U.hom π ∣_ V)
      ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ pullback.snd U.hom π) (V.ι ≫ U.hom) π :=
    hpb0.paste_vert (IsPullback.of_hasPullback U.hom π)
  have hflat : Flat (V.ι ≫ U.hom) := inferInstance
  have hrange : Set.range ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i).base ⊆ Set.range (e j).base := by
    rintro _ ⟨z, rfl⟩
    have hz : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ pullback.fst U.hom π ⁻¹ᵁ V := by
      have h0 : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ Set.range (pullback.fst U.hom π ⁻¹ᵁ V).ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at h0
    simpa using (hV _).1 hz
  let hZ := IsOpenImmersion.lift (e j) ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i) hrange
  have hZe : hZ ≫ e j = (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  let p' := pullback.fst U.hom π ∣_ V
  have heq : pullback.fst p' p' ≫ (hZ ≫ pullback.fst U.hom π) =
      pullback.snd p' p' ≫ (hZ ≫ pullback.fst U.hom π) := by
    obtain ⟨h₂, h₂e, h₂p⟩ := hkey i j (pullback p' p') (pullback.fst p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι)
      (pullback.snd p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι) (pullback.fst p' p' ≫ hZ)
      (by simp only [Category.assoc, ← morphismRestrict_ι]; rw [pullback.condition_assoc])
      (by simp only [Category.assoc, hZe])
    have : h₂ = pullback.snd p' p' ≫ hZ := by
      rw [← cancel_mono (e j), h₂e]; simp only [Category.assoc, hZe]
    subst this
    simpa only [Category.assoc] using h₂p.symm
  obtain ⟨τ, hτ, -⟩ := _root_.GlobalTheory.MorDescent.descend R S V.toScheme (pullback.fst U.hom π ⁻¹ᵁ V).toScheme U.left π
    (V.ι ≫ U.hom) p' _ hπ hs hS hflat hpb _ heq
  refine ⟨τ, fun T a b v hab hv => ?_⟩
  let a' := hpb0.lift v a hv
  have ha'1 : a' ≫ p' = v := hpb0.lift_fst _ _ _
  have ha'2 : a' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι = a := hpb0.lift_snd _ _ _
  have ha'3 : a' ≫ hZ = b := by
    rw [← cancel_mono (e j), Category.assoc, hZe, ← Category.assoc, ha'2, hab]
  rw [← ha'1, Category.assoc, hτ, ← Category.assoc, ha'3]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit (R := k) (evA k x hx f) = ∑ i, lin f i • dUnit (R := k) (x i) := by
  first | exact @GlobalTheory.Katz.counit_dUnit_evA | exact GlobalTheory.Katz.counit_dUnit_evA | (intros; apply GlobalTheory.Katz.counit_dUnit_evA <;> assumption)
end

