module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLocalDoublingIntegralConverges
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfThetaModelCharacter
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar
variable {D : D7}

theorem coe_chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) (x : (AE D)ˣ) :
    ((chi c θ e x : Circle) : ℂ) = (((c.f (finY D x) : ℂˣ) : ℂ) *
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ c.n τ) ^ e := by
  rw [chi, MonoidHom.zpow_apply, Circle.coe_zpow, MonoidHom.mul_apply, Circle.coe_mul, coe_finChar, coe_infChar]

theorem exists_hecke_of_heckeU : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ), (e = 1 ∨ e = -1) →
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ N ∧ HasFinPart χ c e := by
  intro D N c e he
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : Continuous (chi c θ e) := by
    have h : ((chi c θ e : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (finChar c x * infChar θ c.n x) ^ e := by
      funext x; rw [chi, MonoidHom.zpow_apply, MonoidHom.mul_apply]
    rw [h]
    exact ((_root_.GlobalTheory.HeckeUChar.continuous_finChar c).mul (continuous_infChar hθ c.n)).zpow e
  have haut : ∀ a : D.host.Eˣ, chi c θ e (Units.map (incA D).toMonoidHom a) = 1 := by
    intro a
    refine Circle.ext ?_
    rw [coe_chi, finY_incA]
    have h1 : ∀ τ, θ τ (infPart D ((Units.map (incA D).toMonoidHom a : (AE D)ˣ) : AE D)) = embT D τ (a : D.host.E) :=
      fun τ => GlobalTheory.FockCompare.comp_incA hθ τ _
    simp only [h1]
    rw [c.aut a, one_zpow, Circle.coe_one]
  refine ⟨chi c θ e, ⟨hcont, haut⟩, ?_, fun x y hxy => ?_⟩
  · refine _root_.GlobalTheory.HeckeSignEta.resEta_of_sign D _ N ⟨hcont, haut⟩ (fun x y hy => Circle.ext ?_) θ hθ fun τ x h1 h2 h3 => ?_
    · rw [coe_chi, finY_mul_conj x y hy, c.norm, Units.val_one, one_mul, Circle.coe_one]
      have h4 : ∀ τ, θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ) = 1 := by
        intro τ
        have e1 : θ τ (infPart D (y : AE D)) = (Complex.normSq (θ τ (infPart D (x : AE D))) : ℂ) := by
          rw [hy, RingHom.map_mul, map_mul, GlobalTheory.FockCompare.comp_cA hθ, Complex.mul_conj]
        have hne : θ τ (infPart D (x : AE D)) ≠ 0 := by
          intro h0
          have := congrArg (fun z => θ τ (infPart D z)) (Units.mul_inv x)
          simp only [RingHom.map_mul, map_mul, h0, zero_mul, RingHom.map_one, map_one] at this
          exact zero_ne_one this
        have hp : 0 < Complex.normSq (θ τ (infPart D (x : AE D))) := Complex.normSq_pos.2 hne
        rw [e1, Complex.norm_real, Real.norm_of_nonneg hp.le]
        exact div_self (by exact_mod_cast hp.ne')
      simp only [h4, one_zpow, Finset.prod_const_one, one_zpow]
    · have hf : finY D x = 1 := Units.ext (by
        rw [coe_finY, h1, map_one, map_one, Units.val_one])
      rw [coe_chi, hf, map_one, Units.val_one, one_mul, Finset.prod_eq_single τ (fun τ' _ hτ' => by
        rw [h3 τ' hτ']; simp) (fun h => absurd (Finset.mem_univ τ) h), h2]
      have hn : (-1 : ℂ) / (‖(-1 : ℂ)‖ : ℂ) = -1 := by simp
      rw [hn, ← zpow_mul]
      obtain ⟨k, hk⟩ := c.par τ
      have hodd : Odd e := by rcases he with rfl | rfl <;> decide
      obtain ⟨j, hj⟩ := hodd
      have : c.n τ * e = (N : ℤ) + 2 * (k * e + j * (N : ℤ) - (N : ℤ) * 0) := by
        have : c.n τ = k + k + N := by linarith
        rw [this, hj]; ring
      rw [this, zpow_add₀ (by norm_num), zpow_mul, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, mul_one,
        zpow_natCast]
  · obtain ⟨h1, h2⟩ := hxy
    have hy : finY D x = y := Units.ext (by rw [coe_finY, h2, RingEquiv.symm_apply_apply])
    rw [coe_chi, hy, h1]
    simp only [map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one, mul_one]
    rw [Units.val_zpow_eq_zpow_val]

end GlobalTheory.HeckeUChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem data_exists : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H := gbig_and GlobalTheory.BottomPairData.pair_data (gbig_and _root_.GlobalTheory.BottomWitt.wittIndex_eq_zero (gbig_and _root_.GlobalTheory.BottomIPData.isFockVec_bottom (gbig_and GlobalTheory.BottomIPData.unram_bottom (gbig_and _root_.GlobalTheory.BottomCusp.one_mem_A0_of_isBottomTri
    (gbig_and _root_.GlobalTheory.BottomIPData.isParamFun_one_bottom (gbig_and _root_.GlobalTheory.BottomIPData.dSfun_bottom_ne_zero (gbig_and GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom GlobalTheory.T.definiteBottom_localDoublingIntegral_converges)))))))
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ W i j A A' WW X hX hA t
  obtain ⟨cA, a, νW, 𝓕W, hP⟩ := h1 W i j A A' WW X hX hA t
  obtain ⟨par, hpar⟩ := h6 W i j A A' WW X hX t
  obtain ⟨κ, hκ, hL⟩ := h8 W i j A A' WW X hX t par hpar
  obtain ⟨P, hloc⟩ := h9 W i j A A' WW X hX t cA a νW 𝓕W hP
  refine ⟨betaB G i j, betaB G i j / alphaB Lc i j t, fun τ => -X.rA.s τ, X.rW.s, cA, a, νW, 𝓕W, X.rA.Λ, X.rW.Λ,
    sfB G t, par, κ, P, hP, h2 W i j A A' WW X hX t, h3 W i j A A' WW X hX t P, h4 W i j A A' WW X hX t P,
    h5 W i j A A' WW X hX t cA hP.setting, hpar, ?_, hκ, h7 W i j A A' WW X hX t, hL, hloc⟩
  intro v _ k _ g
  rfl

end GlobalTheory.BottomIPData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyDatumAb

theorem exists_keyOn : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  intro A B _ _ _ _ _ f G _ _ L σ g y hg1 hG hd hO hs hpol hy hσ hr
  let W : (Sp A).Opens := ⟨abLocus G, hO⟩
  have hWsub : (W : Set (Sp A)) ⊆ abLocus G := subset_rfl
  have hprop : IsProper (G.hom ∣_ W) := GlobalTheory.AbLocusProperNormal.isProper_restrict_of_subset_abLocus A G hG W hWsub
  have hGW : IsAbelianScheme ((Over.pullback W.ι).obj G) := GlobalTheory.SquareSemiOpen.isAb_pullback_open G hG W hprop
  haveI : IsProper ((Over.pullback W.ι).obj G).hom := hGW.proper
  obtain ⟨ha, hk⟩ := hpol W hWsub
  obtain ⟨x', hx'⟩ : ∃ x' : Sp B ⟶ W.toScheme, x' ≫ W.ι = spMap f :=
    ⟨IsOpenImmersion.lift W.ι (spMap f) (by rw [Scheme.Opens.range_ι]; exact hr), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (spMap f)
  have h₀ := isGrpPullback_pullback G W.ι
  have h₂ := h.congr hx'.symm rfl
  let φ : ((Over.pullback (spMap f)).obj G).left ⟶ G.left := pullback.fst G.hom (spMap f)
  let ψ : ((Over.pullback (spMap f)).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom W.ι = φ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback (spMap f)).obj G) ((Over.pullback W.ι).obj G) x' ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB L.isLB φ
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom W.ι)
  obtain ⟨w, hw⟩ : LBIso (L.L.pull φ) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => φ) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl hL)
  have hamp₀ : RelAmple (Over.mk ((Over.pullback (spMap f)).obj G).hom) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL₀ ha h₃.1
  have hLψ := pull_isLB hL₀ ψ
  obtain ⟨w', hw'⟩ : LBIso (L.L.pull φ) (((L.L.pull (pullback.fst G.hom W.ι)).pull ψ).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl) ⟨w, hw⟩
  have hamp : RelAmple ((Over.pullback (spMap f)).obj G) (L.L.pull φ) :=
    relAmple_pull (A' := (Over.pullback (spMap f)).obj G) (A := Over.mk ((Over.pullback (spMap f)).obj G).hom)
      (IsPullback.id_horiz _) hLψ hL ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp₀
  have hsa := IsSemiAbelian.pullback (spMap f) G hG
  have hA : IsAbelianScheme ((Over.pullback (spMap f)).obj G) :=
    { comm := hsa.comm, smooth := hsa.smooth,
      proper := MorphismProperty.of_isPullback (P := @IsProper) h₃.1 hGW.proper
      geomConnected := hsa.geomConnected }
  haveI := hsa.comm
  let P : PolAV (Sp B) :=
    { A := (Over.pullback (spMap f)).obj G
      isAb := hA
      g := g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hd
      L := L.L.pull φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull h ⟨L.rig, L.rigGen⟩
      sym := PolBaseChange.sym_pull h (CechPic.sym_of_isSymmetric L hs)
      ample := hamp
      ktriv := kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk }
  have he : eSec P.A ≫ φ = spMap f ≫ eSec G := PolBaseChange.eSec_comm h
  have hr' : (rigPullOf φ (spMap f) he L.L L.rig).IsGen :=
    Out.LBxP.isGen_pullAlong L.L φ (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec P.A)
      (fun _ => he) L.rig L.rigGen
  have hw0 := (isGen_iff _).1 (idIso_isGen hL)
  obtain ⟨th', hth'⟩ := sec_pull_down hw0 L.isLB hL σ
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange A B f G P.A φ h hG.smooth g y hy
  have := hA.smooth
  refine ⟨⟨P, hg1, _, hr', th', fun s => ?_, v', hv'⟩, rfl, φ, he, idIso _, Chart.dualMapR f, h, idIso_isGen hL,
    fun p => hr' p.1 p.2, GlobalTheory.KeyPow.appLE_eq_of_stalk _ σ th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv'φ i⟩
  · obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (σ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyDatumAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem card_eq_of_isLieBasis [Nontrivial R] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {w : Fin m → (epsR R ⟶ G)} (hv : IsLieBasis v) (hw : IsLieBasis w) : n = m := by
  choose b hb using fun i => LieEigen.exists_prodPts hw (hv.1 i)
  have key : ∀ c, prodPts c v = prodPts (∑ i, c i • b i) w := fun c => by
    rw [← LieEigen.prodPts_prodPts hw.1]
    exact congrArg (prodPts c) (funext fun i => (hb i).symm)
  let L : (Fin n → R) →ₗ[R] (Fin m → R) := Fintype.linearCombination R b
  have hL : ∀ c, L c = ∑ i, c i • b i := fun c => Fintype.linearCombination_apply R b c
  have bij : Function.Bijective L := by
    refine ⟨fun c c' h => LieEigen.prodPts_injective hv ?_, fun d => ?_⟩
    · show prodPts c v = prodPts c' v
      rw [key, key, ← hL, ← hL, h]
    · obtain ⟨c, hc⟩ := LieEigen.exists_prodPts hv (LieEigen.isTangent_prodPts hw.1 d)
      exact ⟨c, LieEigen.prodPts_injective hw (show prodPts (L c) w = prodPts d w by rw [hL, ← key, hc])⟩
  have := (LinearEquiv.ofBijective L bij).finrank_eq
  simpa using this

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem push_left (x : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) x).left = x.left ≫ pullback.fst G.hom (spMap f) := rfl

theorem push_injective : Function.Injective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) :=
  fun x y e => Over.OverMorphism.ext ((isGrpPullback_pullback G (spMap f)).1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))

theorem push_surjective : Function.Surjective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) := by
  intro w
  have hk := isGrpPullback_pullback G (spMap f)
  refine ⟨Over.homMk (hk.1.lift w.left (epsR k).hom (Over.w w)) (hk.1.lift_snd _ _ _), ?_⟩
  exact Over.OverMorphism.ext (hk.1.lift_fst _ _ _)

theorem unit_fst : η[(Over.pullback (spMap f)).obj G].left ≫ pullback.fst G.hom (spMap f) = spMap f ≫ η[G].left := by
  have e := congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback G (spMap f)) (𝟙_ (Over (Sp k)))))
  have e₁ : (1 : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap f)).obj G) = η[(Over.pullback (spMap f)).obj G] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem isTangent_iff_push (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    IsTangent y ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫
      (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y).left = (1 : Over.mk (spMap f) ⟶ G).left := by
  rw [push_left]
  show _ ↔ _ = spMap f ≫ η[G].left
  unfold IsTangent
  constructor
  · intro h
    rw [← Category.assoc, h, unit_fst]
  · intro h
    apply (isGrpPullback_pullback G (spMap f)).1.hom_ext
    · rw [Category.assoc, h, unit_fst]
    · rw [Category.assoc, Over.w y, Over.w η[(Over.pullback (spMap f)).obj G]]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
        ext s; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      simp

def scaleAt (a : k) : epsPt (spMap f) ⟶ epsPt (spMap f) :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)).left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap f) (Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)))))

theorem push_scale (a : k) (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a) ≫ y) =
      scaleAt f a ≫ pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}


open Classical in
def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) R :=
  if h : IsMonHom u then Matrix.transpose (haveI := h; (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose) else 0

theorem comp_eq_prodPts (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (j : Fin n) :
    v j ≫ u = prodPts (fun i => lieMat hv u i j) v := by
  have h := (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose_spec j
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at h
  rw [lieMat, dite_eq_left (show IsMonHom u from inferInstance)]
  exact h

end GlobalTheory.LieCoordFibre


open GlobalTheory.LieCoordFibre ReciprocityTheory.ChartRestriction.G.Chart in
theorem GlobalTheory.exists_lie_coordinates_fibres : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  intro R _ _ G _ _ hs
  have hlocal : ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ G)), IsLieBasis y := by
    haveI := hs
    obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart G
    obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
    have hu : IsUnit g := by
      by_contra h
      exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
    let L := Localization.Away g
    let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
    have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
    let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs G g
    have hpb : IsGrpPullback G' G (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst G.hom _) :=
      isGrpPullback_pullback G _
    have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
      exact Spec.map_id _
    let φ' : G.left ⟶ G'.left := pullback.lift (𝟙 _) (G.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
    have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
    have hw : φ' ≫ G'.hom = G.hom ≫ spMap f' := pullback.lift_snd _ _ _
    haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
    have hid : IsGrpPullback G G (𝟙 (Sp R)) (𝟙 G.left) := (isGrpPullback_of_iso (Iso.refl G)).congr rfl rfl
    have hn : IsGrpPullback G G (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
      hid.congr hcomp.symm hφ.symm
    have hG : IsGrpPullback G G' (spMap f') φ' := hpb.cancel hn hw
    have hs' : Smooth G'.hom := by
      show Smooth (pullback.snd G.hom _)
      infer_instance
    obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' G φ' hG hs' n v hv
    exact ⟨n, v', hv'⟩
  obtain ⟨n, v, hv⟩ := hlocal
  refine ⟨n, lieMat hv, fun g hg => ?_, fun k _ f => ?_⟩
  · obtain ⟨w, hw⟩ := KeyPow.exists_isLieBasis G hg
    exact card_eq_of_isLieBasis hv hw
  have hk := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', e⟩ := exists_isLieBasis_baseChange R k f G _ _ hk hs n v hv
  let P := pushHom hk (epsR k)
  refine ⟨fun c => P (prodPts c v'), fun c c' h => LieEigen.prodPts_injective hv' (push_injective f h),
    fun w => ?_, fun c c' => ?_, fun t c => ?_, fun u hu c => ?_⟩
  · constructor
    · intro h
      obtain ⟨y, rfl⟩ := push_surjective f w
      obtain ⟨c, rfl⟩ := LieEigen.exists_prodPts hv' ((isTangent_iff_push f y).2 h)
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact (isTangent_iff_push f _).1 (LieEigen.isTangent_prodPts hv'.1 c)
  · show P _ = P _ * P _
    rw [LieEigen.prodPts_add hv'.1, map_mul]
  · show (prodPts (t • c) v').left ≫ _ = _ ≫ (prodPts c v').left ≫ _
    rw [LieEigen.prodPts_smul, Over.comp_left, Category.assoc]
    rfl
  haveI := hu
  let col : Fin n → Fin n → R := fun j i => lieMat hv u i j
  have hz : ∀ j, P (v' j) ≫ u = P (prodPts (f ∘ col j) v') := fun j => Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left, push_left, e j, Category.assoc, ← Over.comp_left,
      comp_eq_prodPts hv u j, ← LieEigen.prodPts_left hk e])
  let Q := (IsMonHom.monoidHom u (epsPt (spMap f))).comp P
  have hQ : ∀ y, Q y = P y ≫ u := fun y => rfl
  have hs' : ∀ j, Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j) =
      P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v') := fun j => by
    rw [hQ, push_scale, push_scale, Category.assoc, hz]
  calc P (prodPts c v') ≫ u = Q (prodPts c v') := rfl
    _ = (List.ofFn fun j => Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j)).prod := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = (List.ofFn fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')).prod := by
      simp only [hs']
    _ = P (prodPts c fun j => prodPts (f ∘ col j) v') := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = P (prodPts (∑ j, c j • (f ∘ col j)) v') := by rw [LieEigen.prodPts_prodPts hv'.1]
    _ = P (prodPts (((lieMat hv u).map f).mulVec c) v') := by
      congr 2
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodChernWeil
section
namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm _root_.GlobalTheory.GoodTop.goodTopChernForm _root_.GlobalTheory.ChernDegree.chernWeilNumbers_holds _root_.GlobalTheory.FlagPushProof.flagPushForward

end GlobalTheory.GoodMetric
end

