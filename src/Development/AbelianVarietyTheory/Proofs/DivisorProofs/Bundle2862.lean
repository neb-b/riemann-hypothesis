module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio.ChrFin

open Formalism.L2.JoinChr

theorem toFinE_inc (D : D7) (a : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) = algebraMap D.host.E _ a :=
  (GlobalTheory.LFun.toFinAd_tmul 1 a).trans (by rw [map_one, one_mul])

theorem toFinE_int (D : D7) {r : Formalism.MainNotions.StandardLatticesGL3.AE D} (hr : r ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.BotFormula.toFinE D r P) ≤ 1 := by
  let S : Subring (Formalism.MainNotions.StandardLatticesGL3.AE D) := (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hS : Formalism.MainNotions.StandardLatticesGL3.OhE D ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨x', rfl⟩ := hx
      intro Q
      change GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D _) Q ∈ _
      rw [toFinE_inc, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((algebraMap D.host.E (Q.adicCompletion D.host.E)) _) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _).trans_le (Q.valuation_le_one x')
    · intro Q
      have h := (GlobalTheory.LFun.mem_int_iff (F := ℚ) (E := D.host.E) (y ⊗ₜ[ℚ] ((1 : 𝓞 D.host.E) : D.host.E))).1
        (AddSubgroup.subset_closure ⟨y, fun v => hy v, 1, rfl⟩) Q
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hS hr P)

theorem adEquiv_eq (D : D7) (z : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.Mem.Col2.SplitChar.adEquiv D z = GlobalTheory.BotFormula.toFinE D z := by
  refine GlobalTheory.PlaceIdem.adele_ext fun P => ?_
  let f1 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.Mem.Col2.SplitChar.adEquiv D).toRingHom
  let f2 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  change f1 z = f2 z
  by_contra hne
  have hd : Valued.v (f1 z - f2 z) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn, hv⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_nat_val_lt P hd
  obtain ⟨a, r, hr, hz⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx z hn
  have ha : f1 (Formalism.MainNotions.StandardLatticesGL3.inc D a) = f2 (Formalism.MainNotions.StandardLatticesGL3.inc D a) := by
    change GlobalTheory.Mem.Col2.SplitChar.adEquiv D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P = GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P
    rw [GlobalTheory.Mem.Col2.SplitChar.adEquiv_inc, toFinE_inc]
  have e1 : f1 z - f2 z = (n : P.adicCompletion D.host.E) * (f1 r - f2 r) := by
    rw [hz, map_add (f := _), map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ha]
    ring
  have h1 : Valued.v (f1 r) ≤ 1 := GlobalTheory.Mem.Col2.SplitChar.vl_le hr P
  have h2 : Valued.v (f2 r) ≤ 1 := toFinE_int D hr P
  have h3 : Valued.v (f1 r - f2 r) ≤ 1 := Valuation.map_sub_le _ h1 h2
  have h4 : Valued.v ((n : P.adicCompletion D.host.E)) = P.valuation D.host.E (n : D.host.E) := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E)) n]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  have h5 : Valued.v (f1 z - f2 z) ≤ P.valuation D.host.E (n : D.host.E) := by
    rw [e1, map_mul, h4]
    exact mul_le_of_le_one_right' h3
  exact absurd (h5.trans_lt hv) (lt_irrefl _)

theorem chrEq_of_finPart : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ)
    (ν : Formalism.L2.Host.HChar D.host.E),
    IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) →
      ChrEq χ ν := by
  intro D χ N c e ν hχ hf hν
  refine ⟨hχ, fun P ε hε k x hx => ?_⟩
  have hι : ∀ x : D.host.E, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    fun x => (GlobalTheory.LFun.toFinAd_tmul 1 x).trans (by rw [map_one, one_mul])
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) hι
    GlobalTheory.LFun.mem_int_iff hε
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, locE, GlobalTheory.HeckeTensorRead.map_loc (infPart D), h1, zero_mul, add_zero]
  have hfin : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
      Neutral.B1.finiteSingle D.host.E P (algebraMap D.host.E _ (k : D.host.E)) := by
    have h4 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) =
        algebraMap D.host.E _ (k : D.host.E) := hι _
    have h5 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (locE D ε (k : D.host.E))) =
        1 + GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D ε) *
          (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)) ε _
    rw [hx, h5]
    exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  let u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom x
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom u
  have hy1 : GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) :=
    (GlobalTheory.BotFormula.toFinE D).apply_symm_apply _
  have hxy : IsFinIdl x y := ⟨hinf, hy1.symm⟩
  have hval := hf x y hxy
  have hy : GlobalTheory.Mem.Col2.SplitChar.finIdl D y = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) := by
    refine Units.ext (Prod.ext rfl ?_)
    rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_snd, adEquiv_eq, hy1, hfin]
    rfl
  have hc : c.f y ^ (-e) = ν.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) := by
    rw [zpow_neg, hν y]
    rfl
  rw [hval, hc, hy]
  rfl

end GlobalTheory.NormRatio.ChrFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricUnitaryGauge
section
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.HermLB

theorem isometric_pull_fs_toProj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (m : ℕ) (t : Fin (m + 1) → L.B.Sec) (ht : ⨆ j, nonzeroLocus (t j) = ⊤)
    (A : (k →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U),
    (∀ (σ : k →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p σ), y ∈ ptsIn p σ (L.B.U i) →
      (L.φ σ).φ i y = Real.log (∑ a, ‖∑ j, A σ j a * valR y.1 (L.B.U i) ((t j).f i)‖ ^ 2)) →
    ((GlobalTheory.HermLB.fs (PSpace.str k m) (GlobalTheory.ProjSpace.O1_isLB k m) (GlobalTheory.ProjSpace.coord k m) (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord k m) A hA hc).pull
      (GlobalTheory.ProjSpace.toProj p t ht) (GlobalTheory.ProjSpace.toProj_str p t ht)).Isometric L := by
  intro k _ X p L m t ht A hA hc h
  refine ⟨ProjSpace.toProjIso p t ht, ProjSpace.toProjIso_isGen p t ht, fun σ a b y ha hb => ?_⟩
  let π := ProjSpace.toProj p t ht
  have hπ : π ≫ PSpace.str k m = p := ProjSpace.toProj_str p t ht
  let z := Points.PtsOver.map π hπ (spMap σ) y
  let B := (ProjSpace.O1 k m).pull π
  have hb' : y ∈ ptsIn p σ (B.U b) := hb
  have hab : y ∈ ptsIn p σ (L.B.U a ⊓ B.U b) := mem_ptsIn_inf.2 ⟨ha, hb'⟩
  have hz : z ∈ ptsIn (PSpace.str k m) σ ((ProjSpace.O1 k m).U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => z) (fun _ => rfl) hb' PUnit.unit
  let u : Γ(X, L.B.U a ⊓ B.U b)ˣ := (ProjSpace.toProjIso p t ht).s (a, b)
  let r : Fin (m + 1) → ℂ := fun j =>
    valR z.1 ((ProjSpace.O1 k m).U (b PUnit.unit)) ((ProjSpace.coord k m j).f (b PUnit.unit))
  have hu : ev p σ _ u.val y ≠ 0 := ev_ne_zero hab u.isUnit
  have e (j) : valR y.1 (L.B.U a) ((t j).f a) = ev p σ _ u.val y * r j := by
    have e₁ : resG X (inf_le_left : L.B.U a ⊓ B.U b ≤ L.B.U a) ((t j).f a) =
        u.val * resG X inf_le_right ((Cartier.secPull (ProjSpace.coord k m j) π).f b) :=
      ProjSpace.secMaps_toProjIso p t ht j (a, b)
    have e₂ := congrArg (ev p σ _ · y) e₁
    simp only [ev_mul, ev_res _ hab] at e₂
    exact e₂.trans (congrArg (_ * ·) (Points.valR_appLE y.1 π _ hb' _))
  have h0 := (Weight.noCommonZero_combVal (p := PSpace.str k m) (σ := σ)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (hA σ)).sum_pos hz
  have h0' : 0 < ∑ c, ‖∑ j, A σ j c * r j‖ ^ 2 := h0.trans_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (‖·‖ ^ 2) ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)))
  have e₃ := (Weight.pull_φ (Weight.fsBasis (PSpace.str k m) σ (ProjSpace.O1_isLB k m) (ProjSpace.coord k m)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (A σ) (hA σ)) π hπ b y).trans (Weight.fsBasis_φ _ _ _ _ _ _ _)
  refine (h σ a y ha).trans (Eq.trans ?_ (congrArg (· + Real.log (‖ev p σ _ u.val y‖ ^ 2)) e₃.symm))
  refine Eq.trans ?_ (Real.log_mul h0'.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hu)))
  rw [Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.sum_mul]
  refine congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => ?_)
  rw [e j]
  ring

end GlobalTheory.HermLB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTer
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gens

theorem res_ι_app {X : Scheme.{0}} (U : X.Opens) (V : U.toScheme.Opens) (x : Γ(X, U.ι ''ᵁ V))
    (hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    (U.toScheme.presheaf.map (homOfLE hle).op).hom ((U.ι.app (U.ι ''ᵁ V)).hom x) = x := by
  have h1 := Scheme.Hom.appIso_hom U.ι V
  rw [Scheme.Opens.ι_appIso] at h1
  have h3 := congrArg (fun f => f.hom x) h1
  simp only [Iso.refl_hom, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact (congrArg (fun f => (U.toScheme.presheaf.map f).hom ((U.ι.app (U.ι ''ᵁ V)).hom x))
    (Subsingleton.elim (homOfLE hle).op _)).trans h3.symm

theorem gs_ι {X : Scheme.{0}} (U : X.Opens) (j : X ⟶ U.toScheme) (hj : j ≫ U.ι = 𝟙 X) (V : U.toScheme.Opens)
    (x : Γ(X, U.ι ''ᵁ V)) (y : X) (hy : j y ∈ V) : gs j y V x = gs (𝟙 X) y (U.ι ''ᵁ V) x := by
  have hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq U.ι V).ge
  have e := gs_res j y hle hy ((U.ι.app (U.ι ''ᵁ V)).hom x)
  rw [res_ι_app] at e
  rw [e, gs_pull j U.ι y _ (hle hy), hj]

theorem gens : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R), ∃ N : ℕ, 1 ≤ N ∧ ∃ (Ix : Type) (U : Ix → Q.P.A.left.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(Q.P.A.left, U i)), (⨆ i, U i = ⊤) ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) ∧ ∀ i j, ∃ σ σ' : Q.SecB N 0, ∀ z ∈ U i, ∀ J, Good Q.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z (U i) (r i j) * sval σ' (𝟙 _) z J := by
  intro R _ _ Q
  obtain ⟨N, hN, M, s, hcov, hs⟩ := Q.P.ample ⊤ (isAffineOpen_top _)
  choose haff r hr hsurj using hs
  let ιU := (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).ι
  let j : Q.P.A.left ⟶ (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).toScheme := Q.P.A.left.topIso.inv
  have hj : j ≫ ιU = 𝟙 _ := by
    show Q.P.A.left.topIso.inv ≫ (⊤ : Q.P.A.left.Opens).ι = _
    rw [← Scheme.topIso_hom, Iso.inv_hom_id]
  have hιj : ιU ≫ j = 𝟙 _ := by
    show (⊤ : Q.P.A.left.Opens).ι ≫ Q.P.A.left.topIso.inv = _
    rw [← Scheme.topIso_hom, Iso.hom_inv_id]; rfl
  have hjι : ∀ w, j (ιU w) = w := fun w => by show (ιU ≫ j).base w = w; rw [hιj]; rfl
  have hfe : FormEq (K := Fin N) (fun _ => 𝟙 Q.P.A.left) (fun _ => (1 : ℤ)) (Q.famφB 0) (DegPre.famε N) := by
    intro U _ h
    refine Eq.trans ?_ (GlobalTheory.Mum.OriginSec.formEq_zero Q N U h)
    simp [Finset.prod_const, Fin.prod_univ_one]
  have hσ : ∀ a, ∃ σ : Q.SecB N 0, ∀ (z : Q.P.A.left) J, Good Q.P.L z J → sval σ (𝟙 _) z J = sval (s a) j z J := by
    intro a
    obtain ⟨s', hs'⟩ := GlobalTheory.UU.exists_pullSec_sval
      (s a : LB.Sec (LB.LinComb Q.P.L (K := Fin N) (fun _ => ιU) (fun _ => (1 : ℤ)))) j
      (fun _ : Fin N => 𝟙 Q.P.A.left) (fun _ => hj)
    obtain ⟨σ, hσ⟩ := exists_sec Q.P.isLB hfe s'
    exact ⟨σ, fun z J hJ => (hσ _ _ z J hJ).trans ((hs' _ _ z J hJ).trans (by rw [Category.id_comp]))⟩
  choose σ hσv using hσ
  refine ⟨N, hN, Fin (M + 1), fun a => ιU ''ᵁ nonzeroLocus (s a), fun _ => Fin (M + 1), fun a b => r a b, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show j y ∈ ⨆ a, nonzeroLocus (s a) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ⟨j y, ha, show (j ≫ ιU).base y = y by rw [hj]; rfl⟩⟩
  · exact fun a => (haff a).image_of_isOpenImmersion ιU
  · intro a
    have key : ∀ (U U' : (Spec (CommRingCat.of R)).Opens) (_ : U = U') (W : Q.P.A.left.Opens) e e'
        (rr : Fin (M + 1) → Γ(Q.P.A.left, W)),
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U' W e').hom rr) →
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U W e).hom rr) := by
      rintro _ _ rfl _ _ _ _ h; exact h
    have e2 := morphismRestrict_appLE Q.P.A.hom ⊤ ⊤ (nonzeroLocus (s a)) le_top
    have h' := (congrArg (fun g => Function.Surjective (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom g) (r a))) e2).mp (hsurj a)
    exact key ⊤ ((⊤ : (Spec (CommRingCat.of R)).Opens).ι ''ᵁ ⊤) (Scheme.Opens.ι_image_top _).symm
      (ιU ''ᵁ nonzeroLocus (s a)) _ _ (r a) h'
  · intro a b
    refine ⟨σ b, σ a, fun z hz J hJ => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hσv _ _ _ hJ, hσv _ _ _ hJ]
    have hm := hJ.mem (fun _ : Fin N => ιU) j
    have hw' : j (ιU w) ∈ nonzeroLocus (s a) := by rw [hjι]; exact hw
    refine ⟨(GlobalTheory.Mum.OriginSec.isUnit_sval_iff' (s a) j (ιU w) hJ).2 hw', ?_⟩
    have hm' : j (ιU w) ∈ nonzeroLocus (s a) ⊓ (powOver Q.P.A Q.P.L ⊤ N).U (fun _ => J (j ≫ ιU)) := ⟨hw', hm⟩
    have e := congrArg (gs j (ιU w) _) (hr a b (fun _ => J (j ≫ ιU)))
    rw [gs_res _ _ _ hm', gs_mul _ _ _ hm', gs_res _ _ _ hm', gs_res _ _ _ hm'] at e
    rw [gs_ι _ j hj _ (r a b) _ hw'] at e
    exact e
end GlobalTheory.Heat.Gens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem IsInv.apply_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by

  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)) = 0 := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ O := hgU.trans (g.preimage_mono hle)

    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ O (constFn G.hom O r) hφ hgO htr

    have hw : (g' * v').left ≫ G.hom =
        spMap ((algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ) := by
      refine (Over.w (g' * v')).trans ?_
      show spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom = _
      rw [hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
      by_cases hO : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
      · rw [GlobalTheory.ArcPts.SecValue.valR_constFn G.hom _ _ hw O hO r]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [valR, dite_eq_right hO]
        rfl
    rw [h0, ← GlobalTheory.HolHom.valR_res g hle _ hgU] at hval
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)))]
    exact hval.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ O} => k.1) O
    (fun k => homOfLE k.2.2) ?_ _ 0 fun k => ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩
  · exact (key k.1 k.2.1 k.2.2).trans (map_zero _).symm

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CosetOrth

section General

variable {E : Type} [Field E] [NumberField E]

def InHat (I : FractionalIdeal (𝓞 E)⁰ E) (x : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (x w) ≤ WithZero.exp (-(FractionalIdeal.count E w I))

theorem inHat_one_iff (x : FiniteAdeleRing (𝓞 E) E) : InHat 1 x ↔ ∀ w, Valued.v (x w) ≤ 1 := by
  simp only [InHat, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]

theorem inHat_zero (I : FractionalIdeal (𝓞 E)⁰ E) : InHat I 0 := fun w => by
  have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
  rw [this, map_zero]; exact zero_le

theorem InHat.mul_left {I : FractionalIdeal (𝓞 E)⁰ E} {t x : FiniteAdeleRing (𝓞 E) E} (ht : InHat 1 t) (hx : InHat I x) :
    InHat I (t * x) := fun w => by
  have : (t * x) w = t w * x w := rfl
  rw [this, map_mul]
  exact (mul_le_of_le_one_left' ((inHat_one_iff t).1 ht w)).trans (hx w)

theorem InHat.add {I : FractionalIdeal (𝓞 E)⁰ E} {x y : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) (hy : InHat I y) :
    InHat I (x + y) := fun w => by
  have : (x + y) w = x w + y w := rfl
  rw [this]
  exact (Valued.v.map_add _ _).trans (max_le (hx w) (hy w))

theorem InHat.neg {I : FractionalIdeal (𝓞 E)⁰ E} {x : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) : InHat I (-x) := fun w => by
  have : (-x) w = -x w := rfl
  rw [this, Valuation.map_neg]
  exact hx w

end General

variable {D : D7}

abbrev FA (D : D7) : Type := FiniteAdeleRing (𝓞 D.host.E) D.host.E

def fe (D : D7) : AE D →+* FA D := (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)

theorem fe_apply (x : AE D) : fe D x = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D x) := rfl

def skewId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def HatPt {S T : HSp D} (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (u : WO S T) : Prop :=
  u.map (infPart D) = 0 ∧ ∀ i j, InHat I (algebraMap D.host.E (FA D) r * fe D (u i j))

def finMat {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Matrix (Fin n) (Fin n) (FA D) :=
  ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (GlobalTheory.BotFormula.toFinE D)

theorem exists_fe (s : FA D) : ∃ σ : AE D, infPart D σ = 0 ∧ fe D σ = s := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s), ?_, ?_⟩
  · exact (he _).1.symm.trans (by rw [e.apply_symm_apply])
  · have : finPart D (e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)) =
        (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := (he _).2.symm.trans (by rw [e.apply_symm_apply])
    rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem ip_eq_zero_of_heis_eigen {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) (v : WO A B) {α β : ℂ}
    (e₁ : heisO ψ A B v f₁ = α • f₁) (e₂ : heisO ψ A B v f₂ = β • f₂) (hβ : ‖β‖ = 1) (hne : α ≠ β) :
    ip A B ν 𝓕 f₁ f₂ = 0 := by
  have key := GlobalTheory.Size.ipO_heisO hψ hν.1 hν.2.1 h₁ h₂ v
  rw [e₁, e₂] at key
  have e : GlobalTheory.Ker.ipO ν 𝓕 (α • f₁) (β • f₂) = (α * starRingEnd ℂ β) * ip A B ν 𝓕 f₁ f₂ := by
    unfold GlobalTheory.Ker.ipO ip
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have e' : GlobalTheory.Ker.ipO ν 𝓕 f₁ f₂ = ip A B ν 𝓕 f₁ f₂ := rfl
  rw [e, e'] at key
  have hb : starRingEnd ℂ β * β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]; simp
  have hne' : α * starRingEnd ℂ β ≠ 1 := fun h => hne (by
    have := congrArg (· * β) h
    simp only [one_mul, mul_assoc, hb, mul_one] at this
    exact this)
  have : (α * starRingEnd ℂ β - 1) * ip A B ν 𝓕 f₁ f₂ = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')

end GlobalTheory.CosetOrth
end
end

