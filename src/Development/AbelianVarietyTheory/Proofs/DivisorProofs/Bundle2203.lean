module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArithIntersectionNonnegOfSmallSectionDiff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef


open MvPolynomial in
theorem mixed_diff_nonneg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  intro hC k _ X _ p D hX A B Φ hΦ hle x y hN
  classical
  haveI := hX.isLocallyNoetherian
  obtain ⟨s, hs, hs0⟩ := (_root_.GlobalTheory.HSNef.le_iff_exists_smallSec k X p A B).1 hle
  have hg :=  (sec_ne_zero_iff s).1 hs0
  let L : Fin 2 → HermLB p := ![A, B]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (A.tens B.dual) L
  let E : Option (Fin 2) → Fin 2 → ℤ := fun o => o.elim ![1, -1] (fun i => Pi.single i 1)
  have hiso : ∀ j, (comb L (E j)).Isometric (F j) := by
    rintro (_ | i)
    · apply HermLB.icls_eq_iff.1
      simp [icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
    · exact isometric_comb_single L i
  have hΦ' := ((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso
  let n : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (comb L n)
  have hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y)) := by
    apply HermLB.icls_eq_iff.1
    simp [icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]
  have hr := isRatSec_ratOfSec s hg
  obtain ⟨-, hmix⟩ := hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr
  have hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) =
      (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D := by
    simp [aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]
    left
    ring
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly] at hmix
  rw [hmix]
  have h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z :=
    finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z))
      (hN.2 h (hNiso.isArithHeight hX hh) z)
  have h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr))
      (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0 := by
    intro σ
    have hneg : ((comb L n).φ σ).chernPart D (-1) = 0 := by
      rw [hNiso.chernPart_eq]
      exact Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)
    rw [Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
    refine MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_
    have hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s) := by
      rw [← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]
      exact hz
    rw [logNorm_ratOfSec _ hz']
    have h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z := by
      unfold Weight.nsq
      positivity
    have := Real.log_nonpos h0 (hs σ z)
    linarith
  have h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0 := by
    have := finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)
    rw [finsum_neg_distrib] at this
    unfold HermLB.archInt
    linarith
  linarith

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleTraitFibreEqUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc


open GlobalTheory.CechPic in
theorem lam_trait_fibre_eq_univ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  intro g n o _ ζ F T W _ _ fK G'' _ β κ hκ hκβ α₂ hα₂
  have hL := T.U.LG.isLB
  have hA := T.A.isLB
  have hP := F.univ.isLB
  have hLβ := pull_isLB hL (pullback.fst G''.hom (jK W) ≫ β)
  have hB₁ : (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))).IsLB :=
    LB.isLB_linComb hLβ _ _
  refine (cls_eq_iff hB₁ (pull_isLB hP α₂)).1 ?_
  have c₂ : cls _ hB₁ = lam (CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL))
      (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))
      (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')) := by
    rw [← cls_pull hL _ hLβ]; exact cls_cube_two hLβ _ _ hB₁
  have hext : CechPic.pull T.U.gen.hom.left (cls _ hA) =
      CechPic.pull (pullback.fst T.G.hom (jK T.V)) (cls _ hL) := by
    have := (cls_eq_iff (pull_isLB hA T.U.gen.hom.left) (pull_isLB hL (pullback.fst T.G.hom (jK T.V)))).2 T.U.ext
    rwa [cls_pull hA, cls_pull hL] at this
  have hΛ : lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A) = CechPic.pull T.α₂ (cls _ hP) := by
    have hl : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb hA _ _
    have := (cls_eq_iff hl (pull_isLB hP T.α₂)).2 T.lb
    rw [cls_pull hP] at this
    exact (cls_cube_two hA _ _ hl).symm.trans this
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e₁ : CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL) = CechPic.pull κ (cls _ hA) := by
    rw [← hκβ, pull_comp, pull_comp, ← hext, ← pull_comp T.U.gen.inv.left, hgi, pull_id]
  rw [c₂, e₁, lam_pull_of_isGrpPullback hκ, cls_pull hP]
  set Q := lift (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
    (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) with hQdef
  have e₃ : lam (cls _ hA) (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
      (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) =
      CechPic.pull Q.left (lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A)) := by
    rw [pull_lam, lift_fst, lift_snd]
  have hQ : Q.left ≫ T.α₂ = α₂ := by
    refine GlobalTheory.UnifLamFibre.isSquare_unique (φ := κ ≫ T.α) ⟨?_, ?_⟩ hα₂
    · rw [Category.assoc, T.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      show ((fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
    · rw [Category.assoc, T.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      show ((snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
  rw [e₃, hΛ, ← pull_comp, hQ]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLe
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem filt_mul_filt_le (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ) :
    filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  classical
  refine Ideal.mul_le.2 fun F hF G hG => ?_
  rw [mem_filt] at hF hG ⊢
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hα : p.1 + p.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : α.degree = p.1.degree + p.2.degree := by rw [← hα, map_add (f := _)]
  have h := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.FormalOrigin.Extend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatFamilyExistsUnique
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

abbrev locAlg (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (s : D) :
    D →ₐ[R] Localization.Away s :=
  IsScalarTower.toAlgHom R D (Localization.Away s)

theorem sm_loc_of_mem {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} (W : K → X.left.Opens)
    (hW : ⨆ i, W i = ⊤) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (P : PrimeSpectrum D) :
    ∃ s : D, s ∉ P.asIdeal ∧ Sm W (D := Localization.Away s) (spOver (locAlg R s) ≫ x) := by
  have h1 : x.left.base P ∈ (⨆ i, W i) := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp h1
  obtain ⟨V, ⟨s, rfl⟩, hPV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := P)
      (u := (x.left ⁻¹ᵁ W i).1) hi (x.left ⁻¹ᵁ W i).isOpen
  refine ⟨s, hPV, i, fun q _ ↦ ?_⟩
  have hq : (spMap (algebraMap D (Localization.Away s))).base q ∈ PrimeSpectrum.basicOpen s := by
    change s ∉ (PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q).asIdeal
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  exact hVU hq

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

def awR (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away a →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b
  commutes' r := by
    change IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away a),
      IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply]

def awL (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away b →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a
  commutes' r := by
    change IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away b),
      IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply]

theorem awR_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awR R a b).comp (locAlg R a) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayRight_eq (P := Localization.Away (a * b)) a b z

theorem awL_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awL R a b).comp (locAlg R b) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayLeft_eq (P := Localization.Away (a * b)) b a z

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem natFamily_existsUnique :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D)
      (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
      Sm W (D := E) (spOver ψ ≫ x) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ x) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ x τ hτ
  let S : Set D := {s | Sm W (D := Localization.Away s) (spOver (locAlg R s) ≫ x)}
  have key : ∀ (s : D), s ∈ S → ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
      (θ : Localization.Away s →ₐ[R] E), θ.comp (locAlg R s) = ψ → θ (τ _ (locAlg R s)) = τ E ψ := by
    intro s hs E _ _ ψ θ h
    rw [← hτ _ _ _ θ hs, h]
  have span : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := sm_loc_of_mem W hW x ⟨M, hM.isPrime⟩
    exact hsM (hSM (Ideal.subset_span hs))
  let v : ∀ a : S, Localization.Away a.1 := fun a ↦ τ _ (locAlg R a.1)
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S span v (fun a b ↦ by
    have e1 := key a a.2 _ _ (awR R (a : D) b) (awR_comp R _ _)
    have e2 := key b b.2 _ _ (awL R (a : D) b) (awL_comp R _ _)
    exact e1.trans e2.symm)
  refine ⟨d, fun E _ _ ψ hψ ↦ ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locAlg R a.1) a.2).symm⟩
  have spanE : Ideal.span ((ψ : D →+* E) '' S) = ⊤ := by
    rw [← Ideal.map_span, span, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ spanE
  funext ⟨t, s, hs, ht⟩
  subst ht
  let θ : E →ₐ[R] Localization.Away (ψ s) := locAlg R (ψ s)
  let θ' : Localization.Away s →ₐ[R] Localization.Away (ψ s) := Localization.awayMapₐ ψ s
  have hc : θ'.comp (locAlg R s) = θ.comp ψ := AlgHom.ext fun z ↦ by
    simp [θ', θ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
  change θ (τ E ψ) = θ (ψ d)
  have e : τ _ (locAlg R s) = algebraMap D _ d := (hd ⟨s, hs⟩).symm
  rw [← hτ E _ ψ θ hψ, ← hc, ← key s hs _ _ θ' rfl, e]
  exact DFunLike.congr_fun hc d

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBase
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatConst

theorem exists_section (Y : Scheme.{0}) {K : Type} (W : K → Y.Opens) (hW : ⨆ i, W i = ⊤)
    (κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Y) → D)
    (hκ : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D' (Spec.map φ ≫ x) = φ (κ D x)) :
    ∃ s : Γ(Y, ⊤), ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D x = (Scheme.ΓSpecIso D).hom (x.appTop s) := by
  let J : Type := {U : Y.affineOpens // ∃ i, U.1 ≤ W i}
  let U : J → Y.Opens := fun j ↦ j.1.1
  have hsm : ∀ j : J, ∃ i, ⊤ ≤ j.1.2.fromSpec ⁻¹ᵁ W i := fun j ↦ by
    obtain ⟨i, hi⟩ := j.2
    refine ⟨i, ?_⟩
    rw [← j.1.2.fromSpec_preimage_self]
    exact fun _ h ↦ hi h
  have hcov : ∀ y : Y, ∃ j : J, y ∈ U j := fun y ↦ by
    have hy : y ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨V, hV, hyV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hi
    exact ⟨⟨⟨V, hV⟩, i, hle⟩, hyV⟩
  let sf : ∀ j : J, Γ(Y, U j) := fun j ↦ κ _ j.1.2.fromSpec
  have hgerm : ∀ (j : J) (y : Y) (hy : y ∈ U j),
      Y.presheaf.germ (U j) y hy (sf j) = κ _ (Y.fromSpecStalk y) := fun j y hy ↦ by
    rw [← j.1.2.fromSpecStalk_eq_fromSpecStalk hy]
    exact (hκ _ _ _ _ (hsm j)).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hcov y)) sf (fun a b ↦ by
      refine TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y hy ↦ ?_
      exact ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm a y hy.1)).trans
        ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm b y hy.2)).symm)
  have hnat : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y),
      (Scheme.ΓSpecIso D').hom ((Spec.map φ ≫ x).appTop s) = φ ((Scheme.ΓSpecIso D).hom (x.appTop s)) := by
    intro D D' φ x
    rw [Scheme.Hom.comp_appTop]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f (x.appTop s)) (Scheme.ΓSpecIso_naturality φ)
  have hj : ∀ j : J, κ _ j.1.2.fromSpec = (Scheme.ΓSpecIso _).hom (j.1.2.fromSpec.appTop s) := fun j ↦ by
    have h1 : j.1.2.fromSpec.appTop ≫ (Scheme.ΓSpecIso _).hom = Y.presheaf.map (homOfLE le_top).op := by
      have h0 := congrArg (fun q ↦ (Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop q ≫ (Scheme.ΓSpecIso _).hom)
        j.1.2.fromSpec_toSpecΓ
      simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Category.assoc,
        Iso.inv_hom_id_assoc] at h0
      exact h0
    exact (hs j).symm.trans (congrArg (fun f ↦ CommRingCat.Hom.hom f s) h1).symm
  refine ⟨s, fun D x hx ↦ Module.eq_of_localization_maximal (R := D) (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap D (Localization.AtPrime P)) _ _ fun P hP ↦ ?_⟩
  let φ : D ⟶ CommRingCat.of (Localization.AtPrime P) := CommRingCat.ofHom (algebraMap D _)
  refine (hκ _ _ φ x hx).symm.trans (Eq.trans ?_ (hnat _ _ φ x))
  obtain ⟨j, hy⟩ := hcov ((Spec.map φ ≫ x) (IsLocalRing.closedPoint (CommRingCat.of (Localization.AtPrime P))))
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem _ hy
  have hr : Set.range (Spec.map φ ≫ x) ⊆ Set.range j.1.2.fromSpec := by
    rw [j.1.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have : z ∈ (Spec.map φ ≫ x) ⁻¹ᵁ U j := by rw [htop]; trivial
    exact this
  haveI : IsOpenImmersion j.1.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := j.1.1) j.1.2
  have hf := IsOpenImmersion.lift_fac j.1.2.fromSpec _ hr
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift j.1.2.fromSpec _ hr)
  rw [← hψ] at hf
  rw [← hf]
  exact (hκ _ _ ψ _ (hsm j)).trans ((congrArg ψ (hj j)).trans (hnat _ _ ψ _).symm)

theorem const_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  intro R _ X K W hW hs k hk
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ X.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), @Pt R _ X D _ (al D x) := fun D x ↦ by
    letI : Algebra R D := al D x
    refine Over.homMk (U := SpAlg R D) (V := X) x ?_
    change x ≫ X.hom = Spec.map (Spec.preimage (x ≫ X.hom))
    exact (Spec.map_preimage (x ≫ X.hom)).symm
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ X.left) → D := fun D x ↦ @k D _ (al D x) (pt D x)
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
      (x : Pt X D) (x' : Pt X D'), Sm W x → spMap φ ≫ x.left = x'.left → k D' x' = φ (k D x) := by
    intro D _ _ D' _ _ φ x x' hx h
    have h1 : x.left ≫ X.hom = spMap (algebraMap R D) := Over.w x
    have h2 : x'.left ≫ X.hom = spMap (algebraMap R D') := Over.w x'
    have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change spMap φ ≫ spMap _ = spMap _
      rw [← h1, ← h2, ← h, Category.assoc]
    let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
    have h4 := hk D D' ψ x hx
    have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
    rw [h5] at h4
    exact (sub_eq_zero.1 h4.symm)
  obtain ⟨s, hs'⟩ := exists_section X.left W hW κ fun D D' φ x hx ↦
    @key D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom (pt D x) (pt D' _) hx rfl
  obtain ⟨r, rfl⟩ := hs s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r, fun D _ inst x hx ↦ ?_⟩
  have h1 : κ (CommRingCat.of D) x.left = k D x :=
    @key D _ inst D _ (al (CommRingCat.of D) x.left) (RingHom.id D) x (pt (CommRingCat.of D) x.left) hx (by
      change Spec.map (𝟙 _) ≫ _ = _
      rw [Spec.map_id, Category.id_comp]; rfl)
  rw [← h1, hs' (CommRingCat.of D) x.left hx]
  have h2 : x.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R D)) := Over.w x
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R D))
  rw [← h2, Scheme.Hom.comp_appTop] at h3
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3

end GlobalTheory.PtExt.NatConst
end

