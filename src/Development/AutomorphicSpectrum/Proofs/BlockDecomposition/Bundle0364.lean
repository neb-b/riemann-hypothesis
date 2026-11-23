module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifference
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem lbIso_pull_quot_of_consecutive_pw : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  intro X Y b A C N n hA hC hN h1 h2
  have hAb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hA b
  have hCb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hC b
  have hT := GlobalTheory.AbLaw.isLB_tw hC hA (-1)
  have hTb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hT b
  rw [← GlobalTheory.CechPic.cls_eq_iff hN hTb, GlobalTheory.CechPic.cls_pull hT b hTb]
  have e1 := (GlobalTheory.CechPic.cls_eq_iff hAb (GlobalTheory.AbLaw.isLB_pw hN n)).2 h1
  have e2 := (GlobalTheory.CechPic.cls_eq_iff hCb (GlobalTheory.AbLaw.isLB_pw hN (n + 1))).2 h2
  rw [GlobalTheory.CechPic.cls_pull hA b hAb, GlobalTheory.EffBound.cls_pw hN n] at e1
  rw [GlobalTheory.CechPic.cls_pull hC b hCb, GlobalTheory.EffBound.cls_pw hN (n + 1)] at e2
  have hT' : GlobalTheory.CechPic.cls (GlobalTheory.AbLaw.tw C A (-1)) hT
      = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
    show GlobalTheory.CechPic.cls (C.div (GlobalTheory.AbLaw.pw A (-(-1)))) hT = _
    rw [GlobalTheory.CechPic.cls_div hC (GlobalTheory.AbLaw.isLB_pw hA _) hT, GlobalTheory.EffBound.cls_pw hA]
    simp
  rw [hT', map_sub, e1, e2, add_smul, one_smul, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.FormalAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.RelOpsLeaf

section Linear

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem eq_det_smul_one (hV : finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  have hm := LinearMap.charpoly_monic f
  have hd : f.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, hV]
  have h1 := hm.eq_X_add_C hd
  have h2 := LinearMap.aeval_self_charpoly f
  obtain ⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by
    refine ⟨-f.charpoly.coeff 0, ?_⟩
    rw [h1, map_add (f := _), aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  subst ht
  rw [LinearMap.det_smul, hV, pow_one]
  simp

theorem charpoly_smul_eq_scaleRoots (f : Module.End ℂ V) {t : ℂ} (ht : t ≠ 0) :
    (t • f).charpoly = f.charpoly.scaleRoots t := by
  refine Polynomial.funext fun z => ?_
  have h0 : t * (z / t) = z := by field_simp
  have h1 := scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t
  simp only [RingHom.id_apply, h0, eval₂_id] at h1
  rw [h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree,
    ← LinearMap.det_smul]
  congr 1
  rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]

theorem charpoly_map_one (hV' : finrank ℂ V' = 1) (f : Module.End ℂ V) :
    (TensorProduct.map f (1 : Module.End ℂ V')).charpoly = f.charpoly := by
  let e : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])
  let F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [F]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← LinearEquiv.charpoly_conj F]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := F.surjective v
  simp [LinearEquiv.conj_apply, key]

end Linear

theorem pow_of_mul_eq_pow {p q : ℂ[X]} {m n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m) (hqd : q.natDegree = n) (h : p * q = (X - 1) ^ (m + n)) :
    p = (X - 1) ^ m ∧ q = (X - 1) ^ n := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at h ⊢
  have key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree := by
    intro r hr hd
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd
    have h1 := eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi
    have h2 : r.natDegree = i := by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [h2]
    exact h1
  subst hpd hqd
  exact ⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩

section Rel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_char_of_lpDim_eq_one (c : WD h) (hc : c.lpDim = 1) :
    ∃ χ : ↥(Weil h) →* ℂˣ, ∀ (x : WD h) (g : ↥(Weil h)),
      (x.lpChar c).charPol g = (x.charPol g).scaleRoots (χ g : ℂ) := by
  induction c using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk] at hc
    let f : ↥(Weil h) →* ℂ := (LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ
    refine ⟨f.toHomUnits, fun x g => ?_⟩
    induction x using WD.ind with
    | hP n a =>
      have hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ)) := by
        rw [MonoidHom.coe_toHomUnits]
        exact eq_det_smul_one hc (b.ρ g)
      rw [WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb,
        TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _),
        charpoly_map_one hc]

end Rel

end GlobalTheory.CompanionTheory.RelOpsLeaf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmple
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.ConsecAmple

variable {R : Type} [CommRing R] {X Y Z P : Scheme.{0}}

theorem veryAmpleBy_box {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)} (sq : IsPullback p q f g) {H : LB X} {K : LB Y} {m n : ℕ}
    {s : Fin (m + 1) → LB.Sec H} {t : Fin (n + 1) → LB.Sec K} (hf : VeryAmpleBy f H s) (hg : VeryAmpleBy g K t)
    (e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1)) :
    VeryAmpleBy (p ≫ f) (box p q H K) fun a => boxSec p q (s (e a).1) (t (e a).2) := by
  obtain ⟨hs, hs'⟩ := hf
  obtain ⟨ht, ht'⟩ := hg
  refine ⟨?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

theorem veryAmpleBy_secPull {f : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {M : ℕ} {s : Fin (M + 1) → LB.Sec L}
    (h : VeryAmpleBy f L s) (j : Z ⟶ Y) [IsClosedImmersion j] :
    VeryAmpleBy (j ≫ f) (L.pull j) fun i => GlobalTheory.Cartier.secPull (s i) j := by
  obtain ⟨hs, hc⟩ := (veryAmpleBy_iff f s).1 h
  refine (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull hs j, ?_⟩
  rw [toProj_secPull hs j]
  infer_instance

theorem gm_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (r : Z ⟶ P) (z : Z) (hz : r z ∈ W)
    (u : Γ(X, U)ˣ) : gm r z W (Units.map (ap p h).toMonoidHom u) = gm (r ≫ p) z U u := by
  have e : Units.map (ap p h).toMonoidHom u = res h (pullU p U u) := Units.ext rfl
  rw [e]
  exact (gm_res r z h hz _).trans (gm_pull r p z U (h hz) u)

theorem gm_box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) (r : Z ⟶ P) (z : Z) (a b : H.ι × K.ι)
    (h : r z ∈ (box p q H K).U a ⊓ (box p q H K).U b) :
    gm r z ((box p q H K).U a ⊓ (box p q H K).U b) ((box p q H K).g a b) =
      gm (r ≫ p) z (H.U a.1 ⊓ H.U b.1) (H.g a.1 b.1) * gm (r ≫ q) z (K.U a.2 ⊓ K.U b.2) (K.g a.2 b.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_ap p _ r z h _) (gm_ap q _ r z h _))

theorem mem_box_of_graph (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) (c : (B.pull ψ).ι × H.ι) (y : X) (hy : y ∈ (tw (B.pull ψ) H 1).U c) :
    j y ∈ (box p q H B).U (c.2, c.1 PUnit.unit) := by
  have h₁ : p (j y) = y := by rw [← Scheme.Hom.comp_apply, hp]; rfl
  have h₂ : q (j y) = ψ y := by rw [← Scheme.Hom.comp_apply, hq]
  have h₃ : ψ y ∈ B.U (c.1 PUnit.unit) := mem_pull.1 hy.1
  have h₄ : y ∈ H.U c.2 := hy.2
  exact ⟨show p (j y) ∈ H.U c.2 by rw [h₁]; exact h₄, show q (j y) ∈ _ by rw [h₂]; exact h₃⟩

def chartPullBox (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) : ChartPull (tw (B.pull ψ) H 1) (box p q H B) j where
  idx c := (c.2, c.1 PUnit.unit)
  le c y hy := mem_box_of_graph p q H B ψ j hp hq c y hy
  g y c c' hc hc' := by
    refine (GlobalTheory.LBAlg.gm_tw (B.pull ψ) H 1 (𝟙 X) y c c' ⟨hc, hc'⟩).trans (Eq.trans ?_
      (gm_box p q H B j y _ _ ⟨mem_box_of_graph p q H B ψ j hp hq c y hc,
        mem_box_of_graph p q H B ψ j hp hq c' y hc'⟩).symm)
    rw [gm_pull_g B ψ (𝟙 X) y c.1 c'.1 hc.1 hc'.1, hp, hq, Category.id_comp, zpow_one, mul_comm]

theorem exists_veryAmpleBy_tw {f : X ⟶ Spec (CommRingCat.of R)} {K M : LB X} (hK : K.IsLB) (hM : M.IsLB) {m n : ℕ}
    {a : Fin (m + 1) → LB.Sec K} (ha : VeryAmpleBy f K a) {c : Fin (n + 1) → LB.Sec M}
    (hc : ⨆ i, nonzeroLocus (c i) = ⊤) :
    ∃ (m' : ℕ) (s : Fin (m' + 1) → LB.Sec (tw M K 1)), VeryAmpleBy f (tw M K 1) s := by
  have hψ : toProj f c hc ≫ PSpace.str R n = f := toProj_str f c hc
  have sq := IsPullback.of_hasPullback f (PSpace.str R n)
  let j : X ⟶ pullback f (PSpace.str R n) := pullback.lift (𝟙 X) (toProj f c hc) (by rw [hψ, Category.id_comp])
  have hp : j ≫ pullback.fst f (PSpace.str R n) = 𝟙 X := pullback.lift_fst _ _ _
  have hq : j ≫ pullback.snd f (PSpace.str R n) = toProj f c hc := pullback.lift_snd _ _ _
  have := isProper_str R n
  have : IsSeparated (pullback.fst f (PSpace.str R n)) := inferInstance
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f (PSpace.str R n)) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp j (pullback.fst f (PSpace.str R n))
  have hcoord : VeryAmpleBy (PSpace.str R n) (O1 R n) (coord R n) :=
    (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) := (finCongr (by ring)).trans finProdFinEquiv.symm
  have h₁ := veryAmpleBy_secPull (veryAmpleBy_box sq ha hcoord e) j
  have e₁ : j ≫ pullback.fst f (PSpace.str R n) ≫ f = f := by rw [← Category.assoc, hp, Category.id_comp]
  rw [e₁] at h₁
  have hB := isLB_box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) hK (O1_isLB R n)
  have hO := LB.isLB_pull (O1_isLB R n) (toProj f c hc)
  have i₁ : LBIso ((box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) K (O1 R n)).pull j)
      (tw ((O1 R n).pull (toProj f c hc)) K 1) :=
    LBIso.chartPull (chartPullPull _ j) (chartPullBox _ _ K (O1 R n) _ j hp hq) (GlobalTheory.LBAlg.lbIso_self hB)
  have i₂ := GlobalTheory.LBAlg.lbIso_tw_congr (t := 1) hK (lbIso_pullback_O1_toProj f c hc)
  obtain ⟨t, ht⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (LB.isLB_pull hB j) (isLB_tw hM hK 1)
    (LBIso.trans (LB.isLB_pull hB j) (isLB_tw hO hK 1) (isLB_tw hM hK 1) i₁ i₂) h₁
  exact ⟨_, t, ht⟩

theorem gm_pw (H : LB X) (n : ℤ) (r : Z ⟶ X) (z : Z) (i j : H.ι) :
    gm r z ((pw H n).U i ⊓ (pw H n).U j) ((pw H n).g i j) = gm r z (H.U i ⊓ H.U j) (H.g i j) ^ n :=
  map_zpow _ _ _

theorem pw_pw (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  change (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  simp only [zpow_mul]

theorem lbIso_tw_tw_pw {L : LB X} (hL : L.IsLB) (N t : ℤ) :
    LBIso (tw (tw L (pw L N) t) (pw (pw L N) t) 1) (pw L (1 + 2 * N * t)) := by
  have l₁ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.1 :=
    fun p x hx => ⟨hx.1, hx.2.1.1⟩
  have l₂ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.2 :=
    fun p x hx => ⟨hx.1, hx.2.1.2⟩
  have l₃ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2 :=
    fun p x hx => ⟨hx.1, hx.2.2⟩
  have v : ∀ (x : X) (p : L.ι × ((L.ι × L.ι) × L.ι)), x ∈ L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) →
      gm (𝟙 X) x _ (res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
          res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) =
        gm (𝟙 X) x _ (L.g p.1 p.2.1.1) * gm (𝟙 X) x _ (L.g p.1 p.2.1.2) ^ (N * t) *
          gm (𝟙 X) x _ (L.g p.1 p.2.2) ^ (N * t) :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ x _ hx _) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _)))))
      ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))
  have key : ∀ (x : X) {a b i j : L.ι}, x ∈ L.U a → x ∈ L.U b → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (L.g a i) = gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b j) * (gm (𝟙 X) x _ (L.g i j))⁻¹ := by
    intro x a b i j ha hb hi hj
    rw [gm_cocycle hL (𝟙 X) x ha hb hj, ← gm_cocycle hL (𝟙 X) x ha hi hj, mul_inv_cancel_right]
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
    res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) fun x p q h₁ h₂ h₃ h₄ => ?_
  have eA : gm (𝟙 X) x _ ((tw (tw L (pw L N) t) (pw (pw L N) t) 1).g p.2 q.2) =
      gm (𝟙 X) x (L.U p.2.1.1 ⊓ L.U q.2.1.1) (L.g p.2.1.1 q.2.1.1) *
        gm (𝟙 X) x (L.U p.2.1.2 ⊓ L.U q.2.1.2) (L.g p.2.1.2 q.2.1.2) ^ (N * t) *
        gm (𝟙 X) x (L.U p.2.2 ⊓ L.U q.2.2) (L.g p.2.2 q.2.2) ^ (N * t) := by
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L N) t) (pw (pw L N) t) 1 (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩).trans ?_
    rw [GlobalTheory.LBAlg.gm_tw L (pw L N) t (𝟙 X) x p.2.1 q.2.1 ⟨h₂.1, h₄.1⟩]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_
    · exact (congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.1.2 q.2.1.2)).trans (zpow_mul _ _ _).symm
    · exact ((zpow_one _).trans (gm_pw (pw L N) t (𝟙 X) x p.2.2 q.2.2)).trans
        ((congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.2 q.2.2)).trans (zpow_mul _ _ _).symm)
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw L _ (𝟙 X) x p.1 q.1).symm
    (congrArg (·⁻¹) eA.symm)) (v x q ⟨h₃, h₄⟩).symm))
  have k₁ := key x (a := p.1) (b := q.1) (i := p.2.1.1) (j := q.2.1.1) h₁ h₃ h₂.1.1 h₄.1.1
  have k₂ := key x (a := p.1) (b := q.1) (i := p.2.1.2) (j := q.2.1.2) h₁ h₃ h₂.1.2 h₄.1.2
  have k₃ := key x (a := p.1) (b := q.1) (i := p.2.2) (j := q.2.2) h₁ h₃ h₂.2 h₄.2
  rw [k₁, k₂, k₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem exists_consecutive_veryAmple : ∀ (A : Type) [CommRing A] [IsNoetherianRing A]
    (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ)
    (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))),
    VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  intro A _ _ X L hL hA
  obtain ⟨N, hN, m, s, hH, hs⟩ := veryAmpleBy_of_relAmple hL hA (𝟙 X.left) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _)) (GlobalTheory.LBAlg.lbIso_self hL))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated A X.left X.hom (pw L N) m s hH hs L hL
  obtain ⟨T, hT, hTt⟩ : ∃ T : ℕ, 1 ≤ T ∧ t₀ ≤ (T : ℤ) := ⟨(max t₀ 1).toNat, by omega, by omega⟩
  obtain ⟨n', u, hu⟩ := ht₀ T hTt
  obtain ⟨k, a, ha⟩ := veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs T hT
  have hK := isLB_pw hH T
  have hM := isLB_tw hL hH T
  obtain ⟨m', s', hs'⟩ := exists_veryAmpleBy_tw hK hM ha hu
  obtain ⟨t', ht'⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw hM hK 1) (isLB_pw hL _)
    (lbIso_tw_tw_pw hL N T) hs'
  have A₁ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T : ℕ) : ℤ)) a := by
    have e₁ : pw L ((2 * N * T : ℕ) : ℤ) = pw (pw L N) ((2 * T : ℕ) : ℤ) := by
      rw [pw_pw]
      congr 1
      push_cast
      ring
    rw [e₁]
    exact veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs (2 * T) (by omega)
  have A₂ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T + 1 : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T + 1 : ℕ) : ℤ)) a := by
    have e₂ : ((2 * N * T + 1 : ℕ) : ℤ) = 1 + 2 * (N : ℤ) * (T : ℤ) := by
      push_cast
      ring
    rw [e₂]
    exact ⟨m', t', ht'⟩
  obtain ⟨k₁, a₁, h₁⟩ := A₁
  obtain ⟨k₂, a₂, h₂⟩ := A₂
  exact ⟨2 * N * T, Nat.mul_pos (Nat.mul_pos two_pos hN) hT, k₁, a₁, k₂, a₂, h₁, h₂⟩

end GlobalTheory.CompanionTheory.ConsecAmple
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplitStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_jacquet_two_factor_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π → ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  first | exact @GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | exact GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormulaStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Segment k) (y : IrrGL (k := k)), IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c → Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | exact GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Δ.first t c → Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | exact GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | (intros; apply GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignOne
section
noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dite_eq_left hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizableStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  first | exact @GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | exact GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | (intros; apply GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactorsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | exact GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | (intros; apply GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv <;> assumption)
end

