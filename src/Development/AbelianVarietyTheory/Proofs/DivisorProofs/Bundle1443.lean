module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import GroundTheory.AutomorphicForms.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0010
public import GroundTheory.AutomorphicForms.SphericalIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
public import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
section
noncomputable section

open NumberField IsDedekindDomain Polynomial MeasureTheory GroundTheory.Automorphic UpperTheory.V.Af GlobalTheory.HenQ
open scoped ValuativeRel Pointwise

namespace GlobalTheory.HenQ.ShellOp

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}


end General

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Series

end Series

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Hecke

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

theorem lamS_univ' : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

theorem gMat_univ' (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ']

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem central_mem_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h1 : ∀ g, f (g * torusPow F n (fun _ => 1)) = monomialChar (fun _ : Fin n => 1) z * f g := by
    intro g
    have h := hT g
    haveI : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) := ⟨fun p => p.2.2.1 (Finset.mem_univ _)⟩
    have hc : ∀ I : Fintype (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]), (@Finset.univ _ I).card = 1 := by
      intro I
      rw [Subsingleton.elim I Unique.fintype]
      rfl
    rw [integral_minusculeHecke_mul hf, evalAt_satakeTransform_minusculeHecke z le_rfl, evalAt_esymmL, hp,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_congr rfl (fun c _ => by rw [gMat_univ' c]),
      Finset.sum_const, hc, one_smul, lamS_univ', Nat.sub_self, mul_zero,
      pow_zero, mul_one, mul_assoc] at h
    exact mul_left_cancel₀ hK h
  have h2 : ∀ g, f (g * torusPow F n (fun _ => -1)) = monomialChar (fun _ : Fin n => -1) z * f g := by
    intro g
    have h := h1 (g * torusPow F n (fun _ => -1))
    have e : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by funext i; simp
    have e' : torusPow F n (fun _ => -1) * torusPow F n (fun _ => 1) = 1 := by
      have : (fun _ : Fin n => (-1 : ℤ)) = -(fun _ => 1) := rfl
      rw [this, torusPow_neg, inv_mul_cancel]
    rw [mul_assoc, e', mul_one] at h
    rw [h, ← mul_assoc, ← monomialChar_add, e, monomialChar_zero, one_mul]
  intro g
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      f (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    have hiff : g₀ * y ∈ centralSet F n ↔ y ∈ (integralGL F n : Set (GL (Fin n) F)) := by
      rw [mem_centralSet, inv_mul_cancel_left]
      rfl
    by_cases hy : y ∈ (integralGL F n : Set (GL (Fin n) F))
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, one_mul, ← mul_assoc, hf _ _ hy]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy, zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, h2, satakeTransform_centralHecke, map_smul,
    Spherical.monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem minuscule_mem_of (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
  intro g
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc, ← mul_assoc (sqrtQ F ^ _), ← h g]
  rfl

end Hecke

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Global

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {K : Type} [Field K] [NumberField K]

end Global

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

end GlobalTheory.HenQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToOneOfStalkMap
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSResOnto

open GlobalTheory.HSCore.VanishNumberField

theorem vanishFrom_adj_of_nef_big : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (B₀ : LB G.Y), B₀.IsLB →
    IsNef K B₀ → IsBig K B₀ → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle B₀)) 0 := by
  intro Q K _ _ G B₀ hB₀ hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens B₀ (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens B₀ (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens B₀ (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens B₀ (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((tw (tens G.K.bundle B₀) G.L j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB hB₀) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB hB₀,
          cls_tens hB₀ (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (tw (tens G.K.bundle B₀) G.L j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) q hKV
  have hB : (tens G.K.bundle B₀).IsLB := isLB_tens G.K.isLB hB₀
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle B₀)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

section Comb

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Comb

section Germs
variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} {I : Y.IdealSheafData}

theorem vanishesTo_one_of_stalkMap {f : Vanishing.H0 p B O}
    (h : ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ O) (j : (B.pull I.subschemeι).ι)
      (hj : z ∈ (B.pull I.subschemeι).U j),
      (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) f) = 0) :
    VanishesTo I 1 f := by
  intro y hs hy i hi
  obtain ⟨z, rfl⟩ := exists_ι_eq hs
  rw [pow_one, ← ker_stalkMap]
  exact RingHom.mem_ker.2 (h z hy (fun _ => i) (mem_pull.2 hi))

theorem stalkMap_germ_eq_zero {f : Vanishing.H0 p B O} (hf : VanishesTo I 1 f) (z : I.subscheme)
    (hz : I.subschemeι z ∈ O) (i : B.ι) (hi : I.subschemeι z ∈ B.U i) :
    (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ i (I.subschemeι z) hz hi f) = 0 := by
  have := hf _ (ι_mem_support I z) hz i hi
  rw [pow_one, ← ker_stalkMap] at this
  exact RingHom.mem_ker.1 this

end Germs

theorem res_onto : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.L₂ → IsBig K G.L₂ →
    ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s), Function.Surjective fun f => hs.res 0 (G.mulE 0 f) := by
  intro Q K _ _ G hnef hbig s hs
  have hB : (tens G.K.bundle G.L₂).IsLB := isLB_tens G.K.isLB G.isLB₂
  have hB' : (G.adj₂ 0).IsLB := isLB_tw hB G.isLB _
  obtain ⟨g, hg, hreg⟩ := _root_.GlobalTheory.RegBasis.exists_regular_basis K G s hs _ hB
  have hproj : IsProjOver (GlobalTheory.strHom K (X := G.Y)) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  have hinv : ∀ {O : G.Y.Opens} {f : Vanishing.H0 G.str (G.adj₂ 0) O},
      VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f → VanishesTo (G.ideal s) 1 f := by
    intro O f hf
    have e : (fun a => ∑ i, g⁻¹ a i • ∑ j, g i j • s j) = s := funext fun a => by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h := vanishesTo_of_isUnit G (fun i => ∑ j, g i j • s j) g⁻¹ (Matrix.isUnit_nonsing_inv_det g hg) hf
    rwa [e] at h
  have key : ∀ y₀ : sectionsOnClosedSubscheme G.str (G.adj₂ 0) (G.ideal s), ∃ f, resTo suppIn_top f = y₀ := by
    intro y₀
    choose W hW b hb using fun y => _root_.GlobalTheory.Vanishing.exists_local_lift_H0On K G.Y G.str (G.adj₂ 0) hB' (G.ideal s) y₀ y
    have hcomp : ∀ y z, VanishesTo (G.ideal s) 1 (Vanishing.H0.restr inf_le_left (b y) -
        Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 G.str (G.adj₂ 0) (W y ⊓ W z)) := by
      intro y z
      refine vanishesTo_one_of_stalkMap fun z' hz' j hj => ?_
      rw [map_sub, Vanishing.H0.germ_restr, Vanishing.H0.germ_restr, map_sub, ← hb y z' hz'.1 j hj,
        ← hb z z' hz'.2 j hj, sub_self]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle K G.Y hproj G.str _ G.L hB G.isLB G.D _ _ hreg
      (vanishFrom_adj_of_nef_big Q K G G.L₂ G.isLB₂ hnef hbig) (by simp) W b hW
      fun y z => vanishesTo_of_isUnit G s g hg (hcomp y z)
    refine ⟨σ, Vanishing.H0.ext_germ fun z _ => ?_⟩
    obtain ⟨c, hc⟩ := exists_chart hB' ((G.ideal s).subschemeι z)
    refine ⟨fun _ => c, mem_pull.2 hc, ?_⟩
    have h₁ := stalkMap_germ_eq_zero (hinv (hσ ((G.ideal s).subschemeι z))) z (hW _) c hc
    rw [map_sub, Vanishing.H0.germ_restr, map_sub, sub_eq_zero] at h₁
    refine (germ_resTo suppIn_top (fun _ => c) z (mem_pull.2 hc) σ).trans ?_
    rw [hb _ z (hW _) (fun _ => c) (mem_pull.2 hc)]
    exact h₁
  intro y₀
  obtain ⟨f, hf⟩ := key (Vanishing.mulDs G.K G.isLB G.isLB₂ (G.sec s) hs.etale rfl y₀)
  refine ⟨f, ?_⟩
  change hs.res 0 (G.mulE 0 f) = y₀
  rw [hs.res_mulE]
  exact (Vanishing.resDs_eq_iff G.K G.isLB G.isLB₂ (G.sec s) hs.etale suppIn_top rfl f y₀).2 hf

end GlobalTheory.HSResOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.MovSize

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

abbrev Zs (F : Type) [Field F] [NumberField F] (n d : ℕ) : Type :=
  (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd
  rw [map_add (f := _), map_add (f := _)]

theorem infAd_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : infAd F (t • a) = realAd F t * infAd F a := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • a) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, Algebra.smul_def]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    rw [mul_zero]

theorem liftI_add (M : Model σ X W) (ζ ζ' : Zs F n d) : liftI M (ζ + ζ') = liftI M ζ + liftI M ζ' := by
  unfold liftI
  rw [← map_add (f := _)]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_add]

theorem liftI_smul (M : Model σ X W) (t : ℝ) (ζ : Zs F n d) : liftI M (t • ζ) = realAd F t • liftI M ζ := by
  unfold liftI
  rw [← LinearEquiv.map_smul]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_smul]

theorem arch_e_liftI (M : Model σ X W) (ζ : Zs F n d) :
    (arch F (M.co.e (liftI M ζ)).1, arch F (M.co.e (liftI M ζ)).2) = ζ := by
  unfold liftI arch
  rw [LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

def readC (M : Model σ X W) : Zs F n d →ₗ[ℝ] (InfinitePlace F → Fin n → Fin d → ℂ) where
  toFun ζ w i j := piInf (τ w) (liftI M ζ i j)
  map_add' ζ ζ' := by funext w i j; simp [liftI_add, map_add (f := _)]
  map_smul' t ζ := by
    funext w i j
    simp only [liftI_smul, Matrix.smul_apply, RingHom.id_apply, Pi.smul_apply]
    rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]

theorem readC_injective (hCM : IsCMExt F E σ) (M : Model σ X W) : Function.Injective (readC τ M) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro ζ hζ
  have hA := (liftI_at_movI F E σ n d X W M 1 ζ).1
  have h0 : liftI M ζ = 0 := by
    ext i j
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
    · intro a ha
      have := congrFun (congrFun (hA a ha) i) j
      simpa [Matrix.smul_apply] using this
    · intro w
      exact congrFun (congrFun (congrFun hζ w) i) j
  rw [← arch_e_liftI M ζ, h0, map_zero]
  refine Prod.ext ?_ ?_ <;> funext i <;> exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem norm_piInf_eq (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ₀ τ' : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ‖piInf τ' z‖ = ‖piInf τ₀ z‖ := by
  unfold piInf
  rcases infEmb_eq_or_conj hCM τ₀ τ' with e | e
  · rw [RingHom.comp_apply, RingHom.comp_apply, e]
  · rw [RingHom.comp_apply, RingHom.comp_apply, e, RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.ArchDecay.MovSize


open GlobalTheory.ArchDecay.MovSize in
theorem GlobalTheory.ArchDecay.movI_size : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hCM : IsCMExt F E σ := hP.base.cm
  set L := readC B.emb M with hL
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 (readC_injective B.emb hCM M))
  set Lc := LinearMap.toContinuousLinearMap L with hLc
  refine ⟨K * (n * d) * ‖Lc‖, 1, fun g h ζ => ?_⟩
  have h1 : ‖movI M (g, h) ζ‖ ≤ K * ‖L (movI M (g, h) ζ)‖ := by
    have := hK.le_mul_dist (movI M (g, h) ζ) 0
    simpa [dist_eq_norm] using this
  have hB : ∀ (w : InfinitePlace F) (τ' : EmbOver E w) k l, ‖piInf τ' (liftI M ζ k l)‖ ≤ ‖L ζ‖ := by
    intro w τ' k l
    rw [norm_piInf_eq hCM (B.emb w) τ']
    exact (norm_le_pi_norm (L ζ w k) l).trans ((norm_le_pi_norm (L ζ w) k).trans (norm_le_pi_norm (L ζ) w))
  have hg : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).1 : ℝ) = ht g := by
    show ((heightGL F ((g⁻¹ : UA σ X.J) : GL (Fin n) (AE F E))) : ℝ) = heightGL F (g : GL (Fin n) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hh : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).2 : ℝ) = ht h := by
    show ((heightGL F ((h⁻¹ : UA σ W.J) : GL (Fin d) (AE F E))) : ℝ) = heightGL F (h : GL (Fin d) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hgh : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  have hpos : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := mul_nonneg hgh (norm_nonneg _)
  have h2 : ‖L (movI M (g, h) ζ)‖ ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := by
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun j => ?_
    show ‖piInf (B.emb w) (liftI M (movI M (g, h) ζ) i j)‖ ≤ _
    rw [(liftI_at_movI F E σ n d X W M (g, h) ζ).2]
    have := GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d X.J W.J (g, h)⁻¹ (liftI M ζ) ‖L ζ‖ (norm_nonneg _) hB w
      (B.emb w) i j
    rwa [hg, hh] at this
  have h3 : ‖L ζ‖ ≤ ‖Lc‖ * ‖ζ‖ := Lc.le_opNorm ζ
  have hK0 : (0 : ℝ) ≤ K := K.2
  calc ‖movI M (g, h) ζ‖ ≤ K * (n * d * ((ht g : ℝ) * ht h) * (‖Lc‖ * ‖ζ‖)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hgh)) hK0)
    _ = K * (n * d) * ‖Lc‖ * ((ht g : ℝ) * ht h) ^ 1 * ‖ζ‖ := by ring
end
end

