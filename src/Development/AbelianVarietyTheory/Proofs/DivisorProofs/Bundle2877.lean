module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMoves
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
open GlobalTheory.CosetOrth

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CosetOrth.Pairing

variable {D : D7}

theorem cA_fin_mul (e : D.host.E) (σ : AE D) (hσ : infPart D σ = 0) :
    cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) * σ = incA D (star e) * σ := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, mul_zero, sub_self]
  · have e1 : finPart D (cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e)) = finPart D (incA D (star e)) := rfl
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, e1, sub_self]

theorem hO_of_gram_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (x y : WO S T) :
    hO S T x y = ∑ a, ∑ c, cA D (y c a) * x c a := by
  unfold hO
  rw [hS, hT, inv_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, one_mul, mul_one]
    · intro d _ hd
      rw [Matrix.one_apply_ne (Ne.symm hd), RingHom.map_zero, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.one_apply_ne (Ne.symm hb), RingHom.map_zero, zero_mul, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def rowMat (S T : HSp D) (p : Fin T.rank) (f : Fin S.rank → AE D) : WO S T :=
  Matrix.of fun c a => if c = p then f a else 0

theorem hO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    hO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      -(incA D (star r⁻¹) * f j) := by
  rw [hO_of_gram_one S T hS hT]
  have h1 : ∀ a, (∑ c, cA D (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank) c a) * rowMat S T p f c a) =
      incA D (star (-(r⁻¹ * if p.1 = o + a.1 then 1 else 0))) * f a := by
    intro a
    rw [Finset.sum_eq_single p]
    · have : rowMat S T p f p a = f a := if_pos rfl
      rw [this]
      exact cA_fin_mul _ _ (hf a)
    · intro c _ hc
      have : rowMat S T p f c a = 0 := if_neg hc
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_eq_single j]
  · rw [if_pos hp, mul_one, star_neg, RingHom.map_neg, neg_mul]
  · intro a _ ha
    have : ¬ p.1 = o + a.1 := fun h => ha (Fin.ext (by omega))
    rw [if_neg this, mul_zero, neg_zero, star_zero, RingHom.map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem actO_rowMat (S T : HSp D) (g : GA D S) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    actO S T g 1 (rowMat S T p (Pi.single i σ)) = rowMat S T p fun a => σ * mt S g⁻¹ i a := by
  have h1 : mt T 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [MonoidHom.map_one]; rfl
  unfold actO
  rw [h1, Matrix.one_mul]
  funext c a
  rw [Matrix.mul_apply]
  by_cases hc : c = p
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = (Pi.single i σ : Fin S.rank → AE D) k := fun k => if_pos hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = σ * mt S g⁻¹ i a := if_pos hc
    rw [e', Finset.sum_eq_single i]
    · rw [e, Pi.single_eq_same]
    · intro k _ hk
      rw [e, Pi.single_eq_of_ne hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = 0 := fun k => if_neg hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = 0 := if_neg hc
    rw [e']
    exact Finset.sum_eq_zero fun k _ => by rw [e, zero_mul]

theorem two_smul_rowMat (S T : HSp D) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    2 • rowMat S T p (Pi.single i σ) = rowMat S T p (Pi.single i (2 * σ)) := by
  funext c a
  show 2 • (if c = p then (Pi.single i σ : Fin S.rank → AE D) a else 0) =
    if c = p then (Pi.single i (2 * σ) : Fin S.rank → AE D) a else 0
  by_cases hc : c = p
  · rw [if_pos hc, if_pos hc]
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same, Pi.single_eq_same, two_nsmul, two_mul]
    · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha, nsmul_zero]
  · rw [if_neg hc, if_neg hc, nsmul_zero]

theorem hatPt_rowMat (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (f : Fin S.rank → AE D) (h0 : ∀ a, infPart D (f a) = 0) (h1 : ∀ a, InHat I (algebraMap D.host.E (FA D) r * fe D (f a))) :
    HatPt r I (rowMat S T p f) := by
  refine ⟨?_, fun c a => ?_⟩
  · funext c a
    show infPart D (if c = p then f a else 0) = 0
    split_ifs
    · exact h0 a
    · exact RingHom.map_zero _
  · show InHat I (algebraMap D.host.E (FA D) r * fe D (if c = p then f a else 0))
    split_ifs
    · exact h1 a
    · rw [RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] (x y s a b : R) : x * (y * (s * (a - b))) = x * -(y * (s * b)) + -(x * -(y * (s * a))) := by
  ring

theorem addChar_linearMap_neg_add_eq_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : AddChar R ℂ) (t : M →ₗ[R] R) (A B : M)
    (h : ψ (t A) = ψ (t B)) : ψ (t (B + -A)) = 1 := by
  rw [map_add (f := _), map_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem symplO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    symplO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * -(incA D (star r⁻¹) * f j)) :=
  congrArg (fun z => Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z)) (hO_rowMat S T hS hT r o j p hp f hf)

theorem single_inf {n : ℕ} (i : Fin n) (s : AE D) (hs : infPart D s = 0) (a : Fin n) :
    infPart D ((Pi.single i s : Fin n → AE D) a) = 0 := by
  by_cases ha : a = i
  · rw [ha, Pi.single_eq_same]; exact hs
  · rw [Pi.single_eq_of_ne ha]; exact RingHom.map_zero _

theorem hatPt_single (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0) (h1 : InHat I (algebraMap D.host.E (FA D) r * fe D σ)) :
    HatPt r I (rowMat S T p (Pi.single i σ)) :=
  hatPt_rowMat S T r I p _ (single_inf i σ hσ) fun a => by
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne ha, RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem hatPt_act (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank) (g : GA D S)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0)
    (h2 : ∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) :
    HatPt r I (actO S T g 1 (rowMat S T p (Pi.single i σ))) := by
  rw [actO_rowMat]
  refine hatPt_rowMat S T r I p _ (fun a => by rw [RingHom.map_mul, hσ, zero_mul]) fun a => ?_
  rw [RingHom.map_mul, ← mul_assoc]; exact h2 a

theorem single_eq_mul_one {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (s : R) :
    (Pi.single i s : Fin n → R) j = s * (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases ha : j = i
  · rw [ha, Pi.single_eq_same, Matrix.one_apply_eq, mul_one]
  · rw [Pi.single_eq_of_ne ha, Matrix.one_apply_ne (Ne.symm ha), mul_zero]

theorem degree_lower_bound_of_rank_split {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ψ : AddChar R ℂ) {n : ℕ} (x y s : M) (i j : Fin n)
    (N : Matrix (Fin n) (Fin n) M)
    (h : ψ (Algebra.trace R M (x * -(y * (Pi.single i s : Fin n → M) j))) = ψ (Algebra.trace R M (x * -(y * (s * N i j))))) :
    ψ (Algebra.trace R M (x * (y * (s * (1 - N) i j)))) = 1 := by
  rw [single_eq_mul_one] at h
  rw [Matrix.sub_apply, units_mul_relation_rearrange_commRing]
  exact addChar_linearMap_neg_add_eq_one ψ _ _ _ h

theorem char_trace_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  intro D ψ S T r I o g hS hT ho H σ i j hσ h1 h2
  obtain ⟨p, hp⟩ : ∃ p : Fin T.rank, p.1 = o + j.1 := ⟨⟨o + j.1, by have := j.2; omega⟩, rfl⟩
  have h2σ : infPart D (2 * σ) = 0 := by rw [RingHom.map_mul, hσ, mul_zero]
  have key := H (rowMat S T p (Pi.single i σ)) (hatPt_single S T r I p i σ hσ h1) (hatPt_act S T r I p g i σ hσ h2)
  rw [two_smul_rowMat, actO_rowMat] at key
  have a1 := symplO_rowMat S T hS hT r o j p hp _ (single_inf i _ h2σ)
  have a2 := symplO_rowMat S T hS hT r o j p hp (fun a => 2 * σ * mt S g⁻¹ i a)
    (fun a => by rw [RingHom.map_mul, h2σ, zero_mul])
  exact degree_lower_bound_of_rank_split ψ _ _ _ i j _ ((congrArg ψ a1).symm.trans (key.trans (congrArg ψ a2)))

end GlobalTheory.CosetOrth.Pairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem archRecip_of_principalisation (hP : GlobalTheory.Published.Principalisation) : ArchRecip := by
  intro k _ Y _ _ q e hq M N L s t hs ht hcov
  have : IsNoetherian Y := hq.isNoetherian
  have : Finite (k →+* ℂ) := hq.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hcons (A : HermLB q) (σ : k →+* ℂ) :
      (fun i => MLine.ofHerm ((Fin.cons A L : Fin (e + 1) → HermLB q) i) σ) =
        Fin.cons (MLine.ofHerm A σ) (fun i => MLine.ofHerm (L i) σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, ((divOfSec A.isLB a ha).mult z : ℝ) *
          cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm B σ).logSec b) z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [_root_.GlobalTheory.MixHt.resArch_eq_finsum_cycInt hP k Y q e hq L B b z hz ((hab z hz).resolve_left hza), finsum_eq_sum_of_fintype,
        Finset.mul_sum]
  have fin (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
    D.finite_support_mult.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      simp [h] at hz
  have hside (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) :
      mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) A (isRatSec_ratOfSec a ha) +
          ∑ᶠ z, ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, side (MLine.ofHerm B σ) (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm A σ).logSec a)
          ((MLine.ofHerm B σ).logSec b) (divOfSec (MLine.ofHerm A σ).φ.isLB a ha) := by
    rw [_root_.GlobalTheory.MixPolar.mixArch_eq_sum hP k Y q (e + 1) hq, finsum_eq_sum_of_fintype, finsum_congr (key A B a b ha hab),
      finsum_sum_comm _ _ (fun σ _ => fin _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [side, ← hcons]
    rfl
  rw [hside M N s t hs hcov, hside N M t s ht fun z hz => (hcov z hz).symm]
  exact Finset.sum_congr rfl fun σ _ => _root_.GlobalTheory.MixRec.side_symm hP k Y q e hq σ (fun i => MLine.ofHerm (L i) σ)
    (MLine.ofHerm M σ) (MLine.ofHerm N σ) s hs t ht hcov

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_ideal_weight_section : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @GlobalTheory.LogCanon.logCanon_iff | exact GlobalTheory.LogCanon.logCanon_iff | (intros; apply GlobalTheory.LogCanon.logCanon_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamily
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechCobGlue

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem cocycle_coboundary_of_subcover : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro Y J W κ σ hcov E hE h' hh'
  have hcovi : ∀ i, W i ≤ ⨆ k, (W i ⊓ W (σ k)) := by
    intro i x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  let f : ∀ i k, Γ(Y, W i ⊓ W (σ k)) := fun i k => E i (σ k) + resG Y inf_le_right (h' k)
  have hf : ∀ i k k', resG Y (inf_le_left : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k)) (f i k)
      = resG Y (inf_le_right : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k')) (f i k') := by
    intro i k k'
    have hPT : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k) ⊓ W (σ k') :=
      le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have e1 := congrArg (resG Y hPT) (hE i (σ k) (σ k'))
    have e2 := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W (σ k) ⊓ W (σ k'))) (hh' k k')
    simp only [map_add (f := _), map_sub, resG_comp] at e1 e2
    simp only [f, map_add (f := _), resG_comp]
    linear_combination e1 - e2
  have hg : ∀ i, ∃ s : Γ(Y, W i), ∀ k, resG Y (inf_le_left : W i ⊓ W (σ k) ≤ W i) s = f i k := by
    intro i
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => W i ⊓ W (σ k)) (W i)
      (fun k => homOfLE (inf_le_left : W i ⊓ W (σ k) ≤ W i)) (hcovi i) (fun k => f i k)
      (fun k k' => hf i k k')
    exact ⟨s, hs⟩
  choose h hh using hg
  refine ⟨h, fun i i' => ?_⟩
  have hcov2 : W i ⊓ W i' ≤ ⨆ k, (W i ⊓ W i' ⊓ W (σ k)) := by
    intro x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  apply Y.sheaf.eq_of_locally_eq' (fun k => W i ⊓ W i' ⊓ W (σ k)) (W i ⊓ W i')
    (fun k => homOfLE (inf_le_left : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W i')) hcov2
  intro k
  show resG Y inf_le_left (E i i') = resG Y inf_le_left (resG Y inf_le_left (h i) - resG Y inf_le_right (h i'))
  have A := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W (σ k))) (hh i k)
  have B := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i' ⊓ W (σ k))) (hh i' k)
  have C := hE i i' (σ k)
  simp only [f, map_add (f := _), resG_comp] at A B
  simp only [map_sub, resG_comp]
  linear_combination C - A + B

end GlobalTheory.CechCobGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.DlogCocycle

theorem resG_resG {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = resG X h u.val := rfl

theorem resG_dlog {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    {P A T : Z.Opens} (hA : A ≤ W₀) (hTA : T ≤ A) (hAP : A ≤ P) (u : Γ(Z, P)ˣ) :
    resG Z hTA (d A (resG Z hAP u.val) * resG Z hAP u⁻¹.val) =
      d T (resG Z (hTA.trans hAP) u.val) * resG Z (hTA.trans hAP) u⁻¹.val := by
  rw [map_mul, ← hd.2.2 A T hTA hA, resG_resG, resG_resG]

theorem dlog_cocycle : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  intro Z L hL W₀ d hd J W j hW hj i i' i''
  have hT0 : W i ⊓ W i' ⊓ W i'' ≤ W₀ := inf_le_left.trans (inf_le_left.trans (hW i))
  have hT : W i ⊓ W i' ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    inf_le_inf (inf_le_inf (hj i) (hj i')) (hj i'')
  rw [resG_dlog hd ((inf_le_left : W i ⊓ W i' ≤ W i).trans (hW i)),
    resG_dlog hd ((inf_le_left : W i' ⊓ W i'' ≤ W i').trans (hW i')),
    resG_dlog hd ((inf_le_left : W i ⊓ W i'' ≤ W i).trans (hW i))]
  have e := congrArg (fun u => resG Z hT u.val) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, map_mul, res_val, resG_resG] at e
  have inv : ∀ {P : Z.Opens} (h : W i ⊓ W i' ⊓ W i'' ≤ P) (u : Γ(Z, P)ˣ),
      resG Z h u.val * resG Z h u⁻¹.val = 1 := fun h u => by rw [← map_mul, Units.mul_inv, map_one]
  have e1 := inv (((inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i').trans (inf_le_inf (hj i) (hj i'))))
    (L.g (j i) (j i'))
  have e2 := inv ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'').trans
    (inf_le_inf (hj i') (hj i''))) (L.g (j i') (j i''))
  have e3 := inv ((le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'').trans
    (inf_le_inf (hj i) (hj i''))) (L.g (j i) (j i''))
  generalize resG Z _ (L.g (j i) (j i')).val = x1 at e e1 ⊢
  generalize resG Z _ (L.g (j i') (j i'')).val = x2 at e e2 ⊢
  generalize resG Z _ (L.g (j i) (j i'')).val = x3 at e e3 ⊢
  generalize resG Z _ (L.g (j i) (j i'))⁻¹.val = y1 at e1 ⊢
  generalize resG Z _ (L.g (j i') (j i''))⁻¹.val = y2 at e2 ⊢
  generalize resG Z _ (L.g (j i) (j i''))⁻¹.val = y3 at e3 ⊢
  have hy3 : y3 = y1 * y2 := by
    linear_combination (-y3 * x2 * y2) * e1 - y3 * e2 + y1 * y2 * e3 + y1 * y2 * y3 * e
  rw [← e, hd.2.1 _ hT0, hy3]
  linear_combination (-(d _ x2 * y2)) * e1 - (d _ x1 * y1) * e2

end GlobalTheory.DlogCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
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

namespace GlobalTheory.LocReg

theorem charZero_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y), CharZero k := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ
  have : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  exact (algebraMap k (ChartRing k m d)).charZero_iff (RingHom.injective _) |>.2 this

end GlobalTheory.LocReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmul
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem exists_isLie_add_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE l
  exact lie_surj_mod_p p O E hE G d c l

end GlobalTheory.QLog
end

