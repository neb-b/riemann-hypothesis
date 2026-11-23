module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValue
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DenValue

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem dh_mem_adjoin (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : MRing ι) :
    TiePrimes.dh y c f ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_le_subring (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (A : Subring Ω)
    (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩)) : x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hr j.1 j.2
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem A r
  | add x y _ _ hx hy => exact A.add_mem hx hy
  | mul x y _ _ hx hy => exact A.mul_mem hx hy

theorem hasVal_ratio (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (z ⟨k, i⟩ / z ⟨k, c k⟩) := by
  classical
  unfold Small.HasVal
  refine ⟨Pi.single k 1, Pi.single k 1, MvPolynomial.X ⟨k, i⟩, MvPolynomial.X ⟨k, c k⟩,
    TiePrimes.homog_X _, TiePrimes.homog_X _, fun k' => by simp, ?_, ?_, ?_⟩
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hyc k)]
  · rw [MvPolynomial.aeval_X]
    exact hzc k
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hzc k)]

theorem hasVal_dh (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {h : MRing ι}
    {d : K → ℕ} (hh : IsMultiHomog h d) :
    Small.HasVal y 0 (TiePrimes.dh y c h) z (aeval z h / aeval z (TiePrimes.cMon c d)) := by
  have hc0 : aeval z (TiePrimes.cMon c d) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  unfold Small.HasVal
  refine ⟨d, d, h, TiePrimes.cMon c d, hh, TiePrimes.homog_cMon c d, fun k => by simp, ?_, hc0, ?_⟩
  · rw [TiePrimes.aeval_eq_dh_mul y c hyc hh, TiePrimes.aeval_eq_dh_mul y c hyc (TiePrimes.homog_cMon c d),
      TiePrimes.dh_cMon y c hyc, one_mul]
  · exact (div_mul_cancel₀ _ hc0).symm

private theorem hasVal_eq_of_hasVal_of_le {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {s : Ω} {w w' : 𝕜}
    (h1 : Small.HasVal y 0 s z w) (h2 : Small.HasVal y 0 s z w') : w = w' := by
  have hz' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ mCoordIdeal y, aeval z f = 0 := hz
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzw'⟩ := h2
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hdeq' : dg' = dh' := funext fun k => by
    have := hd' k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hm1 := TiePrimes.homog_mul hg hh'
  have hm2 := TiePrimes.homog_mul hg' hh
  rw [hdeq', ← hdeq, add_comm] at hm2
  have hneg := TiePrimes.homog_mul (TiePrimes.homog_C (K := K) (J := ι) (-1)) hm2
  rw [zero_add] at hneg
  have hF := TiePrimes.homog_add hm1 hneg
  have hFy : aeval y (g * h' + MvPolynomial.C (-1) * (g' * h)) = 0 := by
    simp only [map_add (f := _), map_mul, hy, hy', MvPolynomial.aeval_C, map_neg, map_one]
    ring
  have hFz := hz'.2 _ ((TiePrimes.mem_coord_iff y hF).2 hFy)
  simp only [map_add (f := _), map_mul, hzw, hzw', MvPolynomial.aeval_C, map_neg, map_one] at hFz
  have hprod : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination hFz
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 (mul_ne_zero hz0 hz0')

theorem value_and_denominator : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  intro K _ ι _ Ω _ y 𝕜 _ z A ev hz hval c hzc hyc hr
  refine ⟨fun k i => hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hr k i⟩) (hasVal_ratio y z c hzc hyc k i), ?_⟩
  intro a
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := hval a
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hbA : TiePrimes.dh y c h ∈ A := adjoin_le_subring y c A hr (dh_mem_adjoin y c h)
  have hc0 : aeval z (TiePrimes.cMon c dh) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  refine ⟨⟨_, hbA⟩, ?_, dh_mem_adjoin y c h, ?_⟩
  · rw [hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hbA⟩) (hasVal_dh y z c hzc hyc hh)]
    exact div_ne_zero hz0 hc0
  · have hab : (a : Ω) * TiePrimes.dh y c h = TiePrimes.dh y c g := by
      have e1 := TiePrimes.aeval_eq_dh_mul y c hyc hg
      have e2 := TiePrimes.aeval_eq_dh_mul y c hyc hh
      rw [hdeq] at e1
      have hP : ∏ k, y ⟨k, c k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
      apply mul_right_cancel₀ hP
      rw [mul_assoc, ← e2, ← e1, hy]
    show (a : Ω) * TiePrimes.dh y c h ∈ _
    rw [hab]
    exact dh_mem_adjoin y c g

end GlobalTheory.CompanionTheory.Ar.DenValue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

section Helpers

attribute [local instance] Over.cartesianMonoidalCategory


open ReciprocityTheory.ChartRestriction.G.Out in
theorem exists_root_through {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V), Finite {x : Over.mk t ⟶ G // x ^ n = 1})
    (O C : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (c : Sp O ⟶ G.left) (K : Type) [Field K] (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (y : Sp K ⟶ G.left)
    (hy : y ≫ (mulA G n).left = r ≫ c) :
    ∃ c' : Sp O ⟶ G.left, c' ≫ (mulA G n).left = c ∧
      c' (IsLocalRing.closedPoint O) = y (IsLocalRing.closedPoint K) := by
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulA G n).left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (mulA G n).left := IsSeparated.of_comp _ G.hom
  have : LocallyQuasiFinite (mulA G n).left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [GlobalTheory.IntDiv.comp_mulA]
      exact h K t
  have : Flat (mulA G n).left :=
    GlobalTheory.flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.IntDiv.flat_fibre G _ _ _) (GlobalTheory.IntDiv.flat_fibre G _ _ _)
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c)
    (pullback.lift y r hy (IsLocalRing.closedPoint K))
    ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y r hy)).trans hr)
  refine ⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs], ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ hs').trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_fst y r hy))))

theorem exists_torsion_point_through {R V O C K : Type} [CommRing R] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] [Field K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (n : ℕ)
    (hA : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1})
    (α : R →+* V) (ρV : V →+* O) (ρ : R →+* O) (hρ : ρV.comp α = ρ) (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (yG : Over.mk (r ≫ spMap ρ) ⟶ G)
    (hyN : yG ^ n = 1) :
    ∃ y : Over.mk (spMap ρ) ⟶ G, y ^ n = 1 ∧
      y.left (IsLocalRing.closedPoint O) = yG.left (IsLocalRing.closedPoint K) := by
  let j : Sp V ⟶ Sp R := spMap α
  have hjρ : spMap ρV ≫ j = spMap ρ := by
    rw [← hρ]
    simp only [j, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hGV : IsSemiAbelian ((Over.pullback j).obj G) := IsSemiAbelian.pullback j G hG
  have := hGV.comm
  have := hGV.smooth
  have := hGV.separated
  have := hGV.quasiCompact
  have := hGV.geomConnected
  have hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V),
      Finite {x : Over.mk t ⟶ ((Over.pullback j).obj G) // x ^ n = 1} := by
    intro K _ _ t
    obtain ⟨E⟩ := hGV.fibres K t
    have := (IsSemiAbelian.pullback t ((Over.pullback j).obj G) hGV).comm
    exact GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
      (GlobalTheory.TorsionLift.ptsEquiv t ((Over.pullback j).obj G) (𝟙_ _) t (by simp)) n
      (hA K ((Over.pullback t).obj ((Over.pullback j).obj G)) ⟨E⟩)
  let s : Sp K ⟶ Sp V := r ≫ spMap ρV
  have hs : s ≫ j = r ≫ spMap ρ := by simp only [s, Category.assoc, hjρ]
  let e₀ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk s) (r ≫ spMap ρ) hs
  obtain ⟨yV, hyV₀⟩ := e₀.surjective yG
  have hyV : yV ^ n = 1 := by
    apply e₀.injective
    rw [map_pow, hyV₀, hyN, map_one]
  let rr : Over.mk s ⟶ Over.mk (spMap ρV) := Over.homMk r rfl
  let c : Sp O ⟶ ((Over.pullback j).obj G).left := (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)).left
  have hc : yV.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n).left = r ≫ c := by
    have h1 : yV ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n =
        rr ≫ (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)) := by
      rw [GlobalTheory.IntDiv.comp_mulA, hyV, MonObj.comp_one]
    exact congrArg (fun q => q.left) h1
  obtain ⟨c', hc', hcl⟩ := exists_root_through ((Over.pullback j).obj G) n hfin O C c K r hr yV.left hc
  have hcw : c' ≫ ((Over.pullback j).obj G).hom = spMap ρV := by
    have h1 := Over.w (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n)
    have h2 : c ≫ ((Over.pullback j).obj G).hom = spMap ρV :=
      Over.w (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G))
    rw [← h1, ← Category.assoc, hc', h2]
  let c₂ : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G) := Over.homMk c' hcw
  have hc₂ : c₂ ^ n = 1 := by
    rw [← GlobalTheory.IntDiv.comp_mulA]
    exact Over.OverMorphism.ext hc'
  let e₁ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk (spMap ρV)) (spMap ρ) hjρ
  refine ⟨e₁ c₂, by rw [← map_pow, hc₂, map_one], ?_⟩
  have h1 : (e₁ c₂).left = c' ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  have h2 : (e₀ yV).left = yV.left ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  rw [h1, ← hyV₀, h2]
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  rw [hcl]
  exact (Scheme.Hom.comp_apply _ _ _).symm

end Helpers

theorem ker_ne_bot_of_finite (L : Type) [Field L] [NumberField L] (k : Type) [Field k] [Finite k] (a : 𝓞 L →+* k) :
    RingHom.ker a ≠ ⊥ := by
  intro h
  have hinj : Function.Injective a := (RingHom.injective_iff_ker_eq_bot a).2 h
  have : Infinite (𝓞 L) := Infinite.of_injective (Nat.cast : ℕ → 𝓞 L) Nat.cast_injective
  exact not_finite_iff_infinite.2 this (Finite.of_injective a hinj)

theorem exists_valuationSubring_of_ne_top (L : Type) [Field L] [NumberField L] (p : Ideal (𝓞 L)) (hp : p ≠ ⊤) :
    ∃ (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O),
      (∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L)) ∧
      ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O := by
  let f : 𝓞 L →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap (𝓞 L) L)
  have hf : Function.Injective f :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (RingOfIntegers.coe_injective)
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hI : p.map f.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : f.range) ∈ p.map f.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h1
    have : x = 1 := hf (by simpa [Subtype.ext_iff] using hx1)
    exact hp ((Ideal.eq_top_iff_one _).2 (this ▸ hx))
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (p.map f.rangeRestrict) hI
  refine ⟨B, f.codRestrict B fun x => hAB ⟨x, rfl⟩, fun a => rfl, fun a ha => ?_⟩
  have h1 : f a ∈ B.nonunits := hB ⟨f.rangeRestrict a, Ideal.mem_map_of_mem _ ha, rfl⟩
  exact ValuationSubring.coe_mem_nonunits_iff.1 h1

theorem exists_lift_atPrime {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (p : Ideal R) [p.IsMaximal]
    (ρ : R →+* O) (hρ : ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρV : Localization.AtPrime p →+* O, ρV.comp (algebraMap R (Localization.AtPrime p)) = ρ := by
  have hu : ∀ y : p.primeCompl, IsUnit (ρ y) := by
    intro y
    by_contra hy
    have h1 : p ≤ (IsLocalRing.maximalIdeal O).comap ρ := hρ
    have h2 : (IsLocalRing.maximalIdeal O).comap ρ ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    have h3 := (Ideal.IsMaximal.eq_of_le ‹_› h2 h1).symm
    have h4 : (y : R) ∈ (IsLocalRing.maximalIdeal O).comap ρ := by
      simpa [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] using hy
    exact y.2 (h3 ▸ h4)
  exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩

theorem exists_factor_of_finite {R k K : Type} [CommRing R] [Field k] [Finite k] [Field K] [IsAlgClosed K]
    (a : R →+* k) (b : R →+* K) [(RingHom.ker a).IsMaximal] (h : RingHom.ker a ≤ RingHom.ker b) :
    ∃ φ : k →+* K, φ.comp a = b := by
  letI : Field (R ⧸ RingHom.ker a) := Ideal.Quotient.field _
  let a' : (R ⧸ RingHom.ker a) →+* k := Ideal.Quotient.lift _ a fun x hx => hx
  let b' : (R ⧸ RingHom.ker a) →+* K := Ideal.Quotient.lift _ b fun x hx => h hx
  letI := a'.toAlgebra
  letI := b'.toAlgebra
  have : Module.Finite (R ⧸ RingHom.ker a) k := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (R ⧸ RingHom.ker a) k := Algebra.IsAlgebraic.of_finite _ _
  let φ : k →ₐ[R ⧸ RingHom.ker a] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, RingHom.ext fun x => ?_⟩
  have h1 : φ (a' (Ideal.Quotient.mk _ x)) = b' (Ideal.Quotient.mk _ x) := φ.commutes _
  simp only [a', b', Ideal.Quotient.lift_mk] at h1
  exact h1

theorem exists_geometric_closedPoint {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (ρ : R →+* O) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (b : R →+* K) (r : Sp K ⟶ Sp O), r ≫ spMap ρ = spMap b ∧
      (∀ x, ρ x ∈ IsLocalRing.maximalIdeal O → b x = 0) ∧
      r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let g : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have : IsLocalHom g := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (IsLocalRing.residue O x) := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have : g x = 0 := by simp [g, h]
      exact hx.ne_zero this
    exact (isUnit_map_iff (IsLocalRing.residue O) x).1 h1
  refine ⟨K, inferInstance, inferInstance, g.comp ρ, spMap g, ?_, fun x hx => ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have h1 : IsLocalRing.residue O (ρ x) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hx
    simp [g, h1]
  · exact IsLocalRing.comap_closedPoint g

theorem exists_torsion_point_reducing_to : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  intro L _ _ G _ _ hG w hw
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let π : Sp (𝓞 L) ⟶ Sp ℤ := spMap (Int.castRingHom (𝓞 L))
  have : LocallyOfFiniteType π := by
    have h1 : (algebraMap ℤ (𝓞 L)).Finite := RingHom.finite_algebraMap.2 inferInstance
    rw [algebraMap_int_eq] at h1
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 h1.finiteType
  obtain ⟨hA, hB⟩ := GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.1
  obtain ⟨N, hN1, hN⟩ := hB (Sp (𝓞 L)) π G w hw
  have : Finite (G.left.residueField w) :=
    (GlobalTheory.jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (G.left.fromSpecResidueField w ≫ G.hom)
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 L →+* G.left.residueField w, CommRingCat.ofHom a = ψ := ⟨ψ.hom, rfl⟩
  have hp0 : RingHom.ker a ≠ ⊥ := ker_ne_bot_of_finite L _ a
  have hpp : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  have hpm : (RingHom.ker a).IsMaximal := hpp.isMaximal hp0
  obtain ⟨O, ρ, hρL, hρp⟩ := exists_valuationSubring_of_ne_top L (RingHom.ker a) hpp.ne_top
  obtain ⟨ρV, hρV⟩ := exists_lift_atPrime (RingHom.ker a) ρ hρp
  have hV : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker a)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hp0 _
  obtain ⟨K, _, _, b, r, hb, hbk, hr⟩ := exists_geometric_closedPoint ρ
  obtain ⟨φ, hφ⟩ := exists_factor_of_finite a b (fun x hx => hbk x (hρp x hx))
  have hy₀ : (Spec.map (CommRingCat.ofHom φ) ≫ G.left.fromSpecResidueField w) ≫ G.hom = r ≫ spMap ρ := by
    rw [hb, Category.assoc, ← hψ, ← hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let yG : Over.mk (r ≫ spMap ρ) ⟶ G := Over.homMk _ hy₀
  have hyl : ∀ z, yG.left z = w := fun z =>
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  have hyN : yG ^ N = 1 := hN K _ yG
    (Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, hyl _⟩, by rintro _ ⟨z, rfl⟩; exact hyl z⟩)
  obtain ⟨y, hy, hyw⟩ := exists_torsion_point_through (C := AlgebraicClosure L) G hG N
    (fun K _ _ G _ _ hE => hA K G hE N hN1) (algebraMap (𝓞 L) (Localization.AtPrime (RingHom.ker a))) ρV ρ hρV r hr yG hyN
  exact ⟨N, O, ρ, y, hN1, hy, hyw.trans (hyl _), hρL⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RankBound

theorem rank_bound_of_points_of_order_two :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) :=
  @PositivityTheory.Xgn.two_torsion_rank_bound

end GlobalTheory.CompanionTheory.Ar.RankBound
end

