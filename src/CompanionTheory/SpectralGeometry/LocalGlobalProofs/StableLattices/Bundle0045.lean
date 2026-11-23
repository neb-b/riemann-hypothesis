module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.Bundle0001
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskyCosets.Imports
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BaseFamilyAlt
section
namespace GlobalTheory.CompanionTheory.BaseFamily

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

theorem baseFam : CompanionTheory.RgExh.Dec.J.BaseFam := by
  intro n ε H _ _ _ σ D E hK hσ
  refine ⟨fun ξ u Y hY g hg => ?_, fun ξ => ?_⟩
  · have h := _root_.GlobalTheory.CompanionTheory.RightRule.rightRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n)) u Y hY g hg
    have e : actM E Y u = ∑ a, ∑ b, Y a b • E a b u := by
      simp [actM, LinearMap.sum_apply]
    show HasDerivAt _ (baseCoef σ D (ξ : H) (actM E Y u) g) 0
    rw [e]
    exact h
  · obtain ⟨l, hl⟩ := _root_.GlobalTheory.CompanionTheory.PathCoef.leftRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n))
    refine ⟨fun c d => (l c d).mapDomain Prod.fst, fun a b u g hg => ?_⟩
    have h := hl a b u g hg
    refine h.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    congr 1
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
    rfl

end GlobalTheory.CompanionTheory.BaseFamily
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem ev_fa {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    ev E (fa n Y) = qdet E (Y + ((n : ℂ) - 1) / 2) := by
  unfold fa
  rw [map_qdet]
  congr 1
  funext p q
  simp [ev]

theorem evL_fb {n M : ℕ} (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n)
    (hlev : ∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    evL lev E (fb d h Y) = (List.ofFn fun i : Fin M =>
      qdet (fun p q : Fin (d i) => E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
        (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)).prod := by
  unfold fb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_qdet, shift, add_sub_assoc]
  congr 1
  funext p q
  simp [evL, hlev]

theorem span_apply_sum {n : ℕ} (lev : Fin n → ℕ) (hm : Monotone lev) {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (r : Fin n → Fin n → Prop) (hr : ∀ p q, r p q → lev p < lev q)
    {y : Module.End ℂ V}
    (hy : y ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin n) (w : Module.End ℂ V), r p q ∧ y = E p q * w})
    (x : V) : ∃ w : Pos n → V, y x = ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    have hl := hr p q hpq
    have hlt : p < q := by
      by_contra hc
      exact absurd (hm (not_lt.mp hc)) (not_le.mpr hl)
    classical
    refine ⟨Pi.single (⟨(p, q), hlt⟩ : Pos n) (w x), ?_⟩
    rw [Finset.sum_eq_single (⟨(p, q), hlt⟩ : Pos n)]
    · simp [inU, hl]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [LinearMap.add_apply, hu, hv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  | smul c a _ ha =>
    obtain ⟨u, hu⟩ := ha
    refine ⟨c • u, ?_⟩
    rw [LinearMap.smul_apply, hu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem co_hyp : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  intro n M lev d h Y hm hlev V _ _ E hE
  rw [ev_fa, evL_fb lev d h hlev]
  refine ⟨fun i _ => (Formalism.REAL.qDetCentral (Module.End ℂ V) n E hE _ i.1.1 i.1.2).symm, fun x => ?_⟩
  have hlevb : ∀ p : Fin n, lev p = ((blk (stdBlocks d h) p : Fin M) : ℕ) := by
    intro p
    have := hlev ((stdBlocks d h).symm p).1 ((stdBlocks d h).symm p).2
    simpa [blk] using this
  have hc := GlobalTheory.CapHC.qdet_blocks_congr (Module.End ℂ V) d h E hE Y
  obtain ⟨w, hw⟩ := span_apply_sum lev hm E (fun p q => blk (stdBlocks d h) p < blk (stdBlocks d h) q)
    (fun p q hpq => by rw [hlevb p, hlevb q]; exact hpq) hc x
  exact ⟨w, by rw [← hw, LinearMap.sub_apply]⟩

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ConjQdet
section
namespace GlobalTheory.CompanionTheory.RgConjQdet

open Finset

theorem conj_single_apply {n : ℕ} (U Ui : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (U * Matrix.single p q 1 * Ui : Matrix (Fin n) (Fin n) ℂ) a b = U a p * Ui q b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem conjQdet : CompanionTheory.RgExh.Dec.J.ConjQdet := by
  intro n X U Ui hUUi hUiU u
  have hE : ∀ (x : ℂ) (p q : Fin n),
      Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) x p q =
        ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d := by
    intro x p q
    have hd : ∑ c, ∑ d, (U c p * Ui q d) • (if c = d then algebraMap ℂ (Module.End ℂ X.V) x else 0)
        = if p = q then algebraMap ℂ (Module.End ℂ X.V) x else 0 := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_smul]
      have hc : ∑ c, U c p * Ui q c = (Ui * U) q p := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      rw [hc, hUiU, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · rw [if_neg (Ne.symm hpq), if_neg hpq, zero_smul]
    simp only [Formalism.REAL.Tm, ReciprocityTheory.ChartRestriction.DS.actM, conj_single_apply, Matrix.transpose_apply,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    rw [hd]
  have hT : Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) =
      fun x p q => ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d :=
    funext fun x => funext fun p => funext fun q => hE x p q
  rw [PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)), hT,
    PI.UnitaryGroupMassFormula.DSIC.qF_row, PI.UnitaryGroupMassFormula.DSIC.qF_col X.E X.gl, smul_smul, Matrix.det_transpose,
    Matrix.det_transpose, ← Matrix.det_mul, hUUi, Matrix.det_one, one_smul]

end GlobalTheory.CompanionTheory.RgConjQdet
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CuspidalTwistInjectiveImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacter
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem exists_character_of_smul_ne_zero :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W]
      [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 →
      ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  intro R _ _ _ W _ _ _ _ t ht
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R W t)
  have hmemJ : ∀ x : R, x ∈ J ↔ x • t = 0 := fun x => by
    simp [J, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ J := h ▸ Submodule.mem_top
    exact ht (by simpa using (hmemJ 1).1 h1)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℂ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)
  haveI : Module.Finite ℂ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ m)
  have bij : Function.Bijective (algebraMap ℂ (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m)) bij
  refine ⟨(e.symm : (R ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m), fun r c h => ?_⟩
  have hmem : r - algebraMap ℂ R c ∈ J := by
    rw [hmemJ, sub_smul, algebraMap_smul, h, sub_self]
  have hq : Ideal.Quotient.mkₐ ℂ m r = algebraMap ℂ (R ⧸ m) c := by
    have h0 : Ideal.Quotient.mk m (r - algebraMap ℂ R c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hJm hmem)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have he : e c = algebraMap ℂ (R ⧸ m) c := rfl
  show e.symm (Ideal.Quotient.mkₐ ℂ m r) = c
  rw [hq, ← he, AlgEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.RgCOBlock
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.QuotAction

theorem descends (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C) (hZ : ∀ k, ∀ z ∈ Z, l k z ∈ Z) (hB : ∀ k, ∀ z ∈ B, l k z ∈ B) :
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  let lZ : L → Module.End ℂ Z := fun k => (l k).restrict (hZ k)
  have hBl : ∀ k, B.comap Z.subtype ≤ (B.comap Z.subtype).comap (lZ k) := by
    intro k z hz
    show Z.subtype (lZ k z) ∈ B
    exact hB k z hz
  let lQ : L → Module.End ℂ (Z ⧸ B.comap Z.subtype) :=
    fun k => (B.comap Z.subtype).mapQ (B.comap Z.subtype) (lZ k) (hBl k)
  have hP : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ l y (z : C) = ((FreeAlgebra.lift ℂ lZ y z : Z) : C) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb]
  have hQ : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ lQ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk (FreeAlgebra.lift ℂ lZ y z) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add (f := _), LinearMap.add_apply, Submodule.Quotient.mk_add, ha, hb]
  refine ⟨FreeAlgebra.lift ℂ lQ, fun y z => ⟨by rw [hP y z]; exact (FreeAlgebra.lift ℂ lZ y z).2, ?_⟩⟩
  rw [hQ y z]
  congr 1
  exact Subtype.ext (hP y z).symm

end GlobalTheory.CompanionTheory.RgCOBlock.QuotAction
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GelfandKazhdanContragredientImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeight
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.TopU

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    ann i x B = if i ∈ B then 0 else CompanionTheory.D.LK.sg i B • x (insert i B) := rfl

theorem cre_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i x B = if i ∈ B then CompanionTheory.D.LK.sg i B • x (B.erase i) else 0 := rfl

theorem sg_erase (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i (B.erase i) = CompanionTheory.D.LK.sg i B := by
  unfold CompanionTheory.D.LK.sg
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sg_sq (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i B * CompanionTheory.D.LK.sg i B = 1 := by
  unfold CompanionTheory.D.LK.sg; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem cre_ann (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i (ann i x) B = if i ∈ B then x B else 0 := by
  rw [cre_app]
  split_ifs with h
  · rw [ann_app, if_neg (notMem_erase i B), insert_erase h, sg_erase, smul_smul, sg_sq, one_smul]
  · rfl

theorem adC_self (a : Fin n) (i k : Pos n) :
    adC a a i k = if k = i then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0 := by
  unfold adC
  have e1 : (a = i.1.1 ∧ k.1 = (a, i.1.2)) ↔ (k = i ∧ i.1.1 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext h1 rfl)), h1.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨h.symm, Prod.ext h rfl⟩
  have e2 : (i.1.2 = a ∧ k.1 = (i.1.1, a)) ↔ (k = i ∧ i.1.2 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext rfl h1.symm)), h1⟩
    · rintro ⟨rfl, h⟩; exact ⟨h, Prod.ext rfl h⟩
  simp only [e1, e2]
  by_cases hk : k = i <;> simp [hk]

theorem adL_self_apply (a : Fin n) (x : Cn n V) (B : Finset (Pos n)) :
    adL a a x B = ∑ i : Pos n, (((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ)) •
      cre i (ann i x) B := by
  simp only [adL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply,
    adC_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem top_cycle_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  intro n ε lev V _ _ E γ u _ hu
  have memA : ∀ i : Pos n, i ∈ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := fun i => by simp [omU]
  refine ⟨?_, fun a => ?_⟩
  · funext B
    rw [CompanionTheory.D.LK.bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := CompanionTheory.D.LK.tri_ne h
        have e : insert i (insert j (B.erase k)) = omU ε lev := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci := (memA i).1 (e ▸ mem_insert_self _ _)
        have cj := (memA j).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have ck : k ∈ omU ε lev := (memA k).2
          ⟨by rw [t2, t3, ci.1, t1]; exact cj.1,
           by rw [t2, t3]; exact (ci.2.trans_eq (congrArg lev t1)).trans cj.2⟩
        rw [← e] at ck
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_app]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i B = omU ε lev
        · have hiA := (memA i).1 (e ▸ mem_insert_self i B)
          rw [e, Pi.single_eq_same, map_smul, hu.2 _ _ i.2 hiA.1, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext B
    show E a a ((Pi.single (omU ε lev) u : Cn n V) B) + adL a a (Pi.single (omU ε lev) u) B = _
    rw [adL_self_apply]
    simp only [cre_ann]
    by_cases e : B = omU ε lev
    · subst e
      rw [Pi.single_eq_same, hu.1 a, Pi.smul_apply, Pi.single_eq_same]
      have hs : ∀ i : Pos n, ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) •
          (if i ∈ omU ε lev then u else 0) =
          (if i ∈ omU ε lev then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0) • u := by
        intro i; split_ifs <;> simp
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_smul, ← add_smul]
      congr 1
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter, Finset.sum_sub_distrib, Finset.sum_boole,
        Finset.sum_boole]
      simp only [wt]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne e]

end GlobalTheory.CompanionTheory.RgCOBlock.TopU
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocalLanglandsOfIrreducibleAdmissibleImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.SumSz

theorem sum_sz_eq_card : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  intro n M lev h
  have key := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M)))
    (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  unfold sz
  congr 1

end GlobalTheory.CompanionTheory.RgCOBlock.SumSz
end

