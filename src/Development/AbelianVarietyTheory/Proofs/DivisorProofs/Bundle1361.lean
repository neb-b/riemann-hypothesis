module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaScaledNe

theorem normAtPlace_le_norm {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (y : mixedEmbedding.mixedSpace F) : mixedEmbedding.normAtPlace w y ≤ ‖y‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
    exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

theorem one_le_norm_mixedEmbedding {F : Type} [Field F] [NumberField F] {y : 𝓞 F} (hy : y ≠ 0) :
    1 ≤ ‖mixedEmbedding F (y : F)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ z : InfinitePlace F, z (y : F) < 1 := fun z => by
    have := normAtPlace_le_norm z (mixedEmbedding F (y : F))
    rw [mixedEmbedding.normAtPlace_apply] at this
    exact this.trans_lt h
  let w : InfinitePlace F := Classical.arbitrary _
  have := InfinitePlace.one_le_of_lt_one (w := w) hy (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr this)

theorem exists_int_of_mem_scaledInt {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0)
    {ξ : κ → F} (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a)
    (i : κ) : ∃ y : 𝓞 F, ξ i = a * (y : F) := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
    have h1 := h i v
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀] at h1
    rw [Valuation.map_mul, map_inv₀]
    have e1 : Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (ξ i)) = v.valuation F (ξ i) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ i)
    rw [e1, e2] at h1
    exact h1
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
  refine ⟨y, ?_⟩
  have hy' : (y : F) = a⁻¹ * ξ i := hy
  rw [hy', mul_inv_cancel_left₀ ha]

theorem exists_thetaSum_scaledInt_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  intro F _ _ κ _ a ha
  let V := κ → mixedEmbedding.mixedSpace F
  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc
  set ε : ℝ := 1 / (‖c‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  let b : ContDiffBump (0 : V) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  refine ⟨f, ?_⟩
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) with hg
  have hzero : ∀ ξ : κ → F, ξ ≠ 0 → pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    rw [pureA_algebraMap]
    by_cases hm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a
    · refine mul_eq_zero_of_left ?_ _
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
        by_contra h; push_neg at h; exact hξ (funext h)
      obtain ⟨y, hy⟩ := exists_int_of_mem_scaledInt ha hm i
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hi (by simpa using hy)
      have hn1 := one_le_norm_mixedEmbedding hy0
      have e : mixedEmbedding F (y : F) = c * mixedEmbedding F (ξ i) := by
        rw [hc, ← map_mul, hy, inv_mul_cancel_left₀ ha]
      have h2 : ‖mixedEmbedding F (ξ i)‖ ≤ ‖(fun j => mixedEmbedding F (ξ j) : V)‖ :=
        norm_le_pi_norm (fun j => mixedEmbedding F (ξ j)) i
      have h3 : 1 ≤ ‖c‖ * ‖(fun j => mixedEmbedding F (ξ j) : V)‖ := by
        rw [e] at hn1
        exact hn1.trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
      rw [hf, b.zero_of_le_dist, Complex.ofReal_zero]
      show ε ≤ dist (fun j => mixedEmbedding F (ξ j) : V) 0
      rw [dist_zero_right, hε, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg c, norm_nonneg (fun j => mixedEmbedding F (ξ j) : V)]
    · refine mul_eq_zero_of_right _ ?_
      rw [hg]
      exact Set.indicator_of_notMem hm _
  have h0 : pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 1 := by
    rw [pureA_algebraMap]
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    have hm : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a := by
      have e : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0 := by
        funext i; exact map_zero _
      rw [e]; exact zero_mem _
    rw [hx, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε0).le), hg,
      Set.indicator_of_mem hm]
    simp
  show (∑' ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ≠ 0
  rw [tsum_eq_single 0 hzero, h0]
  exact one_ne_zero

end GlobalTheory.ThetaScaledNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeight

open GlobalTheory.JointHarm

theorem detPlus_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detP ε (diagonal d) = ∏ a, if ε a then d a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then d a else 1 := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detP, e, det_diagonal]

theorem detM_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detM ε (diagonal d) = ∏ a, if ε a then 1 else d a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then 1 else d a := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detM, e, det_diagonal]

theorem fact_diagonal {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) (d : D.what₂.Tau → Fin m → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    fact ε x₁ x₂ x₃ (fun τ => diagonal (d τ)) (fun _ => 1) (delta p q ap am : PolF D m n) =
      (∏ τ, ∏ a, d τ a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) + x₁ τ else -(am τ (a - p τ) : ℤ) + x₂ τ)) •
        (delta p q ap am : PolF D m n) := by
  have h := DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (fun τ => diagonal (d τ)) (fun _ => 1)
    (fun τ => ⟨by
      rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
      exact (Finset.prod_ne_zero_iff.2 fun a _ => hd τ a).isUnit, by
      simp [Formalism.REAL.Jm, diagonal_mul_diagonal, mul_comm]⟩)
    (fun τ a b h => by
      obtain rfl : a = b := by
        by_contra e
        exact h (diagonal_apply_ne _ e)
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩)
    (fun τ => ⟨isUnit_one, fun a b h => Matrix.one_apply_ne h.ne⟩)
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, h, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [detPlus_diagonal, detM_diagonal, det_one, _root_.one_zpow, mul_one, Matrix.one_apply_eq, Finset.prod_const_one,
    diagonal_apply_eq, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hε]
  by_cases ha : (a : ℕ) < p τ <;> simp [ha, zpow_add₀ (hd τ a), mul_comm]

theorem pure_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem conj_mem {D : D7} {T : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel T S) (τ : D.what₂.Tau)
    {k : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
  have h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
        M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

end GlobalTheory.AdTh.MinorWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameAbelianPartTorsionFrame
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors.FrameTors

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem formEq_of_eq {X Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (h : ∀ i, ε i = ε' i) : FormEq φ ε φ ε' := fun _ _ _ =>
  Finset.prod_congr rfl fun i _ => by rw [h i]

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_lam {N : ℕ} {g o : GtPtF D F} (hg : GtPtF.IsNsmul N g o) (ho : o.IsZero)
    (w : Frm D F 1 g.b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)) (hκ : Normd κ) :
    ∃ c : F, ∀ z J, Good D.P.L z J → (val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J).val = cst F z c := by
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hg).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D F).left = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio D.P.isLB
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w (N ^ 2)) (LB.pullGen D.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ hκ.1 _))
    (LB.oneGen D.P.L) (oneGen_isGen' _) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0,
        Finset.univ_eq_empty, Finset.prod_empty, Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
      generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.P.A)) = a
      generalize h (Over.Hom.left g.b) = b
      group)
  refine ⟨c, fun z J hJ => ?_⟩
  have := hc _ (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_mul hJ, TWM.val_powGen, val_pull hJ, val_one, Units.val_one, _root_.mul_one] at this
  rw [Category.id_comp (Over.Hom.left g.b)] at this
  exact this

end GlobalTheory.Poinc.Tors.FrameTors

namespace GlobalTheory.Poinc.Tors.FrameTors

theorem frame_tors : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), NormW U.toUnifPre w₀ ρ → ∀ N : ℕ, 1 ≤ N → ∀ (g o : GtPtF D.toPre F), GtPtF.IsNsmul N g o → o.IsZero → ∀ (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → LiesOver U.toUnifPre w₀ g w x fr → IsTorsFrame A ρ N x fr → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ ρ hN N hN1 g o hgo ho w x fr hw hlies htors κ hκ
  obtain ⟨lam, hlam⟩ := exists_lam hgo ho w hw κ hκ
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hgo).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.toPre.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := rfl
  have key : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk'1 : 1 ≤ k * N ^ 2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega)))
    obtain ⟨t, c, hc0, htc⟩ := GlobalTheory.T.exists_lineBundlePower_section_nonzero_at_origin hL R A F ρ hN.2.1 k hk
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 N
    have hsm : Function.Injective fun χ : D.toPre.X => N • χ := fun a b h => by
      have h' : (N : ℤ) • a = (N : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 (by omega)) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen N E.aG hEG
    obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![((k * N ^ 2 : ℕ) : ℤ), -(k : ℤ)])
      (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring) (GeneratorPullback.powGen _ _ _ β₀ k)
      (powGen_isGen _ _ _ _ hβ₀ k)
    obtain ⟨-, CT2⟩ := coef_twistPull hL R I hI D A G hG U F E hinj (k * N ^ 2) k hk1 hk'1 ⟨β, hβ⟩
    rw [hEB] at CT2
    obtain ⟨α', hα', hα'n, hpm⟩ := PullMul.pull_mul_value R A F ρ hN.2.1 N k (k * N ^ 2) rfl x fr htors
      (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _) (by rw [MonObj.comp_pow, Category.comp_id])
    obtain ⟨t', htw, htv⟩ := hpm t c htc
    obtain ⟨e₁, he₁⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk1 w₀ hN.1
    obtain ⟨e₂, he₂⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk'1 w₀ hN.1
    have hs : U.ExpandsF F k w₀ t (e₁ t) := (he₁ t _).2 rfl
    have hs' : U.ExpandsF F (k * N ^ 2) w₀ t' (e₂ t') := (he₂ t' _).2 rfl
    obtain ⟨wk, hwk, hwkv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g.b)
      (ε' := DegPre.lineε (k * N ^ 2))
      (formEq_of_eq fun i => by fin_cases i <;> simp [DegPre.lineε]) (GeneratorPullback.powGen _ _ _ w (k * N ^ 2))
      (powGen_isGen _ _ _ _ hw _)
    have hκ'e : ∃ κ' : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (k * N ^ 2) k), κ'.IsGen ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
          val κ' r z J = val (GeneratorPullback.powGen _ _ _ κ k) r z J :=
      exists_gen D.toPre.P.isLB (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring)
        (GeneratorPullback.powGen _ _ _ κ k) (powGen_isGen _ _ _ _ hκ.1 _)
    obtain ⟨κ', hκ'g, hκ'v⟩ := hκ'e
    have hκ' : Normd κ' := ⟨hκ'g, corr_of_val D.toPre.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_one, hκ'v _ _ y J hJ, TWM.val_powGen]
      have a := val_corr hJ hκ.2 (𝟙 _)
      rw [val_pull hJ, val_one] at a
      rw [a, one_pow]⟩

    obtain ⟨ω, hω, hωv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F o.b) (ε' := DegPre.lineε k)
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0, hb,
          Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
        generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.toPre.P.A)) = a
        generalize h (Over.Hom.left g.b) = b
        group)
      (LB.mulGen _ _ _ _ _ wk (LB.pullGen _ _ _ κ' g.b.left))
      (mulGen_isGen _ _ _ _ _ _ _ hwk (pullGen_isGen _ _ _ _ hκ'g _))
    have hωm : ∀ z J, Good D.toPre.P.L z J →
        val wk (𝟙 _) z J * val κ' g.b.left z J = val ω (𝟙 _) z J := fun z J hJ => by
      have a := hωv _ (𝟙 (TF (R := R) F).left) z J hJ
      rw [val_mul hJ, val_pull hJ, Category.id_comp (Over.Hom.left g.b)] at a
      exact a.symm
    obtain ⟨q₁, q₂⟩ := CT2 w₀ ρ hN (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _)
      (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α' hα' hα'n t t' (e₁ t) (e₂ t') hs hs' htw κ' hκ' g o
      ((hEact F g o).2 hgo) wk ω hwk hω hωm
    obtain ⟨w1, hw1⟩ := (CoefBasic.coef_basic R D.toPre F k o).2.1 hb
    have hωl : ∀ z J, Good D.toPre.P.L z J → (val ω (𝟙 _) z J).val = cst F z (lam ^ k) := fun z J hJ => by
      rw [← hωm z J hJ, hwkv _ _ z J hJ, TWM.val_powGen, hκ'v _ _ z J hJ, TWM.val_powGen, pow_mul', ← mul_pow,
        Units.val_pow_eq_pow_val, hlam z J hJ, CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]
    have hcoef : ∀ χ, coef (e₁ t) o ω χ = lam ^ k * coef (e₁ t) o w1 χ := fun χ =>
      CoefBasic.coef_eq fun z J hJ => by
        have a := CoefBasic.isCoef_coef o hw1.1 χ (e₁ t) z J hJ
        rw [hw1.2 z J hJ, Units.val_one, _root_.mul_one] at a
        rw [hωl z J hJ]
        simp only [CoefBasic.cst_eq, map_mul] at a ⊢
        rw [_root_.mul_assoc, a]
        ring
    have hsum1 : SumF I F (coef (e₂ t') g wk) c := hlies (k * N ^ 2) hk'1 wk
      (fun z J hJ => by rw [hwkv _ _ z J hJ, TWM.val_powGen]) hwk t' (e₂ t') c hs' htv
    have hsum0 : SumF I F (coef (e₁ t) o w1) c :=
      (sumF_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN k t (e₁ t) hs o w1 ho hw1 c htc
    have hre := ((GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₂ t') g wk) (coef (e₂ t') g wk) c c).2.2
      D.toPre.X E.h hinj (fun β hβ => q₂ β hβ)).2 hsum1
    have e3 : (coef (e₂ t') g wk ∘ E.h) =
        fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ := funext fun χ => by
      simp only [Function.comp_apply, q₁, hcoef]; ring
    rw [e3] at hre
    have hsc := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₁ t) o w1) (coef (e₁ t) o w1) c c).2.1
      hsum0 hsum0 (lam ^ k - 1)
    have huniq := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X
      (fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ) (coef (e₁ t) o w1) c
      ((lam ^ k - 1) * c + c)).1 hre hsc
    have h0 : (lam ^ k - 1) * c = 0 := by linear_combination -huniq
    rcases mul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hc0
  have h4 := key 4 le_rfl
  have h5 := key 5 (by norm_num)
  have hl : lam = 1 := by
    have h0 : lam ≠ 0 := by rintro rfl; norm_num at h4
    calc lam = lam ^ 5 / lam ^ 4 := by field_simp
    _ = 1 := by rw [h4, h5]; norm_num
  intro z J hJ
  apply Units.ext
  rw [hlam z J hJ, hl, Units.val_one, CoefBasic.cst_eq, map_one]

end GlobalTheory.Poinc.Tors.FrameTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
section
noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def ech (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

def sch {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : Y → ℂ) : Y → ℂ :=
  fun x => ech (β x b + β a b / 2) * f (x + a)

variable (F : Type) [Field F] [NumberField F]

def arch {κ : Type} (v : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (v i)

def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def liftA (ξ : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ)

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}

def lagSet (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ u ∈ iso0 (F := F) n H', At (evI F) u ∧ ∃ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evI F) z ∧
    arch F (M₁.co.e z).1 = 0 ∧
    l = (arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1,
      arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2)}

end GlobalTheory.ArchSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadical
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.UnipMem

open GlobalTheory.LeviPlane Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.UnipMem
end
end

