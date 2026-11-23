module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionPullbackSourceLevelOne
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.EqZeroOfPnorm
section
noncomputable section

namespace GlobalTheory.NetNormExamples

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)

theorem pnorm_le_supN (U : Unf Xo c σ r) (la) {P : FDSec U.X} (hP : P ∈ holSub U.X la) (p : FPt U.X) :
    (U.X p.1).pnorm (la p.1) (P p.1) p.2 ≤ supN U.X la P := by
  unfold supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem eq_zero_of_pnorm (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h0 : X.pnorm la P x = 0) : P x = 0 := by
  have hne : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i e => by
    have := (hx τ).2 i
    rw [e] at this; simp at this
  unfold Data.pnorm at h0
  refine norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _

end GlobalTheory.NetNormExamples
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullEveryLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_pull_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N))
    (h : IsPullByEnd U f k N s s') :
    ∃ c : ∀ y : (pullback G.hom (jK V) : Scheme.{0}), ((pullback G.hom (jK V) ⟶ G.left) → U.LG.L.ι) →
        (pullback G.hom (jK V) : Scheme.{0}).presheaf.stalk y,
      (∀ y J, Good U.LG.L y J → sval s' (𝟙 _) y J = sval s (endK f) y J * c y J) ∧
      ∀ (m : ℕ) (t : U.SecK (m * k)), ∃ t' : U.SecK (m * k * N), IsPullByEnd U f (m * k) N t t' ∧
        ∀ y J, Good U.LG.L y J → sval t' (𝟙 _) y J = sval t (endK f) y J * c y J ^ m := by
  obtain ⟨u, hu, hc, hr⟩ := h
  have hL := U.LG.isLB
  refine ⟨fun y J => (val u (𝟙 _) y J).val, fun y J hJ => ?_, fun m t => ?_⟩
  · have := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 hr _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · obtain ⟨v, hv, hvv⟩ := exists_gen hL (φ' := ![gK, endK f ≫ gK])
      (ε' := ![((m * k * N : ℕ) : ℤ), -((m * k : ℕ) : ℤ)])
      (fun W _ h => by
        simp [Fin.prod_univ_two, _root_.mul_assoc])
      (GeneratorPullback.powGen U.LG.L _ _ u m) (powGen_isGen_of_isGen u hu m)
    obtain ⟨t', ht'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => ((m * k * N : ℕ) : ℤ))
      (fun W _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
        rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec t (endK f) v hv)
    have key : ∀ y J, Good U.LG.L y J →
        sval t' (𝟙 _) y J = sval t (𝟙 _ ≫ endK f) y J * (val v (𝟙 _) y J).val := fun y J hJ => by
      rw [ht' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ]
    refine ⟨t', ⟨v, hv, ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 key⟩, fun y J hJ => ?_⟩
    · refine corr_of_val hL fun z J hJ => ?_
      have e := val_corr hJ hc (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e
      rw [val_pull hJ, val_pull hJ, val_pow, hvv _ _ z J hJ, val_pow, e, ← pow_mul]
      congr 1
      ring
    · rw [key y J hJ, Category.id_comp, hvv _ _ y J hJ, val_pow, Units.val_pow_eq_pow_val]

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Geo.Tor.Host E}
  {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}

theorem expands_pull_every_level (hLaws : Laws) (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ} (hk : 1 ≤ k)
    (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (hs : P.U.Expands k s F)
    (s' : P.U.SecK (k * N)) (hs' : IsPullByEnd P.U (t.act.act a) k N s s') :
    letI := H.starRing
    ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧
      PullAl P.D (FractionRing V) P.oD a k N F F' := by
  letI := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨F', hF'⟩ := exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
    (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  obtain ⟨s'', hs'', -⟩ := (P.U.expand (k * N) (Nat.mul_pos hk hN0)).2 F'
  obtain ⟨c, hc, hpow⟩ := exists_pull_pow P.U _ k N s s' hs'
  have hint := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ _ _ _
    P.U.toUnifPre).2
  have e : s'' = s' := by
    refine SecOps.sec_ext (sec_ext_val P.U.LG.isLB fun y J hJ => ?_)
    have hm : ∀ m : ℕ, 4 ≤ m → sval s'' (𝟙 _) y J ^ m = sval s' (𝟙 _) y J ^ m := fun m hm => by
      have hmk : 4 ≤ m * k := le_trans hm (Nat.le_mul_of_pos_right m hk)
      obtain ⟨τ, hτ⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ _ _ _ P.U.toUnifPre (m * k) hmk _
        (endK (t.act.act a)) y J hJ
      obtain ⟨τ', hτ', hv⟩ := hpow m τ
      obtain ⟨T, hT, -⟩ := (P.U.expand (m * k) (by omega)).1 τ
      obtain ⟨T', hT', hTT⟩ := GlobalTheory.PullExpansion.expands_pull_of_four_le hLaws V E H t P a N hN hN0 (m * k) hmk
        τ T hT τ' hτ'
      have g := GlobalTheory.GenericCross.main hLaws V E H t P a N hN hN0 k s F s'' F' hs hs'' hF' (m * k) τ T τ' T' hT hT'
        hTT m 1 (by ring) y J hJ
      rw [pow_one, pow_one, hv y J hJ] at g
      refine hτ.mul_right_cancel (g.trans ?_)
      rw [hc y J hJ]
      ring
    exact GlobalTheory.PullLevelOne.eq_of_pow_four_five (hm 4 le_rfl) (hm 5 (by norm_num))
  exact ⟨F', e ▸ hs'', hF'⟩

end

end GlobalTheory.PullEveryLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FormAtOfClause
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaValuationTest

open Formalism.MainNotions Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : 0 ≤ X.phiC la y := by
  unfold WeightAlgebra.PJ.phiC
  split_ifs
  · refine mul_nonneg (Nat.cast_nonneg _) (Real.sInf_nonneg ?_)
    rintro x ⟨l, -, hl, rfl⟩
    by_cases h0 : (P.loc X.dat (WeightAlgebra.resCh la)).beS (X.pt66 la y) = 0
    · rw [h0, map_zero]
    · refine (hl _ (fun a => ?_) h0).le
      obtain ⟨ι, _, b, hb⟩ := (P.loc X.dat (WeightAlgebra.resCh la)).be_posDef (X.pt66 la y)
      show 0 ≤ (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a
      by_cases hc : (fun i => ((b.repr a i : ℤ) : ℝ)) = 0
      · have : a = 0 := by
          apply b.repr.injective
          ext i
          have := congrFun hc i
          simpa using this
        simp [this]
      · have h1 := hb _ hc
        have h2 : (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a =
            ∑ i, ∑ k, ((b.repr a i : ℤ) : ℝ) * ((b.repr a k : ℤ) : ℝ) *
              (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (b i) (b k) := by
          conv_lhs => rw [← b.sum_repr a]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        rw [h2]; exact h1.le
  · exact le_rfl

theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
end
end

