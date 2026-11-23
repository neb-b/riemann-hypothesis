module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallCoeffFieldEmbeddingCompHostMap
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay

theorem growth_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF g
  obtain ⟨C, N, hC⟩ := hF g
  set I := ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν with hI
  refine ⟨|C| * ((a : ℝ) + 1) ^ N * I, N, fun y => ?_⟩
  have hint := (hk.2.2 N).const_mul (|C| * ((a : ℝ) + 1) ^ N * height y ^ N)
  have hb : ∀ x, ‖k x * F (g * infGL E a y * infGL E a (γ x))‖ ≤
      |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
    intro x
    rw [mul_assoc g, ← map_mul, norm_mul]
    have h1 := hC (y * γ x)
    have hm := GlobalTheory.HCF.ModGrowth.height_mul_le y (γ x)
    have hy := one_le_height y
    have hg := one_le_height (γ x)
    have hz := one_le_height (y * γ x)
    have e1 : height (y * γ x) ^ N ≤ (((a : ℝ) + 1) * (height y * height (γ x))) ^ N :=
      pow_le_pow_left₀ (by linarith) hm N
    have e2 : ‖F (g * infGL E a (y * γ x))‖ ≤ |C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg C)))
    calc ‖k x‖ * ‖F (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N)) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
      _ = |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
          rw [mul_pow, mul_pow]; ring
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, hI]
  ring

end GlobalTheory.MSpanDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastMemConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
open Formalism.L2.Host (embLL0)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TwistProduct

variable {D : D7}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

theorem chrEq_one_one : ChrEq (1 : (AE D)ˣ →* Circle) (1 : Formalism.L2.Host.HChar D.host.E) :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩

theorem natCast_mem_conj {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c, hc, e⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

theorem tameAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ)
    (v : Pl D.host.E) : χ.TameAt v := by
  by_cases hv : v ∈ t.Q
  · have hr := GlobalTheory.TwistResidue.isRes_of_chrEq D t ht χ hχ v hv
    refine GlobalTheory.TameConjPlace.tameAt_of_congr χ v fun a b ka kb hka hkb ha hab => ?_
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    have hma : (Ideal.Quotient.mk v.asIdeal a : kP v) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    have e1 := hr a ka (Units.mk0 _ hma) hka rfl
    have e2 := hr b kb (Units.mk0 _ hma) hkb (Ideal.Quotient.eq.mpr hab)
    rw [← e1, ← e2]
  · by_cases hc : ∃ P' ∈ t.Q, Formalism.IndefR.Lev.IsConjPl P' v
    · obtain ⟨P', hP', hPc⟩ := hc
      exact GlobalTheory.TameConjPlace.tameAt_conj D t ht χ hχ P' hP' v hPc
    · have hu := GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v hv hc
      intro x hx _
      exact hu x hx

theorem unrAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ) (pd : ℕ)
    (hpd : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (v : Pl D.host.E)
    (hv : ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) : χ.UnrAt v := by
  refine GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v (fun h => hv (hpd v h)) ?_
  rintro ⟨P', hP', hc⟩
  exact hv (natCast_mem_conj hc (hpd P' hP'))

theorem isTwist_mul : ∀ (D : D7) (t t' : Twist D Circle), t.Good → t'.Good → SplitSet (t.Q ∪ t'.Q) → Disjoint t.Q t'.Q →
    ∀ (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ), (∃ n : ℕ, 0 < n ∧ ∀ x, (t.chi * t'.chi) x ^ n = 1) →
    (∀ PP ∈ t.Q ∪ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, (((t.chi * t'.chi) x : Circle) : ℂ) ∈ σ.fieldRange) →
    ∃ δ : Formalism.L2.Host.HChar D.host.E, IsTwist pd σ δ (t.chi * t'.chi) := by
  intro D t t' ht ht' _ _ pd k _ σ hn hpd hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t.chi ht.isHeckeChar
  obtain ⟨χ', hχ'⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t'.chi ht'.isHeckeChar
  have hc : ChrEq (t.chi * t'.chi) (χ * χ') := GlobalTheory.TowerCharRead.chrEq_mul hχ hχ'
  have hpd1 : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_left _ h)
  have hpd2 : ∀ PP ∈ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_right _ h)
  refine ⟨χ * χ', hc, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn0, hnx⟩ := hn
    refine ⟨n, hn0, ?_⟩
    have hp := chrEq_pow hc n hn0
    have h1 : (t.chi * t'.chi) ^ n = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, hnx x, MonoidHom.one_apply]
    rw [h1] at hp
    exact GlobalTheory.ChrEqUnique.hchar_unique D 1 _ _ hp chrEq_one_one
  · exact _root_.GlobalTheory.TrivOnRead.trivOn_of_chrEq D _ _ hc fun a => by rw [MonoidHom.mul_apply, ht.real, ht'.real, one_mul]
  · intro v x hx hx1
    show χ.loc v x * χ'.loc v x = 1
    rw [tameAt_of_good t ht χ hχ v x hx hx1, tameAt_of_good t' ht' χ' hχ' v x hx hx1, one_mul]
  · intro v hv x hx
    show χ.loc v x * χ'.loc v x = 1
    rw [unrAt_of_good t ht χ hχ pd hpd1 v hv x hx, unrAt_of_good t' ht' χ' hχ' pd hpd2 v hv x hx, one_mul]
  · intro v _
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3 v
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (hval (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif v)))
    refine ⟨y, ?_⟩
    rw [hy, hc.2 v e he (Formalism.L2.Host.unif v) _ (Formalism.L2.JoinChr.locU_val hee _)]
    simp [Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val]

end GlobalTheory.TwistProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_le_one_of_mem_locBall_pts : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b), (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf y
  have h := nrm_le_one_of_mem_locBall YS fw iC b j hf y
  have he : fw.e j (cuspOf YS fw j f) = ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ :=
    Subtype.ext (e_cuspOf YS fw j f)
  rw [he] at h
  exact h

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLint
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPoleToc

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem eq_ofReal_norm {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.im = 0) : z = ((‖z‖ : ℝ) : ℂ) := by
  have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]

theorem rsPsi_self_eq (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  set u : Fin a → Cinf E := fun i => pInf E (y i)
  set w := g * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ u))⁻¹
  set s : ℝ := (GlobalTheory.ThetaPoisson.latt a J).indicator 1 ((fun i => pFin E (y i)) - η)
  have hs : (GlobalTheory.ThetaPoisson.latt a J).indicator (1 : (Fin a → Af E) → ℂ) ((fun i => pFin E (y i)) - η) = (s : ℂ) := by
    classical
    simp only [s]; rw [Set.indicator_apply, Set.indicator_apply]; split_ifs <;> simp
  have hs0 : 0 ≤ s := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hΦu : Φ u = (((Φ u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hΦ u).2])
  have e : GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((Complex.normSq (F w) * (Φ u).re * s : ℝ) : ℂ) := by
    simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf]
    rw [hs, Complex.mul_conj, hΦu]
    push_cast
    rfl
  refine eq_ofReal_norm ?_ ?_
  · rw [e, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ u).1) hs0
  · rw [e, Complex.ofReal_im]

theorem tsum_eq_toReal {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i = ((‖f i‖ : ℝ) : ℂ)) :
    ∑' i, f i = (((∑' i, ‖f i‖ₑ).toReal : ℝ) : ℂ) := by
  rw [ENNReal.tsum_toReal_eq fun _ => enorm_ne_top, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [toReal_enorm, ← hf i]

theorem thetaZ_eq_toReal (ℓ : Fin a) (F : GA E a → ℂ) (hF : Continuous F) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ) (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (x : ℝ)
    (hfin : ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤) :
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
                 ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
                 ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  set G : GA E a → ℝ≥0∞ := fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) with hG

  have hcont : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, Continuous fun g : GA E a => GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) := by
    intro ξ
    have h1 : Continuous fun g : GA E a =>
        (g, (fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g.val : Matrix (Fin a) (Fin a) (Ad E))) :=
      continuous_id.prodMk (continuous_const.matrix_vecMul Units.continuous_val)
    have h2 := GlobalTheory.RSTheta.continuous_rsPsi hF hF hΦc hΦs J η
    have h3 := h2.comp h1
    exact h3
  have hdet : Continuous fun g : GA E a => ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    have h : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
      continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
    exact h.rpow_const fun g => Or.inl (ideleModule E (GeneralLinearGroup.det g)).2.ne'
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (ENNReal.measurable_ofReal.comp hdet.measurable)
    exact (lowerSemicontinuous_tsum fun ξ => (hcont ξ).enorm.lowerSemicontinuous).measurable

  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
      ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) = (((G g).toReal : ℝ) : ℂ) := by
    intro g
    rw [tsum_eq_toReal _ fun ξ => rsPsi_self_eq ℓ F Φ hΦ J η g _, hG]
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (ideleModule E (GeneralLinearGroup.det g)).2.le x), Complex.ofReal_mul]
  have hae : ∀ᵐ g ∂μ.restrict 𝓕, G g < ⊤ := ae_lt_top hGm hfin
  calc GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = ∫ g in 𝓕, (((G g).toReal : ℝ) : ℂ) ∂μ := by
        rw [GlobalTheory.RSPole.thetaZ]; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ g in 𝓕, (G g).toReal ∂μ : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_toReal hGm.aemeasurable hae]

theorem thetaZ_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a ℓ π F _ hF Φ hΦc hΦs hΦ J η μ _ 𝓕 _ x hfin
  exact thetaZ_eq_toReal ℓ F hF Φ hΦc hΦs hΦ J η μ 𝓕 x hfin

end GlobalTheory.RSPoleToc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def CopyTw.cm (h : CopyTw D D' ι e) (j : Fin D.R.m) : Fin D'.R.m :=
  Fin.cast (congrArg Ranks.m h.gal.R) j

theorem CopyTw.cm_val (h : CopyTw D D' ι e) (j : Fin D.R.m) : ((h.cm j : Fin D'.R.m) : ℕ) = j := rfl

abbrev SameSetup (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop := SameData ρ ρ'

def RdRel (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b),
    HEq (rd' i' (h.cm j) b (h.fmCast hi ((j : ℕ) + 1) b f)) (rd i j b f)

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod

theorem relIndex_map_of_proj_left {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X)
    (φ P : X →+ X) (M : X →+ Y) (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0)
    (hMP : ∀ x, M (P x) = M x) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    (A.map φ).relIndex A = ((A.map M).map m).relIndex (A.map M) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := (A.map φ).map M) M A, ← AddSubgroup.inf_relIndex_right (A.map φ),
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨z, ⟨y, hy, rfl⟩, hzx⟩, hx⟩
  refine ⟨?_, hx⟩
  have h1 : P (φ y) = P x := by
    have := hK (φ y - x) (by rw [map_sub, hzx, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  have hy' : (x - P x) + P y ∈ A := add_mem (sub_mem hx (hPA x hx)) (hPA y hy)
  have hMy : M ((x - P x) + P y - y) = 0 := by
    rw [map_sub, map_add (f := _), map_sub, hMP, hMP]; abel
  have h2 : P ((x - P x) + P y) = P y := by
    have := hK _ hMy
    rwa [map_sub, sub_eq_zero] at this
  have h3 : P (φ ((x - P x) + P y)) = P (φ y) := by
    have := hK (φ ((x - P x) + P y) - φ y) (by rw [← map_sub, hM, hMy, map_zero])
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨(x - P x) + P y, hy', ?_⟩
  calc φ ((x - P x) + P y) = (φ ((x - P x) + P y) - P (φ ((x - P x) + P y))) + P (φ ((x - P x) + P y)) := by abel
    _ = ((x - P x) + P y - P ((x - P x) + P y)) + P (φ y) := by rw [hφ _ hy', h3]
    _ = x := by rw [h2, h1]; abel

end GlobalTheory.LocKerMod


set_option maxHeartbeats 1000000 in
open GlobalTheory.LFun in
theorem GlobalTheory.LocKerMod.latIndex_embV_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w →
    ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g := by
  intro D T v w h hi g
  let φ : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g)).mulVecLin.toAddMonoidHom
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun y i => singleAt D.host.F w 1 * y i) fun a b => funext fun i => mul_add _ _ _
  let M : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun y i => compAt D.host.F w (y i)) fun a b => funext fun i => map_add _ _ _
  let m : (Fin T.rank → w.adicCompletion D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    (locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (x : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) i,
      compAt D.host.F u (φ x i) = ((locMat D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _)
        (proj D.sp.cm.sig T.gram (u.under (𝓞 D.host.F)) (GlobalTheory.FinZeta.embV T v g))).1 *ᵥ
          fun j => compAt D.host.F u (x j)) i := by
    intro u x i
    rw [← finMat_map_compAt D.sp.cm.sig T.gram rfl]
    exact RingHom.map_mulVec (compAt D.host.F u) _ x i
  have hM : ∀ x, M (φ x) = m (M x) := by
    intro x
    funext i
    have := hcomp w x i
    subst h
    rw [proj_emb_self] at this
    exact this
  have hK : ∀ x, M x = 0 → P x = 0 := by
    intro x hx
    funext i
    have h0 : compAt D.host.F w (x i) = 0 := congrFun hx i
    show singleAt D.host.F w 1 * x i = 0
    rw [singleAt_mul, h0, mul_zero, singleAt_zero]
  have hMP : ∀ x, M (P x) = M x := by
    intro x
    funext i
    show compAt D.host.F w (singleAt D.host.F w 1 * x i) = compAt D.host.F w (x i)
    rw [map_mul, compAt_singleAt, one_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T := by
    intro a ha
    have e : P a = fun i => singleAt D.host.F w (compAt D.host.F w (a i)) := by
      funext i
      show singleAt D.host.F w 1 * a i = _
      rw [singleAt_mul, one_mul]
    rw [e]
    exact singleAt_mem_lamHat (compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha))
  have hφ : ∀ a ∈ Formalism.L2.NTheta.LamHat T, φ a - P (φ a) = a - P a := by
    intro a _
    funext i
    show φ a i - singleAt D.host.F w 1 * φ a i = a i - singleAt D.host.F w 1 * a i
    refine compAt_ext fun u => ?_
    by_cases e : u = w
    · subst e
      simp only [map_sub, map_mul, compAt_singleAt, one_mul, sub_self]
    · have hu : u.under (𝓞 D.host.F) ≠ v := fun hu => e ((InertChart.under_eq_iff hi u).1 hu)
      simp only [map_sub, map_mul, compAt_singleAt_ne e, zero_mul, sub_zero]
      rw [hcomp u a i, GlobalTheory.FinZeta.embV, proj_emb_ne _ _ hu, map_one, Units.val_one, Matrix.one_mulVec]
  have hLM : (Formalism.L2.NTheta.LamHat T).map M = (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup := by
    ext y
    rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      show (fun i => compAt D.host.F w (a i)) ∈ GlobalTheory.LFun.latAt w (frameLat T)
      exact compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha)
    · intro hy
      refine ⟨_, singleAt_mem_lamHat hy, ?_⟩
      funext i
      exact compAt_singleAt w (y i)
  unfold latIndex idxAt
  rw [relIndex_map_of_proj_left _ φ P M m hM hK hMP hPA hφ, hLM]
end
end

