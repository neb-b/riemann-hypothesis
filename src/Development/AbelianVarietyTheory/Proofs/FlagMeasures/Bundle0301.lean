module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCoeff
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab
open scoped InnerProductSpace Classical

noncomputable section

namespace GlobalTheory.LevelIdem

section Conv

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Conv

section Alg

variable {Q : Type} [Group Q] [Fintype Q]

end Alg

section Lev

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem vol_ne_zero (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] {g : ℕ} (hg : 1 ≤ g) :
    μf (I.Kg g) ≠ ⊤ ∧ ((μf (I.Kg g)).toReal : ℂ) ≠ 0 := by
  obtain ⟨-, -, -, hK, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hopen, ⟨S, hS⟩, -⟩ := hKg g hg
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hfin : μf (I.Kg g) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have h1 : (1 : I.Gf) ∈ I.Kg g := by rw [← hS]; exact S.one_mem
  have hpos : μf (I.Kg g) ≠ 0 := (hopen.measure_pos μf ⟨1, h1⟩).ne'
  exact ⟨hfin, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos hfin).ne'⟩

theorem mem_fibre {s : I.Gf} (hs : s ∈ I.Kset) (x : I.Gf) :
    s⁻¹ * x ∈ I.Kg g ↔ x ∈ I.Kset ∧ ρ.toFun x = ρ.toFun s := by
  have hmul : ∀ a ∈ I.Kset, ∀ b ∈ I.Kset, a * b ∈ I.Kset := fun a ha b hb =>
    (mem_Ksub I _).1 ((Ksub I).mul_mem ((mem_Ksub I a).2 ha) ((mem_Ksub I b).2 hb))
  have hinv : ∀ a ∈ I.Kset, a⁻¹ ∈ I.Kset := fun a ha =>
    (mem_Ksub I _).1 ((Ksub I).inv_mem ((mem_Ksub I a).2 ha))
  constructor
  · intro h
    have hk : s⁻¹ * x ∈ I.Kset := (show s⁻¹ * x ∈ I.Kset ∧ _ from h).1
    have hx : x ∈ I.Kset := by simpa using hmul s hs _ hk
    refine ⟨hx, ?_⟩
    have hm := ρ.map_mul s hs _ hk
    rwa [mul_inv_cancel_left, (ρ.ker _ hk).2 h, mul_one] at hm
  · rintro ⟨hx, hxs⟩
    have hk := hmul _ (hinv s hs) x hx
    refine (ρ.ker _ hk).1 ?_
    rw [ρ.map_mul _ (hinv s hs) x hx, ρ.map_inv hs, hxs, inv_mul_cancel]

theorem integral_lift [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q)
    (s : Q → I.Gf) (hs : ∀ q, s q ∈ I.Kset ∧ ρ.toFun (s q) = q) (φ : I.Gf → ℂ)
    (hφ : ∀ x, ∀ k ∈ I.Kg g, φ (x * k) = φ x) :
    ∫ x, ρ.lift μf a x * φ x ∂μf = ∑ q, a.coeff q * φ (s q) := by
  classical
  obtain ⟨hfin, hvol⟩ := vol_ne_zero I μf hg
  have hopen := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 g hg).1
  have hSm : ∀ q, MeasurableSet ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g) := fun q =>
    (hopen.preimage (continuous_const_mul _)).measurableSet
  have hpt : ∀ x, ρ.lift μf a x * φ x = ∑ q, ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g).indicator
      (fun _ => a.coeff q * φ (s q) / ((μf (I.Kg g)).toReal : ℂ)) x := by
    intro x
    by_cases hx : x ∈ I.Kset
    · rw [ρ.lift_of_mem μf a hx, Finset.sum_eq_single (ρ.toFun x)]
      · have hmem : (s (ρ.toFun x))⁻¹ * x ∈ I.Kg g :=
          (mem_fibre ρ (hs _).1 x).2 ⟨hx, (hs _).2.symm⟩
        rw [Set.indicator_of_mem (show x ∈ (fun y => (s (ρ.toFun x))⁻¹ * y) ⁻¹' I.Kg g from hmem)]
        have hφx : φ x = φ (s (ρ.toFun x)) := by
          have h' := hφ (s (ρ.toFun x)) _ hmem
          rwa [mul_inv_cancel_left] at h'
        rw [hφx]
        ring
      · intro q _ hq
        refine Set.indicator_of_notMem (fun hmem => hq ?_) _
        exact ((((mem_fibre ρ (hs q).1 x).1 hmem).2).trans (hs q).2).symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ρ.lift_of_notMem μf a hx, zero_mul]
      refine (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm
      exact ((mem_fibre ρ (hs q).1 x).1 hmem).1
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hSm q), measureReal_def, measure_preimage_mul, Complex.real_smul]
    field_simp
  · intro q _
    refine (integrable_indicator_iff (hSm q)).2 (integrableOn_const ?_)
    rw [measure_preimage_mul]
    exact hfin

end Lev

end GlobalTheory.LevelIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IdemProj

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ]

theorem integral_inv_of_support (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (f : G → ℂ) (hf : Continuous f) (hs : ∀ x, f x ≠ 0 → x ∈ K) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have hKcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  have hu : Continuous ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    (IsClopen.continuous_indicator ⟨hKcl, ho⟩ continuous_const)
  set u : G → ℂ := (K : Set G).indicator fun _ => (1 : ℂ) with hu_def

  set Φ : G × G → ℂ := fun z => f z.2⁻¹ * u (z.1 * z.2) with hΦ_def
  have hΦc : Continuous Φ := (hf.comp continuous_snd.inv).mul (hu.comp continuous_mul)
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (hc.prod hc) fun z hz => ?_
    by_cases h2 : f z.2⁻¹ = 0
    · simp [hΦ_def, h2]
    · have hb : z.2 ∈ K := by simpa using K.inv_mem (hs _ h2)
      have ha : z.1 ∉ K := fun ha => hz ⟨ha, hb⟩
      have : z.1 * z.2 ∉ K := fun h => ha ((K.mul_mem_cancel_right hb).1 h)
      simp [hΦ_def, hu_def, this]
  have hΦi : Integrable Φ (μ.prod μ) := hΦc.integrable_of_hasCompactSupport hΦs
  have hT := measurePreserving_prod_inv_mul_swap μ μ
  have hΦTi : Integrable (fun z : G × G => Φ (z.2, z.2⁻¹ * z.1)) (μ.prod μ) :=
    (hT.integrable_comp hΦc.aestronglyMeasurable).2 hΦi
  have hswap : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = ∫ z, Φ z ∂(μ.prod μ) := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable]
    rw [hT.map_eq]; exact hΦc.aestronglyMeasurable
  set c : ℂ := ∫ a, u a ∂μ with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def, hu_def, integral_indicator_const _ hKcl.measurableSet]
    have hpos : 0 < μ (K : Set G) := ho.measure_pos μ ⟨1, K.one_mem⟩
    have hfin : μ (K : Set G) ≠ ⊤ := hc.measure_lt_top.ne
    have : μ.real (K : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin⟩
    simpa [Complex.real_smul] using this
  have hleft : ∫ z, Φ z ∂(μ.prod μ) = (∫ b, f b⁻¹ ∂μ) * c := by
    rw [integral_prod_symm Φ hΦi, ← integral_mul_const]
    congr 1; funext b
    simp only [hΦ_def]
    rw [integral_const_mul]
    by_cases h2 : f b⁻¹ = 0
    · simp [h2]
    · have hb : b ∈ K := by simpa using K.inv_mem (hs _ h2)
      congr 1
      rw [hc_def]
      congr 1; funext a
      classical
      simp only [hu_def, Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_right hb]
  have hright : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = (∫ x, f x ∂μ) * c := by
    rw [integral_prod _ hΦTi]
    simp only [hΦ_def, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hc_def, ← integral_const_mul]
    congr 1; funext x
    rw [integral_mul_const, integral_mul_left_eq_self (fun y => f y) x⁻¹]
  have := hswap
  rw [hleft, hright] at this
  exact (mul_right_cancel₀ hcne this).symm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem inner_rep (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (x y : H) : ⟪x, π g y⟫_ℂ = ⟪π g⁻¹ x, y⟫_ℂ := by
  have hback : π g (π g⁻¹ x) = x := by
    have := congrArg (fun S : H →L[ℂ] H => S x) (hm g g⁻¹)
    simp only [mul_inv_cancel, h1, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply] at this
    exact this.symm
  let U : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hn g⟩
  calc ⟪x, π g y⟫_ℂ = ⟪U (π g⁻¹ x), U y⟫_ℂ := by
        show ⟪x, π g y⟫_ℂ = ⟪π g (π g⁻¹ x), π g y⟫_ℂ
        rw [hback]
    _ = ⟪π g⁻¹ x, y⟫_ℂ := U.inner_map_map _ _

theorem op_idem (K : Subgroup G) (hc : IsCompact (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hee : ∀ x, ∫ y, e y * e (y⁻¹ * x) ∂μ = e x) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) : T.comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, hT x (T y)]
  have step : ∀ g, ⟪x, π g (T y)⟫_ℂ = ∫ h, e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ ∂μ := by
    intro g
    have shift := integral_mul_left_eq_self (μ := μ) (fun h => e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) g
    simp only [inv_mul_cancel_left] at shift
    rw [inner_rep π h1 hm hn g, hT, ← shift]
    congr 1; funext h
    rw [hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn g]
  have hint : Integrable (Function.uncurry fun g h => e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (he.comp continuous_fst).mul ((he.comp (continuous_fst.inv.mul continuous_snd)).mul
        (continuous_const.inner ((hπ y).comp continuous_snd)))
    · refine HasCompactSupport.intro (hc.prod hc) ?_
      rintro ⟨g, h⟩ hgh
      simp only [Function.uncurry_apply_pair]
      by_cases hg : g ∈ K
      · have hh : h ∉ K := fun hh => hgh ⟨hg, hh⟩
        have h0 : e (g⁻¹ * h) = 0 := by
          by_contra hne
          exact hh (by simpa using K.mul_mem hg (hs _ hne))
        simp [h0]
      · have h0 : e g = 0 := by
          by_contra hne
          exact hg (hs _ hne)
        simp [h0]
  calc ∫ g, e g * ⟪x, π g (T y)⟫_ℂ ∂μ
      = ∫ g, ∫ h, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := by
        congr 1; funext g
        rw [step g, integral_const_mul]
    _ = ∫ h, ∫ g, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ h, e h * ⟪x, π h y⟫_ℂ ∂μ := by
        congr 1; funext h
        simp_rw [← mul_assoc]
        rw [integral_mul_const, hee]
    _ = ⟪x, T y⟫_ℂ := (hT x y).symm

theorem op_symm (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hst : ∀ x, e x⁻¹ = star (e x)) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hF : Continuous fun g => e g * ⟪x, π g y⟫_ℂ := he.mul (continuous_const.inner (hπ y))
  have hFs : ∀ g, e g * ⟪x, π g y⟫_ℂ ≠ 0 → g ∈ K := fun g hg => hs g (left_ne_zero_of_mul hg)
  conv_lhs => rw [← inner_conj_symm]
  rw [hT y x, ← integral_conj, hT x y, ← integral_inv_of_support μ K hc ho _ hF hFs]
  congr 1; funext g
  show (starRingEnd ℂ) (e g * ⟪y, π g x⟫_ℂ) = e g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ
  rw [map_mul, inner_conj_symm, starRingEnd_apply, ← hst g, inner_rep π h1 hm hn g⁻¹, inv_inv]


omit [T2Space G] in
theorem op_fixed (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (e : G → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (k : G) (hk : ∀ h, e (k * h) = e h) :
    (π k).comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, inner_rep π h1 hm hn k, hT, hT]
  have key : ∀ g, e g * ⟪π k⁻¹ x, π g y⟫_ℂ = e (k * g) * ⟪x, π (k * g) y⟫_ℂ := by
    intro g
    rw [hk g, hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn k]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun h => e h * ⟪x, π h y⟫_ℂ) k


omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem eventually_left_inv (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (e : G → ℂ) (he : IsLocallyConstant e) (hs : ∀ x, e x ≠ 0 → x ∈ K) :
    ∀ᶠ k in nhds (1 : G), ∀ h, e (k * h) = e h := by
  have hloc : ∀ h ∈ (K : Set G), ∀ᶠ z : G × G in nhds ((1 : G), h), e (z.1 * z.2) = e z.2 := by
    intro h _
    have hfib : ∀ᶠ y in nhds h, e y = e h := he.eventually_eq h
    have ht : Filter.Tendsto (fun z : G × G => z.1 * z.2) (nhds ((1 : G), h)) (nhds h) := by
      simpa using (continuous_mul (M := G)).tendsto ((1 : G), h)
    have ha := ht.eventually hfib
    have hb : ∀ᶠ z : G × G in nhds ((1 : G), h), e z.2 = e h :=
      (continuous_snd.tendsto ((1 : G), h)).eventually hfib
    filter_upwards [ha, hb] with z hz1 hz2
    rw [hz1, hz2]
  have hK : ∀ᶠ k in nhds (1 : G), ∀ h ∈ (K : Set G), e (k * h) = e h :=
    hc.eventually_forall_of_forall_eventually hloc
  have hmem : ∀ᶠ k in nhds (1 : G), k ∈ (K : Set G) := ho.mem_nhds K.one_mem
  filter_upwards [hK, hmem] with k hk hkK h
  by_cases hh : h ∈ (K : Set G)
  · exact hk h hh
  · have e1 : e h = 0 := by
      by_contra hne
      exact hh (hs h hne)
    have e2 : e (k * h) = 0 := by
      by_contra hne
      exact hh (by simpa using K.mul_mem (K.inv_mem hkK) (hs _ hne))
    rw [e1, e2]

end General

theorem re_orth_proj : ∀ B : RowsAut, IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧ ∃ g : ℕ, 1 ≤ g ∧ ∀ k ∈ B.I.Kg g, (B.R (1, k)).comp B.Re = B.Re := by
  intro B
  obtain ⟨hT2, -, hSC, hKc, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hR1, hRm, hRn, hRc, -⟩ := _root_.GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨hlc, hconv, hst, -, hsupp, -, -⟩ := B.e_adm
  obtain ⟨-, hRe⟩ := B.Re_spec
  have hKc' : IsCompact (K : Set B.I.Gf) := by rw [hK]; exact hKc
  have hKo' : IsOpen (K : Set B.I.Gf) := by rw [hK]; exact hKo
  have hs : ∀ x, B.e x ≠ 0 → x ∈ K := by
    intro x hx
    rw [← SetLike.mem_coe, hK]
    exact hsupp x hx
  have h1 : B.R (1, 1) = 1 := hR1
  have hm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b
    rw [← hRm, Prod.mk_mul_mk, one_mul]
  have hn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => hRn _ v
  have hπ : ∀ v, Continuous fun g : B.I.Gf => B.R (1, g) v :=
    fun v => (hRc v).comp (continuous_const.prodMk continuous_id)
  have he : Continuous B.e := hlc.continuous
  have hee : ∀ x, ∫ y, B.e y * B.e (y⁻¹ * x) ∂B.μf = B.e x := fun x => congrFun hconv x
  have hT : ∀ x y : B.I.L2 B.μf B.fund,
      ⟪x, B.Re y⟫_ℂ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf := hRe
  refine ⟨?_, ?_, ?_⟩
  · show B.Re.comp B.Re = B.Re ∧ (∀ x y, ⟪B.Re x, y⟫_ℂ = ⟪x, B.Re y⟫_ℂ) ∧ _
    exact ⟨op_idem B.μf K hKc' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hee B.Re hT,
      fun x y => op_symm B.μf K hKc' hKo' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hst B.Re hT x y,
      rfl⟩
  · intro g
    refine ContinuousLinearMap.ext fun y => ?_
    refine ext_inner_left ℂ fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT x,
      inner_rep B.R hR1 hRm hRn (g, 1) x, hT]
    congr 1; funext k
    have hcomm : ((1 : B.I.Ginf), k) * (g, 1) = (g, 1) * ((1 : B.I.Ginf), k) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [← inner_rep B.R hR1 hRm hRn (g, 1), ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.mul_apply, ← hRm, ← hRm, hcomm]
  · obtain ⟨g, hg1, hgsub⟩ := B.I.topf_basis _ (eventually_left_inv K hKc' hKo' B.e hlc hs)
    exact ⟨g, hg1, fun k hk => op_fixed B.μf (fun g => B.R (1, g)) h1 hm hn B.e B.Re hT k
      (hgsub hk)⟩

end GlobalTheory.IdemProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletion
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeIndicator

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_int_generators (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ (k : ℕ) (x : Fin k → Fin n → E), (∀ j, x j ∈ L) ∧
      ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • x j := by
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨m, by simpa using (congrArg Subtype.val hm).symm⟩

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem L hL w

theorem latLoc_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsOpen (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective
  obtain ⟨k, x, hxL, hx⟩ := exists_int_generators L hL.fg
  let f : (Fin k → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ fun j i => (1 : Fv F v) ⊗ₜ[F] x j i
  have hfa : ∀ a i, f a i = ∑ j, a j ⊗ₜ[F] x j i := fun a i => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  have hm : ∀ (a : Fv F v) (m : Fin k → ℤ),
      f (fun j => m j • a) = fun i => a ⊗ₜ[F] (∑ j, m j • x j) i := fun a m => by
    funext i
    rw [hfa]
    simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
  have hf : Function.Surjective f := by
    have h1 : ∀ (a : Fv F v) (w : Fin n → E), (fun i => a ⊗ₜ[F] w i) ∈ LinearMap.range f := by
      intro a w
      obtain ⟨N, hN, h⟩ := exists_int_smul_mem L hL w
      obtain ⟨m, e⟩ := hx _ h
      refine ⟨fun j => m j • ((N : Fv F v)⁻¹ * a), ?_⟩
      rw [hm, ← e]
      funext i
      rw [Pi.smul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), one_mul]
    intro y
    rw [← LinearMap.mem_range, ← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    generalize y i = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [Pi.single_add]; exact add_mem hp hq
    | tmul a e =>
      convert h1 a (Pi.single i e) using 1
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  have hfo : IsOpenMap f := IsModuleTopology.isOpenMap_of_surjective (φ := f) hf
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have himg : (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) =
      f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    constructor
    · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ f '' Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · intro a ha w hw
        obtain ⟨m, rfl⟩ := hx w hw
        exact ⟨fun j => m j • a, fun j _ => zsmul_mem ha _, hm a m⟩
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun j _ => add_mem (s := v.adicCompletionIntegers F) (ha j trivial) (hb j trivial),
          map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun j _ => neg_mem (s := v.adicCompletionIntegers F) (ha j trivial), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      have : f a = ∑ j, fun i => a j ⊗ₜ[F] x j i := funext fun i => by rw [hfa, Finset.sum_apply]
      rw [this]
      exact sum_mem (S := GlobalTheory.AdelicU.latLoc F L v) fun j _ =>
        GlobalTheory.AdelicU.tmul_mem_latLoc (ha j trivial) (hxL j)
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hc).image hfc,
    hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩

theorem isSB_indicator_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  intro F E _ _ _ _ _ n L hL v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨hc, ho⟩ := latLoc_compact_open L hL v
  have hcl : IsClosed (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) :=
    (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.isClosed_of_isOpen ho
  have e : {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} =
      Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp [Fin.forall_fin_one]
  rw [e]
  have h1 := isCompact_univ_pi fun _ : Fin 1 => hc
  have h2 := isOpen_set_pi Set.finite_univ fun (_ : Fin 1) _ => ho
  have h3 := isClosed_set_pi (i := Set.univ) fun (_ : Fin 1) _ => hcl
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_, ?_⟩
  · by_cases hX : X ∈ Set.pi Set.univ fun _ : Fin 1 =>
        (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))
    · exact ⟨_, h2, hX, fun Y hY => by rw [Set.indicator_of_mem hY, Set.indicator_of_mem hX]; rfl⟩
    · exact ⟨_, h3.isOpen_compl, hX, fun Y hY => by
        rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro' h1 h3 fun X hX => Set.indicator_of_notMem hX _

end GlobalTheory.LatticeIndicator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_low_types : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdPart.product_moment_first | exact GlobalTheory.MomProdPart.product_moment_first | (intros; apply GlobalTheory.MomProdPart.product_moment_first <;> assumption)
end

