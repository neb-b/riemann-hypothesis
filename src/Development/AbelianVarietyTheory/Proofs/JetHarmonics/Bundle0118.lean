module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PlacePartEigenLifts
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeries
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThetaQuot

def fac (d : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ) +
    (-(Real.pi : ℂ) * h1 d z y - (Real.pi : ℂ) / 2 * h1 d y y))

lemma fac_ne (d : ℕ) (y z : ℂ) : fac d y z ≠ 0 := Complex.exp_ne_zero _

lemma nonzeroIndexPlaces_adelicDataResized_eq (d : ℕ) (y : ℂ) (F : ℂ → ℂ) (z : ℂ) : W1 d y F z = fac d y z * F (z + y) := by
  simp only [W1, U1, fac, Complex.exp_add]; ring

lemma fac_mul (d : ℕ) (α : ℂ) (m : ℕ) (hm : (m : ℂ) = α * conj α) (y z : ℂ) :
    fac d (α * y) (α * z) = fac d y z ^ m := by
  simp only [fac]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [hm, ← Complex.mul_conj, ← Complex.mul_conj]
  simp only [h1, map_mul]
  ring

lemma not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h2 : (-1 : ℂ) = 2 * u + v * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    simp only [wK] at h
    linear_combination 2 * h
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have : (-1 : ℤ) = 2 * u := by
    have : (-1 : ℝ) = 2 * u := by simpa using hre
    exact_mod_cast this
  omega

lemma inOK_mul (d : ℕ) (hd : d % 4 = 3) {α β : ℂ} (ha : InOK d α) (hb : InOK d β) : InOK d (α * β) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨u', v', rfl⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp
  have hk' : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  have hw : wK d ^ 2 = wK d - k := by
    simp only [wK]
    linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4) * hs - (1 / 4) * hk'
  refine ⟨u * u' - k * v * v', u * v' + v * u' + v * v', ?_⟩
  push_cast
  linear_combination (v * v' : ℂ) * hw

lemma zero_of_pole {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (p : ℂ)
    (h : meromorphicOrderAt (fun z => F z / G z) p < 0) : G p = 0 := by
  by_contra hp
  have ha : AnalyticAt ℂ (fun z => F z / G z) p := (hF.analyticAt p).div (hG.analyticAt p) hp
  exact absurd ha.meromorphicOrderAt_nonneg (not_le.mpr h)

theorem theta_quot : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  intro d q _ M ω θ hd hd16 hsp hL hch hθ α m hα hα0 hm
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  have hd4 : d % 4 = 3 := by omega
  have hA : Differentiable ℂ (fun z => θ (α * z)) := hdiff.comp (differentiable_id.const_mul α)
  have hB : Differentiable ℂ (fun z => θ z ^ m) := hdiff.pow m
  have hper : ∀ l ∈ M.L.lattice, ∀ z, θ (α * z) = fac d l z ^ m * θ (α * (z + l)) ∧
      θ z ^ m = fac d l z ^ m * θ (z + l) ^ m := by
    intro l hl z
    have hl' := (hL l).1 hl
    constructor
    · have := congrFun (hW _ (inOK_mul d hd4 hα hl')) (α * z)
      rw [nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm] at this
      rw [← this, mul_add]
    · have := congrFun (hW _ hl') z
      rw [nonzeroIndexPlaces_adelicDataResized_eq] at this
      rw [← mul_pow, this]
  have hEε : Ell M.L (fun z => θ (α * z) / θ z ^ m) := by
    refine ⟨fun p => (hA.analyticAt p).meromorphicAt.div (hB.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (α * (z + l)) / θ (z + l) ^ m = θ (α * z) / θ z ^ m
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hEη : Ell M.L (fun z => θ z ^ m / θ (α * z)) := by
    refine ⟨fun p => (hB.analyticAt p).meromorphicAt.div (hA.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (z + l) ^ m / θ (α * (z + l)) = θ z ^ m / θ (α * z)
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hA0 : θ (α * 0) ≠ 0 := by simp [h0]
  have hB0 : θ 0 ^ m ≠ 0 := by simp [h0]
  have haε : AnalyticAt ℂ (fun z => θ (α * z) / θ z ^ m) 0 :=
    (hA.analyticAt 0).div (hB.analyticAt 0) hB0
  have haη : AnalyticAt ℂ (fun z => θ z ^ m / θ (α * z)) 0 :=
    (hB.analyticAt 0).div (hA.analyticAt 0) hA0
  have hns : ∀ β p : ℂ, InOK d β → β ≠ 0 → θ (β * p) = 0 → ¬ M.Small p := by
    intro β p hβ hβ0 hp hs
    have hp0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
    have := (_root_.GlobalTheory.MomOne.smallTors d q M ω hd hd16 hsp hL hch).2.2.2 p β 0 hβ hβ0 hp0
      (by simpa using hz _ hp) hs
    exact not_half d hd.pos this.2
  have hbε : Bdd (hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m)) := by
    refine _root_.GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell q M _ _ hch hEε haε fun p hp => ?_
    have := zero_of_pole hA hB p hp
    exact hns 1 p ⟨1, 0, by simp⟩ one_ne_zero (by simpa using (pow_eq_zero_iff'.1 this).1)
  have hbη : Bdd (hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z))) := by
    refine _root_.GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell q M _ _ hch hEη haη fun p hp => ?_
    exact hns α p hα hα0 (zero_of_pole hB hA p hp)
  obtain ⟨hh1, hh2, -, hh4, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q M.ι (C ω * logS) hch.2.1
  have hprod : hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m) *
      hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z)) = 1 := by
    rw [← (hh1 _ _ haε haη).2.1]
    have e1 : ∀ᶠ z in 𝓝 (0 : ℂ), θ (α * z) ≠ 0 := hA.continuous.continuousAt.eventually_ne hA0
    have e2 : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ^ m ≠ 0 := hB.continuous.continuousAt.eventually_ne hB0
    have := (hh1 _ (fun _ => (1 : ℂ)) (haε.mul haη) analyticAt_const).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with z h1' h2'
      show θ (α * z) / θ z ^ m * (θ z ^ m / θ (α * z)) = 1
      field_simp)
    refine Eq.trans this ?_
    rw [hh2]; simp
  have hε0 : θ (α * 0) / θ 0 ^ m = 1 := by simp [h0]
  have hmain : ∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * (θ (α * z) / θ z ^ m) := by
    intro z hz'
    field_simp
  refine ⟨fun z => θ (α * z) / θ z ^ m, hEε, haε, hε0, ?_, hmain, ?_⟩
  · refine ((_root_.GlobalTheory.MomOne.sup_norm_laws q).2.2.2.2.1 _ _ hbε hbη hprod ?_).1
    rw [hh4]; simp [h0]
  · intro y z hyz
    rw [nonzeroIndexPlaces_adelicDataResized_eq, nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm, ← mul_add, mul_pow, mul_assoc]
    exact congrArg _ (hmain _ hyz)

end GlobalTheory.MomOne.ThetaQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TotalDegreeLeOfMemFFV
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RamChartCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts GlobalTheory.PowGerm GlobalTheory.HarmCopies
open Matrix

section Val

variable (T : CDVR) (e : ℕ)

theorem nval_nonneg_of_mem {x : T.Fr} (hx : x ∈ (algebraMap T.V T.Fr).range) : (0 : EReal) ≤ nval T.V e x := by
  obtain ⟨r, rfl⟩ := hx
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]; exact le_top
  rw [nval_of_ne hr]
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) r
  have h2 : valV T.V (algebraMap T.V T.Fr r) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  have h4 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by
    have : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by unfold vV; omega
    exact_mod_cast this
  exact_mod_cast div_nonneg h4 (Nat.cast_nonneg e)

theorem le_nval_int_comb {ι : Type} (s : Finset ι) (cf S : ι → T.Fr) (r : EReal)
    (hc : ∀ i, cf i ∈ (algebraMap T.V T.Fr).range) (hS : ∀ i, r ≤ nval T.V e (S i)) :
    r ≤ nval T.V e (∑ i ∈ s, cf i * S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nval_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min ?_ ih) (nval_add e _ _)
    rw [nval_mul]
    calc r = 0 + r := (zero_add r).symm
      _ ≤ _ := add_le_add (nval_nonneg_of_mem T e (hc a)) (hS a)

theorem isIntPS_iff {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro h
    choose g hg using h
    exact ⟨g, MvPowerSeries.ext fun m => hg m⟩
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem isIntPS_boxSer {n d : ℕ} (f : Fin n → Germ.PS T.Fr 1 d) (hf : ∀ b, IsIntPS T (f b)) :
    IsIntPS T (boxSer f) := by
  choose g hg using fun b => (isIntPS_iff T (f b)).1 (hf b)
  refine (isIntPS_iff T _).2 ⟨boxSer g, ?_⟩
  unfold boxSer
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← hg b, MvPowerSeries.rename_map]

end Val

section Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def colVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  ∑ mo ∈ P.support, P.coeff mo *
    ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)

theorem chartVal_boxSer (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : chartVal C k (boxSer f) P = colVal C k f P := by
  letI := io.toAlgebra
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv (E →+* ℂ) Dw.mult n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv _ _ n).surjective P
  unfold chartVal colVal
  rw [nabValN_boxSer T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 (const_eq_zero C.ch.gauge) k n f _ _
    (letterEquiv (E →+* ℂ) Dw.mult n) _ C.ch.uvec _ (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename (letterEquiv (E →+* ℂ) Dw.mult n) (fun mo =>
      ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hc : colM mo b = colOf (Finsupp.mapDomain (letterEquiv (E →+* ℂ) Dw.mult n) mo) b := by
    ext ℓ
    exact (Finsupp.mapDomain_apply_of_injective (letterEquiv (E →+* ℂ) Dw.mult n).injective mo (ℓ, b)).symm
  rw [hc]

theorem bound_all_iff_bound_prod (C : IntegralChartA3 Xo c T io y) (e k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr)
    (r : EReal) :
    (∀ f : Germ.PS T.Fr n (chD C.ch), IsIntPS T f → r ≤ nval T.V e (chartVal C k f P)) ↔
      ∀ f : Fin n → Germ.PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → r ≤ nval T.V e (colVal C k f P) := by
  letI := io.toAlgebra
  constructor
  · intro h f hf
    rw [← chartVal_boxSer]
    exact h _ (isIntPS_boxSer T f hf)
  · intro h f hf
    obtain ⟨S, hS⟩ := exists_jet P.totalDegree f
    have h1 : chartVal C k f P = ∑ j : S, MvPowerSeries.coeff j.1 f *
        chartVal C k (MvPowerSeries.monomial j.1 1) P := by
      unfold chartVal
      rw [(nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).1 _ _ _ hS,
        (nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).2.1]
    rw [h1]
    refine le_nval_int_comb T e _ _ _ r (fun j => hf j.1) fun j => ?_
    rw [monomial_eq_boxSer, chartVal_boxSer]
    refine h _ fun b => (isIntPS_iff T _).2 ⟨∏ i, MvPowerSeries.X ((0 : Fin 1), i) ^ j.1 (b, i), ?_⟩
    simp only [map_prod, map_pow, MvPowerSeries.map_X]

end Values

section Lifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

end Lifts

end GlobalTheory.RamChartCmp
end
end

