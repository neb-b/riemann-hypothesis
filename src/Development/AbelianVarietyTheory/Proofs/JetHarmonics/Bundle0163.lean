module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyUniformisedFormalChartAlgebraicPointStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChart
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharPair

theorem sum_sigma_type {M : Type} [AddCommMonoid M] {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d)
    (f : (Σ b : ZMod d, Fin (m b)) → M) (hf : ∀ x, x.1 ≠ a → f x = 0) : ∑ x, f x = ∑ i : Fin (m a), f ⟨a, i⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    exact Finset.sum_eq_zero fun i _ => hf _ hb
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isSat_type {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) {n : ℕ}
    {w : Fin n → (Σ b : ZMod d, Fin (m b)) → C} (hw : IsSat V w) (h0 : ∀ q x, x.1 ≠ a → w q x = 0) :
    IsSat V fun q (i : Fin (m a)) => w q ⟨a, i⟩ := by
  obtain ⟨h1, w', h2, h3⟩ := hw
  refine ⟨fun q i => h1 q _, fun i q => w' ⟨a, i⟩ q, fun i q => h2 _ q, fun q q' => ?_⟩
  rw [← h3 q q', sum_sigma_type m a (fun x => w q x * w' x q') fun x hx => by rw [h0 q x hx, zero_mul]]

theorem coeff_single_one_uncurry_eq_partialDerivative {C : Type} [Field C] {dd : ℕ} (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single i 1) (un1 f) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl f i := by
  show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem integralSeries_uncurry_one {C : Type} [Field C] {V : VF C} {dd : ℕ} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) :=
  fun _ => hf _

theorem isCharacter_uncurry_logarithm_law {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I) {f : PS C 1 dd}
    (hf : ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.raw p) (gp C (Fin dd) (0 : Fin 2)) (gp C (Fin dd) 1)) (un1 f) =
      MvPowerSeries.subst (gp C (Fin dd) (0 : Fin 2)) (un1 f) * MvPowerSeries.subst (gp C (Fin dd) (1 : Fin 2)) (un1 f) := by
  rw [RowLawPair.formalAdd_eq_law Y p (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawSquare.zc_law Y (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1)),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 0), RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 1)]
  exact hf.2

theorem orbitSum_eq {d l : ℕ} (hl : 0 < l) (p : ZMod d → ℕ) (s : ZMod d) :
    (∑' i : ℕ, ((l : ℝ) ^ (-((i : ℝ) + 1))) * (p (s + ((i + 1 : ℕ) : ZMod d)) : ℝ)) = S4.frobSum l p s := by
  unfold S4.frobSum
  exact tsum_congr fun i => by rw [ValuationFitting.rpow_neg_succ hl]

theorem chSt_pair : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), lab.RankOK Dw → ∀ (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb d _ lab ha hg hr o Hc g a hb w hw h0
  have hinj : Function.Injective (lab.tau o g) := fun s s' h =>
    (Prod.mk.inj (Prod.mk.inj (ha.inj (a₁ := (o, g, s)) (a₂ := (o, g, s')) h)).2).2
  obtain ⟨χ, hχ, hdet⟩ := _root_.GlobalTheory.CharMinor.exists_chars_minor_le hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl d (lab.tau o g) hinj
    (ha.frob o g) a lab.n (fun q i => w q ⟨a, i⟩) (isSat_type (fun b => Dw.mult (lab.tau o g b)) a hw h0)
  have hconj : ∀ s, ComplexEmbedding.conjugate (lab.tau o g s) = lab.tau o (1 - g) s := by
    intro s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  simp only [hconj] at hdet
  have hl1 : 1 < V.l := V.l_prime.one_lt
  rw [orbitSum_eq V.l_prime.pos (fun s => Dw.mult (lab.tau o (1 - g) s)) a] at hdet
  have hL : (1 : ℝ) < V.l := by exact_mod_cast hl1
  have h1 := S4.one_div_eq_gam_add_rho hl1
  have hdiv : ∀ x : ℝ, x / ((V.l : ℝ) - 1) = x * (S4.gam V.l + S4.rho V.l) := fun x => by
    rw [← h1]; ring
  have hrho : 0 ≤ S4.rho V.l := div_nonneg zero_le_one (by nlinarith)
  have hgam : 0 ≤ S4.gam V.l := div_nonneg (by linarith) (by nlinarith)
  have hj : (0 : ℝ) ≤ lab.j := Nat.cast_nonneg _
  have hj' : (0 : ℝ) ≤ lab.j' := Nat.cast_nonneg _
  obtain ⟨hc, hbig, hsm⟩ := hr o
  have hpb : ∀ b, lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = 0 + lab.j' := fun b h => by
    rw [hsm (1 - g) b fun hh => (hc g b).1 hh h, zero_add]
  have hps : ∀ b, ¬ lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = lab.n + lab.j := fun b h =>
    hbig (1 - g) b ((hc g b).2 h)
  have hmat : (Matrix.of fun ρ q : Fin lab.n => ∑ x : lab.II Dw o g,
      (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i) * w q x) =
      Matrix.of fun ρ q : Fin lab.n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i *
        ι (chartUnitVectors C3 ⟨lab.tau o g a, x⟩ i)) * w q ⟨a, x⟩ := by
    ext ρ q
    simp only [Matrix.of_apply, coeff_single_one_uncurry_eq_partialDerivative]
    exact sum_sigma_type (fun b => Dw.mult (lab.tau o g b)) a _ fun x hx => by rw [h0 q x hx, mul_zero]
  rw [← hmat] at hdet
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i,
    fun ρ x => VF.Ge.sum fun i _ => (integralSeries_uncurry_one (hχ ρ).1 _).mul_int (hg.u_int o g x i), fun S t ht ρ => ?_,
    fun hA => hdet.trans (WithTop.coe_le_coe.mpr ?_), fun hB => hdet.trans (WithTop.coe_le_coe.mpr ?_)⟩
  · exact _root_.GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm C V d (lab.II Dw o) (Fin (chD C3.ch)) (Y.raw (pairOfLab ha hg o))
      (RowLawPair.rLaw_raw Y _) Hc (un1 (χ ρ)) (integralSeries_uncurry_one (hχ ρ).1) ((constantCoeff_uncurry _).trans (hχ ρ).2.1)
      (isCharacter_uncurry_logarithm_law Y _ (hχ ρ).2) g S t ht
  · rw [S4.frobSum_alt hl1 0 lab.j' (lab.n + lab.j) (lab.big o g) (CharacteristicFromRanks.alt_step (lab.big o) hc hA g) _ hpb hps a hb]
    show _ ≤ (lab.n : ℝ) * S4.gam V.l + ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj' hgam]
  · rw [S4.frobSum_const hl1 (0 + lab.j') _ (fun b => hpb b (hB b)) a]
    show _ ≤ ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv, hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj hgam]

end GlobalTheory.CharPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundSelfConjugateDegreeTwoIntegralChar
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharSquare

open GlobalTheory.RowLawSquare

theorem tsum_alt (l : ℝ) (hl : 1 < l) (a b : ℝ) (m : ℕ → ℝ) (h0 : ∀ k, m (2 * k) = a) (h1 : ∀ k, m (2 * k + 1) = b) :
    ∑' i : ℕ, l ^ (-((i : ℝ) + 1)) * m i = (a * l + b) / (l ^ 2 - 1) := by
  have hp : 0 < l := by linarith
  have hq : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hg := hasSum_geometric_of_lt_one (r := (l ^ 2)⁻¹) (by positivity) hq
  have e : ∀ i : ℕ, l ^ (-((i : ℝ) + 1)) = (l ^ (i + 1))⁻¹ := fun i => by
    rw [Real.rpow_neg hp.le, ← Real.rpow_natCast]; push_cast; rfl
  have hne : l ^ 2 - 1 ≠ 0 := by nlinarith
  have he : HasSum (fun k : ℕ => l ^ (-(((2 * k : ℕ) : ℝ) + 1)) * m (2 * k)) (l⁻¹ * a * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left (l⁻¹ * a))
    rw [e, h0, pow_succ, pow_mul, inv_pow]; field_simp
  have ho : HasSum (fun k : ℕ => l ^ (-(((2 * k + 1 : ℕ) : ℝ) + 1)) * m (2 * k + 1))
      ((l ^ 2)⁻¹ * b * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left ((l ^ 2)⁻¹ * b))
    rw [e, h1, add_assoc, pow_add, pow_mul, inv_pow]; field_simp
  rw [(HasSum.even_add_odd (f := fun i : ℕ => l ^ (-((i : ℝ) + 1)) * m i) he ho).tsum_eq]
  field_simp

theorem alt_le (l : ℝ) (hl : 1 < l) (n j j' : ℝ) (hj : 0 ≤ j) (hj' : 0 ≤ j') :
    ((n + j) * l + j') / (l ^ 2 - 1) ≤ n * (l / (l ^ 2 - 1)) + (j + j') / (l - 1) := by
  have h1 : 0 < l - 1 := by linarith
  have h2 : 0 < l ^ 2 - 1 := by nlinarith
  have e : (j + j') / (l - 1) = (j + j') * (l + 1) / (l ^ 2 - 1) := by
    field_simp; ring
  rw [e, ← mul_div_assoc, ← add_div]
  refine div_le_div_of_nonneg_right ?_ h2.le
  nlinarith

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem exists_unit (a : ZMod d) (g : Fin 2) : ∃ col, V.v (p.gm a col g) = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ r, 0 < V.v (p.gm (a + p.hd) r (1 - g) * p.gm a r g) := fun r => by
    have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm (a + p.hd) r (1 - g)) := gm_int Y p _ _ _
    have h2 : (0 : WithTop ℝ) ≤ V.v (p.gm a r g) := gm_int Y p _ _ _
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (lt_of_le_of_ne h2 (hc r).symm) (le_add_of_nonneg_left h1)
  have hg : 1 - g ≠ g := by fin_cases g <;> decide
  have e := p.gm_hyp a (1 - g) g
  rw [if_neg hg, Fin.sum_univ_two] at e
  have := V.v.map_lt_add (hpos 0) (hpos 1)
  rw [e, V.v.map_one] at this
  exact lt_irrefl _ this

omit [CharZero C] in
theorem inCol_eq (col : Fin 2) (f : PS C 1 dd) : inCol col (un1 f) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) f :=
  subst_singlePointUncurry (fun _ => MvPowerSeries.constantCoeff_X _) f

omit [CharZero C] in
theorem intS_inCol (col : Fin 2) {f : PS C 1 dd} (hf : IntS V f) : IntS V (inCol col (un1 f)) := by
  rw [inCol_eq]
  exact intS_subst V (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X V _) hf


omit [CharZero C] in
theorem coeff_inCol (col : Fin 2) (f : PS C 1 dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (inCol col (un1 f)) = MvPowerSeries.coeff μ
      (MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X (col, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := by
  have hS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  rw [inCol_eq, coeff_rename_low (fun q : Fin 1 × Fin dd => (col, q.2)) (N := 1)
    (g := MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)) ?_ μ hμ]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← MvPowerSeries.coe_substAlgHom (R := C) hS, map_add (f := _), map_sum]
      simp only [map_smul, MvPowerSeries.substAlgHom_X]
      congr 2
      exact (MvPowerSeries.substAlgHom (R := C) hS).commutes _
  · intro e he
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simp
    · obtain ⟨⟨s, i⟩, rfl⟩ : ∃ q, e = Finsupp.single q 1 := finsupp_deg_one e h
      obtain rfl : s = 0 := Subsingleton.elim _ _
      simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, Pdiv.ChartF.dl]

omit [CharZero C] in
theorem cc_inCol (col : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.constantCoeff (inCol col (un1 f)) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_inCol col f 0 (by simp)]
  simp

omit [CharZero C] in
theorem lin_inCol (col : Fin 2) (f : PS C 1 dd) (x : Fin 2 × Fin dd) :
    MvPowerSeries.coeff (Finsupp.single x 1) (inCol col (un1 f)) = if x.1 = col then Pdiv.ChartF.dl f x.2 else 0 := by
  rw [coeff_inCol col f _ (by simp)]
  obtain ⟨r, i⟩ := x
  by_cases h : r = col <;>
    simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, h]

theorem lin_u (col g : Fin 2) (f : PS C 1 dd) (x : I0) :
    ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 f)) * (Y.rawSelf p).u g x i =
      p.gm (p.ty0 x) col g * ∑ i, Pdiv.ChartF.dl f i * p.e x i := by
  simp only [lin_inCol, Fintype.sum_prod_type, ite_mul, zero_mul, FBChart.rawSelf]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem char_inCol (col : Fin 2) {f : PS C 1 dd} (hf : Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.rawSelf p) (gp C _ (0 : Fin 2)) (gp C _ 1)) (inCol col (un1 f)) =
      MvPowerSeries.subst (gp C _ (0 : Fin 2)) (inCol col (un1 f)) *
        MvPowerSeries.subst (gp C _ (1 : Fin 2)) (inCol col (un1 f)) := by
  have z := fun (j : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
  have h2 := zc2 (z 0) (z 1)
  have e := congrArg (sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col]) hf.2
  have hm : ∀ f g : PS C 2 dd, sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] (f * g) =
      sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] f *
        sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] g :=
    fun f g => MvPowerSeries.subst_mul (hasSubst_sb h2) f g
  rw [substPointsPowerSeries_eval_one h2 (zc_addOf Y 0 1), sb_addOf Y h2, hm, substPointsPowerSeries_eval_one h2 (zc_pt 0), substPointsPowerSeries_eval_one h2 (zc_pt 1), sb_pt' h2,
    sb_pt' h2] at e
  rw [subst_inCol (zc_addP Y p (zc_gp _) (zc_gp _)), subst_inCol (zc_gp _), subst_inCol (zc_gp _)]
  have e2 := col_addP Y p (zc_gp (C := C) (0 : Fin 2)) (zc_gp 1) col
  unfold RowLawSquare.colOf at e2
  rw [e2]
  exact e

end Chart

theorem isSat_fst {C : Type} [Field C] {V : VF C} {m : ZMod 2 → ℕ} {n : ℕ} {w : Fin n → (Σ s : ZMod 2, Fin (m s)) → C}
    (hw : IsSat V w) (h1 : ∀ q i, w q ⟨1, i⟩ = 0) : IsSat V fun q i => w q ⟨0, i⟩ := by
  obtain ⟨hi, u, hu, e⟩ := hw
  refine ⟨fun _ _ => hi _ _, fun i q => u ⟨0, i⟩ q, fun _ _ => hu _ _, fun q q' => ?_⟩
  rw [← e q q', Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
    Finset.sum_pair (by decide)]
  simp [h1]

theorem chSt_rawSelf : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → lab.RankOK Dw → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (p o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hst T io y C3 C _ _ V ι hι k Y hY hy Orb _ lab hA hR p hp o Hc g a hbig w hw hw0
  have ha : a = ((g.val : ℕ) : ZMod 2) := (hp.big o g a).1 hbig
  have h1 : ∀ q i, w q ⟨1, i⟩ = 0 := fun q i => hw0 q _ (by
    simp only [FBChart.rawSelf, hp.ty0, hp.hd, ha]
    fin_cases g <;> decide)
  obtain ⟨χ, hχ, hdet⟩ := _root_.GlobalTheory.CharMinor.exists_chars_minor_le hup E H Dw lv Xo c hst T io y C3 C V ι hι k Y hY hy hA.unr 2 (lab.tau o)
    (fun s s' h => (Prod.ext_iff.1 (hA.inj (a₁ := (o, s)) (a₂ := (o, s')) h)).2) (hA.frob o) 0 _ _ (isSat_fst hw h1)
  obtain ⟨col, hcol⟩ := exists_unit Y (p o) 0 g
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 (χ ρ))) *
    (Y.rawSelf (p o)).u g x i, fun ρ x => ?_, fun S t ht ρ => ?_, fun _ => ?_, fun hall => ?_⟩
  · exact VF.Ge.sum fun i _ => (intS_inCol col (hχ ρ).1 _).mul_int
      ((rlaw_rawSelf C V _ _ Y 2 _ (p o)).uint g x i)
  · exact GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm C V 2 _ _ _ (rlaw_rawSelf C V _ _ Y 2 _ (p o)) Hc _
      (intS_inCol col (hχ ρ).1) (by rw [cc_inCol, (hχ ρ).2.1]) (char_inCol Y (p o) col (hχ ρ).2) g S t ht
  · have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hm : ∀ i : ℕ, ComplexEmbedding.conjugate (lab.tau o (0 + ((i + 1 : ℕ) : ZMod 2))) = lab.tau o i := fun i => by
      rw [← hA.conj]
      congr 1
      push_cast
      generalize (i : ZMod 2) = z
      revert z
      decide
    simp only [hm] at hdet
    rw [tsum_alt V.l hl ((lab.n : ℝ) + lab.j) lab.j' (fun i : ℕ => (Dw.mult (lab.tau o i) : ℝ))
      (fun k => by
        have : ((2 * k : ℕ) : ZMod 2) = 0 := by push_cast; exact mul_eq_zero_of_left rfl _
        simp only [this, (hR o).1, Nat.cast_add])
      (fun k => by
        have : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
          push_cast; rw [mul_eq_zero_of_left (show (2 : ZMod 2) = 0 from rfl), zero_add]
        simp only [this, (hR o).2])] at hdet
    have hM : (Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1)
        (inCol col (un1 (χ ρ))) * (Y.rawSelf (p o)).u g x i) * w q x) =
        (p o).gm 0 col g • Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, Pdiv.ChartF.dl (χ ρ) i *
          ι (chartUnitVectors C3 ⟨lab.tau o 0, x⟩ i)) * w q ⟨0, x⟩ := by
      ext ρ q
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, lin_u, hp.ty0, hp.e]
      rw [Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
      simp only [h1, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [hM, Matrix.det_smul, V.v.map_mul, V.v.map_pow, hcol, smul_zero, zero_add]
    refine hdet.trans (WithTop.coe_le_coe.2 ?_)
    simp only [FBChart.rawSelf, hp.n, hp.j, hp.j', Formalism.IncomingBounds.gam]
    exact alt_le _ hl _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact absurd (((hp.big o g 0).1 (hall 0)).trans ((hp.big o g 1).1 (hall 1)).symm) (by decide)

end GlobalTheory.CharSquare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformizedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_all_models_uniformized : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), y'.IsAlg ∧ 0 < e' ∧ (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧ letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr, (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  first | exact @GlobalTheory.IntegralPull.exists_ext_all_models_uniformised | exact GlobalTheory.IntegralPull.exists_ext_all_models_uniformised | (intros; apply GlobalTheory.IntegralPull.exists_ext_all_models_uniformised <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFiniteExtAllModelsUniformised
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IntegralPull

theorem exists_finite_ext_all_models_uniformised {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) (e : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (ho : OverLa la T.V io e) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (φF : T.Fr →+* T'.Fr) (e₁ : ℕ) (z' : IntFr Xo c T' (φF.comp io)),
      Function.Injective φ ∧ IsLocalHom φ ∧ φ.Finite ∧
      φF.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φ ∧
      0 < e₁ ∧ OverLa la T'.V (φF.comp io) (e * e₁) ∧ z'.IsAlg ∧
      (letI := io.toAlgebra; letI := (φF.comp io).toAlgebra
        FrMap ({ φF with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z'.1) ∧
      ∀ I : IntData Xo c T' (φF.comp io) z'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso := by
  have : Finite (ResidueField T.V) := hy
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  refine ⟨T', algebraMap T.V W, φ, r, y', hi, hl, RingHom.finite_algebraMap.2 hf, RingHom.ext hφ, hr0, ?_, hr, hz,
    fun I => exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS⟩
  rw [Nat.mul_comm]
  exact ho.bc φ hr0 hv

end GlobalTheory.IntegralPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLatticeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_basis_uniformization_lattice : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  first | exact @GlobalTheory.ShortBasisAt.exists_shortBasis | exact GlobalTheory.ShortBasisAt.exists_shortBasis | (intros; apply GlobalTheory.ShortBasisAt.exists_shortBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HodgeTateInclusionIntegralChart
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem hodgeTate_inclusion_intChart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∃ (N : ℕ) (u : Fin N → PS X.O 1 (chD Ch.ch)), (∀ k, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (u k)) ∧ ∀ z : X.O, X.v (algebraMap X.O X.C z) ^ (p - 1) ≤ X.v (p : X.C) → ∀ f : Fin (chD Ch.ch) → X.O, z • f ∈ Submodule.span X.O (Set.range fun k => dl (u k)) := by
  intro p _ hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy
  obtain ⟨U⟩ := GlobalTheory.CharDepth.nonempty_unifChart E H Dw l Xo c T io y Ch hy p X
  have hp : ¬IsUnit (p : U.T'.V) := fun h => by
    have h' := h.map U.ι'
    rw [map_natCast] at h'
    exact (Fact.out : ¬IsUnit (p : X.O)) h'
  obtain ⟨N, u, hu, hz⟩ := hHT U.T'.V hp U.t.G U.P.D U.P.A U.P.U.toUnifPre (chD Ch.ch) U.F U.x
    U.chart X.C X.v X.O X.ints U.ι' U.ι'_local
  refine ⟨N, u, fun k => ?_, fun z hv f => hz z (by rwa [map_natCast]) f⟩
  rw [← U.law_eq]
  exact hu k

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n Dg e : ℕ), 1 ≤ n → 0 < e → DF Dw a ≤ Dg → 4 * Dg + 4 ≤ l.M → (Dg : ℝ) * M0 < l.M → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) ≤ nuLocC C e l.M a n + (((Dg : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  first | exact @GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | exact GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | (intros; apply GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC <;> assumption)
end

