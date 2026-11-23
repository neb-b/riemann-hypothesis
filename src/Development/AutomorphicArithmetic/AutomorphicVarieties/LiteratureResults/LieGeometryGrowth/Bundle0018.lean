module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStepCut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ExpBound
section
open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem exp_bound (D C c : ℝ) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ (N : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ (n : ℕ) (x y : ℝ), 1 ≤ x → y ≤ C * (1 + Real.log x) → n * c - 1 ≤ y →
      Real.exp (D * (n + 1)) ≤ K * x ^ N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (D * |C| / c)
  refine ⟨N, Real.exp (D * ((1 + |C|) / c + 1)), (Real.exp_pos _).le, fun n x y hx h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := one_pos.trans_le hx
  have h3 : y ≤ |C| * (1 + Real.log x) := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
  have h4 : (n : ℝ) ≤ (1 + |C|) / c + |C| / c * Real.log x := by
    have : (1 + |C|) / c + |C| / c * Real.log x = (1 + |C| * (1 + Real.log x)) / c := by
      field_simp
      ring
    rw [this, le_div_iff₀ hc]
    linarith
  have h5 : x ^ N = Real.exp (N * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx0]
  rw [h5, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h6 : D * |C| / c * Real.log x ≤ N * Real.log x := mul_le_mul_of_nonneg_right hN hl
  have h7 := mul_le_mul_of_nonneg_left h4 hD
  have h8 : D * ((1 + |C|) / c + |C| / c * Real.log x) = D * ((1 + |C|) / c) + D * |C| / c * Real.log x := by ring
  nlinarith

theorem UpperTheory.V.Lit.Geo.approx :
    Approx := by
  intro E _ _ _ a ha U hUo hUc Ξ q η hη hM
  obtain ⟨f, Y, C, c, f₀, hS⟩ := stepEx E a ha U hUc
  obtain ⟨D, hD, hP⟩ := prim E a U hUo Ξ f Y C c f₀ hS q η hη hM
  obtain ⟨B, hB, hcut⟩ := stepCut E a U f Y C c f₀ hS
  obtain ⟨N₁, C₁, hC₁, hG⟩ := (bdGrowth E a Ξ (q + 1) _).1 hM
  obtain ⟨N₂, K, hK, hE⟩ := exp_bound D C c hD hS.c_pos
  have hq := (qhtFacts E a).1
  have hfr : ∀ g, f (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = f g := fun g => by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have := hS.f_left 1 t g
    rw [map_one, one_mul] at this
    rw [ht, this]
  refine ⟨N₁ + N₂, C₁ + (q + 1) * B * K, by positivity, fun R => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((|C| * (1 + Real.log (max R 1)) + 1) / c)
  rw [div_le_iff₀ hS.c_pos] at hn
  obtain ⟨η', hη', hd, hb⟩ := hP n
  obtain ⟨u, hu, hU⟩ := hcut (n * c - 1)
  obtain ⟨ζ, hζ, hmul, hdζ⟩ := mulEx E a U Ξ q u η' hu hη'
  have hfar : ∀ g, Real.exp (|C| * (1 + n * c)) < qht g → n * c - 1 + 1 ≤ f g := fun g hg => by
    by_contra hcon
    have h0 : f g ≤ n * c := by linarith
    have h1 : Real.log (qht g) ≤ |C| * (1 + n * c) :=
      (hS.le_f g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [hS.f_nonneg g]) (abs_nonneg C))
    have h2 := Real.exp_le_exp.2 h1
    rw [Real.exp_log (one_pos.trans_le (hq g))] at h2
    linarith
  refine ⟨ζ, hζ, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, fun g => ?_⟩
  · rw [hmul X g, ((hU g).2.2 (hfar g hg)).1, zero_smul]
  · rw [hdζ X g, ((hU g).2.2 (hfar g hg)).1, zero_smul, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((hU g).2.2 (hfar g hg)).2, mul_zero, zero_smul]
  have hcb := cutBd E a Ξ q u η' ζ hdζ g
  rw [hd] at hcb
  have q1 := hq g
  have hM' : 0 ≤ C₁ * qht g ^ N₁ := by positivity
  have near : f g ≤ n * c - 1 → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0 := fun h => by
    have h1 := (hU _).2.1 ((hfr g).trans_le h)
    refine (hcb 0 0 0 _ le_rfl hM' le_rfl (by rw [h1.1]; simp) (fun X => by rw [h1.2]; simp) (Or.inl rfl) (hG g)).mono ?_
    simp
  have hs : ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ 1 := by
    obtain ⟨t, t0, t1, ht⟩ := hu.range (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1
    rw [ht, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have p1 : qht g ^ N₁ ≤ qht g ^ (N₁ + N₂) := pow_le_pow_right₀ q1 (by omega)
  have p2 : qht g ^ N₂ ≤ qht g ^ (N₁ + N₂) := pow_le_pow_right₀ q1 (by omega)
  have p3 : C₁ * qht g ^ N₁ ≤ C₁ * qht g ^ (N₁ + N₂) := mul_le_mul_of_nonneg_left p1 hC₁
  refine ⟨fun hg => near ?_, ?_⟩
  · have h1 : Real.log (qht g) ≤ Real.log (max R 1) :=
      Real.log_le_log (one_pos.trans_le q1) (hg.trans (le_max_left _ _))
    have h2 : f g ≤ |C| * (1 + Real.log (max R 1)) :=
      (hS.f_le g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [Real.log_nonneg q1]) (abs_nonneg C))
    linarith
  by_cases h1 : f g ≤ n * c - 1
  · exact (near h1).mono (by positivity)
  by_cases h2 : f g ≤ n * c
  · refine (hcb 1 B _ _ (Real.exp_pos _).le hM' hB hs (hU _).1 (Or.inr (hb g h2)) (hG g)).mono ?_
    have h3 := (hE n _ _ q1 (hS.f_le g) (not_le.1 h1).le).trans (mul_le_mul_of_nonneg_left p2 hK)
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ (q + 1) * B by positivity)
    nlinarith
  · have h3 := (hU _).2.2 (show n * c - 1 + 1 ≤ _ by rw [hfr g]; linarith)
    refine (hcb 1 0 0 _ le_rfl hM' le_rfl hs (fun X => by rw [h3.2]; simp) (Or.inl rfl) (hG g)).mono ?_
    have h4 : (0 : ℝ) ≤ (q + 1) * B * K * qht g ^ (N₁ + N₂) := by positivity
    nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G2Assumption
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs Filter Topology
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem cone_open (E : Type) [Field E] [NumberField E] (a : ℕ) : IsOpen (cone E a) :=
  isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := UpperTheory.V.Lit.Dr.locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩

private theorem homOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : homOm G W (0 : G.Om (q + 1)) = 0 := by
  have e : (fun s => hom (W s) ((0 : G.Om (q + 1)).1 s)) = fun _ _ => 0 := by
    funext s p
    have : (fun t => hk (W s) t ((0 : G.Om (q + 1)).1 s) p) = fun _ => 0 := by
      funext t
      ext v
      simp [hk_apply]
    rw [hom, this, intervalIntegral.integral_zero]
  rw [homOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem pbOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : pbOm G W (0 : G.Om q) = 0 := by
  have e : (fun s => pb (flow (W s) 1) ((0 : G.Om q).1 s)) = fun _ _ => 0 := by
    funext s p
    ext v
    simp [pb_apply]
  rw [pbOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem corr_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} {α β : Co Ξ q} {w w' : (geo ho U Ξ).Om q}
    (h : Corr U Ξ α w.1) (h' : Corr U Ξ β w'.1) : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← h g x X, ← h' g x X]
  rfl

private theorem corr_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) :
    Corr U Ξ (0 : Co Ξ q) (0 : (geo ho U Ξ).Om q).1 := fun g x X => by
  simp

private theorem half (D c : ℝ) (hD : 0 ≤ D) (hc : 0 < c) : D * Real.exp (-(2 * D / c * c)) ≤ 1 / 2 := by
  rw [div_mul_cancel₀ _ hc.ne', Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have := Real.add_one_le_exp (2 * D)
  linarith

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Lit.Geo.Cs.galois_twist_preserves_siegel_bound (h1 : LamEx) (h2 : DescEx) (h3 : DescFun) (h4 : RapidAll) (h5 : CorrSz) (h6 : DecP)
    (h7 : DecK) (h8 : Loc) (h9 : GeoSum) (h10 : GeoRet) (h11 : Supp) : G2 := by
  intro E _ _ _ a ha U hUo hUc Ξ q ω hω hd hR
  have ho := cone_open E a
  obtain ⟨f, Y, C, c, f₀, hS⟩ := stepEx E a ha U hUc
  have hC : 0 ≤ C := (abs_nonneg _).trans (hS.near 1 0 1 (by simp) (by simp))
  obtain ⟨W, hW⟩ := fieldDef E a U Y C hS.fld
  have hF := (fieldFlow E a ho U Ξ Y C hS.fld W hW).1
  have hH := omHom _ _ _ _ _ W hF
  obtain ⟨lam, hl⟩ := h1 E a ha
  obtain ⟨Φ, hΦ⟩ := h2 E a U f Y C c f₀ hS
  have hΦf := h3 E a ho U Ξ f Y C c f₀ hS Φ hΦ
  obtain ⟨w, hw, hg⟩ := (levGood E a ho U Ξ q).1 ω hω
  have hdw : (geo ho U Ξ).dOm q w = 0 := by
    have c1 := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q ω w hw
    rw [hd] at c1
    exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ (q + 1)).2 _ _ _ c1 (corr_zero ho U Ξ _)
  obtain ⟨B, hB, hrap⟩ := h4 E a U Ξ f lam C hl hS.f_le q ω hω hR
  obtain ⟨u, u0, us⟩ : ∃ u : ℕ → (geo ho U Ξ).Om q, u 0 = w ∧ ∀ j, u (j + 1) = pbOm (geo ho U Ξ) W (u j) :=
    ⟨fun j => (pbOm (geo ho U Ξ) W)^[j] w, rfl, fun j => Function.iterate_succ_apply' _ _ _⟩
  have ug : ∀ j, Good (geo ho U Ξ) (u j) := fun j => by
    induction j with
    | zero => rwa [u0]
    | succ j ih => rw [us]; exact ((omGood _ _ _ _ _ W hF q).1 _ ih).1
  have ud : ∀ j, (geo ho U Ξ).dOm q (u j) = 0 := fun j => by
    induction j with
    | zero => rwa [u0]
    | succ j ih => rw [us, hH.1, ih, pbOm_zero]
  have dec : ∀ k, ∃ A M : ℝ, 0 ≤ A ∧ 0 ≤ M ∧ ∀ j, Dec U Ξ f lam f₀ k A B ((1 / 2) ^ j * M) (u j).1 := fun k => by
    obtain ⟨D, hD, hP⟩ := h6 E a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
    have hA : 0 ≤ 2 * D / c := div_nonneg (by linarith) hS.c_pos.le
    obtain ⟨M, hM, hM'⟩ := h5 E a U Ξ q ω w.1 hw (fun g => Real.exp (B * |lam g| - 2 * D / c * f g))
      (fun _ => (Real.exp_pos _).le) (hrap _ hA) k
    refine ⟨2 * D / c, M, hA, hM, fun j => ?_⟩
    induction j with
    | zero =>
      rw [u0, pow_zero, one_mul]
      exact fun g x _ => hM' g x
    | succ j ih =>
      rw [us]
      have hj : (0 : ℝ) ≤ (1 / 2) ^ j * M := by positivity
      refine Dec.of_le U Ξ (hP _ _ hA hj _ ih) ?_
      rw [pow_succ', mul_assoc (1 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_right (half D c hD hS.c_pos) hj
  have geom : ∀ x : ℝ, Summable fun j : ℕ => x * (1 / 2 : ℝ) ^ j := fun x => summable_geometric_two.mul_left x
  have lim : ∀ s, ∀ p ∈ cone E a, f₀ + C < Φ s p → Tendsto (fun j => (u j).1 s p) atTop (𝓝 0) := fun s p hp hlt => by
    obtain ⟨A, M, hA, hM, hj⟩ := dec 0
    obtain ⟨N, hN, D, hD⟩ := h8 E a ho U Ξ f lam hS.f_nonneg hl Φ hΦ hΦf q 0 A B f₀ hA hB s p hp (by linarith)
    refine squeeze_zero_norm (fun j => ?_) (geom (D * M)).tendsto_atTop_zero
    refine (hD _ (by positivity) _ (hj j) p (mem_of_mem_nhds hN)).norm_le.trans_eq ?_
    ring
  cases q with
  | zero =>
    refine ⟨ω, hω, hd, h11 E a U Ξ f Y C c f₀ hS Φ hΦ 0 ω w.1 (f₀ + C) hw fun s p hp hlt => ?_, sub_self ω⟩
    have e : ∀ j, u j = w := fun j => by
      induction j with
      | zero => exact u0
      | succ j ih =>
        have := hH.2.2.1 w
        rw [hdw, homOm_zero, sub_eq_zero] at this
        rw [us, ih, this]
    have := lim s p hp hlt
    simp only [e] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  | succ q =>
    have hO := omGood _ _ _ _ _ W hF q
    obtain ⟨z, hz, hz'⟩ := h9 _ _ _ _ (geo ho U Ξ) Φ hΦf (f₀ + C) q (fun j => homOm (geo ho U Ξ) W (u j)) u
      (fun j => (hO.2.2 _ (ug j)).inv)
      (fun j => by
        have := hH.2.2.2 q (u j)
        rw [ud j, homOm_zero, add_zero] at this
        exact this.symm.trans (congrArg (· - u j) (us j).symm))
      (fun k s p hp hlt => by
        obtain ⟨A, M, hA, hM, hj⟩ := dec k
        obtain ⟨D', hD', hK⟩ := h7 E a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
        obtain ⟨N, hN, D, hD⟩ := h8 E a ho U Ξ f lam hS.f_nonneg hl Φ hΦ hΦf q k A B (f₀ + C) hA hB s p hp hlt
        refine ⟨N, hN, _, geom (D * D' * M), fun j x hx => ?_⟩
        have p1 : (0 : ℝ) ≤ (1 / 2) ^ j * M := mul_nonneg (pow_nonneg (by norm_num) _) hM
        have p2 := hK _ p1 _ (hj j)
        have p3 := hD _ (mul_nonneg hD' p1) _ p2 x hx
        have p4 : D * (D' * ((1 / 2) ^ j * M)) = D * D' * M * (1 / 2) ^ j := by ring
        rw [p4] at p3
        exact p3) lim
    obtain ⟨l, hgl⟩ := UpperTheory.V.Lit.Dr.gauge E a ha ho U Ξ hUc
    rw [u0] at hz'
    obtain ⟨z', g', hz''⟩ := h10 _ _ _ _ (geo ho U Ξ) (UpperTheory.V.Lit.Dr.coneConvex E a).2 l hgl Φ hΦf (f₀ + C + 1) q w z
      hdw hg.basic hz hz'
    obtain ⟨η, cη, lη⟩ := (levGood E a ho U Ξ q).2 _ g'
    have cd := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q η z' cη
    have cs := corr_sub ho U Ξ hw cd
    refine ⟨ω - dCo (smLie Ξ) η, (levD E a U Ξ _ ω hω).2 _ (levD E a U Ξ q η lη).1, ?_,
      h11 E a U Ξ f Y C c f₀ hS Φ hΦ _ _ _ (f₀ + C + 1) cs fun s p hp hlt => ?_, η, lη, (sub_sub_cancel _ _).symm⟩
    · have c1 := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ _ _ _ cs
      rw [map_sub, hdw, hH.2.1, sub_zero] at c1
      exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ _).1 _ _ _ c1 (corr_zero ho U Ξ _)
    · change w.1 s p - ((geo ho U Ξ).dOm q z').1 s p = 0
      rw [hz'' s p hp hlt, sub_self]
end

