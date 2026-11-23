module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem subst_comb_expPt {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : κ → Fin d → MvPowerSeries σ C) (hw : ∀ b i, constantCoeff (w b i) = 0)
    (F : MvPowerSeries (Fin n × Fin d) C) (M : κ → Fin n → Matrix (Fin d) (Fin d) C) :
    (subst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2)
      (subst (fun q : Fin n × Fin d => expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) F :
        MvPowerSeries (Fin n × Fin d) C) : MvPowerSeries σ C) =
      subst (fun q : Fin n × Fin d => expPt G (∑ b, mv (M b q.1) (w b)) q.2) F := by
  have ht : HasSubst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2) :=
    hasSubst_of_constantCoeff_zero (by intro q; simp [hw])
  have hs : HasSubst (fun q : Fin n × Fin d =>
      expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) :=
    hasSubst_of_constantCoeff_zero (fun q => cc_expPt G (by simp) q.2)
  refine (subst_comp_subst_apply hs ht F).trans ?_
  congr 1
  funext q
  refine (subst_expPt G ht (by simp) q.2).trans ?_
  congr 1
  funext e
  refine (subst_X ht _).trans ?_
  simp [mv, Fintype.sum_prod_type, Finset.sum_apply]

theorem le_v_pow_mul_int {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {p : ℕ} (hp : v (p : C) = 1)
    (N : ℕ) (z : ℤ) : ((N : ℝ) : WithTop ℝ) ≤ v ((((p : ℤ) ^ N * z : ℤ)) : C) := by
  have hz : 0 ≤ v (z : C) := intCast_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v) z
  push_cast
  rw [v.map_mul, v.map_pow, hp]
  calc ((N : ℕ) : WithTop ℝ) = N • (1 : WithTop ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_right hz

theorem limFrame : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  classical
  intro _ hAct hUnit hBi hFr hFin hCont C _ _ v p hp d R _ _ O _ _ _ B hB h hh σ _ κ _ w hw w0 n A a hA hiso α
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have mono : ∀ {M N : ℕ} {x : WithTop ℝ}, M ≤ N → ((N : ℝ) : WithTop ℝ) ≤ x → ((M : ℝ) : WithTop ℝ) ≤ x :=
    fun hMN hx => le_trans (WithTop.coe_le_coe.2 (Nat.cast_le.2 hMN)) hx
  have zle : ∀ {N : ℕ} {x : C}, ((N : ℝ) : WithTop ℝ) ≤ v x → IsIntV v x := fun hx => by
    have := mono (Nat.zero_le _) hx
    simpa [IsIntV] using this
  have hD : ∀ (x : O) i j, IsIntV v (dAct C B x i j) := fun x i j => hB.2.1 x i _
  have hAi : ∀ b j e e', IsIntV v (A b j e e') := fun b j e e' => by
    have := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem (zle (hA 0 b j e e')) (hD (a 0 b j) e e')
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let g : κ × κ × Fin m → MvPowerSeries σ C := fun i =>
    pairSer (fglOf hB) h (w i.1) (mv (dAct C B (e i.2.2)) (w i.2.1))
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i =>
    (hBi C v d R O B hB h hh σ (w i.1) (w i.1) _ (hw _) (hw _)
      ((hAct C v d R O B hB σ (e i.2.2)).2 _ (hw i.2.1))).1
  obtain ⟨N₀, hN₀⟩ := hCont C v (Fin n × Fin d) σ (κ × Fin d)
    (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2)
      (frameSer B h w0 n)) (fun i => w i.1 i.2) (fun i => hw0 _ _) α
  choose N₁ hN₁ using fun γ => hCont C v Unit σ (κ × κ × Fin m) (PowerSeries.exp C) g hg0 γ
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, N₁ x.2 ≤ N :=
    ⟨max N₀ ((Finset.HasAntidiagonal.antidiagonal α).sup fun x => N₁ x.2), le_max_left _ _,
      fun x hx => le_trans (Finset.le_sup (f := fun x => N₁ x.2) hx) (le_max_right _ _)⟩
  have hdec : ∀ b b', ∃ nn : Fin m → ℤ,
      (∑ j, star (a N b j) * a N b' j) * w0 = ∑ i, ((p : ℤ) ^ N * nn i) • e i := fun b b' => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hiso N b b')
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := e) (x := c * w0)).1
      (by rw [he]; exact Submodule.mem_top)
    refine ⟨nn, ?_⟩
    rw [hc, mul_assoc, ← hnn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_assoc]
  choose nn hnn using hdec
  have hU := hFin C v d R O B hB h hh σ κ w hw w0 n (a N) (Fin m) e (fun b b' i => (p : ℤ) ^ N * nn b b' i) hnn
  have hF := (hFr C v d R O B hB h hh w0 n).2.2 σ (fun j => ∑ b, mv (dAct C B (a N b j)) (w b))
    (fun j i => by simp [Finset.sum_apply, mv, hw0])
  let s : κ × κ × Fin m → C := fun i => (((p : ℤ) ^ N * nn i.1 i.2.1 i.2.2 : ℤ) : C)
  have hT : ∑ b, ∑ b', ∑ i, (((p : ℤ) ^ N * nn b b' i : ℤ) : C) •
      pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')) = ∑ i, s i • g i := by
    simp only [Fintype.sum_prod_type, s, g]
  rw [hT] at hU
  have hT0 : constantCoeff (∑ i, s i • g i) = 0 := by simp [hg0]
  obtain ⟨hz, -, -, hmul, -⟩ := hUnit C v σ
  have hprod := hmul _ _ hU.1 hT0
  rw [sub_add_cancel, ← hF] at hprod
  have h1 := hN₀ (fun q i => A i.1 q.1 q.2 i.2) (fun q i => dAct C B (a N i.1 q.1) q.2 i.2)
    (fun q i => hAi _ _ _ _) (fun q i => hD _ _ _) (fun q i => mono hN0 (hA N _ _ _ _))
  rw [subst_comb_expPt (fglOf hB) w hw0 _ A,
    subst_comb_expPt (fglOf hB) w hw0 _ (fun b j => dAct C B (a N b j)), hprod] at h1
  have h2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α,
      IsIntV v (coeff x.2 (PowerSeries.subst (∑ i, s i • g i) (PowerSeries.exp C))) := fun x hx => by
    have h3 := hN₁ x.2 (fun _ => s) (fun _ _ => 0) (fun _ i => zle (le_v_pow_mul_int hp N _))
      (fun _ _ => by simp [IsIntV]) (fun _ i => by
        rw [sub_zero]; exact mono (hN1 x hx) (le_v_pow_mul_int hp N _))
    simp only [zero_smul, Finset.sum_const_zero] at h3
    have h4 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h3 (hz.2 x.2)
    have h5 : ∀ y z : C, y - z + z ∈ ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v → IsIntV v y := fun y z hyz => by
      rw [sub_add_cancel] at hyz
      exact hyz
    exact h5 _ _ h4
  rw [coeff_mul] at h1
  have h6 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h1
    ((ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).sum_mem fun x hx =>
      (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).mul_mem (hU.2 x.1) (h2 x hx))
  rw [sub_add_cancel] at h6
  exact h6

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory.HeightUnique


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_linSubst {R : Type} [CommRing R] {B N n m : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst P (_root_.GlobalTheory.ChowHt.linSubst M f) = _root_.GlobalTheory.ChowHt.linSubst (M * P) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_one {R : Type} [CommRing R] {B N : ℕ} (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst (1 : Matrix (Fin N) (Fin N) R) f = f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  have hX : (fun p : Fin B × Fin N => ∑ k, C ((1 : Matrix (Fin N) (Fin N) R) p.2 k) * X (p.1, k)) = X := by
    funext p
    simp [Matrix.one_apply, apply_ite C, ite_mul]
  rw [hX, aeval_X_left_apply]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_ne_zero {R : Type} [CommRing R] {B N n : ℕ} {M : Matrix (Fin N) (Fin n) R}
    {P : Matrix (Fin n) (Fin N) R} (h : M * P = 1) {f : MvPolynomial (Fin B × Fin N) R} (hf : f ≠ 0) :
    _root_.GlobalTheory.ChowHt.linSubst M f ≠ 0 := by
  intro h0
  apply hf
  have key := _root_.GlobalTheory.HeightUnique.linSubst_linSubst M P f
  rw [h0, h, _root_.GlobalTheory.HeightUnique.linSubst_one] at key
  rw [← key]
  simp [_root_.GlobalTheory.ChowHt.linSubst]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_C_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R) (c : R)
    (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst M (C c * f) = C c * _root_.GlobalTheory.ChowHt.linSubst M f := by
  simp [_root_.GlobalTheory.ChowHt.linSubst]


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.exists_right_inv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective w.mulVecLin
    (by rw [Matrix.range_mulVecLin, hw])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have key := congrArg LinearMap.toMatrix' hg
  have hw' : LinearMap.toMatrix' w.mulVecLin = w := (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hw'] at key

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma isWeightedHomogeneous_aeval_of_isWeightedHomogeneous {R M σ τ : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {w' : τ → M} {g : σ → MvPolynomial τ R} (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (aeval g f) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [aeval_monomial, algebraMap_eq, ← hf (mem_support_iff.mp hd), Finsupp.weight_apply,
    ← zero_add (d.sum fun i c => c • w i)]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i))


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.linSubst_homog {R : Type} [Field R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin N) R} (hf : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a (_root_.GlobalTheory.ChowHt.linSubst M f) := by
  rw [_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block] at hf ⊢
  unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hf ⊢
  unfold _root_.GlobalTheory.ChowHt.linSubst
  refine isWeightedHomogeneous_aeval_of_isWeightedHomogeneous (fun p => ?_) hf
  apply IsWeightedHomogeneous.sum
  intro k _
  have hw : _root_.GlobalTheory.Chow.blockWeight p = _root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n) := by
    simp [_root_.GlobalTheory.Chow.blockWeight]
  rw [hw, ← zero_add (_root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n))]
  exact (isWeightedHomogeneous_C _ _).mul (isWeightedHomogeneous_X _ _ _)


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.gaussAbs_C {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) (c : K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c : MvPolynomial σ K) = w c := by
  classical
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [C_apply, support_monomial, if_neg hc]
    simp [Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_C_mul_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) {c : K}
    (hc : c ≠ 0) (g : MvPolynomial σ K) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c * g) = w c * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have hs : (C c * g).support = g.support := by
    ext s
    simp [coeff_C_mul, hc]
  rw [hs]
  simp_rw [coeff_C_mul, map_mul, Real.toNNReal_mul (apply_nonneg w c)]
  rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_pos_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K)
    {g : MvPolynomial σ K} (hg : g ≠ 0) : 0 < _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hg
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have h1 : (w (AddMonoidAlgebra.coeff g s)).toNNReal ≤ g.support.sup fun t => (w (AddMonoidAlgebra.coeff g t)).toNNReal :=
    Finset.le_sup (f := fun t => (w (AddMonoidAlgebra.coeff g t)).toNNReal) (mem_support_iff.mpr hs)
  have h2 : 0 < w (AddMonoidAlgebra.coeff g s) := w.pos_iff.mpr hs
  exact_mod_cast lt_of_lt_of_le (Real.toNNReal_pos.mpr h2) h1

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma finsum_log_finitePlace_add_sum_log_norm_embedding {K : Type} [Field K] [NumberField K] {c : K}
    (hc : c ≠ 0) : ∑ᶠ v : FinitePlace K, Real.log (v c) + ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc, ← Real.log_finprod (fun v => v.pos_iff.mpr hc), FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv]
  ring


open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HeightUnique.formHeight_C_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (hN : 0 < N) (δ : ℕ)
    {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) {c : F} (hc : c ≠ 0) :
    _root_.GlobalTheory.ChowHt.formHeight δ w A (C c * f) = _root_.GlobalTheory.ChowHt.formHeight δ w A f := by
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.HeightUnique.exists_right_inv hw
  have hLf : _root_.GlobalTheory.ChowHt.linSubst w f ≠ 0 := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hfin : ∀ v : FinitePlace F, Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w (C c * f))) =
      Real.log (v c) + Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f)) := by
    intro v
    rw [_root_.GlobalTheory.HeightUnique.linSubst_C_mul, gaussAbs_C_mul_of_ne_zero v hc,
      Real.log_mul (v.pos_iff.mpr hc).ne' (gaussAbs_pos_of_ne_zero v hLf).ne']
  have harch : ∀ σ : F →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ (C c * f))) =
      Real.log ‖σ c‖ + _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ f)) := by
    intro σ
    have hQ : A σ * (A σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hA σ))
    have hmf : map σ f ≠ 0 := fun h0 => hf (map_injective σ σ.injective (by rw [h0, map_zero]))
    have hg := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hQ hmf
    have hgh := _root_.GlobalTheory.HeightUnique.linSubst_homog (A σ) (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring a f ha σ)
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
    have hC : (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) ≠ 0 := by simpa using hσc
    have hCh : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => 0) (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) :=
      (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt _ _).mpr fun _ => isWeightedHomogeneous_C _ _
    rw [map_mul, map_C, _root_.GlobalTheory.HeightUnique.linSubst_C_mul,
      _root_.ReciprocityTheory.MultiplicativeHeights.sphere_mean_mul_multihomogeneous _root_.ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B N (fun _ => 0) a _ _ hC hg hCh hgh]
    congr 1
    haveI := _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := B) hN
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [eval_C]
  have hsuppc : (Function.support fun v : FinitePlace F => Real.log (v c)).Finite := by
    simpa [_root_.GlobalTheory.HeightUnique.gaussAbs_C] using _root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (C c : MvPolynomial Unit F) (by simpa using hc)
  unfold _root_.GlobalTheory.ChowHt.formHeight
  congr 1
  simp_rw [hfin, harch]
  rw [finsum_add_distrib hsuppc (_root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hLf)]
  simp only [Finset.sum_add_distrib]
  linarith [finsum_log_finitePlace_add_sum_log_norm_embedding hc]

end GlobalTheory.HeightUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin unif IsUnitAt)

namespace GlobalTheory.GaussModulus

variable {E : Type} [Field E] [NumberField E]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 E)) (z : E) :
    Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 E)) {x : w.adicCompletion E} (hx : Valued.v x ≤ 1) (k : ℕ) :
    ∃ y : 𝓞 E, Valued.v (x - algebraMap E (w.adicCompletion E) (y : E)) ≤ WithZero.exp (-(k : ℤ)) := by
  set c : w.adicCompletion E := algebraMap E _ ((unif w ^ k : Eˣ) : E) with hcdef
  have hvc : Valued.v c = WithZero.exp (-(k : ℤ)) := by
    rw [hcdef, valued_algebraMap, valuation_unif_pow]
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hvc
    exact WithZero.exp_ne_zero hvc.symm
  let U : Set (w.adicCompletion E) :=
    (fun z => c⁻¹ * (z - x)) ⁻¹' ((w.adicCompletionIntegers E) : Set (w.adicCompletion E))
  have hU : IsOpen U := (Valued.isOpen_integer (w.adicCompletion E)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have hU' : U.Nonempty := ⟨x, by
    simp only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
    exact zero_mem _⟩
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open hU hU'
  have hb' : Valued.v (algebraMap E _ b - x) ≤ WithZero.exp (-(k : ℤ)) := by
    have h1 : Valued.v (c⁻¹ * (algebraMap E _ b - x)) ≤ 1 := hb
    rw [← mul_inv_cancel_left₀ hc0 (algebraMap E _ b - x), map_mul, hvc]
    exact mul_le_of_le_one_right' h1
  have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hb1 : w.valuation E b ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) b = (algebraMap E _ b - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ (hb'.trans hk1) hx
  obtain ⟨y, hy⟩ := w.exists_valuation_sub_lt_of_integer hb1 (Units.mk0 (WithZero.exp (-(k : ℤ))) WithZero.exp_ne_zero)
  refine ⟨y, ?_⟩
  have e2 : algebraMap E (w.adicCompletion E) (y : E) - x =
      algebraMap E _ ((y : E) - b) + (algebraMap E _ b - x) := by
    rw [map_sub]
    ring
  rw [Valuation.map_sub_swap, e2]
  refine Valuation.map_add_le _ ?_ hb'
  rw [valued_algebraMap]
  exact hy.le

end GlobalTheory.GaussModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh

section Unit

variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem expU_add (s t : MvPowerSeries σ C) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    PowerSeries.subst (s + t) (PowerSeries.exp C) =
      PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])
  have comp : ∀ p : MvPowerSeries (Fin 2) C, constantCoeff p = 0 →
      MvPowerSeries.subst ![s, t] (PowerSeries.subst p (PowerSeries.exp C)) =
        PowerSeries.subst (MvPowerSeries.subst ![s, t] p) (PowerSeries.exp C) := by
    intro p hp
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hst]
  have H := congrArg (MvPowerSeries.subst ![s, t]) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [MvPowerSeries.subst_mul hst, comp _ (by simp), comp _ (by simp), comp _ (by simp),
    MvPowerSeries.subst_add hst, MvPowerSeries.subst_X hst, MvPowerSeries.subst_X hst] at H
  simpa using H

theorem cc_expU (s : MvPowerSeries σ C) (hs : constantCoeff s = 0) :
    constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [map_pow, hs, zero_pow he]

theorem expU_zero : PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  have h := expU_add (0 : MvPowerSeries σ C) 0 (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_expU _ (by simp)]
    exact isUnit_one
  exact hu.mul_left_cancel (by rw [mul_one]; exact h.symm)

omit [CharZero C] in
theorem inv_int (v : AddValuation C (WithTop ℝ)) (U : MvPowerSeries σ C) (hU : MvIsInt v U)
    (h1 : constantCoeff U = 1) : ∃ U', MvIsInt v U' ∧ U * U' = 1 := by
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let U' : MvPowerSeries σ S := fun α => ⟨coeff α U, hU α⟩
  have hU' : map S.subtype U' = U := by ext α; rfl
  have hc : constantCoeff U' = ((1 : Sˣ) : S) := by
    apply Subtype.ext
    change coeff 0 U = 1
    rw [coeff_zero_eq_constantCoeff_apply, h1]
  refine ⟨map S.subtype (invOfUnit U' 1), fun α => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff α (invOfUnit U' 1)).2
  · rw [← hU', ← map_mul, mul_invOfUnit U' 1 hc, map_one]

theorem unitSt : UnitSt := by
  intro C _ _ v σ _
  have hexp0 := expU_zero (C := C) (σ := σ)
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, fun s t hs ht => expU_add s t hs ht, fun s hs => cc_expU s hs,
    fun U hU h1 => inv_int v U hU h1⟩
  · rw [hexp0]; exact Subring.one_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ)
  · rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], ?_⟩
    rw [expU_add s t hs0 ht0]
    exact Subring.mul_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ) hs ht
  · rintro s ⟨hs0, hs⟩
    have hn0 : constantCoeff (-s) = 0 := by simp [hs0]
    refine ⟨hn0, ?_⟩
    obtain ⟨U', hU', hm⟩ := inv_int v _ hs (cc_expU s hs0)
    have e : PowerSeries.subst (-s) (PowerSeries.exp C) * PowerSeries.subst s (PowerSeries.exp C) = 1 := by
      rw [← expU_add _ _ hn0 hs0, neg_add_cancel, hexp0]
    have : PowerSeries.subst (-s) (PowerSeries.exp C) = U' := by
      calc PowerSeries.subst (-s) (PowerSeries.exp C)
          = PowerSeries.subst (-s) (PowerSeries.exp C) * (PowerSeries.subst s (PowerSeries.exp C) * U') := by
            rw [hm, mul_one]
        _ = U' := by rw [← mul_assoc, e, one_mul]
    rw [this]; exact hU'

end Unit

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_normOne_of_strongApproximation : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | exact GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | (intros; apply GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion <;> assumption)
end

