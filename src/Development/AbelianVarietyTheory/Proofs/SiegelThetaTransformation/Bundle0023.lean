module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilAction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwd
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.SwdHeat

open GlobalTheory.SW.EisHeat

section Linear

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem isHeat_sum {ι : Type} [Fintype ι] {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i)) : IsHeat Ψ fun Z z z' => ∑ i, D i Z z z' := by
  have h := isHeat_tsum Ψ hD fun p hp => by
    have hc : ∀ i, ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
        ‖D i q.1 q.2.1 q.2.2‖ < ‖D i p.1 p.2.1 p.2.2‖ + 1 := fun i =>
      ((hD i).1.differentiableAt
        ((isOpen_dom Ψ).mem_nhds hp)).continuousAt.norm.eventually_lt_const (lt_add_one _)
    exact ⟨_, Filter.eventually_all.2 hc, fun i => ‖D i p.1 p.2.1 p.2.2‖ + 1,
      Summable.of_finite, fun i q hq => (hq i).le⟩
  simpa only [tsum_fintype] using h

theorem isHeat_sub {D D' : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D)
    (hD' : IsHeat Ψ D') : IsHeat Ψ fun Z z z' => D Z z z' - D' Z z z' := by
  have h := isHeat_sum Ψ (ι := Bool)
    (D := fun b => bif b then D else fun Z z z' => (-1) * D' Z z z') fun b => by
      cases b
      · exact isHeat_const_mul Ψ hD' _
      · exact hD
  simpa only [Fintype.sum_bool, cond_true, cond_false, neg_one_mul, ← sub_eq_add_neg] using h

end Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem isSB_member {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · have := (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
    simpa [mul_assoc] using this
  · have := h.per Λ hΛ x ((s : E) • y) fun a => h2 _ ((Base.mem_stdL (yᵀ a)).2 fun k => hy k a)
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at this
    exact this

end GlobalTheory.SW.SwdHeat


open GlobalTheory.SW.EisHeat GlobalTheory.SW.SwdHeat in
theorem GlobalTheory.SW.isHeat_swd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → IsHeat Ψ (swd Ψ M φ) := by
  intro E _ _ _ Ψ hΨ n N hn hN M R φ hφ
  haveI := (finite_cls_and_stab E n M hφ.pos.1).1
  haveI := Fintype.ofFinite (Cls E n M)
  have h := isHeat_sum Ψ (ι := Cls E n M) fun c => isHeat_const_mul Ψ
    (isHeat_sub Ψ (_root_.GlobalTheory.SW.isHeat_thH E Ψ hΨ n N _ (isSB_member hφ (Quot.out c).2))
      (_root_.GlobalTheory.SW.isHeat_eis E Ψ hΨ n N hn hN _ (isSB_member hφ (Quot.out c).2))) (wt M (Quot.out c).1 : ℂ)
  convert h using 3 with Z z
  funext z'
  exact finsum_eq_sum_of_fintype _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SwdTendstoZeroAtCusps
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}


omit [IsCMField E] in
theorem exists_den {α β : Type} [Fintype α] [Fintype β] (γ : Matrix α β E) :
    ∃ c : ℕ, 0 < c ∧ Den c γ := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : α × β => γ p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i j => ?_⟩
  have h := hy (γ i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rw [zsmul_eq_mul] at h
  rcases abs_choice y with e | e
  · rw [e]; exact h
  · rw [e, Int.cast_neg, neg_mul]; exact h.neg


omit [NumberField E] [IsCMField E] in
theorem exists_inv (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ a b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, b * a = 1 ∧ a *ᵥ v = Pi.single 0 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let b : Matrix (Fin (N + 1)) (Fin (N + 1)) E :=
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)
  have hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hb : IsUnit b.det := by
    rw [Matrix.det_permute', hd]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)
    exact (Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)
  have hbv : b *ᵥ Pi.single 0 1 = v := by
    ext k; simp [b]
  refine ⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩
  rw [← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]


omit [NumberField E] [IsCMField E] in
theorem pushZ_mem (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext i j
    simp [imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]
    field_simp
    linear_combination (-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq
  rw [e]
  exact (hZ τ).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))

theorem levi_mem {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1) :
    (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) ∈ UU E N := by
  have e : ccT (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 b := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  have h' : ccT a * ccT b = 1 := by rw [← Base.ccT_mul, h, Base.ccT_one]
  change ccT _ * _ * _ = _
  rw [e]
  simp [Matrix.J, Matrix.fromBlocks_multiply, h, h']

theorem hAct_levi (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (τ : Ψ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z τ = a.map τ.1 * Z τ * (a.map τ.1)ᴴ := by
  have h1 : b.map τ.1 * a.map τ.1 = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((b.map τ.1)ᴴ)⁻¹ = (a.map τ.1)ᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp [hAct, hDen, Base.ccT_map, h2]

theorem hAct_pushZ (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) (pushZ Ψ Z v t) =
      pushZ Ψ (hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z) (a *ᵥ v) t := by
  funext τ
  unfold pushZ
  rw [hAct_levi Ψ h, hAct_levi Ψ h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 3
  · funext i; simp [Matrix.mulVec, dotProduct]
  · funext i; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

theorem hFac_levi (Ψ : Finset (E →+* ℂ)) (a b : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) :
    hFac Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z (0 : CM Ψ n N) 0 =
      ∏ τ : Ψ, ((ccT b).map τ.1).det ^ n := by
  simp [hFac, hDen]


omit [IsCMField E] in
theorem colsIn_cons (Λ : Lt E n) (c : E) (x : Matrix (Fin n) (Fin N) E) :
    ColsIn Λ (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E)) ↔
      ColsIn Λ (c • x) := by
  unfold ColsIn
  rw [Fin.forall_fin_succ]
  have : (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E))ᵀ 0 = 0 := by
    ext k; simp
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨Λ.zero_mem, h⟩⟩

theorem admissibleLatticeFamily_restrictFirstColumnZero {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ) :
    admitted M R (fun Λ => dropF (φ Λ)) := by
  refine ⟨hφ.pos, ?_, ?_, ?_, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' m x
    unfold dropF
    rw [← hφ.equiv h hh Λ hΛ Λ' hΛ' m]
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]
  · intro Λ hΛ x hx
    exact (colsIn_cons Λ _ x).1 (hφ.supp Λ hΛ _ hx)
  · intro Λ hΛ x y hy
    have hy' := (colsIn_cons Λ 1 y).2 (by rwa [one_smul])
    rw [one_smul] at hy'
    unfold dropF
    rw [← hφ.per Λ hΛ (Matrix.of fun k => Fin.cons 0 (x k)) _ hy']
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  · intro Λ hΛ Λ' hΛ' ha x hx hx'
    exact hφ.loc Λ hΛ Λ' hΛ' ha _ ((colsIn_cons Λ _ x).2 hx) ((colsIn_cons Λ' _ x).2 hx')

theorem isSB_of_adm {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ}
    {φ : Fam E n N} (hφ : admitted M R φ) : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := by
  intro Λ hΛ
  obtain ⟨c, hc, hd⟩ := exists_den (1 : M2 E N)
  obtain ⟨_, _, -, h⟩ := _root_.GlobalTheory.SW.weil_level_and_sup E Ψ hΨ n N hn c R hc hφ.pos.2
  exact (h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1

theorem tendsto_first {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n)
    (hN : 4 * (N + 1) < n) (hsw : SWAt Ψ n N) {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ)
    {Z : CM Ψ (N + 1) (N + 1)} (hZ : Z ∈ Hn Ψ (N + 1)) :
    Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 0) := by
  have hsb := isSB_of_adm hΨ hn hφ
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hφ.pos.1).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hZ' : dropZ Ψ Z ∈ Hn Ψ N := ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N 0 isSB_zero).2 Z hZ).1
  rw [← hsw M R _ (admissibleLatticeFamily_restrictFirstColumnZero hφ) _ hZ']
  unfold swd classSum
  simp only [finsum_eq_sum_of_fintype]
  refine tendsto_finsetSum _ fun c _ => Tendsto.const_mul _ (Tendsto.sub ?_ ?_)
  · exact ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ (hsb _ (Quot.out c).2)).2 Z hZ).2.2 0 0
  · exact _root_.GlobalTheory.SW.eis_siegel_operator E Ψ hΨ n N hn hN _ (hsb _ (Quot.out c).2) Z hZ

end GlobalTheory.SW.Cusp


open GlobalTheory.SW.Cusp in
theorem GlobalTheory.SW.swd_tendsto_zero_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  intro E _ _ _ Ψ hΨ n N hn hN hsw M R φ hφ v hv Z hZ
  obtain ⟨a, b, hba, hav⟩ := exists_inv v hv
  have hγ := levi_mem hba
  obtain ⟨c, hc, hd⟩ := exists_den (Matrix.fromBlocks a 0 0 (ccT b) : M2 E (N + 1))
  obtain ⟨R', hR'⟩ := _root_.GlobalTheory.SW.weil_admissible E Ψ hΨ n (N + 1) hn c R hc
  have hact := (unitary_act_halfSpace E Ψ (N + 1) _ hγ).2 Z hZ
  have hlim := tendsto_first hΨ hn hN hsw (hR' M φ hφ _ hγ hd) hact.2.1
  have hne : (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    simpa [hDen] using (hact.1 τ).1
  have h2 := hlim.const_mul (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h3 := (_root_.GlobalTheory.SW.swd_automorphy_linear E Ψ hΨ n (N + 1) hn hN M φ hφ.pos.1 (isSB_of_adm hΨ hn hφ) _
    (pushZ_mem Ψ hZ v ht)).1 _ hγ
  rw [hAct_pushZ Ψ hba, hav, hFac_levi] at h3
  rw [h3, inv_mul_cancel_left₀ hne]
end

