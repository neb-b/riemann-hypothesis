module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.HighestWeightKernel

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem inner_compact (hU : IsInfUnitary ε E) {a b : Fin n} (h : ε a = ε b) (x y : V) :
    ⟪E b a x, y⟫_ℂ = ⟪x, E a b y⟫_ℂ := by
  have := hU b a x y
  simpa [adjSign, h.symm] using this

theorem exists_hull (hL : LocFin ε E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ IsKStableSub ε E Y ∧ W ≤ Y := by
  classical
  choose S hSfin hSmem hSk using hL
  let bW := Module.finBasis ℂ W
  let Y : Submodule ℂ V := ⨆ i, S (bW i : V)
  haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _
  refine ⟨Y, Submodule.finite_iSup _, ?_, ?_⟩
  · intro a b hab v hv
    refine Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_
    · intro i x hx
      exact (le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)
    · simp
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  · intro w hw
    have hrep := bW.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V) := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw']
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    exact (le_iSup (fun i => S (bW i : V)) i) (hSmem _)

theorem inner_casimirK (hU : IsInfUnitary ε E) (w : V) :
    ⟪w, casimirK ε E w⟫_ℂ =
      ((∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))
  have hba : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]
  first
    | rfl
    | simp
    | norm_cast

theorem mem_ker_iff (μ : ℝ) (x : V) :
    x ∈ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V)) ↔ casimirK ε E x = (μ : ℂ) • x := by
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem sq_le_of_khw (hU : IsInfUnitary ε E) {w : V} (hw0 : w ≠ 0) {μ : ℝ} (hwμ : casimirK ε E w = (μ : ℂ) • w)
    {Λ : Fin n → ℝ} (hkw : IsKHWVec ε E Λ w) : (∑ a, Λ a ^ 2) ≤ μ := by
  have h1 := inner_casimirK hU w
  rw [hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    exact h1
  have h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a) := by simp
    have hle := Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem
    have hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2 := by
      rw [hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linarith
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [← Finset.sum_mul] at h3
  nlinarith

theorem mem_of_eig (hgl : IsGlRep E) (hU : IsInfUnitary ε E) (hL : LocFin ε E)
    (h3 : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
      ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w)
    (hint : ∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z)
    {Y : Submodule ℂ V} (hYk : IsKStableSub ε E Y) {μ : ℝ}
    (hY : ∀ (w : V) (Λ : Fin n → ℤ), IsKHWVec ε E (fun a => ((Λ a : ℤ) : ℝ)) w →
      (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ μ → w ∈ Y)
    {v : V} (hv : Eig ε E μ v) : v ∈ Y := by
  classical
  have key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k →
      IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Z hZf hZk hZs hZc
      by_cases hZ0 : Z = ⊥
      · rw [hZ0]
        exact bot_le
      obtain ⟨w, Λ, hwZ, hw0, hkw⟩ := h3 Z hZf hZs hZ0
      have hΛ : ∀ a, ∃ z : ℤ, Λ a = z := fun a => hint w a (Λ a) hw0 (hkw.1 a)
      choose Λz hΛz using hΛ
      have hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w := by
        have : Λ = fun a => ((Λz a : ℤ) : ℝ) := funext hΛz
        rw [← this]
        exact hkw
      have hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ := sq_le_of_khw hU hw0 (hZc w hwZ) hkw'
      have hwY : w ∈ Y := hY w Λz hkw' hsq
      let Kw : Submodule ℂ V := sInf {T | w ∈ T ∧ IsKStableSub ε E T}
      have hKwS : IsKStableSub ε E Kw := by
        intro a b hab x hx
        rw [Submodule.mem_sInf] at hx ⊢
        intro T hT
        exact hT.2 a b hab x (hx T hT)
      have hwKw : w ∈ Kw := Submodule.mem_sInf.2 (fun T hT => hT.1)
      have hKwZ : Kw ≤ Z := sInf_le ⟨hwZ, hZs⟩
      have hKwY : Kw ≤ Y := sInf_le ⟨hwY, hYk⟩
      haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ
      have hZ'lt : Kwᗮ ⊓ Z < Z := by
        refine lt_of_le_of_ne inf_le_right (fun h => ?_)
        have hwZ' : w ∈ Kwᗮ ⊓ Z := by
          rw [h]
          exact hwZ
        have h0 : ⟪w, w⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1
        exact hw0 (inner_self_eq_zero.1 h0)
      haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z) := by
        intro a b hab x hx
        refine ⟨?_, hZs a b hab x hx.2⟩
        show E a b x ∈ Kwᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← inner_compact hU hab]
        exact Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1
      have hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k :=
        hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt
      have hZ'le : Kwᗮ ⊓ Z ≤ Y :=
        ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)
      have hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z :=
        Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ
      rw [← hsplit]
      exact sup_le hKwY hZ'le
  obtain ⟨S, hSf, hvS, hSk⟩ := hL v
  haveI : FiniteDimensional ℂ S := hSf
  let Z : Submodule ℂ V := S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))
  have hZk : IsKStableSub ε E Z := by
    intro a b hab x hx
    refine ⟨hSk a b hab x hx.1, ?_⟩
    have hx2 := (mem_ker_iff μ x).1 hx.2
    refine (mem_ker_iff μ _).2 ?_
    have hc := ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab
    have := congrArg (fun U : Module.End ℂ V => U x) hc
    simp only [Module.End.mul_apply] at this
    rw [this, hx2, map_smul]
  exact key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk
    (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩

end PositivityTheory.CW.HighestWeightKernel

namespace PositivityTheory.CW

open PositivityTheory.CW.HighestWeightKernel

theorem k_types_finite_of_highest_weight (h : KStableHighestWeightVector) : KTypesBoundedFinite := by
  classical
  intro n ε V _ _ E hgl hU hL hfinHW hint R
  let F : Set (Fin n → ℤ) := {Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}
  have hFfin : F.Finite := by
    refine (Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
    intro Λ hΛ a _
    have hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R := by
      refine le_trans ?_ hΛ
      exact Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ a)
    have h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq (Λ a)
    have h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by
      have := Int.le_self_sq (-(Λ a))
      rw [neg_sq] at this
      exact_mod_cast this
    have hc := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  haveI : Finite F := hFfin.to_subtype
  let W0 : Submodule ℂ V :=
    ⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}
  haveI : ∀ Λ : F, FiniteDimensional ℂ
      (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _
  haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _
  obtain ⟨Y, hYf, hYk, hWY⟩ := exists_hull hL W0
  haveI : FiniteDimensional ℂ Y := hYf
  refine Submodule.finiteDimensional_of_le (S₂ := Y) ?_
  refine Submodule.span_le.2 ?_
  rintro v ⟨μ, hμR, hv⟩
  refine mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv
  intro w Λ hkw hsq
  have hΛF : Λ ∈ F := le_trans hsq hμR
  exact hWY ((le_iSup (fun Λ : F => Submodule.span ℂ
    {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive
section
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionLinear
section
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegativeSymmetric

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hU a b (E b a x) y, hU b a x (E b a y)]
  simp [adjSign, hab]

theorem re_inner_casK_nonneg (hU : IsInfUnitary ε E) (x : V) : 0 ≤ (⟪x, casimirK ε E x⟫_ℂ).re := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
  have h := hU b a x (E b a x)
  simp only [ReciprocityTheory.ChartRestriction.DS.adjSign, hb', if_true, one_mul] at h
  rw [← h]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := E b a x))

theorem eig_nonneg (hU : IsInfUnitary ε E) {μ : ℝ} {v : V} (hv : v ≠ 0) (h : Eig ε E μ v) : 0 ≤ μ := by
  have h2 := re_inner_casK_nonneg hU v
  rw [show casimirK ε E v = (μ : ℂ) • v from h, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : 0 ≤ μ * ‖v‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h2
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  by_contra hμ
  push_neg at hμ
  nlinarith [mul_neg_of_neg_of_pos hμ hn]

end PositivityTheory.CW.CasimirNonnegativeSymmetric

namespace PositivityTheory.CW

open CasimirNonnegativeSymmetric in
theorem e3a : CasimirPowerSurjectiveSymmetric := by
  intro k ε V _ _ E _ hU hM m
  set a := 1 + casimirK ε E with ha_def
  have ha : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
    intro x y
    simp only [ha_def, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right,
      casK_symm hU]
  have hsymm : ∀ j : ℕ, ∀ x y : V, ⟪(a ^ j) x, y⟫_ℂ = ⟪x, (a ^ j) y⟫_ℂ := by
    intro j
    induction j with
    | zero => intro x y; simp
    | succ j ih =>
      intro x y
      calc ⟪(a ^ (j + 1)) x, y⟫_ℂ = ⟪(a ^ j) (a x), y⟫_ℂ := by rw [pow_succ, Module.End.mul_apply]
        _ = ⟪a x, (a ^ j) y⟫_ℂ := ih _ _
        _ = ⟪x, a ((a ^ j) y)⟫_ℂ := ha _ _
        _ = ⟪x, (a ^ (j + 1)) y⟫_ℂ := by rw [pow_succ', Module.End.mul_apply]
  refine ⟨?_, hsymm m⟩
  have hrange : LinearMap.range (a ^ m) = ⊤ := by
    rw [eq_top_iff, ← hM.span, Submodule.span_le]
    rintro v ⟨μ, hv⟩
    show v ∈ LinearMap.range (a ^ m)
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hμ : 0 ≤ μ := eig_nonneg hU h0 hv
    have h1 : a v = (1 + (μ : ℂ)) • v := by
      simp [ha_def, add_smul, show casimirK ε E v = (μ : ℂ) • v from hv]
    have hav : ∀ j : ℕ, (a ^ j) v = ((1 + (μ : ℂ)) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, ← pow_succ']
    have hne1 : (1 + (μ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast (by linarith : (0 : ℝ) < 1 + μ).ne'
    have hne : (1 + (μ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ hne1
    refine LinearMap.mem_range.2 ⟨((1 + (μ : ℂ)) ^ m)⁻¹ • v, ?_⟩
    rw [map_smul, hav, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact LinearMap.range_eq_top.1 hrange

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SeminormApproximation
section
open scoped InnerProductSpace
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary adjSign)

namespace PositivityTheory.CW.EigenOrthogonalForm

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_symm (hu : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hu a b, hu b a]
  simp [adjSign, hab]

theorem inner_eq_zero_of_eig (hu : IsInfUnitary ε E) {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : ⟪v, y⟫_ℂ = 0 := by
  have h := cas_symm hu v y
  rw [hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

theorem B_eq_zero (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y))
    {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : B v y = 0 := by
  have h := hB v y
  rw [hv, hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
    RingHom.id_apply] at h
  have h2 : ((μ : ℂ) - μ') * B v y = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) hne
  · exact h3

end PositivityTheory.CW.EigenOrthogonalForm

namespace PositivityTheory.CW

open EigenOrthogonalForm in
theorem e2c : CasimirPairingBound := by
  intro n ε V _ _ E _ _ hM Q hQ η
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y}
      add_mem' := by
        rintro a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩
        refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩
        rw [inner_add_left, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha y) (hb y))
      zero_mem' := ⟨0, le_rfl, fun y => by simp⟩
      smul_mem' := by
        rintro c a ⟨C, h, ha⟩
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩
        rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }
  suffices hS : S = ⊤ by
    have hη : η ∈ S := hS ▸ Submodule.mem_top
    exact hη
  rw [eq_top_iff, ← hM.span, Submodule.span_le]
  rintro w ⟨μ, hw⟩
  let W : Submodule ℂ V := Module.End.eigenspace (casimirK ε E) (μ : ℂ)
  have hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v := fun v => Module.End.mem_eigenspace_iff
  haveI : FiniteDimensional ℂ W := by
    haveI := hM.fin μ
    have hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v} :=
      fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩
    exact Submodule.finiteDimensional_of_le hle
  let P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop := fun B =>
    (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y
  let G : Set (Module.Dual ℂ W) := {g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}
  have hspan : Submodule.span ℂ G = ⊤ := by
    have hco : (Submodule.span ℂ G).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      by_contra hne
      have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨B, hB1, hB2, hB3⟩ := hQ y hy0
      have hg : (B y).comp W.subtype ∈ Submodule.span ℂ G :=
        Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩
      exact hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco,
      Submodule.dualAnnihilator_bot]
  have hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G := hspan ▸ Submodule.mem_top
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hl
  choose B hB v hv hgv using fun i => (g i).2
  have hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i) := by
    refine LinearMap.ext_on hM.span ?_
    rintro y ⟨lam, hy⟩
    by_cases hμ : lam = μ
    · subst hμ
      have hyW : y ∈ W := (hWmem y).2 hy
      have := LinearMap.congr_fun hfg ⟨y, hyW⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply,
        Submodule.subtype_apply] at this
      rw [← this, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    · have h0 : ⟪w, y⟫_ℂ = 0 := inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy
      have h1 : ∀ i, B i (v i) y = 0 := fun i =>
        B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy
      rw [LinearMap.sum_apply, innerₛₗ_apply_apply, h0]
      simp [h1]
  show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y
  refine ⟨∑ i, ‖f i‖ * Q (v i),
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩
  have hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y := by
    have h := LinearMap.congr_fun hid y
    rw [innerₛₗ_apply_apply, LinearMap.sum_apply] at h
    rw [h]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hwy, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)

end PositivityTheory.CW
end

