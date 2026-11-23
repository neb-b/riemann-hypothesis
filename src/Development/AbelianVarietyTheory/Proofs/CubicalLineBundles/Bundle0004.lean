module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace AppellHumbertTrivial

theorem _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C a : ℝ) (ha : a < 0)
    (h : ∀ t, ‖f t‖ ≤ C * Real.exp (‖t‖ ^ 2 * a)) : f 0 = 0 := by
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨t, rfl⟩
    have he : Real.exp (‖t‖ ^ 2 * a) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) ha.le)
    have hp := Real.exp_pos (‖t‖ ^ 2 * a)
    refine (h t).trans ?_
    rcases le_or_gt 0 C with hC | hC
    · exact (mul_le_of_le_one_right hC he).trans (le_max_left _ _)
    · nlinarith [le_max_right C 0]
  have hconst : ∀ t, f 0 = f t := fun t => hf.apply_eq_apply_of_bounded hbd 0 t
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * a) Filter.atTop Filter.atBot :=
    ((Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg ha
  have hlim : Filter.Tendsto (fun n : ℕ => C * Real.exp ((n : ℝ) ^ 2 * a)) Filter.atTop
      (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hle : ∀ n : ℕ, ‖f 0‖ ≤ C * Real.exp ((n : ℝ) ^ 2 * a) := fun n => by
    rw [hconst (n : ℂ)]
    simpa using h (n : ℂ)
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

theorem _root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {F : Type} [NormedAddCommGroup F]
    (φ : (Fin g → ℂ) → F) (hφ : Continuous φ)
    (hp : ∀ (l : Λ) z, φ (z + l) = φ z) : Bornology.IsBounded (Set.range φ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  exact (IsZLattice.isCompact_range_of_periodic Λ φ hφ
    (fun z w hw => hp ⟨w, hw⟩ z)).isBounded

variable {g : ℕ}

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_left (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [add_dotProduct]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_left (B : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • x) w = t * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [smul_dotProduct, smul_eq_mul]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right (B : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (t • x) = star t * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_swap {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x = star (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply,
    star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hB.apply j i]
  ring

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.continuous_hermForm_self (B : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  fun_prop

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian)
    (x y : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) (x + y)).re
      = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x x).re + 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y).re + (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y y).re := by
  rw [_root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_left, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right,
    _root_.GlobalTheory.AppellHumbertTrivial.hermForm_swap hB y x]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

end AppellHumbertTrivial


variable {g : ℕ} in
theorem _root_.GlobalTheory.appellHumbert_trivial_of_nowhere_vanishing :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  ∀ (B : Matrix (Fin g) (Fin g) ℂ) (c : Λ → ℂ) (r : (Fin g → ℂ) → ℂ), B.IsHermitian → (∀ l, ‖c l‖ = 1) →
  Differentiable ℂ r → (∀ z, r z ≠ 0) →
  (∀ (l : Λ) z, r (z + l) = c l * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l) * r z) →
  B = 0 ∧ (∀ l, c l = 1) ∧ ∀ z, r z = r 0 := by
  intro g Λ _ hΛ B c r hB hc hr hr0 hper
  have hnorm : ∀ (l : Λ) z, ‖r (z + l)‖ = Real.exp (Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l).re +
      Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l).re) * ‖r z‖ := by
    intro l z
    rw [hper l z, norm_mul, norm_mul, hc, one_mul, Complex.norm_exp]
    congr 2
    simp
  have hφper : ∀ (l : Λ) z, ‖r (z + l)‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (z + l) (z + l)).re)
      = ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro l z
    rw [hnorm, _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB, mul_comm (Real.exp _) ‖r z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hφcont : Continuous fun z => ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
    hr.continuous.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_re.comp (_root_.GlobalTheory.AppellHumbertTrivial.continuous_hermForm_self B))))
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hφcont hφper)
  have hup : ∀ z, ‖r z‖ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re)) *
          Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hψcont : Continuous fun z => (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ :=
    hφcont.inv₀ fun z => (mul_pos (norm_pos_iff.2 (hr0 z)) (Real.exp_pos _)).ne'
  obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hψcont
      fun l z => congrArg (·⁻¹) (hφper l z))
  have hlow : ∀ z, ‖r z‖⁻¹ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM' _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖⁻¹ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ *
          Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_inv, mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]
      _ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hscale : ∀ (t : ℂ) v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • v) (t • v)).re = ‖t‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re := by
    intro t v
    rw [_root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_left, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right, ← mul_assoc]
    have ht : t * star t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [ht, Complex.re_ofReal_mul]

  have hq0 : ∀ v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re = 0 := by
    intro v
    have hd : Differentiable ℂ fun t : ℂ => r (t • v) := hr.comp (differentiable_id.smul_const v)
    rcases lt_trichotomy (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re 0 with hneg | hzero | hpos
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => r (t • v)) hd M
        (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re) (mul_neg_of_pos_of_neg (by positivity) hneg)
        (fun t => by
          refine (hup (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
    · exact hzero
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => (r (t • v))⁻¹)
        (hd.inv fun t => hr0 _) M' (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re)
        (by nlinarith [Real.pi_pos])
        (fun t => by
          rw [norm_inv]
          refine (hlow (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
  have hH : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y = 0 := by
    intro x y
    have h1 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x y
    have h2 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x (Complex.I • y)
    simp only [hq0] at h1
    rw [hq0, hq0, hq0, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right] at h2
    refine Complex.ext ?_ ?_
    · simp only [Complex.zero_re]
      linarith
    · simp [Complex.star_def] at h2
      simpa using h2
  have hB0 : B = 0 := by
    ext i j
    have h := hH (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm at h
    simpa using h
  have hbdd : Bornology.IsBounded (Set.range r) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [hq0] using hup z
  have hconst : ∀ z, r z = r 0 := fun z => hr.apply_eq_apply_of_bounded hbdd z 0
  refine ⟨hB0, fun l => ?_, hconst⟩
  have h := hper l 0
  simp only [hH, hconst (0 + (l : Fin g → ℂ)), mul_zero, add_zero, Complex.exp_zero, mul_one] at h
  exact mul_right_cancel₀ (hr0 0) (h.symm.trans (one_mul _).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DenseClosedPoints
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')

namespace GlobalTheory.SchemeHomsFromPoints

theorem dense_closedPoints {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] :
    Dense (closedPoints X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  rw [dense_iff_closure_eq]
  exact closure_closedPoints

theorem hom_ext_of_points {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    [Y.IsSeparated] (f g : X ⟶ Y) (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g (terminal.from Y) (closedPoints X)
    (dense_closedPoints p) ?_ (terminal.hom_ext _ _)
  intro x hx
  have h := H (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)
  rw [← cancel_epi (Spec.map (residueFieldIsoBase p x hx).hom)]
  simpa only [pointOfClosedPoint, Category.assoc] using h

theorem eq_zero_of_points {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (W : X.Opens) (h : Γ(X, W))
    (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∀ e : ⊤ ≤ x ⁻¹ᵁ W, valAt x W e h = 0) : h = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hne' : ((X.basicOpen h : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hne (TopologicalSpace.Opens.ext h0)
  obtain ⟨x, hx, hxc⟩ := (dense_closedPoints p).inter_open_nonempty _ (X.basicOpen h).isOpen hne'
  have e : ⊤ ≤ (pointOfClosedPoint p x hxc) ⁻¹ᵁ W := by
    intro a _
    change pointOfClosedPoint p x hxc a ∈ W
    exact (pointOfClosedPoint_apply p x hxc a).symm ▸ X.basicOpen_le h hx
  have h1 := H _ (pointOfClosedPoint_comp p x hxc) e
  have h2 : ((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h1
  have h3 := Scheme.basicOpen_appLE (pointOfClosedPoint p x hxc) ⊤ W e h
  have h4 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
      (Spec (CommRingCat.of ℂ)).basicOpen (((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h) := by
    have h5 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
        ⊤ ⊓ (pointOfClosedPoint p x hxc) ⁻¹ᵁ X.basicOpen h := by
      refine ⟨trivial, ?_⟩
      change pointOfClosedPoint p x hxc _ ∈ X.basicOpen h
      exact (pointOfClosedPoint_apply p x hxc _).symm ▸ hx
    rw [← h3] at h5
    exact h5
  rw [h2, Scheme.basicOpen_zero] at h4
  exact h4

theorem lift_toSpecΓ {X : Scheme.{0}} {R : CommRingCat.{0}} (W : X.Opens) (x : Spec R ⟶ X)
    (x' : Spec R ⟶ W) (hx : x' ≫ W.ι = x) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    x' ≫ W.toSpecΓ = Spec.map (x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso R).hom) := by
  have h1 : x.resLE W ⊤ e = (⊤ : (Spec R).Opens).ι ≫ x' := by
    rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, hx]
  have : IsIso (⊤ : (Spec R).Opens).ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  rw [← cancel_epi (⊤ : (Spec R).Opens).ι, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    ← Category.assoc, ← h1, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]

theorem range_subset {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Set.range x ⊆ Set.range W.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact e trivial

theorem top_le_of_lift {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (x' : T ⟶ W)
    (hx : x' ≫ W.ι = x) : ⊤ ≤ x ⁻¹ᵁ W := by
  subst hx
  intro t _
  exact (x'.base t).2

noncomputable def ev {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Γ(X, W) ⟶ CommRingCat.of ℂ :=
  x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom

theorem valAt'_eq {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) (h : Γ(X, W)) :
    valAt' x W h = (ev x W e).hom h := by
  rw [valAt', dite_eq_left e]
  rfl

theorem exists_local {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    (W : X.Opens) (D : Y.Opens) (hD : IsAffineOpen D)
    (hWD : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hf : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (x' : Sp ℂ ⟶ W), x' ≫ W.ι = ex w → x' ≫ g = ey w := by
  choose F hF using hf
  have hF' : ∀ f w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom (F f) = (ev (ey w) D (hWD w e)).hom f := by
    intro f w e
    rw [← valAt'_eq, ← valAt'_eq]
    exact hF f w e
  have inj : ∀ a b : Γ(X, W), (∀ w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom a = (ev (ex w) W e).hom b) → a = b := by
    intro a b hab
    rw [← sub_eq_zero]
    refine eq_zero_of_points p W _ ?_
    intro x hx e
    obtain ⟨w, rfl⟩ := hex x hx
    change (ev (ex w) W e).hom (a - b) = 0
    rw [map_sub, hab w e, sub_self]
  let φ : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := F
      map_one' := inj _ _ fun w e => by rw [hF', map_one, map_one]
      map_mul' := fun a b => inj _ _ fun w e => by rw [hF', map_mul, map_mul, hF', hF']
      map_zero' := inj _ _ fun w e => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => inj _ _ fun w e => by rw [hF', map_add (f := _), map_add (f := _), hF', hF'] }
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hD.fromSpec, ?_⟩
  intro w x' hx'
  have e := top_le_of_lift W (ex w) x' hx'
  have e' := hWD w e
  have hy' := IsOpenImmersion.lift_fac D.ι (ey w) (range_subset D (ey w) e')
  have h1 : x' ≫ W.toSpecΓ = Spec.map (ev (ex w) W e) := lift_toSpecΓ W (ex w) x' hx' e
  have h2 : _ ≫ D.toSpecΓ = Spec.map (ev (ey w) D e') := lift_toSpecΓ D (ey w) _ hy' e'
  have h3 : CommRingCat.ofHom φ ≫ ev (ex w) W e = ev (ey w) D e' := by
    ext f
    exact hF' f w e
  rw [← Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, h3, ← h2, Category.assoc,
    hD.toSpecΓ_fromSpec, hy']

theorem exists_hom {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (H : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
        valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  choose W D hD hW hWD hf using H
  choose g hg using fun z => exists_local p ex ey hex (W z) (D z) (hD z) (hWD z) (hf z)
  have hcov : TopologicalSpace.IsOpenCover W := by
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x₀ _
    by_contra hx₀
    have hcl : IsClosed ((iSup W : X.Opens) : Set X)ᶜ := (iSup W).isOpen.isClosed_compl
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints ⟨x₀, hx₀⟩ hcl.isLocallyClosed
    obtain ⟨z, hz⟩ := hex _ (pointOfClosedPoint_comp p x hxc)
    apply hx
    have h1 : ex z (IsLocalRing.closedPoint ℂ) ∈ W z :=
      hW z (show (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ from trivial)
    have h2 : ex z (IsLocalRing.closedPoint ℂ) = x := by
      rw [hz]
      exact pointOfClosedPoint_apply p x hxc _
    exact le_iSup W z (h2 ▸ h1)
  have hglue : ∀ i j, pullback.fst (W i).ι (W j).ι ≫ g i = pullback.snd (W i).ι (W j).ι ≫ g j := by
    intro i j
    have : IsReduced (pullback (W i).ι (W j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (W i).ι (W j).ι ≫ (W i).ι)
    refine hom_ext_of_points (pullback.fst (W i).ι (W j).ι ≫ (W i).ι ≫ p) _ _ ?_
    intro x hx
    obtain ⟨w, hw⟩ := hex (x ≫ pullback.fst (W i).ι (W j).ι ≫ (W i).ι) (by simpa using hx)
    rw [← Category.assoc, ← Category.assoc, hg i w _ (by rw [hw, Category.assoc]),
      hg j w _ (by rw [hw, Category.assoc, pullback.condition])]
  refine ⟨(X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue, fun z => ?_⟩
  have h1 := IsOpenImmersion.lift_fac (W z).ι (ex z) (range_subset (W z) (ex z) (hW z))
  have h2 : (W z).ι ≫ (X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue = g z :=
    Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover W hcov) g hglue z
  rw [← hg z z _ h1, ← h2, ← Category.assoc, h1]

end GlobalTheory.SchemeHomsFromPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EigenNorm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_left (z z' w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z + z') w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z' w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_right (z w w' : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (w + w') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w' := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_left (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (r • z) w = r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_right (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (r • w) = starRingEnd ℂ r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm w z = starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [Pi.star_apply, Complex.star_def]
  ring

theorem conj_eq_neg_of_sq {ρ : ℂ} {d : ℕ} (hd : d ≠ 0) (h : ρ ^ 2 = -(d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : ρ.re * ρ.im = 0 := by linarith [mul_comm ρ.re ρ.im]
  have h4 : ρ.re = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rw [h] at h1; nlinarith [mul_self_nonneg ρ.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.EigenNorm
end

