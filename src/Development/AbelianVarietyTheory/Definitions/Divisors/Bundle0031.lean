module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KerInfIntegrableOfMemRspan
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.RapidModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_mul (x y : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(x * y) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun l _ => ?_).trans_eq (by simp))
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_le_pi_norm (toL x i) l).trans (norm_le_pi_norm (toL x) i))
    ((norm_le_pi_norm (toL y l) j).trans (norm_le_pi_norm (toL y) l)) (norm_nonneg _) (norm_nonneg _))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_le (x y : GL (Fin a) (Cinf E)) : height (x * y) ≤ (1 + 2 * a) * (height x * height y) := by
  have h1 := norm_toL_mul x.val y.val
  have h2 := norm_toL_mul (y⁻¹).val (x⁻¹).val
  have hx := one_le_height x
  have hy := one_le_height y
  have a1 : ‖toL x.val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL (x⁻¹).val)]
  have a2 : ‖toL (x⁻¹).val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL x.val)]
  have b1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have b2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have c1 : ‖toL x.val‖ * ‖toL y.val‖ ≤ height x * height y := mul_le_mul a1 b1 (norm_nonneg _) (by linarith)
  have c2 : ‖toL (y⁻¹).val‖ * ‖toL (x⁻¹).val‖ ≤ height x * height y := by
    rw [mul_comm]; exact mul_le_mul a2 b2 (norm_nonneg _) (by linarith)
  have c0 : 1 ≤ height x * height y := one_le_mul_of_one_le_of_one_le hx hy
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have e : height (x * y) = 1 + ‖toL (x.val * y.val)‖ + ‖toL ((y⁻¹).val * (x⁻¹).val)‖ := by
    unfold height; rw [mul_inv_rev]; rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left c1 ha, mul_le_mul_of_nonneg_left c2 ha]


variable (E a) in
def modGr : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ g, Measurable (chart F g) ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N}
  add_mem' := fun {F G} hF hG g => by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    obtain ⟨m2, C', N', h0', h2⟩ := hG g
    refine ⟨?_, C + C', N + N', by positivity, fun y => ?_⟩
    · have e : chart (F + G) g = fun x => chart F g x + chart G g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.add m2
    · have hy := one_le_height y
      have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      refine (norm_add_le _ _).trans ?_
      nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' g := ⟨by
      have e : chart (0 : GA E a → ℂ) g = fun _ => 0 := by funext x; simp [chart]
      rw [e]; exact measurable_const, 0, 0, le_rfl, fun y => by simp⟩
  smul_mem' c F hF g := by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    refine ⟨?_, ‖c‖ * C, N, by positivity, fun y => ?_⟩
    · have e : chart (c • F) g = fun x => c * chart F g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.const_mul c
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem integrable_of_modGr {F : GA E a → ℂ} (hF : F ∈ modGr E a) {X : Type} [MeasurableSpace X] {ν : Measure X}
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν := by
  obtain ⟨m, C, N, h0, hC⟩ := hF g
  have h : Measurable fun x => toL (γ x).val := hk.2.1
  have e : (fun x => F (g * infGL E a (γ x))) = fun x => chart F g (toL (γ x).val) :=
    funext fun x => (chart_val F g (γ x)).symm
  have hm : Measurable fun x => F (g * infGL E a (γ x)) := by rw [e]; exact m.comp h
  refine ((hk.2.2 N).const_mul C).mono' (hk.1.mul hm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
        mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_le_modGr (π : CuspSub E a) : rspan π ≤ modGr E a := by
  refine rspan_le (fun φ hφ g => ⟨measurable_chart φ.2 g, ?_⟩) (fun F hF h g => ?_) fun F hF X _ ν _ k γ hk g => ?_
  · obtain ⟨C, N, hC⟩ := (π.cusp φ hφ).1.growth g
    exact ⟨|C|, N, abs_nonneg C, fun y => (hC y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [one_le_height y]) N))⟩
  · rw [← infGL_mul_finGL h]
    set y := Matrix.GeneralLinearGroup.map (pInf E) h
    set k := Matrix.GeneralLinearGroup.map (pFin E) h
    obtain ⟨m, C, N, h0, hC⟩ := hF (g * finGL E a k)
    refine ⟨?_, C * ((1 + 2 * a) * height y) ^ N, N, by have := one_le_height y; positivity, fun z => ?_⟩
    · have e : (fun x => F (x * (infGL E a y * finGL E a k))) =
          fun x => (fun x => F (x * finGL E a k)) (x * infGL E a y) := by
        funext x; simp only [mul_assoc]
      rw [e, chart_rt_inf (fun x => F (x * finGL E a k)), chart_rt_fin]
      exact m.comp (rmul (toL y.val)).continuous.measurable
    · have e : g * infGL E a z * (infGL E a y * finGL E a k) = g * finGL E a k * infGL E a (z * y) := by
        rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
      change ‖F (g * infGL E a z * (infGL E a y * finGL E a k))‖ ≤ _
      rw [e]
      refine (hC _).trans ?_
      rw [mul_assoc C, ← mul_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y)]) ?_ N) h0
      exact (height_mul_le z y).trans_eq (by ring)
  · obtain ⟨m, C, N, h0, hC⟩ := hF g
    refine ⟨?_, C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, fun z => ?_⟩
    · have e : chart (kerInf ν k γ F) g = fun x => ∫ t, k t * chart F g (toL (Matrix.of x * (γ t).val)) ∂ν := by
        funext x
        by_cases h : IsUnit (Matrix.of x)
        · obtain ⟨u, hu⟩ := h
          have hx : x = (toL u.val) := hu.symm
          rw [hx, chart_val, kerInf]
          congr 1
          funext t
          rw [mul_assoc, ← map_mul, ← chart_val F g]
          rfl
        · have h' : ∀ t, ¬ IsUnit (Matrix.of (toL (Matrix.of x * (γ t).val))) :=
            fun t h' => h ((Units.isUnit_mul_units _ (γ t)).1 h')
          simp only [chart, dif_neg h, dif_neg (h' _), mul_zero, integral_zero]
      rw [e]
      have hγ : Measurable fun x => toL (γ x).val := hk.2.1
      have hm : Measurable fun p : Lie E a × X => toL (Matrix.of p.1 * (γ p.2).val) := by
        refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
        change Measurable fun p : Lie E a × X => (Matrix.of p.1 * (γ p.2).val) i j
        simp only [Matrix.mul_apply]
        refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
        · exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp measurable_fst)
        · exact (measurable_pi_apply j).comp ((measurable_pi_apply l).comp (hγ.comp measurable_snd))
      have hs : StronglyMeasurable fun p : Lie E a × X => k p.2 * chart F g (toL (Matrix.of p.1 * (γ p.2).val)) :=
        ((hk.1.comp measurable_snd).mul (m.comp hm)).stronglyMeasurable
      exact hs.integral_prod_right'.measurable
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · rw [kerInf]
      have hz := one_le_height z
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

end GlobalTheory.JSW.RapidModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
section
noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame GlobalTheory.StdFrame
open scoped TensorProduct Matrix

namespace GlobalTheory.StdFrameModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.StdFrame.instCMHostS

variable {D : D7}

theorem hostF_eq (D : D7) : D.host.F = maximalRealSubfield D.host.E := rfl

abbrev sw (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* ReciprocityTheory.Aut.AL D.host.E := tensCastR (hostF_eq D)

theorem sw_tmul (a : Af D.host.F) (x : D.host.E) : sw D (a ⊗ₜ x) = x ⊗ₜ a := rfl

theorem sw_sig (y : ReciprocityTheory.Aut.AL D.host.E) :
    (sw D).symm (ReciprocityTheory.Aut.conjAL D.host.E y) = sigR (Af D.host.F) D.sp.cm.sig ((sw D).symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingEquiv.map_zero, RingHom.map_zero]
  | tmul x a => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingEquiv.map_add (e := _), RingEquiv.map_add (e := _), RingHom.map_add (f := _), hx, hy]

theorem mem_GA_iff {V : HSp D} (hg : V.gram = 1) (κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) :
    κ ∈ ReciprocityTheory.Aut.GA D.host.E V.rank ↔
      Formalism.UG.bc (sw D).symm.toRingHom κ ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have h1 : JR (F := D.host.F) (Af D.host.F) V.gram = 1 := by
    rw [hg, JR]; exact Matrix.map_one _ (map_zero _) (map_one _)
  change κ.1 * ReciprocityTheory.Aut.conjT _ κ.1 = 1 ↔
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) * JR (F := D.host.F) (Af D.host.F) V.gram *
      κ.1.map (sw D).symm.toRingHom = JR (F := D.host.F) (Af D.host.F) V.gram
  have h2 : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) κ.1).map (sw D).symm.toRingHom := by
    ext i j
    exact (sw_sig _).symm
  rw [h1, Matrix.mul_one, h2, ← Matrix.map_mul, mul_eq_one_comm,
    ← Matrix.map_one (sw D).symm.toRingHom (map_zero _) (map_one _)]
  exact ⟨fun h => by rw [h], fun h => Matrix.map_injective (sw D).symm.injective h⟩

theorem exists_lift {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    ∃ g : GA D V, infHom V g = 1 ∧ finHom V g = Formalism.UG.bc (sw D).symm.toRingHom κ.1 :=
  GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) ((mem_GA_iff hg κ.1).1 κ.2)

def unitPsi {V : HSp D} (hg : V.gram = 1) : RowPsi V V.rank where
  ψ := MonoidHom.mk' (fun κ => (exists_lift hg κ).choose) fun a b => by
    refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
    · rw [map_mul, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, mul_one]
    · rw [map_mul, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2,
        ← map_mul]
      rfl
  inj := fun a b h => by
    have h1 := congrArg (finHom V) h
    simp only [MonoidHom.mk'_apply] at h1
    rw [(exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2] at h1
    exact Subtype.ext (Units.ext (Matrix.map_injective (sw D).symm.injective (congrArg Units.val h1)))
  into := fun κ => (exists_lift hg κ).choose_spec.1
  onto := fun g hgf => by
    have e : Formalism.UG.bc (sw D).symm.toRingHom (Formalism.UG.bc (sw D).toRingHom (finHom V g)) = finHom V g := by
      ext i j
      exact (sw D).symm_apply_apply _
    refine ⟨⟨Formalism.UG.bc (sw D).toRingHom (finHom V g), (mem_GA_iff hg _).2 (by
      rw [e]; exact GlobalTheory.UnitarySplit.finHom_mem V g)⟩, GlobalTheory.UnitarySplit.ga_ext V ?_ ?_⟩
    · exact (exists_lift hg _).choose_spec.1.trans (Eq.symm hgf)
    · exact (exists_lift hg _).choose_spec.2.trans e

theorem finMat_unitPsi {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    finMat D.sp.cm.sig V.gram ((unitPsi hg).ψ κ) = κ.1.1.map (sw D).symm :=
  congrArg Units.val (exists_lift hg κ).choose_spec.2

theorem mem_std_lattice_iff_integral_coords {V : HSp D} (h : OrthFrame V) (x : Fin V.rank → D.host.E) :
    x ∈ L0c D V ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := h.mem_iff x

theorem tmul_mem (o : 𝓞 D.host.E) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    sw D (a ⊗ₜ (o : D.host.E)) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  have e : sw D (a ⊗ₜ (o : D.host.E)) =
      ((o : D.host.E) ⊗ₜ (1 : Af D.host.F) : ReciprocityTheory.Aut.AL D.host.E) * ((1 : D.host.E) ⊗ₜ a) := by
    rw [sw_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨o, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩))

theorem int_of_mem {V : HSp D} (h : OrthFrame V) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) (i : Fin V.rank) : sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((mem_std_lattice_iff_integral_coords h x).1 hx i)
    have := tmul_mem o ha
    rw [show (o : D.host.E) = x i from ho] at this
    exact this
  | zero => rw [Pi.zero_apply, RingEquiv.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Pi.add_apply, RingEquiv.map_add (e := _)]; exact add_mem hy hz
  | neg y _ hy => rw [Pi.neg_apply, RingEquiv.map_neg]; exact neg_mem hy

theorem smul_gen {M : ℕ} (L : Set (Fin M → D.host.E)) (c : Af D.host.F ⊗[D.host.F] D.host.E)
    (hc : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, c • (fun i => a ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E L)
    {w : Fin M → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latHat D.host.F D.host.E L) :
    c • w ∈ latHat D.host.F D.host.E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem smul_closure {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (e : B →+* A) (S : AddSubgroup (Fin M → A)) (T : Set B)
    (h : ∀ t ∈ T, ∀ w ∈ S, e t • w ∈ S) {r : B} (hr : r ∈ Subring.closure T) : ∀ w ∈ S, e r • w ∈ S := by
  induction hr using Subring.closure_induction with
  | mem r hr => exact h r hr
  | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [map_one, one_smul]
  | add x y _ _ hx hy => intro w hw; rw [map_add (f := _), add_smul]; exact add_mem (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [map_mul, mul_smul]; exact hx _ (hy w hw)

theorem smul_mem {V : HSp D} (h : OrthFrame V) {r : ReciprocityTheory.Aut.AL D.host.E} (hr : r ∈ ReciprocityTheory.Aut.ALint D.host.E) :
    ∀ w ∈ latHat D.host.F D.host.E (L0c D V), (sw D).symm r • w ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine smul_closure (sw D).symm.toRingHom _ _ (fun r hr w hw => ?_) hr
  rcases hr with ⟨o, rfl⟩ | ⟨b, hb, rfl⟩
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, (o : D.host.E) • x, ?_, ?_⟩) hw
    · rw [mem_std_lattice_iff_integral_coords h] at hx ⊢
      exact fun i => Submodule.smul_mem _ o (hx i)
    · funext i
      change ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => ?_, x, hx, ?_⟩) hw
    · rw [map_mul]
      exact mul_mem (hb v) (ha v)
    · funext i
      change ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]
  exact one_mem _

theorem single_mem {V : HSp D} (h : OrthFrame V) (j : Fin V.rank) :
    (Pi.single j 1 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine AddSubgroup.subset_closure ⟨1, one_mem_intAf _, Pi.single j 1, ?_, ?_⟩
  · rw [mem_std_lattice_iff_integral_coords h]
    intro a
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  · funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero]

theorem mem_latHat_iff {V : HSp D} (h : OrthFrame V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  refine ⟨int_of_mem h, fun hy => ?_⟩
  rw [pi_eq_sum_univ' y]
  refine sum_mem fun i _ => ?_
  have := smul_mem h (hy i) _ (single_mem h i)
  rw [RingEquiv.symm_apply_apply] at this
  exact this

theorem mulVec_mem {V : HSp D} (h : OrthFrame V) {κ : Formalism.AUTREP.GAf D.host.E V.rank}
    (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) :
    (κ.1.1.map (sw D).symm.toRingHom) *ᵥ y ∈ latHat D.host.F D.host.E (L0c D V) := by
  rw [mem_latHat_iff h] at hy ⊢
  intro i
  change (sw D).toRingHom (∑ j, (sw D).symm (κ.1.1 i j) * y j) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum (sw D).toRingHom]
  refine sum_mem fun j _ => ?_
  change sw D _ ∈ _
  rw [RingEquiv.map_mul, RingEquiv.apply_symm_apply]
  exact mul_mem (hκ i j) (hy j)

theorem stdPsi_unitPsi {V : HSp D} (h : OrthFrame V) : StdPsi (hostF_eq D) (unitPsi h.gram_eq) := by
  refine ⟨⟨1, 1, mul_one _, mul_one _, fun κ => ?_⟩, fun κ => ⟨fun hκ => ⟨(unitPsi h.gram_eq).into κ, fun y => ?_, by simp⟩, ?_⟩⟩
  · rw [finMat_unitPsi, Matrix.one_mul, Matrix.mul_one]
  · rw [finMat_unitPsi]
    refine ⟨mulVec_mem h hκ, fun hy => ?_⟩
    have := mulVec_mem h (inv_mem hκ) hy
    erw [Matrix.mulVec_mulVec, ← Matrix.map_mul] at this
    rw [show (κ⁻¹).1.1 * κ.1.1 = 1 from Units.inv_mul κ.1, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mulVec] at this
    exact this
  · rintro ⟨-, hk, -⟩ i j
    have := (mem_latHat_iff h _).1 ((hk _).1 (single_mem h j)) i
    rw [finMat_unitPsi, Matrix.mulVec_single_one] at this
    change sw D ((sw D).symm (κ.1.1 i j)) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

section Conj

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

open ReciprocityTheory.Aut

variable {L}

end Conj

end GlobalTheory.StdFrameModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PositivityModel

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L N A : LB X}

theorem genericPoint_mem [IsIntegral X] (hd : topologicalKrullDim X = 1) {Z : Closeds X}
    (hZ : IsCompleteCurve k Z) : genericPoint X ∈ Z := by
  by_contra hn
  have h := topologicalKrullDim_add_one_le Z.isClosed isClosed_univ fun x _ =>
    ⟨genericPoint X, trivial, hn, genericPoint_specializes x⟩
  have h' := h.trans ((topologicalKrullDim_subspace_le X Set.univ).trans hd.le)
  rw [hZ.2] at h'
  exact absurd h' (by decide)

section Space
open ProjSpace
variable (k) (D : ℕ)

end Space

end GlobalTheory.PositivityModel
end
end

