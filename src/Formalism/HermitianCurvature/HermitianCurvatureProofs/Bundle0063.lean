module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_ideal {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x : A} (hx : x ∈ Ideal.span (rgen k r z' E)) : La x = 0 := by
  have key : ∀ y ∈ Ideal.span (rgen k r z' E), ∀ a : A, La (a * y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, hpq, rfl⟩ := hy
      intro a
      rw [mul_sub, map_sub, hR a p q hpq, ← Algebra.commutes, ← Algebra.smul_def, map_smul, sub_self]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add (f := _), hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
  simpa using key x hx 1

theorem la_congr {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x y : A} (hx : x - y ∈ Ideal.span (rgen k r z' E)) : La x = La y := by
  have := la_ideal hR hx
  rwa [map_sub, sub_eq_zero] at this

theorem sum_single {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} (P : (Fin m → Fin N) → Prop)
    [DecidablePred P] (X : Fin m → Fin N → ℂ) (S : Set (Fin N)) (hX : ∀ a p, p ∉ S → X a p = 0)
    (e : Fin m → Fin N) (he : P e) (huniq : ∀ c, P c → (∀ l, c l ∈ S) → c = e) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      (Matrix.of fun a l => X a (e l)).det • F e := by
  rw [Finset.sum_eq_single e]
  · rw [if_pos he]
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, c l ∈ S
      · exact absurd (huniq c hP hS) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hX a _ hl]), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ e) h

theorem uniq_mono {α : Type} [LinearOrder α] {m : ℕ} (e c : Fin m → α) (he : StrictMono e) (hc : StrictMono c)
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have hcard : (Finset.image e Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ he.injective]; simp
  have hS' : ∀ l, c l ∈ Finset.image e Finset.univ := by
    intro l; obtain ⟨x, hx⟩ := hS l; rw [← hx]; exact Finset.mem_image_of_mem e (Finset.mem_univ x)
  rw [Finset.orderEmbOfFin_unique hcard hS' hc]
  exact (Finset.orderEmbOfFin_unique hcard (fun l => Finset.mem_image_of_mem e (Finset.mem_univ l)) he).symm

theorem uniq_key {N m : ℕ} (key : Fin N → ℕ) (hkey : Function.Injective key) (e c : Fin m → Fin N)
    (he : StrictMono (fun l => key (e l))) (hc : StrictMono (fun l => key (c l)))
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have h := uniq_mono (fun l => key (e l)) (fun l => key (c l)) he hc (by
    intro l; obtain ⟨x, hx⟩ := hS l; exact ⟨x, by simp only [hx]⟩)
  funext l; exact hkey (congrFun h l)

theorem AAx_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (u : ℂ) :
    AAx k r E xi m1 h1 u = AAx k r E xi m2 h2 u := by subst h; rfl

theorem AAv_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (ell : ℂ) :
    AAv k r E y m1 h1 ell = AAv k r E y m2 h2 ell := by subst h; rfl

theorem sgnW_sq (m : ℕ) : sgnW m * sgnW m = 1 := by
  unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem scal_E (dh t σ ε : ℂ) (s' : ℕ) (hdh : dh ≠ 0) (ht : t ≠ 0) (hσ : σ * σ = 1) (hε : ε * ε = 1) :
    (dh * t ^ (s' + 1) * (ε * σ))⁻¹ * (dh * t ^ s' * σ) = ε * t⁻¹ * (dh⁻¹ * dh) := by
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, zero_mul] at hσ; exact zero_ne_one hσ
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  rw [mul_inv, mul_inv, mul_inv, hεi, inv_mul_cancel₀ hdh, pow_succ]
  field_simp

theorem AAx_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → i0 ≤ p.val → xi a p = 0)
    (hh : ∀ a b : Fin i0, xi (Fin.castLE hi0 a) (xR k r i0 hi0 b) = h a b) :
    AAx k r E xi i0 hi0 u = h.det • qminor E (xR k r i0 hi0) (xR k r i0 hi0) u := by
  unfold AAx
  rw [sum_single (fun c => StrictMono c) (fun a p => xi (Fin.castLE hi0 a) p) (Set.range (xR k r i0 hi0))
    ?_ (xR k r i0 hi0) ?_ ?_]
  · congr 2
    ext a l
    simp only [Matrix.of_apply]
    exact hh a l
  · intro a p hp
    apply hz _ _ (by simp)
    by_contra hlt; push Not at hlt; apply hp; exact ⟨⟨p.val, hlt⟩, by ext; simp [xR, eI]⟩
  · intro a b hab; simp only [xR, eI]; exact hab
  · intro c hc hS
    exact uniq_mono _ _ (fun a b hab => by simp only [xR, eI]; exact hab) hc hS

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mulRb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.mul_add]
      map_smul' := fun c X => by ext g : 1; simp }

def mulLb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.add_mul]
      map_smul' := fun c X => by ext g : 1; simp }

theorem vf_eq_b (b : Bool) (X g : Mat k r) :
    vf b X g = (if b then -(mulLb k r X g) else mulRb k r X g) := by
  cases b
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]

theorem vf_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (b : Bool) {X g : P → Mat k r}
    (hX : ContDiff ℝ ∞ X) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun q => vf b (X q) (g q)) := by
  cases b
  · have h := ((mulRb k r).contDiff.comp hX).clm_apply hg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)
  · have h := (((mulLb k r).contDiff.comp hX).clm_apply hg).neg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)

def Phi (F' : Mat k r → E) : (j : ℕ) → (Fin j → Bool) → (Fin j → Mat k r) × Mat k r → E
  | 0, _, q => F' q.2
  | j + 1, bs, q => fderiv ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => q.1 i.succ), g)) q.2
      (vf (bs 0) (q.1 0) q.2)

theorem top_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  first
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  | simp
  | exact le_of_eq (by norm_cast)

theorem phi_contDiffAt (F' : Mat k r → E) {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (q : (Fin j → Mat k r) × Mat k r), q.2 ∈ U → ContDiffAt ℝ ∞ (Phi F' j bs) q := by
  intro j
  induction j with
  | zero =>
    intro bs q hq
    exact (hF.contDiffAt (hU.mem_nhds hq)).comp q contDiffAt_snd
  | succ j ih =>
    intro bs q hq
    have hsh : ContDiff ℝ ∞ (fun p : ((Fin (j + 1) → Mat k r) × Mat k r) × Mat k r =>
        ((fun i : Fin j => p.1.1 i.succ), p.2)) :=
      (contDiff_pi.2 fun (i : Fin j) => by
        simpa only [Function.comp_def] using
          (contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) i.succ).comp (contDiff_fst.comp contDiff_fst)).prodMk
        contDiff_snd
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (p : (Fin (j + 1) → Mat k r) × Mat k r) (g : Mat k r) =>
        Phi F' j (fun i => bs i.succ) ((fun i => p.1 i.succ), g)) (q, q.2) :=
      (ih (fun i => bs i.succ) ((fun i => q.1 i.succ), q.2) hq).comp (q, q.2) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 contDiffAt_snd top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun p : (Fin (j + 1) → Mat k r) × Mat k r => vf (bs 0) (p.1 0) p.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) 0).comp contDiff_fst) contDiff_snd
    exact h2.clm_apply h3.contDiffAt

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem W_eq_phi {F F' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U)
    (hff : ∀ x ∈ U, x ∈ GV k r → F x = F' x) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) →
      ∀ x ∈ U, x ∈ GV k r → W (List.ofFn fun i => (bs i, Xs i)) F x = Phi F' j bs (Xs, x) := by
  intro j
  induction j with
  | zero => intro bs Xs _ x hx hxG; exact hff x hx hxG
  | succ j ih =>
    intro bs Xs hXs x hx hxG
    rw [List.ofFn_succ, W_cons]
    have hd : DifferentiableAt ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => Xs i.succ), g)) x :=
      ((phi_contDiffAt F' hU hF j _ ((fun i => Xs i.succ), x) hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (hasDerivAt_ext (bs 0) hU hx hxG hd (fun h hh hhG => ih _ _ (fun i => hXs i.succ) h hh hhG)
      (hXs 0)).deriv

theorem W_local_zero {F : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V) (h : ∀ x ∈ V, x ∈ GV k r → F x = 0) :
    ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ x ∈ V, x ∈ GV k r → W w F x = 0 := by
  intro w
  induction w with
  | nil => intro _ x hx hxG; exact h x hx hxG
  | cons a w ih =>
    intro hw x hx hxG
    rw [W_cons]
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hc := (cv_hasDerivAt a.1 a.2 x).continuousAt
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, cv a.1 a.2 t x ∈ V :=
      hc.preimage_mem_nhds (by rw [cv_zero]; exact hV.mem_nhds hx)
    have he : (fun t : ℝ => W w F (cv a.1 a.2 t x)) =ᶠ[𝓝 0] fun _ => (0 : E) := by
      filter_upwards [hmem] with t ht
      exact ih hw' _ ht (cv_mem (hw a List.mem_cons_self) hxG t)
    show deriv (fun t : ℝ => W w F (cv a.1 a.2 t x)) 0 = 0
    rw [he.deriv_eq, deriv_const]

def Box (k r : ℕ) : Set (Mat k r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1

theorem box_compact : IsCompact (Box k r) := by
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1

theorem mem_box {X : Mat k r} (h : ∀ i j, ‖X i j‖ ≤ 1) : X ∈ Box k r := by
  exact fun i _ j _ => mem_closedBall_zero_iff.mpr (h i j)

theorem local_bound {F : Mat k r → E} (hF : CkOn ⊤ (GV k r) F) (m : ℕ) {g₀ : Mat k r} (hg₀ : g₀ ∈ GV k r) :
    ∃ V ∈ 𝓝 g₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := by
  obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  have hsub : Metric.closedBall g₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hc' : ContDiffOn ℝ ∞ F' U := by exact_mod_cast hc
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ (Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ
      Metric.closedBall g₀ (ε / 2), ‖Phi F' j bs q‖ ≤ c := by
    intro j bs
    have hK : IsCompact ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall g₀ (ε / 2)) :=
      (isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall g₀ _)
    exact hK.exists_bound_of_continuousOn fun q hq =>
      (phi_contDiffAt F' hU hc' j bs q (hsub hq.2)).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall g₀ (ε / 2), Metric.closedBall_mem_nhds g₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro x hx hxG j hj bs Xs hL hB
  rw [W_eq_phi hU hc' hff j bs Xs hL x (hsub hx) hxG]
  calc ‖Phi F' j bs (Xs, x)‖ ≤ |c j bs| := (hcb j bs (Xs, x) ⟨fun i _ => hB i, hx⟩).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem compact_support_finite_class : Formalism.FourierDecayAlt.P.JFxG.CptInCC := by
  intro k r E _ _ F C hF hC hCF A m
  have hCG : IsCompact (C ∩ GV k r) := hC.inter_right B5.GV_closed
  have hloc : ∀ g₀ ∈ C ∩ GV k r, ∃ V, V ∈ 𝓝 g₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := fun g₀ hg₀ => by
    obtain ⟨V, hV, c, hc0, hc⟩ := local_bound hF m hg₀.2
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hloc
  obtain ⟨t, htC, hcov⟩ := hCG.elim_nhds_subcover V hV
  have hcW : ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F g‖ ≤ ∑ x ∈ t, c x := by
    intro g hg j hj bs Xs hL hB
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (hcov hg)
    exact (hc x (htC x hxt) g hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (htC y hy)) hxt)
  obtain ⟨cg, hcg⟩ := hCG.exists_bound_of_continuousOn (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  have hsum0 : 0 ≤ ∑ x ∈ t, c x := Finset.sum_nonneg fun y hy => hc0 y (htC y hy)
  refine ⟨|cg| * ∑ x ∈ t, c x, B5.ckOn_mono le_top hF, ?_⟩
  intro u v hu hv hl g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW g ⟨hgC, hg⟩ _ hlen (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl (fun x hx _ => hCF x hx) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
section
theorem Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  cutoff_plain_and_smoothed.2
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem isDom_omP {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') :
    Q.IsDom k r z z' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  refine ⟨?_, ?_⟩
  · have e : {g : Q.Mx k r | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
        ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} =
        {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g} ∩
          ⋂ a : Fin r, {g | Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp
    rw [e]
    exact (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z')).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r z' := ⟨h', hh', m', hm'.1, rfl⟩
    have hD : ∀ l, Dmin k r z z' (h * m * g * (h' * m')) l = Dmin k r z z' g l :=
      fun l => dInv k r z z' hz hz' _ hs _ hs' g l
    refine ⟨?_, fun a => by rw [hD]; exact hg.2 a⟩
    have e : Gf k r z z' (h * m * g * (h' * m')) = Gf k r z z' g := by
      unfold Gf
      rw [hD, hD]
    rw [e]
    exact hg.1

theorem coefficient_vector_preserves_form : CVPresFF := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v J hJ Y s
  have hz := (T v).base.z_mem
  have hz' := (T v).base.z'_mem
  have hD : Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := isDom_omP hz hz'
  have hC : Q.CV S.G.k S.G.r (Y : ℂ) J ∈
      Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) :=
    Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ S.G.k S.G.r _ _ _ _ 0 _ (Y : ℂ) 0 0 hz hz' hD J hJ
  exact Formalism.FourierDecayAlt.P.Qx8.FFl_smul hC s

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem quadratic_local_family_holds : GQLFam := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Dc Φ hF Y a b
  obtain ⟨hO, hD, hM, hS, hFF⟩ := hF
  refine ⟨hO, hD, hM, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.transfer_joint_smooth _ _ _ _ _ _ _ Φ (Y : ℂ) a b hO hS
  · intro c hc
    exact Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ _ _ _ _ _ _ _ _ (Y : ℂ) a b Bs.z_mem Bs.z'_mem (hD c hc) _ (hFF c hc)

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScal
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def phiR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g ⟨r, by omega⟩ / Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))

def phiD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)) / (starRingEnd ℂ) (Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)))

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def ScalOK (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ) : Prop :=
  B.CkOn ⊤ (B.GPos D) φ ∧
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m)

end

def JAScalBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ), K * ((r : ℝ) + 1) ≤ Bg →
    ScalOK D Bg (phiR k r D.z D.z') ∧ ScalOK D Bg (phiD k r D.z D.z')

def JAScalConj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ),
    ScalOK D Bg φ → ScalOK D Bg (fun g => (starRingEnd ℂ) (φ g))

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepABorder
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem quantum_minor_border_expansion_first {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (f b : Fin m → Fin n) (hE : GlRel E)
    (hf : ∀ j, f j ≠ e) (hb : ∀ j, b j ≠ e) (u : ℂ) :
    qminor E (bE e f) (bE e b) u = Tm E u e e * qminor E f b (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (f w) e * qminor E (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) * E e (b x)) := by
  rw [Qx6.expFCE E expansion_first_column]
  refine Qx6.add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Qx6.qm_dropE E expansion_last_line quantumMinorRowSkew_holds hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Qx6.Tm_ne E _ (hf w), Qx6.Tm_ne E _ (hb x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
    ← neg_smul, show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring

end Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
end
end

