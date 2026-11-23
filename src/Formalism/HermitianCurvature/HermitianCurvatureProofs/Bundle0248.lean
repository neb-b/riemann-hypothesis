module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0243
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem fold_congrV (V : Set (Mat k r)) :
    ∀ (L : List ((Mat k r → E) → (Mat k r → E))),
    (∀ T ∈ L, ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → T h₁ x = T h₂ x) →
    ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → L.foldr (fun T h => T h) h₁ x = L.foldr (fun T h => T h) h₂ x
  | [], _, _, _, he => by simpa using he
  | T :: L, hT, h₁, h₂, he => by
    intro x hx hxG
    simp only [List.foldr_cons]
    exact hT T (by simp) _ _ (fold_congrV V L (fun T' hT' => hT T' (by simp [hT'])) h₁ h₂ he) x hx hxG

theorem qminorOp_congr {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (x : Mat k r) (hx : x ∈ V)
    (hxG : x ∈ GV k r) : qminorOp (EabH (Hpk k r)) a b u f₁ x = qminorOp (EabH (Hpk k r)) a b u f₂ x := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Pi.smul_apply]
  congr 1
  refine fold_congrV V _ ?_ f₁ f₂ he x hx hxG
  intro T hT h₁ h₂ he' y hy hyG
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact top_congr' V hV _ _ _ he' y hy hyG

theorem vLet_congr (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {V : Set (Mat k r)} (hV : IsOpen V) {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x)
    (x : Mat k r) (hx : x ∈ V) (hxG : x ∈ GV k r) :
    D.vLet k r z z' i hi l e f₁ x = D.vLet k r z z' i hi l e f₂ x := by
  unfold D.vLet C3.AAop C3.AAvop
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl

theorem loc_of_smoothOnH {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) (g : Mat k r) (hg : g ∈ GV k r) :
    Loc (⊤ : ℕ∞) f g := by
  obtain ⟨U, F, a, b, c, d⟩ := hf g hg
  exact ⟨U, F, a, b, c, d⟩

theorem bump_ext {Φ : Mat k r → E} {Dm : Set (Mat k r)} (hDm : IsOpen Dm) (hΦ : Q.SmoothLev k r 0 Dm Φ)
    {p : Mat k r} (hp : p ∈ Dm) (hpG : p ∈ GV k r) :
    ∃ V : Set (Mat k r), IsOpen V ∧ p ∈ V ∧ V ⊆ Dm ∧
      ∃ f : Mat k r → E, SmoothOnH (Hpk k r) f ∧ ∀ x ∈ V, x ∈ GV k r → f x = Φ x := by
  obtain ⟨U, F, hU, hpU, hF, hΦF⟩ := hΦ p ⟨glev0 hpG, hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.inter hDm) p ⟨hpU, hp⟩
  let χ : ContDiffBump p := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  refine ⟨Metric.ball p (ε / 3), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    fun x hx => (hball (Metric.ball_subset_ball (by linarith) hx)).2,
    fun x => ((χ x : ℝ) : ℂ) • F x, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hg : g₀ ∈ U
    · exact ⟨U, fun x => ((χ x : ℝ) : ℂ) • F x, hU, hg,
        ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffOn).smul hF, fun _ _ _ => rfl⟩
    · refine ⟨(tsupport χ)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, ?_, contDiffOn_const,
        fun x hx _ => ?_⟩
      · intro hs
        apply hg
        have h2 : g₀ ∈ Metric.closedBall p (ε / 2) := χ.tsupport_eq.subset hs
        exact (hball (Metric.closedBall_subset_ball (by linarith) h2)).1
      · have h0 : χ x = 0 := by
          by_contra h
          exact hx (subset_tsupport χ (Function.mem_support.2 h))
        simp [h0]
  · intro x hx hxG
    have h1 : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    show ((χ x : ℝ) : ℂ) • F x = Φ x
    rw [h1, Complex.ofReal_one, one_smul]
    exact (hΦF x (hball (Metric.ball_subset_ball (by linarith) hx)).1 (glev0 hxG)).symm

theorem vLet_smul (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {x : Mat k r} (hx : x ∈ GV k r) (c : ℂ) :
    D.vLet k r z z' i hi l e (fun y => c • f y) x = c • D.vLet k r z z' i hi l e f x := by
  let fW : Wsm (E := E) (Set.univ : Set (Mat k r)) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have ec : ((c • fW : Wsm (E := E) (Set.univ : Set (Mat k r))) : Mat k r → E) = fun y => c • f y := rfl
  have hA : ∀ m (hm : m ≤ r) u, C3.AAop k r m hm u (fun y => c • f y) x = c • C3.AAop k r m hm u f x := by
    intro m hm u
    have e1 := AAop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  have hAv : ∀ m (hm : m ≤ r) u, C3.AAvop k r m hm u (fun y => c • f y) x = c • C3.AAvop k r m hm u f x := by
    intro m hm u
    have e1 := AAvop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAvop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  unfold D.vLet
  split_ifs
  · simp
  · rw [hA, smul_comm]
  · rw [hAv, smul_comm]

theorem vLet_transl (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (i : ℕ) (hi : i ≤ r)
    (l : C.Letter) (e : Fin 2) {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {s s' : Mat k r}
    (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') {g : Mat k r} (hg : g ∈ GV k r) :
    D.vLet k r z z' i hi l e f (s * g * s') = D.vLet k r z z' i hi l e (fun x => f (s * x * s')) g := by
  have hD : ∀ l', Dmin k r z z' (s * g * s') l' = Dmin k r z z' g l' :=
    fun l' => dInv k r z z' hz hz' s hs s' hs' g l'
  have hX := fun m (hm : m ≤ r) u ell => operators_commute_translations E k r z z' m hm u ell f hz hz' hf s hs s' hs' g hg
  unfold D.vLet
  split_ifs
  · rfl
  · rw [hD, (hX _ _ _ 0).1]
  · rw [hD, (hX _ _ 0 _).2]

theorem smooth_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {Dm : Set (Mat k r)} (hDm : IsOpen Dm) {Φ : Mat k r → E} (hΦ : Q.SmoothLev k r 0 Dm Φ)
    (hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0) :
    Q.SmoothLev k r 0 Dm (D.vLet k r z z' i hi l e Φ) := by
  rintro g₀ ⟨hg₀G', hg₀D⟩
  have hg₀G : g₀ ∈ GV k r := hg₀G'.1
  obtain ⟨V, hV, hpV, hVD, f, hf, hfe⟩ := bump_ext hDm hΦ hg₀D hg₀G
  let fW : Wsm (E := E) (Sd z z' i hi) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have hL : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e f) g₀ :=
    vLet_mem z z' i hi l e fW g₀ (hne g₀ hg₀D) hg₀G
  have hL2 : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e Φ) g₀ :=
    loc_of_eq hL hV hpV (fun x hx hxG =>
      vLet_congr z z' i hi l e hV (fun y hy hyG => (hfe y hy hyG).symm) x hx hxG)
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hL2
  exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hFe g hg hgl.1⟩

theorem one_mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, BigCellZetaMinors.one_uw z, n, hn, (Matrix.one_mul n).symm⟩

theorem rulesOn_vLet (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDJ : Dm ⊆ LevelPointCoordinates.domJ k r j hj z z')
    (hR : LevelPointCoordinates.RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ j + 1) (hij : i = j ∨ i = j + 1)
    (l : C.Letter) (e : Fin 2) :
    LevelPointCoordinates.RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ) := by
  obtain ⟨hS, hRt, hLt⟩ := hR
  have hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0 := by
    intro g hg
    obtain ⟨h1, h2, _⟩ := hDJ hg
    rcases hij with rfl | rfl
    · exact h1
    · exact h2
  refine ⟨smooth_vLet z z' i (by omega) l e hDm hS hne, ?_, ?_⟩
  · rintro g ⟨hgG', hgD⟩ n hn
    have hgnD := (hRt g ⟨hgG', hgD⟩ n hn).1
    refine ⟨hgnD, ?_⟩
    have hgG : g ∈ GV k r := hgG'.1
    have hgnG : g * n ∈ GV k r := AAInvW.inUH_mul hgG hn.1
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hgnG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => x * n) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_id.matrix_mul continuous_const))
    calc D.vLet k r z z' i _ l e Φ (g * n) = D.vLet k r z z' i _ l e fa (1 * g * n) := by
          rw [Matrix.one_mul]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hgnG
      _ = D.vLet k r z z' i _ l e (fun x => fa (1 * x * n)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z WeylGroupFacts.mem_n_one) (one_mem_S z' hn) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z' cStd n • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.one_mul, hfae (y * n) hy.2 (AAInvW.inUH_mul hyG hn.1),
            (hRt y ⟨glev0 hyG, hVbD hy.1⟩ n hn).2, hfbe y hy.1 hyG]
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]
  · rintro g ⟨hgG', hgD⟩ a
    have hgnD := (hLt g ⟨hgG', hgD⟩ a).1
    refine ⟨hgnD, ?_⟩
    set s := LevelPointCoordinates.nL k r j hj a with hs_def
    have hsN : s ∈ Nset k r := nL_mem j hj a
    have hgG : g ∈ GV k r := hgG'.1
    have hsgG : s * g ∈ GV k r := AAInvW.inUH_mul hsN.1 hgG
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hsgG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => s * x) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_const.matrix_mul continuous_id))
    calc D.vLet k r z z' i _ l e Φ (s * g) = D.vLet k r z z' i _ l e fa (s * g * 1) := by
          rw [Matrix.mul_one]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hsgG
      _ = D.vLet k r z z' i _ l e (fun x => fa (s * x * 1)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z hsN) (one_mem_S z' WeylGroupFacts.mem_n_one) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z cStd s • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.mul_one, hfae (s * y) hy.2 (AAInvW.inUH_mul hsN.1 hyG),
            (hLt y ⟨glev0 hyG, hVbD hy.1⟩ a).2, hfbe y hy.1 hyG]
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

namespace Formalism.FourierDecayAlt.P

theorem rules_closed : Formalism.FourierDecayAlt.P.LevelPointCoordinates.RulesClosed :=
  fun k r j hj z z' E _ _ Dm Φ hz hz' hDm hDJ hR i hi hij l e =>
    SingleEntryHermitianProducts.rulesOn_vLet k r j hj z z' E Dm Φ hz hz' hDm hDJ hR i hi hij l e

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeOperatorClass
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL

abbrev rdzPZ (j : ℕ) : Type := ℂ × (Fin j → Fin j → ℂ)

def rdzLdL {j : ℕ} (x : MJ j) : rdzPZ j →ₗ[ℝ] rdzPZ j where
  toFun q := (0, fun a b => ∑ c, q.2 a c * x c b)
  map_add' p q := Prod.ext (by simp) (by funext a b; simp [add_mul, Finset.sum_add_distrib])
  map_smul' t q := Prod.ext (by simp) (by funext a b; simp [Finset.smul_sum, mul_assoc])

def rdzLd {j : ℕ} (x : MJ j) : rdzPZ j →L[ℝ] rdzPZ j := LinearMap.toContinuousLinearMap (rdzLdL x)

theorem rdzLd_apply {j : ℕ} (x : MJ j) (q : rdzPZ j) : rdzLd x q = (0, fun a b => ∑ c, q.2 a c * x c b) := rfl

theorem rdzLd_inl {j : ℕ} (x : MJ j) (v : ℂ) : rdzLd x ((v, 0) : rdzPZ j) = 0 := by
  rw [rdzLd_apply]
  exact Prod.ext rfl (by funext a b; simp)

theorem rdz_curve {j : ℕ} (x : MJ j) (τ : ℂ) (Z : MJ j) :
    HasDerivAt (fun t : ℝ => ((τ, (Z * NormedSpace.exp ((t : ℂ) • x) : MJ j)) : rdzPZ j)) (rdzLd x (τ, Z)) 0 := by
  refine HasDerivAt.congr_deriv ((hasDerivAt_const (0 : ℝ) τ).prodMk (hasDerivAt_mul_exp_smul_zero Z x)) ?_
  rw [rdzLd_apply]
  exact Prod.ext rfl (funext fun a => funext fun b => Matrix.mul_apply)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdz_da {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : F → E} {V : Set F} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h V) {Z : F} (hZ : Z ∈ V) : DifferentiableAt ℝ h Z :=
  (hh.contDiffAt (hV.mem_nhds hZ)).differentiableAt (by simp)

theorem rdz_rd {j : ℕ} (x : MJ j) (G : rdzPZ j → E) (τ : ℂ) (Z : MJ j) (hd : DifferentiableAt ℝ G (τ, Z)) :
    RdV x (fun Z' : MJ j => G (τ, Z')) Z = fderiv ℝ G (τ, Z) (rdzLd x (τ, Z)) := by
  have h0 : ((τ, (Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) : MJ j)) : rdzPZ j) = (τ, Z) := by
    (simp [NormedSpace.exp_zero]; rfl)
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (rdz_curve x τ Z) h0.symm).deriv

theorem rdz_loc {j : ℕ} (x : MJ j) (h₁ h₂ : MJ j → E) (Z : MJ j) (h : h₁ =ᶠ[𝓝 Z] h₂) :
    RdV x h₁ Z = RdV x h₂ Z := by
  have ht : Tendsto (fun t : ℝ => Z * NormedSpace.exp ((t : ℂ) • x)) (𝓝 0) (𝓝 Z) := by
    have := (hasDerivAt_mul_exp_smul_zero Z x).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one] at this
    exact this
  unfold RdV
  exact Filter.EventuallyEq.deriv_eq (ht.eventually h)

theorem rdz_hd {j : ℕ} (x : MJ j) {h : MJ j → E} {Z : MJ j} (hd : DifferentiableAt ℝ h Z) :
    HasDerivAt (fun t : ℝ => h (Z * NormedSpace.exp ((t : ℂ) • x))) (fderiv ℝ h Z (Z * x)) 0 := by
  have h0 : Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) = Z := by simp [NormedSpace.exp_zero]
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_mul_exp_smul_zero Z x) h0.symm

def rdzK {j : ℕ} (κ : ℂ → MJ j → E) : rdzPZ j → E := fun q => κ q.1 (Matrix.of q.2)

theorem rdz_slice {j : ℕ} (κ : ℂ → MJ j → E) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) (v : ℂ) :
    fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ v = fderiv ℝ (rdzK κ) (τ₀, Z₀) (v, 0) := by
  have hι : HasFDerivAt (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) τ₀ :=
    (hasFDerivAt_id τ₀).prodMk (hasFDerivAt_const _ τ₀)
  have h2 := (hd.hasFDerivAt.comp τ₀ hι).fderiv
  rw [show (fun τ : ℂ => κ τ Z₀) = rdzK κ ∘ (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) from rfl, h2]
  rfl

def rdzH {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) : rdzPZ j → E := fun p =>
  c • (fderiv ℝ (rdzK κ) p (1, 0) + s • fderiv ℝ (rdzK κ) p (Complex.I, 0))

theorem rdz_dz_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dz f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + (-Complex.I) • fderiv ℝ f τ Complex.I) := by
  simp only [PBP.dz, neg_smul, sub_eq_add_neg]

theorem rdz_dzb_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dzb f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I) := rfl

theorem rdz_H_eq {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) :
    c • (fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ 1 + s • fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ Complex.I) =
      rdzH κ c s (τ₀, Z₀) := by
  rw [rdz_slice κ τ₀ Z₀ hd, rdz_slice κ τ₀ Z₀ hd]
  rfl

theorem rdz_H_smooth {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) {U : Set (rdzPZ j)} (hU : IsOpen U)
    (hK : ContDiffOn ℝ ∞ (rdzK κ) U) : ContDiffOn ℝ ∞ (rdzH κ c s) U := by
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hK.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  exact ((hK1.clm_apply contDiffOn_const).add ((hK1.clm_apply contDiffOn_const).const_smul s)).const_smul c

theorem rdz_par {j : ℕ} (x : MJ j) : ParamCommF (E := E) (fun h => RdV x h) := by
  intro U κ hU _ hK
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hKd : ∀ q ∈ U, DifferentiableAt ℝ (rdzK κ) q := fun q hq => rdz_da hU hKc hq
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hKc.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  have hG1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (rdzK κ) q (rdzLd x q)) U :=
    hK1.clm_apply (rdzLd x).contDiff.contDiffOn
  have hrd : ∀ q ∈ U, RdV x (κ q.1) (Matrix.of q.2) = fderiv ℝ (rdzK κ) q (rdzLd x q) :=
    fun q hq => rdz_rd x (rdzK κ) q.1 (Matrix.of q.2) (hKd q hq)
  refine ⟨hG1.congr fun q hq => hrd q hq, fun q hq => ?_⟩
  have hKa : ContDiffAt ℝ ∞ (rdzK κ) q := hKc.contDiffAt (hU.mem_nhds hq)
  have hc : DifferentiableAt ℝ (fderiv ℝ (rdzK κ)) q :=
    (hKa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hsym : IsSymmSndFDerivAt ℝ (rdzK κ) q := hKa.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hG1d : HasFDerivAt (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p))
      ((fderiv ℝ (rdzK κ) q).comp (rdzLd x) + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip (rdzLd x q)) q :=
    hc.hasFDerivAt.clm_apply (rdzLd x).hasFDerivAt
  have hL : ∀ v : ℂ, fderiv ℝ (fun τ => RdV x (κ τ) (Matrix.of q.2)) q.1 v =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) := by
    intro v
    have hev : (fun τ => RdV x (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1]
        (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) := by
      have hc' : ContinuousAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) q.1 :=
        (continuous_id.prodMk continuous_const).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with τ hτ
      exact hrd (τ, q.2) hτ
    have hι : HasFDerivAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) q.1 :=
      (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const _ q.1)
    rw [hev.fderiv_eq, show (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) =
      (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p)) ∘ (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) from rfl,
      (hG1d.comp q.1 hι).fderiv]
    simp [rdzLd_inl]
  have hR : ∀ c s : ℂ, RdV x (fun Z => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) (Matrix.of q.2) =
      c • (fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (1, 0) +
        s • fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (Complex.I, 0)) := by
    intro c s
    have hev : (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
        s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) =ᶠ[𝓝 (Matrix.of q.2)]
        (fun Z : MJ j => rdzH κ c s (q.1, Z)) := by
      have hc' : ContinuousAt (fun Z : MJ j => ((q.1, Z) : rdzPZ j)) (Matrix.of q.2) :=
        (continuous_const.prodMk continuous_id).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with Z hZ
      exact rdz_H_eq κ c s q.1 Z (hKd _ hZ)
    have hH : HasFDerivAt (rdzH κ c s)
        (c • (((fderiv ℝ (rdzK κ) q).comp 0 + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((1, 0) : rdzPZ j)) +
          s • ((fderiv ℝ (rdzK κ) q).comp 0 +
            (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((Complex.I, 0) : rdzPZ j)))) q :=
      ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((1, 0) : rdzPZ j) q)).add
        ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((Complex.I, 0) : rdzPZ j) q)).const_smul s)).const_smul c
    rw [rdz_loc x _ _ _ hev, rdz_rd x (rdzH κ c s) q.1 (Matrix.of q.2) hH.differentiableAt,
      show ((q.1, Matrix.of q.2) : rdzPZ j) = q from rfl, hH.fderiv]
    simp
  have hS : ∀ v : ℂ, fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (v, 0) := fun v => hsym _ _
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    rw [hR, hL, hL, hS, hS]
  · simp only [rdz_dzb_eq]
    rw [hR, hL, hL, hS, hS]

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.P.WirtingerOperators

theorem right_derivative_operator_class : WirtingerOperators.ZOpRd := by
  intro j E _ _ x
  refine ⟨fun h₁ h₂ Z h => rdz_loc x h₁ h₂ Z h, ?_, ?_, rdz_par x⟩
  · intro V h₁ h₂ hV _ c1 c2 Z hZ
    have d1 := rdz_hd x (rdz_da hV c1 hZ)
    have d2 := rdz_hd x (rdz_da hV c2 hZ)
    simp only [RdV]
    rw [d1.deriv, d2.deriv]
    exact (d1.add d2).deriv
  · intro V c h hV _ ch Z hZ
    have d := rdz_hd x (rdz_da hV ch hZ)
    simp only [RdV]
    rw [d.deriv]
    exact (d.const_smul c).deriv

theorem wirtinger_slice_smooth : WirtingerOperators.DzSlice := by
  intro j E _ _ U κ hU hK τ₀
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hι : ContDiff ℝ ∞ (fun Z : MJ j => ((τ₀, Z) : rdzPZ j)) := contDiff_const.prodMk contDiff_id
  have key : ∀ c s : ℂ, ContDiffOn ℝ ∞ (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ Complex.I)) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} := by
    intro c s
    refine ((rdz_H_smooth κ c s hU hKc).comp hι.contDiffOn (fun Z hZ => hZ)).congr fun Z hZ => ?_
    exact rdz_H_eq κ c s τ₀ Z (rdz_da hU hKc hZ)
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    exact key _ _
  · simp only [rdz_dzb_eq]
    exact key _ _

end Formalism.FourierDecayAlt.P
end
end

