module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJAvg

theorem eval_bounded_on_box {σ : Type} (p : MvPolynomial σ ℂ) (M : σ → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : σ → ℂ, (∀ v, ‖x v‖ ≤ M v) → ‖eval x p‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, fun x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp; obtain ⟨B2, h2, hB2⟩ := hq
    exact ⟨B1 + B2, by positivity, fun x hx => by
      rw [map_add (f := _)]; exact (norm_add_le _ _).trans (add_le_add (hB1 x hx) (hB2 x hx))⟩
  | mul_X p n hp =>
    obtain ⟨B, h0, hB⟩ := hp
    refine ⟨B * max (M n) 0, by positivity, fun x hx => ?_⟩
    rw [map_mul, eval_X, norm_mul]
    exact mul_le_mul (hB x hx) ((hx n).trans (le_max_left _ _)) (norm_nonneg _) h0

def univSubst {ι : Type} [Fintype ι] {a b : ℕ} (P : FP ι a b) :
    MvPolynomial (ι × Fin b × Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j)) P

theorem mvZ_one_eq_map_univSubst {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b) :
    mvZ g (fun _ => 1) P = map (eval fun w => g w.1 w.2.1 w.2.2) (univSubst P) := by
  have : (mvZ g (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) : FP ι a b →ₐ[ℂ] FP ι a b) =
      (MvPolynomial.mapAlgHom (aeval fun w : ι × Fin a × Fin a => g w.1 w.2.1 w.2.2)).comp
        (aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j))) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mvZ, aeval_X, AlgHom.comp_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      apply_ite C, C_0, map_sum, map_mul, mapAlgHom_apply, map_C, map_X]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq', coe_aeval_eq_eval]
  have h := DFunLike.congr_fun this P
  rw [h]; rfl

theorem linear_eq_sum_coeff {σ : Type} (Λ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (S : Finset (σ →₀ ℕ)) (p : MvPolynomial σ ℂ)
    (hp : p.support ⊆ S) : Λ p = ∑ m ∈ S, AddMonoidAlgebra.coeff p m * Λ (monomial m 1) := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_subset hp]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [show monomial m (AddMonoidAlgebra.coeff p m) = AddMonoidAlgebra.coeff p m • monomial m (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

section
variable {ι : Type} [Fintype ι] {a : ℕ} {K : Type} [Group K] [TopologicalSpace K]
  {r : K → ι → Matrix (Fin a) (Fin a) ℂ}

theorem ontoUni_one (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm : r 1 τ * r 1 τ = r 1 τ := by rw [← hr.mul, one_mul]
  have hu : star (r 1 τ) * r 1 τ = 1 := (Matrix.mem_unitaryGroup_iff'.mp (hr.uni 1 τ))
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := by rw [mul_assoc]
    _ = 1 := by rw [hm, hu]

theorem ontoUni_inv (hr : OntoUni r) (k : K) (τ : ι) : (r k τ)⁻¹ = r k⁻¹ τ :=
  Matrix.inv_eq_left_inv (by rw [← hr.mul, inv_mul_cancel, ontoUni_one hr])

theorem integrable_avg_term [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (hr : OntoUni r) (p : MvPolynomial (ι × Fin a × Fin a) ℂ) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F) ν := by
  simp only [evalAt]
  have hc : Continuous (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p *
      eval (fun x => (r k x.1 * y x.1) x.2.1 x.2.2) F) := by
    apply Continuous.mul
    · exact (MvPolynomial.continuous_eval p).comp (continuous_pi fun w =>
        (((continuous_apply w.1).comp (hr.cont.comp continuous_inv))).matrix_elem _ _)
    · exact (MvPolynomial.continuous_eval F).comp (continuous_pi fun w =>
        ((((continuous_apply w.1).comp hr.cont)).matrix_mul continuous_const).matrix_elem _ _)
  obtain ⟨B1, h1, hB1⟩ := GlobalTheory.KJAvg.eval_bounded_on_box p (fun _ => 1)
  obtain ⟨B2, h2, hB2⟩ := GlobalTheory.KJAvg.eval_bounded_on_box F (fun w => ∑ l, ‖y w.1 l w.2.2‖)
  refine Integrable.of_bound hc.aestronglyMeasurable (B1 * B2) (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_mul]
  refine mul_le_mul (hB1 _ fun w => entry_norm_bound_of_unitary (hr.uni _ _) _ _) (hB2 _ fun w => ?_)
    (norm_nonneg _) h1
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary (hr.uni _ _) _ _)

end

theorem avg_span : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), 0 < a → ∀ (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b), ∃ (m : ℕ) (y' : Fin m → ι → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ), (∀ j, IsInv (y' j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν = ∑ j, s j * Λ (subY hab (y' j) F) := by
  intro ι _ a b hab ha lam n K _ _ _ _ _ ν _ _ r hr y P
  obtain ⟨-, hcomp, -, -, -, hev, -, -⟩ := _root_.GlobalTheory.KJInf.substIdentities ι a b hab
  let S := (univSubst P).support
  let c : (ι × Fin b × Fin a →₀ ℕ) → K → ℂ := fun m k =>
    eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) (AddMonoidAlgebra.coeff (univSubst P) m)
  have hΛ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) =
      ∑ m ∈ S, c m k * Λ (monomial m 1) := by
    intro Λ k
    rw [mvZ_one_eq_map_univSubst, linear_eq_sum_coeff Λ S _ (support_map_subset _ _)]
    simp only [coeff_map]
    rfl
  have hint : ∀ m F, Integrable (fun k => c m k * evalAt (fun τ => r k τ * y τ) F) ν :=
    fun m F => integrable_avg_term ν hr _ y F
  let φ : (ι × Fin b × Fin a →₀ ℕ) → PY ι a →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun F => ∫ k, c m k * evalAt (fun τ => r k τ * y τ) F ∂ν
      map_add' := fun F G => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (F + G) =
            c m k * evalAt (fun τ => r k τ * y τ) F + c m k * evalAt (fun τ => r k τ * y τ) G := by
          intro k; simp only [evalAt, map_add (f := _), mul_add]
        simp only [e]
        exact integral_add (hint m F) (hint m G)
      map_smul' := fun t F => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (t • F) =
            t * (c m k * evalAt (fun τ => r k τ * y τ) F) := by
          intro k; simp only [evalAt, smul_eval]; ring
        simp only [e, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  let Q : PY ι a →ₗ[ℂ] FP ι a b := ∑ m ∈ S, (φ m).smulRight (monomial m 1)
  have hQ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) F, Λ (Q F) =
      ∫ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν := by
    intro Λ F
    have e : ∀ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F =
        ∑ m ∈ S, c m k * evalAt (fun τ => r k τ * y τ) F * Λ (monomial m 1) := by
      intro k; rw [hΛ, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e]
    rw [integral_finsetSum _ (fun m _ => (hint m F).mul_const _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_mul_const]; rfl
  have heq : ∀ u, IsUni u → ∀ F ∈ Vn lam n, Q (lft u F) = mvZ u (fun _ => 1) (Q F) := by
    intro u hu F _
    obtain ⟨k0, rfl⟩ := hr.onto u hu
    ext m'
    have h1 := hQ (lcoeff ℂ m') (lft (r k0) F)
    have h2 := hQ ((lcoeff ℂ m').comp (mvZ (r k0) (fun _ => 1)).toLinearMap) F
    simp only [lcoeff_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1 h2
    rw [h1, h2]
    conv_rhs => rw [← integral_mul_left_eq_self _ k0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have e1 : (fun τ => r (k0 * k)⁻¹ τ * r k0 τ) = fun τ => r k⁻¹ τ := by
      funext τ; rw [← hr.mul]; congr 2; group
    have e2 : (fun τ => r (k0 * k) τ * y τ) = fun τ => r k0 τ * (r k τ * y τ) := by
      funext τ; rw [hr.mul, mul_assoc]
    dsimp only
    rw [hev, hcomp, e1, e2, mul_one]
  obtain ⟨m, y', s, hinv, hspan⟩ := _root_.GlobalTheory.KJInf.howeSpan_all ι a b hab ha lam n Q heq
  refine ⟨m, y', s, hinv, fun F hF Λ => ?_⟩
  simp_rw [ontoUni_inv hr]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hQ, hspan F hF, map_sum]
  simp [map_smul]

end GlobalTheory.KJAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindex
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_torusElt_eq {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]

theorem sum_indic {n : Type} [Fintype n] [DecidableEq n] (s : Finset n) : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic, Finset.sum_ite_mem]

theorem reGL_symm_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m k) : GlobalTheory.ChainStepSupp.reGL k e.symm (GlobalTheory.ChainStepSupp.reGL k e g) = g := by
  ext i j
  simp [GlobalTheory.ChainStepSupp.val_reGL]

theorem reGL_mem_KO_iff {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} : GlobalTheory.ChainStepSupp.reGL k e g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => reGL_symm_reGL e g ▸ GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm h, GlobalTheory.ChainStepSupp.reGL_mem_KO e⟩

theorem unram_det_KO {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ KO k n) : μ₀ (GeneralLinearGroup.det κ) = 1 :=
  hμ _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hκ))

theorem unram_det_dcoset {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ}
    {s : Finset n} {g : GL n k}
    (h : ∃ κ ∈ KO k n, ∃ κ' ∈ KO k n, g = κ * torusElt k n ϖ (indic s) * κ') :
    μ₀ (GeneralLinearGroup.det g) = μ₀ ϖ ^ s.card := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := h
  rw [map_mul, map_mul, map_mul, map_mul, unram_det_KO hμ hκ, unram_det_KO hμ hκ', det_torusElt_eq, sum_indic,
    map_zpow, one_mul, mul_one, zpow_natCast]


open Classical in
theorem isRepsK_image {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g₀ : GL m k} {R : Finset (GL m k)} (hR : IsRepsK g₀ R) :
    IsRepsK (GlobalTheory.ChainStepSupp.reGL k e g₀) (R.image (GlobalTheory.ChainStepSupp.reGL k e)) := by
  refine ⟨fun g' hg' => ?_, fun κ hκ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hR.1 g hg
    exact ⟨_, GlobalTheory.ChainStepSupp.reGL_mem_KO e ha, _, GlobalTheory.ChainStepSupp.reGL_mem_KO e hb, by simp only [map_mul]⟩
  · obtain ⟨g, ⟨hg, hgK⟩, huniq⟩ := hR.2 (GlobalTheory.ChainStepSupp.reGL k e.symm κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm hκ)
    have key : ∀ x : GL m k, (GlobalTheory.ChainStepSupp.reGL k e x)⁻¹ * (κ * GlobalTheory.ChainStepSupp.reGL k e g₀) =
        GlobalTheory.ChainStepSupp.reGL k e (x⁻¹ * (GlobalTheory.ChainStepSupp.reGL k e.symm κ * g₀)) := by
      intro x
      rw [map_mul, map_mul, map_inv, GlobalTheory.ChainStepSupp.reGL_reGL_symm]
    refine ⟨GlobalTheory.ChainStepSupp.reGL k e g, ⟨Finset.mem_image_of_mem _ hg, ?_⟩, ?_⟩
    · rw [key]; exact GlobalTheory.ChainStepSupp.reGL_mem_KO e hgK
    · rintro y ⟨hy, hyK⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      rw [key, reGL_mem_KO_iff] at hyK
      rw [huniq x ⟨hx, hyK⟩]

theorem twist_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  intro k _ _ _ _ D _ _ N ε ϖ hϖ μ₀ hμ β f hf hH f₂ hf₂
  classical
  refine ⟨fun κ hκ m => ?_, fun s R hR m => ?_⟩
  · have hk1 := unram_det_KO hμ hκ
    have hρ := hf (GlobalTheory.ChainStepSupp.reGL k ε κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO ε hκ) (GlobalTheory.ChainStepSupp.reGL k ε m)
    simp only [hf₂, map_mul, hk1, one_mul, mul_one, hρ.1, hρ.2, and_self]
  · set ρ := GlobalTheory.ChainStepSupp.reGL k ε with hρdef
    set s' := s.map ε.toEmbedding with hs'
    have ht : ρ (torusElt k (Fin N) ϖ (indic s)) = torusElt k D ϖ (indic s') := by
      rw [hρdef, GlobalTheory.ChainStepSupp.reGL_torusElt]
      congr 1
      funext d
      simp [indic, hs', Finset.mem_map_equiv]
    have hR' : IsRepsK (torusElt k D ϖ (indic s')) (R.image ρ) := ht ▸ isRepsK_image ε hR
    have hcard : Fintype.card D = N := (Fintype.card_congr ε).symm.trans (Fintype.card_fin N)
    have hH' := hH s' _ hR' (ρ m)
    rw [Finset.sum_image (fun x _ y _ h => ρ.injective h), hs', Finset.card_map, hcard] at hH'
    have hterm : ∀ g ∈ R, f₂ (m * g) = ((((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
        (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card) * f (ρ m * ρ g) := by
      intro g hg
      rw [hf₂, map_mul, map_mul, map_mul, unram_det_dcoset hμ (hR.1 g hg), mul_inv, Units.val_mul, ← inv_pow,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hH', hf₂]
    ring

end GlobalTheory.TwistRenumber

end
end

