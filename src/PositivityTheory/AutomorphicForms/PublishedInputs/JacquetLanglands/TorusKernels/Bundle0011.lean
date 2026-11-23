module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormulaProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.MultivariableReproducingLemmas

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem norm_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => hb.2.2.2.2.2.1 (k v) (z v) (w v) (hk v)

theorem cont_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (z : X I) : Continuous (qq k z) := by
  unfold qq
  exact continuous_finsetProd _ fun v _ =>
    (hb.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))

theorem integrable {I : Type} [Fintype I] (hb : B1b) (hK : KapInt) (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C)
    (z : X I) : Integrable (fun w => qq k z w * f w) := by
  obtain ⟨C1, A, h⟩ := hK I k hk
  obtain ⟨hm, hl, -⟩ := h z
  have hKi : Integrable (Kap k z) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ w, ‖Kap k z w‖ₑ = ∫⁻ w, ENNReal.ofReal (Kap k z w) := by
          congr 1; funext w; exact Real.enorm_eq_ofReal (Kap_nonneg k z w)
      _ ≤ C1 := hl
      _ < ⊤ := ENNReal.coe_lt_top
  have hc : 0 ≤ ∏ v, (((k v : ℝ) - 1) / (4 * Real.pi)) := Finset.prod_nonneg fun v _ => by
    have h4 : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    exact div_nonneg (by linarith) (by positivity)
  refine (hKi.const_mul ((∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C / nrm k z)).mono'
    ((cont_qq hb k z).mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have h1 := norm_qq hb k (fun v => le_trans (by norm_num) (hk v)) z w
  have hn := nrm_pos k z
  rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hn]
  calc ‖qq k z w‖ * ‖f w‖ * nrm k z = (‖qq k z w‖ * nrm k z) * ‖f w‖ := by ring
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * (‖f w‖ * nrm k w) := by rw [h1]; ring
    _ ≤ (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * C :=
        mul_le_mul_of_nonneg_left (hC w) (mul_nonneg hc (Kap_nonneg k z w))
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C * Kap k z w := by ring

theorem symm_eq (n : ℕ) (p : P × (Fin n → P)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem qq_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (z : X (Fin (n + 1))) (t : P) (w : Fin n → P) :
    qq k z (Fin.cons t w) = q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w := by
  simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem nrm_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (t : P) (w : Fin n → P) :
    nrm k (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k 0 : ℝ) / 2) * nrm (fun j => k j.succ) w := by
  simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem fin_case (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) : ∀ (n : ℕ) (k : Fin n → ℕ), (∀ v, 4 ≤ k v) →
    ∀ f : X (Fin n) → ℂ, SepHol f → ∀ C, (∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z, ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  intro n
  induction n with
  | zero =>
    intro k hk f hf C hC z
    have hF : (fun w => qq k z w * f w) = fun _ => f z := funext fun w => by
      rw [Subsingleton.elim w z]; simp [qq]
    rw [hF, show (volume : Measure (X (Fin 0))) = Measure.dirac z from Measure.pi_of_empty _ z,
      integral_const]
    simp
  | succ n ih =>
    intro k hk f hf C hC z
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
    have hI := integrable hb hK k hk f hf.1 C hC z
    have hG : Integrable (fun p : P × (Fin n → P) =>
        q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 * f (Fin.cons p.1 p.2))
        ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
      have := (hmp.symm.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2 hI
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply, symm_eq, qq_cons]
    have hin : ∀ w : Fin n → P, ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
        f (Fin.cons t w) = qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
      intro w
      have hol : Hol1 fun t => f (Fin.cons t w) := by
        have h := hf.2 (Fin.cons (z 0) w) 0
        convert h using 3 with t
        funext j
        induction j using Fin.cases <;> simp
      have hbd : ∃ C', ∀ t : P, ‖f (Fin.cons t w)‖ * |t.1.im| ^ ((k 0 : ℝ) / 2) ≤ C' := by
        refine ⟨C / nrm (fun j => k j.succ) w, fun t => ?_⟩
        rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← nrm_cons]
        exact hC _
      have h := (h3 (k 0) (hk 0) (fun t => f (Fin.cons t w)) hol hbd (z 0)).2
      calc ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons t w)
          = ∫ t, qq (fun j => k j.succ) (fun j => z j.succ) w * (q1 (k 0) (z 0) t * f (Fin.cons t w)) := by
            congr 1; funext t; ring
        _ = _ := by rw [integral_const_mul, h]
    have hsep : SepHol fun w : X (Fin n) => f (Fin.cons (z 0) w) := by
      refine ⟨hf.1.comp (continuous_pi fun j => ?_), fun w v => ?_⟩
      · induction j using Fin.cases
        · simpa using continuous_const
        · simpa using continuous_apply _
      · have h := hf.2 (Fin.cons (z 0) w) v.succ
        convert h using 3 with t
        funext j
        induction j using Fin.cases with
        | zero => simp [(Fin.succ_ne_zero v).symm]
        | succ j =>
          simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]
          split_ifs <;> simp_all
    have hbd : ∀ w : X (Fin n), ‖f (Fin.cons (z 0) w)‖ * nrm (fun j => k j.succ) w ≤
        C / |(z 0).1.im| ^ ((k 0 : ℝ) / 2) := by
      intro w
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (z 0).2) _), mul_assoc, mul_comm (nrm _ _), ← nrm_cons]
      exact hC _
    calc ∫ w, qq k z w * f w
        = ∫ p, (fun w => qq k z w * f w)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p)
            ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
          (hmp.symm.integral_comp' _).symm
      _ = ∫ p : P × (Fin n → P), q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 *
            f (Fin.cons p.1 p.2) ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
          congr 1; funext p; simp only [symm_eq, qq_cons]
      _ = ∫ w : Fin n → P, (∫ t : P, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
            f (Fin.cons t w)) ∂(Measure.pi fun _ : Fin n => (volume : Measure P)) := integral_prod_symm _ hG
      _ = ∫ w : X (Fin n), qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
          congr 1; funext w; exact hin w
      _ = f (Fin.cons (z 0) (fun j => z j.succ)) := ih _ (fun v => hk _) _ hsep _ hbd _
      _ = f z := congrArg f (Fin.cons_self_tail z)

theorem main (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) (I : Type) [Fintype I] (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : SepHol f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C) (z : X I) :
    ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ : ∀ (w : X I) j, φ w j = w (σ.symm j) := by
    intro w j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [MeasurableEquiv.coe_piCongrLeft]
    exact this
  have hmp : MeasurePreserving φ (volume : Measure (X I)) (volume : Measure (X (Fin (Fintype.card I)))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) := by
    refine ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => ?_⟩
    have h := hf.2 (fun i => w' (σ i)) (σ.symm j)
    convert h using 3 with t
    funext i
    have heq : σ i = j ↔ i = σ.symm j := by
      constructor
      · intro h; exact σ.injective (by simpa using h)
      · intro h; simpa [h]
    simp only [Function.update_apply]
    rw [heq]
  have hnrm : ∀ w' : X (Fin (Fintype.card I)), nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) := by
    intro w'
    exact Fintype.prod_equiv σ.symm _ _ fun j => by simp
  have hbd : ∀ w' : X (Fin (Fintype.card I)), ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    intro w'; rw [hnrm]; exact hC _
  have hqq : ∀ w : X I, qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w := by
    intro w
    simp only [qq, hφ]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' *
          f fun i => w' (σ i)) (φ w) := by
        congr 1; funext w; simp only [hqq, hφ, Equiv.symm_apply_apply]
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : X (Fin (Fintype.card I)) =>
          qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f fun i => z (σ.symm (σ i)) := fin_case ha hb h3 hK _ _ (fun v => hk _) _ hsep C hbd _
    _ = f z := by simp only [Equiv.symm_apply_apply]

end UpperTheory.Esk.MultivariableReproducingLemmas

open UpperTheory.Esk.MultivariableReproducingLemmas in
theorem UpperTheory.Esk.multivariable_reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B3 → UpperTheory.Esk.KapInt → UpperTheory.Esk.MultivariableReproducingFormula := by
  intro ha hb h3 hK I _ k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  exact ⟨integrable hb hK k hk f hf.1 C hC z, main ha hb h3 hK I k hk f hf C hC z⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfEcut
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk

def iN : P := ⟨-Complex.I, by simp⟩

def bs {I : Type} (e : I → Bool) : X I := fun v => if e v then iP else iN

theorem kap_pos (a z : P) (ha : a.1.im = 1 ∨ a.1.im = -1) (h : 0 < a.1.im * z.1.im) : 0 < kap a z := by
  unfold kap
  rw [if_pos h]
  apply div_pos (by linarith)
  apply pow_pos
  apply norm_pos_iff.2
  intro h0
  have h1 := congrArg Complex.im h0
  simp at h1
  rcases ha with ha | ha <;> rw [ha] at h h1 <;> nlinarith

theorem kap_bs_pos {I : Type} (z : X I) (v : I) :
    0 < kap (bs (fun i => decide (0 < (z v).1.im)) v) (z v) := by
  have hz := (z v).2
  unfold bs
  by_cases h : 0 < (z v).1.im
  · simp only [h, decide_true, if_true]
    exact kap_pos _ _ (Or.inl (by simp [iP])) (by simpa [iP] using h)
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    exact kap_pos _ _ (Or.inr (by simp [iN])) (by simp [iN]; linarith)

theorem Kap_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hk0 _ _) _


open Classical in
def uX {I : Type} [Fintype I] (z : X I) : ℝ := by
  classical
  exact ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z

theorem uX_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 ≤ uX z :=
  Finset.sum_nonneg fun e _ => Kap_nonneg hk0 _ _ _

theorem uX_pos {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 < uX z := by
  classical
  unfold uX
  refine Finset.sum_pos' (fun e _ => Kap_nonneg hk0 _ _ _) ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, ?_⟩
  exact Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (kap_bs_pos z v) _

theorem uX_cont {I : Type} [Fintype I] (hkc : Continuous fun p : P × P => kap p.1 p.2) :
    Continuous (uX : X I → ℝ) := by
  unfold uX Kap
  refine continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ => ?_
  exact (hkc.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)

theorem tsum_le_fiber {G Ω : Type} (φ : G → Ω) (w : Ω → ℝ≥0∞) (K : G → ℝ≥0∞) (M : ℝ≥0∞)
    (hK : ∀ ω', ∑' g : {g // φ g = ω'}, K g.1 ≤ M) : ∑' g, w (φ g) * K g ≤ (∑' ω', w ω') * M := by
  rw [← ENNReal.tsum_fiberwise _ φ, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ω' => ?_
  calc ∑' b : φ ⁻¹' {ω'}, w (φ b) * K b = ∑' b : φ ⁻¹' {ω'}, w ω' * K b :=
        tsum_congr fun b => by rw [show φ b = ω' from b.2]
    _ = w ω' * ∑' b : φ ⁻¹' {ω'}, K b := ENNReal.tsum_mul_left
    _ ≤ w ω' * M := by gcongr; exact hK ω'

end UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk in
open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_Ecut : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.Ecut := by
  classical
  intro _ hB hC hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount
  have : Countable D.Om := hax.cO
  obtain ⟨hk0', -, -, -, hkc, -⟩ := hB
  have hk0 : ∀ z w : P, 0 ≤ kap z w := fun z w => (hk0' z w).1
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  have hmX : ∀ g : PG F, Measurable fun z : D.Xs => g • z := fun g => (hpres g).measurable
  have hfib : ∀ y : D.Y, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • y.2 : D.Xs)) ≤ M := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1)
    exact ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (TruncationKernelLemmas.bs e)⟩
  have hucont : Continuous (TruncationKernelLemmas.uX : X I → ℝ) := TruncationKernelLemmas.uX_cont hkc
  have hsplit : ∀ z : X I, ENNReal.ofReal (TruncationKernelLemmas.uX z) =
      ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) z) := by
    intro z
    rw [TruncationKernelLemmas.uX, ENNReal.ofReal_sum_of_nonneg (fun e _ => TruncationKernelLemmas.Kap_nonneg hk0 _ _ _)]
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  set w : D.Om → ℝ := fun ω => (1 / 2 : ℝ) ^ f ω with hw
  have hW : ∑' ω, ENNReal.ofReal (w ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n))
      ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n))).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
  refine ⟨?_, ?_⟩
  · refine (hC (PG F) D.Y).1 ?_ (fun y => w y.1 * TruncationKernelLemmas.uX y.2) ?_ ?_ ?_ ?_
    · intro g
      exact (Measurable.of_discrete.comp measurable_fst).prodMk ((hmX g).comp measurable_snd)
    · have h1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
      have h2 : Measurable fun y : D.Y => TruncationKernelLemmas.uX (y.2 : X I) := hucont.measurable.comp measurable_snd
      exact h1.mul h2
    · exact fun y => mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _)
    · exact fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (TruncationKernelLemmas.uX_pos hk0 y.2)⟩
    · intro y
      obtain ⟨M, hM, hMb⟩ := hfib y
      have hle : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≤
          ∑ e : I → Bool, (∑' ω, ENNReal.ofReal (w ω)) * M := by
        calc ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2)
            = ∑' g : PG F, ∑ e : I → Bool, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) := by
              refine tsum_congr fun g => ?_
              exact (ENNReal.ofReal_mul (by positivity)).trans
                ((congrArg (fun t => ENNReal.ofReal (w (g • y.1)) * t) (hsplit _)).trans (by rw [Finset.mul_sum]; rfl))
          _ = ∑ e : I → Bool, ∑' g : PG F, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ => TruncationKernelLemmas.tsum_le_fiber (fun g : PG F => g • y.1)
                (fun ω => ENNReal.ofReal (w ω))
                (fun g : PG F => ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs))) M (hMb e)
      have hfin : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _))
  · intro ω S hS
    refine (hC S D.Xs).1 ?_ TruncationKernelLemmas.uX ?_ ?_ ?_ ?_
    · intro g
      exact hmX (g : PG F)
    · exact hucont.measurable
    · exact TruncationKernelLemmas.uX_nonneg hk0
    · exact fun z => ⟨1, by simpa using TruncationKernelLemmas.uX_pos hk0 z⟩
    · intro z
      obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
      have hinj : Function.Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h
      have hle : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≤ ∑ e : I → Bool, M := by
        calc ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs))
            = ∑' g : S, ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              tsum_congr fun g => hsplit _
          _ = ∑ e : I → Bool, ∑' g : S, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ =>
              (ENNReal.tsum_comp_le_tsum_of_injective hinj
                (fun γ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} =>
                  ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • ((ω, z) : D.Y).2 : D.Xs)))).trans (hMb e ω)
      have hfin : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (TruncationKernelLemmas.uX_nonneg hk0 _)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFsum
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UpperTheory.Esk.SummedOrbitIntegrals

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

theorem meas_pair [Countable α] {E : Type*} [MeasurableSpace E] {f : α → β → E} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have e : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a : α, ({a} : Set α) ×ˢ (f a ⁻¹' s) := by
    ext ⟨a, b⟩
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hs)

theorem lint_pair (μ : Measure β) [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂(Measure.count.prod μ) = ∑' a, ∫⁻ y, f (a, y) ∂μ := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_count]

theorem count_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  refine Measure.ext_iff_singleton.2 fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

end UpperTheory.Esk.SummedOrbitIntegrals

open UpperTheory.Esk.SummedOrbitIntegrals in
theorem UpperTheory.Esk.pf_Fsum : UpperTheory.Esk.E0a → UpperTheory.Esk.Fsum := by
  intro h0 F I Gf _ _ _ D hax
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  haveI : Countable D.Cj := hcG
  haveI : Countable D.Om := hax.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : SFinite D.μY := by unfold UpperTheory.Esk.Dat.μY; infer_instance
  intro b hb
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun p => hb.nonneg _,
    fun p => hb.sum (p.1.2, p.2)⟩, ?_⟩
  intro u hu hfin
  have hgm : Measurable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) :=
    meas_pair (f := fun (c : D.Cj) (y : D.Y) => b y • u (D.el c) y) fun c => hb.meas.smul (hu (D.el c))
  have hlin : ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) =
      ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
    calc ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY)
        = ∑' c : D.Cj, ∫⁻ y, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          lint_pair D.μY (fun q : D.Cj × D.Y => ‖b q.2 • u (D.el q.1) q.2‖ₑ) hgm.enorm
      _ = ∫⁻ y, ∑' c : D.Cj, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          (lintegral_tsum fun c => ((hb.meas.smul (hu (D.el c))).enorm).aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
          refine lintegral_congr fun y => ?_
          simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]
          exact ENNReal.tsum_mul_left
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ⊤
    rw [hlin]
    exact hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    have hy' : Integrable (fun c : D.Cj => b y • u (D.el c) y) Measure.count := hy
    rw [integral_countable hy']
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact tsum_const_smul'' (b y)
  have hP : Integrable (fun y => b y • ∑' γ, u γ y) D.μY := hgi.integral_prod_right.congr hae
  have hm1 : Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) :=
    meas_pair (α := D.Cj × D.Om) (β := D.Xs) (f := fun a z => u (D.el a.1) (a.2, z))
      fun a => (hu (D.el a.1)).comp measurable_prodMk_left
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs)
      D.μC (Measure.count.prod D.μY) := by
    have e : D.μC = (Measure.count.prod Measure.count).prod volume := by
      unfold UpperTheory.Esk.Dat.μC
      rw [count_prod]
    rw [e]
    exact measurePreserving_prodAssoc _ _ _
  have hC : Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  have hint : ∫ y, b y • ∑' γ, u γ y ∂D.μY =
      ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC := by
    calc ∫ y, b y • ∑' γ, u γ y ∂D.μY
        = ∫ y, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) ∂D.μY := (integral_congr_ae hae).symm
      _ = ∫ q, b q.2 • u (D.el q.1) q.2 ∂(Measure.count.prod D.μY) := (integral_prod_symm _ hgi).symm
      _ = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC :=
          (hmp.integral_comp' (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2)).symm
  exact ⟨hm1, hC, hP, hint⟩
end
end

