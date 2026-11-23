module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
public import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.QminorInt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.LowWeightDensity
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.LowWeightDensity

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem signs {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) : (∃ a, ε' a = false) ∧ (∃ a, ε' a = true) := by
  obtain ⟨hfit, hε'⟩ := hG.fits
  have key0 : ∀ x, x ≠ zi e → ∃ c, x = e (Sum.inl c) := by
    intro x hx
    rcases hb : e.symm x with c | u
    · exact ⟨c, (Equiv.symm_apply_eq e).1 hb⟩
    · cases u
      exact absurd ((Equiv.symm_apply_eq e).1 hb) hx
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hG.neg
    by_cases hz : a = zi e
    · rw [hz, hfit] at ha
      exact absurd ha (by decide)
    · obtain ⟨c, rfl⟩ := key0 a hz
      exact ⟨c, by rw [← hε' c]; exact ha⟩
  · by_contra hno
    push_neg at hno
    have key : ∀ x, x ≠ zi e → ε x = false := by
      intro x hx
      obtain ⟨c, rfl⟩ := key0 x hx
      rw [hε' c]
      simpa using hno c
    have h1 : #{a : Fin (n + 1) | ε a = true} ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hx2 : x = zi e := by
        by_contra h'
        rw [key x h'] at hx
        exact absurd hx (by decide)
      have hy2 : y = zi e := by
        by_contra h'
        rw [key y h'] at hy
        exact absurd hy (by decide)
      rw [hx2, hy2]
    have hsub : Finset.univ.erase (zi e) ⊆ Finset.filter (fun a => ε a = false) Finset.univ := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact key x hx
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h2
    have h3 := hG.le
    have h4 := hG.two
    simp only [Nat.add_sub_cancel] at h2
    omega

theorem exists_ds {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hm : 1 ≤ m) (hc : Formalism.QuantumDeterminants.IsHCParam lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ := by
  have hq : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0 ReciprocityTheory.ChartRestriction.DS.pOf
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith
  have h4 : (8 * (m : ℝ)) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ (8 * (m : ℝ)) * m :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  refine ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap m ε lam hc _ hg (Or.inr ?_)
  rw [max_lt_iff]
  constructor
  · nlinarith
  · nlinarith

theorem exists_ne {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ v ∈ lowKSub ε lam σ, v ≠ 0 := by
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  obtain ⟨v, hv, hv0, -⟩ := hS0.2.2.2.1
  have hle : S0 ≤ lowKSub ε lam σ := le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS0
  exact ⟨v, hle hv, hv0⟩

theorem exists_low {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ w ∈ lowKSub ε lam σ, ‖w‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_ne hσ
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, Submodule.smul_mem _ _ hv, ?_⟩
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn]

theorem exists_P {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} {lam : Fin (n + 1) → ℝ}
    {mu : Fin n → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    {j : H' →L[ℂ] H} (hj : j ≠ 0) (hjm : IsHMap ε' e π σ j) : ∃ P : H →L[ℂ] H', Intertw ε' e π σ P ∧ P ≠ 0 := by
  obtain ⟨-, -, hπU, -⟩ := hπ
  obtain ⟨-, -, hσU, -⟩ := hσ
  have memG : ∀ h : UJ ε', emb e (um h) ∈ PI.UpqRep.UJset ε := fun h =>
    PositivityTheory.UnitaryDecomposition.Com.emb_mem hF h.2
  have memH : ∀ h : UJ ε', um h ∈ PI.UpqRep.UJset ε' := fun h => h.2
  have embmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, emb e A * emb e B = emb e (A * B) := by
    intro A B
    simp only [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have emb1 : emb e 1 = 1 := by
    simp [emb]
  have huinv : ∀ h : UJ ε', um h * um h⁻¹ = 1 := by
    intro h
    simp [um]
  have hπinner : ∀ h : UJ ε', ∀ (u x : H),
      ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
    intro h u x
    have hmul := hπU.1.2 _ (memG h) _ (memG h⁻¹)
    rw [embmul, huinv, emb1, hπU.1.1] at hmul
    have hcomp : π (emb e (um h)) (π (emb e (um h⁻¹)) u) = u := by
      have h2 := congrArg (fun T : H →L[ℂ] H => T u) hmul
      simpa using h2.symm
    let L : H →ₗᵢ[ℂ] H := ⟨(π (emb e (um h))).toLinearMap, hπU.2.1 _ (memG h)⟩
    calc ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪L (π (emb e (um h⁻¹)) u), L x⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
        show ⟪π (emb e (um h)) (π (emb e (um h⁻¹)) u), π (emb e (um h)) x⟫_ℂ = _
        rw [hcomp]
  have hσinner : ∀ h : UJ ε', ∀ (y z : H'),
      ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪y, σ (um h) z⟫_ℂ := by
    intro h y z
    have hmul := hσU.1.2 _ (memH h) _ (memH h⁻¹)
    rw [huinv, hσU.1.1] at hmul
    have hcomp : σ (um h) (σ (um h⁻¹) y) = y := by
      have h2 := congrArg (fun T : H' →L[ℂ] H' => T y) hmul
      simpa using h2.symm
    let L : H' →ₗᵢ[ℂ] H' := ⟨(σ (um h)).toLinearMap, hσU.2.1 _ (memH h)⟩
    calc ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪L (σ (um h⁻¹) y), L z⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪y, σ (um h) z⟫_ℂ := by
        show ⟪σ (um h) (σ (um h⁻¹) y), σ (um h) z⟫_ℂ = _
        rw [hcomp]
  have hjn : ‖j‖ ≠ 0 := norm_ne_zero_iff.2 hj
  have hadj : ∀ (h : UJ ε') (x : H),
      ContinuousLinearMap.adjoint j (π (emb e (um h)) x) = σ (um h) (ContinuousLinearMap.adjoint j x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right, ← hπinner, ← hjm h⁻¹ y,
      ← ContinuousLinearMap.adjoint_inner_right, hσinner]
  refine ⟨((‖j‖ : ℂ)⁻¹) • ContinuousLinearMap.adjoint j, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, LinearIsometryEquiv.norm_map,
      inv_mul_cancel₀ hjn]
  · intro h x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul, hadj]
  · intro h0
    have hc : ((‖j‖ : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hjn)
    have h1 : ContinuousLinearMap.adjoint j = 0 := by
      have := congrArg (fun T => ((‖j‖ : ℂ)) • T) h0
      simpa [smul_smul, hc] using this
    apply hj
    rw [← ContinuousLinearMap.adjoint_adjoint j, h1, map_zero]

theorem dense_sm {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hm : 2 ≤ m)
    (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hS : IsSmMod ε σ S E) : Dense (S : Set H) := by
  obtain ⟨hcs, -, hU, hI, -, ⟨K, hK⟩, -⟩ := hσ
  haveI := hcs
  obtain ⟨v, hvK, hv0, -⟩ := hK.2.2.2.1
  have hvS : v ∈ S :=
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs m ε H σ hU hI v ⟨K, hK.1, hvK, hK.2.1⟩)
  have hstab : ∀ g ∈ PI.UpqRep.UJset ε, ∀ w ∈ S.topologicalClosure, σ g w ∈ S.topologicalClosure := by
    intro g hg w hw
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hw ⊢
    exact map_mem_closure (σ g).continuous hw (fun x hx => hS.stab g hg x hx)
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure hstab with h | h
  · have hv' : v ∈ S.topologicalClosure := S.le_topologicalClosure hvS
    rw [h, Submodule.mem_bot] at hv'
    exact absurd hv' hv0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem one_le_hs' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) (j : Fin m) : 1 ≤ hs (um g) := by
  exact ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_one_le_hs g.2 j

theorem decay_low {n : ℕ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hn : 1 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu) (hσ : IsDS ε' mu σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Continuous (fun h : UJ ε' => conj ⟪w, σ (um h) w⟫_ℂ) ∧ ∃ C : ℝ, ∀ h : UJ ε',
      ‖conj ⟪w, σ (um h) w⟫_ℂ‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + (n : ℝ))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, -, hU, -⟩ := hσ
    have h1 : Continuous (fun h : UJ ε' => um h) :=
      Units.continuous_val.comp continuous_subtype_val
    have hcont : Continuous (fun h : UJ ε' => σ (um h) w) :=
      (hU.2.2 w).comp_continuous h1 (fun h => h.2)
    exact (continuous_const.inner hcont).star
  · set N : ℕ := n ^ 2 + 1 + n with hN
    refine ⟨(Real.exp 1 * √(n : ℝ)) ^ (2 * N), fun h => ?_⟩
    have hA : 2 * N ≤ 12 * (n + 1) ^ 2 := by
      rw [hN]
      nlinarith
    have hb := CompanionTheory.Lime.T3.dec_low (N := n + 1) hn (by omega) hc hσ (by push_cast; exact hg) hw hw1
      (A := 2 * N) (by omega) hA h
    have hpos : 0 ≤ hs (um h) := le_trans zero_le_one (one_le_hs' h ⟨0, hn⟩)
    have hexp : ((n : ℝ) ^ 2 + 1 + n) = (N : ℝ) := by
      rw [hN]
      push_cast
      ring
    have key : (CompanionTheory.Lime.T3.nG h)⁻¹ ^ (2 * N) = hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + n)) := by
      rw [pow_mul, inv_pow, CompanionTheory.Lime.T3.nG_sq, hexp, Real.rpow_neg hpos, Real.rpow_natCast, inv_pow]
    rw [RCLike.norm_conj, ← key]
    exact hb

end PositivityTheory.RgHe.SM.LowWeightDensity
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpaces
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpaces

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com PositivityTheory.RgHe.SM

section WS

variable {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V)

theorem one_mem_ws (L : ℕ) : (1 : Module.End ℂ V) ∈ wordSpan E L :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem_ws (a b : Fin m) : E a b ∈ wordSpan E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem ws_mul {L L' : ℕ} {T T' : Module.End ℂ V} (hT : T ∈ wordSpan E L) (hT' : T' ∈ wordSpan E L') :
    T * T' ∈ wordSpan E (L + L') := by
  have key : wordSpan E L * wordSpan E L' ≤ wordSpan E (L + L') := by
    unfold wordSpan
    rw [Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨A, ⟨w, hw, rfl⟩, B, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨w ++ w', by simp only [List.length_append]; omega, by simp [List.map_append, List.prod_append]⟩
  exact key (Submodule.mul_mem_mul hT hT')

variable {k : ℕ} (F : Fin k → Fin k → Module.End ℂ V)

theorem tm_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) (u : ℂ) (a b : Fin k) : Tm F u a b ∈ wordSpan E 1 := by
  unfold Tm
  refine Submodule.add_mem _ ?_ (hF a b)
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_ws E 1)
  · exact Submodule.zero_mem _

theorem prod_mem_ws (l : List (Module.End ℂ V)) (h : ∀ x ∈ l, x ∈ wordSpan E 1) : l.prod ∈ wordSpan E l.length := by
  induction l with
  | nil => simpa using one_mem_ws E 0
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, add_comm]
    exact ws_mul E (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem qminor_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) {t : ℕ} (a b : Fin t → Fin k) (u : ℂ) :
    qminor F a b u ∈ wordSpan E t := by
  unfold qminor
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h := prod_mem_ws E (List.ofFn fun i : Fin t => Tm F (u - (i : ℂ)) (a (σ i)) (b i)) (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact tm_mem E F hF _ _ _)
  rw [List.length_ofFn] at h
  rw [← zsmul_eq_mul]
  exact zsmul_mem h _

end WS

theorem pj_words {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1)) (hj : j ∈ X.S) :
    ∃ R : Fin (N + 1) → Module.End ℂ S, (∀ l, R l ∈ wordSpan E (N + 1)) ∧
      ∀ ζ ∈ S, ∀ l, X.p j (phi E e P ζ) l = P (ap (R l) ζ) := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  set m : Fin (N + 1) → ℂ := fun i => (mu i : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hm
  have hq : ∀ u v, qdet E' u v = (∏ i, (u + m i)) • v := cap_of hG.hc' hσ hS'
  set w : ℂ := -m j with hw
  have hPs : ∀ v : S, P v ∈ S' := fun v => (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPs v⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hf : ∀ a b (v : S), f (E (ι a) (ι b) v) = E' a b (f v) := fun a b v => Subtype.ext (by
    show P (E (ι a) (ι b) v : H) = (E' a b (f v) : H')
    rw [hS.act, hS'.act, ← blk_single (e := e)]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX v).differentiableAt) _)
  let co : (Fin (N + 1) → S') → Fin (N + 1) → H' := fun x l => x l
  have hco : ∀ x, co x ∈ SmT ε' σ := fun x l => (hS'.mem _).1 (x l).2
  let Y : (Fin (N + 1) → S') → X.S → Fin (N + 1) → S' := fun x t c =>
    ⟨X.p t (co x) c, (hS'.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩
  have hYe : ∀ x t, EE E' (Y x t) = X.κ t • Y x t := fun x t => funext fun c => Subtype.ext (by
    have := congrFun (X.cas t t.2 _ (hco x)) c
    rw [EE_apply, Submodule.coe_sum]
    simp only [hS'.act]
    exact this)
  have hYs : ∀ x, ∑ t, Y x t = x := fun x => funext fun c => Subtype.ext (by
    have := congrFun (X.sum _ (hco x)) c
    rw [Finset.sum_apply] at this
    rw [Finset.sum_apply, Submodule.coe_sum]
    exact (Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)
  set d : ℂ := ∏ i ∈ univ.erase j, (-m j + m i) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Finset.prod_ne_zero_iff]
    intro i hi h0
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    have : mu i = mu j := by
      have h1 : (mu i : ℂ) = mu j := by simp only [hm] at h0; linear_combination h0
      exact_mod_cast h1
    exact hne (hG.hc'.1.injective this)
  have hth : ∀ x, Th E' w x = d • Y x ⟨j, hj⟩ := fun x => by
    have h := th_proj hS'.gl hq univ (Y x) (fun t : X.S => X.κ t)
      (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe x t) (mem_univ (⟨j, hj⟩ : X.S)) j
      (by rw [hκ]; simp only [hm]; push_cast; ring)
    rwa [hYs] at h
  let T : Fin (N + 1) → Module.End ℂ S := fun l =>
    ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (l : ℕ))) •
      (qminor (fun a b => E (ι a) (ι b)) a.succAbove l.succAbove w * E (ι a) z)
  refine ⟨fun l => d⁻¹ • T l, fun l => ?_, fun ζ hζ l => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact ws_mul E (qminor_mem E _ (fun a b => gen_mem_ws E _ _) _ _ _) (gen_mem_ws E _ _)
  · set ζ' : S := ⟨ζ, hζ⟩
    let X0 : Fin (N + 1) → S := fun a => E (ι a) z ζ'
    let x : Fin (N + 1) → S' := fun c => f (X0 c)
    have hco' : co x = phi E e P ζ := funext fun c => by
      simp only [co, x, X0, phi, ap, dif_pos hζ]
      rfl
    have hT : T l ζ' = Th (fun a b => E (ι a) (ι b)) w X0 l := by
      rw [Th_apply]
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
      rfl
    have h1 : P (ap (d⁻¹ • T l) ζ) = d⁻¹ • (f (Th (fun a b => E (ι a) (ι b)) w X0 l) : H') := by
      simp only [ap, dif_pos hζ, LinearMap.smul_apply, Submodule.coe_smul, map_smul]
      rw [hT]
      rfl
    have h2 := (thMap S S' N (fun a b => E (ι a) (ι b)) E' f hf w X0 l).1
    rw [h1, h2, show (fun l => f (X0 l)) = x from rfl, hth x, ← hco']
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rfl

end PositivityTheory.RgHe.SM.WordSpaces
end
end

