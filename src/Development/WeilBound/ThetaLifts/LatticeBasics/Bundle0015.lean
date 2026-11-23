module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0012
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

def nf (z : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (z i)

def fn (z : κ → AF F) : κ → Af F := fun i => (z i).2

omit [Fintype κ] in
theorem pt_self (z : κ → AF F) : pt (nf z) (fn z) = z :=
  funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

theorem nf_pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : nf (pt x y) = x := evI_pt x y

omit [Fintype κ] in
theorem nf_add (z z' : κ → AF F) : nf (z + z') = nf z + nf z' := funext fun _ => evI_add _ _

def DP (a : κ → mixedEmbedding.mixedSpace F) (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (Φ : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  fun z => fderiv ℝ (fun x => Φ (pt x (fn z))) (nf z) a + (-(2 * Real.pi * Complex.I) * (L (nf z) : ℂ)) * Φ z

def D (w : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := DP (nf w.1) (linForm (nf w.2))

theorem linForm_add (b b' : κ → mixedEmbedding.mixedSpace F) : linForm (b + b') = linForm b + linForm b' := by
  ext y
  simp only [add_apply, linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem DP_add_left (a a' L L') (Φ : (κ → AF F) → ℂ) : DP (a + a') (L + L') Φ = DP a L Φ + DP a' L' Φ := by
  funext z
  simp only [DP, map_add (f := _), add_apply, Pi.add_apply]
  push_cast
  ring

theorem DP_smul_left (t : ℝ) (a L) (Φ : (κ → AF F) → ℂ) : DP (t • a) (t • L) Φ = (t : ℂ) • DP a L Φ := by
  funext z
  simp only [DP, map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem D_add_left (w w') (Φ : (κ → AF F) → ℂ) : D (w + w') Φ = D w Φ + D w' Φ := by
  rw [D, Prod.fst_add, Prod.snd_add, nf_add, nf_add, linForm_add, DP_add_left]; rfl

theorem slice {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (y : κ → Af F) : ∃ f : SInf F κ, ∀ x, Φ (pt x y) = f x := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, -, rfl⟩ := h; exact ⟨g y • f, fun x => by rw [pureA_pt, mul_comm]; rfl⟩
  | zero => exact ⟨0, fun _ => rfl⟩
  | add _ _ _ _ h h' => obtain ⟨f, e⟩ := h; obtain ⟨f', e'⟩ := h'; exact ⟨f + f', fun x => by rw [Pi.add_apply, e, e']; rfl⟩
  | smul c _ _ h => obtain ⟨f, e⟩ := h; exact ⟨c • f, fun x => by rw [Pi.smul_apply, e]; rfl⟩

theorem DP_pt {Φ : (κ → AF F) → ℂ} {y : κ → Af F} {f : SInf F κ} (e : ∀ x, Φ (pt x y) = f x) (a L x) :
    DP a L Φ (pt x y) = dop a L f x := by
  rw [dop_apply, DP, nf_pt, e]
  exact congrArg (fun g => fderiv ℝ g x a + _) (funext e)

theorem DP_add {Φ Ψ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (h' : Ψ ∈ schA F κ) (a L) : DP a L (Φ + Ψ) = DP a L Φ + DP a L Ψ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  obtain ⟨g, e'⟩ := slice h' (fn z)
  rw [← pt_self z, Pi.add_apply, DP_pt e, DP_pt e', DP_pt (f := f + g) fun x => by rw [Pi.add_apply, e, e']; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_add f g)

theorem DP_smul {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (c : ℂ) (a L) : DP a L (c • Φ) = c • DP a L Φ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, Pi.smul_apply, DP_pt e, DP_pt (f := c • f) fun x => by rw [Pi.smul_apply, e]; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul c f)

theorem DP_zero (a L) : DP a L (0 : (κ → AF F) → ℂ) = 0 := funext fun z => by simp [DP]

theorem DP_pure (f : SInf F κ) (g : (κ → Af F) → ℂ) (a L) : DP a L (pureA F f g) = pureA F (dop a L f) g := by
  funext z
  rw [← pt_self z, DP_pt (f := g (fn z) • f) fun x => by rw [pureA_pt, mul_comm]; rfl, pureA_pt, mul_comm]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul _ f)

theorem DP_mem {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (a L) : DP a L Φ ∈ schA F κ := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, hg, rfl⟩ := h; rw [DP_pure]; exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero => rw [DP_zero]; exact zero_mem _
  | add _ _ h1 h2 h h' => rw [DP_add h1 h2]; exact add_mem h h'
  | smul c _ h1 h => rw [DP_smul h1]; exact Submodule.smul_mem _ _ h

theorem schr_pt (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) (Ψ : (κ → AF F) → ℂ) (t : ℝ) (x y) :
    schr ψ (realAd F t • w) Ψ (pt x y) = hl (nf w.1) (linForm (nf w.2)) t (fun x => Ψ (pt x y)) x := by
  have ha : At (evI F) w.1 := fun s hs => congrArg Prod.fst (hw s hs)
  have hb : At (evI F) w.2 := fun s hs => congrArg Prod.snd (hw s hs)
  have e : pt x y + realAd F t • w.1 = pt (x + t • nf w.1) y := by
    rw [← pt_self (pt x y + realAd F t • w.1)]
    congr 1
    · rw [nf_add, nf_pt]; congr 1; funext i; simp [nf, evI_mul, evI_realAd, Algebra.smul_def]
    · funext i
      show y i + (realAd F t).2 * (w.1 i).2 = y i
      rw [snd_eq_zero ha, mul_zero, add_zero]
  show ψ (pt x y ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2))) * Ψ (pt x y + realAd F t • w.1) = _
  rw [phase_line ψ hψ _ _ _ hb t, e, evI_half_trace, evI_pt]
  simp only [hl, linForm_apply]
  rfl

theorem hasD (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (z) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ z) (D w Φ z) 0 := by
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, D, DP_pt e]
  simp only [schr_pt hψ hw, e]
  exact hasDerivAt_hl _ _ f _

theorem eval_adm (z : κ → AF F) : (LinearMap.proj z : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fn z) • (BoundedContinuousFunction.evalCLM ℂ (nf z) ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ),
    fun _ => mul_comm _ _⟩

structure Imp (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) :
    Prop where
  pres : ∀ φ ∈ schA F κ, T φ ∈ schA F κ
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ
  add : ∀ w w', g (w + w') = g w + g w'
  smul : ∀ (c : AF F) w, g (c • w) = c • g w
  impl : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ (g w) (T φ)

variable {T : Module.End ℂ ((κ → AF F) → ℂ)} {g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)}

theorem Imp.at (h : Imp ψ T g) {w} (hw : At (evI F) w) : At (evI F) (g w) := fun s hs => by
  rw [← h.smul, hw s hs, ← zero_smul (AF F) (0 : (κ → AF F) × (κ → AF F)), h.smul, zero_smul, zero_smul]

theorem Imp.of_ne (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) (ha : nf w.1 ≠ 0) {Φ} (hΦ : Φ ∈ schA F κ) :
    T (D w Φ) = D (g w) (T Φ) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    have hs : Φ ∈ schA F κ := Submodule.subset_span hm
    obtain ⟨f, φ, hφ, rfl⟩ := hm
    obtain ⟨G, hG, hD⟩ := hl_line_deriv (nf w.1) (linForm (nf w.2)) f
    funext z
    obtain ⟨S, hS⟩ := h.adm _ (eval_adm z) φ hφ
    have h1 := hD ha S
    have e : (fun t => S (G t)) = fun t : ℝ => schr ψ (realAd F t • g w) (T (pureA F f φ)) z := funext fun t => by
      rw [← hS, ← h.smul, ← h.impl _ _ hs]
      refine congrArg (fun Ψ => T Ψ z) (funext fun z' => ?_)
      rw [← pt_self z', schr_pt hψ hw, pureA_pt, hG]
      simp only [pureA_pt, hl, mul_assoc]
    rw [e, ← hS] at h1
    rw [D, DP_pure]
    exact h1.unique (hasD hψ (h.at hw) (h.pres _ hs) z)
  | zero => simp only [D, DP_zero, map_zero]
  | add _ _ h1 h2 i1 i2 => simp only [D] at *; rw [DP_add h1 h2, map_add (f := _), map_add (f := _), DP_add (h.pres _ h1) (h.pres _ h2), i1, i2]
  | smul c _ h1 i1 => simp only [D] at *; rw [DP_smul h1, map_smul, map_smul, DP_smul (h.pres _ h1), i1]

theorem at_pt (x : κ → mixedEmbedding.mixedSpace F) : At (evI F) (pt x (0 : κ → Af F)) := fun s hs => by
  have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
  funext i
  refine Prod.ext ?_ ?_
  · show s.1 * _ = 0
    rw [h1, zero_mul]
  · show s.2 * 0 = 0
    rw [mul_zero]

theorem Imp.inter (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) {Φ} (hΦ : Φ ∈ schA F κ) : T (D w Φ) = D (g w) (T Φ) := by
  by_cases ha : nf w.1 = 0
  · rcases subsingleton_or_nontrivial (κ → mixedEmbedding.mixedSpace F) with hV | hV
    · have z : ∀ a L (Ψ : (κ → AF F) → ℂ), DP a L Ψ = 0 := fun a L Ψ => funext fun z => by
        simp [DP, Subsingleton.elim a 0, Subsingleton.elim (nf z) 0]
      simp only [D, z, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : κ → mixedEmbedding.mixedSpace F)
      have hv : At (evI F) ((pt ξ 0, 0) : (κ → AF F) × (κ → AF F)) := fun s hs => Prod.ext (at_pt ξ s hs) (smul_zero _)
      have h1 := h.of_ne hψ (w := w + (pt ξ 0, 0)) (fun s hs => by rw [smul_add, hw s hs, hv s hs, add_zero])
        (by rwa [Prod.fst_add, nf_add, ha, zero_add, nf_pt]) hΦ
      have h2 := h.of_ne hψ hv (by rwa [nf_pt]) hΦ
      rw [D_add_left, map_add (f := _), h.add, D_add_left, h2] at h1
      exact add_right_cancel h1
  · exact h.of_ne hψ hw ha hΦ

theorem exists_D_fin (N : Submodule ℂ ((κ → AF F) → ℂ)) [FiniteDimensional ℂ N] (hN : N ≤ schA F κ) :
    ∃ N' : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ Φ ∈ N, DP a L Φ ∈ N' := by
  let b := Module.finBasis ℝ ((κ → mixedEmbedding.mixedSpace F) × ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
  let l : _ → N →ₗ[ℂ] ((κ → AF F) → ℂ) := fun i =>
    ⟨⟨fun Φ => DP (b i).1 (b i).2 Φ.1, fun Φ Ψ => DP_add (hN Φ.2) (hN Ψ.2) _ _⟩, fun c Φ => DP_smul (hN Φ.2) c _ _⟩
  refine ⟨⨆ i, LinearMap.range (l i), inferInstance, fun a L Φ hΦ => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), DP q.1 q.2 Φ ∈ ⨆ i, LinearMap.range (l i) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨⟨Φ, hΦ⟩, rfl⟩
    | zero => convert Submodule.zero_mem _; funext z; simp [DP]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, DP_add_left]; exact add_mem hx hy
    | smul t q _ h => rw [Prod.smul_fst, Prod.smul_snd, DP_smul_left]; exact Submodule.smul_mem _ _ h
  exact this (a, L) (b.span_eq ▸ trivial)

end GlobalTheory.ThK.Dbl.Box

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

open PositivityTheory.ThKG.Tow St
open scoped Pointwise

theorem cartan_bound2 {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Aᵀ * dbl M * A.map star = dbl M →
      Commute A (Matrix.fromBlocks θ 0 0 (-θ)) → ∀ i j, ‖A i j‖ ≤ R := by
  let e := (finSumFinEquiv (m := n) (n := n)).symm
  have c : IsCartan ((dbl M).submatrix e e) ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e) := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · simp [Matrix.fromBlocks_multiply, h.1]
    · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      have : θᵀ * M * θ.map (starRingEnd ℂ) = M := h.2.1
      simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_neg, this]
    · obtain ⟨y, z, rfl⟩ : ∃ y z, x = Sum.elim y z ∘ e := ⟨x ∘ e.symm ∘ .inl, x ∘ e.symm ∘ .inr, by
        ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp⟩
      have q : ∀ v, 0 ≤ ((θ *ᵥ v) ⬝ᵥ M *ᵥ star v).re := fun v => by
        by_cases hv : v = 0
        · simp [hv]
        · exact (h.2.2 v hv).le
      have : ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e *ᵥ Sum.elim y z ∘ e) ⬝ᵥ (dbl M).submatrix e e *ᵥ star (Sum.elim y z ∘ e) =
          (θ *ᵥ y) ⬝ᵥ M *ᵥ star y + (θ *ᵥ z) ⬝ᵥ M *ᵥ star z := by
        rw [show star (Sum.elim y z ∘ e) = Sum.elim (star y) (star z) ∘ e by
          ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp]
        simp [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, comp_equiv_dotProduct_comp_equiv, dbl, Matrix.fromBlocks_mulVec,
          Matrix.neg_mulVec]
      rw [this, Complex.add_re]
      by_cases hy : y = 0
      · exact add_pos_of_nonneg_of_pos (q y) (h.2.2 z fun hz => hx (by simp [hy, hz]))
      · exact add_pos_of_pos_of_nonneg (h.2.2 y hy) (q z)
  obtain ⟨R, hR⟩ := cartan_bound c
  refine ⟨R, fun A h1 h2 i j => ?_⟩
  simpa using hR (A.submatrix e e) (by
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1])
    (by rw [Commute, SemiconjBy, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h2.eq]) (e.symm i) (e.symm j)

attribute [local instance] ae_ring ae_t2 ae_smul

theorem stab2Cpt : Stab2Cpt := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  obtain ⟨hL, c, c0, hc⟩ : Y.L.IsFullLattice E ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) :=
    hY.elim (fun h => ⟨h.lat, 1, one_ne_zero, fun w => by simpa using h.cartan w⟩) fun h => ⟨h.lat, _, Complex.I_ne_zero, h.cartan⟩
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound (F := F) Y hL
  choose R hR using fun w => cartan_bound2 (hc w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have cl := (isCompact_latHat Y hL.fg).isClosed
  have key : ∀ k ∈ K, mat2 k ∈ Set.univ.pi fun i => Set.univ.pi fun j =>
      (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C (Sum.elim id id i) (Sum.elim id id j) := fun k hk i _ j _ => by
    obtain ⟨k1, k2⟩ := (hK k).1 hk
    rw [eΦ (mat2 k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      refine hR w ((mat2 k).map (piInf (B.emb w))) ?_ (k1 w) i j
      have e := congrArg (fun X => c • Matrix.map X (piInf (B.emb w)))
        (show (mat2 k)ᵀ * dbl (incM F Y.J) * (mat2 k).map (cA σ) = dbl (incM F Y.J) from k.2)
      have d : c • (dbl (incM F Y.J)).map (piInf (B.emb w)) = dbl (c • Y.J.map (B.emb w).1) := by
        ext (a | a) (b | b) <;> simp [dbl, incM, Levi.piInf_incl]
      have d2 : ((mat2 k).map (cA σ)).map (piInf (B.emb w)) = ((mat2 k).map (piInf (B.emb w))).map star :=
        Matrix.ext fun a b => Levi.piInf_cA hB.cm _ _
      simp only [Matrix.map_mul] at e
      rwa [← Matrix.smul_mul, ← Matrix.mul_smul, d, d2] at e
    · have a := fun y hy => k2 y 0 hy (zero_mem _) k (.inl rfl)
      have b := fun y hy => k2 0 y (zero_mem _) hy k (.inl rfl)
      rw [← Matrix.fromBlocks_toBlocks (mat2 k)] at a b
      simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, zero_add] at a b
      rcases i with i | i <;> rcases j with j | j
      exacts [h i j _ fun y hy => (a y hy).1, h i j _ fun y hy => (b y hy).1, h i j _ fun y hy => (a y hy).2,
        h i j _ fun y hy => (b y hy).2]
  refine isCompact_of_units _ (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const) _ ?_ _
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC _ _)) fun k hk => ⟨key k hk, key _ (inv_mem hk)⟩
  rw [show (K : Set (G2 σ Y)) = {k | _} from Set.ext hK]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  simp only [Set.setOf_and, Set.setOf_forall]
  have v : ∀ {f : G2 σ Y → G2 σ Y}, Continuous f → ∀ z, IsClosed ({k | (mat2 (f k) *ᵥ z) ∘ Sum.inl ∈ latHat Y} ∩
      {k | (mat2 (f k) *ᵥ z) ∘ Sum.inr ∈ latHat Y}) := fun hf z =>
    have t := (hm.comp hf).matrix_mulVec (continuous_const (y := z))
    (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t)).inter
      (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t))
  exact (isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))).inter
    (isClosed_iInter fun z => isClosed_iInter fun z' => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (v continuous_id _).inter (v continuous_inv _))

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem coefLine_of (hS : SWFull) (hX : BoxSec) (hW : DblW) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hR : PairsStable) (hM : MatchEx) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : CoefLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t lam hl y hy Ψ hΨ
  have T := h.triple
  have l1 := T.geo.lt
  have l2 := T.geo.aBig
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ T.base (Or.inl T.geo.hV') (by omega)
  obtain ⟨q1, q2⟩ := (hM F E σ B a a' G X om om' R Rf h).2.2 _ _ hy.1 hy.2
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) _ q1
  have s2 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ q2.1
  have s3 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ hΨ
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega))
  have rp : ∀ s u, IsRapid (comb G om om' s u y) := fun s u =>
    cW.rapid (((c1 _ s1).const_smul s).add ((c2 _ s2).const_smul u)) fun γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_inv G.M (b1 _ s1).2.1 γ hγ, I_inv G.M' (b2 _ s2).2.1 γ hγ]
  have tr : ∀ s u g, (fun h => comb G om om' s u y (h * g)) = comb G om om' s u (om (1, g) y.1, om' (1, g) y.2) := fun s u g =>
    funext fun h => by simp only [comb, Pi.add_apply, Pi.smul_apply, I_right]
  obtain ⟨dd, om₂, S, l, d1, d2, d3, -⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)
  obtain ⟨⟨K, ht, k1, k2, k3, k4⟩, e, ce, he⟩ := hH F E σ B _ G.W _ _ T.base (.inr T.geo.hW)
  obtain ⟨t₀, hi⟩ := hT F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K ht e k1 k2 he μ hμ
  have sec := hX F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inr T.geo.hW) (by omega) cW T.chars.heckeα he ce
    (hK F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K k1) k2 k3 k4 sec.cont sec.law hE hμ hD hi
  have key := An.ident hE.isOpen hE.conn (hol _ (rp s t)) ((hol _ (rp 0 1)).const_mul lam) (fun z hz => ⟨(far z hz).1, by
    simp only [(far z hz).2.2 _ (rp s t), (far z hz).2.2 _ (rp 0 1), tr, ← integral_const_mul,
      fun g => hl _ ((hR F E σ B a a' G X om om' R Rf h hp hq).2 y hy g) y hy]
    exact integral_congr_ae (.of_forall fun g => mul_left_comm _ _ _)⟩) u
  haveI := cW.sc; haveI := cV.sc; haveI := cW.lc; haveI := cV.lc
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cV.fin _ _ T.geo.hM'.haar T.geo.hM'.dom⟩
  have val : ∀ φ, IsRapid φ → kpair X.α e μ D (Ê (((a' : ℂ) - (a + a' : ℕ)) / 2)) φ =
      2 * ((G.M'.μ.real G.M'.dom)⁻¹ : ℝ) * pet G.M'.μ G.M'.dom (th om' μ D φ Ψ) (th om' μ D φ Ψ) := fun φ hφ => by
    have := An.at_value (μ.restrict D) (G.M'.μ.restrict G.M'.dom) ⟨(b2 _ s3).1, cV.bdd₂ cW (b2 _ s3).1 (b2 _ s3).2.1⟩
      ⟨hφ.1, cW.bdd hφ.1 hφ.2.1⟩
    refine Eq.trans ?_ (congrArg _ this)
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, if_neg (show ¬ a + a' < a' by omega), setAverage_eq, Complex.real_smul,
      ← fun g => (((d2 Ψ s3 Ψ s3).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  rw [val _ (rp s t), val _ (rp 0 1), mul_left_comm lam] at key
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (cV.vol_ne T.geo.hM'.haar T.geo.hM'.dom)))) key

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem one_le_height_GL2 (x : G2 σ Y) : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1

theorem modFun_spec {f : G2 σ Y → ℂ} (hf : f ∈ modFun σ Y) :
    Continuous f ∧ ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  induction hf using Submodule.span_induction with
  | mem f h => exact ⟨h.1, 1, h.2.imp fun N h x => by simpa using h x⟩
  | zero => exact ⟨continuous_zero, 0, 0, by simp⟩
  | add f g _ _ a b =>
    obtain ⟨a, C, N, hC⟩ := a
    obtain ⟨b, C', N', hC'⟩ := b
    refine ⟨a.add b, max C 0 + max C' 0, max N N', fun x => (norm_add_le _ _).trans ?_⟩
    have := one_le_height_GL2 x
    rw [add_mul]
    refine add_le_add ((hC x).trans ?_) ((hC' x).trans ?_) <;> gcongr <;> simp
  | smul c f _ a =>
    obtain ⟨a, C, N, hC⟩ := a
    exact ⟨a.const_smul c, ‖c‖ * C, N, fun x => by
      rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

theorem reg_of_weak {s₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 s₀) {H : ℂ → modFun σ Y}
    (h : ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U) :
    An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) (fun s => (H s).1) s₀ := by
  obtain ⟨D, hD, hU', cD⟩ := local_compact_nhds hU
  refine An.reg_of_bound (NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)) hD
    (fun x => (h ((LinearMap.proj x).comp (modFun σ Y).subtype) fun N => ⟨_, fun f hf => hf x⟩).mono hU')
    (fun s _ => (modFun_spec (H s).2).1) (An.unif_bound one_le_height_GL2 (fun f hf => (modFun_spec hf).2) fun μ hμ => ?_)
  exact cD.exists_bound_of_continuousOn ((h μ hμ).mono hU').continuousOn

theorem eisCont_of_reg {f Ê : ℂ → G2 σ Y → ℂ} {t : ℝ} (h1 : ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (f s) x) (Ê s x))
    (h2 : ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re})
    (h3 : ∀ s₀, ∃ (k : ℕ) (H : ℂ → G2 σ Y → ℂ), An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x) :
    ∃ U, IsEisCont f U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k := by
  have disc : ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, z ∈ {s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s} := fun s =>
    let ⟨_, _, a, e⟩ := h3 s
    a.punct one_le_height_GL2 e
  refine ⟨{s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s}, ⟨isOpen_iff_mem_nhds.2 fun s hs => hs.eventually, An.preconn disc, disc, ⟨t, fun s hs => ⟨?_, h1 s hs⟩⟩,
    fun x s hs => ?_, fun y hy => (An.Reg.contAt hy.1 y.2).continuousWithinAt, fun s hs => ?_⟩, fun s => ?_⟩
  · obtain ⟨_, _, a, e⟩ := h3 s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) h2
  · obtain ⟨S, hS, a⟩ := hs
    exact ((a.hol x).differentiableAt hS).differentiableWithinAt
  · obtain ⟨S, hS, -, -, C, N, hC⟩ := hs
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 hS
    exact ⟨r, C, N, r0, fun z hz => hC z (hr hz)⟩
  · obtain ⟨k, H, ⟨S, hS, a⟩, e⟩ := h3 s
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (inter_mem hS (eventually_nhdsWithin_iff.1 e))
    have b := a.mono fun z hz => (hr hz).1
    exact ⟨k, r, H, r0, fun z hz => (hr hz).2, b.hol, b.cont, b.grow⟩

theorem eisContinues_of (h1 : EisBL) (h2 : FrameConj) : EisContinues := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    haveI := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]

end GlobalTheory.ThK.Dbl

end
end

