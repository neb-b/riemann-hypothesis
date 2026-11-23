module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

section General

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Hm : Mt n} {σ : Mt n → (H →L[ℂ] H)} {v : H}

theorem smFn_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) :
    SmFn (fun _ : Unit => Hm) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : Unit → Mt n)).prod ∈ UG (fun _ : Unit => Hm) := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG (fun _ : Unit => Hm) _ (hX i) _
  simp only [Pi.mul_apply, hσ.2 _ (hu ()) _ (hmem _ ()), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply, if_true]
  have h1 := hv k Xs hX
  exact (((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).contDiff.comp h1

theorem der_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) {X : Mt n}
    (hX : X ∈ lieH Hm) {u : Unit → Mt n} (hu : u ∈ UG (fun _ : Unit => Hm)) :
    der () X (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRep σ X v)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ⟪l, σ ((u * (Pi.mulSingle () (NormedSpace.exp (t • X)) : Unit → Mt n)) ()) v⟫_ℂ) =
      fun t : ℝ => ⟪l, σ (u ()) (σ (NormedSpace.exp (t • X)) v)⟫_ℂ := by
    funext t
    rw [Pi.mul_apply, hσ.2 _ (hu ()) _ (single_mem_UG (fun _ : Unit => Hm) () hX t ()), Pi.mulSingle_eq_same]
    rfl
  rw [e]
  exact ((((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth hv hX)).deriv

theorem derC_coef {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀)
    (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) (Z : Mt n) {u : Unit → Mt n}
    (hu : u ∈ UG (fun _ : Unit => Hm)) :
    derC (fun _ : Unit => Hm) () Z (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRepC Hm σ Z v)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth h) (dets_ne h).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv l hA hu, der_coef hσ hv l hB hu, map_add (f := _), map_smul, inner_add_right, inner_smul_right]

theorem inner_iso (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem eq_zero_of_orth [CompleteSpace H] {q : ℕ} {x₀ : Mt n} {w : Fin n → ℤ} (h : OrthFr Hm q x₀)
    (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hirr : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (hv0 : v ≠ 0)
    (hk : ∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v = if a = c then (w a : ℂ) • v else 0)
    (l : H) (hmem : ∀ s, torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm)
    (hl : ∀ s, σ (torEl (fun _ : Unit => x₀) s ()) l = torCh (fun _ : Unit => w) s • l) (h0 : ⟪l, v⟫_ℂ = 0) : l = 0 := by
  have hf : HolFn (fun _ : Unit => Hm) (fun _ => q) (fun _ => x₀) (fun _ => w) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
    refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun _ => h) _ (smFn_coef hσ.1 hv l) ?_
    rintro ⟨⟩ a c hac u hu
    rw [derC_coef h hσ.1 hv l _ hu, hk a c hac]
    split_ifs
    · rw [map_smul, inner_smul_right]
    · simp
  have hz := GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law _ _ _ _ _ _ (fun _ => h) _ hf (fun u hu s => by
    have hn : (starRingEnd ℂ) (torCh (fun _ : Unit => w) s) * torCh (fun _ : Unit => w) s = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [torCh, norm_prod, norm_zpow, Complex.norm_exp_ofReal_mul_I]
    have e := inner_iso _ (hσ.2.1 _ (hmem s)) l (σ (u ()) v)
    rw [hl, inner_smul_left] at e
    simp only [Pi.mul_apply]
    rw [hσ.1.2 _ (hmem s) _ (hu ()), ← e, ← mul_assoc, mul_comm (torCh _ s), hn, one_mul]
    rfl) (by
      simp only [Pi.one_apply]
      rw [hσ.1.1]
      exact h0)
  let P : Submodule ℂ H := ⨅ g ∈ Formalism.QuantumDeterminants.UH Hm, LinearMap.ker ((innerSL ℂ l).comp (σ g)).toLinearMap
  have hP : ∀ y, y ∈ P ↔ ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ⟪l, σ g y⟫_ℂ = 0 := fun y => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hcl : IsClosed (P : Set H) := by
    have : (P : Set H) = ⋂ g ∈ Formalism.QuantumDeterminants.UH Hm, {y | ⟪l, σ g y⟫_ℂ = 0} := by
      ext y
      simp only [SetLike.mem_coe, hP, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (by fun_prop) continuous_const
  have hone : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
    show _ = _
    simp
  rcases hirr P hcl (fun g hg y hy => (hP _).2 fun g' hg' => by
    have hgg : g' * g ∈ Formalism.QuantumDeterminants.UH Hm := by
      have e1 : gᴴ * Hm * g = Hm := hg
      have e2 : g'ᴴ * Hm * g' = Hm := hg'
      show _ = _
      rw [conjTranspose_mul]
      calc gᴴ * g'ᴴ * Hm * (g' * g) = gᴴ * (g'ᴴ * Hm * g') * g := by simp only [Matrix.mul_assoc]
        _ = Hm := by rw [e2, e1]
    have := (hP y).1 hy _ hgg
    rwa [hσ.1.2 _ hg' _ hg] at this) with hb | ht
  · have : v ∈ P := (hP v).2 fun g hg => hz (fun _ => g) fun _ => hg
    rw [hb] at this
    exact absurd this hv0
  · have := (hP l).1 (ht ▸ Submodule.mem_top) 1 hone
    rw [hσ.1.1] at this
    exact inner_self_eq_zero.1 this

theorem torEl_mem {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀) (s : Unit → Fin n → ℝ) :
    torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hx : IsUnit x₀.det := (dets_ne h).2.isUnit
  have hx' : IsUnit x₀ᴴ.det := by rw [det_conjTranspose]; exact hx.star
  set d : Mt n := diagonal fun a => Complex.exp ((s () a : ℂ) * Complex.I) with hd
  have e : dᴴ * (x₀ᴴ * Hm * x₀) * d = x₀ᴴ * Hm * x₀ := by
    rw [h.2, hd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    change (starRingEnd ℂ) (Complex.exp ((s () i : ℂ) * Complex.I)) * _ * _ = _
    rw [mul_right_comm, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  show (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = Hm
  calc (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = (x₀ᴴ)⁻¹ * (dᴴ * (x₀ᴴ * Hm * x₀) * d) * x₀⁻¹ := by
        simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
    _ = Hm := by
      rw [e, Matrix.mul_assoc x₀ᴴ, Matrix.nonsing_inv_mul_cancel_left _ _ hx', Matrix.mul_nonsing_inv_cancel_right _ _ hx]

theorem wt_int {ε : Fin n → Bool} {μ : Fin n → ℝ} (h1 : σ 1 = 1) (hv0 : v ≠ 0) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v)
    (a : Fin n) : ∃ m : ℤ, (m : ℝ) = μ a := by
  have h := hv (Pi.single a (2 * Real.pi)) (diag_mem _)
  have e : (diagonal fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I)) = (1 : Mt n) := by
    rw [← diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  rw [e, h1, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same] at h
  have h2 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 :=
    (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨m, ?_⟩
  have h3 : ((μ a : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = m * (2 * Real.pi * Complex.I) := by
    rw [← hm]; push_cast; ring
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero h3).symm

theorem exists_ext_mem {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hU : IsURepOn (UJset ε) σ) {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS), ?_,
    isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

end General

theorem torus_wt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    (hw : WtIs M w) (τ : D.what₂.Tau) {l : M.H τ} (hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) l)
    (s : Unit → Fin V.rank → ℝ) (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) l = torCh (fun _ : Unit => w τ) s • l := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (fun _ : Unit => x0Mat M τ) s () * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep torCh
  rw [h3, hl (fun a => s () (e.symm a)) (diagonal_mem_Kset _ _), Fintype.prod_unique]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

theorem lowSm_and_lowIrr : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), HolShape M →
    LowSm M ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M := by
  intro D V S M hM
  choose S₀ hS₀ hsm using GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M
  have hU := fun τ => (M.ds τ).2.2.1
  choose v hvS hv1 hvw using fun τ => exists_ext_mem (hU τ) (hS₀ τ)
  have hv0 : ∀ τ, v τ ≠ 0 := fun τ h => by simpa [h] using hv1 τ
  choose w hw using fun τ c => wt_int (hU τ).1.1 (hv0 τ) (hvw τ) (arr (nNeg (M.ε τ)) c)
  have hW : WtIs M w := hw
  have hle : ∀ τ, S₀ τ ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := fun τ =>
    le_sSup (s := {S | IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S}) (hS₀ τ)
  have hE : IsExtVec M fun τ => ⟨v τ, hsm τ (hvS τ)⟩ := fun τ => ⟨hv1 τ, hle τ (hvS τ), hvw τ⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have key : ∀ τ, lowKSub (M.ε τ) (M.lam τ) (M.σ τ) = S₀ τ := fun τ => by
    refine le_antisymm (sSup_le fun T hT => ?_) (hle τ)
    have hT : IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T := hT
    obtain ⟨v', hv'T, hv'1, hv'w⟩ := exists_ext_mem (hU τ) hT
    obtain ⟨hc, hR, hI, hx⟩ := GlobalTheory.HolDict.ModelRep.model_rep D V S M τ
    obtain ⟨ho, -⟩ := hx hM
    obtain ⟨hs, hk⟩ := GlobalTheory.HolDict.VKill.borel_extVec D θ V S M w _ hθ hM hW hE τ
    have hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (v' - ⟪v τ, v'⟫_ℂ • v τ) := fun t ht => by
      rw [map_sub, map_smul, hv'w t ht, hvw τ t ht, smul_sub, smul_comm]
      rfl
    have hz : v' - ⟪v τ, v'⟫_ℂ • v τ = 0 :=
      eq_zero_of_orth ho hR hI hs (hv0 τ) hk _ (torEl_mem ho) (fun s => torus_wt M hW τ hl s (dets_ne ho).2) (by
        rw [← inner_conj_symm, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv1]
        simp)
    have hv'S : v' ∈ S₀ τ := by
      rw [sub_eq_zero.1 hz]
      exact Submodule.smul_mem _ _ (hvS τ)
    rcases hT.2.2.1 (T ⊓ S₀ τ) inf_le_left (fun g hg y hy => ⟨hT.2.1 g hg y hy.1, (hS₀ τ).2.1 g hg y hy.2⟩) with h | h
    · have : v' ∈ T ⊓ S₀ τ := ⟨hv'T, hv'S⟩
      rw [h, Submodule.mem_bot] at this
      simp [this] at hv'1
    · exact h ▸ inf_le_right
  exact ⟨fun τ => key τ ▸ hsm τ, fun τ => key τ ▸ hS₀ τ⟩

end GlobalTheory.HolLowOnce
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringK
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.KMapHol

theorem exp_mem_kset {n : ℕ} (ε : Fin n → Bool) {X : Mt n} (hX : X ∈ lieH (Formalism.REAL.Jm ε))
    (hc : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have h1 : X ∈ lieH (1 : Mt n) := by
    show Xᴴ * 1 + 1 * X = 0
    rw [← hc.eq, ← Matrix.add_mul] at h0
    have := congrArg (· * (Formalism.REAL.Jm ε)⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.zero_mul] at this
    simpa using this
  have h2 : (NormedSpace.exp (t • X))ᴴ * 1 * NormedSpace.exp (t • X) = 1 := GlobalTheory.SmVec.exp_mem_UH isUnit_one h1 t
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by simpa [star_eq_conjTranspose] using h2), ?_⟩
  exact ((hc.smul_left t).exp_left).eq

theorem commute_conjH {n : ℕ} (ε : Fin n → Bool) {E : Mt n} (hc : Commute E (Formalism.REAL.Jm ε)) :
    Commute (conjH (Formalism.REAL.Jm ε) E) (Formalism.REAL.Jm ε) := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h1 : Formalism.REAL.Jm ε * Eᴴ = Eᴴ * Formalism.REAL.Jm ε := by
    have := congrArg conjTranspose hc.eq
    simpa only [conjTranspose_mul, (VKill.jm_herm ε).eq] using this
  have h2 : conjH (Formalism.REAL.Jm ε) E = -Eᴴ := by
    rw [conjH, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  rw [h2]
  exact Commute.neg_left h1.symm

theorem commute_single {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a = ε c) :
    Commute (Matrix.single a c (1 : ℂ)) (Formalism.REAL.Jm ε) := by
  show _ * _ = _ * _
  unfold Formalism.REAL.Jm
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.single_apply]
  split_ifs with h1 h2 h3 <;> simp_all

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem exists_form (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) (e : ∀ τ, lowT M τ)
    (τ : D.what₂.Tau) (x : GA D V) :
    ∃ ℓ : M.H τ →L[ℂ] ℂ, ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x := by
  let P := lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
  haveI : FiniteDimensional ℂ P := (h2 τ).1
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun y => U (Function.update e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩) x
      map_add' := fun y z => congrFun (U.map_update_add e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩ ⟨⟨z, h1 τ z.2⟩, z.2⟩) x
      map_smul' := fun a y => congrFun (U.map_update_smul e τ a ⟨⟨y, h1 τ y.2⟩, y.2⟩) x }
  refine ⟨(LinearMap.toContinuousLinearMap ℓ₀).comp P.orthogonalProjection, fun u => ?_⟩
  have : P.orthogonalProjection ((u : M.sm τ) : M.H τ) = ⟨_, u.2⟩ :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (K := P) ⟨_, u.2⟩
  rw [ContinuousLinearMap.comp_apply, this]
  rfl


open Classical in
theorem rder_eq (θ : InfFam D) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M)
    (hK : KEquiv θ M U) (e : ∀ τ, lowT M τ) (τ : D.what₂.Tau) (x : GA D V) (ℓ : M.H τ →L[ℂ] ℂ)
    (hℓ : ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x)
    {X Y : Mt V.rank} (hY : Y ∈ lieH (Formalism.REAL.Jm (M.ε τ))) (hc : Commute Y (Formalism.REAL.Jm (M.ε τ)))
    (hXY : X = (M.fr τ)⁻¹ * Y * M.fr τ)
    (hd : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ))
      (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) 0) :
    Rder θ V τ X (U e) x = ℓ (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) := by
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e1 : M.fr τ * X * (M.fr τ)⁻¹ = Y := by
    rw [hXY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one]
  have key : ∀ t : ℝ, U e (x * oneP θ V τ X t) = ℓ (M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ)) := by
    intro t
    have hk : M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
      rw [VKill.conj_exp hP, e1]; exact exp_mem_kset _ hY hc t
    have hm := (h2 τ).2.1 _ hk _ (e τ).2
    have h := hK τ _ hk e ⟨⟨_, h1 τ hm⟩, hm⟩ rfl
    have e2 : (M.fr τ)⁻¹ * (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) * M.fr τ = NormedSpace.exp (t • X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hPd, Matrix.mul_one]
    rw [e2] at h
    exact ((hℓ ⟨⟨_, h1 τ hm⟩, hm⟩).trans (congrFun h x)).symm
  unfold Rder
  simp only [key]
  exact ((ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd).deriv

theorem holAd_of_kEquiv : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  classical
  intro D θ V S M w hθ hS hw h1 h2 U hsm hK hp e hv g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => U e (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun τ => ((ModelRep.model_rep D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := hsm e k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := GlobalTheory.MultHol.lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show U e (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => U e (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => U e (g * L u)) u = Rder θ V τ X (U e) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show U e (g * L (u * _)) = _
      rw [hmul u hu _ (GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨hc, hU, -, hx⟩ := ModelRep.model_rep D V S M τ
    obtain ⟨-, hx⟩ := hx hS
    obtain ⟨hs, hk⟩ := VKill.borel_extVec D θ V S M w _ hθ hS hw hv τ
    have hk := hk a c hac
    rw [hx a c] at hk ⊢
    set a' := arr (nNeg (M.ε τ)) a with ha'
    set c' := arr (nNeg (M.ε τ)) c with hc'
    obtain ⟨p1, p2⟩ := GlobalTheory.MultHol.parts_mem_lieH (hG τ).1 (hG τ).2 ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ)
    by_cases hε : M.ε τ a' = M.ε τ c'
    · obtain ⟨ℓ, hℓ⟩ := exists_form h1 h2 U e τ (g * L u)
      obtain ⟨q1, q2⟩ := GlobalTheory.MultHol.parts_mem_lieH (VKill.jm_herm (M.ε τ)) (VKill.jm_det (M.ε τ)) (Matrix.single a' c' 1)
      have c1 := commute_single (M.ε τ) hε
      have c2 := commute_conjH (M.ε τ) c1
      have hcj : conjH (gramAt D V τ) ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ) =
          (M.fr τ)⁻¹ * conjH (Formalism.REAL.Jm (M.ε τ)) (Matrix.single a' c' 1) * M.fr τ := by
        rw [← M.fr_gram τ]; exact VKill.conjH_conj (M.fr_unit τ) _ _
      have hD := ((GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ (hG τ).1 (hG τ).2 hU).2 _ hs).2.1
      have r1 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q1 ((c1.add_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]) (hD _ p1).2
      have r2 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q2 ((c1.sub_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]) (hD _ p2).2
      have hk' := congrArg ℓ hk
      unfold dRepC at hk'
      rw [map_add (f := _), map_smul, smul_eq_mul] at hk'
      unfold derC
      rw [hder _ p1, hder _ p2, r1, r2, hk']
      split_ifs
      · rw [map_smul, hℓ (e τ), Function.update_eq_self, smul_eq_mul]
      · rw [map_zero]
    · obtain ⟨-, p, hpn, hεp⟩ := hS τ
      have hq := nNeg_shape hpn hεp
      have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
        intro b
        have := b.2
        rw [hεp, hq]
        unfold arr
        split_ifs with hb
        · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
        · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
      have hac' : (a : ℕ) ≤ c := hac
      have hne : a ≠ c := fun h => hε (by rw [ha', hc', h])
      rw [ha', hc', hsg, hsg, decide_eq_decide] at hε
      have ha : M.ε τ a' = false := by rw [ha', hsg]; simp only [decide_eq_false_iff_not]; omega
      have hb : M.ε τ c' = true := by rw [hc', hsg]; simp only [decide_eq_true_eq]; omega
      have h0 := congrFun (hp τ _ (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.single_mem_pMinus M τ ha hb) e) (g * L u)
      rw [if_neg hne]
      unfold derC
      rw [hder _ p1, hder _ p2]
      exact h0

end GlobalTheory.KMapHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
end

