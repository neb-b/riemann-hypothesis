module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZe
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem mem_ratV_iff {ι : Type} (x : ι → Ad E) : x ∈ ratV E ι ↔ ∀ t, ∃ c : E, algebraMap E (Ad E) c = x t := by
  constructor
  · rintro ⟨c, rfl⟩ t
    exact ⟨c t, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext hc⟩


variable (E) in
def reix {ι κ : Type} (τ : κ ≃ ι) : (κ → Ad E) ≃ₜ+ (ι → Ad E) where
  toFun w := w ∘ τ.symm
  invFun x := x ∘ τ
  left_inv w := by funext t; simp
  right_inv x := by funext t; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem reix_mem {ι κ : Type} (τ : κ ≃ ι) (w : κ → Ad E) : reix E τ w ∈ ratV E ι ↔ w ∈ ratV E κ := by
  simp only [mem_ratV_iff]
  change (∀ t, ∃ c : E, algebraMap E (Ad E) c = w (τ.symm t)) ↔ _
  exact ⟨fun h s => by simpa using h (τ s), fun h t => h _⟩

theorem per_reix {ι κ : Type} (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    Per (ratV E κ) (fun w => Φ (w ∘ τ.symm)) := by
  refine ⟨h.1.comp (reix E τ).continuous, fun γ hγ w => ?_⟩
  have := h.2 (reix E τ γ) ((reix_mem τ γ).2 hγ) (reix E τ w)
  exact this

theorem avg_reix {ι κ : Type} [Fintype ι] [Fintype κ] (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ) (fun w => Φ (w ∘ τ.symm)) :=
  (_root_.GlobalTheory.CuspGeneric.avg_equiv _ _ _ _ (isCoLat_ratV E κ) (isCoLat_ratV E ι) (reix E τ) (reix_mem τ) Φ h).symm

theorem avg_sum_reix {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂] (τ : κ₁ ⊕ κ₂ ≃ ι)
    {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ₁) (fun z => avg (ratV E κ₂) (fun y => Φ (Sum.elim z y ∘ τ.symm))) := by
  rw [avg_reix τ h]
  exact _root_.GlobalTheory.CuspGeneric.avg_sum_index E κ₁ κ₂ _ (per_reix τ h)

end Gen

end GlobalTheory.CuspGeneric.ColSplit

namespace GlobalTheory.CuspGeneric.ColSplit

section Main

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem sumElim_add_left {κ₁ κ₂ : Type} (c : κ₁ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim ((fun t => algebraMap E (Ad E) (c t)) + n) w =
      (fun s => algebraMap E (Ad E) (Sum.elim c 0 s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem sumElim_add_right {κ₁ κ₂ : Type} (c : κ₂ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) =
      (fun s => algebraMap E (Ad E) (Sum.elim 0 c s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem blk_rat {r' m' : ℕ} {κ : Type} [Fintype κ] (σ : κ ≃ UnipotentBlockColumnIndex a r' m') {f : GA E a → ℂ}
    (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g) (c : κ → E) (v : κ → Ad E) (h : GA E a) :
    f (blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) * h) = f (blkU (v ∘ σ.symm) * h) := by
  have e : blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) =
      ratGL E a (blkU (c ∘ σ.symm)) * blkU (v ∘ σ.symm) := by
    rw [ratGL_blkU]
    exact posU_add _ _ _
  rw [e, mul_assoc, hl]

theorem continuous_sumElim_right {κ₁ κ₂ : Type} (n : κ₁ → Ad E) :
    Continuous fun w : κ₂ → Ad E => Sum.elim n w :=
  continuous_pi fun s => match s with
    | Sum.inl _ => continuous_const
    | Sum.inr l => continuous_apply l

theorem continuous_sumElim {κ₁ κ₂ : Type} : Continuous fun p : (κ₁ → Ad E) × (κ₂ → Ad E) => Sum.elim p.1 p.2 :=
  continuous_pi fun s => match s with
    | Sum.inl l => (continuous_apply l).comp continuous_fst
    | Sum.inr l => (continuous_apply l).comp continuous_snd

theorem per_position {r' m' : ℕ} {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (σ : κ₁ ⊕ κ₂ ≃ UnipotentBlockColumnIndex a r' m')
    {f : GA E a → ℂ} (hc : Continuous f) (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g)
    (n : κ₁ → Ad E) (h : GA E a) : Per (ratV E κ₂) (fun w => f (blkU (Sum.elim n w ∘ σ.symm) * h)) := by
  refine ⟨hc.comp (((continuous_posU _).comp ((reix E σ).continuous.comp (continuous_sumElim_right n))).mul
    continuous_const), ?_⟩
  rintro _ ⟨c, rfl⟩ w
  change f (blkU (Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) ∘ σ.symm) * h) = _
  rw [sumElim_add_right, blk_rat σ hl]

theorem dot_col {r m : ℕ} (hr : r ≤ m) (z : HiIx a r (m + 1) → Ad E) (y : LoIx a r (m + 1) → Ad E) :
    dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) =
      dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : r ≤ (t.1.1 : ℕ)
  · have e : (colEquiv a r (m + 1)).symm t = Sum.inl ⟨t, h⟩ := Equiv.sumCompl_symm_apply_of_pos (p := fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => r ≤ (t.1.1 : ℕ)) h
    simp only [Function.comp, e, Sum.elim_inl]
  · have : (eLast a (m + 1) t : E) = 0 := by
      simp only [eLast]
      rw [if_neg]
      omega
    simp [this]

theorem colT_avg_blk_eq_zero (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hf : Good ψ (m + 1) f)
    (r : ℕ) (h0 : 0 < r) (hr : r ≤ m) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 := by
  have hr1 : r ≤ m + 1 := by omega
  have hl : ∀ {r' : ℕ} (c : UnipotentBlockColumnIndex a r' (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g

  have hA : ∀ n : UnipotentBlockColumnIndex a r m → Ad E, colT ψ (m + 1) f (blkU n * g) =
      avg (ratV E (HiIx a r (m + 1))) (fun z => avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)))) := by
    intro n
    unfold colT coefF
    exact avg_sum_reix (colEquiv a r (m + 1)) (per_coef hψ _ hf.cont hl _)
  have hB : ∀ (n : UnipotentBlockColumnIndex a r m → Ad E) (z : HiIx a r (m + 1) → Ad E),
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g))) =
      ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
        avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
    intro n z
    have e : ∀ y : LoIx a r (m + 1) → Ad E,
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)) =
        ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim n (y + -corr n z) ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)) := by
      intro y
      rw [dot_col hr, ← mul_assoc, blkU_col_mul_blkU hr1, mul_assoc, sub_eq_add_neg]
    simp_rw [e]
    rw [avg_const_mul]
    exact congrArg _ (GlobalTheory.T.quotientAverage_translate_invariant _ _ (isCoLat_ratV _ _)
      (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)))
      (per_position (blkEquiv a r m hr1) hf.cont hl n _) (-corr n z))

  obtain ⟨Φ₂, hΦ₂⟩ : ∃ Φ₂ : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, Φ₂ p =
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm) * (blkU p.1 * g))) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, H p =
      avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim p.1 w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := ⟨_, fun _ => rfl⟩
  have hΦH : ∀ p, Φ₂ p = ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) * H p := by
    intro p
    rw [hΦ₂, hH, hB]
  have hHc : Continuous H := by
    have e : H = fun p => avg (ratV E (LoIx a r (m + 1))) (fun w =>
        (fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) (p, w)) := funext hH
    rw [e]
    refine _root_.GlobalTheory.CuspGeneric.continuous_avg_of_periodic (LoIx a r (m + 1) → Ad E) (ratV E (LoIx a r (m + 1))) (isCoLat_ratV E _)
      ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E))
      (fun q => f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) ?_ ?_
    · have c₁ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.1 q.2 := continuous_sumElim.comp (continuous_fst.fst.prodMk continuous_snd)
      have c₂ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.2 (0 : LoIx a r (m + 1) → Ad E) :=
        continuous_sumElim.comp (continuous_fst.snd.prodMk continuous_const)
      exact hf.cont.comp (((continuous_posU _).comp ((reix E (blkEquiv a r m hr1)).continuous.comp c₁)).mul
        (((continuous_posU _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp c₂)).mul continuous_const))
    · intro x γ hγ y
      exact (per_position (blkEquiv a r m hr1) hf.cont hl x.1 _).2 γ hγ y
  have hψc : Continuous fun p : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) =>
      ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) :=
    hψ.cont.comp ((continuous_dot _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp
      (continuous_sumElim.comp (continuous_snd.prodMk continuous_const)))).neg
  have hPer : Per ((ratV E (UnipotentBlockColumnIndex a r m)).prod (ratV E (HiIx a r (m + 1)))) Φ₂ := by
    refine ⟨?_, ?_⟩
    · rw [funext hΦH]
      exact hψc.mul hHc
    · intro γ hγ p
      rw [AddSubgroup.mem_prod] at hγ
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hγ
      have e₁ : γ.1 = fun t => algebraMap E (Ad E) (c₁ t) := hc₁.symm
      have e₂ : γ.2 = fun t => algebraMap E (Ad E) (c₂ t) := hc₂.symm
      have s₁ : Φ₂ (γ + p) = Φ₂ (p.1, γ.2 + p.2) := by
        rw [show γ + p = (γ.1 + p.1, γ.2 + p.2) from rfl, hΦH, hΦH]
        congr 1
        rw [hH, hH]
        congr 1
        funext w
        change f (blkU (Sum.elim (γ.1 + p.1) w ∘ _) * _) = _
        rw [e₁, sumElim_add_left, blk_rat _ hl]
      have s₂ : Φ₂ (p.1, γ.2 + p.2) = Φ₂ p := by
        rw [hΦ₂, hΦ₂]
        congr 1
        funext y
        change ψ (-dot _ (Sum.elim (γ.2 + p.2) y ∘ _)) * f (blkU (Sum.elim (γ.2 + p.2) y ∘ _) * _) = _
        have hm := hψ.map_dot (eLast a (m + 1)) (Sum.elim c₂ 0 ∘ (colEquiv a r (m + 1)).symm)
          (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)
        rw [e₂, sumElim_add_left, blk_rat _ hl, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
        congr 1
        exact congrArg _ hm
      rw [s₁, s₂]
  have hD : ∀ z : HiIx a r (m + 1) → Ad E, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => Φ₂ (n, z)) = 0 := by
    intro z
    simp_rw [hΦH]
    rw [avg_const_mul]
    have e : avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => H (n, z)) =
        avg (ratV E (UnipotentBlockColumnIndex a r (m + 1))) (fun w => f (blkU w * (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
      rw [avg_sum_reix (blkEquiv a r m hr1) (per_blk hf.cont hl _)]
      simp_rw [hH]
    rw [e, hf.van r h0 hr1, mul_zero]
  have hA' : (fun n => colT ψ (m + 1) f (blkU n * g)) = fun n => avg (ratV E (HiIx a r (m + 1))) (fun z => Φ₂ (n, z)) := by
    funext n
    rw [hA]
    simp_rw [hΦ₂]
  rw [hA', GlobalTheory.T.quotientAverage_adelicRationalPoints_comm E _ _ Φ₂ hPer]
  simp_rw [hD]
  simpa using avg_const_mul (ratV E (HiIx a r (m + 1))) 0 (fun _ => (1 : ℂ))

end Main

theorem _root_.GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ),
    StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ r, 0 < r → r ≤ m → ∀ g : GA E a,
      avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 :=
  fun _ _ _ _ _ hψ m f _ hf r h0 hr g => colT_avg_blk_eq_zero hψ m f hf r h0 hr g

end GlobalTheory.CuspGeneric.ColSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeTieProof

theorem exists_ext_semilin {L V W U ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (σ : L →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range (fun k => j (b k))) = ⊤)
    (f : V →ₛₗ[σ] U) : ∃ F : W →ₗ[ℂ] U, ∀ v, F (j v) = f v := by
  let bC : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  refine ⟨bC.constr ℂ (fun k => f (b k)), fun v => ?_⟩
  have h : (bC.constr ℂ (fun k => f (b k))).comp j = f := by
    refine b.ext fun k => ?_
    rw [LinearMap.comp_apply]
    have : j (b k) = bC k := by simp [bC]
    rw [this, Module.Basis.constr_basis]
  exact congrArg (fun g : V →ₛₗ[σ] U => g v) h

theorem mem_biSup_of_forall {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (H : ι → Submodule K V)
    (hind : iSupIndep H) (htop : ⨆ x, H x = ⊤) (Y : Set ι) (v : V)
    (h : ∀ x0, x0 ∉ Y → v ∈ ⨆ (x) (_ : x ≠ x0), H x) : v ∈ ⨆ x ∈ Y, H x := by
  classical
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp H v).1 (by rw [htop]; exact Submodule.mem_top)
  have h0 : ∀ x0, x0 ∉ Y → f x0 = 0 := by
    intro x0 hx0
    by_cases hs : x0 ∈ f.support
    · have e : f x0 = v - ∑ x ∈ f.support.erase x0, f x := by
        rw [← hsum, Finsupp.sum, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : f x0 ∈ ⨆ (x) (_ : x ≠ x0), H x := by
        rw [e]
        refine Submodule.sub_mem _ (h x0 hx0) (Submodule.sum_mem _ fun x hx => ?_)
        exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hx) (hf x))
      exact (Submodule.disjoint_def.1 (hind x0)) _ (hf x0) m2
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ Y
  · exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx (hf x))
  · rw [h0 x hx]; exact Submodule.zero_mem _

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_symm {D : D7} {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hxy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hxy, host_conj_eq, host_conj_eq, IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

theorem not_bad_of_splitOut {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w) : s.v ∉ badPl D i := by
  rintro ⟨w', hover, hw'⟩
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq]; simp)).2 h3
  obtain ⟨hsp, hl, hS, hQ⟩ := hw
  rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
  · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e
    · subst e
      exact hQ (HT.Q_conj i s.w w (isConjPl_symm hc) hQ')
    · have ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w := by
        ext1; ext x
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        refine (hc x _ ?_).symm
        rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]
      rw [e, ew] at hQ'
      exact hQ hQ'
  · apply hS
    refine (D.nd.S_def i w).2 ⟨?_, hl⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · exact hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)

theorem tN_lin {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hu : IsUnif D.host.E s.v ϖ) (k : ℕ) (c : ℂ)
    (f f' : GAf D.host.E D.R.nV → (M.loc i).wt.W) :
    tN (M.loc i).J s ϖ k (c • f + f') = c • tN (M.loc i).J s ϖ k f + tN (M.loc i).J s ϖ k f' := by
  have hfin := _root_.GlobalTheory.TSetFin.finite_image_tSet D.host.E D.R.nV (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s ϖ k
    (not_bad_of_splitOut HT i hw s hc) hu
  simp only [tN]
  rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

section Hecke

variable {O X Mo : Type} [CommRing O] [IsDomain O] [AddCommGroup Mo] [Module O Mo]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O Mo)

theorem heckeEig_iSupIndep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) Mo) :=
    fun f => (act f).baseChange (FractionRing O)
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show (act f).baseChange _ * (act g).baseChange _ = (act g).baseChange _ * (act f).baseChange _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).eigenspace_le_genEigenspace (k := 1) (by norm_num)).trans
    (((F f).genEigenspace _).monotone le_top)

theorem dual_eig (htop : ⨆ x, heckeEig T act x = ⊤) (x0 : X)
    (φ : Module.Dual (FractionRing O) (TensorProduct O (FractionRing O) Mo))
    (hφ : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig T act x, φ u = 0) (f : T) (u : TensorProduct O (FractionRing O) Mo) :
    φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u := by
  have hu : u ∈ ⨆ x, heckeEig T act x := by rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction (heckeEig T act)
    (motive := fun u => φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u)
    hu ?_ ?_ ?_
  · intro x u hux
    have he : (act f).baseChange (FractionRing O) u = algebraMap O (FractionRing O) ((f : X → O) x) • u :=
      Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hux f)
    rw [he, map_smul, smul_eq_mul]
    by_cases hx : x = x0
    · rw [hx]
    · rw [hφ x hx u hux, mul_zero, mul_zero]
  · simp
  · intro a b ha hb; rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, mul_add]

end Hecke

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

theorem typeTie_holds : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M →
    SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  intro D M i HT HR AV _ HS HE S y hy
  classical
  let ι : FractionRing (D.nd.O i) →+* ℂ := (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)
  have hι : ∀ a, ι (D.nd.embK i a) = D.what₂.embLL a := D.naut.iota_LL i
  refine mem_biSup_of_forall (heckeEig (D.nd.T i) (D.nd.act i))
    (heckeEig_iSupIndep _ _ (D.nd.T_sep i)) (HE i) {x | ∃ P ∈ S, D.naut.ptV i P = some x} _ ?_
  intro x0 hx0
  by_contra hv
  obtain ⟨φ, hφv, hφB⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ0 : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, φ u = 0 := by
    intro x hx u hu
    have hm : φ u ∈ Submodule.map φ (⨆ (x) (_ : x ≠ x0), heckeEig (D.nd.T i) (D.nd.act i) x) :=
      Submodule.mem_map_of_mem (Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx hu))
    rw [hφB] at hm
    exact (Submodule.mem_bot _).1 hm
  have hφe := dual_eig (D.nd.T i) (D.nd.act i) (HE i) x0 φ hφ0
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  have hb := D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b
  let f0 : D.what₂.MtL (D.nd.mu i) (D.nd.j i) →ₛₗ[D.what₂.embLL] ℂ :=
    { toFun := fun z => ι (φ (D.nd.prMt i z))
      map_add' := fun a c => by simp only [map_add (f := _)]
      map_smul' := fun a z => by
        show ι (φ (D.nd.prMt i (a • z))) = D.what₂.embLL a • ι (φ (D.nd.prMt i z))
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hι, smul_eq_mul] }
  obtain ⟨Ψ, hΨ⟩ := exists_ext_semilin D.what₂.embLL (D.what₂.jMt _ _) b hb.1 hb.2 f0
  let bC : Module.Basis _ ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ q, bC q = D.what₂.jMt _ _ (b q) := fun q => by simp [bC]
  have hker : ∀ P ∈ S, D.naut.typeV i P ≤ LinearMap.ker Ψ := by
    intro P hP z hz
    by_contra hz0
    rw [LinearMap.mem_ker] at hz0
    apply hx0
    refine ⟨P, hP, (AV.ptV i P x0).2 ?_⟩
    intro w k s ϖ hw hc hu hk1 hk2 y' hy'
    obtain ⟨c, hcP⟩ := HS P w k s ϖ hw hc hu hk1 hk2
    choose x' hx' using HR i w k s ϖ hw hc hu hk1 hk2
    let Tt : Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
      bC.constr ℂ (fun q => D.what₂.jMt _ _ (x' (b q)))
    have hTb : ∀ q, Tt (bC q) = D.what₂.jMt _ _ (x' (b q)) := fun q => by
      simp only [Tt, Module.Basis.constr_basis]
    have t0 : tN (M.loc i).J s ϖ k (0 : GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
      have e := tN_lin HT i hw s hc ϖ hu k 1 0 0
      simp only [smul_zero, add_zero, one_smul] at e
      simpa using e
    let tl : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) :=
      { toFun := tN (M.loc i).J s ϖ k
        map_add' := fun f f' => by simpa using tN_lin HT i hw s hc ϖ hu k 1 f f'
        map_smul' := fun a f => by simpa [t0] using tN_lin HT i hw s hc ϖ hu k a f 0 }
    have hreal : (M.loc i).real ∘ₗ Tt = tl ∘ₗ (M.loc i).real := bC.ext fun q => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hTb, hbC]
      exact hx' (b q)
    have hΨT : Ψ ∘ₗ Tt = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) • Ψ :=
      bC.ext fun q => by
        rw [LinearMap.comp_apply, hTb, LinearMap.smul_apply, hbC, hΨ, hΨ]
        show ι (φ (D.nd.prMt i (x' (b q)))) = _ • ι (φ (D.nd.prMt i (b q)))
        rw [HT.hT i w k s ϖ hw hc hu hk1 hk2 (b q) (x' (b q)) (hx' (b q)), hφe, map_mul, smul_eq_mul]
    have hTz : Tt z = c • z := (M.loc i).real_inj (by
      have e := LinearMap.congr_fun hreal z
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
      rw [e, map_smul]
      exact hcP z hz)
    have hcz : c = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) := by
      have e := LinearMap.congr_fun hΨT z
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hTz, map_smul, smul_eq_mul, smul_eq_mul] at e
      exact mul_right_cancel₀ hz0 e
    rw [hcP y' hy', hcz]
    rfl
  have hyk := (iSup₂_le hker) hy
  rw [LinearMap.mem_ker, hΨ] at hyk
  exact hφv ((map_eq_zero_iff ι ι.injective).1 hyk)

end GlobalTheory.EtaJoin.TypeTieProof
end
end

