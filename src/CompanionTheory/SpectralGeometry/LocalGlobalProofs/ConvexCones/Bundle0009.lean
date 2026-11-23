module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm

variable {O : Type} [CommRing O]

def twPi (σ : O ≃+* O) (n : ℕ) : (Fin n → O) ≃+ (Fin n → O) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : O ≃+* O) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → O) ≃+ LinearMap.BilinForm ℤ (Fin n → O) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : O ≃+* O) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) (a b : Fin n → O) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

theorem twForm_mem_balForms {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    {β : LinearMap.BilinForm ℤ (Fin n → O)}
    (h : β ∈ balForms bar (Fin n → O)) : twForm σ n β ∈ balForms bar (Fin n → O) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((bar a • z) j)) = bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [hb.comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : O ≃+* O) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ n β ∈ balForms bar (Fin n → O) ↔ β ∈ balForms bar (Fin n → O) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms hb σ.symm h, twForm_mem_balForms hb σ⟩

theorem evalZ_twForm {w0 : O} {φ : InvFun O} (hφ : IsTwG w0 φ) {σ : O ≃+* O} (hσ : σ w0 = w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab →
    ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  intro O _ _ _ _ bar w0 hb ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff hb σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
open GlobalTheory.PolFan.Mark.FaceIn

namespace GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum

theorem inRCone_of_add : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone (bar := bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β + x] ![1] (by simp [hs])
        (by simpa using hsp) (by simp)
    obtain ⟨S, -, hcov⟩ := (hψ X hX).finite
    obtain ⟨e, mm, γ, c, hγ, -, hc, hsum⟩ := hcov _ hR
    refine ⟨_, mm, fun i => pull e.symm.toLinearMap (γ i), CarDim.isCell_pull_equiv hγ e.symm, ⟨c, hc, ?_⟩, rfl⟩
    exact LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply] using this
  obtain ⟨n, γ, hγ, hγs, hrk⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨N', ℓ', hN', h1', h2', h3'⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have e0 := apply_eq_of_inRCone hγ.linear h1 hγs
  rw [map_add (f := _), Int.cast_add, hadd, mul_add] at e0
  have eβ : (N : ℝ) * ψ.evalZ β = ℓ β := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have ex : (N : ℝ) * ψ.evalZ x = ℓ x := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have hγβ : InRCone γ β := by
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hβp eβ
    exact inRCone_of_nsmul_eq hk hc
  obtain ⟨cx, -, hcx⟩ : InRCone γ x := by
    obtain ⟨k, c, hk, hc⟩ := h3 x hx hxp ex
    exact inRCone_of_nsmul_eq hk hc
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (N : ℤ) • ℓ' - (N' : ℤ) • ℓ with hh
  have happ : ∀ u, (h u : ℝ) = N * ℓ' u - N' * ℓ u := fun u => by simp [hh]
  let Z : Finset (Fin n) := Finset.univ.filter fun j => h (γ j) = 0
  let s : Fin Z.card ↪ Fin n := (Z.orderEmbOfFin rfl).toEmbedding
  have hcut : IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have : (0 : ℝ) ≤ h (γ j) := by
        rw [happ, h1]
        have := mul_le_mul_of_nonneg_left (h2' _ (hγ.mem j) (hγ.nonneg j)) hNr.le
        linarith
      exact_mod_cast this
    · have : Set.range s = Z := Z.range_orderEmbOfFin rfl
      rw [this]
      simp [Z]
  have hface := GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q ψ hψ X hX hD n γ hγ _ s h hcut
  have hβ0 : h β = 0 := by
    have : (h β : ℝ) = 0 := by
      rw [happ, apply_eq_of_inRCone hv.linear h1' hvβ, ← eβ]; ring
    exact_mod_cast this
  have hle : genRank γ ≤ genRank fun j => γ (s j) := by
    rw [hlab X hX _ hs hsp, hlab X hX _ hβ hβp, Nat.cast_inj] at hl
    rw [hrk, hl]
    exact Nat.sInf_le ⟨_, _, hface, inRCone_face hcut hγβ hβ0, rfl⟩
  have hall := apply_eq_zero_of_genRank_le (h := h) (fun j => (hcut.2 _).2 ⟨j, rfl⟩) hle
  have hx0 : (h x : ℝ) = 0 := by
    rw [apply_eq_of_toReal_eq hcx h]
    simp [hall]
  rw [happ, ← ex] at hx0
  have ex' : (N' : ℝ) * ψ.evalZ x = ℓ' x := by
    have : (N : ℝ) * (N' * ψ.evalZ x - ℓ' x) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_left hNr.ne']
  obtain ⟨k, c, hk, hc⟩ := h3' x hx hxp ex'
  exact inRCone_of_nsmul_eq hk hc

end GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRank
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone

theorem vanish_of_inRCone_of_genRank_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ τ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell bar ψ (fun k => τ (s k)) :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthGapOnCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
open GlobalTheory.PolFan.StarGap

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap

theorem starDepth_le_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith bar ψ N ℓ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (starDepth bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro O _ _ _ _ bar _ q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.UniformCellBoundPolyhedralFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound

open GlobalTheory.PolFan.StrictData

theorem uniform_bound (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (hb : CMOrd O bar) (q : ℕ) (ψ : InvFun O) (hψ : IsPolyFan bar q ψ) :
    ∃ N₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ := by
  classical
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  have hfin : ∀ k, Module.Finite O (R k) := fun k => (hR k).1
  have key : ∀ k, ∃ N₀ : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)),
      IsCell bar ψ δ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ (R k) →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧
        StrictWith bar ψ N ℓ δ := fun k => by
    have := (hR k).2.1
    exact perModule_bound (hψ (R k) (hR k).2.2)
  choose N₀ hN₀ using key
  refine ⟨Finset.univ.sup N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ :=
    hN₀ k m (fun i => pull f.symm.toLinearMap (γ i)) (CellClass.isCell_pull_equiv hγ f.symm)
  exact ⟨N, _, hN, hNle.trans (Finset.le_sup (Finset.mem_univ k)), StrictWith.of_pull f.symm.surjective hℓ⟩

theorem exists_strict_data : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  intro O _ _ _ _ bar hb q ψ hDom hψ
  obtain ⟨N₀, hN₀⟩ := uniform_bound O bar hb q ψ hψ
  refine ⟨N₀, N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ := hN₀ X hX m γ hγ
  refine ⟨N, ℓ, hN, hNle, hℓ, fun m' s h hh => ?_⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  have hF := GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q ψ hψ X hX (hDom X) m γ hγ m' s h hh
  obtain ⟨NF, ℓF, -, hNFle, hℓF⟩ := hN₀ X hX m' _ hF
  obtain ⟨h1, h2, h3⟩ := faceCut_data (hψ X hX) hγ hN hℓ hh hℓF
  refine ⟨_, h1, h2, fun β hβ hp => (h3 β hβ hp).trans ?_⟩
  have hℓβ : (0 : ℤ) ≤ ℓ β := by
    have := le_trans (mul_nonneg (Nat.cast_nonneg _) (evalZ_nonneg (hψ X hX) hβ hp)) (hℓ.2.1 β hβ hp)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNFle) hℓβ

end GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound
end
end

