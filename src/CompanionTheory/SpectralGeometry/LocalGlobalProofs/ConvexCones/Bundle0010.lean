module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CentreFunctionOneOnCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell


open GlobalTheory.PolFan.StarOnCell in
theorem starDepth_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β) ∧ (starDepth bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro O _ _ _ _ bar _hb q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := _root_.GlobalTheory.PolFan.depth_le_starDepth O bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
    nlinarith
  ·
    intro β _ _ hβ heq
    have hβr : toReal β ∈ rcone γ := by obtain ⟨c, hc0, e⟩ := hβ; exact ⟨c, hc0, e⟩
    obtain ⟨m'', s'', h'', hf'', hpos'', t, ht, e⟩ :=
      GlobalTheory.StarCover.star_cover X m γ β₀ (toReal β) (fun i => (hγ.mem i).1) hγ.nonneg hne hin hβr
    have hpos''' : (0 : ℝ) < h'' β₀ := by exact_mod_cast hpos''

    have r2 := ell_of_eq h'' e
    rw [Fin.sum_univ_succ] at r2
    simp only [Fin.cons_zero, Fin.cons_succ] at r2
    have z2 : ∀ j, (h'' (γ (s'' j)) : ℝ) = 0 := fun j => by
      rw [(hf''.2 (s'' j)).2 ⟨j, rfl⟩, Int.cast_zero]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero] at r2
    have hle : (starDepth bar ψ w).evalZ β ≤ t 0 := by
      have := mul_starDepth_le hγ huniq h'' hf''.1 hpos'' hβ
      rw [r2] at this
      nlinarith

    have r1 := ell_of_eq h e
    rw [Fin.sum_univ_succ] at r1
    simp only [Fin.cons_zero, Fin.cons_succ] at r1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ t j.succ * (h (γ (s'' j)) : ℝ) := fun j _ =>
      mul_nonneg (ht _) (by exact_mod_cast hf.1 _)
    have hsum : ∑ j, t j.succ * (h (γ (s'' j)) : ℝ) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have hcone : InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) β := by
      refine inRCone_of_sum t ht e fun i hi => ?_
      refine Fin.cases (fun _ => ?_) (fun j hj => ?_) i hi
      · simpa using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) 0
      · have h0 : (h (γ (s'' j)) : ℝ) = 0 := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_left hj
        have h0' : h (γ (s'' j)) = 0 := by exact_mod_cast h0
        obtain ⟨k, hk⟩ := (hf.2 (s'' j)).1 h0'
        simpa [hk] using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k.succ
    exact exists_nat_of_inRCone _ β hcone

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsIsPosDefOfBasis
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_isPosDef_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    ∃ B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y z, B₀ y z = B₀ z y) ∧ IsPosDef B₀ := by
  classical
  let B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ k, toReal (GlobalTheory.RedTh.sqForm b (Pi.single k 1))
  have hv : ∀ i j, B₀ (b i) (b j) = if i = j then 1 else 0 := fun i j => by
    simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_basis]
    by_cases h : i = j
    · subst h
      simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
  refine ⟨B₀, fun y z => ?_, (isPosDef_iff_basis b B₀).2 fun c hc => ?_⟩
  · simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_apply, mul_comm]
  · simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

theorem hasRedCover_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], HasRedCover (id : ℤ → ℤ) X := by
  intro X _ _ _
  classical
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  let b₀ : Module.Basis (Fin n) ℤ X := Module.finBasisOfFinrankEq ℤ X hn
  obtain ⟨B₀, hs₀, hp₀⟩ := exists_isPosDef_of_basis b₀
  obtain ⟨S, hS⟩ := GlobalTheory.SiegelCone.gram_mem_cone n
  refine GlobalTheory.RedTh.hasRedCover_of_fintype (ι := ↥S) _ (fun l => GlobalTheory.RedTh.sqForm b₀ l.1)
    (fun l y z => by simp only [GlobalTheory.RedTh.sqForm_apply, mul_comm])
    (fun l y => by simp only [GlobalTheory.RedTh.sqForm_apply]; exact mul_self_nonneg _) fun B hB => ?_
  obtain ⟨X₁, _, m₁, hproj, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  obtain rfl : m₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := inferInstance
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  obtain ⟨b, d, d', u, t, hd, -, -, hg, -⟩ :=
    GlobalTheory.RedTh.exists_siegel_split r σ hrσ B₀ hs₀ hp₀ B₁ hB₁.1 hp₁ n hn
  obtain ⟨c, hc, hG⟩ := hS d u hd
  let e : X ≃ₗ[ℤ] X := b₀.equiv b (Equiv.refl _)
  have he : ∀ i, e (b₀ i) = b i := fun i => by simp [e]
  refine ⟨e, fun l => c l.1, fun l => hc _, ?_⟩
  refine b₀.ext fun i => b₀.ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [hBr, hg, hG]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    GlobalTheory.RedTh.sqForm_basis]
  rw [← Finset.sum_coe_sort S]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSet
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem finite_free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Module.Finite ℤ X ∧ Module.Free ℤ X := by
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hinj : Function.Injective s := fun x y h => by
    have := congrArg (Finsupp.linearCombination O id) h
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hinj ?_)
    rw [map_zero]
    ext c
    have h1 : r • s x = 0 := by
      rw [← map_zsmul s r x, hx, map_zero]
    have h2 : r • (s x c) = 0 := by simpa using DFunLike.congr_fun h1 c
    rw [zsmul_eq_mul] at h2
    have h3 : (r : O) ≠ 0 := by exact_mod_cast hr
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem exists_fin_reindex {T : Type} [Finite T] {X : Type} [AddCommGroup X] (m' : T → ℕ)
    (u' : ∀ t, Fin (m' t) → LinearMap.BilinForm ℤ X) (hsym : ∀ t i y z, u' t i y z = u' t i z y)
    (hnn : ∀ t i y, 0 ≤ u' t i y y) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∃ t, B ∈ rcone (u' t)) → ∃ j, B ∈ rcone (u j) := by
  obtain ⟨k, ⟨eq⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨k, fun j => m' (eq.symm j), fun j => u' (eq.symm j), fun j => hsym _, fun j => hnn _, ?_⟩
  rintro B ⟨t, ht⟩
  refine ⟨eq t, ?_⟩
  have key : ∀ t', t' = t → B ∈ rcone (u' t') := by
    rintro _ rfl
    exact ht
  exact key _ (eq.symm_apply_apply t)

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem isPosDef_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : IsPosDef B) :
    IsPosDef (pullR e.toLinearMap B) := by
  intro n x hx c hc
  let eZ : X ≃ₗ[ℤ] X := e.toAddEquiv.toIntLinearEquiv
  have h1 : LinearIndependent ℤ (fun i => e (x i)) := hx.map' eZ.toLinearMap eZ.ker
  simpa using hB n _ h1 c hc

theorem isMin2_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (hy : IsMin2 B y) :
    IsMin2 (pullR e.toLinearMap B) (e.symm y) := by
  intro x
  have := hy (e x)
  simpa [pullR_apply, map_add (f := _)] using this

theorem exists_rcone_cover_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
    HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR ha
  obtain ⟨hfin, hfree⟩ := finite_free_int_of_projective O X
  obtain ⟨k, n, P, hsym, hnn, hcov⟩ := hR
  choose F hF hmin using fun j => finite_isMin2 X (n j) (P j) (hsym j) (hnn j)
  have hU : (⋃ j, F j).Finite := Set.finite_iUnion hF
  have hS := finite_addHom_of_covers2 X ι a ha _ hU
  let S : Set (X →+ X) := {f : X →+ X | ∀ i, f (a i) ∈ ⋃ j, F j}
  have hSf : Finite S := hS
  let form : ∀ (t : (Fin k) × S), Fin (n t.1) → LinearMap.BilinForm ℤ X := fun t i =>
    (P t.1 i).compl₁₂ t.2.1.toIntLinearMap t.2.1.toIntLinearMap
  obtain ⟨K, m, u, h1, h2, h3⟩ := exists_fin_reindex (T := Fin k × S) (fun t => n t.1) form
    (fun t i y z => hsym _ _ _ _) (fun t i y => hnn _ _ _)
  refine ⟨K, m, u, h1, h2, fun B hB hpos => h3 B ?_⟩
  obtain ⟨e, j, c, hc, hE⟩ := hcov B hB.1
  let f : X →+ X := e.symm.toLinearMap.toAddMonoidHom
  have hf : f ∈ S := fun i => Set.mem_iUnion.2 ⟨j, hmin j _ ⟨c, hc, hE⟩ (isPosDef_pullR e hpos) _ (isMin2_pullR e (hB.2 i))⟩
  refine ⟨(j, ⟨f, hf⟩), c, hc, LinearMap.ext₂ fun y z => ?_⟩
  have h4 := LinearMap.congr_fun₂ hE (f y) (f z)
  simpa [f, form, LinearMap.sum_apply] using h4

end GlobalTheory.CompanionTheory.Ar.Fan
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabel
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.StarLab GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling

theorem isTwG_starLab {O : Type} [CommRing O] (w0 : O) {lab w : InvFun O}
    (hl : IsTwG w0 lab) (hw : IsTwG w0 w) : IsTwG w0 (starLab lab w) := by
  have fwd : ∀ (σ : O ≃+* O), σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      IsCentreRay w (Fin n → O) B →
        IsCentreRay w (Fin n → O) (fun a b => B (fun i => σ (a i)) fun i => σ (b i)) := by
    intro σ hσ n B h
    unfold IsCentreRay at h ⊢
    obtain ⟨t, ht, β, hβ, hB⟩ := h
    let τ : (Fin n → O) →ₗ[ℤ] (Fin n → O) :=
      { toFun := fun a i => σ (a i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun k a => by ext i; simp }
    let β' : LinearMap.BilinForm ℤ (Fin n → O) := β.compl₁₂ τ τ
    have h1 : w.evalZ β' = w.evalZ β := by
      unfold GlobalTheory.LocM.InvFun.evalZ
      rw [GlobalTheory.LocM.InvFun.eval_pi, GlobalTheory.LocM.InvFun.eval_pi]
      exact hw σ hσ n (fun a b => ((β a) b : ℝ))
    exact ⟨t, ht, β', h1.trans hβ, fun a b => hB (τ a) (τ b)⟩
  intro σ hσ n B
  have hσ' : σ.symm w0 = w0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hσ.symm
  have hiff : IsCentreRay w (Fin n → O) (fun a b => B (fun i => σ (a i)) fun i => σ (b i)) ↔
      IsCentreRay w (Fin n → O) B := by
    refine ⟨fun h => ?_, fwd σ hσ n B⟩
    have h2 := fwd σ.symm hσ' n _ h
    simp only [RingEquiv.apply_symm_apply] at h2
    exact h2
  rw [← GlobalTheory.LocM.InvFun.eval_pi, ← GlobalTheory.LocM.InvFun.eval_pi, starLab_eval, starLab_eval,
    GlobalTheory.LocM.InvFun.eval_pi, GlobalTheory.LocM.InvFun.eval_pi, hl σ hσ n B]
  by_cases hc : IsCentreRay w (Fin n → O) B
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (mt hiff.mp hc), if_neg hc]

theorem exists_isTwG_simpLab_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 lab → SimpLab bar q φ lab → IsTwG w0 w → IsCentreSet bar q φ w →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' →
    ∃ lab' : InvFun O, IsTwG w0 lab' ∧ SimpLab bar q ψ' lab' := by
  intro O _ _ _ _ bar w0 hb q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwG_starLab w0 hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le O bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell bar φ (fun j => δ (s j)) := _root_.GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell bar φ (fun j => γ (s j)) := _root_.GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le O bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · exact LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => by
        have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
        have h2 := congrArg g hz
        rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
        exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthBoundedDenominator
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator

theorem starDepth_den : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
        ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  intro O _ _ _ _ bar hb q ψ w hψ hw
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  have key : ∀ k : Fin n, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ {x : ℝ | ∃ β ∈ balForms bar (R k), (∀ y, 0 ≤ β y y) ∧
      haveI := (hR k).1; x = (starDepth bar ψ w).evalZ β}, ∃ z : ℤ, (D : ℝ) * x = z := fun k => by
    haveI := (hR k).1
    haveI := (hR k).2.1
    obtain ⟨-, h2, h3⟩ := hw (R k) (hR k).2.2
    obtain ⟨D, hD, hA⟩ := GlobalTheory.PolFan.StarDen.module_den (hψ (R k) (hR k).2.2) h2 h3
    refine ⟨D, hD, ?_⟩
    rintro x ⟨β, hβ, hp, rfl⟩
    exact hA β (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hb (R k) β hβ hp)
  obtain ⟨D₀, hD₀, hall⟩ := GlobalTheory.PolFan.StarDen.common_den _ key
  refine ⟨D₀, hD₀, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  haveI := (hR k).1
  have hval : (starDepth bar ψ w).evalZ (pull f.symm.toLinearMap β) = (starDepth bar ψ w).evalZ β :=
    evalZ_pull _ f.symm.surjective β
  rw [← hval]
  exact hall k _ ⟨_, pull_mem _ hβ, fun y => hp _, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator
end

