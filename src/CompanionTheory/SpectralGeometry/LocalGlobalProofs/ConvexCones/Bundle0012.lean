module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsDescendingRaysPullback
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.DescendingRaysPullback

theorem exists_desc_rays_pullAdd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
  [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, hm i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) (τ : O ≃+* O)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 → Function.Surjective f →
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule O X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule O X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun O, IsTwG w0 lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  intro O _ _ _ _ bar w0 hb X₀ _ _ _ m₀ δ₀ hm hpos hli hprim v t ht hv X _ _ _ β τ f hτ hf hsm hβ
  classical
  generalize hK : (CarDim.orad v : Submodule (O) X₀) = K at *
  have hvan : ∀ i, 0 < t i → ∀ x ∈ K, ∀ y, δ₀ i x y = 0 := by
    intro i hi x hx y
    have hxx : v x x = 0 := by rw [← hK] at hx; simpa using (CarDim.mem_orad.1 hx) 1 x
    have hsum := LinearMap.congr_fun₂ hv x x
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hxx, Int.cast_zero] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (ht j) (Int.cast_nonneg (hpos j x))).1 hsum.symm i (Finset.mem_univ _)
    have h0 : δ₀ i x x = 0 := by
      rcases mul_eq_zero.1 hall with h | h
      · exact absurd h hi.ne'
      · exact_mod_cast h
    exact ConeSub.eq_zero_of_self_eq_zero (δ₀ i) (hm i).1 (hpos i) h0 y
  have hex : ∀ i, ∃ u : LinearMap.BilinForm ℤ (X₀ ⧸ K), 0 < t i → pull K.mkQ u = δ₀ i := by
    intro i
    by_cases hi : 0 < t i
    · obtain ⟨u, hu⟩ := CarDim.exists_pull_mkQ_eq_of_vanish K (δ₀ i) (hvan i hi)
        (fun x y hy => by rw [(hm i).1]; exact hvan i hi y hy x)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose u hu using hex
  have hU : ∀ i, 0 < t i → ∀ y₀ z₀ : X₀, u i (Submodule.Quotient.mk y₀) (Submodule.Quotient.mk z₀) = δ₀ i y₀ z₀ :=
    fun i hi y₀ z₀ => LinearMap.congr_fun₂ (hu i hi) y₀ z₀
  have hq : ∀ z : X₀ ⧸ K, ∃ z₀ : X₀, Submodule.Quotient.mk z₀ = z := Submodule.Quotient.mk_surjective K
  let P : LinearMap.BilinForm ℤ (X₀ ⧸ K) →ₗ[ℤ] LinearMap.BilinForm ℤ X₀ :=
    { toFun := pull K.mkQ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨u, ?_, ?_, ?_⟩
  · refine LinearMap.ext₂ fun x y => ?_
    obtain ⟨x₀, hx₀⟩ := hq (f x)
    obtain ⟨y₀, hy₀⟩ := hq (f y)
    have h1 := LinearMap.congr_fun₂ hv x₀ y₀
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pullAdd_apply] at h1 ⊢
    rw [hβ x y x₀ y₀ hx₀ hy₀, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (ht i).lt_or_eq with hi | hi
    · rw [← hx₀, ← hy₀, hU i hi]
    · rw [← hi, zero_mul, zero_mul]
  · have hδ : LinearIndependent ℤ (fun i : {i // 0 < t i} => δ₀ i) := hli.comp _ Subtype.val_injective
    have hu' : LinearIndependent ℤ (fun i : {i // 0 < t i} => u i) := by
      refine LinearIndependent.of_comp P ?_
      convert hδ using 1
      funext i
      exact hu i i.2
    exact hu'.map' (pullAddLin f) (LinearMap.ker_eq_bot.2 (pullAdd_injective hf))
  · intro i hi
    refine ⟨hu i hi, ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, fun k β' hk => ?_, fun lab hlab => ?_⟩
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, ← hy₀, ← hz₀, hU i hi]
      exact (hm i).1 y₀ z₀
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, hsm, ← hy₀, ← hz₀, ← Submodule.Quotient.mk_smul, hU i hi]
      rw [(hm i).2, hb.comm τ a]
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      simp only [pullAdd_apply, ← hy₀, hU i hi]
      exact hpos i y₀
    · obtain ⟨ζ, hζ⟩ : ∃ ζ : LinearMap.BilinForm ℤ (X₀ ⧸ K), (k : ℤ) • ζ = u i := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · refine ⟨0, ?_⟩
          have : pullAdd f (u i) = pullAdd f 0 := by
            rw [← hk]; ext; simp
          rw [pullAdd_injective hf this]; simp
        · have hk0' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
          have hval : ∀ x y, (k : ℤ) * β' x y = u i (f x) (f y) := fun x y => by
            rw [← pullAdd_apply, ← hk]; simp
          obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β'
            (fun x hx y => by
              have := hval x y
              rw [hx, map_zero, LinearMap.zero_apply] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
            (fun x hx y => by
              have := hval y x
              rw [hx, map_zero] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
          refine ⟨ζ, LinearMap.ext₂ fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := hf a
          obtain ⟨y, rfl⟩ := hf b
          simp [hζ, hval]
      refine isPrim_eq_one_of_smul_eq bar (δ₀ i) (hm i) (hprim i) k (pull K.mkQ ζ) ?_
      rw [← hu i hi, ← hζ]
      ext a b
      simp
    · have h1 := GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval.eval_pull_semilinear_of_isTwG O bar w0 hb lab hlab τ hτ f hf hsm (fun a b => (u i a b : ℝ))
      rw [← hu i hi, evalZ_pull lab K.mkQ_surjective]
      exact h1

end GlobalTheory.CompanionTheory.Ar.Fan.DescendingRaysPullback
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPullbackCoordinateOfPos
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates

theorem mem_balForms_of_descend {O : Type} [CommRing O] {bar : O → O} (hb : CMOrd O bar) {X Y : Type} [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] (τ : O ≃+* O) {f : X →+ Y} (hf : Function.Surjective f)
    (hsm : ∀ (a : O) (x : X), f (a • x) = τ a • f x) {δ : LinearMap.BilinForm ℤ X} (hδ : δ ∈ balForms bar X)
    {ε : LinearMap.BilinForm ℤ Y} (hε : ∀ x y, ε (f x) (f y) = δ x y) : ε ∈ balForms bar Y := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    rw [hε, hε, hδ.1]
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    obtain ⟨a, rfl⟩ := τ.surjective a
    rw [← hb.comm τ a, ← hsm, ← hsm, hε, hε, hδ.2]

theorem exists_coord_pullAdd_of_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (π : X₀ →ₗ[O] Y), Function.Surjective π → ∀ (τ : O ≃+* O) (f : X →+ Y), τ w0 = w0 →
    Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  intro O _ _ _ _ bar w0 hb φ htw X₀ _ _ _ m₀ δ₀ h₀ hind v t ht hvt X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc j hj
  classical
  have hval : ∀ x y, (β x y : ℝ) = ∑ l, c l * (δ l x y : ℝ) := fun x y => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hβc x y
  have hvan : ∀ l, 0 < c l → ∀ x, f x = 0 → ∀ y, δ l x y = 0 := by
    intro l hl x hx y
    have hb : β x x = 0 := by simpa using hβ x x 0 0 (by simp [hx]) (by simp [hx])
    have hk := hval x x
    rw [hb, Int.cast_zero] at hk
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hc i) (Int.cast_nonneg (hδ.nonneg i x))).1 hk.symm l (Finset.mem_univ _)
    have h0 : δ l x x = 0 := Int.cast_eq_zero.1 ((mul_eq_zero.1 hall).resolve_left hl.ne')
    exact ConeSub.eq_zero_of_self_eq_zero (δ l) (hδ.mem l).1 (hδ.nonneg l) h0 y
  set S : Finset (Fin m) := Finset.univ.filter fun l => 0 < c l with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hspos : ∀ i, 0 < c (s i) := fun i => by
    have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
    simpa [hS] using this
  have hdesc : ∀ i : Fin S.card, ∃ ε : LinearMap.BilinForm ℤ Y, ∀ x y, ε (f x) (f y) = δ (s i) x y := fun i =>
    GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf _ (hvan _ (hspos i)) fun x hx y => by rw [(hδ.mem _).1]; exact hvan _ (hspos i) x hx y
  choose ε hε using hdesc
  have hεm : ∀ i, ε i ∈ balForms bar Y := fun i => mem_balForms_of_descend hb τ hf hsm (hδ.mem _) (hε i)
  have hεn : ∀ i y, 0 ≤ ε i y y := fun i y => by
    obtain ⟨y, rfl⟩ := hf y
    rw [hε]; exact hδ.nonneg _ _
  have hsemi := _root_.GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval.eval_pull_semilinear_of_isTwG O bar w0 hb φ htw τ hτ f hf hsm
  have hεl : φ.LinearOn ε := by
    intro d hd
    have h1 := linearOn_comp hδ.linear s d hd
    have h2 : ∀ i, φ.evalZ (δ (s i)) = φ.evalZ (ε i) := fun i => by
      have := hsemi fun a b => (ε i a b : ℝ)
      simp only [hε] at this
      exact this
    have h3 := hsemi fun a b => ∑ i, d i * (ε i a b : ℝ)
    simp only [hε] at h3
    simp only [h2] at h1
    exact h3.symm.trans h1
  have hvb : toReal v = ∑ i, c (s i) • toReal (pull π (ε i)) := LinearMap.ext₂ fun x₀ y₀ => by
    obtain ⟨x, hx⟩ := hf (π x₀)
    obtain ⟨y, hy⟩ := hf (π y₀)
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply]
    rw [← hβ x y x₀ y₀ hx.symm hy.symm, hval, ← hx, ← hy]
    simp only [hε]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun l hl => ?_) fun i => rfl).symm
    have : ¬ 0 < c l := by rw [hs] at hl; simpa [hS] using hl
    rw [le_antisymm (not_lt.1 this) (hc l), zero_mul]
  obtain ⟨j, rfl⟩ : j ∈ Set.range s := by rw [hs]; simpa [hS] using hj
  obtain ⟨a, ha, ha0, he⟩ := exists_face_coord_of_linearOn h₀ hind (fun i => pull_mem π (hεm i)) (fun i y => hεn i _)
    ((linearOn_pull_iff hπ).2 hεl) ht hspos hvt hvb j
  refine ⟨a, ha, ha0, LinearMap.ext₂ fun x y => ?_⟩
  obtain ⟨x₀, hx⟩ := hπ (f x)
  obtain ⟨y₀, hy⟩ := hπ (f y)
  have h1 := LinearMap.congr_fun₂ he x₀ y₀
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply, pullAdd_apply] at h1 ⊢
  rw [hx, hy, hε] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).eq_or_lt with h | h
  · rw [ha0 i h.symm, zero_mul, zero_mul]
  · rw [← hu i h, pull_apply, hx, hy]

end GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStar
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity


open GlobalTheory.PolFan.StarNewCell in
theorem cellMult_lt_of_star_new : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar φ γ → β₀ ∈ balForms bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
  intro O _ _ _ _ bar _hb q φ lab w ψ' hSL hCS hcoord M hM X _ _ _ _ hX n γ' hγ' hliγ' hprimγ' m γ β₀ m' s h hγ hβ₀ hβ₀p hw
    hβ₀γ hcut hpos hτ hγ'τ
  classical

  obtain ⟨m₀, δ, hδ, hliδ, -, hγδ⟩ := hSL.2 X hX m γ hγ
  obtain ⟨δt, hδt, hliδt, hprimδt, hδδt⟩ := _root_.GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim bar φ δ hδ hliδ
  have hγδt : ∀ k, InRCone δt (γ k) := fun k => hδδt _ (hγδ k)

  obtain ⟨h₂, h₂0, h₂γ, h₂cut⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form bar φ δt γ hδt hγ hγδt
  have hcutγ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 →
      InRCone (fun k => γ (s k)) β :=
    fun β _ _ hβ hβ0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero γ h s β hcut.1 (fun i hi => (hcut.2 i).1 hi) hβ hβ0
  have hhs : ∀ k, h (γ (s k)) = 0 := fun k => (hcut.2 (s k)).2 ⟨k, rfl⟩
  obtain ⟨h₃, h₃0, h₃γs, h₃cut⟩ := _root_.GlobalTheory.PolFan.exists_linForm_cut_face_of_face bar δt γ (fun k => γ (s k)) h₂ h hδt.mem hδt.nonneg
    (fun k => inRCone_self γ (s k)) h₂0 h₂γ h₂cut hcut.1 hhs hcutγ

  set I : Finset (Fin m₀) := Finset.univ.filter (fun i => h₃ (δt i) = 0) with hI
  set eI : Fin I.card ↪ Fin m₀ := (I.orderEmbOfFin rfl).toEmbedding with heIdef
  have heI : ∀ i, i ∈ Set.range eI ↔ h₃ (δt i) = 0 := by
    intro i
    show i ∈ Set.range (I.orderEmbOfFin rfl) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [I]
  have hsupp : ∀ β, InRCone δt β → h₃ β = 0 → InRCone (fun k => δt (eI k)) β :=
    fun β hβ h0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero δt h₃ eI β h₃0 (fun i hi => (heI i).2 hi) hβ h0

  obtain ⟨c, hc0, hcβ⟩ : InRCone δt β₀ := StarNewCell.inRCone_trans hγδt hβ₀γ
  have hclt : ∀ i, c i < 1 := hcoord X hX m₀ δt hδt hliδt hprimδt β₀ hβ₀ hβ₀p hw c hc0 hcβ
  obtain ⟨j, hcj, hjI⟩ : ∃ j, 0 < c j ∧ h₃ (δt j) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h30 : h₃ β₀ = 0 := by
      have : (h₃ β₀ : ℝ) = 0 := by
        rw [val_eq h₃ hcβ]
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases (hc0 i).eq_or_lt with hi | hi
        · rw [← hi, zero_mul]
        · rw [hno i hi]; simp
      exact_mod_cast this
    have := val_zero h hhs (h₃cut β₀ hβ₀ hβ₀p ⟨c, hc0, hcβ⟩ h30)
    omega

  have hprimβ₀ : ∀ hx : β₀ ∈ balForms bar X, IsPrim bar (⟨β₀, hx⟩ : balForms bar X) := by
    intro hx k β' hk
    refine (hCS X hX).2.1 β₀ hβ₀ hβ₀p hw k β' ?_
    have h' : β₀ = ((k • β' : balForms bar X) : LinearMap.BilinForm ℤ X) := congrArg Subtype.val hk
    rw [h', Submodule.coe_smul_of_tower, natCast_zsmul]

  set δs : Fin m₀ → balForms bar X := fun i => ⟨δt i, hδt.mem i⟩ with hδs
  set βs : balForms bar X := ⟨β₀, hβ₀⟩ with hβs
  have hliδs : LinearIndependent ℤ δs := LinearIndependent.of_comp (balForms bar X).subtype hliδt

  set ρs : Fin (I.card + 1) → balForms bar X := Fin.cons βs (fun k => δs (eI k)) with hρsdef
  obtain ⟨ρ, hρ0, hρs, hρv⟩ : ∃ ρ : Fin (I.card + 1) → LinearMap.BilinForm ℤ X, ρ 0 = β₀ ∧
      (∀ k, ρ k.succ = δt (eI k)) ∧ ∀ i, ρ i = (ρs i : LinearMap.BilinForm ℤ X) :=
    ⟨fun i => (ρs i : LinearMap.BilinForm ℤ X), by simp [ρs, βs], fun k => by simp [ρs, δs], fun i => rfl⟩
  have hjeI : j ∉ Set.range eI := fun hh => hjI ((heI j).1 hh)
  have hliρ : LinearIndependent ℤ ρ := by
    have h1 := _root_.GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero bar δs βs c j eI hliδs hcβ hcj.ne' hjeI
    have h2 := h1.map' (balForms bar X).subtype (Submodule.ker_subtype _)
    have : ρ = (balForms bar X).subtype ∘ ρs := funext hρv
    rw [this]; exact h2
  have hρmem : ∀ i, ρ i ∈ balForms bar X := fun i => by rw [hρv]; exact (ρs i).2
  have hρnn : ∀ i y, 0 ≤ ρ i y y := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact hβ₀p
    · rw [hρs]; exact hδt.nonneg _
  have hρprim : ∀ i, IsPrim bar (⟨ρ i, hρmem i⟩ : balForms bar X) := by
    have key : ∀ (x y : LinearMap.BilinForm ℤ X) (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), x = y →
        IsPrim bar (⟨y, hy⟩ : balForms bar X) → IsPrim bar (⟨x, hx⟩ : balForms bar X) := by
      rintro x y hx hy rfl hp; exact hp
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · exact key _ _ _ hβ₀ hρ0 (hprimβ₀ hβ₀)
    · exact key _ _ _ (hδt.mem _) (hρs k) (hprimδt _)

  have hτρ : ∀ i, InRCone ρ ((Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, ← hρ0]; exact inRCone_self ρ 0
    · rw [Fin.cons_succ]
      exact StarNewCell.inRCone_trans (fun l => hρs l ▸ inRCone_self ρ l.succ) (hsupp _ (hγδt (s k)) (h₃γs k))
  have hρτ : ∀ i, InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) (ρ i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact inRCone_cons_zero _ _
    · rw [hρs]
      exact StarNewCell.inRCone_trans (fun l => inRCone_cons_succ β₀ (fun j => γ (s j)) l)
        (h₃cut _ (hδt.mem _) (hδt.nonneg _) (inRCone_self δt _) ((heI _).1 ⟨k, rfl⟩))

  obtain ⟨h₁, h₁0, h₁γ', h₁cut⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form bar ψ' _ γ' hτ hγ' hγ'τ
  obtain ⟨s', hs', -⟩ := _root_.GlobalTheory.PolFan.eq_subfamily_of_face bar ρ γ' hρmem hγ'.mem h₁ hliρ hliγ' hρprim hprimγ'
    (fun k => StarNewCell.inRCone_trans hτρ (hγ'τ k)) (fun i => val_nonneg h₁ h₁0 (hρτ i)) h₁γ'
    (fun i hi => h₁cut (ρ i) (hρmem i) (hρnn i) (hρτ i) hi)

  set J : Finset (Fin m₀) := Finset.univ.erase j with hJ
  have hJc : J.card = m₀ - 1 := by simp [J]
  set eJ : Fin (m₀ - 1) ↪ Fin m₀ := (J.orderEmbOfFin hJc).toEmbedding with heJdef
  have heJ : ∀ i, i ∈ Set.range eJ ↔ i ≠ j := by
    intro i
    show i ∈ Set.range (J.orderEmbOfFin hJc) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [J]
  set ρ's : Fin (m₀ - 1 + 1) → balForms bar X := Fin.cons βs (fun k => δs (eJ k)) with hρ'sdef
  have hliρ' : LinearIndependent ℤ ρ's := _root_.GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero bar δs βs c j eJ hliδs hcβ hcj.ne' (fun hh => (heJ j).1 hh rfl)
  have hmultρ' : (cellMult bar ρ's : ℝ) = c j * cellMult bar δs :=
    _root_.GlobalTheory.PolFan.ConsMult.cellMult_cons_eq bar δs βs c j eJ hliδs hcβ hcj heJ (_root_.GlobalTheory.PolFan.cellMult_pos bar δs)
  have hrange : Set.range (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ⊆ Set.range ρ's := by
    rintro _ ⟨k, rfl⟩
    have e := hs' k
    rcases Fin.eq_zero_or_eq_succ (s' k) with h0 | ⟨l, hl⟩
    · refine ⟨0, Subtype.ext ?_⟩
      simp [ρ's, βs]
      rw [e, h0, hρ0]
    · have hne : eI l ≠ j := fun hh => hjI (hh ▸ (heI (eI l)).1 ⟨l, rfl⟩)
      obtain ⟨r, hr⟩ := (heJ (eI l)).2 hne
      refine ⟨r.succ, Subtype.ext ?_⟩
      simp [ρ's, δs]
      rw [e, hl, hρs, hr]
  have hdvd : cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ∣ cellMult bar ρ's :=
    _root_.GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset (balForms bar X) ρ's _ hliρ' hrange
  have hle := Nat.le_of_dvd (_root_.GlobalTheory.PolFan.cellMult_pos bar ρ's) hdvd
  have hδpos := _root_.GlobalTheory.PolFan.cellMult_pos bar δs
  have hlt : (cellMult bar ρ's : ℝ) < cellMult bar δs := by
    rw [hmultρ']; exact mul_lt_of_lt_one_left (by exact_mod_cast hδpos) (hclt j)
  have hlt' : cellMult bar ρ's < cellMult bar δs := by exact_mod_cast hlt
  have hδsM : cellMult bar δs ≤ M := by
    have := (SmoothEnd.cellMult_le_maxMult hX hδt hliδt hprimδt).trans hM
    exact_mod_cast this
  omega

end GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStar
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity

theorem starOld_cell_mult_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → IsCell bar ψ' γ →
          (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell bar φ γ', cellMult bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms bar X)) ≤ M ∧
            ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  intro O _ _ _ _ bar hb q φ lab w ψ' hDom hφ hlab M hM X _ _ _ _ hX n γ' hγ' hli' hp' m γ hγφ hγψ hw hin

  obtain ⟨m', δ, hδ, hδli, -, hδγ⟩ := hlab.2 X hX m γ hγφ
  obtain ⟨δ₁, hδ₁, hδ₁li, hδ₁p, hδδ₁⟩ := _root_.GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim bar φ δ hδ hδli
  have hγδ₁ : ∀ k, InRCone δ₁ (γ k) := fun k => hδδ₁ _ (hδγ k)

  obtain ⟨h₂, h₂n, h₂z, h₂c⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form bar φ δ₁ γ hδ₁ hγφ hγδ₁
  obtain ⟨h₁, h₁n, h₁z, h₁c⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form bar ψ' γ γ' hγψ hγ' hin
  obtain ⟨h, hn, hz, hc⟩ := _root_.GlobalTheory.PolFan.exists_linForm_cut_face_of_face bar δ₁ γ γ' h₂ h₁ hδ₁.mem hδ₁.nonneg hin h₂n h₂z h₂c h₁n h₁z h₁c
  have hin₁ : ∀ j, InRCone δ₁ (γ' j) := fun j => inRCone_trans hγδ₁ (hin j)
  obtain ⟨s, hs, hsf⟩ := _root_.GlobalTheory.PolFan.eq_subfamily_of_face bar δ₁ γ' hδ₁.mem hγ'.mem h hδ₁li hli' hδ₁p hp' hin₁ hn hz
    (fun i hi => hc _ (hδ₁.mem i) (hδ₁.nonneg i) (inRCone_self δ₁ i) hi)
  have hγ'eq : γ' = fun j => δ₁ (s j) := funext hs
  have hcut : IsFaceCut δ₁ s h := ⟨hn, hsf⟩
  have hφ' : IsCell bar φ γ' := by
    rw [hγ'eq]; exact GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q φ hφ X hX (hDom X) m' δ₁ hδ₁ _ s h hcut
  refine ⟨hφ', ?_, fun β hβ hβn hβc h1 => ?_⟩
  ·
    have hliB : LinearIndependent ℤ (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) :=
      LinearIndependent.of_comp (balForms bar X).subtype hδ₁li
    have hrange : Set.range (fun j => (⟨γ' j, hφ'.mem j⟩ : balForms bar X)) ⊆
        Set.range (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨s j, Subtype.ext (hs j).symm⟩
    have hdvd := _root_.GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset (balForms bar X) _ _ hliB hrange
    have hpos := _root_.GlobalTheory.PolFan.cellMult_pos bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X))
    have hle := SmoothEnd.cellMult_le_maxMult hX hδ₁ hδ₁li hδ₁p
    have hle' : cellMult bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) ≤ M := by
      exact_mod_cast hle.trans hM
    exact (Nat.le_of_dvd hpos hdvd).trans hle'
  ·
    rw [hw β hβ hβn (inRCone_trans hin hβc)] at h1
    exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity
end

