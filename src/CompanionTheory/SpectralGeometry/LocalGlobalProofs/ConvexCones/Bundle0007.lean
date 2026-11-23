module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan GlobalTheory.PolFan.CellClass

namespace GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells

theorem perModule {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolyFanOn bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
      ∃ e : X ≃ₗ[O] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms bar X, IsPrim bar (⟨t, ht⟩ : balForms bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := _root_.GlobalTheory.PolFan.isPrim_ray_eq bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone (bar := bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (_root_.GlobalTheory.PolFan.cell_gen_mem_cone_of_smul bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O),
    IsPolyFan bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong bar q φ M n := by
  intro O _ _ _ _ bar hb q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  haveI hfin : ∀ k, Module.Finite O (R k) := fun k => (hR k).1
  have key : ∀ k, ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar (R k))) →
        ∃ e : (R k) ≃ₗ[O] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    haveI := (hR k).2.1
    exact perModule bar φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily O := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim bar (⟨δ' i, hcell'.mem i⟩ : balForms bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthTwistedGalois
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist

section Twist

variable {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O}

variable {X : Type} [AddCommGroup X] [Module O X]

theorem mem_balForms_twist (hb : CMOrd O bar) (τ : O ≃+* O) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (bar a) • z)
    rw [h2, hb.comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (bar (τ.symm a)) • z) at this
    rwa [hb.comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwG {φ : InvFun O} (hφ : IsTwG w0 φ) (τ : O ≃+* O) (hτ : τ w0 = w0)
    [Module.Finite O X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite O X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → O) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module O X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm


omit [Module O X] in
theorem depthSet_twist_subset (hb : CMOrd O bar) {ψ w : InvFun O} (hψ : IsTwG w0 ψ) (hw : IsTwG w0 w) (σ : O ≃+* O)
    (hσ : σ w0 = w0) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    depthSet bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ w0 = w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → O) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite O X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → O) →ₗ[O] X₁) hs
  have hd' := isStarDepth_transfer bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist hb τ)
    (eval_twist_of_isTwG hψ τ hτ hf') (eval_twist_of_isTwG hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

end Twist

theorem isTwG_starDepth : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ w : InvFun O), IsTwG w0 ψ → IsTwG w0 w → IsTwG w0 (starDepth bar ψ w) := by
  intro O _ _ _ _ bar w0 hb ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset hb hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset hb hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositive
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_least_points {X : Type} [AddCommGroup X] {n : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y) :
    ∃ a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ, (∀ y, redV 1 (a y) = y) ∧ ∀ y, IsMin2 (toReal β) (r (a y)) := by
  have hmin : ∀ y : Fin n → ZMod (1 + 1), ∃ c : Fin n → ℤ, redV 1 c = y ∧
      ∀ c', redV 1 c' = y → β (r c) (r c) ≤ β (r c') (r c') := fun y => by
    obtain ⟨c0, h0⟩ := redV_surjective 1 n y
    obtain ⟨c, hc, hm⟩ := WellFounded.has_min
      (InvImage.wf (fun c : Fin n → ℤ => (β (r c) (r c)).toNat) Nat.lt_wfRel.wf)
      {c | redV 1 c = y} ⟨c0, h0⟩
    refine ⟨c, hc, fun c' hc' => ?_⟩
    have h1 : ¬ (β (r c') (r c')).toNat < (β (r c) (r c)).toNat := hm c' hc'
    have h2 := hβ (r c)
    have h3 := hβ (r c')
    omega
  choose a ha hm using hmin
  refine ⟨a, ha, fun y x => ?_⟩
  obtain ⟨d, rfl⟩ := hr x
  have h := hm y (a y + (((1 : ℕ) : ℤ) + 1) • d) (by rw [redV_add_smul, ha])
  have e : r (a y + (((1 : ℕ) : ℤ) + 1) • d) = r (a y) + (r d + r d) := by
    rw [map_add (f := _), map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  rw [e] at h
  simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
  exact_mod_cast h

theorem apply_eq_zero_of_self {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {z : X} (hz : β z z = 0) (w : X) : β z w = 0 := by
  by_contra ht
  have h := hβ (w + (-(β w w + 1) * β z w) • z)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hz, hs w z] at h
  have h1 : 1 ≤ β z w * β z w := mul_self_pos.2 ht
  have h2 := hβ w
  nlinarith

theorem eq_zero_of_covers {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {ι : Type} {a : ι → X} (hc : Covers2 a) (h0 : ∀ i, β (a i) (a i) = 0) : β = 0 := by
  have hdiv : ∀ (k : ℕ) (z w : X), (2 : ℤ) ^ k ∣ β z w := by
    intro k
    induction k with
    | zero => intro z w; simp
    | succ k ih =>
      intro z w
      obtain ⟨i, x, rfl⟩ := hc z
      obtain ⟨m, hm⟩ := ih x w
      refine ⟨m, ?_⟩
      simp only [map_add (f := _), LinearMap.add_apply, apply_eq_zero_of_self β hs hβ (h0 i) w, hm]
      ring
  refine LinearMap.ext₂ fun z w => ?_
  refine Int.eq_zero_of_abs_lt_dvd (hdiv (β z w).natAbs z w) ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_two_pow_self

theorem vorFun_int_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q →
    (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  intro O _ _ _ _ bar g q X _ _ _ _ hg hq
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  have hO : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.trans O
  have hfree : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have hn : Module.finrank ℤ X ≤ g := by
    rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := O) (M := X)]
    exact (Nat.mul_le_mul_left _ hq).trans hg
  let b : Module.Basis (Fin (Module.finrank ℤ X)) ℤ X := Module.finBasis ℤ X
  let r : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hr : Function.Surjective r := b.equivFun.symm.surjective
  have key : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) →
      ∃ a : (Fin (Module.finrank ℤ X) → ZMod (1 + 1)) → Fin (Module.finrank ℤ X) → ℤ, Covers2 (fun y => r (a y)) ∧
        (vorFun O g).evalZ β = 2 ^ (g - Module.finrank ℤ X) * ∑ y, (β (r (a y)) (r (a y)) : ℝ) := by
    intro β hβ
    obtain ⟨a, ha, hm⟩ := exists_least_points r hr β hβ
    obtain ⟨hc, h⟩ := vorFun_value_le O bar g X _ r a hr ha
    refine ⟨a, hc, ?_⟩
    have hB : ∀ y, 0 ≤ toReal β y y := fun y => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
      exact_mod_cast hβ y
    have h1 := ((h (toReal β) hB).2).2 hm
    rw [evalR_toReal] at h1
    have h2 : ∀ u v, toReal β u v = (β u v : ℝ) := fun u v => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
    simp only [h2] at h1
    have h3 : (2 : ℝ) ^ g = 2 ^ Module.finrank ℤ X * 2 ^ (g - Module.finrank ℤ X) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    rw [h3, mul_assoc] at h1
    exact mul_left_cancel₀ (by positivity) h1
  refine ⟨fun β hβ => ?_, fun β hs hβ hne => ?_⟩
  · obtain ⟨a, -, h⟩ := key β hβ
    exact ⟨2 ^ (g - Module.finrank ℤ X) * ∑ y, β (r (a y)) (r (a y)), by rw [h]; push_cast; rfl⟩
  · obtain ⟨a, hc, h⟩ := key β hβ
    have hnn : ∀ y, (0 : ℝ) ≤ (β (r (a y)) (r (a y)) : ℝ) := fun y => by exact_mod_cast hβ _
    rw [h]
    refine mul_pos (by positivity) (lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hnn y) fun h0 => hne ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 h0.symm
    exact eq_zero_of_covers β hs hβ hc fun y => by exact_mod_cast h1 y (Finset.mem_univ y)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

