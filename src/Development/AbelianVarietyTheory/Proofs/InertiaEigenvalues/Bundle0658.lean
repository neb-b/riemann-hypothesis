module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumLocalEulerFactorHeckeOperators
section
open scoped InnerProductSpace BigOperators

noncomputable section

namespace GlobalTheory.UpInj.LocalSum

def dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : Set Γ :=
  {y | ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ y = k₁ * g * k₂}

theorem mem_dc_self {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : g ∈ dc K c g :=
  ⟨1, 1, K.one_mem, map_one c, K.one_mem, map_one c, by simp⟩

theorem mul_mem_dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y k : Γ} (h : y ∈ dc K c g)
    (hk : k ∈ K) (hck : c k = k) : y * k ∈ dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  exact ⟨k₁, k₂ * k, h1, h2, K.mul_mem h3 hk, by rw [map_mul, h4, hck], by simp [mul_assoc]⟩

theorem dc_eq_of_mem {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y : Γ} (h : y ∈ dc K c g) :
    dc K c y = dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁, k₂ * l₂, K.mul_mem i1 h1, by rw [map_mul, i2, h2], K.mul_mem h3 i3,
      by rw [map_mul, h4, i4], by simp [mul_assoc]⟩
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁⁻¹, k₂⁻¹ * l₂, K.mul_mem i1 (K.inv_mem h1), by rw [map_mul, map_inv, i2, h2],
      K.mul_mem (K.inv_mem h3) i3, by rw [map_mul, map_inv, h4, i4], by group⟩

theorem out_mk {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (δ : Γ) :
    ∃ h, c h ∈ K ∧ Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c) = δ * h := by
  have e := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk δ : Γ ⧸ K.comap c))
  refine ⟨δ⁻¹ * Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c), ?_, by group⟩
  have := (K.comap c).inv_mem e
  rw [mul_inv_rev, inv_inv] at this
  exact this

end GlobalTheory.UpInj.LocalSum


open GlobalTheory.UpInj.LocalSum in
theorem GlobalTheory.UpInj.localSum_hasSum : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (S : ℝ), (∀ g, c (c g) = c g) → (∀ g k k', k ∈ K → k' ∈ K → a (k * g * k') = a g) → (∀ g k, k ∈ K → B (g * k) = B g) → (∀ g, ‖B g‖ ≤ 1) → (∀ C : Finset Γ, (∀ g ∈ C, c g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ S) → (∀ α, c α = α → ∃ C, GlobalTheory.UpInj.DCRep c K α C) → (∀ α C, c α = α → GlobalTheory.UpInj.DCRep c K α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) → ∀ γ, HasSum (fun x : Γ ⧸ K.comap c => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap c, a (c (Quotient.out x)) • B (c (Quotient.out x))) := by
  intro Γ _ K c H _ _ _ a B S hc ha hB hB1 hS hex hH γ
  classical
  let r : Γ ⧸ K.comap c → Γ := fun x => c (Quotient.out x)
  have hr_fix : ∀ x, c (r x) = r x := fun x => hc _
  have hr_eq : ∀ x x' : Γ ⧸ K.comap c, (r x)⁻¹ * r x' ∈ K ↔ x = x' := by
    intro x x'
    have e : (r x)⁻¹ * r x' = c ((Quotient.out x)⁻¹ * Quotient.out x') := by simp [r, map_mul, map_inv]
    rw [e, ← Subgroup.mem_comap, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hr_one : ∀ x : Γ ⧸ K.comap c, r x ∈ K ↔ x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c) := by
    intro x
    have key : (QuotientGroup.mk 1 : Γ ⧸ K.comap c) = QuotientGroup.mk (Quotient.out x) ↔
        1⁻¹ * Quotient.out x ∈ K.comap c := QuotientGroup.eq
    rw [QuotientGroup.out_eq', inv_one, one_mul, Subgroup.mem_comap] at key
    rw [eq_comm]; exact key.symm
  have ha1 : ∀ g, g ∈ K → a g = a 1 := fun g hg => by simpa using ha 1 g 1 hg K.one_mem
  have hsum : Summable (fun x : Γ ⧸ K.comap c => ‖a (r x)‖) := by
    refine summable_of_sum_le (c := ‖a 1‖ + S) (fun x => norm_nonneg _) (fun u => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not u (fun x => x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c))]
    gcongr ?_ + ?_
    · calc ∑ x ∈ u.filter (fun x => x = QuotientGroup.mk 1), ‖a (r x)‖
            ≤ ∑ x ∈ {(QuotientGroup.mk 1 : Γ ⧸ K.comap c)}, ‖a (r x)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp [(Finset.mem_filter.1 hx).2])
              (fun _ _ _ => norm_nonneg _)
        _ = ‖a 1‖ := by rw [Finset.sum_singleton, ha1 _ ((hr_one _).2 rfl)]
    · rw [← Finset.sum_image (f := fun g => ‖a g‖) (fun x _ x' _ h => (hr_eq x x').1 (by rw [h, inv_mul_cancel]; exact K.one_mem))]
      apply hS
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨hr_fix x, fun h => (Finset.mem_filter.1 hx).2 ((hr_one x).1 h)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨x', _, rfl⟩ := Finset.mem_image.1 hg'
        rw [(hr_eq x x').1 h]
  have hnorm : ∀ g γ', ‖a g • B (γ' * g)‖ ≤ ‖a g‖ := fun g γ' => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hB1 _)
  let F : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))
  let G : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (c (Quotient.out x))
  have hF : Summable F := Summable.of_norm_bounded hsum (fun x => hnorm _ _)
  have hG : Summable G := Summable.of_norm_bounded hsum (fun x => by simpa using hnorm (r x) 1)
  let q : Γ ⧸ K.comap c → Set Γ := fun x => dc K c (r x)
  have hfib : ∀ b : Set Γ, ∑' y : {x // q x = b}, F y.1 = B γ * ∑' y : {x // q x = b}, G y.1 := by
    intro b
    by_cases hb : ∃ x0, q x0 = b
    swap
    · push_neg at hb
      haveI : IsEmpty {x // q x = b} := ⟨fun y => hb y.1 y.2⟩
      simp [tsum_empty]
    obtain ⟨x0, rfl⟩ := hb
    obtain ⟨C, hC⟩ := hex (r x0) (hr_fix x0)
    have memfib : ∀ x, q x = q x0 ↔ r x ∈ dc K c (r x0) := fun x =>
      ⟨fun h => by rw [← show dc K c (r x) = dc K c (r x0) from h]; exact mem_dc_self K c _,
       fun h => dc_eq_of_mem K c h⟩
    have hval : ∀ δ ∈ C, ∃ k, k ∈ K ∧ c k = k ∧ r (QuotientGroup.mk δ) = δ * k := by
      intro δ hδ
      obtain ⟨h, hh, he⟩ := out_mk K c δ
      exact ⟨c h, hh, hc h, by show c (Quotient.out _) = _; rw [he, map_mul, (hC.1 δ hδ).1]⟩
    have haδ : ∀ δ ∈ C, ∀ k, k ∈ K → a (δ * k) = a (r x0) := by
      intro δ hδ k hk
      obtain ⟨_, k₁, k₂, h1, -, h3, -, hδe⟩ := hC.1 δ hδ
      rw [hδe, ← ha (r x0) k₁ (k₂ * k) h1 (K.mul_mem h3 hk)]
      simp [mul_assoc]
    have hFv : ∀ δ ∈ C, F (QuotientGroup.mk δ) = a (r x0) • B (γ * δ) := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (γ * r _) = _
      rw [he, haδ δ hδ k hk, ← mul_assoc, hB _ _ hk]
    have hGv : ∀ δ ∈ C, G (QuotientGroup.mk δ) = a (r x0) • B δ := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (r _) = _
      rw [he, haδ δ hδ k hk, hB _ _ hk]
    let e : C → {x // q x = q x0} := fun δ => ⟨QuotientGroup.mk δ.1, (memfib _).2 (by
      obtain ⟨k, hk, hck, he⟩ := hval δ.1 δ.2
      rw [he]
      obtain ⟨_, k₁, k₂, h1, h2, h3, h4, hδe⟩ := hC.1 δ.1 δ.2
      exact mul_mem_dc K c ⟨k₁, k₂, h1, h2, h3, h4, hδe⟩ hk hck)⟩
    have hinj : Function.Injective e := by
      rintro ⟨δ, hδ⟩ ⟨δ', hδ'⟩ h
      have h' : (QuotientGroup.mk δ : Γ ⧸ K.comap c) = QuotientGroup.mk δ' := congrArg Subtype.val h
      have hfix : c (δ⁻¹ * δ') = δ⁻¹ * δ' := by rw [map_mul, map_inv, (hC.1 δ hδ).1, (hC.1 δ' hδ').1]
      rw [QuotientGroup.eq, Subgroup.mem_comap, hfix] at h'
      apply Subtype.ext
      exact (hC.2 δ' (hC.1 δ' hδ').2).unique ⟨hδ, h', hfix⟩ ⟨hδ', by simp, by simp⟩
    have hsurj : Function.Surjective e := by
      rintro ⟨x, hx⟩
      obtain ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩ := (memfib x).1 hx
      obtain ⟨δ, ⟨hδ, hK, -⟩, -⟩ := hC.2 (r x) ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩
      refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
      show (QuotientGroup.mk δ : Γ ⧸ K.comap c) = x
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv, (hC.1 δ hδ).1]
      exact hK
    have hT : ∀ f : Γ ⧸ K.comap c → (H →L[ℂ] H),
        ∑' y : {x // q x = q x0}, f y.1 = ∑ δ ∈ C, f (QuotientGroup.mk δ) := by
      intro f
      rw [← Equiv.tsum_eq (Equiv.ofBijective e ⟨hinj, hsurj⟩) (fun y : {x // q x = q x0} => f y.1), tsum_fintype]
      exact Finset.sum_coe_sort C (fun δ => f (QuotientGroup.mk δ))
    rw [hT, hT, Finset.sum_congr rfl hFv, Finset.sum_congr rfl hGv, ← Finset.smul_sum, ← Finset.smul_sum,
      hH (r x0) C (hr_fix x0) hC γ, mul_smul_comm]
  let eσ := Equiv.sigmaFiberEquiv q
  have hFs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, F y.1) (∑' x, F x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hF.hasSum) (fun b => (hF.comp_injective Subtype.val_injective).hasSum)
  have hGs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, G y.1) (∑' x, G x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hG.hasSum) (fun b => (hG.comp_injective Subtype.val_injective).hasSum)
  have hGm := hGs.mul_left (B γ)
  rw [← funext hfib] at hGm
  have := hFs.unique hGm
  show HasSum F _
  rw [← this]
  exact hF.hasSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
section
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

open Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.ProdIrr

theorem exists_mem_ind_apply_one {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (hG : ∀ N ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g ∈ K, g ∈ N)
    (P : Subgroup G) (σ : Representation ℂ P W) (hσ : IsSmooth σ) (u : W) :
    ∃ f : smoothPart (ind P σ), f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ p, f.1.1 g = σ p u := by
  classical
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))
  obtain ⟨K, hKo, hKN⟩ := hG N (by simpa using hN)
  have hfix : ∀ p : P, (p : G) ∈ K → σ p u = u := fun p hp => hNS (hKN _ hp)
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩,
    ?_, ?_⟩
  · apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  · show F 1 = u
    have := hF 1 1 K.one_mem
    simpa using this
  · intro g
    show F g = 0 ∨ ∃ p, F g = σ p u
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg; exact Or.inr ⟨p, hF _ _ hc⟩
    · exact Or.inl (hF0 _ hg)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem continuous_leviProj (e : (Σ a, m a) ≃ n) : Continuous (leviProj k e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, leviProj_apply]
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have : (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) =
        fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k) := by
      funext p; rw [map_inv]; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [leviProj_apply]
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _

theorem exists_openSubgroup_GL :
    ∀ N ∈ 𝓝 (1 : GL n k), ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ ∀ g ∈ K, g ∈ N := by
  intro N hN
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset hN
  exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩

theorem exists_indSp_apply_one {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (hρ : IsSmooth ρ) (u : W) :
    ∃ f : IndSp e ρ, f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ l : Levi k m, ∃ c : ℂ, f.1.1 g = c • ρ l u := by
  obtain ⟨f, h1, h2⟩ := exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u
  exact ⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩

end Local

end GlobalTheory.SmGL.ProdIrr

namespace GlobalTheory.SmGL.ProdIrr

theorem isIrreducible_of_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  intro k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩
  classical
  have hI : (prod₂ σ₀ τ).IsIrreducible := (MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi
  obtain ⟨hV, -⟩ := (isIrreducible_iff σ₀).1 hσi
  obtain ⟨hX, hIirr⟩ := (isIrreducible_iff _).1 hI
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
  let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
  have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
  let ρ' := (extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hσs hτs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have h0 : ∀ z : V ⊗[ℂ] W, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))
  rw [isIrreducible_iff]
  refine ⟨hW, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
  have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
    rintro l _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
      exact ⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
        ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have hLR : ∀ y ∈ R, L y ∈ S := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
    { carrier := {f | ∀ g, f.1.1 g ∈ R}
      add_mem' := fun ha hb g => add_mem (ha g) (hb g)
      zero_mem' := fun g => zero_mem R
      smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
  have hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y := fun g f hf x => hf (x * g)
  have hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u := by
    intro u hu
    obtain ⟨f, h1, h2⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
    refine ⟨f, fun g => ?_, h1⟩
    rcases h2 g with h | ⟨l, c, h⟩
    · rw [h]; exact zero_mem R
    · rw [h]; exact R.smul_mem c (hR l u hu)
  have hYtop : Y = ⊤ := by
    refine (hIirr Y hYs).resolve_left fun hY => ?_
    obtain ⟨f, hf, h1⟩ := hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩
    rw [hY, Submodule.mem_bot] at hf
    have : L (x₀ ⊗ₜ s) = 0 := by rw [← h1, hf]; rfl
    rw [hL] at this
    exact smul_ne_zero hφ hs0 this
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, h1, -⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)
  have hf : f ∈ Y := hYtop ▸ Submodule.mem_top
  have h2 := hLR _ (h1 ▸ hf 1)
  rw [hL] at h2
  exact (S.smul_mem_iff hφ).1 h2

end GlobalTheory.SmGL.ProdIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SumProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem sum_fst_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors hx).symm.trans hd

theorem exists_isLSeg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π)
    {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨_, x, -, ⟨D, ⟨rfl, -⟩, hD⟩, -⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hΔ
  exact ⟨x a, hD a⟩

theorem exists_isL [CharZero k] (hS : StandardCosocleGL) {𝔪 : Multiset (Segment k)}
    (h : ∀ Δ ∈ 𝔪, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep) (hN : (𝔪.map Segment.deg).sum = N) :
    ∃ π : IrrRep (GL (Fin N) k), IsL 𝔪 π.ρ := by
  obtain ⟨D, hD⟩ := exists_isOrderedForm 𝔪
  have hm : ∀ i, D i ∈ 𝔪 := fun i => hD.1 ▸ Multiset.mem_map_of_mem D (Finset.mem_univ i)
  choose x hx using fun i => h _ (hm i)
  have hF : LFactors 𝔪 x := ⟨D, hD, hx⟩
  have hd : ∑ a, (x a).1 = N := (sum_fst_of_lFactors hF).trans hN
  obtain ⟨π, hπ⟩ := hS k 𝔪 _ _ x hd hF
  exact ⟨π, _, x, hd, hF, hπ⟩

theorem isL_add_of_equiv_prod₂ : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  rintro hM hS k _ _ _ _ _ r t σ τ π 𝔪 𝔫 h1 h2 ⟨e⟩
  obtain ⟨y, hy⟩ := exists_isL (N := r + t) hS (𝔪 := 𝔪 + 𝔫)
    (fun Δ hΔ => (Multiset.mem_add.1 hΔ).elim (exists_isLSeg_of_isL h1) (exists_isLSeg_of_isL h2))
    (by rw [Multiset.map_add (f := _), Multiset.sum_add, deg_of_isL h1, deg_of_isL h2])
  have hd : ∑ a, (![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ.ρ σ.smooth σ.irr τ.ρ τ.smooth τ.irr hd
  have ψ := IrrGL.equivOf y.ρ y.smooth y.irr
  have a1 : IsL 𝔪 (IrrGL.of σ.ρ σ.smooth σ.irr).rep := h1.of_equiv (IrrGL.equivOf _ _ _)
  have a2 : IsL 𝔫 (IrrGL.of τ.ρ τ.smooth τ.irr).rep := h2.of_equiv (IrrGL.equivOf _ _ _)
  have a3 : IsL (𝔪 + 𝔫) (IrrGL.of y.ρ y.smooth y.irr).rep := hy.of_equiv ψ
  have hs := (hM k).2 𝔪 𝔫 ![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr]
    (IrrGL.of y.ρ y.smooth y.irr) hd a1 a2 a3
  have E := (e.trans φ).symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)) (IrrRep.irr _) π.irr
  exact a3.of_equiv θ.symm

end GlobalTheory.LocGL.SumProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerCharacterFactorsAbsoluteGaloisAbelianization
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.KummerAb

theorem kummer_char_eq_of_toAb_eq : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  intro E' Ω _ _ _ _ _ m hm ζ hζ c hc y hy σ τ he
  have hc' : algebraMap E' Ω c ≠ 0 := (map_ne_zero_iff _ (algebraMap E' Ω).injective).mpr hc
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact hc' hy.symm
  haveI : NeZero m := ⟨hm.ne'⟩
  have hζ' : IsPrimitiveRoot (algebraMap E' Ω ζ) m := hζ.map_of_injective (algebraMap E' Ω).injective
  have key : ∀ ρ : G E' Ω, ∃ e : E', ρ y = algebraMap E' Ω e * y := by
    intro ρ
    have h1 : (ρ y / y) ^ m = 1 := by
      rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    refine ⟨ζ ^ i, ?_⟩
    rw [map_pow, hi, div_mul_cancel₀ _ hy0]
  let φ : G E' Ω →* Ωˣ := MonoidHom.mk' (fun ρ => Units.mk0 (ρ y / y)
      (div_ne_zero ((map_ne_zero_iff _ ρ.injective).mpr hy0) hy0)) (by
    intro a b
    ext
    obtain ⟨e, he⟩ := key b
    simp only [Units.val_mul, Units.val_mk0, AlgEquiv.mul_apply, he, map_mul, AlgEquiv.commutes]
    field_simp)
  have hφ : ∀ ρ, (φ ρ : Ω) = ρ y / y := fun ρ => rfl
  have hint : IsIntegral E' y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E' (IntermediateField.adjoin E' {y}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen (φ.ker : Set (G E' Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin E' {y}).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)
    intro ρ hρ
    have : ρ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ y
      (IntermediateField.subset_adjoin E' {y} rfl)
    rw [MonoidHom.mem_ker]
    ext
    rw [hφ, this, div_self hy0, Units.val_one]
  have hclosed : IsClosed (φ.ker : Set (G E' Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  have hle : (commutator (G E' Ω)).topologicalClosure ≤ φ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ) hclosed
  have hmem : σ⁻¹ * τ ∈ (commutator (G E' Ω)).topologicalClosure := QuotientGroup.eq.mp he
  have h2 := hle hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← hφ, ← hφ, h2]

end GlobalTheory.KummerAb
end

