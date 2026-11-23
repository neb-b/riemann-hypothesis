module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepPatchTwist
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem exists_hom_patch_of_agree {Γ G : Type*} [Group Γ] [Group G] (a b : Γ →* G)
    (η₀ η : Γ →* ℤˣ) (s : Γ) (h0 : η₀ s = 1) (h1 : η s = -1)
    (hab : ∀ g, η₀ g = 1 → η g = 1 → b g = a g)
    (hc : ∀ y : G, (∀ g, η₀ g = 1 → η g = 1 → a g * y = y * a g) → a s * y = y * a s) :
    ∃ ρ : Γ →* G, (∀ g, η₀ g = 1 → ρ g = a g) ∧ ∀ g, η g = 1 → ρ g = b g := by
  classical
  by_cases ht : ∃ t, η₀ t = -1 ∧ η t = 1
  swap
  · refine ⟨a, fun g _ => rfl, fun g hg => ?_⟩
    rcases Int.units_eq_one_or (η₀ g) with h | h
    · exact (hab g h hg).symm
    · exact absurd ⟨g, h, hg⟩ ht
  obtain ⟨t, ht0, ht1⟩ := ht
  set z := (a t)⁻¹ * b t with hz
  have hzK : ∀ g, η₀ g = 1 → η g = 1 → a g * z = z * a g := by
    intro g hg0 hg1
    have e : b (t * g * t⁻¹) = a (t * g * t⁻¹) :=
      hab _ (by simp only [map_mul, map_inv, hg0, mul_one, mul_inv_cancel])
        (by simp only [map_mul, map_inv, hg1, mul_one, mul_inv_cancel])
    simp only [map_mul, map_inv, hab g hg0 hg1] at e
    rw [hz]
    calc a g * ((a t)⁻¹ * b t) = (a t)⁻¹ * (a t * a g * (a t)⁻¹) * b t := by group
      _ = (a t)⁻¹ * (b t * a g * (b t)⁻¹) * b t := by rw [e]
      _ = (a t)⁻¹ * b t * a g := by group
  have hzs : a s * z = z * a s := hc z hzK
  have hzH0 : ∀ g, η₀ g = 1 → a g * z = z * a g := by
    intro g hg0
    rcases Int.units_eq_one_or (η g) with hg1 | hg1
    · exact hzK g hg0 hg1
    · have hk0 : η₀ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0, hg0]; decide
      have hk1 : η (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, h1, hg1]; decide
      have hk := hzK _ hk0 hk1
      have hg : a g = a s * a (s⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      rw [hg, mul_assoc, hk, ← mul_assoc, hzs, mul_assoc]
  have hzz : ∀ g, η₀ g = -1 → z * a g * z = a g := by
    intro g hg0
    have hm : η₀ (t⁻¹ * g) = 1 := by rw [map_mul, map_inv, ht0, hg0]; decide
    have hg : a g = a t * a (t⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
    have ht2 : b (t * t) = a (t * t) :=
      hab _ (by rw [map_mul, ht0]; decide) (by rw [map_mul, ht1]; decide)
    rw [map_mul, map_mul] at ht2
    rw [hg]
    calc z * (a t * a (t⁻¹ * g)) * z = z * a t * (a (t⁻¹ * g) * z) := by group
      _ = z * a t * (z * a (t⁻¹ * g)) := by rw [hzH0 _ hm]
      _ = (a t)⁻¹ * (b t * b t) * a (t⁻¹ * g) := by rw [hz]; group
      _ = a t * a (t⁻¹ * g) := by rw [ht2]; group
  have hn : ∀ u : ℤˣ, u = -1 → ¬ u = 1 := by rintro u rfl; decide
  refine ⟨MonoidHom.mk' (fun g => if η₀ g = 1 then a g else a g * z) ?_, ?_, ?_⟩
  · intro g g'
    rcases Int.units_eq_one_or (η₀ g) with h | h <;> rcases Int.units_eq_one_or (η₀ g') with h' | h'
    · rw [if_pos (by rw [map_mul, h, h']; decide), if_pos h, if_pos h', map_mul]
    · rw [if_neg (hn _ (by rw [map_mul, h, h']; decide)), if_pos h, if_neg (hn _ h'), map_mul, mul_assoc]
    · rw [if_neg (hn _ (by rw [map_mul, h, h']; decide)), if_neg (hn _ h), if_pos h', map_mul,
        mul_assoc, mul_assoc, hzH0 g' h']
    · rw [if_pos (by rw [map_mul, h, h']; decide), if_neg (hn _ h), if_neg (hn _ h'), map_mul,
        mul_assoc, ← mul_assoc z, hzz g' h']
  · intro g hg
    rw [MonoidHom.mk'_apply, if_pos hg]
  · intro g hg
    rw [MonoidHom.mk'_apply]
    rcases Int.units_eq_one_or (η₀ g) with h | h
    · rw [if_pos h, hab g h hg]
    · rw [if_neg (hn _ h)]
      have hk : b (g * t⁻¹) = a (g * t⁻¹) :=
        hab _ (by rw [map_mul, map_inv, h, ht0]; decide) (by rw [map_mul, map_inv, hg, ht1]; decide)
      simp only [map_mul, map_inv] at hk
      rw [hz]
      calc a g * ((a t)⁻¹ * b t) = a g * (a t)⁻¹ * b t := by group
        _ = b g * (b t)⁻¹ * b t := by rw [hk]
        _ = b g := by group

theorem exists_rep_patch_twist : ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (ρ₀ ρ' : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (P : GL (Fin n) k) (s : Γ), η₀ s = 1 → η s = -1 → (∀ g, η₀ g = 1 → η g = 1 → ρ' g = P⁻¹ * ρ₀ g * P) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ ∀ g, η g = 1 → ρ g = P * ρ' g * P⁻¹ := by
  intro Γ k _ _ n ρ₀ ρ' η₀ η P s hs0 hs1 hagree hcomm
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_hom_patch_of_agree ρ₀ ((MulAut.conj P).toMonoidHom.comp ρ') η₀ η s hs0 hs1
    (fun g h0 h1 => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hagree g h0 h1]
      group)
    (fun y hy => by
      apply Units.ext
      simp only [Units.val_mul]
      apply hcomm
      intro g h0 h1
      simpa only [Units.val_mul] using congrArg Units.val (hy g h0 h1))
  refine ⟨ρ, hρ0, fun g hg => ?_⟩
  rw [hρ1 g hg]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuadraticCharactersInAdjoint
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem linearIndependent_conj_eigenmatrices {Γ k ι : Type} [Group Γ] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (ψ : ι → Γ →* k) (hψ : Function.Injective ψ)
    (X : ι → Matrix (Fin n) (Fin n) k) (hX : ∀ i, X i ≠ 0)
    (h : ∀ i g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X i =
      ψ i g • (X i * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    LinearIndependent k X := by
  have hli : LinearIndependent k (fun i => (ψ i : Γ → k)) :=
    (linearIndependent_monoidHom Γ k).comp ψ hψ
  rw [linearIndependent_iff'] at hli ⊢
  intro s c hc i hi
  have key : ∀ g, ∑ j ∈ s, (c j * ψ j g) • X j = 0 := by
    intro g
    have h1 : (∑ j ∈ s, (c j * ψ j g) • X j) *
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      have h2 : ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (∑ j ∈ s, c j • X j) = 0 := by
        rw [hc, Matrix.mul_zero]
      rw [← h2, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, h, smul_smul, smul_mul_assoc]
    exact (Units.mul_left_eq_zero (r g)).1 h1
  by_contra hci
  apply hX i
  ext a b
  have h3 := hli s (fun j => c j * X j a b) (by
    funext g
    have h4 := congrFun (congrFun (key g) a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun j _ => by ring) i hi
  simpa [hci] using h3

theorem finite_quadratic_characters_in_adjoint :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k),
      Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  intro Γ k _ _ _ n r
  set S := {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} with hS
  have hex : ∀ χ : S, ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ.1 g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :=
    fun χ => χ.2
  choose X hX h using hex
  let ψ : S → Γ →* k := fun χ =>
    ((Int.castRingHom k).toMonoidHom.comp (Units.coeHom ℤ)).comp χ.1
  have hψ : Function.Injective ψ := by
    intro χ₁ χ₂ e
    apply Subtype.ext
    ext g
    have h1 : ((χ₁.1 g : ℤ) : k) = ((χ₂.1 g : ℤ) : k) := DFunLike.congr_fun e g
    exact_mod_cast h1
  have hli := linearIndependent_conj_eigenmatrices r ψ hψ X hX h
  have : Finite S := hli.finite_of_isNoetherian
  exact Set.toFinite S

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSSRepOfFiniteIndex
section
open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.FiniteIndexSemisimple

theorem isSSRep_of_finiteIndex {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (N : Subgroup Γ) [N.FiniteIndex] (h : IsSSRep (r.comp N.subtype)) : IsSSRep r := by
  classical
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W (fun g v hv => hW g v hv)
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin
  have hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v; simp [ρ, Matrix.mulVec_mulVec, map_mul]
  have hρ1 : ∀ v, ρ 1 v = v := by intro v; simp [ρ]
  have hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g v hv
  let p : (Fin n → k) →ₗ[k] (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (W.linearProjOfIsCompl W' hc v).2
  have hpl : ∀ w ∈ W, p w = w := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    exact e
  have hpr : ∀ w ∈ W', p w = 0 := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    exact e
  have hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v) := by
    intro m hm v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hb' : ρ m b ∈ W' := hW' ⟨m, hm⟩ b hb
    rw [show p (a + b) = a by rw [map_add (f := _), hpl a ha, hpr b hb, add_zero], map_add (f := _), map_add (f := _), hpl _ (hWρ m a ha),
      hpr _ hb', add_zero]
  let T : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹
  have hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g := by
    intro g m hm; refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply]
    rw [mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]
  have hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v) := by
    intro h g v
    simp only [T, LinearMap.comp_apply]
    rw [hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]
  have hTW : ∀ g v, T g v ∈ W := fun g v => hWρ g _ (hpW _)
  have hTfix : ∀ g, ∀ w ∈ W, T g w = w := by
    intro g w hw
    simp only [T, LinearMap.comp_apply]
    rw [hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  let S : (Fin n → k) →ₗ[k] (Fin n → k) := ∑ q : Γ ⧸ N, T q.out
  have hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out) := by
    intro h q
    have e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hm : (h * q.out)⁻¹ * (h • q).out ∈ N := QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)
    rw [← hTN (h * q.out) _ hm, mul_inv_cancel_left]
  have hS : ∀ h v, ρ h (S v) = S (ρ h v) := by
    intro h v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S, LinearMap.sum_apply, map_sum, hTc h]
    rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hout]
  set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • S
  have hPW : ∀ v, P v ∈ W := fun v => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)
  have hPfix : ∀ w ∈ W, P w = w := fun w hw => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hP : ∀ h v, ρ h (P v) = P (ρ h v) := fun h v => by
    simp only [P, LinearMap.smul_apply, map_smul, hS]
  refine ⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩
  · show P (ρ g v) = 0
    rw [← hP, LinearMap.mem_ker.mp hv, map_zero]
  · refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩
    · rw [← hPfix v hv]; exact hv'
    · have : v = P v + (v - P v) := by abel
      rw [this]
      refine Submodule.add_mem_sup (hPW v) ?_
      rw [LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]

end GlobalTheory.FiniteIndexSemisimple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
section
open Finset Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.Lin


open Finset in
theorem _root_.GlobalTheory.Lin.primesAPInterval_of_primesRel (h : _root_.GlobalTheory.Lin.PrimesRel) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ _root_.Formalism.HermitianLattices.GL2PrimeSums.PrimesAPInterval C₀ Cr cr c := by
  unfold _root_.GlobalTheory.Lin.PrimesRel at h
  obtain ⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁8, hc₂, hc₃, hCA, hcS, hmain⟩ := h
  set cr := min c₃ (Real.sqrt c₃) with hcr
  have hcr0 : 0 < cr := lt_min hc₃ (Real.sqrt_pos.mpr hc₃)
  have hdata : _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions c₂ CA cr cS := by
    unfold _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions
    intro m a hm ha
    haveI : NeZero m := ⟨by omega⟩
    obtain ⟨huniq, hgap, hcount⟩ := hmain m hm
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hlogm : 0 < Real.log m := Real.log_pos hm1
    have hlog4m : Real.log m ≤ Real.log (4 * m) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog3 : 1 < Real.log m := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith [Real.exp_one_lt_d9]

    have hterm : ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cS / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
        _root_.GlobalTheory.Lin.ExcData c₁ m a θ β := by
      by_cases hex : ∃ (χ : DirichletCharacter ℂ m) (β : ℝ), _root_.GlobalTheory.Lin.IsExc c₁ χ β
      · obtain ⟨χ, β, hχ⟩ := hex
        have hunit : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr ha
        have hsq : χ (a : ZMod m) ^ 2 = 1 := by
          rw [← MulChar.pow_apply' χ (by norm_num), hχ.1, MulChar.one_apply hunit]
        obtain ⟨θ, hθ, hθmem⟩ : ∃ θ : ℤ, χ (a : ZMod m) = θ ∧ θ ∈ ({-1, 0, 1} : Set ℤ) := by
          have hsq' : χ (a : ZMod m) * χ (a : ZMod m) = 1 := by rw [← pow_two]; exact hsq
          rcases mul_self_eq_one_iff.mp hsq' with h1 | h1
          · exact ⟨1, by simp [h1], by simp⟩
          · exact ⟨-1, by simp [h1], by simp⟩
        refine ⟨θ, β, hθmem, fun _ => ⟨?_, hχ.2.2.1, ?_⟩, Or.inr ⟨χ, hχ, hθ⟩⟩
        · have h1 := hχ.2.1
          have : c₁ / Real.log m ≤ 1 / 2 := by
            rw [div_le_iff₀ hlogm]
            linarith
          linarith
        · refine le_trans ?_ (hgap χ β hχ)
          apply div_le_div_of_nonneg_left hcS.le (by positivity)
          have : (m : ℝ) ^ 2 ≤ (4 * m) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            linarith
          exact mul_le_mul this hlog4m hlogm.le (by positivity)
      · refine ⟨0, 1 / 2, by simp, fun h0 => absurd rfl h0, Or.inl ⟨rfl, fun χ β hχ => hex ⟨χ, β, hχ⟩⟩⟩
    obtain ⟨θ, β, hθmem, hβ, hdat⟩ := hterm
    refine ⟨θ, β, fun _ => 0, hθmem, hβ,
      fun _ => ⟨le_rfl, mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))⟩, ?_⟩
    intro Y hY
    have hY1 : (m : ℝ) ^ c₂ ≤ Y := by
      refine le_trans ?_ hY
      exact Real.rpow_le_rpow (by positivity) (by linarith) hc₂.le
    have hb := hcount a θ β ha hdat Y hY1
    have hY1' : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY1
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1'
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log m) +
        Real.exp (-√(c₃ * Real.log Y))) := by
      positivity
    have hE : 0 ≤ _root_.Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y :=
      (mul_nonneg_iff_of_pos_left hpos).mp ((abs_nonneg _).trans hb)
    have h1 : Real.exp (-c₃ * Real.log Y / Real.log m) ≤
        Real.exp (-cr * Real.log Y / Real.log (4 * m)) := by
      rw [Real.exp_le_exp, neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
        hlogm hlog4m
    have h2 : Real.exp (-√(c₃ * Real.log Y)) ≤ Real.exp (-cr * √(Real.log Y)) := by
      rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, Real.sqrt_mul hc₃.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
    simp only [add_zero]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    unfold _root_.Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCA.le) (mul_le_mul_of_nonneg_left h2 hCA.le)
  obtain ⟨C₀', c, hC₀', hc, hint⟩ := _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA cr cS hc₂ hCA hcr0 hcS hdata
  exact ⟨C₀', CA, cr, c, hC₀', hCA, hcr0, hc, hint⟩

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement
section
namespace GlobalTheory.ThetaWeberObj

theorem thetaWeberStatement : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeberStatement :=
  GlobalTheory.ThetaWeberRoad.thetaWeberStatement_of Formalism.L2.Th1.F.thetaLine Formalism.L2.Th1.F.sgStarBasic
    Formalism.L2.Th1.F.sgStarAdd

end GlobalTheory.ThetaWeberObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernel
section
open Formalism.MainNotions.N

namespace GlobalTheory

private theorem exists_intertwiner_decomp_of_kernel_intertwines {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (P Q : Γ → Matrix (Fin n) (Fin n) k) (hP : ∀ a b, P (a * b) = P a * P b)
    (hQ : ∀ a b, Q (a * b) = Q a * Q b) (c : Γ → k) (hc : ∀ a b, c (a * b) = c a * c b)
    (hcc : ∀ a, c a * c a = 1) (S : Subgroup Γ) (η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k)
    (hX : ∀ g ∈ S, η g = 1 → P g * X = c g • (X * Q g)) :
    ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, P g * X₁ = c g • (X₁ * Q g)) ∧
      (∀ g ∈ S, P g * X₂ = (c g * ((η g : ℤ) : k)) • (X₂ * Q g)) := by
  by_cases h : ∀ s ∈ S, η s = 1
  · refine ⟨X, 0, by simp, fun g hg => hX g hg (h g hg), fun g _ => by simp⟩
  push Not at h
  obtain ⟨s, hs, hs1⟩ := h
  have hsm : η s = -1 := (Int.units_eq_one_or _).resolve_left hs1
  have hc1 : c 1 = 1 := by
    have h := hc 1 1
    rw [one_mul] at h
    rw [h]
    exact hcc 1
  have hcinv : ∀ a, c a⁻¹ = c a := by
    intro a
    calc c a⁻¹ = c a⁻¹ * (c a * c a) := by rw [hcc, mul_one]
      _ = c (a⁻¹ * a) * c a := by rw [hc]; ring
      _ = c a := by rw [inv_mul_cancel, hc1, one_mul]
  have hX' : ∀ t ∈ S, η t = 1 → ∀ M, P t * (X * M) = c t • (X * (Q t * M)) := by
    intro t ht het M
    rw [← Matrix.mul_assoc, hX t ht het, Matrix.smul_mul, Matrix.mul_assoc]
  set Y := c s • (P s * X * Q s⁻¹) with hY
  have key1 : ∀ g ∈ S, η g = 1 → P g * Y = c g • (Y * Q g) := by
    intro g hg he
    have ht : s⁻¹ * g * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hg) hs
    have het : η (s⁻¹ * g * s) = 1 := by simp [he]
    have hPgs : ∀ M, P g * (P s * M) = P s * (P (s⁻¹ * g * s) * M) := by
      intro M
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hP, ← hP]
      congr 2
      group
    have hQt : Q (s⁻¹ * g * s) * Q s⁻¹ = Q s⁻¹ * Q g := by
      rw [← hQ, ← hQ]
      congr 1
      group
    have hct : c (s⁻¹ * g * s) = c g := by
      rw [hc, hc, hcinv]
      calc c s * c g * c s = c g * (c s * c s) := by ring
        _ = c g := by rw [hcc, mul_one]
    simp only [hY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hPgs, hX' _ ht het, hQt, hct,
      smul_smul, mul_comm]
  have key2 : ∀ g ∈ S, η g = -1 → P g * X = c g • (Y * Q g) ∧ P g * Y = c g • (X * Q g) := by
    intro g hg he
    have hu : s⁻¹ * g ∈ S := S.mul_mem (S.inv_mem hs) hg
    have heu : η (s⁻¹ * g) = 1 := by simp [he, hsm]
    have hv : g * s ∈ S := S.mul_mem hg hs
    have hev : η (g * s) = 1 := by simp [he, hsm]
    constructor
    · have hPg : P g = P s * P (s⁻¹ * g) := by
        rw [← hP]
        congr 1
        group
      have hQu : Q (s⁻¹ * g) = Q s⁻¹ * Q g := by
        rw [← hQ]
      have hcu : c (s⁻¹ * g) = c s * c g := by rw [hc, hcinv]
      have e1 : P g * X = P s * (P (s⁻¹ * g) * (X * 1)) := by
        rw [hPg, Matrix.mul_one, Matrix.mul_assoc]
      rw [e1, hX' _ hu heu, Matrix.mul_one, hQu, hcu]
      simp only [hY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul, mul_comm]
    · have hPv : ∀ M, P g * (P s * M) = P (g * s) * M := by
        intro M
        rw [← Matrix.mul_assoc, ← hP]
      have hQv : Q (g * s) * Q s⁻¹ = Q g := by
        rw [← hQ]
        congr 1
        group
      have hcv : c (g * s) = c g * c s := hc g s
      simp only [hY, Matrix.mul_smul, Matrix.mul_assoc, hPv, hX' _ hv hev, hQv, hcv,
        smul_smul]
      congr 1
      calc c s * (c g * c s) = c g * (c s * c s) := by ring
        _ = c g := by rw [hcc, mul_one]
  refine ⟨(2 : k)⁻¹ • (X + Y), (2 : k)⁻¹ • (X - Y), by module, ?_, ?_⟩
  · intro g hg
    rcases Int.units_eq_one_or (η g) with he | he
    · simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, Matrix.add_mul, hX g hg he, key1 g hg he]
      module
    · obtain ⟨a1, a2⟩ := key2 g hg he
      simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, Matrix.add_mul, a1, a2]
      module
  · intro g hg
    rcases Int.units_eq_one_or (η g) with he | he
    · simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, hX g hg he, key1 g hg he,
        he, Units.val_one, Int.cast_one, mul_one]
      module
    · obtain ⟨a1, a2⟩ := key2 g hg he
      simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, a1, a2, he, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
      module

theorem twistedIntertwiner_decomp_of_quadraticKernel :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (σ σ' : Γ →* GL (Fin n) k) (S : Subgroup Γ) (χ η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k), (∀ g ∈ S, η g = 1 → ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₁ = ((χ g : ℤ) : k) • (X₁ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₂ = (((χ * η) g : ℤ) : k) • (X₂ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) := by
  intro Γ k _ _ _ n σ σ' S χ η X hX
  obtain ⟨X₁, X₂, hsum, h₁, h₂⟩ := exists_intertwiner_decomp_of_kernel_intertwines (fun g => ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (fun g => ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (fun a b => by simp [map_mul])
    (fun a b => by simp [map_mul]) (fun g => ((χ g : ℤ) : k)) (fun a b => by simp [map_mul])
    (fun a => by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp) S η X hX
  refine ⟨X₁, X₂, hsum, h₁, fun g hg => ?_⟩
  rw [h₂ g hg]
  simp [MonoidHom.mul_apply, Units.val_mul, Int.cast_mul]

end GlobalTheory
end

