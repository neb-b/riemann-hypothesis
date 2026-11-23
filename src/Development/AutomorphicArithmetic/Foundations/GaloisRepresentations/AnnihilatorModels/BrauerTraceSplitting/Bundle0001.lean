module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0011
public import GroundTheory.PAdicHodge.BdRAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AnnDrop
section
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison.Br

theorem annDrop : AnnDrop := by
  intro F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx
  rw [mem_Dinv] at hx
  have hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b) := by
    intro m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact hφ _
  let Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C := TensorProduct.congr i.symm e.toLinearEquiv
  have hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C),
      (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) →
      ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z) := by
    intro a a' b b' ha hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v y =>
      simp only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]
      rw [ha v]
      congr 1
      exact hb y
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x := by
    intro g
    rw [← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]
    intro v
    have h := hρ g (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have hsum := hrel (Φ x) hinv
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N))) := by
    have h0 : Function.Injective (ψ.toLinearMap ^ (f * N)) := by
      rw [Module.End.coe_pow]
      exact Function.Injective.iterate hψ _
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0
  have hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) •
      TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0 := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp,
      ← pow_add]
    congr 3
    ring
  apply Φ.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum, Finset.sum_range, ← hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]
  · intro v
    have h := hT j (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · intro y
    rw [← pow_mul]
    exact hpow _ y

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AwayEq
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem cp_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem ainf_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (cp_eq σ τ h) _ _

private theorem away_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, ainf_eq σ τ h])

private theorem cris_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, away_eq σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

theorem actEq : ActEq := by
  intro l _
  refine ⟨fun K g x => ?_, fun z => ?_⟩
  · exact RingHom.congr_fun (cris_eq _ _ fun _ => rfl) x
  · have h : (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp ((Formalism.Per6.ainfMap l).comp (Formalism.Per6.zA l)) = zA l :=
      ringHom_ext_padicInt _ _
    exact congrArg (Formalism.Per6.cB l) (RingHom.congr_fun h z)

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.LocFacts
section
open Formalism.Per6 in
private theorem exists_finset_adjoin_laurent_preimage {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (x : Loc2 a t) : ∃ (k : ℕ) (y : A), Loc2.mk₀ a t t ^ k * x = Loc2.mk₀ a t y := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj
    (algebraMap A (Localization.Away a) t) (S := Localization.Away (algebraMap A (Localization.Away a) t)) x
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj a (S := Localization.Away a) b
  have hb' : x * Loc2.mk₀ a t t ^ n = Loc2.mk₁ a t b := hb
  have hy' : Loc2.mk₁ a t b * Loc2.mk₀ a t a ^ m = Loc2.mk₀ a t y := by
    have := congrArg (Loc2.mk₁ a t) hy
    simpa [Loc2.mk₀] using this
  refine ⟨r * m + n, y * c ^ m, ?_⟩
  have hT : Loc2.mk₀ a t t ^ r = Loc2.mk₀ a t a * Loc2.mk₀ a t c := by
    rw [← map_pow, hc, map_mul]
  rw [map_mul, map_pow, ← hy', ← hb', pow_add, pow_mul, hT, mul_pow]
  ring

open Formalism.Per6 in
private theorem exists_pow_kill_of_localization_zero {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (y : A) (hy : Loc2.mk₀ a t y = 0) : ∃ k : ℕ, t ^ k * y = 0 := by
  have h1 : algebraMap (Localization.Away a) (Localization.Away (algebraMap A (Localization.Away a) t))
      (algebraMap A (Localization.Away a) y) = 0 := hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A (Localization.Away a) t)) _ _).1 h1
  have h2 : algebraMap A (Localization.Away a) (t ^ k * y) = 0 := by
    simpa [map_mul, map_pow] using hk
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 h2
  refine ⟨r * m + k, ?_⟩
  have hm' : a ^ m * (t ^ k * y) = 0 := hm
  calc t ^ (r * m + k) * y = c ^ m * (a ^ m * (t ^ k * y)) := by
        rw [pow_add, pow_mul, hc, mul_pow]; ring
    _ = 0 := by rw [hm', mul_zero]

theorem UpperTheory.Gal.crystallineComparison.Br.locFacts :
    UpperTheory.Gal.crystallineComparison.Br.LocFacts := by
  intro A _ a t ⟨r, c, hc⟩
  exact ⟨exists_finset_adjoin_laurent_preimage a t c r hc, exists_pow_kill_of_localization_zero a t c r hc⟩
end

