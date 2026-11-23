module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := _root_.GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_fin_mul_inf (y : UA E n) : ∃ a ∈ finU (E := E) (n := n), ∃ b ∈ infU E n, y = a * b := by
  let yi := GeneralLinearGroup.map (pInf E) y.1
  have hyi : yi.valᴴ * yi.val = 1 := by
    have hy : cT (conjAd E) y.1.val * 1 * y.1.val = 1 := y.2
    have h3 : (cT (conjAd E) y.1.val).map (pInf E) = yi.valᴴ := by
      ext1 i j
      rw [Matrix.conjTranspose_apply]
      exact (infEq E).symm_apply_apply _
    have h := congrArg (pInf E).mapMatrix hy
    rw [map_mul, map_mul, map_one, mul_one, RingHom.mapMatrix_apply, h3] at h
    exact h
  let b : UA E n := ⟨infGL E n yi, infGL_mem_UA yi hyi⟩
  have hb : b ∈ infU E n := MonoidHom.mem_ker.2 (pFin_infGL yi)
  have ha : b⁻¹ * y ∈ finU (E := E) (n := n) := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv]
    have : cInf b = cInf y := pInf_infGL yi
    rw [this, inv_mul_cancel]
  refine ⟨b⁻¹ * y, ha, b, hb, ?_⟩
  rw [fin_mul_inf ha hb, mul_inv_cancel_left]

def X (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_X (φ : UA E n → ℂ) (x : infU E n) {ξ : UA E n → ℂ} (h : ξ ∈ X φ) : RU E n x ξ ∈ X φ := by
  have : X φ ≤ (X φ).comap (RU E n x) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨x * k, (RU_RU _ _ _).symm⟩)
  exact this h

theorem self_mem_X (φ : UA E n → ℂ) : φ ∈ X φ :=
  Submodule.subset_span ⟨1, by show RU E n 1 φ = φ; rw [map_one]; rfl⟩

def rhoX (φ : UA E n → ℂ) (x : infU E n) : Module.End ℂ (X φ) :=
  (RU E n x).restrict fun _ h => RU_mem_X φ x h

theorem rhoX_mul (φ : UA E n → ℂ) (x y : infU E n) : rhoX φ (x * y) = rhoX φ x * rhoX φ y :=
  LinearMap.ext fun ξ => Subtype.ext (RU_RU (x : UA E n) y ξ.1).symm

def coef (φ : UA E n → ℂ) : Module.Dual ℂ (Module.End ℂ (X φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (rhoX φ x)

def C (φ : UA E n → ℂ) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef φ)

theorem mem_C (φ : UA E n → ℂ) (f : X φ →ₗ[ℂ] ℂ) (ξ : X φ) : (fun x : infU E n => f (rhoX φ x ξ)) ∈ C φ :=
  ⟨f ∘ₗ LinearMap.applyₗ ξ, rfl⟩

theorem C_right (φ : UA E n → ℂ) {c : infU E n → ℂ} (hc : c ∈ C φ) (y : infU E n) :
    (fun x => c (x * y)) ∈ C φ := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (rhoX φ y), funext fun x => ?_⟩
  change B (rhoX φ x * rhoX φ y) = B (rhoX φ (x * y))
  rw [rhoX_mul]

def Y (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C φ).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {φ ψ : UA E n → ℂ} : ψ ∈ Y φ ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C φ := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : AutSub E n) {φ : UA E n → ℂ} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) : π.V ≤ Y φ := by
  have hφY : φ ∈ Y φ := mem_Y.2 fun g =>
    mem_C φ ((LinearMap.proj g) ∘ₗ (X φ).subtype) ⟨φ, self_mem_X φ⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y φ, RU E n x ψ ∈ π.V ⊓ Y φ := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) = fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g, ← fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right φ (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y φ) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hφ, hφY⟩ : φ ∈ π.V ⊓ Y φ))) h0
  · rw [← h]
    exact inf_le_right

theorem eq_zero_of_vanish {K : Subgroup (finU (E := E) (n := n))} {S : Finset (UA E n)}
    (hS : ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n))
    {f : UA E n → ℂ} (hl : ∀ γ ∈ ratU E n, ∀ g, f (γ * g) = f g) (hK : ∀ k ∈ K, RU E n k f = f)
    (h0 : ∀ s ∈ S, ∀ x ∈ infU E n, f (s * x) = 0) : f = 0 := by
  funext g
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  rw [mul_assoc, mul_assoc, hl γ hγ, ← mul_assoc]
  have := congrFun (hK k hk) (s * x)
  rw [RU_apply] at this
  rw [this, h0 s hs x hx]
  rfl

theorem exists_ne_zero (π : AutSub E n) : ∃ φ ∈ π.V, φ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot π.isAut.ne_bot

theorem finiteDimensional_fixed (π : AutSub E n) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let L : fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K →ₗ[ℂ] (S → C φ) :=
    LinearMap.pi fun s => LinearMap.codRestrict (C φ)
      ((LinearMap.funLeft ℂ ℂ fun x : infU E n => (s : UA E n) * x) ∘ₗ π.V.subtype ∘ₗ (fixed _ K).subtype)
      (fun ψ => mem_Y.1 (le_Y π hφ h0 ψ.1.2) s)
  refine Module.Finite.of_injective L (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun ψ hψ => ?_))
  have hK' : ∀ k ∈ K, RU E n k ψ.1.1 = ψ.1.1 := fun k hk => by
    have e : (π.rep.comp (finU (E := E) (n := n)).subtype) k ψ.1 = (((1 : K →* ℂˣ) ⟨k, hk⟩ : ℂˣ) : ℂ) • ψ.1 := ψ.2 ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact congrArg Subtype.val e
  have hf := eq_zero_of_vanish hS (π.isAut.aut _ ψ.1.2).left hK' fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hψ ⟨s, hs⟩)) ⟨x, hx⟩
  exact Subtype.ext (Subtype.ext hf)

def stab (φ : UA E n → ℂ) : Subgroup (finU (E := E) (n := n)) where
  carrier := {k | RU E n k φ = φ}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, ← RU_RU, hb, ha]
  one_mem' := by
    show RU E n 1 φ = φ
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [RU_RU, InvMemClass.coe_inv, inv_mul_cancel, map_one]
    rfl

theorem finiteDimensional_hom (π : AutSub E n) : FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n (stab φ) (π.isAut.aut φ hφ).level
  let φV : π.V := ⟨φ, hφ⟩
  have hXV : X φ ≤ π.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact π.isAut.stable _ φ hφ)
  have hmem : ∀ (T : π.rep.IntertwiningMap (autRep E n)) (s : UA E n),
      (fun x : infU E n => (T φV).1 (s * x)) ∈ C φ := by
    intro T s
    have e : (fun x : infU E n => (T φV).1 (s * x)) = fun x => ((LinearMap.proj s) ∘ₗ (autU E n).subtype ∘ₗ
        T.toLinearMap ∘ₗ Submodule.inclusion hXV) (rhoX φ x ⟨φ, self_mem_X φ⟩) :=
      funext fun x => (congrFun (congrArg Subtype.val (LinearMap.congr_fun (T.isIntertwining' (x : UA E n)) φV)) s).symm
    rw [e]
    exact mem_C φ _ _
  let Φ : π.rep.IntertwiningMap (autRep E n) →ₗ[ℂ] (S → C φ) :=
    { toFun := fun T s => ⟨fun x : infU E n => (T φV).1 ((s : UA E n) * x), hmem T s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun T hT => ?_))
  have hK : ∀ k ∈ stab φ, RU E n k (T φV).1 = (T φV).1 := fun k hk => by
    have e : T (π.rep k φV) = autRep E n k (T φV) := LinearMap.congr_fun (T.isIntertwining' (k : UA E n)) φV
    rw [show π.rep k φV = φV from Subtype.ext hk] at e
    exact (congrArg Subtype.val e).symm
  have hTφ : T φV = 0 := Subtype.ext (eq_zero_of_vanish hS (mem_autU.1 (T φV).2).left hK fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hT ⟨s, hs⟩)) ⟨x, hx⟩)
  let W : Submodule ℂ (UA E n → ℂ) := (LinearMap.ker T.toLinearMap).map π.V.subtype
  have hst : ∀ x, ∀ ψ ∈ W, RU E n x ψ ∈ W := by
    rintro x _ ⟨ψ', hψ', rfl⟩
    refine ⟨π.rep x ψ', ?_, rfl⟩
    have h1 : T ψ' = 0 := hψ'
    change T (π.rep x ψ') = 0
    have h2 : T (π.rep x ψ') = autRep E n x (T ψ') := LinearMap.congr_fun (T.isIntertwining' x) ψ'
    rw [h2, h1, map_zero]
  rcases π.isAut.irred W (Submodule.map_subtype_le _ _) hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨φV, hTφ, rfl⟩ : φ ∈ W))) h0
  · refine DFunLike.ext _ _ fun ψ => ?_
    obtain ⟨ψ', hψ', e⟩ : ψ.1 ∈ W := h.symm ▸ ψ.2
    rw [← Subtype.ext e]
    exact hψ'

theorem admissible_finiteMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    (∀ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) →
      FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K)) ∧
    FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) :=
  fun _ _ _ _ _ π => ⟨fun K hK => finiteDimensional_fixed π K hK, finiteDimensional_hom π⟩

end GlobalTheory.DefU.admitted
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.FockAct

open GlobalTheory.AdTh.SourceBasis GlobalTheory.OrientedHeis

theorem unitMap_mul_mul {m n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ) (B' H : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * U) (B' * H) i j = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • unitMap B B' i' c := by
  have e : H * Matrix.single i j (1 : ℂ) * U⁻¹ = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • Matrix.single i' c (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (H * Matrix.single i j (1 : ℂ) * U⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun c _ hc => by simp [Matrix.mul_single_apply_of_ne, hc]) (by simp)]
    simp
  unfold unitMap
  calc _ = B' * (H * Matrix.single i j (1 : ℂ) * U⁻¹) * B⁻¹ := by
        rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem pureTensorO_mul_mul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BV U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (P : Pol D.what₂.Tau W.rank V.rank) :
    pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) (fun τ => BV τ * U τ) (fun τ => BW τ * H τ) f P =
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BV BW f (subst (fun τ => (U τ)⁻¹) H P) := by
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') := fun f g hf hg => {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun c f hf => {
    quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  have hA : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have hm : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q,
      IsThetaFunO ψ V W (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) := fun BS BT Q =>
    GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT) hf Q
  have hX : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q v,
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
        aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT v
          (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) :=
    fun BS BT Q v => GlobalTheory.Ker.FockAlg.pure_X_mul (A := aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT)
      (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT)
      (fun i j _ h => aPlus_comm hψ hθ i.1 _ (s := fun _ => 1) (fun τ => by simp) (fun τ => by simp) j.1 _ h)
      (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h) hf Q v
  have h1 := fun BS BT => GlobalTheory.FiniteFock.pureTensorO_one ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul,
      map_smul, map_smul, h1, h1]
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), map_add (f := _), hP, hQ]
  | mul_X P v hP =>
    obtain ⟨τ, i, j⟩ := v
    rw [mul_comm, hX, hP, map_mul]
    clear hP
    generalize (subst _ H P : Pol D.what₂.Tau W.rank V.rank) = Q
    rw [subst, MvPolynomial.aeval_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hX]
    simp only [aPlusAll, aPlus]
    rw [unitMap_mul_mul, crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [crea_smul hψ hθ τ _ (hm _ _ _) _ True (by simp), if_pos trivial, smul_comm]

theorem om_vac {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    {sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D V τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D W τ) (sT τ))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sS τ) (sT τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W)
    (cS : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt V g) = compAt θ τ (Formalism.L2.Theta.mt V g) * sS τ)
    (cT : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt W h) = compAt θ τ (Formalism.L2.Theta.mt W h) * sT τ) :
    ∃ c : ℂ, ω (g, h) f = c • f := by
  obtain ⟨x₁, x₂, y₁, y₂, hc⟩ := GlobalTheory.VacuumChar.vacuum_char D ψ θ V W χS χT ω hω hθ kV kW sS sT hS hT
  exact ⟨_, hc f hf hv g hg h hh cS cT⟩

open Classical in
theorem compAt_atTau {S : D.what₂.Tau → SPar} {M : DSModel V S} (hθ : IsInfFam θ) (h : AllPlus M) (τ : D.what₂.Tau)
    (u : Matrix.unitaryGroup (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    onb M ρ * (if ρ = τ then (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1) =
      compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) * onb M ρ := by
  have s := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (h.unfr_mem τ u)
  split_ifs with e
  · subst e
    have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V ρ (unfr M ρ u))) = unfr M ρ u := s.2.1
    rw [e1, unfr, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M ρ)]
  · have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) = 1 := s.2.2 ρ e
    rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem compAt_one (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    B * 1 = compAt θ ρ (Formalism.L2.Theta.mt V 1) * B := by
  have e1 : compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 := GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem om_ptOf {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK) (hM : AllPlus M)
    (hM' : AllPlus M') (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W) (U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hU : ∀ ρ, onb M ρ * U ρ = compAt θ ρ (Formalism.L2.Theta.mt V g) * onb M ρ)
    (hH : ∀ ρ, onb M' ρ * H ρ = compAt θ ρ (Formalism.L2.Theta.mt W h) * onb M' ρ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (g, h) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (subst (fun ρ => (U ρ)⁻¹) H P) := by
  have e1 : cart M = fun _ => 1 := funext hM.cart
  have e2 : cart M' = fun _ => 1 := funext hM'.cart
  unfold ptOf
  rw [e1, e2] at hv ⊢
  obtain ⟨c, c0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ ω (g, h) f = c • f := by
    by_cases f0 : f = 0
    · exact ⟨1, one_ne_zero, by rw [f0, map_zero, smul_zero]⟩
    obtain ⟨c, e⟩ := om_vac hω hθ kV kW (sS := fun _ => 1) (sT := fun _ => 1)
      (fun τ => ⟨by simp, by simp, by simpa using hM.posDef τ⟩) (fun τ => ⟨by simp, by simp, by simpa using hM'.posDef τ⟩)
      hf hv hg hh (fun τ => by simp) (fun τ => by simp)
    refine ⟨c, fun c0 => f0 ?_, e⟩
    rw [c0, zero_smul] at e
    have e' := congrArg (ω (g, h)⁻¹) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e'
  refine ⟨c, c0, fun P => ?_⟩
  rw [(om_pureTensorO D ψ θ V W χS χT ω hω hθ (fun _ => 1) (fun _ => 1) (onb M) (fun ρ => onb M ρ * U ρ)
    (fun _ => 1) (fun _ => 1) (onb M') (fun ρ => onb M' ρ * H ρ) g h (fun τ => by simp) (fun τ => by simp) hU hH f hf P).2,
    hc, GlobalTheory.FiniteFock.pureTensorO_smul, pureTensorO_mul_mul hω.std hθ _ _ _ _ hf]

theorem fock_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  classical
  intro D ψ V W χS χT ω θ S S' M M' f hω hθ kV kW hM hM' hf hv τ
  refine ⟨fun g => ?_, fun u => ?_⟩
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (one_mem _) _ (fun _ => 1)
      (compAt_atTau hθ hM τ g) (fun ρ => compAt_one _ ρ)
    have e : (fun ρ => (if ρ = τ then (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1)⁻¹) =
        fun ρ => if ρ = τ then star (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
      funext ρ
      split_ifs
      · exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 g.2)
      · exact inv_one
    rw [e] at this
    exact this
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _) (fun _ => 1) _
      (fun ρ => compAt_one _ ρ) (compAt_atTau hθ hM' τ u)
    simp only [inv_one] at this
    exact this

end GlobalTheory.DefLift.FockAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_unipB_mul_diagT_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  intro k _ _ _ _ m g
  obtain ⟨u, l, w, hw, h⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (points (Fin m)) g
  refine ⟨u, u.2, (leviTorus k (Fin m)).symm l, w, hw, ?_⟩
  rw [h]
  simp [diagT]

end GlobalTheory.SmGL
end

