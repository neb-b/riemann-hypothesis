module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
section
namespace DualFramesAlt.EigenUniformiser

open PowerSeries

variable {O : Type*} [CommRing O]

private theorem powerSeries_algHom_C_eq (α : PowerSeries O →ₐ[O] PowerSeries O) (c : O) : α (C c) = C c := by
  have h : (C c : PowerSeries O) = algebraMap O (PowerSeries O) c := by
    rw [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul, mul_one]
  rw [h, AlgHom.commutes]

private theorem X_pow_dvd_algHom_sub_of_X_eq (α β : PowerSeries O →ₐ[O] PowerSeries O) (hX : α X = β X)
    (h0 : constantCoeff (α X) = 0) (n : ℕ) (f : PowerSeries O) :
    (X : PowerSeries O) ^ n ∣ α f - β f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    obtain ⟨g, c, hf⟩ : ∃ (g : PowerSeries O) (c : O), f = X * g + C c :=
      ⟨_, _, eq_X_mul_shift_add_const f⟩
    subst hf
    have key : α (X * g + C c) - β (X * g + C c) = α X * (α g - β g) := by
      rw [map_add (f := _), map_add (f := _), map_mul, map_mul, powerSeries_algHom_C_eq α, powerSeries_algHom_C_eq β, ← hX]; ring
    rw [key, pow_succ']
    exact mul_dvd_mul (X_dvd_iff.mpr h0) (ih g)

private theorem algHom_apply_eq_of_X_eq (α β : PowerSeries O →ₐ[O] PowerSeries O) (hX : α X = β X)
    (h0 : constantCoeff (α X) = 0) (f : PowerSeries O) : α f = β f := by
  rw [← sub_eq_zero]
  ext n
  have h := (X_pow_dvd_iff.mp (X_pow_dvd_algHom_sub_of_X_eq α β hX h0 (n + 1) f)) n (Nat.lt_succ_self n)
  rw [h, map_zero]

theorem algHom_subst (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : constantCoeff (φ X) = 0) {p : PowerSeries O} (hp : constantCoeff p = 0)
    (g : PowerSeries O) :
    φ (PowerSeries.subst p g) = PowerSeries.subst (φ p) g := by
  have h0 : constantCoeff (φ p) = 0 := by
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr hp
    rw [hq, map_mul, map_mul, hφ, zero_mul]
  have hps : HasSubst p := HasSubst.of_constantCoeff_zero' hp
  have hb : HasSubst (φ p) := HasSubst.of_constantCoeff_zero' h0
  let α : PowerSeries O →ₐ[O] PowerSeries O := φ.comp (substAlgHom (R := O) hps)
  let β : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (R := O) hb
  have hα : ∀ f : PowerSeries O, α f = φ (PowerSeries.subst p f) :=
    fun f => congrArg φ (congrFun (coe_substAlgHom (R := O) hps) f)
  have hβ : ∀ f : PowerSeries O, β f = PowerSeries.subst (φ p) f :=
    fun f => congrFun (coe_substAlgHom (R := O) hb) f
  have hX : α X = β X := by rw [hα, hβ, subst_X (R := O) hps, subst_X (R := O) hb]
  have h0' : constantCoeff (α X) = 0 := by rw [hα, subst_X (R := O) hps]; exact h0
  rw [← hα, ← hβ]
  exact algHom_apply_eq_of_X_eq α β hX h0' g

section Coordinate

variable {p : PowerSeries O} (hp0 : constantCoeff p = 0) (hp1 : IsUnit (coeff 1 p))
include hp0 hp1

end Coordinate

private theorem algHom_eq_C_constantCoeff_add_X_mul (α : PowerSeries O →ₐ[O] PowerSeries O) (f : PowerSeries O) :
    α f = C (constantCoeff f) + α X * α (mk fun n => coeff (n + 1) f) := by
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [map_add (f := _), map_mul, powerSeries_algHom_C_eq, add_comm]

theorem subst_eq_C_add {a : PowerSeries O} (ha : constantCoeff a = 0) (f : PowerSeries O) :
    PowerSeries.subst a f = C (constantCoeff f) +
      a * PowerSeries.subst a (mk fun n => coeff (n + 1) f) := by
  have ha' : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  let α : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (R := O) ha'
  have hα : ∀ g : PowerSeries O, α g = PowerSeries.subst a g :=
    fun g => congrFun (coe_substAlgHom (R := O) ha') g
  rw [← hα, ← hα, algHom_eq_C_constantCoeff_add_X_mul α f, hα X, subst_X (R := O) ha']

end DualFramesAlt.EigenUniformiser
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FinrankMapMkQ
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Module

variable {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X]

theorem finrank_map_mkQ (Oth S : Submodule LL X) (h : Disjoint S Oth) :
    finrank LL ↥(S.map Oth.mkQ) = finrank LL ↥S := by
  have hinj : Function.Injective (Oth.mkQ ∘ₗ S.subtype) := by
    intro x y hxy
    have hxy' : Oth.mkQ (x : X) = Oth.mkQ (y : X) := hxy
    simp only [Submodule.mkQ_apply] at hxy'
    rw [Submodule.Quotient.eq] at hxy'
    have h0 : (x : X) - y = 0 := (Submodule.disjoint_def.mp h) _ (sub_mem x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp h0)
  have hr : LinearMap.range (Oth.mkQ ∘ₗ S.subtype) = S.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  calc finrank LL ↥(S.map Oth.mkQ)
        = finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ S.subtype)) := by rw [hr]
    _ = finrank LL ↥S := ((LinearEquiv.ofInjective _ hinj).finrank_eq).symm

theorem match_fil (I D Oth : Submodule LL X) [FiniteDimensional LL ↥I] [FiniteDimensional LL ↥D]
    (hDO : Disjoint D Oth) (hdim : finrank LL ↥I = finrank LL ↥D) (hDI : D ≤ I ⊔ Oth) :
    Disjoint I Oth ∧ ∀ F : Submodule LL X, F ≤ D → finrank LL ↥(I ⊓ (F ⊔ Oth)) = finrank LL ↥F := by
  have hsupmap : ∀ P : Submodule LL X, (P ⊔ Oth).map Oth.mkQ = P.map Oth.mkQ := by
    intro P
    first
      | rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
      | simp [Submodule.map_sup]
  have hmap : D.map Oth.mkQ ≤ I.map Oth.mkQ := by
    calc D.map Oth.mkQ ≤ (I ⊔ Oth).map Oth.mkQ := Submodule.map_mono hDI
      _ = I.map Oth.mkQ := hsupmap I
  haveI hfin : FiniteDimensional LL ↥(I.map Oth.mkQ) := by
    first
      | infer_instance
      | exact Module.Finite.map I Oth.mkQ
  have hDmap : finrank LL ↥(D.map Oth.mkQ) = finrank LL ↥D :=
    finrank_map_mkQ Oth D hDO
  have hIle : finrank LL ↥(I.map Oth.mkQ) ≤ finrank LL ↥I := by
    first
      | exact Submodule.finrank_map_le _ _
      | apply Submodule.finrank_map_le
  have hle2 : finrank LL ↥(D.map Oth.mkQ) ≤ finrank LL ↥(I.map Oth.mkQ) := by
    first
      | exact Submodule.finrank_le_finrank_of_le hmap
      | exact LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hmap)
  have hIeq : finrank LL ↥(I.map Oth.mkQ) = finrank LL ↥I := by omega
  have hrI : LinearMap.range (Oth.mkQ ∘ₗ I.subtype) = I.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Oth.mkQ ∘ₗ I.subtype)
  have hr' : finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ I.subtype)) = finrank LL ↥I := by
    rw [hrI]; exact hIeq
  have hk : finrank LL ↥(LinearMap.ker (Oth.mkQ ∘ₗ I.subtype)) = 0 := by omega
  have hkb : LinearMap.ker (Oth.mkQ ∘ₗ I.subtype) = ⊥ := by
    first
      | exact Submodule.finrank_eq_zero.mp hk
      | exact (Submodule.finrank_eq_zero (S := LinearMap.ker (Oth.mkQ ∘ₗ I.subtype))).mp hk
      | (haveI := Module.finrank_zero_iff.mp hk; exact Submodule.eq_bot_of_subsingleton)
  have hinj : Function.Injective (Oth.mkQ ∘ₗ I.subtype) := LinearMap.ker_eq_bot.mp hkb
  have hdisj : Disjoint I Oth := by
    rw [Submodule.disjoint_def]
    intro x hxI hxO
    have h1 : (Oth.mkQ ∘ₗ I.subtype) ⟨x, hxI⟩ = (Oth.mkQ ∘ₗ I.subtype) 0 := by
      rw [map_zero]
      show Oth.mkQ x = 0
      first
        | (rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxO)
        | simp [hxO]
    have h2 := hinj h1
    first
      | exact congrArg Subtype.val h2
      | simpa using congrArg Subtype.val h2
  refine ⟨hdisj, fun F hF => ?_⟩
  have hFO : Disjoint F Oth := hDO.mono_left hF
  have hJO : Disjoint (I ⊓ (F ⊔ Oth)) Oth := hdisj.mono_left inf_le_left
  have heq : (I ⊓ (F ⊔ Oth)).map Oth.mkQ = F.map Oth.mkQ := by
    apply le_antisymm
    · calc (I ⊓ (F ⊔ Oth)).map Oth.mkQ ≤ (F ⊔ Oth).map Oth.mkQ := Submodule.map_mono inf_le_right
        _ = F.map Oth.mkQ := hsupmap F
    · intro y hy
      obtain ⟨f, hfF, rfl⟩ := Submodule.mem_map.mp hy
      have hfD : Oth.mkQ f ∈ I.map Oth.mkQ := hmap (Submodule.mem_map.mpr ⟨f, hF hfF, rfl⟩)
      obtain ⟨i, hiI, hif⟩ := Submodule.mem_map.mp hfD
      have hsub : i - f ∈ Oth := by
        simp only [Submodule.mkQ_apply] at hif
        exact (Submodule.Quotient.eq Oth).mp hif
      have h3 : f + (i - f) ∈ F ⊔ Oth := Submodule.add_mem_sup hfF hsub
      have hi : i ∈ F ⊔ Oth := by
        first
          | simpa using h3
          | (rw [add_sub_cancel] at h3; exact h3)
      exact Submodule.mem_map.mpr ⟨i, Submodule.mem_inf.mpr ⟨hiI, hi⟩, hif⟩
  calc finrank LL ↥(I ⊓ (F ⊔ Oth))
        = finrank LL ↥((I ⊓ (F ⊔ Oth)).map Oth.mkQ) :=
          (finrank_map_mkQ Oth _ hJO).symm
    _ = finrank LL ↥(F.map Oth.mkQ) := by rw [heq]
    _ = finrank LL ↥F := finrank_map_mkQ Oth F hFO

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.IsAdicCompleteMax
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.AdicCompletionMax

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_eq_max_pow {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.span {p} = IsLocalRing.maximalIdeal O ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩
  · rintro rfl
    rw [pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at hn
    exact absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)
  · rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

private theorem isAdicComplete_of_isAdicComplete_pow {J : Ideal O} {k : ℕ} (hk : 1 ≤ k)
    (h : IsAdicComplete (J ^ k) O) : IsAdicComplete J O := by
  have key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n) := fun n => (pow_mul J k n).symm
  have hkn : ∀ n : ℕ, n ≤ k * n := fun n => by simpa using Nat.mul_le_mul hk (le_refl n)
  have hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤ :=
    fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [key]
    exact hx (k * n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n))
      (fun {a b} hab => by
        rw [key]
        exact hf (Nat.mul_le_mul (le_refl k) hab))
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)] := hf (hkn n)
    have h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := by
      have h3 := hL n
      rw [key] at h3
      exact SModEq.mono (hle (hkn n)) h3
    exact h1.trans h2

theorem isAdicComplete_max {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O)
    [h : IsAdicComplete (Ideal.span {p}) O] : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  obtain ⟨k, hk, hkeq⟩ := span_eq_max_pow hp0 hpm
  rw [hkeq] at h
  exact isAdicComplete_of_isAdicComplete_pow hk h

end Formalism.MainNotions.N.Ln34.AdicCompletionMax
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankInverseBounds
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankInverseBounds

open Module
open scoped Classical

variable {O V : Type*} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]

def Inv (γ : V →ₗ[O] V) (K' P : Submodule O V) : Submodule O V :=
  P ⊓ K'.comap (γ - LinearMap.id)

abbrev InvQ (γ : V →ₗ[O] V) (K' P : Submodule O V) : Type _ :=
  ↥(Inv γ K' P) ⧸ K'.comap (Inv γ K' P).subtype

abbrev Gr (P P' : Submodule O V) : Type _ := ↥P ⧸ P'.comap P.subtype

private theorem mem_Inv_iff_mem_and_sub_mem {γ : V →ₗ[O] V} {K' P : Submodule O V} {x : V} :
    x ∈ Inv γ K' P ↔ x ∈ P ∧ γ x - x ∈ K' := by
  first
  | exact Iff.rfl
  | simp only [Inv, Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.id_apply]

theorem inv_mono (γ : V →ₗ[O] V) (K' : Submodule O V) {P P' : Submodule O V} (h : P' ≤ P) :
    Inv γ K' P' ≤ Inv γ K' P := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_Inv_iff_mem_and_sub_mem.mp hx
  exact mem_Inv_iff_mem_and_sub_mem.mpr ⟨h h1, h2⟩

theorem rank_eq_zero_of_smul {M : Type*} [AddCommGroup M] [Module O M] (a : O) (ha : a ≠ 0)
    (h : ∀ x : M, a • x = 0) : Module.rank O M = 0 := by
  first
  | exact rank_eq_zero_iff.mpr fun x => ⟨a, ha, h x⟩
  | exact (rank_eq_zero_iff (R := O) (M := M)).mpr fun x => ⟨a, ha, h x⟩

theorem step (γ : V →ₗ[O] V) (K' : Submodule O V) (hK : ∀ x ∈ K', γ x ∈ K')
    (F0 F1 : Submodule O V) (c : O) (h10 : F1 ≤ F0) (hγ : ∀ x ∈ F0, γ x - c • x ∈ F1) :
    Module.rank O (InvQ γ K' F0) ≤ Module.rank O (InvQ γ K' F1) +
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
  have hle : Inv γ K' F1 ≤ Inv γ K' F0 := inv_mono γ K' h10
  let f : InvQ γ K' F1 →ₗ[O] InvQ γ K' F0 :=
    Submodule.mapQ (K'.comap (Inv γ K' F1).subtype)
      (K'.comap (Inv γ K' F0).subtype) (Submodule.inclusion hle) (by
        intro x hx
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
        exact hx)
  let π : ↥(Inv γ K' F0) →ₗ[O] InvQ γ K' F0 ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ (K'.comap (Inv γ K' F0).subtype).mkQ
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨x, rfl⟩
  have key : ∀ x : ↥(Inv γ K' F0),
      (K'.comap (Inv γ K' F0).subtype).mkQ x ∈ LinearMap.range f → π x = 0 := by
    intro x hx
    simp only [π, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hquot : Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) ≤
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
    split_ifs with hc1
    · let ψ : ↥(Inv γ K' F0) →ₗ[O] Gr F0 F1 :=
        (F1.comap F0.subtype).mkQ ∘ₗ Submodule.inclusion (fun y hy => (mem_Inv_iff_mem_and_sub_mem.mp hy).1)
      have hker : LinearMap.ker ψ ≤ LinearMap.ker π := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        have hxF1 : (x : V) ∈ F1 := by
          first
          | (simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
              Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx
             exact hx)
          | simpa [ψ] using hx
        apply key
        have hx1 : (x : V) ∈ Inv γ K' F1 :=
          mem_Inv_iff_mem_and_sub_mem.mpr ⟨hxF1, (mem_Inv_iff_mem_and_sub_mem.mp x.2).2⟩
        refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨x, hx1⟩, ?_⟩
        first
        | rfl
        | (simp only [f, Submodule.mapQ_apply, Submodule.mkQ_apply]; rfl)
      let g : ↥(Inv γ K' F0) ⧸ LinearMap.ker ψ →ₗ[O]
          InvQ γ K' F0 ⧸ LinearMap.range f :=
        (LinearMap.ker ψ).liftQ π hker
      have hg : Function.Surjective g := by
        intro b
        obtain ⟨a, rfl⟩ := hπ b
        exact ⟨Submodule.Quotient.mk a, rfl⟩
      calc _ ≤ Module.rank O (↥(Inv γ K' F0) ⧸ LinearMap.ker ψ) :=
            LinearMap.rank_le_of_surjective g hg
        _ = Module.rank O (LinearMap.range ψ) := ψ.quotKerEquivRange.rank_eq
        _ ≤ Module.rank O (Gr F0 F1) := Submodule.rank_le _
    · apply le_of_eq
      apply rank_eq_zero_of_smul (c - 1) (sub_ne_zero.mpr hc1)
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      rw [← map_smul π]
      apply key
      obtain ⟨hxF0, hxK⟩ := mem_Inv_iff_mem_and_sub_mem.mp x.2
      have hmem : c • (x : V) - γ x ∈ Inv γ K' F1 := by
        refine mem_Inv_iff_mem_and_sub_mem.mpr ⟨?_, ?_⟩
        · rw [← neg_sub]
          exact F1.neg_mem (hγ _ hxF0)
        · have e : γ (c • (x : V) - γ x) - (c • (x : V) - γ x) = c • (γ x - x) - γ (γ x - x) := by
            simp only [map_sub, map_smul, smul_sub]
            abel
          rw [e]
          exact K'.sub_mem (K'.smul_mem c hxK) (hK _ hxK)
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
      have e1 : f (Submodule.Quotient.mk ⟨_, hmem⟩) =
          (Submodule.Quotient.mk (Submodule.inclusion hle ⟨_, hmem⟩) : InvQ γ K' F0) := by
        first
        | rfl
        | simp only [f, Submodule.mapQ_apply]
      rw [e1, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      convert K'.neg_mem hxK using 1
      simp only [map_sub, map_smul, Submodule.subtype_apply, Submodule.coe_inclusion, sub_smul,
        one_smul]
      abel
  calc Module.rank O (InvQ γ K' F0)
      = Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) +
          Module.rank O (LinearMap.range f) := by
        exact (rank_quotient_add_rank_of_isDomain _).symm
    _ ≤ (if c = 1 then Module.rank O (Gr F0 F1) else 0) +
          Module.rank O (InvQ γ K' F1) :=
        add_le_add hquot (by
          first
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict (fun y => by
              obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
              exact ⟨x, Subtype.ext hx⟩))
    _ = _ := add_comm _ _

end Formalism.MainNotions.N.Ln34.RankInverseBounds

end
end

