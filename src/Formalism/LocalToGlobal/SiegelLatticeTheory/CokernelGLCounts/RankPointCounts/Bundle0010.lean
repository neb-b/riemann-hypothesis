module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNC
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem X_le_orth (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) : X ≤ orth S X :=
  fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => hXiso y hy x hx

theorem orth_X {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT x u = 0 :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx

theorem orth_X' {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT u x = 0 := by
  rw [hsw S x u, orth_X S hu hx, star_zero]

theorem stepB (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ₂ : Submodule.IsLattice E Λ₂) (hSD₂ : SD S Λ₂)
    (hX : ∀ x ∈ X, x ∈ Λ₂ → x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) :
    ∃ A : orth S X →ₗ[E] S.V, (∀ u, A u ∈ X) ∧ (∀ u : orth S X, (u : S.V) ∈ X → A u = 0) ∧
      A ⟨z, hzX⟩ = 0 ∧ ∀ (x : S.V) (hx : x ∈ orth S X), x ∈ Λ₂ → x + A ⟨x, hx⟩ ∈ Λ := by
  classical
  obtain ⟨y, hyΛ, hyX, hyz⟩ := hy
  let M₂ : Submodule (𝓞 E) S.V := Λ₂ ⊓ (orth S X).restrictScalars (𝓞 E)
  have hM₂fg : M₂.FG := Submodule.FG.of_le hΛ₂.fg inf_le_left
  have hXo := X_le_orth S X hXiso
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S M₂ Λ hM₂fg X X (fun x hx hxX => hX x hxX hx.1)
    (fun x hx => hL x hx.1 hx.2)
  let z₂ : M₂ := ⟨z, hz₂, hzX⟩
  let κ : M₂ →ₗ[𝓞 E] E := ((S.hT y).restrictScalars (𝓞 E)) ∘ₗ M₂.subtype
  let δ' : M₂ →ₗ[𝓞 E] S.V := δ - κ.smulRight (δ z₂)
  have hδ'app : ∀ m, δ' m = δ m - S.hT y m • δ z₂ := fun m => rfl
  have hδ'X : ∀ m, δ' m ∈ X := fun m => by
    rw [hδ'app]; exact X.sub_mem (hδX m) (X.smul_mem _ (hδX z₂))
  have hδ'0 : ∀ m : M₂, (m : S.V) ∈ X → δ' m = 0 := fun m hm => by
    rw [hδ'app, hδ0 m hm, orth_X' S hyX hm, zero_smul, sub_zero]
  have hδ'z : δ' z₂ = 0 := by
    rw [hδ'app]; show δ z₂ - S.hT y z • δ z₂ = 0; rw [hyz, one_smul, sub_self]
  have hδzΛ : δ z₂ ∈ Λ := by
    have := Λ.sub_mem (hδΛ z₂) hz
    have e : (z₂ : S.V) + δ z₂ - z = δ z₂ := by show z + δ z₂ - z = δ z₂; abel
    rwa [e] at this
  have hδ'Λ : ∀ m : M₂, (m : S.V) + δ' m ∈ Λ := fun m => by
    rw [hδ'app, ← add_sub_assoc]
    exact Λ.sub_mem (hδΛ m) (int_smul_mem (sd_int hSD₂ m.2.1 hyΛ) hδzΛ)
  have hden : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₂ := by
    intro u
    obtain ⟨s, hs⟩ := hΛ₂.fg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s (fun x => S.hT x u)
    let P : Submodule (𝓞 E) S.V := {
      carrier := {x | IsIntegral ℤ ((d : 𝓞 E) • S.hT x u)}
      zero_mem' := by simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
      add_mem' := by
        intro x y hx hy
        simpa [map_add, LinearMap.add_apply, smul_add] using hx.add hy
      smul_mem' := by
        intro a x hx
        change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u) at hx
        change IsIntegral ℤ ((d : 𝓞 E) • S.hT (a • x) u)
        rw [oSmul S a x, hT_smulL S, oSmulW, smul_eq_mul]
        have ha : IsIntegral ℤ (star (a : E)) := isInt_star a.2
        convert ha.mul hx using 1 <;> rw [oSmulW, smul_eq_mul] <;> ring }
    have hsP : (s : Set S.V) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := hd x hx
      change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u)
      rw [← hb]
      exact b.2
    have hdu : (d : 𝓞 E) • u ∈ Λ₂ := by
      apply (hSD₂ _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u) at hxP
      rw [oSmul S, map_smul]
      simpa only [oSmulW] using hxP
    exact ⟨d, nonZeroDivisors.ne_zero d.2, hdu⟩
  have hfull : ∀ u ∈ orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ M₂ := fun u hu => by
    obtain ⟨d, hd, hdu⟩ := hden u
    exact ⟨d, hd, hdu, by show d • u ∈ orth S X; rw [oSmul]; exact (orth S X).smul_mem _ hu⟩
  obtain ⟨A, hA⟩ := ext_lat S (W := S.V) (orth S X) M₂ (fun x hx => hx.2) hfull δ'
  have hscale : ∀ u : orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • (u : S.V)) ∈ M₂,
      (d : E) • A u = δ' ⟨_, hm⟩ := fun u => by
    obtain ⟨d, hd, hdu⟩ := hfull u u.2
    rw [oSmul] at hdu
    refine ⟨d, hd, hdu, ?_⟩
    rw [← map_smul, ← hA _ hdu]
    rfl
  refine ⟨A, fun u => ?_, fun u hu => ?_, ?_, fun x hx hxΛ => ?_⟩
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    have h1 : (d : E) • A u ∈ X := by rw [he]; exact hδ'X _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ'0 _ (X.smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)
  · rw [hA z ⟨hz₂, hzX⟩]; exact hδ'z
  · rw [hA x ⟨hxΛ, hx⟩]; exact hδ'Λ ⟨x, hxΛ, hx⟩

theorem stepW (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (A : orth S X →ₗ[E] S.V)
    (hA : ∀ u, A u ∈ X) (hA0 : ∀ u : orth S X, (u : S.V) ∈ X → A u = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (g a) (g b) = S.hT a b) ∧ ∀ u : orth S X, g u = u + A u := by
  let f : orth S X →ₗ[E] S.V := (orth S X).subtype + A
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h1 : (u : S.V) = -A u := eq_neg_of_add_eq_zero_left hu
    have h2 : (u : S.V) ∈ X := by rw [h1]; exact X.neg_mem (hA u)
    have h3 := hA0 u h2
    rw [h3, neg_zero] at h1
    exact (Submodule.mem_bot E).2 (Subtype.ext h1)
  have hiso : ∀ u v : orth S X, S.hT (f u) (f v) = S.hT u v := fun u v => by
    show S.hT ((u : S.V) + A u) ((v : S.V) + A v) = S.hT u v
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, orth_X' S u.2 (hA v), orth_X S v.2 (hA u),
      hXiso _ (hA u) _ (hA v)]
    ring
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => by rw [hsw S x y])
    (fun x hx => S.nondeg.1 x hx) (orth S X) f hinj hiso
  exact ⟨g, hg, fun u => hgf u⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassClEqSum
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RhoPf

open Formalism.L2.SG.TypedSets

section Abstract

variable {G : Type} [Group G]

theorem mem_map_conj (K : Subgroup G) (x a : G) :
    a ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * a * x ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem stab_eq_map (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom =
      (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
  ext a
  rw [Subgroup.mem_inf, mem_map_conj, mem_map_conj, Subgroup.mem_inf, mem_map_conj]
  have e1 : (γ * x * k)⁻¹ * a * (γ * x * k) = k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k := by group
  have e2 : x⁻¹ * (γ⁻¹ * a * γ) * x = k * (k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k) * k⁻¹ := by group
  constructor
  · rintro ⟨ha, hK⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) ha) hγ, ?_⟩
    rw [e1] at hK
    rw [e2]
    exact K.mul_mem (K.mul_mem hk hK) (K.inv_mem hk)
  · rintro ⟨ha, hK⟩
    refine ⟨?_, ?_⟩
    · have e3 : a = γ * (γ⁻¹ * a * γ) * γ⁻¹ := by group
      rw [e3]
      exact Γ.mul_mem (Γ.mul_mem hγ ha) (Γ.inv_mem hγ)
    · rw [e1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hK) hk

theorem card_conj_eq (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  rw [stab_eq_map Γ K x γ k hγ hk]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

theorem card_out_eq (Γ K : Subgroup G) (x : G) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out (DoubleCoset.mk Γ K x))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨γ, hγ, k, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
  rw [h]
  exact card_conj_eq Γ K x γ k hγ hk

end Abstract

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem massCl_comap (e : G' ≃* G) (Γ K : Subgroup G) :
    massCl (Γ.comap e.toMonoidHom) (K.comap e.toMonoidHom) = massCl Γ K := by
  set Γ' := Γ.comap e.toMonoidHom with hΓ'
  set K' := K.comap e.toMonoidHom with hK'
  have hstab : ∀ y : G', Nat.card ↥(Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom) := by
    intro y
    have hm : (Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom =
        Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom := by
      ext a
      rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj, mem_map_conj]
      simp [hΓ', hK', Subgroup.mem_comap, map_mul, map_inv]
    rw [← hm, Subgroup.card_map_of_injective e.injective]
  unfold massCl
  refine finsum_eq_of_bijective (fun c => DoubleCoset.mk Γ K (e (Quotient.out c))) ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (@DoubleCoset.eq _ _ Γ K _ _).mp h
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    refine (@DoubleCoset.eq _ _ Γ' K' _ _).mpr
      ⟨e.symm γ, by simpa [hΓ'] using hγ, e.symm k, by simpa [hK'] using hk, ?_⟩
    apply e.injective
    simp [map_mul, h2]
  · intro c
    obtain ⟨γ, hγ, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ' K' (e.symm (Quotient.out c))
    refine ⟨DoubleCoset.mk Γ' K' (e.symm (Quotient.out c)), ?_⟩
    show DoubleCoset.mk Γ K (e (Quotient.out (DoubleCoset.mk Γ' K' (e.symm (Quotient.out c))))) = c
    rw [hout]
    conv_rhs => rw [← Quotient.out_eq c]
    refine ((@DoubleCoset.eq _ _ Γ K _ _).mpr ⟨e γ, hγ, e k, hk, ?_⟩).symm
    simp [map_mul]
  · intro c
    rw [card_out_eq, hstab]

end Transport

section Count

variable {G α : Type} [Group G]

theorem massCl_eq_sum (Γ K : Subgroup G) (S : Finset α) (ℓ : G → α) (w : α → ℝ)
    (hS : ∀ x, ℓ x ∈ S)
    (hrel : ∀ x y, ℓ x = ℓ y ↔ ∃ γ ∈ Γ, ∃ k ∈ K, y = γ * x * k)
    (hsurj : ∀ s ∈ S, ∃ x, ℓ x = s)
    (hw : ∀ x, ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℕ) : ℝ)⁻¹ = w (ℓ x)) :
    massCl Γ K = ∑ s ∈ S, w s := by
  unfold massCl
  have hout : ∀ x, ∃ γ ∈ Γ, ∃ k ∈ K, Quotient.out (DoubleCoset.mk Γ K x) = γ * x * k := by
    intro x
    obtain ⟨γ, hγ, k, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
    exact ⟨γ, hγ, k, hk, h⟩
  rw [← Finset.sum_coe_sort S w, ← finsum_eq_sum_of_fintype]
  refine finsum_eq_of_bijective (fun c => (⟨ℓ (Quotient.out c), hS _⟩ : {s // s ∈ S}))
    ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    have h' : ℓ (Quotient.out c1) = ℓ (Quotient.out c2) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (hrel _ _).mp h'
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    exact (@DoubleCoset.eq _ _ Γ K _ _).mpr ⟨γ, hγ, k, hk, h2⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := hsurj s hs
    refine ⟨DoubleCoset.mk Γ K x, Subtype.ext ?_⟩
    obtain ⟨γ, hγ, k, hk, h⟩ := hout x
    exact ((hrel _ _).mpr ⟨γ, hγ, k, hk, h⟩).symm
  · intro c
    exact hw _

end Count

end Formalism.L2.SG.RhoPf
end
end

