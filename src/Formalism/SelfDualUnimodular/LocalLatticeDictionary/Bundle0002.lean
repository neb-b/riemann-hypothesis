module

public import Mathlib
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.Bundle0001
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.ExistsUnitNorm

@[expose] public section

-- bundled from Formalism.SelfDualUnimodular.LocalLatticeDictionary.AlgebraMapNeZero
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem loc_iff_of_isom (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {L M : Submodule (𝓞 E) (Fin n → E)} {p : Ideal (𝓞 E)}
    (hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ g x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M)
    (γ : GL (Fin n) E) (hγg : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (v : Fin n → E) :
    v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔ ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v := by
  constructor
  · intro hv
    refine ⟨g.symm v, (hm _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hv), ?_⟩
    rw [hγg, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [hγg]; exact (hm w).1 hw

theorem semiGenus_of (hG : SemiGenusLoc) : SemiGenus := by
  intro E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp
  obtain ⟨g, hg, hm⟩ := hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  exact ⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩

theorem algebraMap_ne_zero' {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 :=
  algebraMap_ne_zero_of_mem_hcompl hp ht

theorem smul_eq_alg (t : 𝓞 E) (v : Fin n → E) : t • v = (algebraMap (𝓞 E) E t) • v := by
  rw [algebraMap_smul]

theorem semiGenusZ_of (hZ : SemiGenusZLoc) : SemiGenusZ := by
  intro E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp
  have hpP := hp.isPrime

  have hU' : ∀ w ∈ Submodule.span E (Set.range s),
      w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by
    intro w hw
    change w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M
    constructor
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).1 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).2 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
  have hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup,
        w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by
    intro N hN w hw
    obtain ⟨t, ht, htw⟩ := hw
    obtain ⟨u, huN, hus, hu0⟩ := hN _ htw
    have ht0 := algebraMap_ne_zero' hpP ht
    refine ⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩
    · rw [smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; exact huN
    · have e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u) := by
        rw [smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]
  have hprim : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup → c ∈ locRing p := by
    intro N hN c hc
    obtain ⟨t, ht, htc⟩ := hc
    rw [smul_eq_alg, smul_smul] at htc
    obtain ⟨r, hr⟩ := hN _ htc
    have ht0 := algebraMap_ne_zero' hpP ht
    rw [mem_locRing, mem_locR_iff hpP]
    refine ⟨r, t, ht, ?_⟩
    rw [hr]; field_simp
  have hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup :=
    fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩
  obtain ⟨g, hg, hgs, hgz, hm⟩ := hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
    hsz hU' (hsplit L hSL) (hsplit M hSM) (hzloc L hzL) (hzloc M hzM) (hprim L hPL) (hprim M hPM)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  refine ⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
end
end

-- bundled from Formalism.SelfDualUnimodular.LocalLatticeDictionary.SelfDualRestr
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]

def restr (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (by intro x y z; simp) (by intro c x y; simp) (by intro x y z; simp) (by intro c x y; simp)

def coef (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) : V →ₗ[K] K := (h X X)⁻¹ • h X

theorem coef_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X x : V) : coef h X x = (h X X)⁻¹ * h X x := rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : V →ₗ[K] LinearMap.ker (h X) :=
  LinearMap.codRestrict (LinearMap.ker (h X)) (LinearMap.id - (coef h X).smulRight X) (by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
      smul_eq_mul, coef_apply]
    field_simp
    ring)

theorem proj_val (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    (proj h X hX x : V) = x - coef h X x • X := rfl

theorem coef_self (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : coef h X X = 1 := by
  rw [coef_apply, inv_mul_cancel₀ hX]

theorem coef_ker (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (w : LinearMap.ker (h X)) : coef h X w = 0 := by
  rw [coef_apply, LinearMap.mem_ker.mp w.2, mul_zero]

theorem decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    x = coef h X x • X + (proj h X hX x : V) := by
  rw [proj_val]
  abel

def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) :
    V →ₗ[K] V :=
  (coef h X).smulRight X + (LinearMap.ker (h X)).subtype ∘ₗ (g : _ →ₗ[K] _) ∘ₗ proj h X hX

theorem ext_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g x = coef h X x • X + (g (proj h X hX x) : V) := rfl

theorem coef_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    coef h X (ext h X hX g x) = coef h X x := by
  rw [ext_apply, map_add (f := _), map_smul, coef_self h X hX, coef_ker h X (g (proj h X hX x)), smul_eq_mul,
    mul_one, add_zero]

theorem proj_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    proj h X hX (ext h X hX g x) = g (proj h X hX x) := by
  apply Subtype.ext
  rw [proj_val, coef_ext, ext_apply]
  abel

theorem ext_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g.symm (ext h X hX g x) = x := by
  rw [ext_apply, coef_ext, proj_ext, LinearEquiv.symm_apply_apply]
  exact (decomp h X hX x).symm

def extE (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (ext h X hX g) (ext h X hX g.symm)
    (by
      ext x
      have := ext_comp h X hX g.symm x
      rwa [LinearEquiv.symm_symm] at this)
    (by ext x; exact ext_comp h X hX g x)

theorem extE_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    extE h X hX g x = ext h X hX g x := rfl

theorem h_ker_X (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hs : ∀ u v, star (h u v) = h v u)
    (w : LinearMap.ker (h X)) : h w X = 0 := by
  rw [← hs X w, LinearMap.mem_ker.mp w.2, star_zero]

theorem h_decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (x y : V) :
    h x y = star (coef h X x) * coef h X y * h X X + h (proj h X hX x) (proj h X hX y) := by
  conv_lhs => rw [decomp h X hX x, decomp h X hX y]
  simp only [LinearMap.map_add₂, map_add (f := _), LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [LinearMap.mem_ker.mp (proj h X hX y).2, h_ker_X h X hs (proj h X hX x)]
  ring

theorem extE_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X))
    (hg : ∀ u v, h (g u : V) (g v : V) = h (u : V) (v : V)) (x y : V) :
    h (extE h X hX g x) (extE h X hX g y) = h x y := by
  rw [h_decomp h X hX hs, h_decomp h X hX hs x y, extE_apply, extE_apply, coef_ext, coef_ext, proj_ext,
    proj_ext, hg]

variable {S : Subring K}

theorem mem_iff_split {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M) {X : V}
    (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) (x : V) :
    x ∈ M ↔ coef h X x ∈ S ∧ (proj h X hXu.1 x : V) ∈ M := by
  constructor
  · intro hx
    have hc : coef h X x ∈ S := by
      rw [coef_apply]
      exact S.mul_mem hXu.2.2 (hM.int X hXM x hx)
    refine ⟨hc, ?_⟩
    rw [proj_val]
    exact M.sub_mem hx (hM.smul_mem _ hc X hXM)
  · rintro ⟨hc, hp⟩
    rw [decomp h X hXu.1 x]
    exact M.add_mem (hM.smul_mem _ hc X hXM) hp

theorem selfDual_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {X : V} (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) :
    IsSelfDualMod S (restr h (LinearMap.ker (h X)))
      (M.comap ((LinearMap.ker (h X)).subtype : LinearMap.ker (h X) →ₗ[K] V).toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    change ((a • m : LinearMap.ker (h X)) : V) ∈ M
    rw [Submodule.coe_smul]
    exact hM.smul_mem a ha _ hm
  · exact fun x hx y hy => hM.int _ hx _ hy
  · intro x hx
    change (x : V) ∈ M
    apply hM.dual
    intro m hm
    have hpm : ((proj h X hXu.1 m : LinearMap.ker (h X)) : V) ∈ M := ((mem_iff_split hM hXM hXu m).1 hm).2
    have e : h m x = h (proj h X hXu.1 m) x := by
      conv_lhs => rw [decomp h X hXu.1 m]
      rw [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, LinearMap.mem_ker.1 x.2,
        smul_zero, zero_add]
    rw [e]
    exact hx (proj h X hXu.1 m) hpm
  · intro x
    obtain ⟨t, ht, htx⟩ := hM.span (x : V)
    exact ⟨t, ht, by change ((t • x : LinearMap.ker (h X)) : V) ∈ M; rw [Submodule.coe_smul]; exact htx⟩

theorem nondeg_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {X : V} (hX : h X X ≠ 0) (w : LinearMap.ker (h X))
    (hw : ∀ y, restr h (LinearMap.ker (h X)) w y = 0) : w = 0 := by
  refine Subtype.ext (hnd _ (fun z => ?_))
  rw [decomp h X hX z, map_add (f := _), map_smul, smul_eq_mul, h_ker_X h X hs w, mul_zero, zero_add]
  exact hw (proj h X hX z)

theorem symm_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (W : Submodule K V) :
    (restr h W).IsSymm := by
  first
    | exact fun x y => hsy x y
    | exact ⟨fun x y => hsy.eq x y⟩

theorem selfDual_map {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, h (g x) (g y) = h x y) :
    IsSelfDualMod S h (M.comap (g.symm : V →ₗ[K] V).toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    change g.symm (a • m) ∈ M
    rw [map_smul]; exact hM.smul_mem a ha _ hm
  · intro x hx y hy
    have := hM.int _ hx _ hy
    change h (g.symm x) (g.symm y) ∈ S at this
    rwa [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  · intro x hx
    change g.symm x ∈ M
    apply hM.dual
    intro m hm
    have := hx (g m) (by change g.symm (g m) ∈ M; rwa [LinearEquiv.symm_apply_apply])
    rw [← hg m (g.symm x), LinearEquiv.apply_symm_apply]
    exact this
  · intro x
    obtain ⟨t, ht, htx⟩ := hM.span (g.symm x)
    exact ⟨t, ht, by change g.symm (t • x) ∈ M; rwa [map_smul]⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
end
end

