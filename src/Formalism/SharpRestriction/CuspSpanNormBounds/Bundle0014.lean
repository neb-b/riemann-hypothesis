module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVN

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fixF (K : Type) [Field K] [NumberField K] [StarRing K] :
    ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap (cmF K) K) := by
  intro a
  constructor
  · intro h
    exact ⟨⟨a, (mem_cmF_iff K a).2 h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact star_coe_cmF K x

theorem card_quot (hK : IsCMUnram K) :
    Nat.card ((𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range) = 2 ^ fDeg K := by
  rw [Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK),
    (discrTower K (cmF K) hK (fixF K)).2.1]

theorem span_mul_span1 (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem iota_inv (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

theorem iota_ne_zero (x : (𝓞 (cmF K))ˣ) : iota K x ≠ 0 := by
  intro h0
  have := congrArg (iota K) (mul_inv_cancel x)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

theorem star_iota (x : (𝓞 (cmF K))ˣ) : star (iota K x) = iota K x := star_coe_cmF K _

theorem card_classReps_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0)
    (s : Finset (Submodule (𝓞 K) K)) (hs : IsClassReps h (1 : Submodule (𝓞 K) K) s) :
    s.card ≤ classNumber K * 2 ^ fDeg K := by
  classical
  have hlat : ∀ M : s, Submodule.IsFullLattice K (M : Submodule (𝓞 K) K) := by
    intro M
    have := (hs.1 M M.2).1
    obtain ⟨p, hp, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (𝓞 K)) bot_ne_top
    obtain ⟨z, hz, hzloc⟩ := exists_local h h1 (hs.1 M M.2) hp
    have hz0 : z ≠ 0 := by
      intro e
      simp [e] at hz
    have hzm : z ∈ loc (K := K) p (M : Submodule (𝓞 K) K) :=
      (hzloc z).2 ⟨1, one_mem_locR p, one_mul z |>.symm⟩
    obtain ⟨r, hr, hrz⟩ := hzm
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := by
      intro e
      have : r = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by simpa using e)
      subst r
      exact (hcompl_le_primeCompl hp hr) (Ideal.zero_mem p)
    exact ⟨span_eq_top_of_ne_zero hrz (by simpa [Algebra.smul_def] using mul_ne_zero hr0 hz0)⟩
  let cl : s → ClassGroup (𝓞 K) := fun M => ClassGroup.mk K (fracU (hlat M))
  let base : s → s := fun M => Classical.choose (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have hbase : ∀ M, cl (base M) = cl M := fun M =>
    Classical.choose_spec (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have gen : ∀ (γ γ' : ClassGroup (𝓞 K)) (hγ : ∃ B : s, cl B = γ) (hγ' : ∃ B : s, cl B = γ'),
      γ = γ' → Classical.choose hγ = Classical.choose hγ' := by
    intro γ γ' hγ hγ' e
    subst e
    rfl
  have hbase_eq : ∀ M M', cl M = cl M' → base M = base M' := fun M M' e => gen _ _ _ _ e
  have hex : ∀ M : s, ∃ a : K, a ≠ 0 ∧
      (M : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {a} * ((base M : s) : Submodule (𝓞 K) K) :=
    fun M => exists_eq_span_mul (hlat M) (hlat (base M)) (hbase M).symm
  choose a ha0 haM using hex
  have hu : ∀ M : s, ∃ t : (𝓞 (cmF K))ˣ, iota K t = a M * star (a M) := by
    intro M
    obtain ⟨i1, i2⟩ := norm_unit h h1 (hs.1 M M.2) (hs.1 _ (base M).2) (haM M)
    exact exists_unitF (mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))) i1 i2
      (by rw [star_mul', star_star, mul_comm])
  choose t ht using hu
  let Q := (𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range
  let Ψ : s → ClassGroup (𝓞 K) × Q := fun M => (cl M, ((t M : (𝓞 (cmF K))ˣ) : Q))
  have hinj : Function.Injective Ψ := by
    intro M M' e
    have ecl : cl M = cl M' := congrArg Prod.fst e
    have eB : base M = base M' := hbase_eq M M' ecl
    have eq : ((t M : (𝓞 (cmF K))ˣ) : Q) = ((t M' : (𝓞 (cmF K))ˣ) : Q) := congrArg Prod.snd e
    rw [QuotientGroup.eq] at eq
    obtain ⟨v, hv⟩ := eq
    set ν : K := iota K v with hνdef
    have hν0 : ν ≠ 0 := iota_ne_zero v
    have hνs : star ν = ν := star_iota v
    have hv' : ν ^ 2 = (iota K (t M))⁻¹ * iota K (t M') := by
      rw [hνdef, ← map_pow, ← iota_inv, ← map_mul, ← hv, powMonoidHom_apply]
    have hu0 : a M * star (a M) ≠ 0 := mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))
    have key : a M' * star (a M') = a M * star (a M) * ν ^ 2 := by
      rw [← ht M, ← ht M', hv', mul_inv_cancel_left₀ (iota_ne_zero _)]
    set b : K := a M' * (a M * ν)⁻¹ with hbdef
    have hb0 : b ≠ 0 := mul_ne_zero (ha0 M') (inv_ne_zero (mul_ne_zero (ha0 M) hν0))
    have hb : star b * b = 1 := by
      have e : star b * b = (a M' * star (a M')) * (a M * star (a M) * ν ^ 2)⁻¹ := by
        rw [hbdef, star_mul', star_inv₀, star_mul', hνs]
        have hsa : star (a M) ≠ 0 := star_ne_zero.2 (ha0 M)
        field_simp
      rw [e, key, mul_inv_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hν0))]
    let g : K ≃ₗ[K] K := LinearEquiv.smulOfNeZero K K b hb0
    have hg : g ∈ isom h := by
      refine (mem_isom_iff h1 g).2 ?_
      show star (b • (1 : K)) * (b • (1 : K)) = 1
      rw [smul_eq_mul, mul_one]
      exact hb
    obtain ⟨w, hw⟩ := exists_unitK v
    have hwinv : algebraMap (𝓞 K) K ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ν⁻¹ := by
      rw [hνdef, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    have hgM : gmap g (M : Submodule (𝓞 K) K) = M' := by
      rw [gmap_smul, haM M, haM M', ← eB, ← mul_assoc, span_mul_span1]
      have e : b * a M = a M' * ν⁻¹ := by
        rw [hbdef]
        field_simp
        exact mul_div_cancel_right₀ _ (ha0 M)
      rw [e, ← span_mul_span1, mul_assoc, ← hwinv, span_unit_mul]
    have hU := hs.2 M' (hs.1 M' M'.2)
    exact Subtype.ext (hU.unique ⟨M.2, g, hg, hgM⟩ ⟨M'.2, 1, (isom h).one_mem, gmap_one _⟩)
  have hQ : Nat.card Q = 2 ^ fDeg K := card_quot hK
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  have hc := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, hQ, Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), Nat.card_eq_fintype_card,
    Fintype.card_coe] at hc
  exact hc

theorem mass_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) :
    mass h (1 : Submodule (𝓞 K) K) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  unfold mass
  split_ifs with hex
  · refine le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))
    calc ∑ M ∈ hex.choose, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ _M ∈ hex.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      _ = (hex.choose.card : ℝ) := by simp
  · positivity

theorem isLattice_one : Submodule.IsFullLattice K (1 : Submodule (𝓞 K) K) := by
  have : Submodule.IsLattice K (1 : Submodule (𝓞 K) K) := Submodule.IsLattice.of_fg K (by
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton 1)
  exact ⟨span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩

theorem mass_std_one_le (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  have hs := stdForm_isSymm K 1
  have ho := stdLat_isOrtho K 1
  have := finiteDimensional_of_ortho ho
  let φ := LinearEquiv.funUnique (Fin 1) K K
  let h' : K →ₗ⋆[K] K →ₗ[K] K :=
    ((stdForm K 1).comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hφ (x y : Fin 1 → K) : h' (φ x) (φ y) = stdForm K 1 x y := by
    simp [h']
  have hn : h' 1 1 ≠ 0 := by
    simp [h', φ, stdForm_apply]
  have hmap : mapE φ (stdLat K 1) = (1 : Submodule (𝓞 K) K) := by
    change (stdLat K 1).map (φ.restrictScalars (𝓞 K)).toLinearMap = 1
    rw [stdLat, Submodule.map_span, Submodule.one_eq_span, ← Set.range_comp]
    have he : (φ.restrictScalars (𝓞 K)).toLinearMap ∘
        (fun i : Fin 1 => (Pi.single i 1 : Fin 1 → K)) = fun _ => (1 : K) := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      change (Pi.single (0 : Fin 1) 1 : Fin 1 → K) 0 = 1
      exact Pi.single_eq_same _ _
    rw [he, Set.range_const]
  obtain ⟨hex, -, -⟩ := massBasic K (Fin 1 → K) (stdForm K 1) hs
    (trace_pos (isTotPosDef_of_ortho hK hs ho)) (stdLat K 1) (isFullLattice_of_ortho ho)
  have e := (mass_mapE φ hφ hex).2
  rw [hmap] at e
  rw [← e]
  exact mass_le hK h' hn

end Formalism.MainNotions.BridgeLemVN

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeRowsLift
section
noncomputable section

namespace Formalism.MainNotions.BridgeRowsLift

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module Formalism.MainNotions.BridgeLemma

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def rlift_Spl (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V) (P P' : S.V →ₗ[E] S.V) : Prop :=
  LAdj S P P' ∧ (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P ∧ LInt Λ P' ∧ ∀ w y, S.hT (P' w) (P' y) = 0

theorem rlift_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

theorem rlift_spl_of_retr (hcm : Formalism.HermitianLatticesTheory.IsCMUnram E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V)
    (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (P0 : S.V →ₗ[E] S.V) (hid : ∀ x ∈ X, P0 x = x) (hX : ∀ y, P0 y ∈ X) (hint : LInt Λ P0) :
    ∃ P P' : S.V →ₗ[E] S.V, rlift_Spl Λ X P P' ∧ ∀ y, (∀ x ∈ X, S.hT x y = 0) → P0 y = 0 → P y = 0 := by
  obtain ⟨P0', hadj, hint'⟩ := l_adj E S Λ huni P0 hint
  obtain ⟨θ, hθ⟩ := l_theta E hcm
  have hbar : star (θ : E) = ((1 - θ : 𝓞 E) : E) := by
    have : ((1 - θ : 𝓞 E) : E) = 1 - (θ : E) := by simp
    rw [this]
    linear_combination hθ
  have hrev : ∀ x y, S.hT (P0' x) y = S.hT x (P0 y) := by
    intro x y
    rw [← S.herm.eq y (P0' x), ← hadj y x, S.herm.eq]
  have hHX : ∀ y, P0 (P0' y) ∈ X := fun y => hX _
  have hHH : ∀ x y, S.hT (P0 (P0' x)) y = S.hT x (P0 (P0' y)) := by
    intro x y
    rw [hadj, hrev]
  have hzero' : ∀ y, (∀ x ∈ X, S.hT x y = 0) → P0' y = 0 := by
    intro y hy
    refine S.nondeg.2 _ (fun w => ?_)
    rw [← hadj]
    exact hy _ (hX w)
  have hzero : ∀ x ∈ X, P0' x = 0 := fun x hx => hzero' x (fun w hw => hiso w hw x hx)
  refine ⟨P0 - (θ : E) • (P0 ∘ₗ P0'), P0' - star (θ : E) • (P0 ∘ₗ P0'), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    rw [hadj, hHH]
  · intro x hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hzero x hx, map_zero, smul_zero, sub_zero, hid x hx]
  · intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact X.sub_mem (hX y) (X.smul_mem _ (hHX y))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact Λ.sub_mem (hint l hl) (liso_smul_mem Λ θ (hint _ (hint' l hl)))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hbar]
    exact Λ.sub_mem (hint' l hl) (liso_smul_mem Λ (1 - θ) (hint _ (hint' l hl)))
  · intro w y
    have e1 : S.hT (P0' w) (P0' y) = S.hT w (P0 (P0' y)) := hrev _ _
    have e2 : S.hT (P0' w) (P0 (P0' y)) = S.hT w (P0 (P0' y)) := by
      rw [hrev, hid _ (hHX y)]
    have e3 : S.hT (P0 (P0' w)) (P0' y) = S.hT w (P0 (P0' y)) := by
      rw [← hadj, hid _ (hHX w), hHH]
    have e4 : S.hT (P0 (P0' w)) (P0 (P0' y)) = 0 := hiso _ (hHX w) _ (hHX y)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, star_star, RingHom.id_apply]
    rw [e1, e2, e3, e4]
    linear_combination (-(S.hT w (P0 (P0' y)))) * hθ
  · intro y hy h0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [h0, hzero' y hy, map_zero, smul_zero, sub_zero]

section Spl

variable {Λ : Submodule (𝓞 E) S.V} {X : Submodule E S.V} {P P' : S.V →ₗ[E] S.V}

theorem rlift_P'_perp (h : rlift_Spl Λ X P P') {y : S.V} (hy : ∀ x ∈ X, S.hT x y = 0) : P' y = 0 := by
  refine S.nondeg.2 _ (fun w => ?_)
  rw [← h.1]
  exact hy _ (h.2.2.1 w)

theorem rlift_PP' (h : rlift_Spl Λ X P P') (y : S.V) : P (P' y) = 0 := by
  refine S.nondeg.1 _ (fun w => ?_)
  rw [h.1]
  exact h.2.2.2.2.2 _ _

def rlift_R (P P' : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V := LinearMap.id - P - P'

theorem rlift_R_apply (y : S.V) : rlift_R P P' y = y - P y - P' y := rfl

theorem rlift_R_perp (h : rlift_Spl Λ X P P') (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (y : S.V) :
    ∀ x ∈ X, S.hT x (rlift_R P P' y) = 0 := by
  intro x hx
  rw [rlift_R_apply, map_sub, map_sub, hiso x hx _ (h.2.2.1 y), ← h.1, h.2.1 x hx]
  ring

theorem rlift_PR (h : rlift_Spl Λ X P P') (y : S.V) : P (rlift_R P P' y) = 0 := by
  rw [rlift_R_apply, map_sub, map_sub, h.2.1 _ (h.2.2.1 y), rlift_PP' h, sub_self, sub_zero]

theorem rlift_R_X (h : rlift_Spl Λ X P P') (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) {x : S.V} (hx : x ∈ X) :
    rlift_R P P' x = 0 := by
  rw [rlift_R_apply, h.2.1 x hx, rlift_P'_perp h (fun w hw => hiso w hw x hx), sub_self, sub_zero]

theorem rlift_R_of_perp (h : rlift_Spl Λ X P P') {y : S.V} (hy : ∀ x ∈ X, S.hT x y = 0) :
    rlift_R P P' y = y - P y := by
  rw [rlift_R_apply, rlift_P'_perp h hy, sub_zero]

theorem rlift_R_int (h : rlift_Spl Λ X P P') {l : S.V} (hl : l ∈ Λ) : rlift_R P P' l ∈ Λ :=
  Λ.sub_mem (Λ.sub_mem hl (h.2.2.2.1 l hl)) (h.2.2.2.2.1 l hl)

theorem rlift_decomp (y : S.V) : y = P y + rlift_R P P' y + P' y := by
  rw [rlift_R_apply]; abel

end Spl

theorem rlift_three {X : Submodule E S.V} (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    {x w y x' w' y' : S.V} (hx : x ∈ X) (hx' : x' ∈ X) (hw : ∀ v ∈ X, S.hT v w = 0) (hw' : ∀ v ∈ X, S.hT v w' = 0)
    (hyy : S.hT y y' = 0) (hwy : S.hT w y' = 0) (hyw : S.hT y w' = 0) :
    S.hT (x + w + y) (x' + w' + y') = S.hT x y' + S.hT w w' + S.hT y x' := by
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hiso x hx x' hx', hw' x hx, rlift_swap (hw x' hx'), hyy, hwy, hyw]
  ring

theorem rlift_main {X : Submodule E S.V} (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (hu₁ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ₁) (hu₂ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ₂)
    {P₁ P₁' P₂ P₂' : S.V →ₗ[E] S.V} (h₁ : rlift_Spl Λ₁ X P₁ P₁') (h₂ : rlift_Spl Λ₂ X P₂ P₂')
    {z : S.V} (hzX : ∀ x ∈ X, S.hT x z = 0) (hz₁ : P₁ z = 0) (hz₂ : P₂ z = 0)
    (hA : ∀ x ∈ X, x ∈ Λ₁ ↔ x ∈ Λ₂)
    (hL : ∀ l ∈ Λ₁, (∀ x ∈ X, S.hT x l = 0) → ∃ l₂ ∈ Λ₂, l - l₂ ∈ X) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ x ∈ X, n x = x) ∧ n z = z ∧
      (∀ y, (∀ x ∈ X, S.hT x y = 0) → n y - y ∈ X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  set nL : S.V →ₗ[E] S.V := P₁ + rlift_R P₂ P₂' ∘ₗ rlift_R P₁ P₁' + P₂' ∘ₗ P₁' with hnL
  have hn : ∀ a, nL a = P₁ a + rlift_R P₂ P₂' (rlift_R P₁ P₁' a) + P₂' (P₁' a) := fun a => rfl
  have hmem : ∀ (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → ∀ y,
      y ∈ Λ ↔ ∀ l ∈ Λ, S.hT l y ∈ (1 : Submodule (𝓞 E) E) := by
    intro Λ hu y
    conv_lhs => rw [← hu]
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  have hisom : ∀ a b, S.hT (nL a) (nL b) = S.hT a b := by
    intro a b
    have hwa := rlift_R_perp h₁ hiso a
    have hwb := rlift_R_perp h₁ hiso b
    have e1 : S.hT (nL a) (nL b) = S.hT (P₁ a) (P₂' (P₁' b)) +
        S.hT (rlift_R P₂ P₂' (rlift_R P₁ P₁' a)) (rlift_R P₂ P₂' (rlift_R P₁ P₁' b)) + S.hT (P₂' (P₁' a)) (P₁ b) := by
      rw [hn, hn]
      refine rlift_three hiso (h₁.2.2.1 a) (h₁.2.2.1 b) (rlift_R_perp h₂ hiso _) (rlift_R_perp h₂ hiso _)
        (h₂.2.2.2.2.2 _ _) ?_ ?_
      · rw [← h₂.1, rlift_PR h₂, map_zero, LinearMap.zero_apply]
      · refine rlift_swap ?_
        rw [← h₂.1, rlift_PR h₂, map_zero, LinearMap.zero_apply]
    have e2 : S.hT a b = S.hT (P₁ a) (P₁' b) + S.hT (rlift_R P₁ P₁' a) (rlift_R P₁ P₁' b) + S.hT (P₁' a) (P₁ b) := by
      conv_lhs => rw [rlift_decomp (P := P₁) (P' := P₁') a, rlift_decomp (P := P₁) (P' := P₁') b]
      refine rlift_three hiso (h₁.2.2.1 a) (h₁.2.2.1 b) hwa hwb (h₁.2.2.2.2.2 _ _) ?_ ?_
      · rw [← h₁.1, rlift_PR h₁, map_zero, LinearMap.zero_apply]
      · refine rlift_swap ?_
        rw [← h₁.1, rlift_PR h₁, map_zero, LinearMap.zero_apply]
    have e3 : ∀ x ∈ X, ∀ y, S.hT x (P₂' y) = S.hT x y := by
      intro x hx y
      rw [← h₂.1, h₂.2.1 x hx]
    have e4 : ∀ x ∈ X, ∀ y, S.hT (P₂' y) x = S.hT y x := by
      intro x hx y
      rw [← S.herm.eq x (P₂' y), e3 x hx, S.herm.eq]
    have e5 : S.hT (rlift_R P₂ P₂' (rlift_R P₁ P₁' a)) (rlift_R P₂ P₂' (rlift_R P₁ P₁' b)) =
        S.hT (rlift_R P₁ P₁' a) (rlift_R P₁ P₁' b) := by
      rw [rlift_R_of_perp h₂ hwa, rlift_R_of_perp h₂ hwb]
      simp only [map_sub, LinearMap.sub_apply]
      rw [hwb _ (h₂.2.2.1 _), rlift_swap (hwa _ (h₂.2.2.1 (rlift_R P₁ P₁' b))), hiso _ (h₂.2.2.1 _) _ (h₂.2.2.1 _)]
      ring
    rw [e1, e2, e3 _ (h₁.2.2.1 a), e4 _ (h₁.2.2.1 b), e5]
  have hinj : Function.Injective nL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    refine S.nondeg.1 _ (fun b => ?_)
    rw [← hisom, ha, map_zero, LinearMap.zero_apply]
  set n : S.V ≃ₗ[E] S.V := LinearEquiv.ofInjectiveEndo nL hinj with hndef
  have hnn : ∀ a, n a = nL a := fun a => congrFun (LinearEquiv.coe_ofInjectiveEndo nL hinj) a
  have hX : ∀ x ∈ X, nL x = x := by
    intro x hx
    rw [hn, h₁.2.1 x hx, rlift_R_X h₁ hiso hx, map_zero, rlift_P'_perp h₁ (fun w hw => hiso w hw x hx), map_zero,
      add_zero, add_zero]
  have hperp : ∀ y, (∀ x ∈ X, S.hT x y = 0) → nL y = y - P₂ (rlift_R P₁ P₁' y) := by
    intro y hy
    rw [hn, rlift_P'_perp h₁ hy, map_zero, add_zero, rlift_R_of_perp h₂ (rlift_R_perp h₁ hiso y), rlift_R_of_perp h₁ hy]
    abel
  have hsub : ∀ l ∈ Λ₁, nL l ∈ Λ₂ := by
    intro l hl
    rw [hn]
    refine Λ₂.add_mem (Λ₂.add_mem ?_ ?_) ?_
    · exact (hA _ (h₁.2.2.1 l)).1 (h₁.2.2.2.1 l hl)
    · obtain ⟨l₂, hl₂, hx⟩ := hL _ (rlift_R_int h₁ hl) (rlift_R_perp h₁ hiso l)
      have : rlift_R P₂ P₂' (rlift_R P₁ P₁' l) = rlift_R P₂ P₂' l₂ := by
        rw [← sub_eq_zero, ← map_sub]
        exact rlift_R_X h₂ hiso hx
      rw [this]
      exact rlift_R_int h₂ hl₂
    · rw [hmem Λ₂ hu₂]
      intro l' hl'
      rw [← h₂.1]
      exact (hmem Λ₁ hu₁ _).1 (h₁.2.2.2.2.1 l hl) _ ((hA _ (h₂.2.2.1 l')).2 (h₂.2.2.2.1 l' hl'))
  refine ⟨n, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hnn, hnn]
    exact hisom a b
  · intro x hx
    rw [hnn]
    exact hX x hx
  · rw [hnn, hperp z hzX, rlift_R_of_perp h₁ hzX, hz₁, sub_zero, hz₂, sub_zero]
  · intro y hy
    rw [hnn, hperp y hy, sub_sub_cancel_left]
    exact X.neg_mem (h₂.2.2.1 _)
  · ext y
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      change n l ∈ Λ₂
      rw [hnn]
      exact hsub l hl
    · intro hy
      refine ⟨n.symm y, ?_, by change n (n.symm y) = y; simp⟩
      rw [hmem Λ₁ hu₁]
      intro l hl
      have : S.hT l (n.symm y) = S.hT (nL l) y := by
        rw [← hisom, ← hnn (n.symm y), LinearEquiv.apply_symm_apply]
      rw [this]
      exact (hmem Λ₂ hu₂ y).1 hy _ (hsub l hl)

end Formalism.MainNotions.BridgeRowsLift

end
end

