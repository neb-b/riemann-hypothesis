module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0035

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LaurentAdjoinEqOfImageEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumRegroup
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MassProductFormula

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality


open Classical in
theorem sum_regroup (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {A : Submodule (𝓞 K) V'} (hAfull : Submodule.IsFullLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0) (hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0)
    (hZA : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    (s : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Finset (Submodule (𝓞 K) V'))
    (hsr : ∀ 𝔭, IsLocReps S L 𝔭.1 (s 𝔭)) :
    ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1 := by
  have hA := hAfull.toIsLattice
  have hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1 := fun 𝔭 h𝔭 =>
    fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)
  have hex : ∀ τ : ↥Z → Submodule (𝓞 K) V', τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) →
      ∃ M, Good F S L M ∧ (∀ 𝔭 : ↥Z, locF 𝔭.1.1 M = τ 𝔭) ∧
        ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
    intro τ hτ
    rw [Fintype.mem_piFinset] at hτ
    obtain ⟨M, hM, h1, h2⟩ := exists_patch hK hF S hLfull hAfull Z
      (fun 𝔭 => if H : 𝔭 ∈ Z then τ ⟨𝔭, H⟩ else ⊥)
      (fun 𝔭 h𝔭 => by
        simp only [dif_pos h𝔭]
        exact ⟨((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).1, ((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).2.2⟩)
      (fun 𝔭 h𝔭 => by rw [hZ1 𝔭 h𝔭]; exact one_ne_zero)
    exact ⟨M, hM, fun 𝔭 => by rw [h1 𝔭.1 𝔭.2, dif_pos 𝔭.2], h2⟩
  choose! M hMg hMZ hMA using hex
  rw [← Finset.prod_coe_sort Z (fun 𝔭 => ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1),
    Finset.prod_univ_sum, Finset.mul_sum]
  have e1 : ∀ τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1),
      c * ∏ 𝔭 : ↥Z, ((fibLoc S L 𝔭.1.1 (τ 𝔭) : ℝ) * lamP h' (τ 𝔭) 𝔭.1.1) =
        ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' (M τ) Λ'),
          (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
    intro τ hτ
    rw [sum_genus hK hF hs hd S hLfull hLi hc hs' hA hAi Z hZ1 hZA (hMg τ hτ) (hMA τ hτ),
      ← Finset.prod_coe_sort Z]
    congr 1
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [hMZ τ hτ 𝔭]
  rw [Finset.sum_congr rfl e1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Λ' hΛ' => ?_
  by_cases hg : Good F S L Λ'
  · have hloc : ∀ 𝔭 : ↥Z, ∃! T₀, T₀ ∈ s 𝔭.1 ∧
        ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = locF 𝔭.1.1 Λ' := fun 𝔭 =>
      (hsr 𝔭.1).2 _ (LocF.locF_idem _ _)
        (isIntegralAt_locF 𝔭.1.2.isPrime hF (hg.integral hF hLfull.toIsLattice hLi))
        (by rw [fibLoc_locF]; exact hg.2 𝔭.1)
    choose τ₀ hτ₀ hu using hloc
    have hmem : τ₀ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) :=
      Fintype.mem_piFinset.mpr fun 𝔭 => (hτ₀ 𝔭).1
    rw [Finset.sum_eq_single τ₀, if_pos]
    · rw [sameGenus_iff hK hF]
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ Z
      · have := (hτ₀ ⟨𝔭, h𝔭⟩).2
        rw [hMZ τ₀ hmem ⟨𝔭, h𝔭⟩]
        exact this
      · exact good_orbit hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭)
          ((hMg τ₀ hmem).2 𝔭) (hg.2 𝔭)
    · intro τ hτ hne
      rw [if_neg]
      intro hsg
      apply hne
      funext 𝔭
      apply hu 𝔭
      refine ⟨Fintype.mem_piFinset.mp hτ 𝔭, ?_⟩
      have := (sameGenus_iff hK hF _ _).mp hsg 𝔭.1
      rwa [hMZ τ hτ 𝔭] at this
    · intro hc'
      exact absurd hmem hc'
  · have hlat := isFullLattice_of_fibReps S hs' hΛ'
    have : ∃ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 Λ' = 0 := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hlat.toIsLattice, hcon⟩
    obtain ⟨𝔭, h𝔭⟩ := this
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi hlat 𝔭 h𝔭]
    simp

theorem repMass_eq_prod_psi' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) =
      c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 := by
  classical
  have hL : Submodule.IsLattice K L := hLfull.toIsLattice
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  rw [repMass_eq_sum_fib hK hs hd S hL hLi hs']
  by_cases H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0
  · obtain ⟨n, hn⟩ := exists_norm_eq hF hs S hLi H
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact S.hx₀ (by rw [hn]; simp)
    have hAfull := StabilizerLattices.isFullLattice_cut S hLfull
    have hAi := isIntegralLat_cut S hLi
    have f1 := finite_vd_ne_zero hK hF hs hd hLfull hLi
    have f2 := finite_vF_ne_zero hn0
    have f3 := finite_vd_ne_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hAfull hAi
    set Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
      f1.toFinset ∪ f2.toFinset ∪ f3.toFinset with hZ
    have hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inl h0))
    have hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inr h0))
    have hZA : ∀ 𝔭 ∉ Z, vd h' (S.cut L) 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inr h0)
    choose T hT using H
    obtain ⟨M₀, hM₀, -, -⟩ := exists_patch hK hF S hLfull hAfull Z (fun 𝔭 => locF 𝔭.1 (T 𝔭))
      (fun 𝔭 _ => ⟨LocF.locF_idem _ _, by rw [fibLoc_locF]; exact hT 𝔭⟩)
      (fun 𝔭 h𝔭 => by
        rw [fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)]
        exact one_ne_zero)
    have hex := fun 𝔭 => exists_locReps hK hF hs hd S hLfull hLi hM₀ 𝔭
    rw [sum_regroup hK hF hs hd S hLfull hLi hc hs' hn hAfull hAi Z hZL hZn hZA
      (fun 𝔭 => (hex 𝔭).choose) (fun 𝔭 => (hex 𝔭).choose_spec)]
    congr 1
    rw [tprod_eq_prod (s := Z) (fun 𝔭 h𝔭 =>
      psiP_eq_one' hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭))]
    exact Finset.prod_congr rfl fun 𝔭 _ => (psiP_eq S L 𝔭.1 (hex 𝔭)).symm
  · push Not at H
    obtain ⟨𝔭, H⟩ := H
    rw [tprod_of_exists_eq_zero ⟨𝔭, psiP_eq_zero S L 𝔭.1 H⟩, mul_zero]
    refine Finset.sum_eq_zero fun Λ' hΛ' => ?_
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi (isFullLattice_of_fibReps S hs' hΛ') 𝔭 (H Λ')]
    simp

end Formalism.HermitianLattices.Ext.L3.MassProductFormula
end
end

