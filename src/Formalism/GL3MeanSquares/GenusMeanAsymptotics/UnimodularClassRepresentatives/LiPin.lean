module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepRatioEqZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0030
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0046

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace PinD

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero (algebraMap F K)).2 hnF
  set S₁ := unscale hc S with hS₁
  have hx1 : h S₁.x₀ S₁.x₀ = 1 := by
    have e := hx
    rw [smul_form_apply] at e
    exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
  have hs : h.IsSymm := isSymm_of_smul hF hc hs'
  have hd : IsTotPosDef h := isTotPosDef_of_smul hK hF hs hd' hx1
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 := fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have exists_full : ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧ S₁.x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
    open Cell LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA in
    have aux {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n))
        (hn : n ∉ 𝔭) : ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
          Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧ x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
      let ι := algebraMap (𝓞 F) (𝓞 K)
      let κ := algebraMap (𝓞 K) K
      have hp := h𝔭.isPrime
      have hp0 := ne_bot h𝔭
      have han := LocF.aniso_of_totPosDef hd
      have κι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : κ (ι t) ≠ 0 := by
        intro h0
        apply ht
        have hι := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero κ).symm)
        exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (hι.trans (map_zero ι).symm)
      have hx0 : x₀ ≠ 0 := by
        rintro rfl
        rw [map_zero] at hx
        exact κι_ne_zero (ne_zero_of_notMem hn) hx.symm
      have hm : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩
      obtain ⟨r, hr⟩ : ∃ r, finrank K V = r + 1 := ⟨finrank K V - 1, by omega⟩
      have symm0 {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
        have e : starRingEnd K (h x y) = h y x := by
          first
          | exact hs.eq x y
          | exact hs x y
        rw [hxy, map_zero] at e
        exact e.symm
    
      have form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
          h (μ • x) (ν • y) = star μ * ν * h x y := by
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
        ring
    
      have exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
          (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
          ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
        have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
        have hds : star (h e e) = h e e := by
          have e' : starRingEnd K (h e e) = h e e := by
            first
            | exact hs.eq e e
            | exact hs e e
          rwa [starRingEnd_apply] at e'
        obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
        exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩
    
      have exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
          {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
          (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
          (hap : a ∈ 𝔭) :
          ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
            h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
        have hez := symm0 hs hze
        obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
        have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
        set W := c * ν + a with hW
        have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
        have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
        have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
        obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
          (by simpa using hW2) (by simpa using hW3)
        obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
          (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
        have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
        refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
          ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
        · rw [form_smul_smul, hμ₁s, ← hb₁]
          congr 1
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
          linear_combination κ (ι c) * hν'
        · rw [form_smul_smul, hμ₂s, ← hb₂]
          congr 1
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
          linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
        · rw [form_smul_smul]
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
          ring
        · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
            smul_eq_mul, hzv, hev, mul_zero, add_zero]
        · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
            smul_eq_mul, hzv, hev, mul_zero, add_zero]
    
      have κι_inj {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by
        have e : ∀ c : 𝓞 F, κ (ι c) = algebraMap F K (c : F) := fun c => rfl
        rw [e, e] at hab
        exact RingOfIntegers.ext ((algebraMap F K).injective hab)
    
      have exists_family_local : ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
          (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
          (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
          (z = x₀ ∨ ∃ i, y i = x₀) := by
        have hp := h𝔭.isPrime
        intro r
        induction r with
        | zero =>
          intro _
          refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
            fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
          rw [Finset.univ_eq_empty, Finset.prod_empty]
          exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        | succ r ih =>
          intro hr
          obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
          obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
            (by omega)
          obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
          have hze : h z (μ • e₀) = 0 := by
            have := hoe 0
            rw [Fin.cons_zero] at this
            rw [map_smul, this, smul_zero]
          have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
            have := hoe i.succ
            rw [Fin.cons_succ] at this
            rw [map_smul, this, smul_zero]
          set e := μ • e₀ with he
          have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
              b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
              (u = x₀ ∨ ∃ i, y i = x₀) := by
            by_cases hcp : c ∈ 𝔭
            · have hx₀' : ∃ i, y i = x₀ := by
                rcases hx₀ with rfl | h1
                · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
                · exact h1
              by_cases hap : ae ∈ 𝔭
              · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
                  exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
                exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
                  fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
              · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
                  fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
            · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
                fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
          obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
          refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
          · intro i j
            refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
            · intro hij; exact absurd rfl hij
            · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
            · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
            · intro hij
              rw [Fin.cons_succ, Fin.cons_succ]
              exact ho i j fun hh => hij (by rw [hh])
          · intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · rw [Fin.cons_zero]; exact h5
            · rw [Fin.cons_succ]; exact (h6 i).2
          · intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
            · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
          · rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
          · rcases h7 with rfl | ⟨i, hi⟩
            · exact ⟨0, by rw [Fin.cons_zero]⟩
            · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩
      obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ :=
        exists_family_local r (by omega)
      have hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0 := by
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact absurd rfl hij
        · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact hzy j
        · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (hzy i)
        · intro hij
          rw [Fin.cons_succ, Fin.cons_succ]
          exact ho i j fun hh => hij (by rw [hh])
      have hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) =
          κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i)) := by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [Fin.cons_zero, Fin.cons_zero]; exact hnz
        · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
      have hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2 := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hc2' : c ∉ 𝔭 ^ (1 + 1) := by simpa using hc2
        have hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1) := by simpa using hprod
        have := mul_notMem hp hp0 hc2' hprod'
        simpa using this
      have hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0 := by
        intro i
        rw [hnf]
        refine κι_ne_zero fun h0 => hP ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
        exact zero_mem _
      obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne
      refine ⟨spanO e, { toIsLattice := isLattice_spanO e, span_eq_top := ?_ },
        integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
          (fun i => by rw [he]; exact hnf i), ?_,
        vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
          (fun i => by rw [he]; exact hnf i) hP⟩
      · change Submodule.span K (Submodule.span (𝓞 K) (Set.range e) : Set V) = ⊤
        rw [Submodule.span_span_of_tower, e.span_eq]
      · rcases hx₀ with rfl | ⟨i, hi⟩
        · exact Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩
        · exact Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩
    apply aux (n := 1)
    · simpa using hx1
    · exact h1𝔭
  obtain ⟨L₀, hLf, hLi, hxL, hvd⟩ := exists_full
  have hL : Submodule.IsLattice K L₀ := hLf.toIsLattice
  have hs₁' : h'.IsSymm := S₁.isSymm hs
  have hd₁' : IsTotPosDef h' := S₁.isTotPosDef hd
  have hsc' := S.isSymm hs'
  have hdc' := S.isTotPosDef hd'
  have hCf := StabilizerLattices.isFullLattice_cut S₁ hLf
  have hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S₁.cut L₀) := Formalism.HermitianLattices.Ext.L3.UnimodularLocalization.isIntegralLat_cut S₁ hLi
  have hvdC : vd h' (S₁.cut L₀) 𝔭 = vd h L₀ 𝔭 := PinC.vd_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭
  have hm := S₁.finrank_add_one
  have hLic := PinA.isIntegralLat_smul hLi n
  have hCic := PinA.isIntegralLat_smul hCi n
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hsplit : alphaL h L₀ 𝔭 = alphaN h L₀ 𝔭 1 * alphaL h' (S₁.cut L₀) 𝔭 :=
    alphaL_split hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hαpos : 0 < alphaL h L₀ 𝔭 := alphaL_pos hK hF hs hd hLf hLi h𝔭
  have hαC : 0 < alphaL h' (S₁.cut L₀) 𝔭 := alphaL_pos hK hF hs₁' hd₁' hCf hCi h𝔭
  have hαN : alphaN h L₀ 𝔭 1 ≠ 0 := by
    intro h0
    rw [hsplit, h0, zero_mul] at hαpos
    exact lt_irrefl _ hαpos
  have hNsm : alphaN (algebraMap F K (n : F) • h) L₀ 𝔭 n =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 n * alphaN h L₀ 𝔭 1 := by
    have e := alphaN_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd' (by omega) one_ne_zero
    rwa [mul_one] at e
  have hLsm := alphaL_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd'
  have hvsm := PinA.vd_smul hK hF hs hd hLf hLi h𝔭 hn
  have hvT : vd (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      vd h' (S₁.cut L₀) 𝔭 + finrank K V' * vF 𝔭 n := by
    rw [vd_locF hK hF hsc' hdc' hCf.toIsLattice hCic h𝔭]
    exact PinA.vd_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn
  have hαT : alphaL (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 n * finrank K V' ^ 2) * alphaL h' (S₁.cut L₀) 𝔭 := by
    rw [← alphaL_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn hsc' hdc']
    unfold alphaL
    simp only [akCount_locF hF _ (S₁.cut L₀) 𝔭 h𝔭]
  have hrep : IsLocReps S₁ L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} :=
    PinC.isLocReps_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hrep' : IsLocReps S L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} := isLocReps_scale hF hc S hL hLi h𝔭 hrep
  have hpsi : psiP S L₀ 𝔭 = lamP (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 := by
    rw [psiP_eq_sum hK hF hs' hd' S hL hLic h𝔭 hrep', Finset.sum_singleton, fibLoc_unscale hc,
      PinC.fibLoc_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd]
    simp
  refine ⟨L₀, hLf, hLic, ?_, ?_⟩
  · unfold repRatio
    rw [hNsm, hLsm]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (mul_ne_zero (pow_ne_zero _ hN) hαN))
      (mul_ne_zero (pow_ne_zero _ hN) hαpos.ne')
  · rw [hpsi]
    unfold lamP repRatio
    rw [hvT, hαT, hNsm, hLsm, hvsm, hsplit, hvdC, ← hm, Nat.add_sub_cancel]
    have hA := hαC.ne'
    field_simp
    ring

end PinD

theorem liPin : LIPin := by
  unfold LIPin
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S 𝔭 n hs hd h𝔭 hn hx
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero _).2 hnF
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : V →ₗ⋆[K] V →ₗ[K] K, algebraMap F K (n : F) • h₀ = h :=
    ⟨(algebraMap F K (n : F))⁻¹ • h, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨h₀', rfl⟩ : ∃ h₀' : V' →ₗ⋆[K] V' →ₗ[K] K, algebraMap F K (n : F) • h₀' = h' :=
    ⟨(algebraMap F K (n : F))⁻¹ • h', by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  exact PinD.core hK hF n hn S hs hd h𝔭 hx

end Formalism.HermitianLattices.Ext.L3
