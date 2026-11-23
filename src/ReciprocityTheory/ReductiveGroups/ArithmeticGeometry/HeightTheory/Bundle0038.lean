module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormLineSectionPow

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightDecompositionLocalTerms
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem finsum_finset_sum_comm' {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by
  first
    | exact finsum_sum_comm s (fun a b => f b a) hf
    | (classical
       induction s using Finset.induction_on with
       | empty => simp
       | insert b s hb ih =>
         simp only [Finset.sum_insert hb]
         rw [finsum_add_distrib (hf b (Finset.mem_insert_self b s))
           ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset
             (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_decomposition_local_terms (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (Function.support fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la).Finite ∧
    (∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.localHeightAtEmbedding (d.wx x) c) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 F + d.delc c * (harmonic d.N : ℝ) / 2 := by
  obtain ⟨hFne, hFx⟩ := d.fZ_and_substituted_ne_zero hd h x hx c F hF
  obtain ⟨κ, hκ, hs⟩ := d.substituted_factorization_exists hd h x hx c F hF
  have hfin := d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs
  have harch := d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs
  rw [(d.height_substituted_eq_finsum hd h x hx c F hF).2]
  set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) -
    Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG
  have hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) =
      fun la => G (FinitePlace.equivHeightOneSpectrum.symm la) := by
    funext la; rw [hfin la]; rfl
  have s1 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne
  have s2 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx
  have s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_
    intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
  have sG : (Function.support G).Finite := ((s1.union s2).union s3).subset (by
    intro v hv; by_contra hn; apply hv
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    simp only [hG, hn.1.1, hn.1.2, hn.2]; ring)
  have hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v := by
    rw [hg]; exact finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (sG.image FinitePlace.equivHeightOneSpectrum).subset (by
      intro la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)
  rw [hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3,
    finsum_sub_distrib s1 s2]
  have hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0 := by
    classical
    have hm := FinitePlace.hasFiniteMulSupport hκ
    set U := hm.toFinset
    have hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U := by
      intro v hv; exact hm.mem_toFinset.mpr hv
    have hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U := by
      intro v hv; apply hsub1; intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
    have hprod := FinitePlace.prod_eq_inv_abs_norm hκ
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub1] at hprod
    rw [finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ,
      ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]
    push_cast
    rw [Real.log_inv]; ring
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK ReciprocityTheory.MultiplicativeHeights.h0
  simp_rw [harch]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp
  linarith [hpf]

theorem height_minMax_eq_sum_heights (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 := by
  have hc := fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)
  have hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la := by
    intro la
    simp only [NlaMM, localHeightAtPrime, Finset.sum_mul]
  have hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg := by
    funext sg
    rfl
  have hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c) := by
    simp only [meanK, Finset.sum_div]
    rw [Finset.sum_comm]
  unfold HgtMM mahlerMeasureHeight
  simp only [hla]
  rw [finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]
  rw [hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]
  simp only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UpSiegel
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem up_siegel (hd : d.AxH 𝒜) (F1 : MvPolynomial (UXVar d.D d.N) K) (deF : ℕ)
    (h1 : 1 ≤ deF) (hle : deF ≤ d.del) (hirr : Irreducible F1) (hx : XHom deF F1)
    (hu : UDegLE ((d.D + 1) * d.del) F1) (hpos : 0 < hT F1) :
    ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K), XHom d.n96 (mapK Q) ∧ UDegLE d.n96' (mapK Q) ∧
      ¬ F1 ∣ mapK Q ∧
      meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) ≤
        -(d.n96 * hT F1 / ((d.D + 2) * deF)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO := by
  classical
  have hF1 : F1 ≠ 0 := hirr.ne_zero
  obtain ⟨sF, hsF, hsFu⟩ := Finset.exists_mem_eq_sup F1.support
    (Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF1)) uDeg
  generalize hudef : F1.support.sup uDeg = u at hsFu
  have hule : u ≤ (d.D + 1) * d.del := hsFu ▸ hu sF hsF
  have hn96 : d.n96 = 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊) := rfl
  have hn : 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del ≤ d.n96 := by
    rw [hn96]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hdeln : d.del ≤ d.n96 := by
    refine le_trans ?_ hn
    rw [show 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del =
      (8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1)) * d.del by ring]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hdn : deF ≤ d.n96 := le_trans hle hdeln
  have hn' : d.n96' = 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del := rfl
  have hun' : u ≤ d.n96' := by
    have : (d.D + 1) * d.del ≤ d.n96' := by
      rw [hn', show 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del =
        (8 * d.n96 * ((d.D + 2) * (d.N + 1))) * ((d.D + 1) * d.del) by ring]
      have : 0 < d.n96 := by omega
      exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hadd : ∀ a ∈ F1.support, ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      a + m ∈ upMono d.D d.N d.n96 d.n96' := by
    intro a ha m hm
    rw [mem_upMono] at hm
    rw [mem_upMono, hups_xDeg_add, hups_uDeg_add, hx a ha]
    have : uDeg a ≤ u := hudef ▸ Finset.le_sup ha
    omega
  have hST : ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      (F1 * MvPolynomial.monomial m 1).support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro m hm s hs
    obtain ⟨a, ha, m', hm', rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hs)
    have : m' = m := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')
    subst this
    exact hadd a ha m' hm
  obtain ⟨b, hbL, hbli, hspan, hdeg⟩ := satDeg_le K F1 hF1 (upMono d.D d.N d.n96 d.n96')
    (upMono d.D d.N (d.n96 - deF) (d.n96' - u)) (upMono d.D d.N d.n96 d.n96').equivFin hST
  have hk : (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card < (upMono d.D d.N d.n96 d.n96').card := by
    rw [card_upMono, card_upMono]; exact hups_cardUX_lt _ _ _ _ _ _ h1 hdn
  obtain ⟨q, hqnot, hmean⟩ := mink_sat K _ _ b hbli hbL hk
  set e := (upMono d.D d.N d.n96 d.n96').equivFin with he
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K),
      Q = ∑ i, MvPolynomial.monomial (e.symm i : UXVar d.D d.N →₀ ℕ) (q i) := ⟨_, rfl⟩
  have hQc : ∀ i, Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) = q i := fun i => by
    rw [hQ, MvPolynomial.coeff_sum, Fintype.sum_eq_single i]
    · simp
    · intro j hj
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hj (e.symm.injective (Subtype.ext h))
  have hQs : Q.support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro s hs
    by_contra h
    rw [MvPolynomial.mem_support_iff, hQ, MvPolynomial.coeff_sum] at hs
    apply hs
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h' => h (h' ▸ (e.symm i).2)
  have hQKs : (mapK Q).support ⊆ upMono d.D d.N d.n96 d.n96' :=
    (MvPolynomial.support_map_subset _ _).trans hQs
  have hQx : XHom d.n96 (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).1
  have hQu : UDegLE d.n96' (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).2
  have hqQ : (fun i => ((q i : 𝓞 K) : K)) =
      fun i => ((Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) : 𝓞 K) : K) :=
    funext fun i => by rw [hQc]
  refine ⟨Q, hQx, hQu, ?_, ?_⟩
  · rintro ⟨P, hP⟩
    have hPS : P.support ⊆ upMono d.D d.N (d.n96 - deF) (d.n96' - u) := fun s hs =>
      hups_cofactor hF1 hx hsF hsFu.symm (hP ▸ hQx) (hP ▸ hQu) s hs
    apply hqnot
    rw [hspan, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun m => P.coeff m, funext fun i => ?_⟩
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hups_coeff_mul_of_supp F1 P _ hPS, ← hP, MvPolynomial.coeff_map, hQc]
  · have hqn : ∀ σ : K →+* ℂ, qnorm σ F1 d.n96 d.n96' Q = qdist σ b (fun i => ((q i : 𝓞 K) : K)) :=
      fun σ => by
        rw [hqQ]
        refine hups_qnorm_eq σ F1 _ _ (fun s hs => mem_upMono.1 hs) hadd ?_ e b hspan Q hQs
        intro P hPx hPu s hs
        have hFσs : (MvPolynomial.map σ F1).support = F1.support :=
          MvPolynomial.support_map_of_injective _ σ.injective
        have hFσ0 : MvPolynomial.map σ F1 ≠ 0 := by
          intro h; apply hF1
          rw [← MvPolynomial.support_eq_empty, ← hFσs, h, MvPolynomial.support_zero]
        exact hups_cofactor hFσ0 (fun t ht => hx t (hFσs ▸ ht)) (hFσs ▸ hsF) hsFu.symm hPx hPu s hs
    simp_rw [hqn]
    refine hmean.trans ?_
    have e4 := hd.rd_le
    have e5 := hups_log_rd_nonneg K
    have hratio := hups_ratio d.D d.N d.n96 d.n96' deF u d.del h1 hle hule hn rfl
    have hdK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    have hkr : (((upMono d.D d.N d.n96 d.n96').card - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card
        : ℕ) : ℝ) = ((upMono d.D d.N d.n96 d.n96').card : ℝ) -
          (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card := Nat.cast_sub hk.le
    have hR : (0 : ℝ) < (((upMono d.D d.N d.n96 d.n96').card -
        (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card : ℕ) : ℝ) :=
      Nat.cast_pos.2 (Nat.sub_pos_of_lt hk)
    generalize ReciprocityTheory.MultiplicativeHeights.latDeg (K := K) (fun _ => 1)
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K (upMono d.D d.N d.n96 d.n96').card) b) b = Ld at hdeg ⊢
    simp only [card_upMono] at hkr hR hdeg ⊢
    generalize ((cardUX d.D d.N d.n96 d.n96' - cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℕ) : ℝ) = R
      at hkr hR ⊢
    generalize (cardUX d.D d.N d.n96 d.n96' : ℝ) = rr at hkr hratio ⊢
    generalize (cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℝ) = kk at hkr hratio hdeg ⊢
    generalize (Module.finrank ℚ K : ℝ) = dK at hdK hdeg e4 e5 ⊢
    generalize hT F1 = h at hpos hdeg ⊢
    have hc : (0 : ℝ) < (d.D + 2) * deF := by positivity
    have e1 : Ld / (dK * R) ≤ -(kk * h) / R := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc Ld * R ≤ -(kk * dK * h) * R := mul_le_mul_of_nonneg_right hdeg hR.le
        _ = _ := by ring
    have e2 : -(kk * h) / R ≤ -(d.n96 * h / ((d.D + 2) * deF)) := by
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hc hR]
      have h' : (d.n96 : ℝ) * R ≤ (d.D + 2) * deF * kk := by rw [hkr]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h' hpos.le]
    have e3 : Real.log R ≤ Real.log rr := Real.log_le_log hR (by
      have : (0 : ℝ) ≤ kk := by
        by_contra hneg
        rw [not_le] at hneg
        nlinarith
      linarith)
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

