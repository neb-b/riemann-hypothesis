module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PListsEx
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.listsEx_of :
    ListsEx := by
  intro F _ _ n χ hχ
  classical
  refine ⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩
  intro τ
  have hc : ((Polynomial.map τ χ).roots.toList).length = n := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]
  have hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0)
      = (Polynomial.map τ χ).roots.toList := by
    apply List.ext_getElem
    · simp [hc]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  show (Polynomial.map τ χ).roots = _
  rw [Fin.univ_val_map, hl, Multiset.coe_toList]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMarkRoots
section
set_option autoImplicit false

noncomputable section

open NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.W2 (rts)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem markRoots_of : MarkRoots := by
  intro p _ D G L ha i₀ v hv hinv P hP
  obtain ⟨i, rfl⟩ := (L.sig v).1 hv
  have hi : i = i₀ := by
    have : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hi
  set φ : G.F →+* ℂ := G.iotaC.comp (L.s i) with hφ
  have hφe : ∀ x : D.F, φ (L.e x) = D.tau i x := fun x => L.s_C i x
  have hcomp : (D.tau i).comp (L.e.symm : G.F →+* D.F) = φ := by
    ext x
    rw [RingHom.comp_apply, ← hφe]
    simp
  have hP' : (map (L.e.symm : G.F →+* D.F) P).coeff 0 ≠ 0 := by
    rw [coeff_map]
    simpa using hP
  have hR : rts (endPol L P) (D.tau i) = Multiset.map (fun z : ℂ => z⁻¹) (map φ P).roots := by
    show rts (invPol (map (L.e.symm : G.F →+* D.F) P)) (D.tau i) = _
    rw [hinv D.F _ hP' (D.tau i)]
    simp only [rts, Polynomial.map_map, hcomp]
  rw [hR]
  have hω : φ (L.e D.ω) = D.ρc := by rw [hφe]; exact D.tau_ω i
  have hρ : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
    intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = D.ρc := ⟨D.ρc.re, Complex.conj_eq_iff_re.mp h⟩
    have h0 := D.ρc_root
    rw [← hr] at h0
    have h1 : r ^ 2 - (D.tr : ℝ) * r + (D.nm : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa [sq] using this
    have h2 : ((D.tr : ℝ) ^ 2 - 4 * (D.nm : ℝ)) < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * r - (D.tr : ℝ))]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω]
  · rw [h]
    have hmap : map (ComplexEmbedding.conjugate φ) P = map (starRingEnd ℂ) (map φ P) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, (IsAlgClosed.splits (map φ P)).roots_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω, hρ]

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolyFnConj
section
set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem conv_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (K : Subgroup H) (f₁ f₂ : H → ℂ) :
    Formalism.UG.conv K (fun g => σ (f₁ g)) (fun g => σ (f₂ g)) = fun g => σ (Formalism.UG.conv K f₁ f₂ g) := by
  funext g
  unfold Formalism.UG.conv
  have h := σ.toAddEquiv.map_finsum
    (fun x : H ⧸ K => f₁ (Quotient.out x) * f₂ ((Quotient.out x)⁻¹ * g))
  simpa [map_mul] using h.symm

private theorem wordFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (w : List J) :
    wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g)) = fun g => σ (wordFn K ψ w f g) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Formalism.UG.conv K (fun g => σ (ψ j g)) (wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g))) = _
    rw [ih, conv_conj]
    rfl

private theorem polyFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (s : List J →₀ ℂ) :
    polyFn K (fun j g => σ (ψ j g)) (wmap σ.toRingHom s) (fun g => σ (f g)) = fun g => σ (polyFn K ψ s f g) := by
  funext g
  unfold polyFn wmap
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finsupp.sum, Finset.sum_apply, map_sum, wordFn_conj]

private theorem wmap_wmul {J : Type} (f : ℂ →+* ℂ) (a s : List J →₀ ℂ) :
    wmap f (wmul a s) = wmul (wmap f a) (wmap f s) := by
  unfold wmul wmap
  have hm : ∀ t : List J →₀ ℂ, Finsupp.mapRange f f.map_zero t =
      Finsupp.mapRange.addMonoidHom f.toAddMonoidHom t := fun t => rfl
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  rw [hm, map_finsuppSum]
  refine Finsupp.sum_congr (fun w _ => ?_)
  rw [map_finsuppSum, Finsupp.sum_mapRange_index (by intro w'; simp)]
  refine Finsupp.sum_congr (fun w' _ => ?_)
  rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  congr 1
  exact map_mul f (a w) (s w')

theorem polyFnConj_of : PolyFnConj := fun σ _ _ _ K ψ f =>
  ⟨wordFn_conj σ K ψ f, polyFn_conj σ K ψ f, wmap_wmul σ.toRingHom⟩

end UpperTheory.Gal.LocalSmoothExtension

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PRootW
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWConj
section
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private lemma roots_map_sigma (σ : ℂ ≃+* ℂ) (p : ℂ[X]) :
    (p.map (σ : ℂ →+* ℂ)).roots = p.roots.map (σ : ℂ →+* ℂ) :=
  (IsAlgClosed.splits p).roots_map _

private lemma sigma_sch (σ : ℂ ≃+* ℂ) {n : ℕ} (μ : Fin n → ℕ) (x : Fin n → ℂ) :
    σ (UpperTheory.Gal.Schur.sch μ x) = UpperTheory.Gal.Schur.sch μ (fun i => σ (x i)) := by
  unfold UpperTheory.Gal.Schur.sch
  exact MvPolynomial.comp_aeval_apply (φ := (σ : ℂ →+* ℂ).toRatAlgHom) x _

theorem UpperTheory.Gal.LocalSmoothExtension.schWConj_of :
    SchWEq → SchWConj := by
  intro hE σ F _ _ n lam χ
  classical
  by_cases h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g
  · obtain ⟨g, hg⟩ := h
    have hg' : Lists χ (fun τ i => σ (g ((σ.symm : ℂ →+* ℂ).comp τ) i)) := by
      intro τ
      have h1 : χ.map τ = (χ.map ((σ.symm : ℂ →+* ℂ).comp τ)).map (σ : ℂ →+* ℂ) := by
        rw [Polynomial.map_map]
        congr 1
        ext x
        simp
      have h2 := hg ((σ.symm : ℂ →+* ℂ).comp τ)
      unfold UpperTheory.Gal.W2.rts at h2 ⊢
      rw [h1, roots_map_sigma, h2, Multiset.map_map]
      rfl
    rw [hE F n (conjWt σ lam) χ _ hg', hE F n lam χ g hg, map_prod]
    let e : (F →+* ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun τ => (σ.symm : ℂ →+* ℂ).comp τ
        invFun := fun τ => (σ : ℂ →+* ℂ).comp τ
        left_inv := fun τ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    refine Fintype.prod_equiv e _ _ fun τ => ?_
    rw [sigma_sch]
    rfl
  · have h0 : schW lam χ = 0 := by
      unfold schW
      exact dif_neg h
    have h1 : schW (conjWt σ lam) χ = 0 := by
      unfold schW
      exact dif_neg h
    rw [h0, h1, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq
section
open UpperTheory.Gal.LocalSmoothExtension

private theorem exists_perm_of_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, b (e i) = a i :=
  _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq a b h

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dite_eq_left h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSpecConj
section
set_option autoImplicit false

open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)
open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

private theorem map_oneP {p : ℕ} [Fact p.Prime] (σ : ℂ ≃+* ℂ) (G : HTGroup p) (x : Gr G 1) :
    σ (oneP G x) = oneP G x := by
  by_cases h : x ∈ (Kp G : Set (Gr G 1))
  · simp [oneP, Set.indicator_of_mem h]
  · simp [oneP, Set.indicator_of_notMem h]

private theorem dTrace_conj {p : ℕ} [Fact p.Prime] (hH : HeckeTraceSemi) (σ : ℂ ≃+* ℂ) (G : HTGroup p)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (ξ' : Representation ℂ (G.Cˣ × ℚˣ) V') (e : V ≃+ V') (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) (K : Subgroup G.GAf) (f : G.GAf → ℂ) :
    dTrace G ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (dTrace G ξ K f (Kp G) (oneP G)) := by
  have hterm : ∀ B : DForm G, B.trace ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (B.trace ξ K f (Kp G) (oneP G)) := by
    intro B
    have h := hH σ (grp G B.β) (G.GAf × Gr G 1) V V' (ξ.comp (grp G B.β).subtype) (ξ'.comp (grp G B.β).subtype) e hs
      (fun g x => hi g.1 x) B.emb (K.prod (Kp G)) (fun h => f h.1 * oneP G h.2)
    have hF : (fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2)) = fun h => σ (f h.1) * oneP G h.2 := by
      funext h
      rw [map_mul, map_oneP]
    rw [hF] at h
    exact h
  unfold dTrace
  have hm := σ.toAddEquiv.map_finsum (fun q : DFCls G => (Quot.out q).trace ξ K f (Kp G) (oneP G))
  calc _ = ∑ᶠ q : DFCls G, σ ((Quot.out q).trace ξ K f (Kp G) (oneP G)) := finsum_congr fun q => hterm _
    _ = _ := hm.symm

theorem UpperTheory.Gal.LocalSmoothExtension.specConj_of :
    TraceSemi → ConjRep → HeckeTraceSemi → GoodConj → SchWConj → PolyFnConj → SpecConj := by
  intro hT hCR hH hG hSW hP σ p _ D G L lam K J ψ θ f hS
  obtain ⟨hcomm, V, i1, i2, i3, ξ, hwt, hsp⟩ := hS
  obtain ⟨V', j1, j2, j3, ξ', e, hse, hint⟩ := hCR σ (G.Cˣ × ℚˣ) V ξ
  have hPf := hP σ G.GAf J K ψ f
  refine ⟨fun j j' w => ?_, V', j1, j2, j3, ξ', ?_, ?_⟩
  · rw [hPf.1, hPf.1, hcomm]
  · intro B y h1 h2
    rw [hSW, ← hwt B y h1 h2]
    exact hT σ V V' e hse (ξ y.1) (ξ' y.1) (fun x => hint y.1 x)
  · intro s' hs'
    obtain ⟨s, rfl⟩ : ∃ s : List J →₀ ℂ, wmap σ.toRingHom s = s' := by
      refine ⟨wmap σ.symm.toRingHom s', ?_⟩
      ext w
      simp [wmap]
    have hw : σ (wop θ s) = wop (fun j => σ (θ j)) (wmap σ.toRingHom s) :=
      UpperTheory.Gal.CertificateRingHomMap.map_wop_wmap σ.toRingHom σ.toRingHom (fun _ => rfl) θ s
    have hne : wop θ s ≠ 0 := by
      intro h0
      apply hs'
      rw [← hw, h0, map_zero]
    obtain ⟨a, hgood, htr⟩ := hsp s hne
    refine ⟨wmap σ.toRingHom a, ?_⟩
    have hc : polyFn K (fun j g => σ (ψ j g)) (wmul (wmap σ.toRingHom a) (wmap σ.toRingHom s)) (fun g => σ (f g)) =
        fun g => σ (polyFn K ψ (wmul a s) f g) := by
      rw [← hPf.2.2, hPf.2.1]
    rw [hc]
    refine ⟨hG σ p G K _ hgood, ?_⟩
    rw [dTrace_conj hH σ G ξ ξ' e hse hint]
    exact fun h0 => htr ((map_eq_zero σ).1 h0)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOf
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOne
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTraceSemi
section
open UpperTheory.Gal.LocalSmoothExtension

private theorem semi_symm {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) : IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [h]
  simp

private theorem exists_basis {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ b' : Module.Basis ι ℂ V', ∀ y i, b'.repr y i = σ (b.repr (e.symm y) i) := by
  refine ⟨Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))
      invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        have hs := semi_symm h c y
        simp [hs]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }, ?_⟩
  intro y i
  rfl

theorem UpperTheory.Gal.LocalSmoothExtension.traceSemi_of :
    TraceSemi := by
  intro σ V V' _ _ _ _ e h T T' hT
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    obtain ⟨b', hb'⟩ := exists_basis h b
    have hbj : ∀ j, b' j = e (b j) := by
      intro j
      apply b'.repr.injective
      rw [b'.repr_self]
      ext k
      rw [hb', AddEquiv.symm_apply_apply, b.repr_self]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [Finsupp.single_apply, hjk]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT,
      AddEquiv.symm_apply_apply]
  · have H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V') := by
      rintro ⟨t, ⟨c⟩⟩
      obtain ⟨c', -⟩ := exists_basis (semi_symm h) c
      exact H ⟨_, ⟨c'.reindexFinsetRange⟩⟩
    simp only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound
section
open UpperTheory.Gal.LocalSmoothExtension

open scoped Classical in
private lemma hexp_finite {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) : {h : Fin n → ℕ | IsHExp t₀ ε lam h}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.toFinite _
  · let i₀ : Fin n := ⟨0, hn⟩
    let c : ℕ := ∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀),
      ε τ * ∑ j, lam τ j
    let h₁ : Fin n → ℕ := fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) +
      (lam t₀ i + (n - 1 - (i : ℕ)))
    let h₂ : Fin n → ℕ := fun i => (lam t₀ i₀ + c) +
      (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))
    refine (Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_
    rintro h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)
    · left
      funext i
      rw [hh i, ← hm i₀]
    · right
      funext i
      rw [hh i, ← hm i₀]

theorem UpperTheory.Gal.LocalSmoothExtension.unifBound_of :
    UnifBound := by
  intro F _ _ n I _ t ε lam κ
  have hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ,
      IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b := by
    intro π i
    obtain ⟨b, hb⟩ := ((hexp_finite (t i) ε (fun τ => lam (π τ))).image
      (κ (fun τ => lam (π τ)) i)).bddAbove
    exact ⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩
  choose b hb using hb
  obtain ⟨k, hk⟩ := Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)
  refine ⟨k, fun σ i h hh => ?_⟩
  exact (hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans
    (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))
end

