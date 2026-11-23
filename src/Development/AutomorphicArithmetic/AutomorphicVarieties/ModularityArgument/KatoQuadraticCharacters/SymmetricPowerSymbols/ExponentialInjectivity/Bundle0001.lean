module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.GalNear

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.Cancel
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.cancel :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω), admitted X τ s → admitted X τ' s' →
        ∀ (u v : X.K) (P Q R : Pt X m), IsPt X m u v P → IsPt X m (τ u) (τ v) Q → IsPt X m (τ' (τ u)) (τ' (τ v)) R →
          ∀ f, Mv X m τ s P Q 1 → Mv X m (τ.trans τ') (s' * s) P R f → Mv X m τ' s' Q R f := by
  intro Ω _ _ _ ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR f h1 hf
  obtain ⟨-, -, -, htr, -⟩ := admB Ω ε X
  obtain ⟨g, -, hg⟩ := (mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).1 R hR
  have hc := mvComp Ω ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR 1 g h1 hg
  rw [map_one, one_pow, one_mul] at hc
  have hfg := ((mvEx Ω ε X m hm (τ.trans τ') (s' * s) (htr τ s τ' s' hτ hτ') u v P hP).2.2.2 R hR g f hc).1 hf
  exact ((mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).2.2.2 R hR g f hg).2 hfg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.Imports
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.coc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s s' x y, Ok x y → Cgr m (w (s * s') x y) (w s x y * tw X m M s (w s') x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw s s' x y hxy
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  set x1 := gr M s⁻¹ x
  set y1 := gr M s⁻¹ y
  have hxy1 : Ok x1 y1 := (hok x y hxy).2.2.1 s⁻¹
  have hxy2 : Ok (gr M s'⁻¹ x1) (gr M s'⁻¹ y1) := (hok x1 y1 hxy1).2.2.1 s'⁻¹
  have ex : gr M (s * s')⁻¹ x = gr M s'⁻¹ x1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have ey : gr M (s * s')⁻¹ y = gr M s'⁻¹ y1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have w1 := (hw s' x1 y1 hxy1).2
  have w2 := (hw s x y hxy).2
  have w3 := (hw (s * s') x y hxy).2
  rw [ex, ey] at w3
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have gs : ∀ (r : Gal(Ω/ℚ)) (a b : Row M), Ok a b → (X.gal r) (sg X c M a) = sg X c M (gr M r a) ∧ (X.gal r) (sg X d M b) = sg X d M (gr M r b) := by
    intro r a b hab
    exact ⟨(sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).2.2.1 r, (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).2.2.1 r⟩
  have inv1 : ∀ (r : Gal(Ω/ℚ)) (a : Row M), gr M r (gr M r⁻¹ a) = a := by
    intro r a
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 a).2]
  have q1 : IsPt X m ((X.gal s') (sg X c M (gr M s'⁻¹ x1))) ((X.gal s') (sg X d M (gr M s'⁻¹ y1))) (t (sg X c M x1) (sg X d M y1)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1]
    exact pt _ _ hxy1
  have q2 : IsPt X m ((X.gal s) ((X.gal s') (sg X c M (gr M s'⁻¹ x1)))) ((X.gal s) ((X.gal s') (sg X d M (gr M s'⁻¹ y1)))) (t (sg X c M x) (sg X d M y)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1, (gs s _ _ hxy1).1, (gs s _ _ hxy1).2, inv1, inv1]
    exact pt _ _ hxy
  have comp := mvComp Ω ε X m hm (X.gal s') (X.gal s) s' s (hadm s') (hadm s) _ _ _ _ _ (pt _ _ hxy2) q1 q2 _ _ w1 w2
  have eg : (X.gal s').trans (X.gal s) = X.gal (s * s') := by
    ext f
    rw [gal_mul_apply]
    rfl
  rw [eg] at comp
  have u := ((mvEx Ω ε X m hm (X.gal (s * s')) (s * s') (hadm _) _ _ _ (pt _ _ hxy2)).2.2.2 _ ?_ _ _ comp).1 w3
  · unfold tw
    rw [mul_comm (w s x y)]
    exact u
  · rw [gal_mul_apply, gal_mul_apply]
    exact q2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsAlt
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.eqv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s, Eqv X m M (w s) := by
  classical
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w hT hW s x y hxy
  refine ⟨(hW s x y hxy).1, fun γ => ?_⟩
  have hR := rowB Ω M hL.1
  have hSg := sgB Ω ε X
  have hAd := admB Ω ε X
  have hUτ : ∀ (τ : X.K ≃+* X.K) (s' : Gal(Ω/ℚ)), admitted X τ s' → ∀ a, IsU X a → IsU X (τ a) :=
    fun τ s' h => (hAd.2.2.2.2.2.1 τ s' h).1
  have hgr : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
    intro z
    rw [← (hR.1 s s⁻¹ z).1, mul_inv_cancel, (hR.1 1 1 z).2]
  have hok0 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hR.2.1 x y hxy).2.2.1 s⁻¹
  have hokγ : Ok (rt x γ) (rt y γ) := (hR.2.1 x y hxy).2.2.2 γ
  have hok1 : Ok (gr M s⁻¹ (rt x γ)) (gr M s⁻¹ (rt y γ)) := (hR.2.1 _ _ hokγ).2.2.1 s⁻¹
  have sx0 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok0).1
  have sy0 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok0).2.1
  have sx := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hxy).1
  have sy := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hxy).2.1
  have sxγ := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hokγ).1
  have syγ := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hokγ).2.1
  have sx1 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok1).1
  have sy1 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok1).2.1
  have ga_u : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by rw [sx0.2.2.1 s, hgr]
  have ga_v : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by rw [sy0.2.2.1 s, hgr]
  have hP := (hT _ _ sx0.1 sy0.1).1
  obtain ⟨S, hSn⟩ := mvNear Ω ε X m hm _ _ _ hP
  obtain ⟨γ', hγ'⟩ := recip Ω ε X s γ
    (insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S))
  have hB : IsPt X m (sg X c M (rt x γ)) (sg X d M (rt y γ))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) := (hT _ _ sxγ.1 syγ.1).1
  have h2 := (hT _ _ sx.1 sy.1).2 γ
  rw [sx.2.1 γ, sy.2.1 γ] at h2
  have p1 := mvComp Ω ε X m hm (X.gal s) (slR X (ofSL γ)) s 1 (hAd.2.1 s) (hAd.1 _) _ _ _ _ _ hP
    (by rw [ga_u, ga_v]; exact (hT _ _ sx.1 sy.1).1)
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ (hW s x y hxy).2 h2
  have a1 := hAd.2.2.2.1 _ _ _ _ (hAd.2.1 s) (hAd.1 (ofSL γ))
  rw [one_mul] at a1 p1
  have e_u : X.sl (ofSL γ') (sg X c M (gr M s⁻¹ x)) = sg X c M (gr M s⁻¹ (rt x γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_u, sx.2.1 γ, sx1.2.2.1 s, hgr]
  have e_v : X.sl (ofSL γ') (sg X d M (gr M s⁻¹ y)) = sg X d M (gr M s⁻¹ (rt y γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_v, sy.2.1 γ, sy1.2.2.1 s, hgr]
  have h3 := (hT _ _ sx0.1 sy0.1).2 γ'
  rw [e_u, e_v] at h3
  have p2 := mvComp Ω ε X m hm (slR X (ofSL γ')) (X.gal s) 1 s (hAd.1 _) (hAd.2.1 s) _ _ _ _ _ hP
    (by
      change IsPt X m (X.sl (ofSL γ') _) (X.sl (ofSL γ') _) _
      rw [e_u, e_v]
      exact (hT _ _ sx1.1 sy1.1).1)
    (by
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ h3 (hW s (rt x γ) (rt y γ) hokγ).2
  have a2 := hAd.2.2.2.1 _ _ _ _ (hAd.1 (ofSL γ')) (hAd.2.1 s)
  rw [mul_one] at a2 p2
  rw [map_one, one_pow, one_mul] at p2
  have hfix : ∀ f ∈ insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S),
      (((X.gal s).trans (slR X (ofSL γ))).trans ((slR X (ofSL γ')).trans (X.gal s)).symm) f = f := by
    intro f hf
    rw [RingEquiv.trans_apply]
    have k : ((X.gal s).trans (slR X (ofSL γ))) f = ((slR X (ofSL γ')).trans (X.gal s)) f := hγ' f hf
    rw [k, RingEquiv.symm_apply_apply]
  have aρ := hAd.2.2.2.1 _ _ _ _ a1 (hAd.2.2.2.2.1 _ _ a2)
  rw [inv_mul_cancel] at aρ
  have near := hSn _ 1 aρ (fun f hf => hfix f (by simp [hf]))
  have p3 := mvComp Ω ε X m hm _ ((slR X (ofSL γ')).trans (X.gal s)) 1 s aρ a2 _ _ _ _ _ hP
    (by rw [hfix _ (by simp), hfix _ (by simp)]; exact hP)
    (by
      rw [hfix _ (by simp), hfix _ (by simp)]
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ near p2
  rw [map_one, one_pow, one_mul, mul_one] at p3
  have htr : ((((X.gal s).trans (slR X (ofSL γ))).trans
      ((slR X (ofSL γ')).trans (X.gal s)).symm).trans ((slR X (ofSL γ')).trans (X.gal s)))
      = (X.gal s).trans (slR X (ofSL γ)) := by
    ext f
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rw [htr] at p3
  have hC := ((mvEx Ω ε X m hm _ s a1 _ _ _ hP).2.2.2 _
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ p3).mp p1
  rw [mul_one] at hC
  have hu : (unU X (slR X (ofSL γ))) (w s x y) = slU X (ofSL γ) (w s x y) := Units.ext rfl
  rw [hu] at hC
  rcases Nat.lt_or_ge 1 m with h1m | h1m
  · haveI : Fact (1 < m) := ⟨h1m⟩
    have hcyc := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
    rw [hcyc, ZMod.val_one, pow_one] at hC
    exact hC
  · obtain rfl : m = 1 := by omega
    exact ⟨(w s (rt x γ) (rt y γ))⁻¹ * slU X (ofSL γ) (w s x y), by group⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsBis
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.loc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∃ T : Finset Ω, ∀ s s', (∀ z ∈ T, s z = s' z) → ∀ x y, Ok x y → Cgr m (w s x y) (w s' x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  classical
  haveI : NeZero M := ⟨by omega⟩
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have loc : ∀ a b : Row M, ∃ T : Finset Ω, ∀ r : Gal(Ω/ℚ), (∀ z ∈ T, r z = z) → Ok a b →
      (X.gal r) (sg X c M a) = sg X c M a ∧ (X.gal r) (sg X d M b) = sg X d M b ∧
      Mv X m (X.gal r) r (t (sg X c M a) (sg X d M b)) (t (sg X c M a) (sg X d M b)) 1 := by
    intro a b
    by_cases hab : Ok a b
    · obtain ⟨T1, h1⟩ := PC.galNear Ω ε X (sg X c M a)
      obtain ⟨T2, h2⟩ := PC.galNear Ω ε X (sg X d M b)
      obtain ⟨S, hS⟩ := mvNear Ω ε X m hm _ _ _ (pt a b hab)
      let Tf : X.K → Finset Ω := fun f => Classical.choose (PC.galNear Ω ε X f)
      refine ⟨T1 ∪ T2 ∪ S.biUnion Tf, fun r hr _ => ⟨h1 r (fun z hz => hr z (by simp [hz])), h2 r (fun z hz => hr z (by simp [hz])), ?_⟩⟩
      refine hS _ r (hadm r) (fun f hf => ?_)
      exact Classical.choose_spec (PC.galNear Ω ε X f) r (fun z hz => hr z (by simp only [Finset.mem_union, Finset.mem_biUnion]; exact Or.inr ⟨f, hf, hz⟩))
    · exact ⟨∅, fun r _ h => absurd h hab⟩
  let G : Row M × Row M → Finset Ω := fun p => Classical.choose (loc p.1 p.2)
  refine ⟨Finset.univ.biUnion G, ?_⟩
  intro s s' hss x y hxy
  set r := s'⁻¹ * s
  set a := gr M s⁻¹ x
  set b := gr M s⁻¹ y
  have hab : Ok a b := (hok x y hxy).2.2.1 s⁻¹
  have hr : ∀ z ∈ G (a, b), r z = z := by
    intro z hz
    have := hss z (Finset.mem_biUnion.2 ⟨(a, b), Finset.mem_univ _, hz⟩)
    show s'⁻¹ (s z) = z
    rw [this]
    exact s'.symm_apply_apply z
  obtain ⟨fa, fb, fm⟩ := Classical.choose_spec (loc a b) r hr hab
  have hsr : s' * r = s := by simp [r]
  have hrs : r * s⁻¹ = s'⁻¹ := by simp [r]
  have inv1 : ∀ (q : Gal(Ω/ℚ)) (e : Row M), gr M q (gr M q⁻¹ e) = e := by
    intro q e
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 e).2]
  have sa := sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1
  have sb := sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1
  have ex : sg X c M (gr M s'⁻¹ x) = sg X c M a := by
    rw [← hrs, (hgr _ _ _).1, ← sa.2.2.1 r, fa]
  have ey : sg X d M (gr M s'⁻¹ y) = sg X d M b := by
    rw [← hrs, (hgr _ _ _).1, ← sb.2.2.1 r, fb]
  have ws' := (hw s' x y hxy).2
  rw [ex, ey] at ws'
  have ws := (hw s x y hxy).2
  have gx : (X.gal s) (sg X c M a) = sg X c M x := by rw [sa.2.2.1 s, inv1]
  have gy : (X.gal s) (sg X d M b) = sg X d M y := by rw [sb.2.2.1 s, inv1]
  have q1 : IsPt X m ((X.gal r) (sg X c M a)) ((X.gal r) (sg X d M b)) (t (sg X c M a) (sg X d M b)) := by
    rw [fa, fb]
    exact pt a b hab
  have q2 : IsPt X m ((X.gal s') ((X.gal r) (sg X c M a))) ((X.gal s') ((X.gal r) (sg X d M b))) (t (sg X c M x) (sg X d M y)) := by
    rw [← gal_mul_apply, ← gal_mul_apply, hsr, gx, gy]
    exact pt x y hxy
  have comp := mvComp Ω ε X m hm (X.gal r) (X.gal s') r s' (hadm r) (hadm s') _ _ _ _ _ (pt a b hab) q1 q2 _ _ fm ws'
  rw [map_one, one_pow, one_mul] at comp
  have eg : (X.gal r).trans (X.gal s') = X.gal s := by
    ext f
    rw [← hsr, gal_mul_apply]
    rfl
  rw [eg, hsr] at comp
  have q3 : IsPt X m ((X.gal s) (sg X c M a)) ((X.gal s) (sg X d M b)) (t (sg X c M x) (sg X d M y)) := by
    rw [gx, gy]
    exact pt x y hxy
  exact ((mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ (pt a b hab)).2.2.2 _ q3 _ _ comp).1 ws
end

