module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalVectorFieldUniqueCombinationBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

open GlobalTheory.Points (le_preimage_mono)

theorem exists_epsPt : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧ ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := _root_.GlobalTheory.EpsPoint.exists_epsPoint

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := _root_.GlobalTheory.VertSpan.exists_coeffs_translate

theorem coeffs_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := _root_.GlobalTheory.VertSpan.coeffs_zero

theorem vert_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (W : t.G.left.Opens) (hW : W ≤ t.G.hom ⁻¹ᵁ U.1) (e : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), IsField W e → (∀ r : Γ(X, U.1), e W ((t.G.hom.appLE U.1 W hW).hom r) = 0) → ∃! c : Fin n → Γ(t.G.left, W), ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)), e O f = ∑ a, resG t.G.left hO (c a) * δ a O f := by
  intro E _ _ _ H X t U n v hv hb δ hδF hδ0 hδv W hW e he he0
  classical
  have hφ : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      ∃ φ : Γ(X, U.1) →+* S, g ≫ t.G.hom = spMap φ ≫ chart U := fun S _ g hg =>
    ⟨_, (GlobalTheory.Points.specMap_valMap_fromSpec U.2 (g ≫ t.G.hom) (le_preimage_mono g hW hg)).symm⟩
  have hE : ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ c : Fin n → S,
      ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S')
        (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)),
        (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) →
        ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O),
          valR (spMap ρ ≫ g₀) O (e O f) = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
    intro S _ g₀ hg
    obtain ⟨φ, hφg⟩ := hφ S g₀ hg
    obtain ⟨w, hred, hw⟩ := exists_epsPt t.G.left W e he S g₀ hg
    have hwW : ⊤ ≤ w ⁻¹ᵁ W := GlobalTheory.CechKS.le_preimage_of_red hred hg
    have hid : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
    have hid' : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
      have : dualMap (RingHom.id S) = RingHom.id _ := by
        refine RingHom.ext fun z => ?_
        ext <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have hover : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom := by
      have hU1 : ⊤ ≤ (w ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono w hW hwW
      have hU0 : ⊤ ≤ (g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono g₀ hW hg
      have hU2 : ⊤ ≤ (spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 :=
        fun p _ => hU0 (Set.mem_univ (spMap (algebraMap S (DualNumber S)) p))
      refine GlobalTheory.Points.ext_of_valR U.2 hU1 hU2 fun r => ?_
      rw [← GlobalTheory.Points.valR_appLE w t.G.hom hW hwW r, GlobalTheory.Points.valR_spMap_comp _ _ _ hU0,
        ← GlobalTheory.Points.valR_appLE g₀ t.G.hom hW hg r]
      have h₁ := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom w W hwW
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hred] at h₁
      have h₂ := hw S (RingHom.id S) W le_rfl (by rw [hid, Category.id_comp]; exact hg)
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hid, hid', Category.id_comp, Category.id_comp, he0, GlobalTheory.Points.valR_zero _ _ hg] at h₂
      ext
      · rw [h₁]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [h₂]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc⟩ := exists_coeffs E H X t U n v hv hb S φ g₀ w hφg hred hover
    exact ⟨c, fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => by
      rw [← hw S' ρ O hO hgO f, hc S' ρ φ' wt h₁ h₂ O hgO f]⟩
  let F : ∀ (S : Type) [CommRing S], (Sp S ⟶ t.G.left) → Fin n → S := fun S _ g =>
    if h : ⊤ ≤ g ⁻¹ᵁ W then (hE S g h).choose else 0
  have hF : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (h : ⊤ ≤ g ⁻¹ᵁ W), F S g = (hE S g h).choose :=
    fun S _ g h => dif_pos h
  have hrel : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ g ⁻¹ᵁ O →
      ∀ f : Γ(t.G.left, O), valR g O (e O f) = ∑ a, F S g a * (valR (wt a) O f).snd := by
    intro S _ g hg φ wt h₁ h₂ O hO hgO f
    have hid : spMap (RingHom.id S) ≫ g = g := by
      rw [show spMap (RingHom.id S) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    have := (hE S g hg).choose_spec S (RingHom.id S) φ wt (by rw [hid]; exact h₁) (by rw [hid]; exact h₂) O hO
      (by rw [hid]; exact hgO) f
    rw [hid] at this
    rw [this, hF S g hg]
    rfl
  have hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ρ : S →+* S') (g : Sp S ⟶ t.G.left),
      ⊤ ≤ g ⁻¹ᵁ W → F S' (spMap ρ ≫ g) = fun a => ρ (F S g a) := by
    intro S S' _ _ ρ g hg
    have hg' : ⊤ ≤ (spMap ρ ≫ g) ⁻¹ᵁ W := fun p _ => hg (Set.mem_univ (spMap ρ p))
    have hz := coeffs_eq_zero E H X t U n v hv hb S' (spMap ρ ≫ g) W hW hg'
      (fun a => F S' (spMap ρ ≫ g) a - ρ (F S g a)) (fun S'' _ ρ' φ' wt h₁ h₂ O hO hgO f => by
        have hc : spMap (ρ'.comp ρ) ≫ g = spMap ρ' ≫ spMap ρ ≫ g := by
          rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
        have e₁ := (hE S' (spMap ρ ≫ g) hg').choose_spec S'' ρ' φ' wt h₁ h₂ O hO hgO f
        have e₂ := (hE S g hg).choose_spec S'' (ρ'.comp ρ) φ' wt (by rw [hc]; exact h₁) (by rw [hc]; exact h₂) O hO
          (by rw [hc]; exact hgO) f
        rw [hc, ← hF S g hg] at e₂
        rw [← hF S' (spMap ρ ≫ g) hg'] at e₁
        simp only [RingHom.comp_apply] at e₂
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
        rw [← e₁, ← e₂, sub_self])
    funext a
    exact sub_eq_zero.1 (congrFun hz a)
  choose cs hcs using fun a => GlobalTheory.LogKSLin.exists_sec W (fun S _ g => F S g a)
    (fun S S' _ _ ρ g hg => congrFun (hnat S S' ρ g hg) a)
  have hval : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens) (hO : O ≤ W), ⊤ ≤ g ⁻¹ᵁ O →
      ∀ (c : Fin n → Γ(t.G.left, W)) (f : Γ(t.G.left, O)),
        valR g O (∑ a, resG t.G.left hO (c a) * δ a O f) = ∑ a, valR g W (c a) * (valR (wt a) O f).snd := by
    intro S _ g φ wt hφg hwt O hO hgO c f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.Points.valR_eq _ _ hgO, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← GlobalTheory.Points.valR_eq _ _ hgO, GlobalTheory.Points.valR_mul _ _ hgO, GlobalTheory.Points.valR_res _ hO hgO,
      hδv a O (hO.trans hW) f S φ g (wt a) hφg hgO (hwt a)]
  have hex : ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)),
      e O f = ∑ a, resG t.G.left hO (cs a) * δ a O f := by
    intro O hO f
    refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    have hgW := le_preimage_mono g hO hg
    obtain ⟨φ, hφg⟩ := hφ S g hgW
    choose wt hwt using fun a => (existsUnique_isTranslate t φ hφg (hv a)).exists
    rw [hrel S g hgW φ wt hφg hwt O hO hg f, hval S g φ wt hφg hwt O hO hg cs f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcs a S g hgW]
  refine ⟨cs, hex, fun c' hc' => ?_⟩
  have key : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      (fun a => valR g W (c' a) - valR g W (cs a)) = 0 := by
    intro S _ g hg
    refine coeffs_eq_zero E H X t U n v hv hb S g W hW hg _ fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => ?_
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← GlobalTheory.Points.valR_spMap_comp ρ g W hg]
    rw [← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO c' f, ← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO cs f,
      ← hc' O hO f, ← hex O hO f, sub_self]
  funext a
  exact GlobalTheory.CechInv.ext_of_valR W _ _ fun S _ g hg => sub_eq_zero.1 (congrFun (key S g hg) a)

end GlobalTheory.VertSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem omegaStd_nsmul_left' {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (M • a) b = (M : ℤ) * omegaStd a b := by
  unfold omegaStd
  simp only [Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inl i) 1) = -a (Sum.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem kappaOK_dvd_iff {h M d : ℕ} {κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)}
    (hκ : KappaOK h M d κ) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b := by
  constructor
  · intro hk
    choose c hc using hk
    have hdiv : ∀ b, (M : ℤ) ∣ omegaStd a b := by
      intro b
      have h2 : (M : ℤ) ∣ formZ d h (fun k => κ k a) (fun k => κ k b) := by
        unfold formZ
        refine Finset.dvd_sum fun k _ => Finset.dvd_sum fun l _ => ?_
        dsimp only
        rw [hc k, omegaStd_nsmul_left']
        exact Dvd.intro (form d (sig k) (sig l) * omegaStd (c k) (κ l b)) (by ring)
      have := dvd_add (hκ.1 a b).dvd h2
      simpa using this
    have hx : ∀ x, (M : ℤ) ∣ a x := by
      rintro (i | i)
      · simpa [omegaStd_single_inr] using hdiv (Pi.single (Sum.inr i) 1)
      · simpa [omegaStd_single_inl] using hdiv (Pi.single (Sum.inl i) 1)
    exact ⟨fun x => a x / M, funext fun x => by simp [Int.mul_ediv_cancel' (hx x)]⟩
  · rintro ⟨b, rfl⟩ k
    exact ⟨κ k b, map_nsmul _ _ _⟩

theorem kappaOK_mod (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ))
    (hM : 1 ≤ M) (hκ : KappaOK h M d κ) :
    (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧
      ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  refine ⟨kappaOK_dvd_iff hκ, ?_⟩
  haveI : NeZero M := ⟨by omega⟩
  let f : (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) → (Fin 8 → Fin h ⊕ Fin h → ZMod M) :=
    fun x k j => ((κ k (fun i => ((x i).val : ℤ)) j : ℤ) : ZMod M)
  have hinj : Function.Injective f := by
    intro x y hxy
    let a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ := fun i => ((x i).val : ℤ) - ((y i).val : ℤ)
    have hk : ∀ k, ∃ b, κ k a = M • b := by
      intro k
      have hj : ∀ j, (M : ℤ) ∣ κ k a j := by
        intro j
        have e := congrFun (congrFun hxy k) j
        simp only [f] at e
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have ha : a = (fun i => ((x i).val : ℤ)) - (fun i => ((y i).val : ℤ)) := rfl
        rw [ha, map_sub, Pi.sub_apply, Int.cast_sub, e, sub_self]
      exact ⟨fun j => κ k a j / M, funext fun j => by simp [Int.mul_ediv_cancel' (hj j)]⟩
    obtain ⟨b, hb⟩ := (kappaOK_dvd_iff hκ a).1 hk
    funext i
    have e := congrFun hb i
    have h2 : ((a i : ℤ) : ZMod M) = 0 := by rw [e]; simp
    simp [a] at h2
    exact sub_eq_zero.mp h2
  have hcard : Fintype.card (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) =
      Fintype.card (Fin 8 → Fin h ⊕ Fin h → ZMod M) := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    rw [← pow_mul]
    congr 1
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  intro cc
  obtain ⟨x, hx⟩ := hbij.2 (fun k j => (cc k j : ZMod M))
  refine ⟨fun i => ((x i).val : ℤ), fun k => ?_⟩
  have hj : ∀ j, (M : ℤ) ∣ κ k (fun i => ((x i).val : ℤ)) j - cc k j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have e := congrFun (congrFun hx k) j
    simp only [f] at e
    rw [e, sub_self]
  refine ⟨fun j => (κ k (fun i => ((x i).val : ℤ)) j - cc k j) / M, funext fun j => ?_⟩
  rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hj j)]
  ring

end GlobalTheory.ZarhinFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZarhinFam

section Maps

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def zpr (mu : B ⟶ A) (k : Fin 8) : Zob A B ⟶ A :=
  Sum.elim (pa A B) (fun j => pb A B j ≫ mu) (sig k)

def zphi (mu : B ⟶ A) : Zob A B ⟶ Out.powObj A 8 :=
  (Out.powIsLimit A 8).lift (Fan.mk _ (zpr A B mu))

theorem zphi_powPr (mu : B ⟶ A) (k : Fin 8) : zphi A B mu ≫ Out.powPr A k = zpr A B mu k :=
  (Out.powIsLimit A 8).fac _ ⟨k⟩

end Maps

def zW (d : ℕ) : Matrix (Fin 8) (Fin 8) ℤ := fun k l =>
  Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 (sig k) (sig l)

end GlobalTheory.ZarhinFam
end
end

