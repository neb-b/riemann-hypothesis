module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFractionEvalSectionAffineNearPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.WtRat

theorem ev_spMap_top {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) :=
  (ev_top (spMap e) h u).trans
    (congrArg (fun q => CommRingCat.Hom.hom q u)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom e)))

theorem exists_frac_ev (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W))
    (x : PrimeSpectrum R) (hx : x ∈ W) :
    ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W),
      WtRat.ev (spMap e) W h s * e β = e α := by
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  obtain ⟨f, hfW, hxf⟩ := hT.exists_basicOpen_le (V := W) ⟨x, hx⟩ trivial
  have hb : (Sp R).basicOpen f =
      PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom f) :=
    basicOpen_eq_of_affine' f
  haveI := hT.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f)
    (((Sp R).presheaf.map (homOfLE hfW).op).hom s)
  set φ : Γ(Sp R, ⊤) →+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom with hφ
  refine ⟨φ a * φ f, φ f ^ (n + 1), ?_, ?_⟩
  · intro hm
    rw [hb] at hxf
    exact hxf (x.isPrime.mem_of_pow_mem _ hm)
  · intro F _ e h
    by_cases h0 : e (φ f) = 0
    · simp [h0]
    have hD : ⊤ ≤ spMap e ⁻¹ᵁ (Sp R).basicOpen f := by
      intro y _
      rw [hb]
      change e (φ f) ∉ y.asIdeal
      intro hy
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (Ne.isUnit h0))
    have key := congrArg (ev (spMap e) _ hD) ha
    rw [map_mul, ev_res (spMap e) hfW hD h s] at key
    have hv : ∀ u : Γ(Sp R, ⊤),
        ev (spMap e) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen f) u) = e (φ u) :=
      fun u => (ev_res (spMap e) ((Sp R).basicOpen_le f) hD le_top u).trans
        (ev_spMap_top e le_top u)
    rw [hv, hv] at key
    simp only [map_pow] at key
    rw [map_pow, map_mul, pow_succ, ← _root_.mul_assoc, key]

end GlobalTheory.SS.WtRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFunctionFieldPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {Y : Scheme.{0}}

theorem top_le_fromSpecStalk_preimage (x : Y) {V : Y.Opens} (hx : x ∈ V) :
    ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V := by
  intro y _
  have : Y.fromSpecStalk x y ∈ Set.range (Y.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact this.mem_open V.isOpen hx

theorem ev_fromSpecStalk (x : Y) {V : Y.Opens} (hx : x ∈ V)
    (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V) (u : Γ(Y, V)) :
    ev (R := Y.presheaf.stalk x) (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem genericPoint_mem [IsIntegral Y] {V : Y.Opens} (hV : (V : Set Y).Nonempty) :
    genericPoint Y ∈ V :=
  ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

theorem exists_generic_field_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  intro Y _
  have hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ Y.fromSpecStalk (genericPoint Y) ⁻¹ᵁ V :=
    fun V hV => top_le_fromSpecStalk_preimage _ (genericPoint_mem hV)
  refine ⟨Y.functionField, inferInstance, Y.fromSpecStalk (genericPoint Y), hg, ?_, ?_, ?_⟩
  · intro V hV a b hab
    have ha := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) a
    have hb := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) b
    exact germ_injective_of_isIntegral Y (genericPoint Y) (genericPoint_mem hV)
      (ha.symm.trans (hab.trans hb))
  · intro τ
    have e : τ.hom (genericPoint Y) = genericPoint Y := genericPoint_eq_of_isOpenImmersion τ.hom
    have sp : τ.hom (genericPoint Y) ⤳ genericPoint Y := specializes_of_eq e
    refine ⟨(Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)).hom, ?_⟩
    change Spec.map (Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)) ≫
      Y.fromSpecStalk (genericPoint Y) = Y.fromSpecStalk (genericPoint Y) ≫ τ.hom
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro U hU I _ x
    have key : ∀ a : Y.functionField, ∃ (V : Y.Opens) (hV : genericPoint Y ∈ V) (s : Γ(Y, V)),
        (Y.presheaf.germ V _ hV).hom s = a ∧ (a ≠ 0 → IsUnit s) := by
      intro a
      obtain ⟨V, hV, s, hs⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) a
      by_cases ha : a = 0
      · exact ⟨V, hV, s, hs, fun h => (h ha).elim⟩
      · have hm : genericPoint Y ∈ Y.basicOpen s := by
          rw [Scheme.mem_basicOpen Y s _ hV]
          have : IsUnit a := isUnit_iff_ne_zero.mpr ha
          rw [← hs] at this
          exact this
        refine ⟨Y.basicOpen s, hm, (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom s, ?_,
          fun _ => Y.toRingedSpace.isUnit_res_basicOpen s⟩
        rw [← hs]
        exact Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le s)) _ hm s
    choose V hV s hs hu using fun j => key (x j)
    have hle : ∀ j, U ⊓ Finset.univ.inf V ≤ V j := fun j =>
      inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
    have hm : genericPoint Y ∈ U ⊓ Finset.univ.inf V := by
      refine ⟨genericPoint_mem hU, ?_⟩
      change genericPoint Y ∈ ((Finset.univ.inf V : Y.Opens) : Set Y)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      simp only [Set.mem_iInter]
      exact fun j _ => hV j
    refine ⟨U ⊓ Finset.univ.inf V, ⟨_, hm⟩,
      fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom (s j), inf_le_left, fun j => ⟨?_, fun h => (hu j h).map _⟩⟩
    refine (ev_fromSpecStalk _ hm _ _).trans ?_
    rw [← hs j]
    exact Y.presheaf.germ_res_apply (homOfLE (hle j)) _ hm (s j)

end GlobalTheory.SS.WtRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightedRelationOfMinimalSupport
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_minimal_support {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by
  classical
  let s : (J → F) → Finset J := fun u => A.filter (fun i => u i ≠ 0)
  have hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n := ⟨_, v, hv, hLv, rfl⟩
  obtain ⟨v', hMv', hLv', hcard⟩ := Nat.find_spec hex
  refine ⟨v', hMv', hLv', ?_⟩
  have hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False := by
    intro u hMu hLu hsub hne
    have hlt : (s u).card < (s v').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hcard] at hlt
    exact Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩
  intro w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj
  by_contra hwj
  have hv'j : v' j ≠ 0 := fun h => hwj (hsupp j hj h)
  by_cases hLw : L w = 0
  · have hMu : M (fun i => v' i - v' j / w j * w i) := hM v' w _ hMv' hMw
    have hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0 := by
      rw [hL v' w, hLw, mul_zero, sub_zero]
      exact hLv'
    apply hmin _ hMu hLu
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun h => hi.2 ?_⟩
      rw [h, hsupp i hi.1 h, mul_zero, sub_zero]
    · intro heq
      have hjs : j ∈ s v' := by simp [s, hj, hv'j]
      rw [← heq] at hjs
      simp only [s, Finset.mem_filter] at hjs
      exact hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])
  · apply hmin w hMw hLw
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩
    · intro heq
      have hi₀s : i₀ ∈ s v' := by simp [s, hi₀, hv'i₀]
      rw [← heq] at hi₀s
      simp [s, hwi₀] at hi₀s

theorem exists_weighted_relation :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  intro F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum
  classical
  have hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1 := by
    intro t χ
    rw [← hmul, mul_inv_cancel, hone]
  obtain ⟨v', hMv', hLv', hmin⟩ := exists_minimal_support (S.disjSum S)
    (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ))
    (fun v => ∑ χ ∈ S, v (Sum.inl χ))
    (by
      intro v w a hv hw t
      have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ)
          = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ := by
        intro g h
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)),
        e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]
      linear_combination hv t - a * hw t)
    (by
      intro v w a
      rw [Finset.sum_sub_distrib, Finset.mul_sum])
    (Sum.elim p q) (fun t => hrel t) hsum
  obtain ⟨χ₀, hχ₀S, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLv'
  set r := v' (Sum.inl χ₀) with hrdef
  have htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ)))
      = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ))) := by
    intro t t'
    have h := congrArg (σ t) (hMv' (t' * t⁻¹))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h
    have e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ :=
      fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
    rw [e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]
    exact h
  have hfin : ∀ t, ∀ i ∈ S.disjSum S,
      σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i) := by
    intro t i hi
    have hsr : σ t r ≠ 0 := (map_ne_zero (σ t)).mpr hr
    have hz := hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j)
      (fun t' => by
        have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ)
            = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ := by
          intro g h
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun χ _ => by ring
        simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
        rw [e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)),
          e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]
        linear_combination htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')
      (by
        intro j _ hj
        simp [hj])
      (Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr
      (by
        show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0
        rw [div_mul_cancel₀ _ hr, sub_self])
      i hi
    have e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i := by
      have hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i :=
        sub_eq_zero.mp hz
      rw [hz']
      field_simp
    have hc := hcinv t (Sum.elim id id i)
    have hc0 := hcinv t χ₀
    have h1 : σ t r * (σ t r)⁻¹ = 1 := mul_inv_cancel₀ hsr
    have h2 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    rw [map_mul, map_inv₀]
    linear_combination ((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e'
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc
      + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1
      + (r⁻¹ * c t (Sum.elim id id i) * v' i) * hc0
  refine ⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_ne_zero (inv_ne_zero hr) hLv'
  · have h1 := hMv' 1
    simp only [hone, _root_.one_mul] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← h1]
    ring
  · intro t χ hχ
    exact ⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ),
      by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IndepOfNestedSpecialFibreImages
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.indep_of_special_fibres : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  intro C _ h p _ y y' hy hy' hr b hb
  obtain ⟨τ, τ', hτ⟩ := h p y y' hy hy' hr
  obtain ⟨c, hc, hcb⟩ := τ.lift b hb
  obtain ⟨c', hc', hcf⟩ := hτ (rPt p ≫ c) (by rw [Category.assoc, hc])
  have := τ'.smooth
  have : Smooth τ'.H.hom := SmoothOfRelativeDimension.smooth C.g τ'.H.hom
  obtain ⟨d, hd, hdr⟩ := _root_.GlobalTheory.ZJ.exists_classical_lift_of_smooth p _ _ τ'.H.hom (spMap τ'.j) c' hc'
  refine ⟨d ≫ τ'.f, ?_, ?_⟩
  · rw [Category.assoc, τ'.f_over, ← Category.assoc, hd, τ'.fac]
  · rw [← Category.assoc, hdr, hcf, Category.assoc, hcb]

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory

theorem jacobson_closedPoints_tools_int : ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧ (∀ (ξ : X) (κ : Type) [Finite κ] (U : κ → X.Opens) (W : X.Opens), ξ ∈ W → ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧ (∀ (κ : Type) [Finite κ] (Sg : κ → Set X), IrreducibleSpace X → (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) :=
  jacobson_tools_of_locallyOfFiniteType_int
end GlobalTheory
end

