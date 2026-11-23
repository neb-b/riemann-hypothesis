module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem homLocRing_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hc : c = ∑ k, c k • blockWeight ι ⟨k, i k⟩ := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k)
      (fun k => c k • blockWeight ι ⟨k, i k⟩)
      fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) _).pow _
    rw [← hc] at h
    exact h
  · intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
    exact hi k (hW.mem_of_pow_mem _ hk)

theorem HomLocRingLocal.proof (hloc : HomLocRingIsLocal.Statement.{u})
    (hnoeth : HomLocRingNoetherian.Statement.{u}) (hdim : HomLocRingDimLe.Statement.{u}) :
    HomLocRingLocal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel
  have := hP.isPrime
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨hlocal, hunit⟩ := hloc O K ι P W hWp hPW
  have hnoe := hnoeth O K ι P W hP.multiHomog hWp hWrel hPW
  refine ⟨hlocal, hnoe, le_antisymm ?_ ?_⟩
  · refine (hdim O K ι P W hP.multiHomog hWp hWrel hPW).trans ?_
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    exact_mod_cast h1
  · obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hWp hWrel c
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
          homLocRing P W :=
      Subring.subset_closure ⟨c, x, g, hx, hg, hgW, rfl⟩
    have hnu : ¬ IsUnit (⟨_, hz⟩ : homLocRing P W) :=
      fun h => (hunit c x g hx hg hgW hz).mp h hxW
    have hne : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
      intro h0
      have h1 := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, div_eq_zero_iff,
        IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact hxP h1
      · exact hgW (hPW h1)
    have hlt : (⊥ : Ideal (homLocRing P W)) < IsLocalRing.maximalIdeal (homLocRing P W) := by
      refine bot_lt_iff_ne_bot.mpr fun h => hne ?_
      have hm := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rwa [h, Ideal.mem_bot] at hm
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h3 : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (homLocRing P W)).height :=
      le_trans le_add_self h2
    exact_mod_cast h3

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HomLocRingMem.algebraMap_mk_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [P.IsPrime] {g : MRing ι R} (hg : g ∉ P) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

theorem HomLocRingMem.proof : HomLocRingMem.Statement := by
  intro R _ K _ ι P W _ hW hPW z
  have hne : ∀ g : MRing ι R, g ∉ W →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  constructor
  · intro hz
    refine Subring.closure_induction (fun x hx => hx) ?_ ?_ ?_ ?_ ?_ hz
    · exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * g₂ + g₁ * f₂, g₁ * g₂, (hf₁.mul hg₂).add ?_, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      · rw [add_comm b₁ b₂, mul_comm g₁ f₂]
        exact hf₂.mul hg₁
      · set_option synthInstance.maxHeartbeats 200000 in
        simp only [map_add, map_mul]
        rw [div_add_div _ _ (hne g₁ hW₁) (hne g₂ hW₂)]
    · rintro x - ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨b, -f, g, hf.neg, hg, hgW, by simp only [map_neg, neg_div]⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * f₂, g₁ * g₂, hf₁.mul hf₂, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      simp only [map_mul]
      rw [div_mul_div_comm]
  · intro hz
    exact Subring.subset_closure hz

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HomLocRingNoetherian

variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

theorem component_form_mul {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  have hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem
  rw [← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d),
    ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]
  exact this

variable (P : Ideal (MRing ι R)) [P.IsPrime]

abbrev img : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P}


omit [DecidableEq K] in
theorem img_eq_zero_iff {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by
  simp [img, Ideal.Quotient.eq_zero_iff_mem]

theorem img_component_congr (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by
  rw [← sub_eq_zero, ← map_sub, img_eq_zero_iff] at huv ⊢
  rw [← map_sub]
  exact hP _ huv d


omit [DecidableEq K] in
theorem img_ne_zero {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := fun h0 => ht (hPW (img_eq_zero_iff.mp h0))

theorem quot_mem {W : Ideal (MRing ι R)} {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hgW : g ∉ W) : img P f / img P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

end HomLocRingNoetherian


open HomLocRingNoetherian in
theorem HomLocRingNoetherian.proof (hmem : HomLocRingMem.Statement.{u}) :
    HomLocRingNoetherian.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W _ hP hW _ hPW
  classical
  set S := MRing ι R
  set D := S ⧸ P
  set F := FractionRing D

  let T : Submonoid S :=
    { carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W}
      one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }
  let T' : Submonoid D := T.map (Ideal.Quotient.mk P)
  have hT' : T' ≤ nonZeroDivisors D := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  let B : Subalgebra D F := Localization.subalgebra F T' hT'
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing T' B inferInstance

  have rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h := by
    rintro y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩
  have hAB : ∀ x ∈ homLocRing P W, x ∈ B := by
    intro x hx
    refine (Subring.closure_le (t := B.toSubring)).mpr ?_ hx
    rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div]⟩
  let j : homLocRing P W →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I := by
    intro I z hz
    let Q : F → Prop := fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W →
      y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W →
        ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t
    have Q0 : Q 0 := by
      intro s e h _ _ hy d t _ _
      refine ⟨0, I.zero_mem, ?_⟩
      rw [zero_mul, eq_comm, img_eq_zero_iff] at hy
      rw [img_eq_zero_iff.mpr (hP h hy d), zero_div]
      rfl
    have Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂) := by
      intro y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep y₁ hy₁
      obtain ⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩ := rep y₂ hy₂
      have hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂) := (hs.mul ht₁).mul ht₂
      have hσW : s * t₁ * t₂ ∉ W := hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W
      have hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d) := (ht₁.mul ht₂).mul ht
      have hτW : t₁ * t₂ * t ∉ W := hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW
      obtain ⟨a₁, ha₁I, ha₁⟩ := Q₁ _ _ (h₁ * (s * t₂)) hσ hσW
        (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW
      obtain ⟨a₂, ha₂I, ha₂⟩ := Q₂ _ _ (h₂ * (s * t₁)) hσ hσW
        (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW
      refine ⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩
      have hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h) := by
        simp only [map_mul, map_add (f := _)]; rw [← hb₁, ← hb₂, ← hy]; ring
      have hc := img_component_congr hP hsum ((e₁ + e₂) + d)
      rw [component_form_mul (ht₁.mul ht₂), map_add (f := _), map_add (f := _)] at hc
      have h1 := img_ne_zero hPW ht₁W
      have h2 := img_ne_zero hPW ht₂W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_add, ha₁, ha₂, ← add_div, hc]
      simp only [map_mul]
      field_simp
    have Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F)) := by
      intro b hb a haI s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep b hb
      obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW a).mp a.2
      have hfg' : (a : F) = img P f / img P g := hfg
      have hg0 := img_ne_zero hPW hgW
      have hfa : img P f = a * img P g := by rw [hfg', div_mul_cancel₀ _ hg0]
      have hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h) := by
        simp only [map_mul]; rw [hfa, ← hy, ← hb₁]; ring
      have hc := img_component_congr hP hrel (c + (d + e₁))
      rw [component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel,
        component_form_mul (ht₁.mul hg)] at hc
      have ha' := quot_mem (P := P) (W := W)
        (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁)
        (hW.mul_notMem htW ht₁W)
      refine ⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩
      have h1 := img_ne_zero hPW ht₁W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_mul, hfg']
      simp only [map_mul] at hc ⊢
      field_simp
      linear_combination hc
    have hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F)) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, haI, rfl⟩ b
        exact Qgen b b.2 a haI
      · intro b
        simpa using Q0
      · intro y₁ y₂ _ _ Q₁ Q₂ b
        have := Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)
        simpa [mul_add] using this
      · intro c y _ Qy b
        have := Qy (b * c)
        simpa [mul_assoc] using this
    obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW z).mp z.2
    have hfg' : (z : F) = img P f / img P g := hfg
    have hg0 := img_ne_zero hPW hgW
    obtain ⟨a, haI, ha⟩ := hspan _ hz 1 g c f hg hgW
      (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0])
      c g hg hgW
    rw [hf.weightedHomogeneousComponent_same, ← hfg'] at ha
    exact (Subtype.ext ha : a = z) ▸ haI
  have hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j) := by
    intro I₁ I₂ h12
    have e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I := fun I =>
      le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map
    rw [← e I₁, ← e I₂]
    exact congrArg (Ideal.comap j) h12
  have hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j) := fun _ _ h => Ideal.map_mono h
  have hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j) :=
    hmono'.strictMono_of_injective hinj
  have : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

theorem sup_span_C_ne_top_of_multiHomog {O : Type*} [CommRing O] {K : Type} [DecidableEq K]
    (ι : K → Type) {W : Ideal (MRing ι O)} (hW : IsMultiHomogIdeal W)
    (h0 : W.comap (C : O →+* MRing ι O) = ⊥) {ϖ : O} (hϖ : ¬ IsUnit ϖ) :
    W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤ := by
  intro htop
  have h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)} := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have hw0 : (C (AddMonoidAlgebra.coeff w 0) : MRing ι O) ∈ W := by
    have h := hW w hw 0
    rwa [weightedHomogeneousComponent_zero] at h
    intro v hv
    have := congrFun hv v.1
    simp [blockWeight] at this
  have hc : AddMonoidAlgebra.coeff w 0 = 0 := by
    have h : AddMonoidAlgebra.coeff w 0 ∈ W.comap (C : O →+* MRing ι O) := hw0
    rw [h0] at h
    exact h
  have h2 := congrArg (AddMonoidAlgebra.coeff · 0) hwt
  rw [MvPolynomial.coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one] at h2
  exact hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)

theorem ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} [P.IsPrime] {f : MRing ι O} (hfP : f ∉ P)
    (hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (hWϖ : W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤) (N : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι O ⧸ W) = (N : WithBot ℕ∞) := by
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm'⟩ := Ideal.exists_le_maximal _ hWϖ
  have hWm : W ≤ m := le_sup_left.trans hWm'
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm
    (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hdim] at hPdim
  have hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : N ≤ b0 := by omega
  have hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hdim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' hup

theorem HorizontalComponentModel.proof : HorizontalComponentModel.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW
  have hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  obtain ⟨hWmin, hrel⟩ := hWd
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hWh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin

  have h0 : W.comap (C : O →+* MRing ι O) = ⊥ := by
    by_contra hne
    have hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal :=
      haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _
      IsPrime.to_maximal_ideal hne
    have hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O) := by
      rw [IsLocalRing.eq_maximalIdeal hmx]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact hϖW hϖm
  have hdim := ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin
    (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K)
    (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])
  exact ⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

