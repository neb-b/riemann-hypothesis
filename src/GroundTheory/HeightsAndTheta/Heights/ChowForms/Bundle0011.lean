module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartIncOrd
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartDehomog.proof : ChartDehomog.Statement := by
  intro F _ n W t G d hW hH ht hG hmem
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hhom (homogeneousComponent_isHomogeneous k g)]
        have : φ (homogeneousComponent k g) = 0 := by
          simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hH g hg k)]
        rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (ChartLocDomain.linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have h0 : ψ G = 0 := hle hmem
  rw [hhom hG] at h0
  have h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 :=
    calc algebraMap _ A (Ideal.Quotient.mk W G)
        = (algebraMap _ A a * v) ^ d * φ G := by
          rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]; rfl
      _ = algebraMap _ A a ^ d * (v ^ d * φ G) := by ring
      _ = 0 := by rw [h0, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartHomogenise

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type} [Field F] {n : ℕ}

theorem exists_homogeneous_sub_mem_span (ℓ g : MvPolynomial (Fin n) F) (hℓ : ℓ.IsHomogeneous 1) :
    ∃ (G : MvPolynomial (Fin n) F) (D : ℕ), G.IsHomogeneous D ∧ G - g ∈ Ideal.span {ℓ - 1} := by
  classical
  refine ⟨∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g,
    g.totalDegree, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hdD : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (hℓ.pow (g.totalDegree - d)).mul (homogeneousComponent_isHomogeneous d g)
    rwa [one_mul, Nat.sub_add_cancel hdD] at h
  · have e : ∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g - g =
        ∑ d ∈ Finset.range (g.totalDegree + 1), (ℓ ^ (g.totalDegree - d) - 1) * homogeneousComponent d g := by
      simp only [sub_one_mul, Finset.sum_sub_distrib, sum_homogeneousComponent]
    rw [e]
    refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.mem_span_singleton]
    simpa using sub_dvd_pow_sub_pow ℓ 1 (g.totalDegree - d)

theorem proof : ChartHomogenise.Statement := by
  intro F _ n Q t hQ ht
  set 𝒜 := homogeneousSubmodule (Fin n) F
  set W : Ideal (MvPolynomial (Fin n) F) := (Q.homogeneousCore 𝒜).toIdeal with hW
  have hWQ : W ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hWprime : W.IsPrime := hQ.homogeneousCore
  have hWhom : IsHomogIdeal W := (isHomogIdeal_iff W).mpr (Q.homogeneousCore 𝒜).isHomogeneous
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  have hℓQ : linForm t ∉ Q := by
    intro h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Q.sub_mem h ht
  have hℓW : linForm t ∉ W := fun h => hℓQ (hWQ h)
  have hrel : IsRelevant W := by
    by_contra h
    simp only [IsRelevant, not_exists, not_not] at h
    exact hℓW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  refine ⟨W, ⟨hWprime, hWhom, hrel⟩, hℓW, le_antisymm ?_ ?_, ?_⟩
  · exact sup_le hWQ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  · intro g hg
    obtain ⟨G, D, hG, hGg⟩ := exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hspan : Ideal.span {linForm t - 1} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr ht
    have hGQ : G ∈ Q := by simpa using Q.add_mem (hspan hGg) hg
    have hGW : G ∈ W :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (mem_homogeneousSubmodule D G).mpr hG⟩ hGQ
    have : g = G - (G - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  · intro J hJ hJQ
    have hJh := (isHomogIdeal_iff J).mp hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJQ

end ChartHomogenise

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let g := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let f : (R ⧸ Ideal.span {x}) →ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun r a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, g,
          Ideal.quotientEquiv_mk, RingHom.coe_coe] }
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective f (by exact g.bijective))).symm

theorem ord_atPrime_congr {R : Type*} [CommRing R] {P₁ P₂ : Ideal R} [P₁.IsPrime] [P₂.IsPrime]
    (h : P₁ = P₂) (x : R) :
    Ring.ord (Localization.AtPrime P₁) (algebraMap R _ x) =
      Ring.ord (Localization.AtPrime P₂) (algebraMap R _ x) := by
  subst h; rfl

theorem ord_atPrime_map_localization {R : Type*} [CommRing R] (M : Submonoid R) (P : Ideal R)
    [hP : P.IsPrime] (hd : Disjoint (M : Set R) P) [hP' : (P.map (algebraMap R (Localization M))).IsPrime]
    (x : R) :
    Ring.ord (Localization.AtPrime (P.map (algebraMap R (Localization M))))
        (algebraMap (Localization M) _ (algebraMap R _ x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by
  have hc : (P.map (algebraMap R (Localization M))).comap (algebraMap R (Localization M)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (Localization M) hP hd
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
    (P.map (algebraMap R (Localization M)))
  rw [← IsScalarTower.algebraMap_apply, ← e.commutes x]
  exact (ord_ringEquiv e.toRingEquiv _).trans (ord_atPrime_congr hc x)

theorem chartIncIdeal_eq_sup {F : Type} [Field F] {n : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)}
    (t : Fin n → F) (e : ℕ) (h : I ≤ W) :
    chartIncIdeal W t e = W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
  unfold chartIncIdeal
  rw [Ideal.map_sup, Ideal.map_sup]
  have hba : I.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) ≤
      W.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) := Ideal.map_mono h
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (le_sup_of_le_right (le_sup_of_le_left le_sup_right)))
      (le_sup_of_le_right le_sup_right)
  · exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le (sup_le (le_sup_of_le_left (le_sup_of_le_left hba)) (le_sup_of_le_left le_sup_right))
        le_sup_right)

private theorem linForm_isHomogeneous_one {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem ChartLocalOrder.proof (h₂ : ChartIncDomain.Statement) (h₃ : ChartKernel.Statement)
    (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncIdealPrime.Statement) (h₈ : ChartIncOrd.Statement)
    (h₉ : DehomogOrd.Statement) (h₁₀ : LocalMultOrd.Statement) : ChartLocalOrder.Statement := by
  intro F _ n e I W f t u q p _ hI hf hu hq hp _ hW hqW htW

  obtain ⟨hWp, hWd⟩ := h₅ F n e I W u hI (h₄ F n (e + 1) I f hI hf) hu hW
  have := hWp.isPrime
  have hIW : I ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨g, hg⟩ := h₆ F n e W hWp hWd
  rw [isChowForm_iff] at hg
  have hinc : incIdeal W e = p := by
    have hpr := h₇ F n e W hWp.isPrime hWp.isRelevant
    have hqg : q ∈ Ideal.span {g} := hg.2 ▸ hqW
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hqg
    have hgu : ¬ IsUnit g := fun h => hpr.ne_top (by rw [hg.2, Ideal.span_singleton_eq_top.mpr h])
    have hcu : IsUnit c := (hq.irreducible.isUnit_or_isUnit (by rw [← hc, mul_comm])).resolve_left hgu
    rw [hp, hg.2, Ideal.span_singleton_eq_span_singleton]
    exact ⟨hcu.unit, by rw [IsUnit.unit_spec, mul_comm, hc]⟩

  obtain ⟨hdomW, hkerXW⟩ := h₂ F n e W t hWp htW
  have hkerW := h₃ F n e W t hWp htW
  have hcW := chartIncIdeal_eq_sup t e hIW
  have hcWp : (chartIncIdeal W t e).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomW
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk _
  have hkπ : RingHom.ker π = chartIncIdeal I t e := Ideal.mk_ker
  have hQ : W.map (chartX I t e) = (W.map (rename Sum.inl)).map π := by
    change _ = Ideal.map π (Ideal.map (rename Sum.inl).toRingHom _)
    rw [Ideal.map_map]; rfl
  have hmem : ∀ a, π a ∈ W.map (chartX I t e) ↔ a ∈ chartIncIdeal W t e := fun a => by
    have hkb : Ideal.comap π (⊥ : Ideal (ChartInc I t e)) = chartIncIdeal I t e := hkπ
    have hcm : Ideal.comap π ((W.map (rename Sum.inl)).map π) =
        W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
      rw [← hkb]; exact Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective _
    rw [← hcW, ← hQ] at hcm
    exact SetLike.ext_iff.mp hcm a
  have h𝔔 : (W.map (chartX I t e)).IsPrime := by
    rw [hQ]
    exact isPrime_map_of_sup_ker π Ideal.Quotient.mk_surjective _ (by rw [hkπ, ← hcW]; exact hcWp)
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Submonoid _) :
      Set (ChartInc I t e)) (W.map (chartX I t e)) := by
    rw [Set.disjoint_left]
    intro y hy hyQ
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    have h1 : π (rename Sum.inr s) ∈ W.map (chartX I t e) := hyQ
    have h0 : algebraMap _ (ChartInc W t e) s = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem _).mp h1)
    have : s ∈ p := by rw [← hinc, ← hkerW]; exact h0
    exact hs this

  have hP : (chartIdeal I t e p W).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ (ChartLoc I t e p) _ h𝔔 hdisj
  refine ⟨hP, ?_⟩
  have hWI : (W.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIW)
  have hWQ : (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime := by
    have := hdomW
    have hpr : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := hkerXW ▸ RingHom.ker_isPrime _
    exact isPrime_map_of_sup_ker _ Ideal.Quotient.mk_surjective _
      (by rw [Ideal.mk_ker, ← sup_assoc, sup_eq_left.mpr hIW]; exact hpr)
  calc _ = Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
          (algebraMap (ChartInc I t e) _ (chartX I t e (linForm u))) :=
        ord_atPrime_map_localization (hP' := hP) _ _ hdisj _
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) (linForm u))) :=
        h₈ F n e I W t (linForm u)
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I (linForm u))) :=
        (h₉ F n I W t hI.isHomog hWp.isHomog hIW htW (linForm u) 1 (linForm_isHomogeneous_one u)).symm
    _ = _ := (h₁₀ (MvPolynomial (Fin n) F) I W (linForm u) hW.1).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PComponentOfIncIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace ComponentOfIncIdeal

theorem ringKrullDim_quot_add_one_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (hPQ : P ≤ Q) (hne : P ≠ Q) : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
  have hne' : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h0
    have hx : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hxQ
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hxP hx
  have h := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne'
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)] at h

theorem one_le_ringKrullDim_quot {F : Type} [Field F] {n : ℕ} {W : Ideal (MvPolynomial (Fin n) F)}
    (hW : IsProjPrime W) : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) := by
  have hWp := hW.isPrime
  set m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmp : m.IsPrime := RingHom.ker_isPrime _
  have hle : W ≤ m := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h
    have h0 := hW.isHomog f hf 0
    rw [homogeneousComponent_zero] at h0
    have hc : AddMonoidAlgebra.coeff f 0 ≠ 0 := by rwa [← constantCoeff_eq]
    exact hWp.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hc).map C))
  have hne : W ≠ m := by
    obtain ⟨j, hj⟩ := hW.isRelevant
    intro h
    exact hj (h ▸ (by simp [m] : (X j : MvPolynomial (Fin n) F) ∈ m))
  have h := ringKrullDim_quot_add_one_le hle hne
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ m) :=
    ringKrullDim_nonneg_of_nontrivial
  exact (le_add_of_nonneg_left h0).trans h

theorem exists_nat_of_bounds {x : WithBot ℕ∞} {e : ℕ} (h1 : 1 ≤ x) (h2 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ k : ℕ, x = (k : WithBot ℕ∞) ∧ 1 ≤ k ∧ k ≤ e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        le_trans (le_add_of_nonneg_right zero_le_one) h2
      have h4 : (⊤ : ℕ∞) ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h3
      exact absurd h4 (by simp)
    | coe k =>
      refine ⟨k, rfl, ?_, ?_⟩
      · exact_mod_cast h1
      · have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
        have : k + 1 ≤ e + 1 := by exact_mod_cast this
        omega

end ComponentOfIncIdeal


open ComponentOfIncIdeal in
theorem ComponentOfIncIdeal.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement)
    (h₃ : ConeDimComponent.Statement) : ComponentOfIncIdeal.Statement := by
  intro F _ n e I W u q hI hdim hu hW hle hq hinc
  have hWp := hW.isPrime
  have := hI.isPrime

  have hIW : I ≤ W := le_sup_left.trans hle
  have huW : linForm u ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hIneW : I ≠ W := fun h => hu (h ▸ huW)
  have hup := ringKrullDim_quot_add_one_le hIW hIneW
  rw [hdim] at hup
  obtain ⟨k, hk, hk1, hke⟩ := exists_nat_of_bounds (one_le_ringKrullDim_quot hW) hup

  have hdimInc := h₁ F n e (k - 1) W hW (by rw [hk]; congr 2; omega)
  have hincp : (incIdeal W e).IsPrime := h₂ F n e W hWp hW.isRelevant
  have hS : ringKrullDim (MvPolynomial (Fin e × Fin n) F) = ((e * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField (Field.toIsField F)]
    simp [Nat.card_eq_fintype_card]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) (incIdeal W e)
  rw [hdimInc, hS] at hsum
  have hqle : (Ideal.span {q}).height ≤ 1 := Ideal.height_span_singleton_le_one hq.not_isUnit
  have hht : (incIdeal W e).height ≤ 1 := (Ideal.height_mono hinc).trans hqle
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (incIdeal W e).height = h :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hht) |>.imp fun _ h => h.symm
  rw [hh] at hsum hht
  have hh1 : h ≤ 1 := by exact_mod_cast hht
  have hnat : h + (e * n - e + min e (k - 1)) = e * n := by
    have h5 : (((h + (e * n - e + min e (k - 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) = (((e * n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [Nat.cast_add, WithBot.coe_add]
      exact hsum
    exact_mod_cast WithBot.coe_inj.mp h5
  have hn : 1 ≤ n := by
    obtain ⟨j, _⟩ := hW.isRelevant
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
  have hen : e ≤ e * n := Nat.le_mul_of_pos_right e hn
  have hmin : min e (k - 1) = k - 1 := min_eq_right (by omega)
  rw [hmin] at hnat
  generalize e * n = N at hnat hen
  have hke' : k = e := by omega
  have hh' : h = 1 := by omega
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨W'', hmin'', hW''⟩ := Ideal.exists_minimalPrimes_le hle
    have hrel : IsRelevant W'' := by
      obtain ⟨j, hj⟩ := hW.isRelevant
      exact ⟨j, fun hj'' => hj (hW'' hj'')⟩
    have hdim'' := (h₃ F n e I W'' u hI hdim hu ⟨hmin'', hrel⟩).2
    by_cases heq : W'' = W
    · exact heq ▸ ⟨hmin'', hrel⟩
    · have := hmin''.1.1
      have hlt := ringKrullDim_quot_add_one_le hW'' heq
      rw [hdim'', hk, hke'] at hlt
      have : e + 1 ≤ e := by exact_mod_cast hlt
      omega
  ·
    by_contra hne
    have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have : (Ideal.span {q}).FiniteHeight :=
      (Ideal.span {q}).finiteHeight_iff.mpr (Or.inr (ne_top_of_le_ne_top (by simp) hqle))
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hinc hne)
    rw [hh, hh'] at hlt
    exact absurd (hlt.trans_le hqle) (lt_irrefl _)

end GroundTheory.Heights₂.Heights
end

