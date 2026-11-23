module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0148
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

section

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem fnField_toSubfield (y : (Σ b, ι b) → Ω) :
    (fnField k y).toSubfield = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y := by
  rw [fnField, IntermediateField.adjoin_toSubfield]
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 2
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only at hpq
    subst hpq
    exact ⟨⟨a, i, j⟩, rfl⟩
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩

theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

theorem krull_pointIdeal (y : (Σ b, ι b) → Ω) (d : ℕ) (h : IsPt k y d) [(pointIdeal k y).IsPrime] :
    ringKrullDim (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hnz, hfin, htr⟩ := h
  have hcone := ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz
  have hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω) := by
    rw [← fnField_toSubfield k y]
    rfl
  have hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y) := by
    rw [hset]
    have : Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra :=
      Algebra.adjoin_eq (fnField k y).toSubalgebra
    rw [this]
    rfl
  haveI : FiniteDimensional (fnField k y) Ω := hfin
  have htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal) := hcone
    rw [e, hadj, trdeg_eq_of_finite k (fnField k y), htr]
    push_cast
    rfl
  exact ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'

end

theorem ptDim : PtDim := by
  intro k _ Ω _ _ K _ ι _ y d h
  classical
  have hmp : IsMultiProjPrime (pointIdeal k y) := PointIdealMultiProj.proof k Ω K ι y h.1
  have hdim := krull_pointIdeal k y d h
  refine ⟨?_, ?_, ?_⟩
  · convert hmp
  · unfold FieldNumbers.relDim
    rw [hdim]
    have e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ) := by
      push_cast
      ring
    change (WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))
    rw [e]
    rfl
  · refine ⟨?_, hdim⟩
    exact (Bridge.isMultiProjPrime_iff _).1 hmp

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLinkA
section
noncomputable section

namespace SheetDecomposition

open GlobalTheory.CompanionTheory.Ar

section

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mem_flagStep_iff (f : Fin r → V) (n : ℕ) (x : V) :
    x ∈ flagStep Ω f n ↔ ∃ B : Fin r → Ω, (∀ m : Fin r, n ≤ (m : ℕ) → B m = 0) ∧ x = ∑ m, B m • f m := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨Pi.single k 1, fun m hm => ?_, ?_⟩
      · have : m ≠ k := by rintro rfl; exact absurd hk (not_lt.2 hm)
        simp [this]
      · simp [Pi.single_apply]
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨B, hB, rfl⟩ := hx
      obtain ⟨C, hC, rfl⟩ := hy
      exact ⟨B + C, fun m hm => by simp [hB m hm, hC m hm], by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨B, hB, rfl⟩ := hx
      exact ⟨a • B, fun m hm => by simp [hB m hm], by simp [Finset.smul_sum, mul_smul]⟩
  · rintro ⟨B, hB, rfl⟩
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases h : (m : ℕ) < n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, h, rfl⟩)
    · simp [hB m (not_lt.1 h)]

theorem coeff_zero_of_mem {f : Fin r → V} (hf : LinearIndependent Ω f) {n : ℕ} {a : Fin r → Ω}
    (h : ∑ m, a m • f m ∈ flagStep Ω f n) (m : Fin r) (hm : n ≤ (m : ℕ)) : a m = 0 := by
  obtain ⟨B, hB, e⟩ := (mem_flagStep_iff f n _).1 h
  have := Fintype.linearIndependent_iff.1 hf (a - B) (by simp [sub_smul, Finset.sum_sub_distrib, e]) m
  simpa [hB m hm] using this

theorem smul_mem_flagStep {f : Fin r → V} (hf : LinearIndependent Ω f) {m : Fin r} {t : Ω}
    (h : t • f m ∈ flagStep Ω f m) : t = 0 := by
  classical
  have := coeff_zero_of_mem hf (a := Pi.single m t) (n := m) (by simpa [Pi.single_apply] using h) m le_rfl
  simpa using this

theorem sum_sub_mem (f : Fin r → V) (m : Fin r) {B : Fin r → Ω} (hB : ∀ m' : Fin r, (m : ℕ) + 1 ≤ (m' : ℕ) → B m' = 0) :
    ∑ m', B m' • f m' - B m • f m ∈ flagStep Ω f m := by
  classical
  refine (mem_flagStep_iff f m _).2 ⟨B - Pi.single m (B m), fun m' hm' => ?_, ?_⟩
  · by_cases e : m' = m
    · simp [e]
    · have : (m' : ℕ) ≠ m := fun h => e (Fin.ext h)
      simp [e, hB m' (by omega)]
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]

theorem self_mem_flagStep (f : Fin r → V) (m : Fin r) : f m ∈ flagStep Ω f (m + 1) :=
  Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩

theorem flagStep_mono (f : Fin r → V) {n n' : ℕ} (h : n ≤ n') : flagStep Ω f n ≤ flagStep Ω f n' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem gr_span {b₀ bb : Fin r → V} (h₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω bb)
    (hf : ∀ n, flagStep Ω bb n = flagStep Ω b₀ n) (R : Subring Ω) (m : Fin r) {t : Ω}
    (ht : bb m - t • b₀ m ∈ flagStep Ω b₀ m) :
    t ≠ 0 ∧ Submodule.span R {t' : Ω | ∃ e ∈ Submodule.span R (Set.range bb), e - t' • b₀ m ∈ flagStep Ω b₀ m} =
      Submodule.span R {t} := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro rfl
    have : (1 : Ω) • bb m ∈ flagStep Ω bb m := by simpa [hf] using ht
    exact one_ne_zero (smul_mem_flagStep hb this)
  · rintro t' ⟨e, he, h⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have e1 : ∑ l, a l • bb l = ∑ l, (a l : Ω) • bb l := rfl
    rw [e1] at h
    have h1 : ∑ l, (a l : Ω) • bb l ∈ flagStep Ω bb (m + 1) := by
      rw [hf]
      have := Submodule.add_mem _ (flagStep_mono b₀ (Nat.le_succ _) h)
        (Submodule.smul_mem _ t' (self_mem_flagStep (Ω := Ω) b₀ m))
      simpa using this
    have h2 := sum_sub_mem bb m (B := fun l => (a l : Ω)) (coeff_zero_of_mem hb h1)
    rw [hf] at h2
    have h3 : (t' - a m * t) • b₀ m ∈ flagStep Ω b₀ m := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ h2 (Submodule.smul_mem _ (a m : Ω) ht)) h
      convert this using 1
      simp only [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := smul_mem_flagStep h₀ h3
    exact Submodule.mem_span_singleton.2 ⟨a m, by
      show (a m : Ω) * t = t'
      linear_combination -h4⟩
  · rintro _ rfl
    exact Submodule.subset_span ⟨bb m, Submodule.subset_span ⟨m, rfl⟩, ht⟩

end

section

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃)

theorem det_mul_rows {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) :
    (H * G).det = ∑ I : Fin n → Fin r, (∏ a, H a (I a)) * (Matrix.of fun a b => G (I a) b).det := by
  have e : (H * G : Matrix (Fin n) (Fin n) Ω₃) = fun a => ∑ l, H a l • G l := by
    funext a b
    simp [Matrix.mul_apply]
  have h := (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap.map_sum (fun a l => H a l • G l)
  have h' : (H * G).det = (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap (fun a => ∑ l, H a l • G l) := by
    rw [e]; rfl
  rw [h', h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem sup_minor_eq_one {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) (hH : ∀ a l, H a l ∈ O)
    (hG : ∀ l b, G l b ∈ O) (h : H * G = 1) :
    (Finset.univ.sup fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) = 1 := by
  refine le_antisymm (Finset.sup_le fun I _ => (O.valuation_le_one_iff _).2 ?_) ?_
  · rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hG _ _)
  · have e := det_mul_rows H G
    rw [h, Matrix.det_one] at e
    rw [← O.valuation.map_one, e]
    refine Valuation.map_sum_le _ fun I _ => ?_
    rw [map_mul]
    refine (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (prod_mem fun a _ => hH _ _))).trans ?_
    exact Finset.le_sup (f := fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) (Finset.mem_univ I)

theorem val_le_of_mem_span {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {S : Set Ω}
    {γ : O.ValueGroup} (hS : ∀ s ∈ S, O.valuation (i s) ≤ γ) {x : Ω} (hx : x ∈ Submodule.span R S) :
    O.valuation (i x) ≤ γ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    show O.valuation (i ((a : Ω) * x)) ≤ γ
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (hR _ a.2))).trans hx

theorem val_eq_of_span_eq {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {x y : Ω}
    (h : Submodule.span R {x} = Submodule.span R {y}) : O.valuation (i x) = O.valuation (i y) :=
  le_antisymm (val_le_of_mem_span O i R hR (S := {y}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self x))
    (val_le_of_mem_span O i R hR (S := {x}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self y))

end

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushVal
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition
end
end

