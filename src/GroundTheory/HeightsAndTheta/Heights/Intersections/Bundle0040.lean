module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ChartCongr
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegreeAfterAdjoining.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem VerticalDegreeAfterAdjoining.proof (hA : RankAdjoinFrac.Statement) (hB : FnDegAdjoin.Statement)
    (hT : ChartScalingIndep.Statement) (hC : AdjoinIndepRelfinrank.Statement)
    (hD : FinrankAdjoinRange.Statement) : VerticalDegreeAfterAdjoining.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW _ hc G'

  have hpΩ : ((p : ℕ) : G'.Φ') = 0 := by
    have h : ((p : ℕ) : MRing ι') ∈ RingHom.ker (aeval G'.x' : MRing ι' →ₐ[ℤ] G'.Φ') := G'.genericFibre_ker_target.symm ▸ hp
    rwa [RingHom.mem_ker, map_natCast] at h
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have : CharP G'.Φ p := ((algebraMap G'.Φ G'.Φ').charP_iff_charP p).2 inferInstance
  let : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  let : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

  have hker : RingHom.ker (aeval G'.x' : MRingOver (ZMod p) ι' →ₐ[ZMod p] G'.Φ') =
      W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
    ext g
    obtain ⟨f, rfl⟩ := PointVertical.red_surjective (ι := ι') p g
    have e : aeval G'.x' (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = aeval G'.x' f := by
      rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
    rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, e, ← RingHom.mem_ker, G'.genericFibre_ker_target]
  rw [← hker] at hW hc ⊢
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hc k' (by rw [RingHom.mem_ker, aeval_X, h])
  have hmh := hW.1.2.1

  let y' : (Σ k', ι' k') → G'.Φ' := fun q => G'.x' q / G'.x' ⟨q.1, i' q.1⟩
  let t : K → G'.Φ' := fun k => G'.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ').fieldRange
  let L₀ := IntermediateField.adjoin (ZMod p) (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin (ZMod p) (Set.range y')
  let E := IntermediateField.adjoin (ZMod p) (Set.range t)
  have mono : ∀ {A B : Set G'.Φ'}, A ⊆ B → IntermediateField.adjoin (ZMod p) A ≤ IntermediateField.adjoin (ZMod p) B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G'.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => VerticalDegreeAfterAdjoining.chart_congr G'.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G'.Φ G'.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G'.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G'.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G'.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G'.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G'.compat]
          refine mul_mem hf ?_
          have hq : G'.x' (v q) = y' (v q) * t q.1 := by
            show _ = G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ' (aeval G'.x f / aeval G'.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin (ZMod p)
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩) := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_)
      (((le_sup_right : E ≤ L₀ ⊔ E).trans hL₀E.le).trans le_sup_left)) (sup_le ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hv.2.2.2 q hq
        exact (le_sup_left : Φ₁ ≤ _) (hyv r)
      · exact (le_sup_right : IntermediateField.adjoin _ _ ≤ _)
          (IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩)
    · rw [← hL₀E]
      exact sup_le_sup_right (mono (Set.range_comp_subset_range v y')) E
    · refine (mono ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨q.1.1, q.2⟩, rfl⟩

  have hindep : AlgebraicIndependent L t := (hT (ZMod p) G'.Φ' K' ι' G'.x' i' hx hmh).comp κ hv.1
  refine Eq.trans (hB (ZMod p) G'.Φ' K ι K' ι' v G'.x' i' hx hmh)
    (Eq.trans (hA (ZMod p) G'.Φ' _ _ (Set.range_comp_subset_range v y')) ?_)
  rw [← hC (ZMod p) G'.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep, hD (ZMod p) G'.Φ G'.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldExistsInv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_intCast_coe (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by
  rw [eq_intCast C n, map_intCast, map_intCast]
  simp

theorem funField_exists_inv {P : Ideal (MRing ι)} [hPp : P.IsPrime] (y : funField P)
    (hy : (y : FractionRing (MRing ι ⧸ P)) ≠ 0) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hFL : (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := y.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hv, hvP, huv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL
  have huP : u ∉ P := fun h => by
    have h0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
    rw [← huv] at h0
    exact mul_ne_zero hy (hφ v hvP) h0
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hv hu huP
  refine ⟨x, mul_right_cancel₀ (hφ v hvP) ?_⟩
  rw [mul_assoc, huv, hx, one_mul]

theorem regRing_exists_coe {P : Ideal (MRing ι)} {y : funField P} (hy : y ∈ regRing P) :
    ∃ b : regRing P, (b : funField P) = y :=
  ⟨⟨y, hy⟩, rfl⟩

theorem RegularityMaximalSurjective.proof (h₁ : RegularityOrder.Statement) (h₂ : RegularityLocalPrime.Statement) : RegularityMaximalSurjective.Statement := by
  classical
  intro K _ ι _ P hP m hm
  have hPp : P.IsPrime := hP.2.1.1
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof

  have hmZ : (m.comap (algebraMap ℤ (regRing P))).IsMaximal := by
    have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
    have : Algebra.IsIntegral ℤ (regRing P) := Algebra.IsIntegral.of_finite ℤ _
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) m
  have hp := Submodule.IsPrincipal.prime_generator_of_isPrime (is_prime := hmZ.isPrime) _
    (Ring.ne_bot_of_isMaximal_of_not_isField hmZ Int.not_isField)
  set p := Submodule.IsPrincipal.generator (m.comap (algebraMap ℤ (regRing P)))
  have hZ : ∀ n : ℤ, (n : regRing P) ∈ m ↔ p ∣ n := fun n => by
    rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
  have hCp : C p ∉ P := fun h => by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hP.2.2.1] at h'
    exact hp.ne_zero (Ideal.mem_bot.mp h')
  have hp0 : (p : regRing P) ≠ 0 := fun h => by
    have h' := regRing_intCast_coe P p
    rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem] at h'
    exact hCp h'

  have hS : {W | IsClosedPt W ∧ P ≤ W ∧ C p ∈ W}.Finite :=
    (divSupp_finite P (C p)).subset fun W hW =>
      (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W hP (RegularityDenominator.isMultiHomog_C p) hCp).2 hW
  let g : Ideal (MRing ι) → Ideal (regRing P) := fun W =>
    if h : IsClosedPt W ∧ P ≤ W then regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 else ⊥
  have hgW : ∀ W (h : IsClosedPt W ∧ P ≤ W), g W = regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 :=
    fun W h => dif_pos h
  by_contra hcon
  push Not at hcon

  let T : Finset (Ideal (regRing P)) := insert ⊥ (hS.toFinset.image g)
  have hT : ¬ ((m : Set (regRing P)) ⊆ ⋃ i ∈ (↑T : Set (Ideal (regRing P))), ((fun i => i) i : Set (regRing P))) := by
    rw [Ideal.subset_union_prime (f := fun i : Ideal (regRing P) => i) ⊥ ⊥ fun i hi h1 _ => ?_]
    · rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hp0 (Ideal.mem_bot.1 (hle ((hZ p).2 dvd_rfl)))
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        obtain ⟨x, hx, z, hz, hxz⟩ := hcon W hWc hPW
        have h' := hle hx
        rw [hgW W ⟨hWc, hPW⟩] at h'
        exact (not_mem_regMaxAt_iff hWc hPW _ x).2 ⟨z, hz, hxz⟩ h'
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact absurd rfl h1
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        rw [hgW W ⟨hWc, hPW⟩]
        exact (regMaxAt_isMaximal h₁ hL hP hWc hPW _).isPrime
  obtain ⟨a, ham, ha⟩ := Set.not_subset.1 hT
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at ha
  have ha0 : ((a : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h =>
    ha ⊥ (Finset.mem_insert_self _ _) (Ideal.mem_bot.2 (Subtype.ext (Subtype.ext (by rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))))

  obtain ⟨x, hxa⟩ := funField_exists_inv (a : funField P) ha0
  obtain ⟨n, hpn, hn⟩ := h₂ K ι P p x hP hp fun W hWc hPW hpW => by
    have h' := ha (g W) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (hS.mem_toFinset.2 ⟨hWc, hPW, hpW⟩)))
    rw [hgW W ⟨hWc, hPW⟩] at h'
    obtain ⟨z, hz, haz⟩ := (not_mem_regMaxAt_iff hWc hPW _ a).1 h'
    rwa [show (x : FractionRing (MRing ι ⧸ P)) = z by rw [← mul_one (x : FractionRing (MRing ι ⧸ P)), ← haz,
      ← mul_assoc, hxa, one_mul]]

  refine hpn ((hZ n).1 ?_)
  obtain ⟨b, hb⟩ := regRing_exists_coe hn
  have he : a * b = (n : regRing P) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hb, Subring.coe_mul, Subring.coe_intCast, Subring.coe_intCast,
      Subring.coe_intCast]
    rw [mul_left_comm, mul_comm ((a : funField P) : FractionRing (MRing ι ⧸ P)), hxa, mul_one]
  rw [← he]
  exact m.mul_mem_right b ham

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBis
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ArithmeticIntersectionDivisorPushforward.proof (hDeh : regularityDehomogenization_holds.Statement) (hLoc : LocRingDimOne.Statement)
    (hFin : SemilocFinite.Statement) (hRank : SemilocRank.Statement) (hLen : SemilocLength.Statement) :
    ArithmeticIntersectionDivisorPushforward.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE
  have : P'.IsPrime := hP'.2.1.1
  have : (imageZ v P').IsPrime := hP.2.1.1

  obtain ⟨t, ht, htW⟩ := exists_form_notMem hW.2 hW.1.1.1 α
  have ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P'))
      (Ideal.Quotient.mk _ t) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))
  set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) /
    algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy
  have hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) := div_mul_cancel₀ _ ht0
  obtain ⟨hyA, hm⟩ := hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt
  obtain ⟨hNoeth, hLocal, hDim⟩ := hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW
  let _ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) := (locToSemiloc hv P' W).toAlgebra
  obtain ⟨hBf, hBt⟩ := hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW
  have hrk := hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW
  obtain ⟨N, hlen, hN⟩ := hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE
  have hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0 := fun h => by
    have h' : y = 0 := congrArg Subtype.val h
    rw [hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact h'.elim hsP ht0

  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim
  have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0
  have hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ =
      (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞) := by
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)
    rw [hm, locIdeal_eq_span hyA]
    exact (ENat.natCast_toNat hfin).symm
  rw [hlen, hord] at key
  have hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) *
      multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    exact_mod_cast key
  rw [← hN, hNat, ← hrk]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalize.exists_prime_over {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  have : W.IsPrime := hW.1.1
  have : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.IsPrime.comap _
  refine ⟨_, Submodule.IsPrincipal.prime_generator_of_isPrime _ hvert, fun k => ?_⟩
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap]

theorem RegularityLocalize.proof (h₁ : RegularityLocalPrime.Statement) : RegularityLocalize.Statement := by
  classical
  intro K _ ι _ P W y hP hW hPW hy
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1
  have hφ : ∀ f : MRing ι, f ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hf
  obtain ⟨p, hp, hpW⟩ := RegularityLocalize.exists_prime_over hP hW
  have hCpP : (C p : MRing ι) ∉ P := fun h => hp.ne_zero (by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rwa [hP.2.2.1, Ideal.mem_bot] at h')

  set S : Set (Ideal (MRing ι)) := {W' | IsClosedPt W' ∧ P ≤ W' ∧ C p ∈ W'} with hS
  have hSfin : S.Finite := (divSupp_finite P (C p)).subset fun W' hW' =>
    (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W' hP (RegularityDenominator.isMultiHomog_C p) hCpP).2 hW'
  have hWS : W ∈ S := ⟨hW, hPW, (hpW p).2 dvd_rfl⟩
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSfin fun W' hW' => hW'.1.1

  obtain ⟨u₀, v₀, a, hu₀, hv₀, hv₀W, hyv₀⟩ := LocRingFrac.proof K ι P W hPp hWp hPW y hy
  choose c hc using hW.1.2.2
  obtain ⟨t, ht, htW⟩ : ∃ t : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t 1 ∧ t ∉ W :=
    ⟨_, AvoidRing.isMultiHomog_coordProd c 1, AvoidRing.coordProd_not_mem hWp c hc 1⟩
  obtain ⟨u, v, hu, hv, hvW, hyv⟩ : ∃ u v : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u (a + 1) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog v (a + 1) ∧ v ∉ W ∧
      y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
    ⟨u₀ * t, v₀ * t, AvoidRing.isMultiHomog_mul hu₀ ht, AvoidRing.isMultiHomog_mul hv₀ ht,
      fun h => (hWp.mem_or_mem h).elim hv₀W htW, by simp only [map_mul, ← mul_assoc, hyv₀]⟩

  set m := ∑ k, d₀ k
  obtain ⟨h, hh, hhS⟩ := hd₀ ((m + 1) • (a + 1)) fun k => by
    have h1 : d₀ k ≤ m := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    nlinarith
  have hhW : h ∉ W := hhS W hWS
  have hhP : h ∉ P := fun e => hhW (hPW e)
  have hvm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (v ^ (m + 1)) ((m + 1) • (a + 1)) := AvoidRing.isMultiHomog_pow hv _
  have hxm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (v ^ m * u) ((m + 1) • (a + 1)) := by
    rw [succ_nsmul]; exact AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_pow hv _) hu
  obtain ⟨s₀, hs₀⟩ := exists_funField_mul_eq hvm hh hhP
  obtain ⟨x₀, hx₀⟩ := exists_funField_mul_eq hxm hh hhP
  have hys : y * (s₀ : FractionRing (MRing ι ⧸ P)) = x₀ := by
    refine mul_right_cancel₀ (hφ h hhP) ?_
    rw [mul_assoc, hs₀, hx₀]
    simp only [map_pow, map_mul]
    rw [pow_succ, ← hyv]
    ring

  have hover : ∀ z : funField P, (∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g ((m + 1) • (a + 1)) ∧
      (z : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P h) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
      ∀ W', IsClosedPt W' → P ≤ W' → C p ∈ W' → (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W' :=
    fun z ⟨g, hg, hz⟩ W' h1 h2 h3 => frac_mem_locRing h2 hg hh (hhS W' ⟨h1, h2, h3⟩) hz
  obtain ⟨n₁, hn₁, hs⟩ := h₁ K ι P p s₀ hP hp (hover s₀ ⟨_, hvm, hs₀⟩)
  obtain ⟨n₂, hn₂, hx⟩ := h₁ K ι P p x₀ hP hp (hover x₀ ⟨_, hxm, hx₀⟩)
  have hsc : (((n₂ : regRing P) * ⟨_, hs⟩ : regRing P) : funField P) = (n₂ : funField P) * ((n₁ : funField P) * s₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  have hxc : (((n₁ : regRing P) * ⟨_, hx⟩ : regRing P) : funField P) = (n₁ : funField P) * ((n₂ : funField P) * x₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  refine ⟨(n₂ : regRing P) * ⟨_, hs⟩, (n₁ : regRing P) * ⟨_, hx⟩, ?_, ?_⟩
  ·
    have hnW : (C (n₁ * n₂) : MRing ι) ∉ W := fun e => by
      rcases hp.dvd_or_dvd ((hpW _).1 e) with h' | h'
      exacts [hn₁ h', hn₂ h']
    have hden : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C (n₁ * n₂) * v ^ (m + 1)) ((m + 1) • (a + 1)) := by
      simpa using AvoidRing.isMultiHomog_mul (RegularityDenominator.isMultiHomog_C (n₁ * n₂)) hvm
    have hdenW : C (n₁ * n₂) * v ^ (m + 1) ∉ W := fun e =>
      (hWp.mem_or_mem e).elim hnW fun e' => hvW (hWp.mem_of_pow_mem _ e')
    have hden0 := hφ _ fun e => hdenW (hPW e)
    refine ⟨_, frac_mem_locRing hPW hh hden hdenW (div_mul_cancel₀ _ hden0), ?_⟩
    rw [hsc, mul_div_assoc', div_eq_one_iff_eq hden0]
    simp only [map_mul, eq_intCast C, map_intCast, Int.cast_mul, Subring.coe_mul, Subring.coe_intCast, ← hs₀]
    ring
  · rw [hsc, hxc]
    simp only [Subring.coe_mul, Subring.coe_intCast, ← hys]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurther
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PullbackVanishingOfNullCycle.proof (hElim : PullbackEliminationOfVariable.Statement) : PullbackVanishingOfNullCycle.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' J' n Ψ hv hP' hP hΨ hJ hJP
  obtain ⟨h, a, hha, hhP, hvan⟩ := hElim K ι K' ι' κ v P' J' n hv hP' hP hJ hJP
  have hJh : IsMultiHomogIdeal (Ideal.span {h}) :=
    ⟨{h}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hha⟩, rfl⟩
  have hJhP : ¬ Ideal.span {h} ≤ imageZ v P' := fun hle => hhP (hle (Ideal.subset_span rfl))
  refine measure_mono_null ?_ (projB_null Ψ hP hΨ hJh hJhP)
  rintro y ⟨z', hz'P, hz'J, -, -, -, hΨy⟩
  set w : (Σ k, ι k) → ℂ := fun p => z' (v p) with hw
  have hw1 : (Ψ (segre w) 0)⁻¹ * Ψ (segre w) 0 = 1 := by
    have := congrFun hΨy 0
    simpa [map_smul] using this
  have h0 : Ψ (segre w) 0 ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre w) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre w) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hwP : w ∈ mcPts (imageZ v P') := IntersectionWithSection.comp_mem_mcPts hv hz'P
  have hwh : w ∈ mcPts (Ideal.span {h}) := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hvan z' hz'P hz'J, mul_zero]
  refine ⟨fun p => c p.1 * w p, mcPts_smul hP.2.1.2.1 c hc hwP, mcPts_smul hJh c hc hwh, ?_⟩
  rw [segre_smul, hpc]
  exact hΨy

end GroundTheory.Heights₂.Heights.Inter
end
end

