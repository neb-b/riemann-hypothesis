module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.Imports
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ChartNormCount.proof (hSC : ChartSpecCount.Statement) (hNP : ChartNormPts.Statement) :
    ChartNormCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hZ hj hfin
  classical
  have hchar : CharZero G.Φ := by
    refine charZero_of_inj_zero fun N hN => ?_
    have hmem : (C (N : ℤ) : MRing ι) ∈ imageZ v P' := by
      rw [← G.ker_x, RingHom.mem_ker]
      simpa using hN
    have h2 : (N : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := hmem
    rw [hZ.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot.mp h2)
  obtain ⟨E, hE, hcount⟩ := hSC (MRing ι) G.Φ G.Φ' (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom _
    (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) G.gen hfin
  refine ⟨E, fun hm => hE ?_, fun w hw hEw => ?_⟩
  · rw [← G.ker_x] at hm
    exact hm
  have hker : RingHom.ker (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) w) := by
    intro f hf
    have hf' : f ∈ imageZ v P' := by
      rw [← G.ker_x]
      exact hf
    have h0 := hw.2 f hf'
    rw [RingHom.mem_ker, coe_eval₂Hom]
    rwa [eval_map] at h0
  have hψE : eval₂Hom (Int.castRingHom ℂ) w E ≠ 0 := by
    rwa [coe_eval₂Hom, ← eval_map]
  obtain ⟨hZfin, hZcard, hZne⟩ := hcount _ hker hψE
  have hmh : IsMultiHomogIdeal P' := hP'.2.1.2.1
  have hiff : ∀ z' : (Σ k', ι' k') → ℂ, (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) (fun q => z' ⟨q.1.1, q.2⟩) F = 0) := by
    intro z' hzw hz1
    have hw' : (fun p => z' (v p)) = w := funext hzw
    have hwz : (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
      rw [hw']
      exact hw
    have h := hNP K ι K' ι' κ v P' G j hv hmh hj z' hwz hz1
    rw [hw'] at h
    exact h
  set Z := {y : (Σ k : FibreBlock κ, ι' k.1) → ℂ | ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) w) y F = 0} with hZdef
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hNdef
  let res : ((Σ k', ι' k') → ℂ) → (Σ k : FibreBlock κ, ι' k.1) → ℂ := fun z' q => z' ⟨q.1.1, q.2⟩
  have hinj : Set.InjOn res N := by
    intro a ha b hb hab
    funext q'
    obtain ⟨k', i⟩ := q'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨p, hp⟩ := hv.2.2.2 ⟨k', i⟩ h
      rw [← hp, ha.2.1 p, hb.2.1 p]
    · exact congrFun hab ⟨⟨k', h⟩, i⟩
  have himg : res '' N = Z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z', hz', rfl⟩
      exact (hiff z' hz'.2.1 hz'.2.2).1 hz'.1
    · intro y hy
      have hy1 : ∀ k : FibreBlock κ, y ⟨k, j k⟩ = 1 := by
        intro k
        have h := hy (X ⟨k, j k⟩ - 1) (by simp [div_self (hj k)])
        simpa [sub_eq_zero] using h
      let z' : (Σ k', ι' k') → ℂ := fun q' =>
        if h : q'.1 ∈ Set.range κ then w (hv.2.2.2 q' h).choose else y ⟨⟨q'.1, h⟩, q'.2⟩
      have hzw : ∀ p, z' (v p) = w p := by
        intro p
        have h : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
        have hc : (hv.2.2.2 (v p) h).choose = p := hv.2.1 (hv.2.2.2 (v p) h).choose_spec
        simp only [z', dif_pos h, hc]
      have hz1 : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1 := by
        intro k
        simp only [z', dif_neg k.2]
        exact hy1 k
      have hres : res z' = y := by
        funext q
        simp only [res, z', dif_neg q.1.2]
      refine ⟨z', ⟨(hiff z' hzw hz1).2 ?_, hzw, hz1⟩, hres⟩
      have : (fun q : Σ k : FibreBlock κ, ι' k.1 => z' ⟨q.1.1, q.2⟩) = y := hres
      rw [this]
      exact hy
  refine ⟨Set.Finite.of_finite_image (himg ▸ hZfin) hinj, ?_, ?_⟩
  · rw [← hinj.ncard_image, himg]
    exact hZcard
  · intro z' hz' hzw hz1 q hq
    have hy := (hiff z' hzw hz1).1 hz'
    exact hZne _ hy q (div_ne_zero hq (hj q.1))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ChartNormPts.proof : ChartNormPts.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G j hv hP' hj z' hw hz1
  classical
  have hcast : ∀ p : MRing ι', eval z' (map (Int.castRingHom ℂ) p) = aeval z' p := fun p => by
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hcoef : (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) =
      (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom := by
    ext c
    · simp
    · simp
  have hφ : (algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom =
      (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom := by
    ext c
    · simp
    · simp [G.compat]
  rw [hφ, hcoef]
  constructor
  · intro hz F hF
    have hH : ChartNormPts.homogenise v (fun q : Σ k : FibreBlock κ, ι' k.1 => (⟨q.1.1, q.2⟩ : Σ k', ι' k'))
        (fun q => ⟨q.1.1, j q.1⟩) F ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      show aeval G.x' _ = 0
      rw [ChartNormPts.aeval_homogenise_div v _ _ F G.x' fun q => hj q.1, hF, mul_zero]
    have h0 := hz.2 _ hH
    rwa [hcast, ChartNormPts.aeval_homogenise_one v _ _ F z' fun q => hz1 q.1] at h0
  · intro hF
    refine ⟨fun k' => ?_, fun f hf => ?_⟩
    · by_cases h : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := h
        obtain ⟨i, hi⟩ := hw.1 k
        replace hi : z' (v ⟨k, i⟩) ≠ 0 := hi
        revert hi
        generalize hq : v ⟨k, i⟩ = q
        obtain ⟨k₀, i₀⟩ := q
        intro hi
        have e : k₀ = κ k := by rw [← hv.2.2.1 ⟨k, i⟩, hq]
        subst e
        exact ⟨i₀, hi⟩
      · exact ⟨j ⟨k', h⟩, by rw [hz1 ⟨k', h⟩]; exact one_ne_zero⟩
    obtain ⟨S, hS, rfl⟩ := hP'
    suffices hle : Ideal.span S ≤ RingHom.ker (aeval z' : MRing ι' →ₐ[ℤ] ℂ) by
      rw [hcast]; exact hle hf
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS g hg
    let σ : (Σ k', ι' k') → MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) := fun q' =>
      if h : q'.1 ∈ Set.range κ then C (X (hv.2.2.2 q' h).choose) else X ⟨⟨q'.1, h⟩, q'.2⟩
    have hcomp : ∀ {R : Type} [CommRing R] (ψ : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* R),
        ψ (aeval σ g) = aeval (fun q' => ψ (σ q')) g := fun ψ =>
      comp_aeval_apply (f := σ) ψ.toIntAlgHom g
    have h1 := hF (aeval σ g)
    rw [← coe_eval₂Hom, ← coe_eval₂Hom, hcomp, hcomp] at h1
    let c : K' → G.Φ' := fun k' => if h : k' ∈ Set.range κ then 1 else (G.x' ⟨k', j ⟨k', h⟩⟩)⁻¹
    have hx : (fun q' => eval₂Hom (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom
        (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) (σ q')) = fun q' => c q'.1 * G.x' q' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, c, dif_pos h, coe_eval₂Hom, eval₂_C, one_mul]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, c, dif_neg h, coe_eval₂Hom, eval₂_X]
        rw [div_eq_inv_mul]
    have hz : (fun q' => eval₂Hom (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom
        (fun q => z' ⟨q.1.1, q.2⟩) (σ q')) = z' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, dif_pos h, coe_eval₂Hom, eval₂_C]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, dif_neg h, coe_eval₂Hom, eval₂_X]
    rw [hx, hz, ChartNormPts.aeval_smul_homog g a ha] at h1
    have hg0 : aeval G.x' g = 0 := by
      have : g ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [G.genericFibre_ker_target]; exact Ideal.subset_span hg
      exact this
    exact h1 (by rw [hg0, mul_zero])

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocChartRatio
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocChartRatio.proof (hF : FibreOverFinite.Statement) : SemilocChartRatio.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s α W i' hv hP' hZ hs hsn hW hi' q
  have hSf : (insert P' (fibreOver v P' W)).Finite :=
    (hF K ι K' ι' κ v P' n s α W hv hP' hZ hs hsn hW).insert P'
  have hSp : ∀ V ∈ insert P' (fibreOver v P' W), IsMultiProjPrime V := by
    rintro V (rfl | hV)
    · exact hP'.2.1
    · exact hV.1
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid _ hSf hSp
  obtain ⟨w, hwd, hwS⟩ := hd₀ (Pi.single q.1 1 + d₀) le_add_self
  have hPp : P'.IsPrime := hP'.2.1.1
  have hwP' : w ∉ P' := hwS P' (Set.mem_insert _ _)
  have hwnz : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  set N : MRing ι' := ∏ k, (X ⟨k, i' k⟩ : MRing ι') ^ d₀ k with hN
  have hNd : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog N d₀ := AvoidRing.isMultiHomog_coordProd i' d₀
  have hNP : N ∉ P' := AvoidRing.coordProd_not_mem hPp i' hi' d₀
  have hwW : ∀ W' ∈ fibreOver v P' W, w ∉ W' := fun W' hW' => hwS W' (Set.mem_insert_of_mem _ hW')
  have gen : ∀ u : MRing ι', ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u (Pi.single q.1 1 + d₀) →
      IsLocalization.mk' (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' u) ⟨_, hwnz⟩ ∈
        semiLocRing P' (fibreOver v P' W) := fun u hu =>
    Subring.subset_closure ⟨u, w, _, hwnz, hwW, hu, hwd, rfl⟩
  have hq : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X q * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 q.2) hNd
  have hc : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨q.1, i' q.1⟩ * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 (i' q.1)) hNd
  refine ⟨⟨_, gen _ hq⟩, ⟨_, gen _ hc⟩, ?_, ?_⟩
  · show IsLocalization.mk' _ _ _ ≠ (0 : FractionRing (MRing ι' ⧸ P'))
    rw [Ne, IsFractionRing.mk'_eq_zero_iff_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    rcases hPp.mem_or_mem h with h | h
    · exact hi' q.1 h
    · exact hNP h
  · show IsLocalization.mk' _ _ _ * _ = IsLocalization.mk' _ _ _ * _
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm (IsLocalization.mk' _ _ _),
      IsLocalization.mul_mk'_eq_mk'_of_mul]
    congr 1
    simp only [map_mul]
    ring

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocIntegral.proof (h₁ : ValCentreZ.Statement) (h₂ : CentreOverW.Statement) :
    SemilocIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hP hs hsP hW
  have := hP'.2.1.1
  letI := (locToSemiloc hv P' W).toAlgebra
  let f : locRing (imageZ v P') W →+* FractionRing (MRing ι' ⧸ P') :=
    (semiLocRing P' (fibreOver v P' W)).subtype.comp (locToSemiloc hv P' W)
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := (semiLocRing P' (fibreOver v P' W)).subtype)
    Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    obtain ⟨y, hy⟩ := h₁ K' ι' P' hP'.2.1 V
    have hcase := h₂ K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW V
      (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) y hy
    have hle : semiLocRing P' (fibreOver v P' W) ≤ V.toSubring := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
      have hwy : w ∉ y := by
        rcases hcase with rfl | hy'
        · exact fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        · exact hwW y hy'
      rw [SetLike.mem_coe, IsFractionRing.mk'_eq_div]
      exact (hy.2.2 a u w hu hwa hwy).1
    exact hle b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLengthSum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocLengthSum.proof (h₁ : SemilocFinite.Statement) (h₂ : SemilocMaxIdeals.Statement)
    (h₃ : SemilocResidueDeg.Statement) (h₄ : FibreDivSupp.Statement) (h₅ : LocRingDimOne.Statement)
    (h₆ : FibreOverFinite.Statement) :
    SemilocLengthSum.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hfin := h₆ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨hmax, hinj, hcov⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  have : IsLocalRing (locRing (imageZ v P') W) := (h₅ K ι (imageZ v P') s α W hPn.2.1 hs hsP hW).2.1
  have : Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) :=
    (h₁ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW).1
  let _ : Fintype (fibreOver v P' W) := hfin.fintype
  have hloc : ∀ W' : fibreOver v P' W, IsLocalRing (locRing P' W'.1) := fun W' =>
    haveI := W'.2.1.1; regularityLocalFlat_holds.isLocalRing W'.2.2.1
  let _ : ∀ W' : fibreOver v P' W, Algebra (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) :=
    fun W' => (semiToLoc P' _ W'.1 W'.2).toAlgebra
  have key := FieldNumbers.FiniteAlgebraLengthSum.proof.{0} (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))
    (fibreOver v P' W) (fun W' => semiMaxIdeal P' _ W'.1 W'.2) (fun W' => (hmax W'.1 W'.2).1)
    (fun W₁ W₂ h => Subtype.ext (hinj W₁.1 W₂.1 W₁.2 W₂.2 h))
    (fun M hM => by obtain ⟨W', hW', h⟩ := hcov M hM; exact ⟨⟨W', hW'⟩, @h (hloc ⟨W', hW'⟩)⟩)
    (fun W' => locRing P' W'.1) (fun W' => (hmax W'.1 W'.2).2) y

  refine ⟨hfin, ?_⟩
  have hyne : (y : FractionRing (MRing ι ⧸ imageZ v P')) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hy
    exact hsP hy
  have hs' : rename v s ∉ P' := hsP
  have hterm : ∀ W' : fibreOver v P' W,
      Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2) ≠ ⊤ ∧
      (((Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2)).toNat : ℕ) : ℤ) =
        if rename v s ∈ W'.1 then
          ((Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y))).toNat : ℤ) *
            E W'.1 else 0 := by
    intro W'
    obtain ⟨hW'p, hPW', hW'i⟩ := W'.2
    have := hW'p.1
    set x := algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
      (algebraMap (locRing (imageZ v P') W) _ y) with hxdef
    have hx : (x : FractionRing (MRing ι' ⧸ P')) = fracMapZ v P' y := by
      rw [hxdef, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, semiToLoc_coe, locToSemiloc_coe]
    have hord : Ring.ord (locRing P' W'.1) x =
        Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y)) := by
      have hI : locIdeal P' W'.1 (fracMapZ v P' y) = Ideal.span {x} := by
        rw [locIdeal, ← hx]
        congr 1
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact Subtype.ext_iff.symm
      rw [Ring.ord, hI]
    split_ifs with hsW'
    · obtain ⟨G', J', hJ', hEW'⟩ := hE W'.1 W'.2 hsW'
      obtain ⟨d, hd, hdE⟩ := h₃ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1 W'.2 G' J' hJ'
      have hdiv : W'.1 ∈ divSupp P' (rename v s) :=
        ((h₄ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1).1 ⟨W'.2, hsW'⟩).1
      obtain ⟨hN, -, hdim⟩ := h₅ K' ι' P' (rename v s) (Function.extend κ α 0) W'.1 hP'.2.1
        (rename_isMultiHomog hv hs) hs' hdiv
      have : Ring.KrullDimLE 1 (locRing P' W'.1) := by
        rw [Ring.krullDimLE_iff, hdim]
        rfl
      have hx0 : x ≠ 0 := fun h =>
        (map_ne_zero (fracMapZ v P')).mpr hyne (by rw [← hx, h, ZeroMemClass.coe_zero])
      have hfinord := Ring.ord_ne_top (R := locRing P' W'.1) (mem_nonZeroDivisors_of_ne_zero hx0)
      rw [hd, ← hord]
      refine ⟨WithTop.mul_ne_top hfinord (ENat.natCast_ne_top d), ?_⟩
      rw [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hdE, hEW']
    · have ht' : rename v t ∉ W'.1 := fun h => htW (hW'i ▸ h)
      have hxe : (x : FractionRing (MRing ι' ⧸ P')) * regularityLocalFlat_holds.fracHom P' (rename v t) =
          regularityLocalFlat_holds.fracHom P' (rename v s) := by
        rw [hx, regularityLocalFlat_holds.fracHom_apply, regularityLocalFlat_holds.fracHom_apply, ← fracMapZ_algebraMap, ← fracMapZ_algebraMap,
          ← map_mul, hy]
      have hu : IsUnit x := (regularityLocalFlat_holds.isUnit_iff hPW' x (rename_isMultiHomog hv hs) (rename_isMultiHomog hv ht) ht'
        hxe).mpr hsW'
      rw [Ring.ord_of_isUnit hu, zero_mul]
      simp
  have hset : {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'} =
      ↑(hfin.toFinset.filter (fun W' => rename v s ∈ W')) := by
    ext
    simp
  have hsum := ENat.sum_ne_top.mpr fun W' (_ : W' ∈ Finset.univ) => (hterm W').1
  rw [key]
  refine ⟨_, (ENat.natCast_toNat hsum).symm, ?_⟩
  rw [ENat.toNat_sum fun W' _ => (hterm W').1, Nat.cast_sum, hset, finsum_mem_coe_finset, Finset.sum_filter,
    Finset.sum_subtype (F := hfin.fintype) hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  exact Finset.sum_congr rfl fun W' _ => (hterm W').2

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocResidueAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩)) : ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFibreDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocResidueFibreDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ W' ∈ fibreOver v P' W, ∀ G' : GenFibre v W', IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0

end GroundTheory.Heights₂.Heights.Inter
end
end

