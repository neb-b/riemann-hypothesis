module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace GenKoszulStep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem subsingleton_cechHc_iff {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c (n + 1)) ↔
      ∀ x ∈ KH.cechCc ι 𝓜 c (n + 1), KH.cechD S ι M (n + 1) x = 0 →
        ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechD S ι M n y = x := by
  rw [KH.cechHc, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hdx
    have hZ : x ∈ KH.cechZc ι 𝓜 c (n + 1) := ⟨hx, hdx⟩
    obtain ⟨y, hy, hyx⟩ := h (Submodule.mem_top (x := ⟨x, hZ⟩))
    exact ⟨y, hy, hyx⟩
  · rintro h ⟨x, hx, hdx⟩ -
    obtain ⟨y, hy, hyx⟩ := h x hx hdx
    exact ⟨y, hy, hyx⟩

theorem gather {V : Ideal (MRingOver S ι)} {α : K → ℤ} (h : KH.GeneratedV S V α) :
    ∃ (R : ℕ) (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
      (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) ∧
      ∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
        (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1 := by
  classical
  choose r zz uu hz hu hs using h
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  let _ : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  set e := Fintype.equivFin (Σ I : KH.Cell K ι 0, Fin (r I))
  let v : ∀ I : KH.Cell K ι 0, (Σ I' : KH.Cell K ι 0, Fin (r I')) →
      LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I σ => if h : σ.1 = I then h ▸ uu σ.1 σ.2 else 0
  refine ⟨Fintype.card (Σ I : KH.Cell K ι 0, Fin (r I)), fun j => zz (e.symm j).1 (e.symm j).2,
    fun j => hz _ _, fun I => ⟨fun j => v I (e.symm j), fun j => ?_, ?_⟩⟩
  · have hv : ∀ σ, v I σ ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := by
      rintro ⟨I', i⟩
      simp only [v]
      split_ifs with hI
      · subst hI
        exact hu _ i
      · exact Submodule.zero_mem _
    exact hv (e.symm j)
  · rw [Equiv.sum_comp e.symm (fun σ => v I σ * zz σ.1 σ.2 I), Fintype.sum_sigma,
      Finset.sum_eq_single I]
    · simp only [v, dif_pos rfl]
      exact hs I
    · intro I' _ hI'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [v, dif_neg hI']
      exact zero_mul (zz I' i I)
    · simp

end GenKoszulStep

open GenKoszulStep

theorem GenKoszulStep.proof (hB : KoszulCechComplex.Statement) (hC : KoszulCechExact.Statement)
    (hD : DoubleComplexVanish.Statement) (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) :
    GenKoszulStep.Statement := by
  intro S _ K _ _ ι _ _ V α _ hα
  obtain ⟨R, z, hz, hu⟩ := gather hα
  refine ⟨R, fun c hc => ?_⟩
  have hB' := hB S K ι V α R z hz c
  have hC' := hC S K ι V α R z hu c
  have key := hD (fun p n => KosC S ι V R p n) (fun p n => kosPart S ι V R α c p n)
    (fun p n => kosCech S ι V R p n) (fun p n => kosD z p n) R
    (fun p n x hx J _ => hDeg S K ι _ _ _ n (x J) (hx J trivial))
    (fun p n x hx => (hB' p n).1 x hx)
    (fun p n x _ => funext fun J => LinearMap.congr_fun (hSq S K ι (MRingOver S ι ⧸ V) n) (x J))
    (fun p n x _ => (hB' p n).2.1 x)
    (fun p n x _ => (hB' p n).2.2 x)
    (fun n x hx => (hC' n).1 x hx)
    (fun p n x hx h0 => (hC' n).2 p x hx h0)
    (fun p n hp x _ => funext fun J => absurd ((J.2.symm.trans_le (J.1.card_le_univ)).trans_eq
      (Fintype.card_fin R)) (by omega))
    (fun p hp1 hpR n x hx h0 => by
      have hJ := fun J => (subsingleton_cechHc_iff _ _ n).mp (hc p hp1 hpR (n + 1) (by omega))
        (x J) (hx J trivial) (congrFun h0 J)
      choose y hy hdy using hJ
      exact ⟨y, fun J _ => hy J, funext hdy⟩)
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [subsingleton_cechHc_iff]
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := key n (fun _ => x) (fun J _ => by simpa using hx) (funext fun _ => hdx)
  exact ⟨y ⟨∅, Finset.card_empty⟩, by simpa using hy _ trivial, congrFun hdy _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNefGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GeneratedNefGeneric.eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

theorem GeneratedNefGeneric.isProjVarF_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) d := by
  obtain ⟨-, ⟨hWp, ⟨S, hS, hWS⟩, hrel⟩, hhor, hdim⟩ := hW
  have : W.IsPrime := hWp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ W → m = 0 := by
    intro m hm
    have h1 : m ∈ W.comap (C : ℤ →+* MRing ι) := hm
    rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec W hchar
  have hq : ReciprocityTheory.AnForm.R.extQ W = W.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show W.map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hWS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GeneratedNefGeneric.eq_natCast_of_add_one_eq (d + Fintype.card K) _ ?_
    rw [hform, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega]
    push_cast
    rfl

theorem GeneratedNefGeneric.proof (hG : GenOnFibres.Statement) (hR : GeneratedRestrict.Statement)
    (hN : GeneratedProductNonneg.Statement) : GeneratedNefGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a q w _ hw hgen W hW hPW
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hQ : KH.GeneratedV ℚ (KH.genIdeal y) a := (hG K ι Ω y a q w hw hgen).1
  have hWQ : KH.GeneratedV ℚ (W.map (MvPolynomial.map (Int.castRingHom ℚ))) a :=
    hR ℚ K ι _ _ a (Ideal.map_mono hPW) hQ
  have hV : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GeneratedNefGeneric.isProjVarF_map (d := 1) hW
  have h := hN ℚ K ι (fun V _ L => NumbersDVR.intNum ℚ V L) _ 1 (fun _ => a)
    (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) hV (fun _ => hWQ)
  unfold genDeg
  convert h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjDegGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace ProjDegGenDeg

theorem succ_rpow_isBigO (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  refine IsBigO.of_bound (2 ^ D) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_sub_one (by positivity), Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) ^ D / ((n : ℝ) + 1) ≤ (2 * (n : ℝ)) ^ D / n :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _) hpos (by linarith)
    _ = 2 ^ D * ((n : ℝ) ^ D / n) := by rw [mul_pow]; ring

theorem pow_div_isLittleO (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun n : ℕ => (1 : ℝ) / n) =o[atTop] fun _ : ℕ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr tendsto_one_div_atTop_nhds_zero_nat
  exact (h1.mul_isBigO (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop)).congr (fun n => by ring)
    (fun n => by ring)

theorem eq_zero_of_isBigO (D : ℕ) (c : ℝ)
    (h : (fun n : ℕ => c * (n : ℝ) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) : c = 0 := by
  by_contra hc
  have h2 := (isLittleO_const_mul_left_iff hc).mp (h.trans_isLittleO (pow_div_isLittleO D))
  refine isLittleO_irrefl ?_ h2
  refine (eventually_ge_atTop 1).frequently.mono fun n hn => ?_
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

end ProjDegGenDeg


open ProjDegGenDeg in
theorem ProjDegGenDeg.proof (hR : RankOfSections.Statement) : ProjDegGenDeg.Statement := by
  intro D Ω _ _ κ _ x e hA hF
  obtain ⟨hq, hdim⟩ := GenericFibre.proof Ω κ x D hA
  obtain ⟨C, hC⟩ := hR κ _ D hq hdim
  set γ : ℤ := genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 with hγ
  have hγ' : GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = γ := by
    rw [hγ]; unfold genDeg; congr 1

  have h1 : (fun n : ℕ => (Module.finrank ℤ (sec ℤ x n) : ℝ) - (γ : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
    refine IsBigO.trans ?_ (succ_rpow_isBigO D)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    have hn := hC n
    rw [hγ', SectionsRank.proof Ω κ x n] at hn
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast hn

  have h2 := finrank_sec_asymp x e hF
  have h3 : (fun n : ℕ => (((projDeg x e : ℝ) - (γ : ℝ)) / (D.factorial : ℝ)) * (n : ℝ) ^ D)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) :=
    (h1.sub h2).congr_left fun n => by ring
  have h4 := eq_zero_of_isBigO D _ h3
  have hfac : (D.factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_zero_iff, sub_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact_mod_cast h4.symm
  · exact absurd h4 hfac

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Cardinal

noncomputable section

theorem exists_ringHom_complex_ker_eq_of_isPrime {σ : Type} [Finite σ] (P : Ideal (MvPolynomial σ ℚ))
    [P.IsPrime] : ∃ φ : MvPolynomial σ ℚ →+* ℂ, ∀ f, φ f = 0 ↔ f ∈ P := by
  let Q := MvPolynomial σ ℚ ⧸ P
  let F := FractionRing Q
  have : CharZero F := charZero_of_injective_algebraMap (R := ℚ) (algebraMap ℚ F).injective
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  refine ⟨(ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P), fun f => ?_⟩
  have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
    ψ.injective.comp (IsFractionRing.injective Q F)
  rw [RingHom.comp_apply, map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]

theorem PullConeNull.proof : PullConeNull.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL
  set I := coneNullIdeal y L

  have hrad : ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ∈ I.radical := by
    intro c
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) ⟨hIP, hP⟩
    obtain ⟨φ, hker⟩ := exists_ringHom_complex_ker_eq_of_isPrime P
    let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
    have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ (map (Int.castRingHom ℚ) f) := by
      intro f
      have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ.comp (map (Int.castRingHom ℚ)) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · exact RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C)
            ((φ.comp (map (Int.castRingHom ℚ))).comp C)) r
        · simp [z]
      exact RingHom.congr_fun h f
    by_contra hc
    have hz : z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_⟩
      · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
        exact Ideal.mul_mem_right _ P ((hker _).mp h0)
      · rw [hev, hker]
        exact hIP (Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩))
    obtain ⟨j, hj⟩ := hL z hz
    apply hj
    rw [hev, hker]
    exact hIP (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
  choose n hn using fun c => Ideal.mem_radical_iff.mp (hrad c)
  refine ⟨Finset.univ.sup n, fun c => ?_⟩
  have hle : n c ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ c)
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact I.mul_mem_right _ (hn c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftIntersectionPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply)

noncomputable section

namespace ShiftIntersectionPolynomial

theorem prod_weights {n : ℕ} (q : ℝ) (s : Fin n → Fin 2) :
    ∏ j, (![q, 1] : Fin 2 → ℝ) (s j) = q ^ (Finset.univ.filter fun j => s j = 0).card := by
  have h : ∀ j, (![q, 1] : Fin 2 → ℝ) (s j) = if s j = 0 then q else 1 := by
    intro j
    rcases Fin.exists_fin_two.mp ⟨s j, rfl⟩ with h | h <;> rw [h] <;> simp
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem proof : ShiftIntersectionPolynomial.Statement := by
  intro K _ ι _ II P n A B hII hP hA hB
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![A, B] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h <;> rw [h] <;> simpa [e]
  refine ⟨∑ s : Fin n → Fin 2, Polynomial.C (II K ι P n (e ∘ s)) *
      Polynomial.X ^ (Finset.univ.filter fun j => s j = 0).card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (fun _ => 0)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      have hc : (Finset.univ.filter fun j : Fin n => (fun _ : Fin n => (0 : Fin 2)) j = 0).card = n := by simp
      rw [if_pos hc.symm]
      rfl
    · intro s _ hs
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro hc
      apply hs
      have hu : (Finset.univ.filter fun j => s j = 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      funext j
      have := Finset.filter_eq_self.mp hu j (Finset.mem_univ j)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q
    set Z := HermLine.zcomb A B (q : ℤ) 1 with hZ_def
    have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hA hB _ _
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        II K ι P n (Function.update L a Z) =
          (![(q : ℝ), 1] : Fin 2 → ℝ) 0 * II K ι P n (Function.update L a (e 0)) +
            (![(q : ℝ), 1] : Fin 2 → ℝ) 1 * II K ι P n (Function.update L a (e 1)) := by
      intro L a hL
      cases n with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hA hB (q : ℤ) 1
        simp only [Int.cast_natCast, Int.cast_one, one_mul] at h
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm e Z ![(q : ℝ), 1] he hZ hposition
      Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, famExt_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_weights, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end ShiftIntersectionPolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphFibreRatio
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphFibreRatio.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    ∀ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (k : K) (i j : ι k),
      G.x' ⟨Sum.inl k, j⟩ ≠ 0 → G.x' ⟨Sum.inl k, i⟩ / G.x' ⟨Sum.inl k, j⟩ ∈ (algebraMap G.Φ G.Φ').range

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n r : ℕ) (b : Fin r → MvPolynomial (Σ k, ι k) ℚ),
    IsSecBasisM d.y d.k₀ n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (blockPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

