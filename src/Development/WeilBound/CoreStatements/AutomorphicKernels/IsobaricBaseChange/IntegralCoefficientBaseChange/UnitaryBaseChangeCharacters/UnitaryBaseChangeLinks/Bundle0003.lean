module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittFN
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittHS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.AdelicClassCountProduct
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_mem_eq_zero_of_factor {ι : Type} (f : ι → ℂ) (S : Set ι)
    (hfin : {w | f w ≠ 1}.Finite) {w₀ : ι} (hw₀ : w₀ ∈ S) (h0 : f w₀ = 0) :
    ∏ᶠ w ∈ S, f w = 0 := by
  have hs : (S ∩ Function.mulSupport f).Finite := hfin.subset fun w hw => hw.2
  rw [finprod_mem_eq_prod f hs]
  refine Finset.prod_eq_zero (i := w₀) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw₀, ?_⟩
  rw [Function.mem_mulSupport, h0]
  exact zero_ne_one

theorem finsum_finprod_local_sums_expand : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  intro ι S Cl _ D R _ loc O s good N hA hB hC hD hE
  classical
  haveI : ∀ w, Fintype (Cl w) := fun w => Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨T, hTfin, hTA⟩ : ∃ T : Set ι, T.Finite ∧ ∀ w, w ∉ T →
      ((∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) :=
    ⟨_, Filter.eventually_cofinite.1 hA, fun w hw => not_not.1 hw⟩
  have hO : ∀ w, w ∉ T → ∀ c, O w c = if good w c then 1 else 0 := fun w hw c => ((hTA w hw).2 c).1
  have hs1 : ∀ w, w ∉ T → ∀ c, good w c → ∀ d, s d w c = 1 := fun w hw c => ((hTA w hw).2 c).2
  have huniq : ∀ w, w ∉ T → ∀ c c', good w c → good w c' → c = c' :=
    fun w hw c c' hc hc' => (hTA w hw).1.unique hc hc'
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ w, w ∈ F ↔ w ∈ S ∧ w ∈ T :=
    ⟨hTfin.toFinset.filter (· ∈ S), fun w => by simp [and_comm]⟩
  obtain ⟨ext, ext_F, ext_good⟩ : ∃ ext : (∀ w : F, Cl w) → ∀ w, Cl w,
      (∀ x (w : F), ext x w = x w) ∧ ∀ x w, w ∉ T → good w (ext x w) := by
    refine ⟨fun x w => if h : w ∈ F then x ⟨w, h⟩ else if hw : w ∈ T then
      (hB w (fun hS => h ((hF w).2 ⟨hS, hw⟩))).some else (hTA w hw).1.exists.choose,
      fun x w => dif_pos w.2, fun x w hw => ?_⟩
    have hwF : w ∉ F := fun h => hw ((hF w).1 h).2
    simp only [dif_neg hwF, dif_neg hw]
    exact (hTA w hw).1.exists.choose_spec
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : R → ∀ w : F, Cl w, ∀ r (w : F), ρ r w = loc r w :=
    ⟨fun r w => loc r w, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set R, ∀ r, r ∈ G ↔ ∀ w ∈ S, w ∉ T → good w (loc r w) :=
    ⟨{r | ∀ w ∈ S, w ∉ T → good w (loc r w)}, fun _ => Iff.rfl⟩
  have prodS : ∀ φ : ι → ℂ, (∀ w ∈ S, w ∉ T → φ w = 1) → ∏ᶠ w ∈ S, φ w = ∏ w : F, φ w := by
    intro φ hφ
    have h1 : S ∩ Function.mulSupport φ ⊆ (F : Set ι) := by
      rintro w ⟨hwS, hw1⟩
      by_contra hwF
      exact hw1 (hφ w hwS fun hT => hwF (Finset.mem_coe.2 ((hF w).2 ⟨hwS, hT⟩)))
    have h2 : (F : Set ι) ⊆ S := fun w hw => ((hF w).1 (Finset.mem_coe.1 hw)).1
    rw [finprod_mem_eq_prod_of_subset φ h1 h2, ← Finset.prod_coe_sort]
  have hR : ∀ d, ∏ᶠ w ∈ S, ∑ᶠ c, s d w c * O w c =
      ∑ x : (∀ w : F, Cl w), (∏ w : F, s d w (x w)) * ∏ w : F, O w (x w) := by
    intro d
    rw [prodS]
    · simp only [finsum_eq_sum_of_fintype]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib
    · intro w _ hw
      obtain ⟨c0, hc0⟩ := (hTA w hw).1.exists
      rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single c0]
      · rw [hO w hw c0, if_pos hc0, hs1 w hw c0 hc0 d, mul_one]
      · intro c _ hc
        rw [hO w hw c, if_neg (fun hg => hc (huniq w hw c c0 hg hc0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c0) h
  have hs_ext : ∀ d x, ∏ᶠ w ∈ S, s d w (ext x w) = ∏ w : F, s d w (x w) := by
    intro d x
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [ext_F]
    · intro w _ hw
      exact hs1 w hw _ (ext_good x w hw) d
  have hEx : ∀ x, ∑ d, ∏ w : F, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = ext x w then N else 0 := by
    intro x
    rw [← hE (ext x) ?_, finsum_eq_sum_of_fintype]
    · exact Finset.sum_congr rfl fun d _ => (hs_ext d x).symm
    · exact Filter.eventually_cofinite.2 (hTfin.subset fun w hw => by_contra fun hwT => hw (ext_good x w hwT))
  have hρ : ∀ r ∈ G, ∀ w ∈ S, loc r w = ext (ρ r) w := by
    intro r hr w hwS
    by_cases hwF : w ∈ F
    · have h := ext_F (ρ r) ⟨w, hwF⟩
      rw [hρdef] at h
      exact h.symm
    · have hwT : w ∉ T := fun hT => hwF ((hF w).2 ⟨hwS, hT⟩)
      exact huniq w hwT _ _ ((hG r).1 hr w hwS hwT) (ext_good _ w hwT)
  have hρinj : Set.InjOn ρ G := by
    intro r hr r' hr' h
    apply hD
    intro w hwS
    rw [hρ r hr w hwS, hρ r' hr' w hwS, h]
  have hP0 : ∀ r, r ∉ G → ∏ᶠ w ∈ S, O w (loc r w) = 0 := by
    intro r hr
    rw [hG] at hr
    push_neg at hr
    obtain ⟨w, hwS, hwT, hg⟩ := hr
    refine finprod_mem_eq_zero_of_factor _ S ?_ hwS ?_
    · refine (hTfin.union (Filter.eventually_cofinite.1 (hC r))).subset fun v hv => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hv (by rw [hO v hcon.1, if_pos hcon.2])
    · rw [hO w hwT, if_neg hg]
  have hP1 : ∀ r ∈ G, ∏ᶠ w ∈ S, O w (loc r w) = ∏ w : F, O w (ρ r w) := by
    intro r hr
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [hρdef]
    · intro w hwS hwT
      rw [hO w hwT, if_pos ((hG r).1 hr w hwS hwT)]
  have hGfin : G.Finite := Set.Finite.of_finite_image (Set.toFinite _) hρinj
  have hmem : ∀ x, x ∈ ρ '' G ↔ ∃ r, ∀ w ∈ S, loc r w = ext x w := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hρ r hr⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · rw [hG]
        intro w hwS hwT
        rw [hr w hwS]
        exact ext_good x w hwT
      · funext w
        rw [hρdef, hr w ((hF w).1 w.2).1, ext_F]
  have hsum : ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) =
      ∑ x : (∀ w : F, Cl w), if ∃ r, ∀ w ∈ S, loc r w = ext x w then ∏ w : F, O w (x w) else 0 := by
    calc ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) = ∑ᶠ r ∈ G, ∏ w : F, O w (ρ r w) := by
          rw [finsum_mem_def]
          apply finsum_congr
          intro r
          by_cases hr : r ∈ G
          · simp only [Set.indicator_apply, hr, if_true]
            exact hP1 r hr
          · simp only [Set.indicator_apply, hr, if_false]
            exact hP0 r hr
      _ = ∑ᶠ x ∈ ρ '' G, ∏ w : F, O w (x w) :=
          (finsum_mem_image (f := fun x : (∀ w : F, Cl w) => ∏ w : F, O w (x w)) hρinj).symm
      _ = _ := by
          rw [finsum_mem_def, finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, hmem]
  refine ⟨hGfin.subset fun r hr => by_contra fun hrG => hr (hP0 r hrG), ?_⟩
  rw [hsum, finsum_congr hR, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, hEx x]
  split_ifs <;> ring

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolyLocalRealisation
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.IntUnitaryPoly

theorem lemGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := _root_.GlobalTheory.GlobHerm.exists_mat_herm

theorem lemLocal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L), (∀ i j, H i j ∈ intL L) →
      Valued.v H.det = 1 → cT σ H = H →
      ∃ R ∈ GLint (Fin n) (intL L), cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  intro L _ _ _ ϖ σ q hU hq n H hint hdet hH
  have hv := hU.2.1
  set O := Formalism.IndefR.LocBrg.VA L
  set s := Formalism.IndefR.LocBrg.sigA σ hv
  have hs : ∀ x, s (s x) = x := Formalism.IndefR.LocBrg.sigA_inv σ hv hU.1
  have h2 : IsUnit (2 : O) := Formalism.IndefR.LocBrg.two_unit_VA hU hq
  have hτ : ∃ τ : O, τ + s τ = 1 := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    have hs2 : s 2 = 2 := map_ofNat s 2
    have hfix : s ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O) := by
      have e : s ((u⁻¹ : Oˣ) : O) * 2 = 1 := by rw [← hs2, ← map_mul, ← hu, Units.inv_mul, map_one]
      calc s ((u⁻¹ : Oˣ) : O) = s ((u⁻¹ : Oˣ) : O) * (2 * ((u⁻¹ : Oˣ) : O)) := by rw [← hu, Units.mul_inv, mul_one]
        _ = ((u⁻¹ : Oˣ) : O) := by rw [← mul_assoc, e, one_mul]
    rw [hfix, ← two_mul, ← hu, Units.mul_inv]
  have hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u := fun u hu hsu =>
    Formalism.IndefR.LocBrg.normSurj Formalism.IndefR.LocBrg.finNormSurj Formalism.IndefR.LocBrg.henselSqrt hU hq u hsu hu
  set Q : Matrix (Fin n) (Fin n) O := fun i j =>
    ⟨H i j, Formalism.IndefR.LocBrg.mem_VA.2 (Formalism.IndefR.LocBrg.mem_intL.1 (hint i j))⟩ with hQdef
  have hmap : Q.map O.subtype = H := by ext i j; rfl
  have hQ : cT s Q = Q := by
    ext i j; exact congrFun (congrFun hH i) j
  have hQu : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det, Formalism.IndefR.LocBrg.isUnit_VA_iff]
    have e : ((Q.det : O) : L) = H.det := by rw [← hmap]; exact RingHom.map_det O.subtype Q
    rw [e]; exact hdet
  obtain ⟨a, ha⟩ := GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing O s hs hτ hn n Q hQ hQu
  let ι : O →+* intL L := O.subtype.codRestrict (intL L)
    (fun x => Formalism.IndefR.LocBrg.mem_intL.2 (Formalism.IndefR.LocBrg.mem_VA.1 x.2))
  refine ⟨bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a), ⟨_, rfl⟩, ?_⟩
  have hR : ((bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (a : Matrix (Fin n) (Fin n) O).map O.subtype := by ext i j; rfl
  rw [hR, ← hmap]
  have hc : cT σ ((a : Matrix (Fin n) (Fin n) O).map O.subtype) = (cT s (a : Matrix (Fin n) (Fin n) O)).map O.subtype := by
    ext i j; rfl
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem lemOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → Odd q := by
  intro L _ _ ϖ σ q hU h2
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hcard : Nat.card (IsLocalRing.ResidueField V) = q ^ 2 := hU.2.2.2.2.2.2
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  haveI : Finite (IsLocalRing.ResidueField V) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq0)
  have h20 : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have hu : IsUnit (2 : V) := by
    have hmem : (2 : L)⁻¹ ∈ V := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h2, inv_one])
    have hmul : (2 : V) * ⟨(2 : L)⁻¹, hmem⟩ = 1 := by
      apply Subtype.ext
      first
        | exact mul_inv_cancel₀ h20
        | (show (2 : L) * (2 : L)⁻¹ = 1; exact mul_inv_cancel₀ h20)
        | (push_cast; exact mul_inv_cancel₀ h20)
    exact ⟨⟨2, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have h2V : (2 : IsLocalRing.ResidueField V) ≠ 0 := by
    intro h
    have hm : (2 : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat]; exact h
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  by_contra hodd
  have heven : Even q := Nat.not_odd_iff_even.1 hodd
  have hdvd : 2 ∣ Nat.card (IsLocalRing.ResidueField V) := by
    rw [hcard]; exact dvd_pow (even_iff_two_dvd.1 heven) two_ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
  have hx0 : x ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hx; norm_num at hx
  have hmul : (2 : IsLocalRing.ResidueField V) * x = 0 := by
    rw [two_mul, ← two_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  exact h2V ((mul_eq_zero.1 hmul).resolve_right hx0)

theorem val_alg {E : Type} [Field E] [NumberField E] (w : Pl E) (x : E) :
    Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem ae_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (K := E) x).eventually_cofinite_notMem] with w hw
  have hw' : ¬ 1 < w.valuation E x := hw
  rw [val_alg]
  exact not_lt.1 hw'

theorem ae_unit {E : Type} [Field E] [NumberField E] {x : E} (hx : x ≠ 0) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) = 1 := by
  filter_upwards [ae_int x, ae_int x⁻¹] with w h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap E (w.adicCompletion E) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (_root_.map_ne_zero _).2 hx
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)

theorem mem_GLint {L : Type} [Field L] {O : Subring L} {n : ℕ} (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h2 i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have inj : ∀ M N : Matrix (Fin n) (Fin n) O, M.map O.subtype = N.map O.subtype → M = N := fun M N h => by
    ext i j; exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext i j; rfl

theorem Ov_eq {E : Type} [Field E] [NumberField E] (w : Pl E) :
    (w.adicCompletionIntegers E).toSubring = intL (w.adicCompletion E) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (Valuation.mem_integer_iff _ _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
    (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧
      ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  intro E _ _ _ hU n P hP
  obtain ⟨C, H, hC, hCd, hHd, hHh, hCH⟩ := lemGlobal E n P hP
  set Ci := C⁻¹ with hCi
  have hCCi : C * Ci = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hCd)
  have hCiC : Ci * C = 1 := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.2 hCd)
  let f : ∀ w : Pl E, E →+* w.adicCompletion E := fun w => algebraMap E (w.adicCompletion E)
  let Cw : ∀ w : Pl E, GLw n w := fun w =>
    ⟨C.map (f w), Ci.map (f w), by rw [← Matrix.map_mul, hCCi, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hCwv : ∀ w, ((Cw w : GLw n w) : Matrix (Fin n) (Fin n) _) = C.map (f w) := fun w => rfl
  have hCwi : ∀ w, (((Cw w)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = Ci.map (f w) := fun w => rfl
  have hchar : ∀ w, (C.map (f w)).charpoly = atPl w P := fun w => by
    rw [Matrix.charpoly_map, hC]
  refine ⟨?_, fun w hs => ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, hchar w⟩⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) E, ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, Valued.v (f w (M i j)) ≤ 1 :=
    fun M => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j)
  filter_upwards [hall C, hall Ci, hall H, ae_unit hHd, ae_unit (two_ne_zero : (2 : E) ≠ 0)] with w h1 h2 h3 h4 h5
  have hO : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 → x ∈ (w.adicCompletionIntegers E).toSubring :=
    fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx
  have hK : Cw w ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mem_GLint _ (fun i j => hO _ (h1 i j)) (fun i j => hO _ (h2 i j))
  by_cases hs : IsSplitAt w
  · exact ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, Subgroup.mem_subgroupOf.2 hK, hchar w⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -, -⟩ := hns hs
    have h2v : Valued.v (2 : w.adicCompletion E) = 1 := by
      have e : f w 2 = 2 := map_ofNat _ 2
      rw [← e]; exact h5
    have hq := lemOdd _ ϖ (cj w) q hUI h2v
    set Hw := H.map (f w) with hHwdef
    have hHw1 : ∀ i j, Hw i j ∈ intL (w.adicCompletion E) := fun i j => (Valuation.mem_integer_iff _ _).2 (h3 i j)
    have hHw2 : Valued.v Hw.det = 1 := by
      rw [show Hw.det = f w H.det from (RingHom.map_det (f w) H).symm]; exact h4
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) E,
        cT (cj w) (M.map (f w)) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (f w) := by
      intro M; refine Matrix.ext fun i j => ?_; simp only [cT, Matrix.map_apply, Matrix.transpose_apply]; exact hext (M j i)
    have hHw3 : cT (cj w) Hw = Hw := by rw [hmapc, hHh]
    have hCHw : cT (cj w) (C.map (f w)) * Hw * C.map (f w) = Hw := by
      rw [hmapc, hHwdef, ← Matrix.map_mul, ← Matrix.map_mul, hCH]
    obtain ⟨R, hR, hRH⟩ := lemLocal (w.adicCompletion E) ϖ (cj w) q hUI hq n Hw hHw1 hHw2 hHw3
    have hRK : R ∈ GlobalTheory.LFun.KGL w (n := n) := by
      have e : GlobalTheory.LFun.KGL w (n := n) = GLint (Fin n) (intL (w.adicCompletion E)) := by
        show GLint (Fin n) (w.adicCompletionIntegers E).toSubring = _
        rw [Ov_eq]
      rw [e]; exact hR
    refine ⟨⟨R⁻¹ * Cw w * R, ?_⟩, Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem (inv_mem hRK) hK) hRK), ?_⟩
    · rw [UL, if_neg hs]
      show cT (cj w) ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 *
        ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
      rw [Units.val_mul, Units.val_mul, hCwv]
      set r := ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      set ri := (((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      have hri : r * ri = 1 := Units.mul_inv R
      have hH' : Hw = cT (cj w) ri * ri := by
        calc Hw = cT (cj w) (r * ri) * Hw * (r * ri) := by rw [hri, cT_one, Matrix.one_mul, Matrix.mul_one]
          _ = cT (cj w) ri * (cT (cj w) r * Hw * r) * ri := by rw [cT_mul]; simp only [Matrix.mul_assoc]
          _ = cT (cj w) ri * ri := by rw [hRH, Matrix.mul_one]
      rw [Matrix.mul_one, cT_mul, cT_mul]
      calc cT (cj w) r * (cT (cj w) (C.map (f w)) * cT (cj w) ri) * (ri * C.map (f w) * r)
          = cT (cj w) r * (cT (cj w) (C.map (f w)) * (cT (cj w) ri * ri) * C.map (f w)) * r := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← hH', hCHw, hRH]
    · have hinv : ((((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))⁻¹ =
          ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [← Matrix.coe_units_inv, inv_inv]
      have e := Matrix.charpoly_units_conj (R⁻¹ : GLw n w) (C.map (f w))
      rw [hinv] at e
      have key : ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = atPl w P := by
        rw [Units.val_mul, Units.val_mul, hCwv, e, hchar]
      exact key

end GlobalTheory.IntUnitaryPoly
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolySelfReciprocal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_charpoly_self_reciprocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  have hcsr := GlobalTheory.CompanionTheory.EllLoc.csr_global hP
  refine ⟨fun h0 => ?_, hcsr⟩
  rw [h0, map_zero, C_0, zero_mul] at hcsr
  have hm : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).Monic := hP.1.map _
  exact hm.ne_zero (Polynomial.reverse_eq_zero.mp hcsr.symm)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ExistsGlobalHermitianForm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_global_hermitian_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  first | exact @GlobalTheory.RefForm.cT_mul | exact @GlobalTheory.RefForm.cT_cT_conj | exact @GlobalTheory.RefForm.det_cT_conj | exact @GlobalTheory.RefForm.cT_diag_mul_diag | exact @GlobalTheory.RefForm.assemble | exact @GlobalTheory.RefForm.exists_roots_enum | exact @GlobalTheory.RefForm.powBasis_apply | exact @GlobalTheory.RefForm.vandermonde_mul_compMat | exact @GlobalTheory.RefForm.charpoly_compMat | exact @GlobalTheory.RefForm.trace_semiconj | exact @GlobalTheory.RefForm.exists_model | exact @GlobalTheory.RefForm.map_cT_complexConj | exact @GlobalTheory.RefForm.exists_refForm | (intros; apply GlobalTheory.RefForm.exists_refForm <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliser
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormHasseCent

theorem inv_hh {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (k : GL (Fin n) K) : (k.val * cT σ k.val)⁻¹ = cT σ (k⁻¹).val * (k⁻¹).val :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_assoc, cT_units_left', Units.mul_inv])

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  intro E _ _ _ hU n γ h hγ hP hconj hloc
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσdef
  have hσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  set N := cT σ (h⁻¹).val * (h⁻¹).val with hN
  have hγ' : cT σ γ.val * 1 * γ.val = 1 := hγ
  have hinv := inv_of_unit σ h γ hconj
  have hγγ : γ.val * cT σ γ.val = 1 := by
    rw [Matrix.mul_one] at hγ'; exact mul_eq_one_comm.1 hγ'
  have hcomm : γ.val * N = N * γ.val := by
    have := congrArg (γ.val * ·) hinv
    simp only [← Matrix.mul_assoc, hγγ, Matrix.one_mul] at this
    rw [hN]; simpa only [Matrix.mul_assoc] using this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val N hP.2.2.1 hcomm
  have hherm : cT σ (aeval γ.val m) = aeval γ.val m := by
    rw [← hm]; exact herm_of σ hσ h
  have hM : (h.val * cT σ h.val)⁻¹ = aeval γ.val m := by rw [inv_hh, ← hN, hm]
  have hsr := _root_.GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hP
  have hfix := GlobalTheory.T.involution_fixes_polynomial_image E n γ hγ hP m hherm
  have hloc' : ∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E)) := (fun w hw => by
    obtain ⟨c, hc1, hc2⟩ := hloc w hw
    refine ⟨c, hc1, ?_⟩
    rw [hc2, inv_hh, ← hm, hN, ← map_inv]
    rw [Matrix.map_mul, cT_map hU w hw]; rfl)
  have hfin : ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
    intro r Q hQ hx v
    by_cases hs : ∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v
    · exact _root_.GlobalTheory.LocalNormSplit.exists_norm_of_split E r Q _ hx v hs
    · refine _root_.GlobalTheory.NormInert.main E hU n γ hγ hP m hloc' r Q hQ hx v (fun w w' hw hw' => ?_)
      by_contra hne
      exact hs ⟨w, w', hne, hw, hw'⟩
  have hinf := _root_.GlobalTheory.RealPlaceNorms.exists_norm_at_infinite E n γ hγ hP m (fun τ => by rw [← hm]; exact GlobalTheory.T.conj_transpose_mul_posDef E n h τ)
  obtain ⟨c, hc1, hc2⟩ := _root_.GlobalTheory.NormAssemble.exists_norm_of_factors E n γ hγ hP hsr m (fun r Q hQ =>
    GlobalTheory.T.global_norm_of_local_norms E r Q _ (hfix r Q hQ) (hfin r Q hQ (hfix r Q hQ)) (hinf r Q hQ (hfix r Q hQ)))
  exact ⟨c, hc1, by rw [hc2, hM]⟩

end GlobalTheory.NormHasseCent
end

