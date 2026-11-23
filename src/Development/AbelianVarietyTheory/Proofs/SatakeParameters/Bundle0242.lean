module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.Bundle0047
public import Formalism.LocalToGlobal.Columns.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RcUnlinkedChars
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

theorem rc_unlinked_chars : Inputs → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero (h := h)).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dite_eq_left (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dite_eq_left (by omega), Loc.atN, dite_eq_left hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SatChar

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem charPol_satWD (h : IsPlaceOver A w) (n : ℕ) (B : Multiset ℂˣ) (g : Weil h) :
    (satWD h n B).charPol g = (B.map fun b : ℂˣ =>
      X - C ((((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - n) / 2 : ℝ)) : ℂ)) ^ deg g * ((b : ℂ)⁻¹) ^ deg g)).prod := by
  classical
  have hs : ∀ {ι : Type} (c : ℂ) (d : ι → ℂ), c • diagEnd d = diagEnd (fun i => c * d i) := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [satWD, WD.lpUnr, WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hs, charpoly_diagEnd,
    ← Finset.prod_map_val]
  rw [Multiset.map_univ (B.map fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))
    (fun z : ℂ => X - C ((((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) ^ deg g * ((WD.unitOf z : ℂˣ) : ℂ) ^ deg g)),
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [WD.coe_unitOf (by simp), Units.val_inv_eq_inv_val]

def ordHom (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ord (w.adicCompletion E) x)) fun x y => by
    rw [ord_mul, ofAdd_add]

theorem unram_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : ∀ x : (w.adicCompletion E)ˣ, Valued.v (x : w.adicCompletion E) = 1 → χ x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (g : Weil h) :
    χ (a g) = χ ϖ ^ (-deg g) := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  have h2 : ord (w.adicCompletion E) (a g * ϖ ^ deg g) = 0 := by
    have := congrArg Multiplicative.toAdd (map_mul (ordHom w) (a g) (ϖ ^ deg g))
    rw [map_zpow] at this
    simp only [ordHom, MonoidHom.mk'_apply, toAdd_ofAdd, toAdd_mul, toAdd_zpow, smul_eq_mul] at this
    rw [this, ha.ord_eq, h1]; ring
  have h3 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [SphCompletion.ord_completion, neg_eq_zero] at h2
    have h0 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    rw [← WithZero.exp_log h0, h2, WithZero.exp_zero]
  have h4 : a g = (a g * ϖ ^ deg g) * ϖ ^ (-deg g) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h4, map_mul, hχ _ h3, one_mul, map_zpow]

theorem absPow_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (s : ℝ)
    (g : Weil h) :
    (absPow (w.adicCompletion E) (s : ℂ) (a g) : ℂ) = (((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    exact_mod_cast (zero_lt_one.trans this)
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq.le, ← Complex.ofReal_zpow,
    ← Complex.ofReal_cpow (zpow_pos hq _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, mul_comm]

theorem satWD_charPol_chars : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ) (ξ ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, ξ' j = ξ j * absPow (w.adicCompletion E) ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := by
  intro Ω _ E _ _ _ _ w A h n ξ ξ' hξ' hun ϖ hϖ a ha g
  rw [charPol_satWD, Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rw [hξ' j, MonoidHom.mul_apply, Units.val_mul, unram_art ha (ξ j) (hun j) ϖ hϖ g, absPow_art ha]
  congr 2
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, inv_zpow, mul_comm]

end GlobalTheory.SatChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SingularWeightMonotoneRegularization
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.CharSupport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : UpperTheory.Zero.LLC.LawsT a ha rc) (Δ : Segment (w.adicCompletion E))
    (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.RoadU.CharSupport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TwistSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_neg (x : IrrGL (k := k)) (s : ℂ) : (x.nu s).nu (-s) = x := by
  rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]

theorem nu_injective (s : ℂ) : Function.Injective fun x : IrrGL (k := k) => x.nu s := fun x y h => by
  have := congrArg (fun z : IrrGL (k := k) => z.nu (-s)) h
  simpa only [nu_nu_neg] using this

theorem chars_eq_map_nu {n : ℕ} (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ) (h : ∀ j, ξ' j = ξ j * absPow k s) :
    chars ξ' hξ' = (chars ξ hξ).map fun y => y.nu s := by
  unfold chars
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]
  exact IrrGL.ofChar_inj.2 (h j)

theorem unlinked_map_nu (m : Multiset (IrrGL (k := k))) (s : ℂ) :
    Unlinked (m.map fun y => y.nu s) ↔ Unlinked m := by
  constructor
  · intro h y hy z hz e
    refine h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  · intro h y' hy' z' hz' e
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    refine h y hy z hz (nu_injective s ?_)
    simp only
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]

theorem supp_nu_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  intro k _ _ _ _ _ x n ξ ξ' hξ hξ' s h
  rw [chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]
  refine ⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩
  have H' := SupportRing.hasSupport_nu H (-s)
  rw [nu_nu_neg, Multiset.map_map] at H'
  simpa only [Function.comp_def, nu_nu_neg, Multiset.map_id'] using H'

end GlobalTheory.RoadU.TwistSupp
end
end

