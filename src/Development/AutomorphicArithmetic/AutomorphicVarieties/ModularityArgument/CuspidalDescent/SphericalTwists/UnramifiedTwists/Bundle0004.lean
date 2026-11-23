module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.GalAEOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W.GaloisCompatibilityAlmostEverywhere

section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rc_chars (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : UpperTheory.Zero.LLC.LawsT a ha rc) (x : IrrGL (k := w.adicCompletion E)) (n : ℕ)
    (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hs : HasSupport x.rep (chars ξ hξ))
    (hu : Unlinked (chars ξ hξ)) :
    (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hE (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
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

end Loc

private theorem norm_absPow_unif (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    ‖((GlobalTheory.SmGL.absPow (w.adicCompletion E) (1 : ℂ) ϖ : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  rw [GlobalTheory.SmGL.val_absPow, Complex.cpow_one, GlobalTheory.LGrp.nabs_eq_zpow, h1, GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  simp

private theorem unlinked_of_sat (hJ : GlobalTheory.Published.JacquetShalikaBound) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hB : (CG.mk π).HasSat w (Finset.univ.val.map fun j => ξ j ϖ)) : Unlinked (chars ξ hξ) := by
  intro y hy z hz e
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  simp only [IrrGL.nu, IrrGL.tw_ofChar] at e
  have e' := IrrGL.ofChar_inj.1 e
  have hval : ((ξ i ϖ : ℂˣ) : ℂ) = ((ξ j ϖ : ℂˣ) : ℂ) * ((GlobalTheory.SmGL.absPow (w.adicCompletion E) (1 : ℂ) ϖ : ℂˣ) : ℂ) := by
    rw [e']; rfl
  have hnorm : ‖((ξ i ϖ : ℂˣ) : ℂ)‖ = ‖((ξ j ϖ : ℂˣ) : ℂ)‖ * (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    rw [hval, norm_mul, norm_absPow_unif E w ϖ hϖ]
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) hn
  have hT := (hB.twist_absPow (-t)).1
  have e0 : (CG.mk π).twist (GlobalTheory.HeckeGal.Model.absPow E (-t)) = π₀ := by
    rw [he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  rw [e0] at hT
  set c := (GlobalTheory.HeckeGal.Model.absPow E (-t)).val w
  have hmem : ∀ m, ξ m ϖ * c ∈ (Finset.univ.val.map fun j => ξ j ϖ).map (· * c) := fun m =>
    Multiset.mem_map.2 ⟨ξ m ϖ, Multiset.mem_map.2 ⟨m, Finset.mem_univ_val _, rfl⟩, rfl⟩
  have hi := hJ E n π₀ hu w _ hT _ (hmem i)
  have hj := hJ E n π₀ hu w _ hT _ (hmem j)
  simp only [Units.val_mul, norm_mul] at hi hj
  have hq : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ)
  have hq0 : 0 < q := zero_lt_one.trans hq
  set s : ℝ := q ^ (1 / 2 : ℝ)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hq0 _
  have hss : s * s = q := by
    rw [← Real.rpow_add hq0]; norm_num
  have hsn : q ^ (-(1 / 2) : ℝ) = s⁻¹ := Real.rpow_neg hq0.le _
  rw [hsn] at hi
  rw [hnorm] at hi
  set b := ‖((ξ j ϖ : ℂˣ) : ℂ)‖
  set C := ‖((c : ℂˣ) : ℂ)‖
  have key : b * C = q * (b * q⁻¹ * C) := by field_simp
  have h1 : s * (s⁻¹) < s * (b * q⁻¹ * C) := mul_lt_mul_of_pos_left hi.1 hs0
  rw [mul_inv_cancel₀ hs0.ne'] at h1
  have h2 : s * 1 < s * (s * (b * q⁻¹ * C)) := mul_lt_mul_of_pos_left h1 hs0
  rw [mul_one, ← mul_assoc, hss, ← key] at h2
  exact absurd hj.2 (not_lt.2 h2.le)

private theorem comm_one {G : Type} [Group G] {H : Type} [CommGroup H] (f : G →* H) (s t : G) : f ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement]
  exact (Commute.all _ _).commutator_eq

private theorem rec_sat (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hJ : GlobalTheory.Published.JacquetShalikaBound) {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B)
    (hBσ : GlobalTheory.LFun.HasSatGL w σ.ρ B) (rc : IrrGL (k := w.adicCompletion E) → WD h) (hrc : UpperTheory.Zero.LLC.IsRecT h rc) :
    rc (algNorm σ) = satWD h n B ∧ UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0 := by
  obtain ⟨a, ha, hL⟩ := hrc
  obtain ⟨ξ, hξ, ϖ, hsup, hunr, hϖ, rfl⟩ := GlobalTheory.T.supercuspidal_support_characters E n hn w σ B hBσ
  have hun : Unlinked (chars ξ hξ) := unlinked_of_sat hJ E n hn π w ξ hξ ϖ hϖ hB
  set s : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) with hs
  let ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * GlobalTheory.SmGL.absPow _ s
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' s
    (fun _ => rfl)
  have hsup' : HasSupport (algNorm σ).rep (chars ξ' hξ') := hnu.1.1 hsup
  have hun' : Unlinked (chars ξ' hξ') := hnu.2.1 hun
  have h2 := rc_chars hE hZ hL (algNorm σ) n ξ' hξ' hsup' hun'
  have h3 := GlobalTheory.SatChar.satWD_charPol_chars Ω E w A h n ξ ξ' (fun _ => rfl) hunr ϖ hϖ a ha
  have hm : (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).mono0 := by
    unfold satWD
    rw [WD.monomial_twist_iff]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))
  refine ⟨GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ h2.1 hm fun g => (h2.2 g).trans (h3 g).symm, fun u v => ?_, h2.1⟩
  show WD.charPol _ _ = _
  rw [h2.2, hL.dim]
  have h1 : ∀ j, ξ' j (a ⁅u, v⁆) = 1 := fun j => by
    rw [map_commutatorElement]
    exact comm_one (ξ' j) (a u) (a v)
  simp only [h1]
  simp
  rfl

private theorem val_frob (q a : ℕ) (b : ℂˣ) :
    ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) * ((b : ℂ)⁻¹) ^ (-1 : ℤ) =
      (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ) := by
  have h1 : (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) = ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ))⁻¹ := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [h1, zpow_neg_one, zpow_neg_one, inv_inv]

end UpperTheory.V.Z.Desc.W.GaloisCompatibilityAlmostEverywhere

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatFrobT
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) (x : IrrGL (k := w.adicCompletion E))
    (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨a, ha, H⟩ := H
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

private theorem rec_algNorm_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  obtain ⟨a, ha, L⟩ := H
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem gd_diag {n : ℕ} (c : Fin n → ℂˣ) : Z.Win.Gd (WD.mk (WDRep.diag h c)) := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩
  have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
    rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]
  simp

private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

end

