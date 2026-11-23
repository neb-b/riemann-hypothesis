module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.BaseExt
  GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsBase

theorem span_eq_of_isPrincipal {E : Type} [Field E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (hF : ∀ x, φ x ∈ F)
    (𝔞 : Ideal (𝓞 E)) (h : (𝔞.map (RingOfIntegers.mapRingHom (φ.codRestrict F hF))).IsPrincipal) :
    ∃ β : F, Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  obtain ⟨b, hb⟩ := h
  refine ⟨(b : F), ?_⟩
  have h := congrArg (Submodule.map (Algebra.linearMap (𝓞 F) F)) hb
  rw [Submodule.map_span, Set.image_singleton, Ideal.map, Ideal.span, Submodule.map_span, Set.image_image] at h
  refine h.symm.trans (congrArg _ ?_)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, Subtype.ext hx.symm⟩

theorem exists_base_of_contents (B : Pre) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    (hEF : ∀ x, B.host.φ₀ x ∈ F) (hr : rootsField B ≤ F) (hp : rootOne B.host.pde ∈ F)
    (hp' : rootOne B.host.pde' ∈ F) (hh : rootOne (classNumber B.host.E) ∈ F)
    (hc : ∀ 𝔞 : Ideal (𝓞 B.host.E), ∃ β : F,
      Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (a : B.host.E)})
    (hk : ∀ j, 1 ≤ j → j ≤ B.R.m → ∀ 𝔞 : Ideal (𝓞 B.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧
      Submodule.span (𝓞 F) {β} = ∏ g : Tau B.R,
        (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (a : B.host.E))} ^
            (B.R.sigW j).1 *
          Submodule.span (𝓞 F)
            {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (B.host.conj (a : B.host.E)))} ^
            (B.R.sigW j).2) ∧
      ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((B.R.sigW j).1 + (B.R.sigW j).2)) :
    ∃ B' : Base, B'.toPre = B ∧ B'.KsC = F := by
  classical
  obtain ⟨SF, hSF, hF⟩ := exists_gens_le F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (SF ∪ SR) (by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      exacts [hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := hF K fun z hz => hS z (.inl hz)
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hEF x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (.inr hz)
  have : NumberField K := {}
  simp only [rootsField, sup_le_iff, cycField_le_iff] at hr
  obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := hr
  let f := toComap hFK
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K hEK
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := F.comap K.val
            Ks_le := le_top
            E_le_Ks := hEF
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, IntermediateField.ext fun z => ?_⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hc 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_comap hFK 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K hEK) fun _ => rfl)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hk j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    refine h.trans (Finset.prod_congr rfl fun g _ => ?_)
    have e1 := image_comap hFK 𝔞 (B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_comap hFK 𝔞 ((B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E)).comp
        (B.host.conj : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g (B.host.conj a))) fun _ => rfl
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · exact fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩

theorem exists_base_listField (hR : RayField) (hP : PrincipalIdealSt) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P)
    (δ : FieldDat P) : listField δ f ≤ δ.Om ∧ ∃ B : Base, B.toPre = P ∧ B.KsC = listField δ f := by
  have hO : listField δ f ≤ δ.Om := listField_le_Om δ f
  have := host_cplx P
  have := finite_Om δ
  have : FiniteDimensional ℚ (listField δ f) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hO).toLinearMap (IntermediateField.inclusion_injective hO)
  obtain ⟨h1, -, h3, h4, -, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hm : 1 ≤ P.R.m := le_trans one_le_two P.R.two_le_m
  refine ⟨hO, exists_base_of_contents P _ ((imField_le_iff _).1 h1) h4
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde_dvd P) δ.isRay))
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde'_dvd P) δ.isRay))
    (cycField_le_iff.1 ((le_sup_right.trans le_sup_left).trans (h6 1 le_rfl hm)))
    (fun 𝔞 => span_eq_of_isPrincipal _ _ _ 𝔞
      (hP.of_isRayFieldIn hR (natIdeal_ne_bot (modulus_ne_zero P)) δ.isRay h3 𝔞))
    fun j hj hj' => _root_.GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le P δ _ j (h6 j hj hj')⟩

end GlobalTheory.Mem.KsBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd

theorem satAt_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  intro L _ _ _ n π π' hiso v w _ Dv Dv' α hsat
  have h1 : NG.SatAt π Dv' α := by
    obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hsat
    refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
    have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [_root_.GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv Dv' U _ h' hh'.1 f,
      hH _ (_root_.GlobalTheory.SatInd.guMap_hecke_comap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
      _root_.GlobalTheory.SatInd.satU_guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
        (_root_.GlobalTheory.SatInd.cosetT_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
          Dv.unram Dv'.unram hm)]
  exact GlobalTheory.T.inertSatakeParameters_eq_of_iso L n π π' hiso v w Dv' α
    (_root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv' (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv'.ϖ Dv'.σw _ n Dv'.unram) (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv')) h1

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions.Examples₂ GlobalTheory.EX.WinLow

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  push_cast
  rw [lamOf_eq p j hj, lamOf_eq p j hj, wtQ_eq_wtN, wtQ_eq_wtN]
  have a1 : wtN p (R.N R.m - 1) ≤ wtN p (R.N j - 1) := wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : blkN R (R.N R.m - 1) < R.m := by omega
    unfold wtN
    rw [dite_eq_right c1, dite_eq_left c2]
    have e : (⟨blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold wtN
    rw [dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

theorem hcW_injective {s : Scale} {C : FC} {cD ch : ℝ} {P : PreCh} {q1 : ℕ} {a b : P.R.A → ℤ}
    {c : P.Word → Fin (P.R.k - 2) → Bool} (h : ChOK s C cD ch P q1 a b c) : Function.Injective P.hcW := by
  intro u u' huu
  apply h.inj
  funext l
  have hD : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _)
    exact_mod_cast this
  have e1 := h.code u (placeNo P.H 0) l.1 l.2
  have e2 := h.code u' (placeNo P.H 0) l.1 l.2
  rw [huu, e2] at e1
  change _ - (if c u' l then _ else _) = _ - (if c u l then _ else _) at e1
  cases h1 : c u l <;> cases h2 : c u' l <;> simp only [h1, h2, if_true, Bool.false_eq_true, if_false] at e1 ⊢ <;> (exfalso; linarith)


set_option maxHeartbeats 1000000 in
theorem ev_preX_frame : StandardLattice.SiegelMassRatioCM → Ev fun K => ∀ B : Pre, K.Over B → Nonempty (PreX B) ∧ Nonempty (Fr B) := by
  intro h2b
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ⟨0, fun cD hcD => ?_⟩⟩⟩
  obtain ⟨c2, hw⟩ := window_lower h2b eps C h0 h1 hC cD hcD
  refine ⟨max c2 0, fun ch hch => ?_⟩
  have hch0 : 0 ≤ ch := le_trans (le_max_right _ _) hch
  obtain ⟨x1, hx1⟩ := hw ch (le_trans (le_max_left _ _) hch)
  obtain ⟨x2, hx2⟩ := places_ok eps C cD ch h0 h1 hC hcD hch0
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 406 1 h0 one_pos
  refine ⟨max (max x1 x2) (max x3 (max x4 10)), ?_⟩
  rintro ⟨s, C', cD', ch', P, q1, a, b, c, std, ok, Lv, hdu, hDs, hG⟩ rfl rfl rfl he hx B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
  simp only [max_le_iff] at he hx
  obtain ⟨⟨y1, y2⟩, y3, y4, y5⟩ := hx
  have hev : (Pre.ofCh P Lv sp hT hY hA hV hz).EvenExp := (ok.hc P.u₀).2.2.2
  refine ⟨?_, Pre.nonempty_hframe _ hev⟩
  have hlow := hx1 s P q1 a b c Lv.duStar Lv.Dstar he y1 ok hdu (hDs ▸ (GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P).2)
  have hpl := hx2 s P q1 a b c he y2 ok
  obtain ⟨hf, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, hN, -⟩ := hx3 s P.R he y3 ok.rank
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hk3 := P.R.m_add_three_le_k
  have hm2 := P.R.two_le_m
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (P.R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hN' : (P.R.N P.R.m : ℝ) ≤ s.x ^ 402 := by rw [← pw]; exact_mod_cast hN
  have hb' : s.x ^ 406 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have hone : 1 ≤ s.x := by linarith
  have hz1 : 10 * s.x ^ 405 ≤ s.b := by
    calc 10 * s.x ^ 405 ≤ s.x * s.x ^ 405 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 406 := by ring
      _ ≤ s.b := hb'
  have hfN : (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 405 := by
    calc (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 3 * s.x ^ 402 := mul_le_mul hf' hN' (by positivity) (by positivity)
      _ = s.x ^ 405 := by ring
  have hN2 : (P.R.N P.R.m : ℝ) ≤ s.x ^ 405 := hN'.trans (pow_le_pow_right₀ hone (by norm_num))
  have hx2' : 10 * s.x ≤ s.x ^ 405 := by
    calc 10 * s.x ≤ s.x ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ hone (by norm_num)
  generalize s.x ^ 405 = z at hz1 hfN hN2 hx2'
  have hkN : (P.R.k : ℝ) ≤ P.R.N P.R.m := by
    have : P.R.k ≤ P.R.N P.R.m := Nat.le_add_right _ _
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hbb : 1000 * s.b ≤ s.b * s.b := by nlinarith
  have hxb : 100 * (s.x * s.b) ≤ s.b * s.b := by nlinarith
  choose πg g1 g2 g3 using ok.gnorm
  refine ⟨{ piG := πg
            piG_K := g1
            piG_norm := g2
            piG_cong := fun i => Ideal.mem_span_singleton.1 (g3 i)
            piT := Lv.piT
            piT_K := Lv.piT_K
            piT_norm := Lv.piT_norm
            piT_cong := fun u => Ideal.mem_span_singleton.1 (Lv.piT_cong u)
            pde_split := ok.arith.2.2.1
            ccK_top := P.ccK_top
            e_even := hev
            hcW_inj := hcW_injective ok
            a := s.b * s.b / 5
            g_big := fun i => ?_
            T_gt := fun u => ?_
            a_gt := ?_
            spread_le := fun u j hj τ => ?_ }⟩
  · show 2 * P.R.f * P.R.k < P.H.g i - 1
    have b1 : 1 ≤ s.b := by linarith
    have c1 : s.b ≤ (P.H.g i : ℝ) :=
      calc s.b ≤ (P.R.k : ℝ) * s.b := le_mul_of_one_le_left hb0.le hk1
        _ ≤ ((P.R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 b1) (by norm_num)
        _ ≤ _ := (ok.val.2.2.2.2.1 i).1
    have c2 : (P.R.f : ℝ) * P.R.k ≤ P.R.f * P.R.N P.R.m := mul_le_mul_of_nonneg_left hkN (by positivity)
    have c3 : ((2 * P.R.f * P.R.k + 1 : ℕ) : ℝ) < P.H.g i := by
      push_cast
      nlinarith
    have c4 : 2 * P.R.f * P.R.k + 1 < P.H.g i := by exact_mod_cast c3
    omega
  · show 4 * (s.b * s.b / 5) < (Lv.T u : ℝ)
    have w := (Lv.T_win u).1
    rw [hG] at w
    have hT0 : 0 < (Lv.Dstar / Lv.duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C' s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
      have : (0 : ℝ) < Lv.duStar u := by exact_mod_cast Lv.duStar_pos u
      have := Lv.Dstar_pos
      have : 0 < GamS C' s P.R := Real.exp_pos _
      positivity
    have c1 := ((Real.le_log_iff_exp_le hT0).1 (hlow u)).trans w
    have c2 : s.b * s.b ≤ Real.exp (P.R.m * s.L) := by
      unfold Scale.b
      rw [← Real.exp_add]
      have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm2
      have := mul_le_mul_of_nonneg_right this (by linarith : 0 ≤ s.L)
      exact Real.exp_le_exp.2 (by linarith)
    have := mul_pos hb0 hb0
    linarith
  · show ((2 * P.R.f * P.R.N P.R.m + 1 : ℕ) : ℝ) < 4 * (s.b * s.b / 5)
    push_cast
    nlinarith
  · show (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤ 2 * (s.b * s.b / 5)
    have hk0 : 0 < P.R.k := by omega
    have hm0 : 0 < P.R.m := by omega
    have hm1 : P.R.m - 1 < P.R.m := by omega
    have c1 := spread_lamOf_le (P.hcW u τ) j hj hk0 hm1
    have c2 : (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤
        (((P.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) + P.R.N P.R.m := by
      exact_mod_cast c1
    obtain ⟨⟨p1, -, -, -, p5, -, -, p8, p9⟩, p10⟩ := hpl u τ
    have p1' := (p1 0 (by omega)).2
    rw [seqOf_lt _ hk0] at p5
    rw [seqOf_lt _ hm0] at p8
    rw [seqOf_lt _ hm1] at p9
    obtain ⟨-, -, ⟨b1, v3, -⟩, -⟩ := ok.hc u
    have d1 : (P.hcW u τ).b ⟨0, hm0⟩ ≤ (P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ := by
      rw [(v3 τ _).2, (v3 τ _).1, (v3 τ _).1]
      have : (0 : ℚ) ≤ ((P.R.m - 1 : ℕ) : ℚ) * (h0v s ch' : ℚ) + (h0v s ch' : ℚ) / 2 := by positivity
      simp only [Nat.cast_zero, zero_mul]
      linarith
    have d2 : (((P.hcW u τ).b ⟨0, hm0⟩ : ℚ) : ℝ) ≤ (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) := by exact_mod_cast d1
    have d3 : (P.R.k : ℝ) * (4 * (Delv s cD' : ℝ)) ≤ 2 * s.b := by
      refine p8.trans ?_
      rw [div_le_iff₀ hx0]
      nlinarith
    have ea : s.a = s.x * s.b := rfl
    have hxb0 : 0 ≤ s.x * s.b := by positivity
    rcases p5 with ⟨q, -⟩ | ⟨-, q, -⟩ <;> linarith

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
end

