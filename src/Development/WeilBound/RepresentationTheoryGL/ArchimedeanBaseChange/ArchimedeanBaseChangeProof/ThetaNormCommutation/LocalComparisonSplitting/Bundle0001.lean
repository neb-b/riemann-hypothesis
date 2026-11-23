module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem mul_finsum_eq {α : Type*} (r : ℂ) (f : α → ℂ) : ∑ᶠ i, r * f i = r * ∑ᶠ i, f i := by
  have h := smul_finsum (R := ℂ) (M := ℂ) r f
  simpa only [smul_eq_mul] using h.symm

theorem global_character_of_holds : GlobalCharacterOfInputs := by
  intro hT hO hA hC hP E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨c, hc0, hc⟩ := hT E hU a b μ₁ μ₂ ν₁ ν₂
  refine ⟨c, hc0, ?_⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂
  obtain ⟨e₁, he₁⟩ := hC E a u₁ hu₁
  obtain ⟨e₂, he₂⟩ := hC E b u₂ hu₂
  have hψ : ∀ v, Continuous (ψ v) := fun v => (hL v).1
  unfold ellSum2 geomRat2
  rw [← finsum_comp_equiv (e₁.prodCongr e₂), ← mul_finsum_eq]
  refine finsum_congr fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  obtain ⟨g₁, hg₁, hr₁⟩ := he₁ x₁
  obtain ⟨g₂, hg₂, hr₂⟩ := he₂ x₂
  have hiff : (IsRegEll (Quot.out (e₁ x₁)) ∧ IsRegEll (Quot.out (e₂ x₂))) ↔ (pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b) := by
    rw [hr₁, hr₂, (hP E a u₁ hu₁ _).1, (hP E b u₂ hu₂ _).1, mul_inv_cancel_right, mul_inv_cancel_right]
    exact Iff.rfl
  have horb : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (Quot.out (e₁ x₁)) (Quot.out (e₂ x₂)) =
      orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (x₁.rep * u₁) (x₂.rep * u₂) := by
    rw [hg₁, hg₂, hO E a b μ₁ μ₂ _ _ g₁ _ g₂ (hA E hU a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ hψ hφ₁ hφ₂ _ _)]
  rw [finsum_eq_if]
  by_cases h : pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b
  · rw [if_pos (hiff.2 h), if_pos h, horb]
    have ht := hc S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂ (x₁.rep * u₁) (x₂.rep * u₂)
      (hr₁.1 (hiff.2 h).1) (hr₂.1 (hiff.2 h).2)
    simp only [mul_inv_cancel_right] at ht
    exact ht
  · rw [if_neg (mt hiff.1 h), if_neg h, mul_zero]

end PositivityTheory.Rg.BcB.G8

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PAdelEqOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (twConj)

theorem adeleqof_map_Phi {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    (GlobalTheory.Tw.Phi m R).map f = GlobalTheory.Tw.Phi m S := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem adeleqof_map_PhiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    GeneralLinearGroup.map f (PhiU m R) = PhiU m S := by
  apply Units.ext
  show (PhiU m R).val.map f = (PhiU m S).val
  rw [phiU_val, phiU_val]
  exact adeleqof_map_Phi f m

theorem adeleqof_map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (σ : R →+* R) (τ : S →+* S)
    (hf : ∀ y, f (σ y) = τ (f y)) (m : ℕ) (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (thetaR σ m g) = thetaR τ m (GeneralLinearGroup.map f g) := by
  apply Units.ext
  show (thetaR σ m g).val.map f = (thetaR τ m (GeneralLinearGroup.map f g)).val
  rw [thetaR_val, thetaR_val, ← map_inv]
  ext i j
  exact hf _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem adeleqof_pFin_conj (y : Ad E) :
    pFin E (conjAd E y) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E y) := rfl

theorem adeleqof_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) := by
  rw [thF, thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, adeleqof_map_PhiU,
    adeleqof_map_thetaR (pFin E) (conjAd E) _ adeleqof_pFin_conj]

omit [IsCMField E] in
theorem adeleqof_pFin_ratGL (d : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  ext i j
  rfl

omit [IsCMField E] in
theorem adeleqof_map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem adeleqof_twist (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) :
    twConj (thetaA E n) g (ratGL E n d) * (ratGL E n u)⁻¹ = g⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) g := by
  rw [hT E n u hu g, twConj, map_mul, map_inv]
  group

theorem adeleqof_cpt (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) (w : Pl E) :
    cpt w u (twConj (thetaA E n) g (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) g)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) g)) := by
  rw [cpt, adeleqof_map_cW, adeleqof_twist hT hu]
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL]

end PositivityTheory.Rg.BcB.G8

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PPolEq
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem poleq_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) (d : GL (Fin n) E) : d * u⁻¹ * thE E n (d * u⁻¹) = nrm d := by
  have h2 : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right hu.2
  rw [hu.1, map_mul, map_inv, h2, nrm]
  group

end PositivityTheory.Rg.BcB.G8

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem termof_twConj_cont {n : ℕ} (hθ : Continuous (thetaR (starRingEnd ℂ) n)) (d : GL (Fin n) ℂ) :
    Continuous fun x : GL (Fin n) ℂ => twConj (thetaR (starRingEnd ℂ) n) x d := by
  show Continuous fun x : GL (Fin n) ℂ => x⁻¹ * d * thetaR (starRingEnd ℂ) n x
  exact (continuous_inv.mul continuous_const).mul hθ

theorem termof_hcs {a b : ℕ} (hEP : EllProper) (ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (hψ : HasCompactSupport ψ)
    (d₁ : GL (Fin a) ℂ) (d₂ : GL (Fin b) ℂ) (h₁ : EllC d₁) (h₂ : EllC d₂) :
    HasCompactSupport fun y : GL (Fin a) ℂ × GL (Fin b) ℂ =>
      ψ (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) := by
  have hK := (hEP a d₁ h₁ _ (hψ.isCompact.image continuous_fst)).prod
    (hEP b d₂ h₂ _ (hψ.isCompact.image continuous_snd))
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  have hm : (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) ∈ tsupport ψ :=
    subset_tsupport _ hne
  exact ⟨⟨_, hm, rfl⟩, ⟨_, hm, rfl⟩⟩

theorem termOf_holds : TermOf := by
  intro hQS hHS hTopo hCI hKf hFL hFH hAE hCE hPE hEP
  intro E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨⟨hlcA, hscA, ht2A⟩, ⟨hlcfA, hscfA, ht2fA⟩, ⟨hlcCA, hscCA⟩, hcntA, -, hθA⟩ := hTopo E a
  obtain ⟨⟨hlcB, hscB, ht2B⟩, ⟨hlcfB, hscfB, ht2fB⟩, ⟨hlcCB, hscCB⟩, hcntB, -, hθB⟩ := hTopo E b
  letI mB : MeasurableSpace (Gf E a b) := borel _
  haveI : BorelSpace (Gf E a b) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hCI E a b
  let e' : (GA E a × GA E b) →* (Gi E a b × Gf E a b) := e.toMulEquiv.toMonoidHom
  have he' : ∀ x, e' x = comps x := he
  have hνH : (ν₁.prod ν₂).IsHaarMeasure := inferInstance
  have hνS : SigmaFinite (ν₁.prod ν₂) := inferInstance
  have hαH : (Measure.pi fun _ : InfinitePlace E => ν₁.prod ν₂).IsHaarMeasure := inferInstance
  let α : Measure (Gi E a b) := Measure.pi fun _ => ν₁.prod ν₂
  obtain ⟨β, hβ, hmap⟩ := hHS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α e
  haveI := hβ
  obtain ⟨hKo₁, hKc₁⟩ := hKf E a
  obtain ⟨hKo₂, hKc₂⟩ := hKf E b
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKo₁.prod hKo₂
  have hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKc₁.prod hKc₂
  refine ⟨(β.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hKo.measure_ne_zero β ⟨1, Subgroup.one_mem _⟩, hKc.measure_lt_top.ne⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hLef hφ₁ hφ₂ d₁ d₂ hd₁ hd₂
  obtain ⟨hP₁, hPv₁⟩ := hPE E a u₁ hu₁ d₁
  obtain ⟨hP₂, hPv₂⟩ := hPE E b u₂ hu₂ d₂
  have hCE' := hCE E a b u₁ u₂ hu₁ hu₂ d₁ d₂
  let f : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ := fun v y =>
    ψ v (twConj (thetaR (starRingEnd ℂ) a) y.1 (GeneralLinearGroup.map v.embedding d₁),
      twConj (thetaR (starRingEnd ℂ) b) y.2 (GeneralLinearGroup.map v.embedding d₂))
  let F₁ : Gi E a b → ℂ := fun y => ∏ v, f v (y v)
  let F₂ : Gf E a b → ℂ := orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    (hLef v).1.comp (((termof_twConj_cont hθA _).comp continuous_fst).prodMk
      ((termof_twConj_cont hθB _).comp continuous_snd))
  have hfs : ∀ v, HasCompactSupport (f v) := fun v =>
    termof_hcs hEP (ψ v) (hLef v).2.1 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂)
  have hint : ∀ v, Integrable (f v) (ν₁.prod ν₂) := fun v => (hfc v).integrable_of_hasCompactSupport (hfs v)
  have hF₁i : Integrable F₁ α := Integrable.fintype_prod hint
  have hF₁m : Measurable F₁ :=
    (continuous_finsetProd _ fun v _ => (hfc v).comp (continuous_apply v)).measurable
  haveI : Countable ↥((ratCent d₁).prod (ratCent d₂)) := by
    have hsub : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)) ⊆
        Set.range (fun p : GL (Fin a) E × GL (Fin b) E => (ratGL E a p.1, ratGL E b p.2)) := by
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_prod] at hx
      obtain ⟨g₁, -, hg₁⟩ := Subgroup.mem_map.1 hx.1
      obtain ⟨g₂, -, hg₂⟩ := Subgroup.mem_map.1 hx.2
      exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hΓ : ((ratCent d₁).prod (ratCent d₂)).map ((MonoidHom.snd _ _).comp e') = gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) := by
    ext y
    rw [Subgroup.mem_map, hCE'.1 y]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, (congrArg Prod.snd (he' γ)).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, congrArg Prod.snd (he' γ)⟩
  have hinj : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), (e' γ).2 = 1 → γ = 1 := by
    intro γ hγ h1
    rw [he'] at h1
    exact (hCE'.2 γ hγ).1 h1
  have hF₁inv : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ∀ x, F₁ ((e' γ).1 * x) = F₁ x := by
    intro γ hγ x
    have hc := (hCE'.2 γ hγ).2
    rw [he']
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [f, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    rw [PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).1, PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).2]
  have hF₂inv : ∀ γ ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹), ∀ y, F₂ (γ * y) = F₂ y := by
    intro γ hγ y
    have h : γ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) =
        (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b γ := (Subgroup.mem_inf.1 hγ).2
    simp only [F₂, orbFn]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ at h ⊢
    rw [(thP E a b).map_mul γ y, show (γ * y)⁻¹ * δ * (thP E a b γ * thP E a b y) =
      y⁻¹ * (γ⁻¹ * (δ * thP E a b γ)) * thP E a b y by group, ← h]
    group
  obtain ⟨U, hUo, hUinv⟩ := hFL E hU a b S φ₁ φ₂ hφ₁ hφ₂
  have hF₂U : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y := by
    intro u hu y
    simp only [F₂, orbFn]
    rw [← hUinv u hu (y⁻¹ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b y)]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ
    rw [(thP E a b).map_mul y u]
    group
  obtain ⟨hfin, hstab, hdc⟩ :=
    hFH E hU a b S hS φ₁ φ₂ hφ₁ hφ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (hP₁.1 hd₁) (hP₂.1 hd₂)
  have hQ := hQS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α β e' (map_continuous e).measurable hmap
    ((ratCent d₁).prod (ratCent d₂)) (gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) ((Kf E a).prod (Kf E b)) U hΓ hinj hKo hKc hUo
    F₁ F₂ hF₁m hF₁i hF₁inv hF₂inv hF₂U hfin hstab
  have hEq : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
      Measure.count (fun x => F₁ (e' x).1 * F₂ (e' x).2) := by
    unfold orbTerm2
    congr 1
    funext x
    rw [hAE E a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x, he' x]
  have hI : ∫ x, F₁ x ∂α = ∏ v, (val v * starRingEnd ℂ (chAt (l₁ v) ((polE (d₁ * u₁⁻¹)).map v.embedding)) *
      starRingEnd ℂ (chAt (l₂ v) ((polE (d₂ * u₂⁻¹)).map v.embedding))) := by
    rw [integral_fintype_prod_eq_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hLef v).2.2 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂), (hPv₁ v).1, (hPv₂ v).1]
  rw [hEq, hQ, hI, hdc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [chW]
  ring

end PositivityTheory.Rg.BcB.G8

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTranslAd
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem translad_map_PhiU (n : ℕ) {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) :
    GeneralLinearGroup.map p (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  change p ((PhiU n R).val i j) = (PhiU n S).val i j
  rw [phiU_val, phiU_val]
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translad_thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val, ← map_inv (thetaR σ n) g, thetaR_val, inv_inv]
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, hσ]

theorem translad_central (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) : u⁻¹ * PhiU n E ∈ Subgroup.center (GL (Fin n) E) := by
  have hcc : ∀ x, conjE E (conjE E x) = x := fun x => IsCMField.complexConj_apply_apply (K := E) x
  refine Subgroup.mem_center_iff.mpr fun h => ?_
  have h2 : thetaE E n (thetaE E n h) = h := translad_thetaR_thetaR (conjE E) hcc n h
  have h1 := hu.1 (thetaE E n h)
  rw [h2] at h1
  have h3 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
    rw [show thE E n (thetaE E n h) = thetaGL n (conjE E) (thetaE E n h) from rfl, thetaGL_eq]
    exact congrArg (fun x => PhiU n E * x * (PhiU n E)⁻¹) h2
  rw [h3] at h1
  calc h * (u⁻¹ * PhiU n E) = u⁻¹ * (u * h * u⁻¹) * PhiU n E := by group
    _ = u⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹) * PhiU n E := by rw [h1]
    _ = u⁻¹ * PhiU n E * h := by group

theorem translAd_holds : TranslAd := by
  intro E _ _ _ n u hu g
  have hz := GeneralLinearGroup.map_center_le (algebraMap E (Ad E)) (translad_central E n u hu)
  rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at hz
  have hr : ratGL E n u = GeneralLinearGroup.map (algebraMap E (Ad E)) u := rfl
  rw [hr, thetaGL_eq]
  change PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹ =
    GeneralLinearGroup.map (algebraMap E (Ad E)) u * thetaR (conjAd E) n g *
      (GeneralLinearGroup.map (algebraMap E (Ad E)) u)⁻¹
  have hcomm := Subgroup.mem_center_iff.mp hz (thetaR (conjAd E) n g)
  generalize thetaR (conjAd E) n g = T at hcomm ⊢
  generalize GeneralLinearGroup.map (algebraMap E (Ad E)) u = U at hcomm ⊢
  generalize PhiU n (Ad E) = P at hcomm ⊢
  calc P * T * P⁻¹ = U * ((U⁻¹ * P) * T) * (U⁻¹ * P)⁻¹ * U⁻¹ := by group
    _ = U * (T * (U⁻¹ * P)) * (U⁻¹ * P)⁻¹ * U⁻¹ := by rw [hcomm]
    _ = U * T * U⁻¹ := by group

end PositivityTheory.Rg.BcB.G8

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.TopoThetaRCont
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

theorem topo_units {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.t2Space
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)
  exact ⟨h.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space⟩

theorem topo_thetaR_cont {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R)
    (hc : Continuous c) (n : ℕ) : Continuous (thetaR c n) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv.matrix_map hc).matrix_transpose,
    (Units.continuous_val.matrix_map hc).matrix_transpose⟩

theorem topo_countable (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
    fun _ _ h => Units.ext h

theorem topo_thF_cont (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : ∀ g, thF E n g = PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g *
      (PhiU n (Af E))⁻¹ := fun g => thetaGL_eq n (Af E) _ g
  rw [show (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = _ from funext h]
  exact (continuous_const.mul (topo_thetaR_cont _ (continuous_conjFin _) n)).mul continuous_const

theorem topo_holds : Topo := by
  intro E _ _ _ n
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨hc, hs, -⟩ := topo_units (R := ℂ) n
  exact ⟨topo_units n, topo_units n, ⟨hc, hs⟩, topo_countable E n, topo_thF_cont E n,
    topo_thetaR_cont _ Complex.continuous_conj n⟩

end PositivityTheory.Rg.BcB.G8

end
end

