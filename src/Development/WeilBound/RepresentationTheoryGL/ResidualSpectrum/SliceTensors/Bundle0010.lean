module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ConstantTermZeroEq
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def E_L (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N r : ℕ) (t : ℝ) :
    (GA E N → ℂ) →ₗ[ℂ] (GA E N → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun g => aT E N r t * g

theorem E_L_apply {N r : ℕ} (t : ℝ) (f : GA E N → ℂ) (g : GA E N) : E_L E N r t f g = f (aT E N r t * g) := rfl

theorem constant_term_zero_eq {N r : ℕ} (f : GA E N → ℂ) : E_L E N r 0 f = f := by
  funext g
  rw [E_L_apply, aT_zero, one_mul]

theorem E_LL {N r : ℕ} (s t : ℝ) (f : GA E N → ℂ) : E_L E N r s (E_L E N r t f) = E_L E N r (t + s) f := by
  funext g
  rw [E_L_apply, E_L_apply, E_L_apply, aT_add, mul_assoc]

variable {r s : ℕ}

theorem E_key_left {r₁ : ℕ} (hr₁ : r₁ < r) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E r → ℂ) (m₂ : GA E s) (h : GA E (r + s)) (hψF : ∀ m₁, ψ m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₁ ψ = E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a (An.ctn r₁ φ.1) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  funext m₁
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_top hr₁ x hx
    omega
  have e2 : ∀ A : UPos r r₁ → Ad E, ψ (unipGL A * m₁) = ∑ t ∈ τs, a t *
      An.ctn r φ.1 (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)) := by
    intro A
    rw [hψF, hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : lev (Ad E) r s (unipGL A * m₁, m₂) = lev (Ad E) r s (unipGL A, 1) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_left r s r₁ hr₁, mul_assoc, ← mul_assoc (aT E (r + s) r t), aT_comm_parGL _ _ _ _ hpos,
      mul_assoc]
  have e3 : ∀ z, ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r x} => boxMeasure E) =
      (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) r₁ * ∫ b, An.ctn r₁ φ.1 (parGL (joinPos (r := r₁) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} => boxMeasure E)) := by
    intro z
    simp only [E_ctn_eq r]
    rw [integral_const_mul, ← constantTermPar_eq_top hr₁ hφc, constantTermPar_eq_bot hr₁ hφc hφl]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext b
    exact E_ct_eq r₁ _ _
  have hint : ∀ t ∈ τs, Integrable (fun A : UPos r r₁ → Ad E => a t * An.ctn r φ.1
      (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)))
      (Measure.pi fun _ => boxMeasure E) := by
    intro t _
    refine (integrable_box ?_).const_mul _
    exact hcr.comp ((((E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r).comp
      (continuous_pi fun q => continuous_apply _))).mul continuous_const)
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [integral_finsetSum _ hint]
  simp only [integral_const_mul, E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_box_reindex (eL r s r₁ hr₁)
    (fun b => An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * y))), e3]
  ring

theorem E_hB_left {r₁ : ℕ} (hr₁ : r₁ < r) (m₂ : GA E s) (h : GA E (r + s)) (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (t : ℝ) (f : GA E (r + s) → ℂ) :
    E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E => (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a (E_L E (r + s) r₁ t f) =
    E_L E r r₁ t (E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a f) := by
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r₁ x → ((x.1.1 : ℕ) < r₁ ↔ (x.1.2 : ℕ) < r₁) := fun x hx => by
    have := E_pos_bot hr₁ x hx
    omega
  funext m₁
  rw [E_L_apply]
  unfold E_B
  refine congrArg (κ * ·) (Finset.sum_congr rfl fun u _ => congrArg (a u * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) r₁ t * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) r₁ t), aT_comm, mul_assoc,
    ← mul_assoc (aT E (r + s) r₁ t), ← lev_aT_left r s r₁ hr₁.le, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem E_trans_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (w : GA E (r + s)) :
    ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * w)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * w)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E)) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hpq : r < r + r₂ := by omega
  simp only [E_ctn_eq r]
  rw [integral_const_mul, ← constantTermPar_eq_bot hpq hφc hφl, constantTermPar_eq_top hpq hφc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext b
  exact E_ct_eq (r + r₂) _ _

theorem E_int_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (z : GA E (r + s)) :
    ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    ∑ t ∈ τs, a t * ((E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * (aT E (r + s) r t * z))
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E))) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have e1 : ∀ b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E, F (parGL (joinPos (r := r) 0 b) * z) =
      ∑ t ∈ τs, a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z)) := by
    intro b
    rw [hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc]
  have hint : ∀ t ∈ τs, Integrable (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E =>
      a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))) (Measure.pi fun _ => boxMeasure E) :=
    fun t _ => (integrable_box (hcr.comp
      ((E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) r).mul continuous_const))).const_mul _
  simp only [e1]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, E_trans_right hr₂ φ hφ]

theorem E_G_shift {r₂ : ℕ} (hr₂ : 0 < r₂) (τs : Finset ℝ) (a : ℝ → ℂ) (u : ℝ) (f : GA E (r + s) → ℂ)
    (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (E_L E (r + s) (r + r₂) u f) z =
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (aT E (r + s) (r + r₂) u * z) := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop (r + r₂) x →
      ((x.1.1 : ℕ) < r + r₂ ↔ (x.1.2 : ℕ) < r + r₂) := fun x hx => by
    have := E_pos_top hpq x hx
    omega
  unfold E_B
  refine congrArg (1 * ·) (Finset.sum_congr rfl fun t _ => congrArg (a t * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) (r + r₂) u * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) (r + r₂) u), aT_comm, mul_assoc]

theorem E_aT_right {r₂ : ℕ} (hr₂s : r₂ ≤ s) (t : ℝ) (m₁ : GA E r) (m₂ : GA E s) (h : GA E (r + s)) :
    aT E (r + s) (r + r₂) t * (lev (Ad E) r s (m₁, m₂) * h) =
      aT E (r + s) r t * (lev (Ad E) r s (m₁, aT E s r₂ t * m₂) * h) := by
  have e1 : aT E (r + s) (r + r₂) t = lev (Ad E) r s (1, aT E s r₂ t) * aT E (r + s) r t := by
    rw [lev_aT_right r s r₂ hr₂s, mul_assoc, ← aT_add, neg_add_cancel, aT_zero, mul_one]
  have e2 : lev (Ad E) r s (m₁, aT E s r₂ t * m₂) = lev (Ad E) r s (1, aT E s r₂ t) * lev (Ad E) r s (m₁, m₂) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, e2, (aT_comm_lev r s t _).symm]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PDich

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a N : ℕ}


open PExpFin in
theorem continuous_aT (F : Sm E N) (r : ℕ) (g : GA E N) : Continuous fun t : ℝ => F.1 (aT E N r t * g) := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) g
  set k := Matrix.GeneralLinearGroup.map (pFin E) g
  have hg : g = infGL E N y * finGL E N k := (infGL_mul_finGL g).symm
  have e : ∀ t, aT E N r t * g = g * infGL E N (y⁻¹ * aInf E N r t * y) := by
    intro t
    calc aT E N r t * g = infGL E N (y * (y⁻¹ * aInf E N r t * y)) * finGL E N k := by
          rw [hg, aT, ← mul_assoc, ← map_mul]
          congr 2
          group
      _ = g * infGL E N (y⁻¹ * aInf E N r t * y) := by
          rw [hg, map_mul, mul_assoc, mul_assoc, infGL_comm, mul_assoc]
  have e2 : (fun t : ℝ => F.1 (aT E N r t * g)) =
      chart F.1 g ∘ fun t : ℝ => toL (y⁻¹ * aInf E N r t * y).val := by
    funext t
    rw [Function.comp_apply, chart_val, e]
  rw [e2]
  refine (F.2 g).continuousOn.comp_continuous ?_ fun t => val_mem_invSet _
  change Continuous fun t : ℝ => (y⁻¹).val * Matrix.diagonal (fun (i : Fin N) (_ : InfinitePlace E) =>
    Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)) * y.val
  have hi : ∀ (i : Fin N) (t : ℝ), (if (i : ℕ) < r then (t : ℂ) else 0) = (if (i : ℕ) < r then 1 else 0) * t := by
    intro i t
    split_ifs <;> simp
  simp_rw [hi]
  fun_prop

theorem ascEmb_one {π π' : CuspSub E a} (h : π.Iso π') : AscEmb π.V π' 1 := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl π.V
  let P := Submodule.projectionOnto π.V q hq
  have hP : ∀ φ (hφ : φ ∈ π.V), P φ = ⟨φ, hφ⟩ := fun φ hφ =>
    Submodule.projectionOnto_apply_left hq ⟨φ, hφ⟩
  have hs : ∑ _ : Fin 1, a = a := by simp
  refine ⟨hs, fun _ => 1, fun i => ?_, π'.V.subtype ∘ₗ T.toLinearMap ∘ₗ P, fun φ hφ => ?_, fun φ hφ h0 => ?_,
    fun o φ hφ => ?_⟩
  · have e : -spehExp 1 i + a * spehExp 1 i = 0 := by simp [spehExp]
    rw [e]
    exact ⟨fun _ _ _ => rfl, fun _ => by simp [HChar.val, HChar.locK, HChar.loc], fun _ => by simp [HChar.inf]⟩
  · rw [show (fun _ : Fin 1 => π'.twist 1) = fun _ => π' from funext fun _ => π'.twist_one, indForms_one]
    exact (T (P φ)).2
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, hP φ hφ] at h0
    have h1 : T ⟨φ, hφ⟩ = 0 := Subtype.ext h0
    have h2 : (⟨φ, hφ⟩ : π.V) = 0 := T.injective (h1.trans T.map_zero.symm)
    exact congrArg Subtype.val h2
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      hP φ hφ, hP _ (π.stable o φ hφ)]
    have e : (⟨act o φ, π.stable o φ hφ⟩ : π.V) = π.op o ⟨φ, hφ⟩ := rfl
    rw [e, hT]
    rfl

end PDich

open PExpFin PDich in
theorem dich_of (hD : Dict) (hT : FinTr) (hK : KillPoly) : Dich := by
  intro E _ _ _ N hN V hV
  obtain ⟨-, -, -, hDct⟩ := hD E N
  by_cases hex : ∃ r, 0 < r ∧ r < N ∧ ∃ φ ∈ V, An.ctn r φ.1 ≠ 0
  · right
    obtain ⟨r, hr, hrN, φ, hφ, hne⟩ := hex
    obtain ⟨hct, -⟩ := hDct φ (hV.aut φ hφ) r hr hrN
    have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
      let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
      obtain ⟨F, hF, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ (hV.aut φ hφ).left (hV.aut φ hφ).level μ 𝓕 hμ h𝓕
      have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
      intro g
      rw [e2]
      exact PDich.continuous_aT F r g
    obtain ⟨p, hp, hk, hroot⟩ := hK (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
      (hT E N φ (hV.aut φ hφ) r hr hrN _ hct)
    have hdeg : 0 < p.degree := hp.degree_pos.2 fun h1 => hne (funext fun g => by
      have := hk g
      rw [h1] at this
      simpa [aT_zero] using this)
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    obtain ⟨c, -, F, hF, hF0, hFe⟩ := hroot z hz
    exact ⟨r, hr, hrN, c, φ, hφ, An.ctn r φ.1, hct, F, hF, hF0, hFe⟩
  · left
    push Not at hex
    have hcusp : ∀ φ ∈ V, IsCuspForm φ := fun φ hφ => ⟨hV.aut φ hφ, by
      intro r hr hrN inst1 inst2 μ 𝓕 hμ hF g
      obtain rfl : inst1 = _root_.borel _ := inst2.measurable_eq
      obtain ⟨c, -, e⟩ := (hDct φ (hV.aut φ hφ) r hr hrN).2 _ ⟨μ, 𝓕, hμ, hF, rfl⟩
      have := congrFun e g
      rw [hex r hr hrN φ hφ] at this
      simpa [PositivityTheory.Affgl.CT.ct] using this⟩
    let π : CuspSub E N := ⟨V, hcusp, hV.stable, hV.ne_bot, hV.irred⟩
    have hn : IsNormalised π := fun φ hφ => (hV.sqInt φ hφ).1
    exact ⟨π, GlobalTheory.SpehPair.isUnitary_of_isNormalised hn, hn, fun π' hiso => ascEmb_one hiso⟩

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LintegralMulRight
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

namespace PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

theorem sq_lintegral_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) {g : Y → ℝ≥0∞} (hg : AEMeasurable g ρ) :
    (∫⁻ y, g y ∂ρ) ^ 2 ≤ ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞))
    aemeasurable_const hg
  simp only [ENNReal.one_rpow, lintegral_const] at h
  calc (∫⁻ y, g y ∂ρ) ^ 2 ≤ (ρ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        simpa [Pi.mul_apply] using h
    _ = ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem lintegral_sq_lt_top {μ : Measure (GA E N)} [μ.IsHaarMeasure] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) : ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hm := ((memL2_iff_fundamental_domain (isFundamentalDomain_stdDom (latticeGL E N) μ)).1 h).2
  have := hm
  change eLpNorm _ _ _ < ⊤ at this
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hm.aestronglyMeasurable] at this
  simpa using this

theorem lintegral_mul_right {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) (g : GA E N) :
    ∫⁻ x in stdDom (latticeGL E N), ‖φ (x * g)‖ₑ ^ 2 ∂μ = ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have hm : AEMeasurable (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2) (quotMeasure (latticeGL E N) μ) :=
    h.2.aestronglyMeasurable.enorm.pow_const 2
  have e1 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2)
  have e2 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ (rmul (latticeGL E N) g q)‖ₑ ^ 2)
  simp only [rmul_mk, h.1.descend_mk] at e1 e2
  rw [← e1, ← e2]
  have hp := measurePreserving_rmul (Γ := latticeGL E N) (μ := μ) g
  conv_rhs => rw [← hp.map_eq]
  rw [lintegral_map' (by rwa [hp.map_eq]) (measurable_rmul g).aemeasurable]

theorem memL2_of_smoothing (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (Lie E N))
    [ν.IsAddHaarMeasure] {α : Lie E N → ℂ} (hα : GlobalTheory.CuspQuot.IsTest (invSet E N) α) {φ : GA E N → ℂ}
    (hc : Continuous φ) (h : MemL2Quotient (latticeGL E N) μ φ) :
    MemL2Quotient (latticeGL E N) μ (GlobalTheory.CuspQuot.smoothing ν α φ) := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have : ProperSpace (Lie E N) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hl : LeftInv (latticeGL E N) φ := h.1
  have hlS : LeftInv (latticeGL E N) (GlobalTheory.CuspQuot.smoothing ν α φ) := fun γ hγ g => by
    simp only [GlobalTheory.CuspQuot.smoothing, chart, mul_assoc, hl γ hγ]
  have hH : Continuous fun p : GA E N × Lie E N => α p.2 * chart φ p.1 p.2 :=
    GlobalTheory.CuspQuot.continuous_integrand hα hc
  have hmS : AEStronglyMeasurable (GlobalTheory.CuspQuot.smoothing ν α φ) (μ.restrict (stdDom (latticeGL E N))) :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
  set K := tsupport α with hKdef
  have hKν : ν K < ⊤ := hα.2.1.isCompact.measure_lt_top
  have hpt : ∀ x, ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by
    intro x
    have h1 : ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ≤ ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν := by
      rw [setLIntegral_eq_of_support_subset]
      · exact enorm_integral_le_lintegral_enorm _
      · intro y hy
        by_contra hyK
        apply hy
        simp [image_eq_zero_of_notMem_tsupport hyK]
    have hx : Continuous fun y => α y * chart φ x y := hH.comp (continuous_const.prodMk continuous_id)
    have h2 := sq_lintegral_le (ν.restrict K) (g := fun y => ‖α y * chart φ x y‖ₑ) hx.enorm.aemeasurable
    rw [Measure.restrict_apply_univ] at h2
    calc _ ≤ (∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν) ^ 2 := by gcongr
      _ ≤ ν K * ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := h2
      _ ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by gcongr; exact Measure.restrict_le_self
  set I := ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ with hIdef
  have hI : I < ⊤ := lintegral_sq_lt_top h
  have hin : ∀ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ = ‖α y‖ₑ ^ 2 * I := by
    intro y
    by_cases hy : IsUnit (Matrix.of y)
    · simp_rw [chart, dite_eq_left hy, enorm_mul, mul_pow]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_right h]
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hα.2.2 h')
      simp [this]
  have hα2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν < ⊤ := by
    have hmα := hα.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := ν) hα.2.1
    have := hmα
    change eLpNorm _ _ _ < ⊤ at this
    rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmα.aestronglyMeasurable] at this
    simpa using this
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖α y * chart φ x y‖ₑ ^ 2)
      ((μ.restrict (stdDom (latticeGL E N))).prod ν) :=
    ((ENNReal.continuous_pow 2).comp hH.enorm).measurable.aemeasurable
  refine (memL2_iff_fundamental_domain hd).2 ⟨hlS, ?_⟩
  change eLpNorm _ _ _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmS]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x in stdDom (latticeGL E N), ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in stdDom (latticeGL E N), ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν K * ∫⁻ x in stdDom (latticeGL E N), ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ hKν.ne
    _ = ν K * ∫⁻ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ν K * ((∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν) * I) := by
        simp_rw [hin]
        rw [lintegral_mul_const' _ _ hI.ne]
    _ < ⊤ := ENNReal.mul_lt_top hKν (ENNReal.mul_lt_top hα2 hI)

end PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

end
end

