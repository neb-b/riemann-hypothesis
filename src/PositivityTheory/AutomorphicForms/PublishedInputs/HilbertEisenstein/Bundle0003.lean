module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle0008

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleSectionMul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pair_sum {α : Type*} [Zero α] {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Summable f) :
    Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => f (ξ.1 0) * f (ξ.1 1)) ∧
      ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤
        2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := by
  set f' : α → ℝ := fun x => if x = 0 then 0 else f x with hf'def
  have hf'0 : ∀ x, 0 ≤ f' x := fun x => by
    simp only [f']; split_ifs
    · exact le_rfl
    · exact hf0 x
  have hf'le : ∀ x, f' x ≤ f x := fun x => by
    simp only [f']; split_ifs
    · exact hf0 x
    · exact le_rfl
  have hf' : Summable f' := hf.of_nonneg_of_le hf'0 hf'le
  have hP1 : Summable (fun p : α × α => f' p.1 * f p.2) := hf'.mul_of_nonneg hf hf'0 hf0
  have hP2 : Summable (fun p : α × α => f p.1 * f' p.2) := hf.mul_of_nonneg hf' hf0 hf'0
  set g : α × α → ℝ := fun p => f' p.1 * f p.2 + f p.1 * f' p.2 with hgdef
  have hg : Summable g := hP1.add hP2
  set e : (Fin 2 → α) ≃ α × α := finTwoArrowEquiv α
  have hge : ∀ ξ : Fin 2 → α, g (e ξ) = f' (ξ 0) * f (ξ 1) + f (ξ 0) * f' (ξ 1) := fun ξ => rfl
  have hQ : Summable (fun ξ : Fin 2 → α => g (e ξ)) := (e.summable_iff (f := g)).2 hg
  have hQ0 : ∀ ξ : Fin 2 → α, 0 ≤ g (e ξ) := fun ξ => by
    rw [hge]
    exact add_nonneg (mul_nonneg (hf'0 _) (hf0 _)) (mul_nonneg (hf0 _) (hf'0 _))
  have hle : ∀ ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤ g (e ξ.1) := by
    intro ξ
    rw [hge]
    by_cases h0 : ξ.1 0 = 0
    · have h1 : ξ.1 1 ≠ 0 := by
        intro h1
        apply ξ.2
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have : f' (ξ.1 1) = f (ξ.1 1) := by simp only [f', if_neg h1]
      rw [this]
      linarith [mul_nonneg (hf'0 (ξ.1 0)) (hf0 (ξ.1 1))]
    · have : f' (ξ.1 0) = f (ξ.1 0) := by simp only [f', if_neg h0]
      rw [this]
      linarith [mul_nonneg (hf0 (ξ.1 0)) (hf'0 (ξ.1 1))]
  have hQs : Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => g (e ξ.1)) := hQ.subtype _
  have hS : Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => f (ξ.1 0) * f (ξ.1 1)) :=
    hQs.of_nonneg_of_le (fun ξ => mul_nonneg (hf0 _) (hf0 _)) hle
  refine ⟨hS, ?_⟩
  have h1 : ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤
      ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, g (e ξ.1) := hS.tsum_le_tsum hle hQs
  have h2 : ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, g (e ξ.1) ≤ ∑' ξ : Fin 2 → α, g (e ξ) :=
    hQ.tsum_subtype_le _ {ξ | ξ ≠ 0} hQ0
  have h3 : ∑' ξ : Fin 2 → α, g (e ξ) = ∑' p : α × α, g p := e.tsum_eq g
  have h4 : ∑' p : α × α, g p = (∑' x, f' x) * (∑' x, f x) + (∑' x, f x) * (∑' x, f' x) := by
    rw [hgdef, hP1.tsum_add hP2, hf'.tsum_mul_tsum hf hP1, hf.tsum_mul_tsum hf' hP2]
  have h5 : (∑' x, f' x) * (∑' x, f x) + (∑' x, f x) * (∑' x, f' x) = 2 * (∑' x, f x) * ∑' x, f' x := by
    ring
  calc ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤ 2 * (∑' x, f x) * ∑' x, f' x := by
        rw [← h5, ← h4, ← h3]; exact h1.trans h2
    _ = 2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := rfl

theorem decay1D {G : Ad F → ℂ} (hG : G ∈ schwartzBruhat F) {C : Set (IdeleGroup F)} (hC : IsCompact C)
    (w : InfinitePlace F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ C, ∀ T : {r : ℝ // 0 < r}, 1 ≤ (T : ℝ) →
      Summable (fun x : F => ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ∧
      ∑' x : F, (if x = 0 then 0 else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ≤ ((T : ℝ) ^ 3)⁻¹ * M ∧
      ∑' x : F, ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖ ≤ ‖G 0‖ + M := by
  obtain ⟨u, hu, hFu⟩ := exists_decay_bound w hG hC 3
  refine ⟨∑' ξ, |u ξ|, tsum_nonneg fun _ => abs_nonneg _, fun a ha T hT => ?_⟩
  have hs : Summable (fun x : F => ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) :=
    summable_norm_smul_algebraMap _ hG
  have hT0 : 0 < ((T : ℝ) ^ 3)⁻¹ := inv_pos.2 (pow_pos T.2 3)
  have hT1 : ((T : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have hs' : Summable (fun x : F =>
      if x = 0 then (0 : ℝ) else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) :=
    hs.of_nonneg_of_le (fun x => by split_ifs <;> positivity) (fun x => by split_ifs <;> simp)
  have h2 : ∑' x : F, (if x = 0 then 0 else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ≤
      ((T : ℝ) ^ 3)⁻¹ * ∑' ξ, |u ξ| := by
    rw [← tsum_mul_left]
    refine hs'.tsum_le_tsum (fun ξ => ?_) (hu.abs.mul_left _)
    split_ifs with h
    · exact mul_nonneg hT0.le (abs_nonneg _)
    · exact (hFu a ha T hT ξ h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hT0.le)
  refine ⟨hs, h2, ?_⟩
  rw [hs.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero]
  have h3 : ((T : ℝ) ^ 3)⁻¹ * ∑' ξ, |u ξ| ≤ ∑' ξ, |u ξ| :=
    mul_le_of_le_one_left (tsum_nonneg fun _ => abs_nonneg _) hT1
  have h4 := h2.trans h3
  linarith

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (ideleModule F z : ℝ) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow,
    Positive.val_mul, Positive.val_pow]

theorem ideleModule_section_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    (ideleModule F (moduleSection (w0 F) t * (u : Ideles F)) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  change (ideleModule F (moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) = t
  rw [map_mul, ideleModule_moduleSection, hu, mul_one]

theorem integrable_bound : Integrable (fun t : {r : ℝ // 0 < r} => (1 + Real.log t ^ 2)⁻¹) posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  change Integrable _ (Measure.map expPosHomeomorph.toMeasurableEquiv volume)
  refine (integrable_map_equiv expPosHomeomorph.toMeasurableEquiv _).2 ?_
  refine integrable_inv_one_add_sq.congr (Filter.Eventually.of_forall fun x => ?_)
  show (1 + x ^ 2)⁻¹ = (1 + Real.log (Real.exp x) ^ 2)⁻¹
  rw [Real.log_exp]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ImportsAlt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem top (hP : SPois) (hI : SPois → SInt) (hG : SPois → SInt → SSmooth → SGrowth) (hS : SPois → SInt → SSmooth)
    (hL : SPois → SInt → SSmooth → SLeft) (hV : SPois → SInt → SSmooth → SLevel) (hO : SPois → SInt → SSmooth → SOpen) (hC : SPois → SInt → SSmooth → SCent)
    (hK : SPois → SInt → SSmooth → SKfin) (hW : SPois → SInt → SSmooth → SWt) (hLo : SPois → SInt → SSmooth → SLow) (hZ : SPois → SInt → SSmooth → SZfin)
    (hE : SPois → SInt → SSmooth → SExp) (hM : SPois → SInt → SSmooth → SSmul) : HilbertEisOne := by
  have hI' := hI hP
  have hS' := hS hP hI'
  intro F _ _ _ ω c hfin hodd hcond hram
  have H : Hyp ω c := ⟨hfin, hodd, hcond, hram⟩
  obtain ⟨C₀, L, hC₀, hexp⟩ := hE hP hI' hS' F ω c H
  have hs := hS' F ω c H
  let φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hlev : ∀ w, φ ∈ UpperTheory.V.Hi.fixd (locSm F w) (K1 w (c w)) := by
    intro w k hk
    refine Subtype.ext (funext fun g => ?_)
    exact hV hP hI' hS' F ω c H w k hk g
  have hcent := hC hP hI' hS' F ω c H
  have hwt := hW hP hI' hS' F ω c H hs
  have hlow := hLo hP hI' hS' F ω c H hs
  have hol : IsHol 1 c ω φ :=
    { aut := ⟨hL hP hI' hS' F ω c, hO hP hI' hS' F ω c H hs, hK hP hI' hS' F ω c H hs, hZ hP hI' hS' F ω c hfin φ hcent hwt hlow,
        hG hP hI' hS' F ω c H⟩
      level := hlev
      cent := hcent
      wt := hwt
      low := hlow }
  have hM' := hM hP hI' hS' F ω c 1 φ C₀⁻¹ (inv_ne_zero hC₀)
  refine ⟨C₀⁻¹ • φ, C₀⁻¹ * L, hM'.1 hol, ?_⟩
  have h2 := hM'.2 _ _ hexp
  convert h2 using 2
  rw [← mul_assoc, inv_mul_cancel₀ hC₀, one_mul]

end UpperTheory.HilbertEisensteinWeightOne
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.KFinitenessHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sgn (b : Bool) : ℝ := if b then 1 else -1

def archE (ε : InfinitePlace F → Bool) (x y : UpperTheory.V.TR.Rinf F) : ℂ :=
  ∏ v, (((x v : ℂ) + (sgn (ε v) : ℂ) * Complex.I * (y v : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * ((x v : ℂ) ^ 2 + (y v : ℂ) ^ 2)))


open Classical in
def PhiE (c : HeightOneSpectrum (𝓞 F) → ℕ) (ε : InfinitePlace F → Bool) (ξ : Fin 2 → Ad F) : ℂ :=
  archE ε (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (ξ 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

def lam (k : UpperTheory.V.TR.Kinf F 2) : ℂ := ∏ w, ((k.1 0 0 w : ℂ) + Complex.I * (k.1 0 1 w : ℂ))

def eps (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) : Bool :=
  decide (0 < k.1 0 0 w * k.1 1 1 w - k.1 0 1 w * k.1 1 0 w)

theorem place (a b c d x y : ℝ) (h1 : a * a + c * c = 1) (h2 : b * b + d * d = 1) (h3 : a * b + c * d = 0)
    (h4 : a * a + b * b = 1) (h5 : c * c + d * d = 1) (h6 : a * c + b * d = 0) :
    (((x * a + y * c : ℝ) : ℂ) + Complex.I * ((x * b + y * d : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2)) =
    ((a : ℂ) + Complex.I * (b : ℂ)) * (((x : ℂ) + (sgn (decide (0 < a * d - b * c)) : ℂ) * Complex.I * (y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hsq : (x * a + y * c) ^ 2 + (x * b + y * d) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination x ^ 2 * h4 + y ^ 2 * h5 + 2 * x * y * h6
  have hC : (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hsq
  rw [hC]
  generalize Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = E
  have hs2 : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h4 + h5 - (a * c + b * d) * h6
  have hsg : ((sgn true : ℝ) : ℂ) = 1 := by simp [sgn]
  have hsg' : ((sgn false : ℝ) : ℂ) = -1 := by simp [sgn]
  rcases mul_self_eq_one_iff.mp hs2 with hs | hs
  · have hc : c = -b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hpos : 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_true hpos, hsg]
    subst hc hd
    push_cast
    linear_combination (-((b : ℂ) * (y : ℂ) * E)) * Complex.I_sq
  · have hc : c = b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = -a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hneg : ¬ 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_false hneg, hsg']
    subst hc hd
    push_cast
    linear_combination ((c : ℂ) * (y : ℂ) * E) * Complex.I_sq

theorem rels (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) :
    k.1 0 0 w * k.1 0 0 w + k.1 1 0 w * k.1 1 0 w = 1 ∧ k.1 0 1 w * k.1 0 1 w + k.1 1 1 w * k.1 1 1 w = 1 ∧
    k.1 0 0 w * k.1 0 1 w + k.1 1 0 w * k.1 1 1 w = 0 ∧ k.1 0 0 w * k.1 0 0 w + k.1 0 1 w * k.1 0 1 w = 1 ∧
    k.1 1 0 w * k.1 1 0 w + k.1 1 1 w * k.1 1 1 w = 1 ∧ k.1 0 0 w * k.1 1 0 w + k.1 0 1 w * k.1 1 1 w = 0 := by
  have hA := Unitary.coe_star_mul_self k
  have hB := Unitary.coe_mul_star_self k
  have e : ∀ (M N : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)), M = N → ∀ i j, M i j w = N i j w :=
    fun M N h i j => by rw [h]
  have a1 := e _ _ hA 0 0
  have a2 := e _ _ hA 1 1
  have a3 := e _ _ hA 0 1
  have b1 := e _ _ hB 0 0
  have b2 := e _ _ hB 1 1
  have b3 := e _ _ hB 0 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at a1 a2 a3 b1 b2 b3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

theorem arch_rot (k : UpperTheory.V.TR.Kinf F 2) (X Y : UpperTheory.V.TR.Rinf F) :
    arch (fun w => X w * k.1 0 0 w + Y w * k.1 1 0 w) (fun w => X w * k.1 0 1 w + Y w * k.1 1 1 w) =
      lam k * archE (eps k) X Y := by
  unfold arch archE lam
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rels k w
  exact place (k.1 0 0 w) (k.1 0 1 w) (k.1 1 0 w) (k.1 1 1 w) (X w) (Y w) h1 h2 h3 h4 h5 h6

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (k : UpperTheory.V.TR.Kinf F 2) (v : Fin 2 → Ad F) :
    Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      lam k * PhiE c (eps k) v := by
  have hK : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (UpperTheory.V.TR.pInf F) = k.1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pInf_infGL (E := F) (Unitary.toUnits k))
    exact h
  have hKf : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (pFin F) = 1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (E := F) (Unitary.toUnits k))
    exact h
  have ef : ∀ i, pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
    intro i
    rw [RingHom.map_vecMul, hKf, Matrix.vecMul_one]
    rfl
  have e0 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 0) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 0 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 0 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have e1 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 1) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 1 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 1 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  unfold Phi PhiE
  rw [ef 0, ef 1, e0, e1, arch_rot k, mul_assoc]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul]
  rfl

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := by
  unfold absD
  exact ((IdeleGroup.ideleModule F) (Matrix.GeneralLinearGroup.det g)).2.le

theorem eis_smul (ω : HChar F) (a : ℂ) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) :
    Eis ω (fun v => a * Ψ v) g = a * Eis ω Ψ g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  simp only [tsum_mul_left]
  ring

theorem eis_mul_right (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g K : GA F 2) :
    Eis ω Ψ (g * K) = ((absD K ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
      Eis ω (fun v => Ψ (v ᵥ* (K : Matrix (Fin 2) (Fin 2) (Ad F)))) g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  rw [absD_mul, Real.mul_rpow (absD_nonneg g) (absD_nonneg K)]
  simp only [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) _) g K, Units.val_mul, ← Matrix.vecMul_vecMul]
  push_cast
  ring

theorem cpt_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2)
    (k : UpperTheory.V.TR.Kinf F 2) (g : GA F 2) :
    (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩).1 g =
      ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) *
        Eis ω (PhiE c (eps k)) g := by
  change Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k)) = _
  rw [eis_mul_right, show (fun v => Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))) = fun v => lam k * PhiE c (eps k) v from funext (phi_rot c k), eis_smul]
  ring

end UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

open UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein in
theorem UpperTheory.HilbertEisensteinWeightOne.K_finiteness_holds : SPois → SInt → SSmooth → SKfin := by
  intro _ _ _ F _ _ _ ω c _ hs
  haveI : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hle : (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩)).map
      (UpperTheory.V.TR.Sm F 2).subtype ≤
      Submodule.span ℂ (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : (UpperTheory.V.TR.Sm F 2).subtype (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩) =
        ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) •
          Eis ω (PhiE c (eps k)) :=
      funext fun g => by rw [Pi.smul_apply, smul_eq_mul]; exact cpt_eq ω c hs k g
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨eps k, rfl⟩)
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LeftInvarianceHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace LeftInvarianceEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rowA_vecMul (ξ : Fin 2 → F) (γ : GL (Fin 2) F) :
    rowA ξ ᵥ* ((ratGL F 2 γ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowA (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) := by
  funext i
  exact (RingHom.map_vecMul (algebraMap F (Ad F)) (γ : Matrix (Fin 2) (Fin 2) F) ξ i).symm

def permE (γ : GL (Fin 2) F) : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])

theorem thetaS_ratGL (Ψ : (Fin 2 → Ad F) → ℂ) (a : (Ad F)ˣ) (γ : GL (Fin 2) F) (g : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (ratGL F 2 γ * g)) =
      thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) := by
  unfold thetaS
  refine Eq.trans ?_ ((permE γ).tsum_eq (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
    Ψ (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))))
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, Units.val_mul,
    ← Matrix.vecMul_vecMul, rowA_vecMul]
  rfl

theorem absD_ratGL (γ : GL (Fin 2) F) (g : GA F 2) : absD (ratGL F 2 γ * g) = absD g := by
  have h : Matrix.GeneralLinearGroup.det (ratGL F 2 γ) =
      IdeleGroup.diagonal F (Matrix.GeneralLinearGroup.det γ) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap F (Ad F)) γ) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  unfold absD
  rw [map_mul, map_mul, h, IdeleGroup.ideleModule_diagonal, one_mul]

end LeftInvarianceEisenstein

theorem left_invariance_holds : SPois → SInt → SSmooth → SLeft := by
  intro _ _ _ F _ _ _ ω c γ g
  unfold Eis eisInt
  simp_rw [LeftInvarianceEisenstein.thetaS_ratGL, LeftInvarianceEisenstein.absD_ratGL]

end UpperTheory.HilbertEisensteinWeightOne
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibFresh
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.Fresh

variable {F : Type} [Field F] [NumberField F]

theorem ordI_mul_of_ne_bot (v : HeightOneSpectrum (𝓞 F)) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ordI v (I * J) = ordI v I + ordI v J := by
  unfold ordI
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

theorem ordI_asIdeal_self (w : HeightOneSpectrum (𝓞 F)) : ordI w w.asIdeal = 1 := by
  unfold ordI
  exact Associates.count_self w.associates_irreducible

theorem hasDerivAt_chart_curve [IsTotallyReal F] (f : GA F 2 → ℂ) (g : GA F 2)
    (hd : DifferentiableAt ℝ (UpperTheory.V.TR.chart f g) (UpperTheory.V.TR.oneL F 2))
    (k : ℝ → GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (X : UpperTheory.V.TR.Lie F 2) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => UpperTheory.V.TR.toL (k t).val) X 0) :
    HasDerivAt (fun t => f (g * UpperTheory.V.TR.infGL F 2 (k t))) (UpperTheory.V.TR.lieD X f g) 0 := by
  unfold UpperTheory.V.TR.lieD
  have hf := hd.hasFDerivAt
  have hpt : UpperTheory.V.TR.oneL F 2 = (fun t => UpperTheory.V.TR.toL (k t).val) 0 := by
    simp only [h0, Units.val_one]
  rw [hpt] at hf
  have := hf.comp_hasDerivAt 0 hk
  rw [← hpt] at this
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  exact (UpperTheory.V.TR.chart_val f g (k t)).symm

end UpperTheory.HilbertEisensteinWeightOne.Fresh
end
end

