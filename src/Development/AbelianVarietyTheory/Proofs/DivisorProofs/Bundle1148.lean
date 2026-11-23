module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAddMulGeometricDegreeNonnegOfSmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nsq_pow_addFn_const {σ : k →+* ℂ} {B : LB X} (φ : Weight p σ B) (c : ℝ) (m : ℕ)
    (s : (lbPow B m).ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    ((φ.addFn fun _ => c).pow m).nsq s y = (φ.pow m).nsq s y * Real.exp (-(m * c)) := by
  simp only [Weight.nsq]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Weight.addFn]
  push_cast
  ring

theorem isometric_pull_id (L : HermLB p) : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
    (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
  · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
      (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
    rw [Category.comp_id]
  · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))

theorem recursion_pull_id [IsLocallyNoetherian X] {D : ℕ} (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ}
    (H : L.IsArithHeight h) (m : ℕ) {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q)
    (r : ((L.pull (𝟙 X) hq).pow m).B.ι → X.functionFieldˣ) (hr : IsRatSec ((L.pull (𝟙 X) hq).pow m).B r) :
    (L.pull (𝟙 X) hq).ArchIntegrable ((L.pull (𝟙 X) hq).pow m) D hr ∧
      (m : ℝ) * h (genericPoint X) = ∑ᶠ z, ((((L.pull (𝟙 X) hq).pow m).div hr).mult z : ℝ) * h z -
        (L.pull (𝟙 X) hq).archInt ((L.pull (𝟙 X) hq).pow m) D hr := by
  subst hq
  have e := H.recursion X (𝟙 X) hX.charZero D hD hX.dim_eq m r hr
  simpa using e

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem height_add_mul_gdeg_nonneg_of_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  intro HC k _ X _ p D hX hD C h hSP H hnn m u hm hu hex
  obtain ⟨s, hs, hs0⟩ := hex
  have := hX.isLocallyNoetherian
  have := hX.finite_emb
  have hiso := isometric_pull_id C
  set C' := C.pull (𝟙 X) (Category.id_comp p) with hC'
  let s' : (C.pow m).B.Sec := s
  have hg : genericPoint X ∈ nonzeroLocus s' := (sec_ne_zero_iff s').1 hs0
  obtain ⟨r', hr', hdiv, hlog⟩ := (hiso.pow m).exists_isRatSec (isRatSec_ratOfSec s' hg)
  obtain ⟨hI, hrec⟩ := recursion_pull_id hX hD H m (Category.id_comp p) r' hr'

  have hsum : 0 ≤ ∑ᶠ z, (((C'.pow m).div hr').mult z : ℝ) * h z := by
    refine finsum_nonneg fun z => ?_
    rw [hdiv]
    by_cases hz : ((C.pow m).div (isRatSec_ratOfSec s' hg)).mult z = 0
    · simp [hz]
    · exact mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
        (hnn z fun e => CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hz))

  have hneg (σ : k →+* ℂ) : (C.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (C.cInf σ) (hSP σ)
  have hfin (σ : k →+* ℂ) : IsFiniteMeasure ((C.φ σ).chernPart D 1) := by
    have hu1 : ∀ σ (y : CxPts p σ), CInfAt (fun _ : CxPts p σ => (1 : ℝ)) y := fun σ y => cInfAt_const 1 y
    have hc1 : ∀ σ σ' : k →+* ℂ, (Weight.ofFun (fun _ : CxPts p σ => (1 : ℝ))).IsConj
        (Weight.ofFun (fun _ : CxPts p σ' => (1 : ℝ))) := fun _ _ _ _ _ _ _ => rfl
    obtain ⟨Φ, hΦ⟩ := ((HC.arExists k X p D hX).2 (Option Unit)
      (fun o : Option Unit => o.elim (ArInt.fnB (fun σ (_ : CxPts p σ) => (1 : ℝ)) hu1 hc1) fun _ => C)).1
    have h1 := ((HC.arMix.fnB HC.arExists hX hΦ (Pi.single () 1)).1 σ).1
    rw [(isometric_comb_single (fun _ : Unit => C) ()).chernPart_eq σ D 1] at h1
    exact (integrable_const_iff.1 (integrableOn_univ.1 h1)).resolve_left one_ne_zero

  have hpt (σ : k →+* ℂ) : ∀ y ∈ offSupp p σ ((C'.pow m).div hr'),
      logNorm ((C'.pow m).φ σ) r' y ≤ m * u := by
    intro y hy
    rw [hdiv] at hy
    rw [hlog σ hy]
    have hy' : y ∈ ptsIn p σ (nonzeroLocus s') := by
      have := hy
      rwa [offSupp_divOfSec] at this
    rw [logNorm_ratOfSec _ hy']
    have h1 := hs σ y
    change (((C.φ σ).addFn fun _ => 2 * u).pow m).nsq (secVal p σ s') y ≤ 1 at h1
    rw [nsq_pow_addFn_const] at h1
    have h2 : ((C.φ σ).pow m).nsq (secVal p σ s') y ≤ Real.exp (m * (2 * u)) := by
      have := Real.exp_pos (m * (2 * u))
      rw [Real.exp_neg] at h1
      rwa [mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at h1
    have h0 := ((C.φ σ).pow m).nsq_nonneg (secVal p σ s') y
    have h3 : Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) ≤ m * (2 * u) := by
      rcases h0.eq_or_lt with e | e
      · rw [← e, Real.log_zero]; positivity
      · exact (Real.log_le_iff_le_exp e).2 h2
    change Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) / 2 ≤ _
    linarith
  have hA : C'.archInt (C'.pow m) D hr' ≤ m * u * gdeg C D := by
    rw [HermLB.archInt, gdeg, chInt, mul_finsum]
    refine finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun σ => ?_
    have hS : MeasurableSet (offSupp p σ ((C'.pow m).div hr')) := (isOpen_offSupp _).measurableSet
    have hint := hI σ
    rw [← hiso.chernIntegrableOn_eq] at hint
    rw [← hiso.chernInt_eq]
    haveI := hfin σ
    simp only [Weight.chernInt, hneg σ, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_const, smul_eq_mul, mul_one]
    calc ∫ y in offSupp p σ ((C'.pow m).div hr'), logNorm ((C'.pow m).φ σ) r' y ∂(C.φ σ).chernPart D 1
        ≤ ∫ y in offSupp p σ ((C'.pow m).div hr'), (m * u : ℝ) ∂(C.φ σ).chernPart D 1 :=
          setIntegral_mono_on hint.1 (integrable_const _).integrableOn hS (hpt σ)
      _ = ((C.φ σ).chernPart D 1).real (offSupp p σ ((C'.pow m).div hr')) * (m * u) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((C.φ σ).chernPart D 1).real Set.univ * (m * u) :=
          mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
            (by positivity)
      _ = m * u * ((C.φ σ).chernPart D 1).real Set.univ := by ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 ≤ (m : ℝ) * (h (genericPoint X) + u * gdeg C D) := by
    have := hrec
    nlinarith
  exact nonneg_of_mul_nonneg_right this hmpos

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.NuEq

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ}

theorem ratVal_one' : ratVal (1 : X.functionField) y = 1 := by
  have h1 := unitAt_one (under y)
  have e := ratVal_mul (y := y) h1.regAt h1.regAt
  rw [mul_one] at e
  exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm

theorem ratVal_inv' {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, ratVal_one'] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem unitAt_pow {x : X} {u : X.functionField} (h : UnitAt x u) (m : ℕ) : UnitAt x (u ^ m) := by
  induction m with
  | zero => simpa using unitAt_one x
  | succ m ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_zpow {x : X} {u : X.functionField} (h : UnitAt x u) (n : ℤ) : UnitAt x (u ^ n) := by
  cases n with
  | ofNat m => simpa using unitAt_pow h m
  | negSucc m => rw [zpow_negSucc]; exact (unitAt_pow h _).inv

theorem ratVal_pow' {u : X.functionField} (h : UnitAt (under y) u) (m : ℕ) :
    ratVal (u ^ m) y = ratVal u y ^ m := by
  induction m with
  | zero => simpa using ratVal_one'
  | succ m ih => rw [pow_succ, ratVal_mul (unitAt_pow h m).regAt h.regAt, ih, pow_succ]

theorem ratVal_zpow' {u : X.functionField} (h : UnitAt (under y) u) (n : ℤ) :
    ratVal (u ^ n) y = ratVal u y ^ n := by
  cases n with
  | ofNat m => simpa using ratVal_pow' h m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc, ratVal_inv' (unitAt_pow h _), ratVal_pow' h]

end GlobalTheory.VolBr.NuEq

namespace GlobalTheory.VolBr


open NuEq in
theorem nu_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  intro k _ X _ p P a b f hf σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have c0 : 0 < ‖CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG)
  have c0' : 0 < ‖CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG')
  rw [Pair.nu, hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
    ratVal_zpow' uG, ratVal_zpow' uG', eG, eG', (P.L.φ σ).trans i _ y hi hi₀,
    (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_mul, norm_zpow, norm_zpow]
  change _ = ‖CxPts.gv p σ P.L.B i _ y‖ ^ a * ‖CxPts.gv p σ P.A.B j _ y‖ ^ b * _ * _
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
    Real.log_pow, Real.log_pow]
  have key : ∀ (N u v s t : ℝ), N * Real.exp (-(a * (s - 2 * u) + b * (t - 2 * v)) / 2) =
      Real.exp (u * a) * Real.exp (v * b) * N * Real.exp (-(a * s + b * t) / 2) := by
    intro N u v s t
    rw [mul_comm (Real.exp (u * a) * Real.exp (v * b)) N, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  push_cast
  exact key _ _ _ _ _

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuMul

theorem loc_mul {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b a' b' : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') (f * g) i j = P.loc a b f i j * P.loc a' b' g i j := by
  have h1 : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h2 : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [Pair.loc, zpow_add₀ h1, zpow_add₀ h2]
  ring

theorem mul_mem_H_and_nu_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  intro k _ X _ p P a b a' b' f g hf hg
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_mul]
    exact (hf x i j hi hj).mul (hg x i j hi hj)
  · have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    simp only [Pair.nu]
    rw [loc_mul, ratVal_mul (hf _ _ _ hi hj) (hg _ _ _ hi hj), norm_mul]
    have e : -(((a + a' : ℤ) : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + ((b + b' : ℤ) : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
      = -((a : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
        + -((a' : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b' : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 := by
      push_cast; ring
    rw [e, Real.exp_add]
    ring

end GlobalTheory.VolBr.NuMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.NefShift

theorem isNef_shift_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' →
    (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  intro _ k _ X _ p D hX M t t' htt h
  refine ⟨fun σ => ?_, h.vertical, ?_⟩
  · have := (h.semiPos σ).addFn_const (2 * (t' - t))
    have e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) =
        (M.shift (fun _ => t') fun _ => rfl).φ σ := by
      simp only [HermLB.shift, Weight.addFn]
      congr 1
      funext a b
      ring
    exact e ▸ this
  · intro Z i _ _ _ hc hd
    obtain ⟨r, hr, h0⟩ := h.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    have e₁ := HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr
    have e₂ := HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr
    rw [e₂]
    rw [e₁] at h0
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]

end GlobalTheory.NefShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.NefShift

theorem isNef_shift_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D →
      (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro k _ X _ p D hX M t ht hM
  refine ⟨hM.semiPos.shift _ _, fun Z i _ _ κ _ _ _ hd => hM.vertical Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr, h0⟩ := hM.horizontal Z i hc hd
  refine ⟨r, hr, ?_⟩
  rw [GlobalTheory.HtSelfInter.curveDeg_shift hX M t i hc hd hr]
  have : (0 : ℝ) ≤ t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by positivity
  linarith

end GlobalTheory.NefShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isometric_keeps : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.Isometric M → (L.SemiPos D → M.SemiPos D) ∧
      (L.IsNef D → M.IsNef D) ∧ (HtNef L D → HtNef M D) ∧ (∀ a, L.IsSelfInter a → M.IsSelfInter a) ∧
      (IsAmpleLB L.B → IsAmpleLB M.B) := by
  intro hA k _ X _ p D hX L M e
  have hS : L.SemiPos D → M.SemiPos D := HermLB.Isometric.semiPos L M D e
  refine ⟨hS, fun hL => ?_, fun hL => ⟨hS hL.1, fun h H x => hL.2 h (e.symm.isArithHeight hX H) x⟩,
    fun a ha => e.isSelfInter hX ha, fun hL => ?_⟩
  · obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 L
    have HM := e.isArithHeight hX H
    obtain ⟨h₁, h₂⟩ := (H.isNef_iff hX).1 hL
    exact (HM.isNef_iff hX).2 ⟨hS h₁, h₂⟩
  · obtain ⟨w, hw, -⟩ := e.symm
    exact IsAmpleLB.of_lbIso hL M.isLB ⟨w, hw⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndex
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittIdxBound

theorem witt_frame_le_wittIdx : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  intro D V r X Y h
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj V X
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj V Y
  have hiso : ∀ a b, V.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun h.xx a) b
  have hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]
    simp [Matrix.one_apply]
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun v => V.hT v (ev' j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1
    simpa using h1
  have hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x :=
    fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  apply le_csSup
  · refine ⟨Module.finrank D.host.E V.V, ?_⟩
    rintro k ⟨W, rfl, -⟩
    exact Submodule.finrank_le W
  · refine ⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro x hx y hy
      obtain ⟨c, rfl⟩ := hmem x hx
      obtain ⟨d, rfl⟩ := hmem y hy
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]

end GlobalTheory.WittIdxBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDisc
section
open MeasureTheory Filter Topology

namespace GlobalTheory.GoodTop

theorem integrableOn_poincare_disc :
    IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  have h := _root_.GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq
  have key : Integrable (fun z : ℂ =>
      (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2) ‖z‖) := by
    rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2))]
    have h2 : IntegrableOn ((Set.Iic (1 / 2 : ℝ)).indicator
        (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2)) (Set.Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
        Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
      exact h
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro t _
    by_cases ht : t ∈ Set.Iic (1 / 2 : ℝ)
    · simp only [Set.indicator_of_mem ht, Complex.finrank_real_complex, smul_eq_mul]
      norm_num
    · simp only [Set.indicator_of_notMem ht, smul_zero]
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine key.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Set.Iic (1 / 2 : ℝ)
  · have hz' : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
  · have hz' : z ∉ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']

end GlobalTheory.GoodTop
end

