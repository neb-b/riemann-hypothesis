module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0015
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SmoothDecompositionForms
public import Formalism.PeriodIntegrals.UpqRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartCanonGaugeCongr
section
set_option autoImplicit false

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem bilinPart_canonGauge_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → (∀ i j, ((bilinPart k h)ᵀ - bilinPart k h) i j ∈ (algebraMap R k).range) ∧ (∀ a : O, (∀ i j, ((dAct k B a)ᵀ * bilinPart k h - bilinPart k h * dAct k B (star a)) i j ∈ (algebraMap R k).range)) ∧ (∀ a : O, (∀ i j, (dAct k B a) i j ∈ (algebraMap R k).range)) ∧ dAct k B 1 = 1 ∧ (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ ∀ a b : O, dAct k B (a * b) = dAct k B a * dAct k B b := by
  intro R _ d O _ _ k _ _ _ B h hc
  refine ⟨fun i j => ?_, fun a i j => ?_, fun a i j => ?_, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one k B,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add k B, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul k B⟩
  · have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low h hc.ax0 hc.ax1) _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz i j), map_sub, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_swap', coeff_map,
      Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm (Finsupp.single (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.swE d _) 1)] at e
    exact ⟨_, e⟩
  · obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int B h hc a j i
    refine ⟨-r, ?_⟩
    rw [map_neg, hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, bilinPart,
      neg_mul, Finset.sum_neg_distrib, mul_comm (dAct k B _ _ _)]
    ring
  · exact ⟨coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i), by
      unfold dAct FB.actK; rw [coeff_map]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinearLogFormEvalZeroRightEqZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart dLin)

namespace GlobalTheory.GaugeShift

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ ev_sub ev_zeroFam logOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix (bilL lg)
open GlobalTheory.TwistCheck (ev_bilL cc_log bilL_mixed balanced_iff)

variable {S : Type} [CommRing S] {d : ℕ}

theorem cz2 {n : ℕ} {a b : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    CZ (![a, b] : Fin 2 → Pt S n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem coeff_mixed (g : PS S 2 d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) g =
      constantCoeff (pderiv (R := S) ((0 : Fin 2), i) (pderiv (R := S) ((1 : Fin 2), l) g)) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

variable [Algebra ℚ S]

theorem ev_zero_log {n : ℕ} (G : FGLaw S d) (i : Fin d) : ev (n := n) ![0] (logOf G i) = 0 := by
  have e : (![0] : Fin 1 → Pt S n d) = fun _ _ => 0 := by
    funext j c; fin_cases j; rfl
  rw [e, ev_zeroFam, cc_log, map_zero]

theorem cz0 {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt S n d) i) = 0 := by simp

theorem bilinearLogForm_eval_zero_left_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![0, pt S d 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 cz0 (FBMap.cz_pt _))]
  simp [ev_zero_log]

theorem bilinearLogForm_eval_zero_right_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![pt S d 0, 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) cz0)]
  simp [ev_zero_log]

theorem bilL_add_left (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (FBMap.cz_pt _)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2c.formal_log_add_first_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_add_right (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 1] (bilL G c) + ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (CIndFrFix2b.constantCoeff_add_second_third G)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2b.formal_log_add_last_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_swap (G : FGLaw S d) (c : Fin d → Fin d → S) (hs : ∀ i l, c i l = c l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (bilL G c) = bilL G c := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, bilL, lg, smul_eq_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs l i, mul_comm (ev _ _)]

theorem canon_sub_bilin : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ β : Matrix (Fin d) (Fin d) k, βᵀ = β → (∀ a : O, (dAct k B a)ᵀ * β = β * dAct k B (star a)) → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ bilinPart k h' = bilinPart k h - β := by
  intro R _ d O _ _ k _ _ _ B h hc β hs hb
  let G : FGLaw k d := FBMap.mapG (algebraMap R k) B.G
  let A : OAct O G := FBMap.mapA (algebraMap R k) B.A
  have hF : B.FK k = G.F := rfl
  have hA : ∀ a, B.actK k a = A.act a := fun _ => rfl
  have p {n : ℕ} (j : Fin n) := FBMap.cz_pt (R := k) (d := d) j
  have q (a : O) (j : Fin 2) := FBMap.cz_comp1 (A.act a) (A.const a) (pt k d j) (p j)
  refine ⟨h - bilL G β, ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩, ?_⟩
  · rw [ev_sub (cz2 cz0 (p _)), hc.ax0, bilinearLogForm_eval_zero_left_eq_zero G β, sub_zero]
  · rw [ev_sub (cz2 (p _) cz0), hc.ax1, bilinearLogForm_eval_zero_right_eq_zero G β, sub_zero]
  · rw [hc.ph1, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (p _)), bilL_add_left G β]
    congr 1; ring
  · rw [hc.ph2, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (p _) (CIndFrFix2b.constantCoeff_add_second_third G)), bilL_add_right G β]
    congr 1; ring
  · rw [hc.sy, ev_sub (cz2 (p _) (p _)), bilL_swap G β (fun i l => congrFun (congrFun hs l) i)]
    congr 1; ring
  · have hbal := (balanced_iff G A a (star a) β).1 (hb a)
    rw [hc.ad a, hA, hA, ev_sub (cz2 (q _ _) (p _)), ev_sub (cz2 (p _) (q _ _)), hbal]
    congr 1; ring
  · funext i l
    have := coeff_mixed (bilL G β) i l
    rw [bilL_mixed G β] at this
    simp only [bilinPart, map_sub, this, Matrix.sub_apply]

end GlobalTheory.GaugeShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegral
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigen_pair_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (σ : OE →+* R) (a0 : OE), IsUnit (σ a0 - σ (star a0)) → ∀ u u' : Fin d → R, (∀ a, (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (B.A.act a)).mulVec u = σ a • u) → (∀ a, (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (B.A.act a)).mulVec u' = σ a • u') → ∀ w : OE, dotProduct (fun i => algebraMap R k (u i)) ((ReciprocityTheory.ChartRestriction.G.TB.bilinPart k h).mulVec ((ReciprocityTheory.ChartRestriction.G.TB.dAct k B w).mulVec (fun i => algebraMap R k (u' i)))) ∈ (algebraMap R k).range := by
  intro R _ d OE _ _ k _ _ _ B h hc σ a0 ha u u' hu hu' w
  have key : ∀ v : Fin d → R, (∀ a, (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (B.A.act a)).mulVec v = σ a • v) → ∀ a,
      (ReciprocityTheory.ChartRestriction.G.TB.dAct k B a).mulVec (fun i => algebraMap R k (v i)) =
        algebraMap R k (σ a) • (fun i => algebraMap R k (v i)) := by
    intro v hv a
    funext i
    have e := congrArg (algebraMap R k) (congrFun (hv a) i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart,
      Matrix.of_apply] at e ⊢
    rw [← e]
    rfl
  have h3 := GlobalTheory.bilinPart_eigen_mem_range R d OE k B h hc a0 u u' _ _ (key u hu a0) (key u' hu' (star a0)) ha
  rw [key u' hu' w, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  exact Subring.mul_mem _ ⟨_, rfl⟩ h3

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardOrthogonalIdempotentsLeNcardPrimesOver
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem padicTensor_eq_mul_add (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime]
    (r : ℤ_[p] ⊗[ℤ] A) :
    ∃ (s : ℤ_[p] ⊗[ℤ] A) (x : A), r = (p : ℤ_[p] ⊗[ℤ] A) * s + (1 : ℤ_[p]) ⊗ₜ[ℤ] x := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    have h := PadicInt.zmodRepr_spec a
    obtain ⟨-, h⟩ := h
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c ⊗ₜ[ℤ] x, (a.zmodRepr : ℤ) • x, ?_⟩
    have ha : a = (p : ℕ) • c + (a.zmodRepr : ℤ) • (1 : ℤ_[p]) := by
      rw [nsmul_eq_mul, ← hc]; simp
    rw [← nsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, ← ha]
  | add a b ha hb =>
    obtain ⟨s, x, rfl⟩ := ha
    obtain ⟨s', x', rfl⟩ := hb
    exact ⟨s + s', x + x', by rw [TensorProduct.tmul_add]; ring⟩

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartLocalDepthLeOfValuedExtensionBound
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_addValuation_mul_log {C : Type} [Field C] (v : Valuation C NNReal) (r : ℝ) (hr : r < 0) :
    ∃ w : AddValuation C (WithTop ℝ), ∀ x, x ≠ 0 → w x = ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hpos : ∀ x : C, x ≠ 0 → (0 : ℝ) < (v x : ℝ) := fun x hx => by
    have : v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hmono : ∀ x y : C, x ≠ 0 → y ≠ 0 → v x ≤ v y →
      ((r * Real.log (v y : ℝ) : ℝ) : WithTop ℝ) ≤ ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
    intro x y hx hy h
    rw [WithTop.coe_le_coe]
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos x hx) (by exact_mod_cast h)) hr.le
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp) ?_ ?_, fun x hx => by simp [hx]⟩
  · intro x y
    by_cases hxy : x + y = 0
    · simp [hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg hxy]
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact min_le_of_left_le (hmono _ _ hxy hx h)
    · exact min_le_of_right_le (hmono _ _ hxy hy h)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [map_mul, NNReal.coe_mul, Real.log_mul (hpos x hx).ne' (hpos y hy).ne', mul_add, WithTop.coe_add]

theorem ValExt.exists_addValuation {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (e : ℕ) (he : 0 < e) :
    ∃ w : AddValuation X.C (WithTop ℝ),
      (∀ x : X.O, ((0 : ℝ) : WithTop ℝ) ≤ w (algebraMap X.O X.C x)) ∧
      (∀ x : T.Fr, nval T.V e x = (WithBot.some (w (X.ιF x)) : WithBot (WithTop ℝ))) ∧
      ∀ (x : X.C) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v x : ℝ) →
        w x ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : WithTop ℝ) := by
  have hp0 : (p : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpos : ∀ x : X.C, x ≠ 0 → (0 : ℝ) < (X.v x : ℝ) := fun x hx => by
    have : X.v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hle : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  have hne : X.v (p : X.C) ≠ 1 := fun h =>
    X.nonunit.out (X.ints.isUnit_of_one' (by rwa [map_natCast]))
  have hlt : (X.v (p : X.C) : ℝ) < 1 := by exact_mod_cast lt_of_le_of_ne hle hne
  have hlog : Real.log (X.v (p : X.C) : ℝ) < 0 := Real.log_neg (hpos _ hp0) hlt
  have hpT : (p : T.Fr) ≠ 0 := fun h => hp0 (by rw [← map_natCast X.ιF, h, map_zero])
  have he0 : (0 : ℝ) < (vV T.V (p : T.Fr) : ℝ) := by
    have h1 : 0 ≤ vV T.V (p : T.Fr) := by
      have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
      rwa [map_natCast] at this
    refine lt_of_le_of_ne (by exact_mod_cast h1) fun h => ?_
    have h2 := X.val _ hpT
    rw [← h, div_zero, Real.rpow_zero, map_natCast] at h2
    exact hlt.ne h2
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hc : 0 < (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) := div_pos he0 heR
  have hr : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) < 0 := div_neg_of_pos_of_neg hc hlog
  obtain ⟨w, hw⟩ := exists_addValuation_mul_log X.v _ hr
  refine ⟨w, fun x => ?_, fun x => ?_, fun x A hA => ?_⟩
  · by_cases hx : algebraMap X.O X.C x = 0
    · rw [hx, AddValuation.map_zero]; exact le_top
    rw [hw _ hx, WithTop.coe_le_coe]
    exact mul_nonneg_of_nonpos_of_nonpos hr.le
      (Real.log_nonpos (hpos _ hx).le (by exact_mod_cast X.ints.map_le_one x))
  · by_cases hx : x = 0
    · rw [hx, nval_zero, map_zero, AddValuation.map_zero]; rfl
    rw [nval_of_ne hx, hw _ ((map_ne_zero X.ιF).2 hx), X.val x hx, Real.log_rpow (hpos _ hp0)]
    have : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) *
        ((vV T.V x : ℝ) / (vV T.V (p : T.Fr) : ℝ) * Real.log (X.v (p : X.C) : ℝ)) = (vV T.V x : ℝ) / e := by
      have := hlog.ne
      field_simp
    rw [this]; rfl
  · have hA0 : 0 < (X.v (p : X.C) : ℝ) ^ A := Real.rpow_pos_of_pos (hpos _ hp0) A
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hA
      exact absurd (hA0.trans_le hA) (by simp)
    rw [hw _ hx, WithTop.coe_le_coe]
    have h1 := Real.log_le_log hA0 hA
    rw [Real.log_rpow (hpos _ hp0)] at h1
    refine (mul_le_mul_of_nonpos_left h1 hr.le).trans (le_of_eq ?_)
    have := hlog.ne
    field_simp

theorem nuLocC_le_of_value_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (B : FB X.O (chD Ch.ch) (𝓞 E)), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) → (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → ∀ (P : MvPolynomial (LtN Dw n) X.O), MvPolynomial.map (algebraMap X.O X.C) P ∈ HHa Dw.mult n X.C ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (f : PS X.O n (chD Ch.ch)) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v (nabValN B X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k (MvPowerSeries.map (algebraMap X.O X.C) f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i))) (MvPolynomial.map (algebraMap X.O X.C) P)) : ℝ) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X B hF hA e k n a he P hP f A hv
  letI := io.toAlgebra
  obtain ⟨w, hO, hT, hw⟩ := X.exists_addValuation e he
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hcomp : X.ιF.comp (algebraMap T.V T.Fr) = (algebraMap X.O X.C).comp X.ι := RingHom.ext X.comp
  have hmm : ∀ {m : ℕ} (g : PS T.V m (chD Ch.ch)),
      MvPowerSeries.map (algebraMap X.O X.C) (MvPowerSeries.map X.ι g) =
        MvPowerSeries.map X.ιF (MvPowerSeries.map (algebraMap T.V T.Fr) g) := fun g => by
    ext μ
    simp only [MvPowerSeries.coeff_map, X.comp]
  let R : Subring X.C :=
    { carrier := {x | ((0 : ℝ) : WithTop ℝ) ≤ w x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, WithTop.coe_zero] at *
        rw [w.map_mul]; exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => w.map_le_add ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [w.map_neg] }
  have key := GlobalTheory.nabValN_lower_bound_baseChange T X.C w X.ιF R (fun x => Iff.rfl)
    (fun x => by rw [X.comp]; exact hO _) _ (𝓞 E) Ch.ch.B (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B)
    (fun i => by
      rw [Ch.gen.1.1 i, ← hmm]
      change MvPowerSeries.map _ (B.G.F i) = _
      rw [hF])
    (fun b i => by
      rw [Ch.gen.1.2.1 b i, ← hmm]
      change MvPowerSeries.map _ (B.A.act b i) = _
      rw [hA])
    Ch.ch.h hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    (fun ℓ => ℓ.2.2) (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (nuLocC Ch e k a n)
    (by
      intro Q hQ g hg
      rw [← hT]
      unfold nuLocC
      exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl))))
    (MvPolynomial.map (algebraMap X.O X.C) P)
    ⟨hP, fun m => by rw [MvPolynomial.coeff_map]; exact hO _⟩
    (MvPowerSeries.map (algebraMap X.O X.C) f)
    (fun μ => by rw [MvPowerSeries.coeff_map]; exact hO _)
  refine key.trans (WithBot.coe_le_coe.2 (le_trans (le_of_eq (congrArg w ?_)) (hw _ A hv)))
  have hu : (fun (ℓ : LtN Dw n) j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j)) =
      fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i)) := by
    funext ℓ j
    rw [Ch.gen.1.2.2.2.2.2.2, X.comp]
  have h1 : (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).FK X.C = B.FK X.C := by
    funext i
    ext μ
    simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt]
  have h2 : ∀ b, (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).actK X.C b = B.actK X.C b := by
    intro b
    funext i
    ext μ
    simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt]
  rw [hu]
  unfold nabValN FB.hL
  rw [h1, h2]

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOnOfSmoothOnH
section
open Matrix Finset PI.UpqRep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.TensCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms (HRep IsSmoothMap IsSmoothMapInto IsSmoothMapFrom IsSmoothDecomp IsSignedDecomp IsFormRep
  tensSmooth tensAct tensForm pureT contr LieWord Mx Ix)

variable {k r : ℕ}

theorem isURepOn_of_isDS {R : BranchingSupport.Rep k r} {ε : Ix k r → Bool} {μ : Ix k r → ℝ} (h : R.IsDS ε μ) :
    IsURepOn (BranchingSupport.GG k r) R.σ := by
  obtain ⟨-, P, hP, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨⟨by simpa [hPP] using h1, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · have := hm _ (hmaps ha) _ (hmaps hb)
    have e2 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    simpa only [e2, e] using this
  · simpa only [e] using hn _ (hmaps hg) v
  · have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp h3.continuousOn hmaps
    simpa only [Function.comp_def, e] using this

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth

section Tensor

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : HRep k r} {Rs : κ → HRep k r}
  {io : ∀ I, (Rs I).H → ι → R.H} {pr : ∀ I, ι → R.H → (Rs I).H} {p : ∀ I, (ι → R.H) → (Rs I).H} {ep : κ → ℝ}


end Tensor

end GlobalTheory.TensCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMovesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_levelMap_by_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  first | exact @GlobalTheory.exists_conj_levelMap | exact GlobalTheory.exists_conj_levelMap | (intros; apply GlobalTheory.exists_conj_levelMap <;> assumption)
end

