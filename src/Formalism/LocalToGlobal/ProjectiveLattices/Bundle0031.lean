module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def ProdInLat (ka : WeightFamilies.Wt D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (n : ℕ) : Prop :=
  ∀ s : Fin n → Fin (N + 1), ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧ (F : Tc.R j) = ∏ k, wR (s k)

def SupPTGe (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evC_prod (h : GenFrEx Xo c) (hgt : GenFromTest Xo c h) (Z : Comp Xo c) {n : ℕ} (f : Fin n → Rul Xo c) :
    evC h Z (∏ k, f k) = ∏ k, evC h Z (f k) := by
  let φ : Rul Xo c →* Om Z :=
    { toFun := evC h Z
      map_one' := evalAt_one _ _ _ (hgt Z)
      map_mul' := fun a b => evalAt_mul _ _ a b _ }
  exact map_prod φ f Finset.univ

theorem evC_add (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := evalAt_add _ _ f g _

theorem evC_zero (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := evalAt_zero _ _ _

theorem evC_smul (h : GenFrEx Xo c) (Z : Comp Xo c) (a : c.F) (f : Rul Xo c) :
    evC h Z (a • f) = algebraMap c.F (Om Z) a * evC h Z f := evalAt_smul _ _ a f _

theorem smul_single_AC (Z : Comp Xo c) (a : 𝓞 c.F) (G : WTZ E) (e : Om Z) :
    a • (AddMonoidAlgebra.single G e : AC Z) = AddMonoidAlgebra.single G (algebraMap c.F (Om Z) (a : c.F) * e) := by
  first
  | rw [AddMonoidAlgebra.smul_single]
  | erw [AddMonoidAlgebra.smul_single]
  rw [Algebra.smul_def]
  congr 1

theorem valC_smul (h : GenFrEx Xo c) (a : 𝓞 c.F) (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h u n ((a : c.F) • f) Z = a • valC h u n f Z := by
  simp only [valC, evC_smul]
  exact (smul_single_AC Z a _ _).symm

end Ev

set_option maxHeartbeats 1000000 in
theorem coe_smul_cusp {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (a : 𝓞 Tc.Q.c.F) (F : (recB hL).Cusp j ka) :
    ((a • F : (recB hL).Cusp j ka) : Tc.R j) = ((a : Tc.Q.c.F) • (F : Tc.R j)) := by
  rfl

def LamConst (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j) (P : ℝ) (n : ℕ) (s : ℝ) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * s

theorem htLAM_of [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j)
    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hlam : LAMwAt large₂ (recB hL) j ka C A)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsup : SupPTGe hL j h fn yP ka)
    (hc : LamConst j large₂ C A ka PP0' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM := by
  classical
  intro Z g hg hgZ
  obtain ⟨F, hFM, rfl⟩ : ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧
      g = valC h (wtA ka) ka.n (F : Tc.R j) := by
    clear hgZ
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨F, hFM, hF⟩ := hprod s
      refine ⟨F, hFM, ?_⟩
      funext Z
      rw [hF]
      beta_reduce
      rw [Finset.prod_apply]
      change ∏ k, AddMonoidAlgebra.single (wtZ uL.1 uL.2) (evC h Z (wR (s k))) =
        AddMonoidAlgebra.single (wtZ (wtA ka) ka.n) (evC h Z (∏ k, wR (s k)))
      rw [AddMonoidAlgebra.prod_single, hka, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        evC_prod h hgt Z]
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      funext Z
      simp [valC, evC_zero]
    | add x y _ _ hx hy =>
      obtain ⟨F, hFM, rfl⟩ := hx
      obtain ⟨G, hGM, rfl⟩ := hy
      refine ⟨F + G, Submodule.add_mem _ hFM hGM, ?_⟩
      funext Z
      simp [valC, evC_add, AddMonoidAlgebra.single_add]
    | smul a x _ hx =>
      obtain ⟨F, hFM, rfl⟩ := hx
      refine ⟨a • F, Submodule.smul_mem _ a hFM, ?_⟩
      funext Z
      show a • valC h (wtA ka) ka.n (F : Tc.R j) Z = valC h (wtA ka) ka.n ((a • F : (recB hL).Cusp j ka) : Tc.R j) Z
      rw [coe_smul_cusp hL j ka a F]
      exact (valC_smul h a _ _ _ Z).symm
  have hev : evC h Z (F : Tc.R j) ≠ 0 := fun h0 => hgZ (by simp [valC, h0])
  obtain ⟨F', hF'M, hF'0, hle⟩ := hsup Z F hFM hev
  have hl := hlam F' hF'M hF'0
  refine (neg_le_neg hc).trans (hl.trans ?_)
  unfold WeightFamilies.meanLogSup meanK
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
  have hpos : 0 < (recB hL).supN j ka sg F' :=
    lt_of_le_of_ne ((recB hL).supN_nonneg _ _ _ _)
      (fun h0 => hF'0 (((recB hL).supN_eq_zero _ _ _ _).1 h0.symm))
  refine Real.log_le_log hpos ((hle sg).trans (le_of_eq ?_))
  change _ = ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (_ • wtZ uL.1 uL.2) _ P
  rw [hka]

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveFr
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

lemma weight_add_shift {e k : ℕ} {w' : WeightFamilies.Wt D j} (hw : wadd wF w' = wsmul e wL) :
    wadd (addL wF wL k) w' = addL (wt0 D j) wL (k + e) := by
  have h1 := congrArg WeightFamilies.Wt.aP hw
  have h2 := congrArg WeightFamilies.Wt.aM hw
  have h3 := congrArg WeightFamilies.Wt.n hw
  simp only [wadd, wsmul] at h1 h2 h3
  unfold addL wadd wsmul wt0 wscalar
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i
    have := congrFun (congrFun h1 τ) i
    linarith
  · funext τ i
    have := congrFun (congrFun h2 τ) i
    linarith
  · linarith

variable (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF)

lemma product_cusp_forms_mem_weight {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ) ∈
      Vw (xplus X E hM) la G.N (addL (wt0 D j) wL e) := by
  have := mul_mem_Vw (xplus X E hM) la G.N (emb_mem_Vw (xplus X E hM) la G.N wF g0)
    (emb_mem_Vw (xplus X E hM) la G.N w' θ)
  have hw' : addL (wt0 D j) wL e = wadd wF w' := by rw [hw]; exact zero_weight_add _
  rw [hw']
  exact this

def u0 {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w e (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ)),
    Algebra.subset_adjoin (frac_mem_Hfr _ _ _ (product_cusp_forms_mem_weight G la g0 θ hw))⟩

lemma top_span_mem {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    (⟨z, Algebra.mem_top⟩ : ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ :
          ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)))) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Ideal.subset_span ⟨i, rfl⟩
  | zero => exact Ideal.zero_mem _
  | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
  | smul a b _ hb =>
    have : (⟨a • b, Algebra.mem_top⟩ :
        ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) =
        ⟨a, Algebra.mem_top⟩ * ⟨b, Algebra.mem_top⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hb

theorem curveModel_of_fr
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w))
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hu0 : IsUnit (toOsK (xplus X E hM) la G.w (u0 G la g0 θ hw)))
    (hinj : ∀ b : ↥(Frac0 (xplus X E hM) la G.w),
      (b : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 →
        b = 0) :
    Nonempty (CurveModel G la g0) := by
  obtain ⟨v, hv⟩ := hu0
  obtain ⟨c, hc⟩ := toOsK_surjective (xplus X E hM) la G.w (↑v⁻¹)
  set A : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w) := ⊤ with hA
  have hJh : c * u0 G la g0 θ hw - 1 ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_mul, map_one, hc, ← hv, Units.inv_mul, sub_self]

  have hspan : Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ : ↥A)) =
      (Jid (xplus X E hM) la G.w).map (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N)).symm := by
    rw [Jid, Ideal.map_span, ← Set.range_comp]
    rfl
  let qe := Ideal.quotientEquivAlg (R₁ := Kp (xplus X E hM) la G.N) (Jid (xplus X E hM) la G.w) _
    (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N) (A := ↥(Frac0 (xplus X E hM) la G.w))).symm hspan
  have hfd' : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) :=
    hfd
  have hred' : IsReduced (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) := hred
  refine ⟨{ A' := A
            sA := fun _ => Algebra.mem_top
            h := ⟨c * u0 G la g0 θ hw, Algebra.mem_top⟩
            h_one := ?_
            fin := ?_
            red := ?_
            loc := fun b => ⟨0, ⟨b, Algebra.mem_top⟩, by rw [pow_zero, one_mul]⟩
            base_form_injective := ?_
            base_form_local := ?_ }⟩
  · have := top_span_mem G la hJh
    convert this using 1
  · exact LinearEquiv.finiteDimensional qe.toLinearEquiv
  · exact isReduced_of_injective qe.symm.toRingEquiv.toRingHom qe.symm.injective
  · intro a₁ a₂ h12
    apply Subtype.ext
    have h0 : (((a₁ : ↥(Frac0 (xplus X E hM) la G.w)) - (a₂ : ↥(Frac0 (xplus X E hM) la G.w)) :
        ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
          (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 := by
      rw [Subalgebra.coe_sub, sub_mul, sub_eq_zero]
      exact h12
    exact sub_eq_zero.1 (hinj _ h0)
  · intro x
    obtain ⟨k, g, hg, hx⟩ := (mem_Hfr (xplus X E hM) la G.w).1 ((mem_HK (xplus X E hM) la G.w).1 x.2)
    have hgθ : g * emb (xplus X E hM) la G.N (X.inc w' θ) ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL (k + e)) := by
      rw [← weight_add_shift (k := k) hw]
      exact mul_mem_Vw _ _ _ hg (emb_mem_Vw _ _ _ w' θ)
    let b : ↥(Frac0 (xplus X E hM) la G.w) :=
      ⟨frac (xplus X E hM) la G.w (k + e) (g * emb (xplus X E hM) la G.N (X.inc w' θ)),
        Algebra.subset_adjoin (frac_mem_Hfr _ _ _ hgθ)⟩
    refine ⟨1, ⟨c * b, Algebra.mem_top⟩, ?_⟩
    show ((c * u0 G la g0 θ hw : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ 1 *
        (x : Lw (xplus X E hM) la G.w) =
      ((c * b : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0))
    rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_mul, hx, ← frac_zero, mul_assoc, mul_assoc]
    congr 1
    show frac _ _ _ e _ * frac _ _ _ k g = frac _ _ _ (k + e) _ * frac _ _ _ 0 _
    rw [frac_mul, frac_mul, add_zero, add_comm e k]
    congr 1
    ring

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

namespace CurveModel

variable (M : CurveModel G la g0)

def JA : Ideal ↥M.A' :=
  Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => (⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ : ↥M.A'))

theorem map_JA : M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) = Jid (xplus X E hM) la G.w := by
  rw [JA, Ideal.map_span, ← Set.range_comp]
  rfl

theorem bij_quot : Function.Bijective (Ideal.quotientMap (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
    (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) Ideal.le_comap_map) := by
  refine ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc M.h M.JA M.h_one (fun b => ?_) Subtype.val_injective
  obtain ⟨m, a, ha⟩ := M.loc b
  exact ⟨m, a, by rw [map_pow]; exact ha⟩

def quotEquiv : (↥M.A' ⧸ M.JA) ≃ₐ[Kp (xplus X E hM) la G.N] OsK (xplus X E hM) la G.w :=
  AlgEquiv.ofBijective
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).toAlgHom.comp
      (Ideal.quotientMapₐ (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
        (IsScalarTower.toAlgHom (Kp (xplus X E hM) la G.N) ↥M.A' ↥(Frac0 (xplus X E hM) la G.w))
        Ideal.le_comap_map))
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).bijective.comp M.bij_quot)

theorem toOsK_h : toOsK (xplus X E hM) la G.w (M.h : ↥(Frac0 (xplus X E hM) la G.w)) = 1 := by
  have h1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) - 1) ∈ Jid (xplus X E hM) la G.w := by
    rw [← M.map_JA]
    let f := algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)
    change f M.h - 1 ∈ Ideal.map f M.JA
    rw [← f.map_one, ← f.map_sub]
    exact Ideal.mem_map_of_mem f M.h_one
  have h2 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 h1
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2

theorem fractionToIntegralSection_smul_eq (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) :
    toA0K (xplus X E hM) la G.w wF (b • n) = toOsK (xplus X E hM) la G.w b • toA0K (xplus X E hM) la G.w wF n := by
  rw [map_smul]
  exact (algebraMap_smul (OsK (xplus X E hM) la G.w) b _).symm

theorem coe_smul_base_cusp_form (b : ↥(Frac0 (xplus X E hM) la G.w)) :
    ((b • toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
      (b : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) := by
  rw [Submodule.coe_smul, coe_toHK0]
  rfl

theorem coe_smul' (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) : ((b • n : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) = (b : Lw (xplus X E hM) la G.w) * (n : Lw (xplus X E hM) la G.w) := by
  rw [Submodule.coe_smul]
  rfl


set_option maxHeartbeats 1000000 in
theorem JH_mem (z : ↥(HK (xplus X E hM) la G.w wF)) (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w wF))) :
    ∃ m : ℕ, ∃ a' ∈ M.JA, ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • z) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) •
      toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have key : ∀ r ∈ Jid (xplus X E hM) la G.w, ∀ n : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a' ∈ M.JA,
      ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • (r • n)) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro n
      obtain ⟨m, a, ha⟩ := M.base_form_local n
      refine ⟨m, ⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ * a, Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
      apply Subtype.ext
      rw [coe_smul', coe_smul', he0, coe_smul_base_cusp_form]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_left_comm, ha]
      ring
    | zero => intro n; exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx n
      obtain ⟨m', a', ha', he'⟩ := hy n
      refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
        (Ideal.mul_mem_left _ _ ha'), ?_⟩
      have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (x • n) = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
      have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (y • n) = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
      rw [add_smul, smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]
    | smul c x _ hx =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx ((c • n : ↥(HK (xplus X E hM) la G.w wF)))
      refine ⟨m, a, ha, ?_⟩
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact he
  refine Submodule.smul_induction_on hz (fun r hr n _ => key r hr n) ?_
  rintro x y ⟨m, a, ha, he⟩ ⟨m', a', ha', he'⟩
  refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
    (Ideal.mul_mem_left _ _ ha'), ?_⟩
  have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • x = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
  have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • y = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
  rw [smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]

theorem isGen (M : CurveModel G la g0) : IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have hres : resF G la g0 = toA0K (xplus X E hM) la G.w wF e0 := rfl
  unfold IsGen
  rw [hres]
  constructor
  · intro u v huv
    rw [← sub_eq_zero]
    have hw : (u - v) • toA0K (xplus X E hM) la G.w wF e0 = 0 := by rw [sub_smul]; exact sub_eq_zero.2 huv
    obtain ⟨b, hb⟩ := toOsK_surjective (xplus X E hM) la G.w (u - v)
    obtain ⟨m, a, ha⟩ := M.loc b
    have hta : toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) = u - v := by
      rw [← ha, map_mul, map_pow, M.toOsK_h, one_pow, one_mul, hb]
    rw [← hta, ← fractionToIntegralSection_smul_eq] at hw
    obtain ⟨m', a', ha', he'⟩ := M.JH_mem _ ((reduction_eq_zero_iff_mem_ideal_smul (xplus X E hM) la G.w wF _).1 hw)
    have hinj : M.h ^ m' * a = a' := by
      apply M.base_form_injective
      have := congrArg (fun n : ↥(HK (xplus X E hM) la G.w wF) => (n : Lw (xplus X E hM) la G.w)) he'
      rw [he0] at this
      simp only [coe_smul', coe_toHK0, SubmonoidClass.coe_pow] at this
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_assoc]
      exact this
    have hJ : ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
      rw [hinj, ← M.map_JA]; exact Ideal.mem_map_of_mem _ ha'
    have h0 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 hJ
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, M.toOsK_h, one_pow, one_mul] at h0
    rw [← hta]
    exact h0
  · intro n
    obtain ⟨x, rfl⟩ := reductionMap_surjective (xplus X E hM) la G.w wF n
    obtain ⟨m, a, ha⟩ := M.base_form_local x
    refine ⟨toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)), ?_⟩
    have hx : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x) = ((a : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
      apply Subtype.ext
      rw [coe_smul', he0, coe_smul_base_cusp_form]
      simpa only [Subalgebra.coe_pow, SubmonoidClass.coe_pow] using ha
    show toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) • toA0K (xplus X E hM) la G.w wF e0 = toA0K (xplus X E hM) la G.w wF x
    rw [← fractionToIntegralSection_smul_eq, ← hx, fractionToIntegralSection_smul_eq, map_pow, M.toOsK_h, one_pow, one_smul]

end CurveModel

theorem inCurveSec (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : InCurveSecSt (E := E) G la := by
  intro y hs g0 hMod _
  obtain ⟨M⟩ := hMod
  refine ⟨?_, ?_, M.isGen⟩
  · haveI : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥M.A' ⧸ M.JA) := M.fin
    exact LinearEquiv.finiteDimensional M.quotEquiv.toLinearEquiv
  · haveI : IsReduced (↥M.A' ⧸ M.JA) := M.red
    exact isReduced_of_injective M.quotEquiv.symm.toRingHom M.quotEquiv.symm.injective

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftModelSt
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def LiftModelSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    Nonempty (LiftModel G la y (fun ζ => (hw ζ).toSecPt) g0 T)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)

end Formalism.L2.Pj
end
end

