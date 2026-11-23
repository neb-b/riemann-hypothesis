module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.ContDiffAtOfDiff

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frMap (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

end Gen

section Rec

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (hL : LawsP T) (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

def SupRLeRec (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ) (i : ℕ)
    (η : (recB hL.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA (wEt D j i)) (wEt D j i).n η.1 ≤ (recB hL.toLawsCore).supN j _ sg η

end Rec

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CBaseYPDef
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖


def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'



variable (Xo c) in
def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def BIRSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (a : Om Z), ∃ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (wsmul k wL))
    (p : MvPolynomial (Fin G.N) T.Q.c.F), p.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p =
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j)

def CompSplitSt : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    ∃ g' : (recB h.toLawsCore).Cusp j w,
      evC hG Z ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) ∧
      ∀ Z', Z' ≠ Z → evC hG Z' ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = 0

def GenValInjSt : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) = 0) → g = 0

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveUnit
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem curveUnit_isUnit_emb (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (F : X.Forms) (hF : gF F ≠ 0) :
    IsUnit (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (emb X la N F))) := by
  rw [lwZ_alg, rzMap_emb]
  have h1 : IsUnit ((1 : X.Kl la) ⊗ₜ[B.KO] gF F) := by
    simpa using (IsUnit.mk0 _ hF).map
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω)
  have h2 : IsUnit ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] gF F)) := by
    simpa using h1.map (Algebra.TensorProduct.includeRight :
      X.Kl la ⊗[B.KO] Ω →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω))
  exact h2.map _

theorem curveUnit_isUnit_w0inv (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) :
    IsUnit (lwZ X la N Ω gF w (w0inv X la w)) := by
  refine IsUnit.of_mul_eq_one (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
  rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem nonzero_divisor_cusp_form
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (F : X.Forms) (hF : ∀ Z, gF Z F ≠ 0) (b : ↥(Frac0 X la w))
    (hb : (b : Lw X la w) * algebraMap (Rp X la N) (Lw X la w) (emb X la N F) = 0) : b = 0 := by
  refine hInj b fun Z => ?_
  rw [phiZ_apply]
  have h1 := congrArg (lwZ X la N (Ω Z) (gF Z) w) hb
  rw [map_mul, map_zero] at h1
  exact (curveUnit_isUnit_emb X la N w (Ω Z) (gF Z) F (hF Z)).mul_left_eq_zero.mp h1

theorem curveUnit_unit_gen [Fintype ι]
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q → ∀ Z Z',
      RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ Q → Z = Z')
    (hloc : ∀ Z (r : RZs X la N (Ω Z) (gF Z) w), ∃ a p : ↥(Frac0 X la w),
      (∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q →
        RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → p ∉ Q) ∧
      phiZ X la N (Ω Z) (gF Z) w p * r = phiZ X la N (Ω Z) (gF Z) w a)
    (hfd : FiniteDimensional (Kp X la N) (OsK X la w))
    (u : ↥(Frac0 X la w)) (hu : ∀ Z, IsUnit (phiZ X la N (Ω Z) (gF Z) w u)) :
    IsUnit (toOsK X la w u) := by
  classical
  have hmem : ∀ b : ↥(Frac0 X la w), b * u ∈ Jid X la w → b ∈ Jid X la w := by
    intro b hb
    refine LocalUnitReduction.mem_of_forall_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) hInj hone fun Z => ?_
    refine LocalUnitReduction.mem_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) (hloc Z) ?_
    obtain ⟨v, hv⟩ := hu Z
    have h1 : phiZ X la N (Ω Z) (gF Z) w (b * u) ∈
        Ideal.map (phiZ X la N (Ω Z) (gF Z) w) (Jid X la w) := Ideal.mem_map_of_mem _ hb
    rw [map_mul, ← hv] at h1
    have h2 := Ideal.mul_mem_right (↑v⁻¹ : RZs X la N (Ω Z) (gF Z) w) _ h1
    rwa [mul_assoc, Units.mul_inv, mul_one] at h2
  have hinj : Function.Injective (LinearMap.mulRight (Kp X la N) (toOsK X la w u)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨b, rfl⟩ := toOsK_surjective X la w y
    rw [LinearMap.mulRight_apply, ← map_mul, toOsK_eq_zero_iff] at hy
    rw [toOsK_eq_zero_iff]
    exact hmem b hy
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  rw [LinearMap.mulRight_apply] at hy
  exact IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)

end Gen

section U0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
  {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem phi_unit_product_cusp_forms (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (g0 : B.Cusp j wF) {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (hg : gF (X.inc wF g0) ≠ 0) (hθ : gF (X.inc w' θ) ≠ 0) :
    IsUnit (phiZ (xplus X E hM) la G.N Ω gF G.w (u0 G la g0 θ hw)) := by
  rw [phiZ_apply]
  show IsUnit (lwZ (xplus X E hM) la G.N Ω gF G.w (frac (xplus X E hM) la G.w e
    (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ))))
  simp only [frac_apply, map_mul, map_pow]
  exact ((curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hg).mul
    (curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hθ)).mul ((curveUnit_isUnit_w0inv _ la G.N G.w Ω gF).pow e)

end U0

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveUnit_gF_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPJ h j hj).inc u F) = evC hG Z (F : T.R j) :=
  formsEvR_single j hG hT Z _ _

variable {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
  (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF)

theorem nonzero_divisor_cusp_form_record
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0) :
    ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
      (b : Lw (recPlus h j hj) la G.w) *
        algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
          (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 →
        b = 0 :=
  fun b hb => nonzero_divisor_cusp_form (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj _ (fun Z h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0)) b hb

theorem unit_ideal_cusp_form_record [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
      ∀ Z Z' : Comp (T.Q.Xo j) T.Q.c,
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q →
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z') (formsEvR j hG hT Z') G.w) ≤ Q → Z = Z')
    (hloc : ∀ (Z : Comp (T.Q.Xo j) T.Q.c)
      (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
      ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
        (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
          RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q → p ∉ Q) ∧
        phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w p * r =
          phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w a)
    (hfd : FiniteDimensional (Kp (recPlus h j hj) la G.N) (OsK (recPlus h j hj) la G.w))
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0)
    (hθ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) :
    IsUnit (toOsK (recPlus h j hj) la G.w (u0 G la g0 θ hw)) :=
  curveUnit_unit_gen (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj hone hloc hfd _ fun Z => phi_unit_product_cusp_forms G la g0 θ hw (Om Z) (formsEvR j hG hT Z)
      (fun h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0))
      (fun h0 => hθ Z ((curveUnit_gF_inc h j hj hG hT Z w' θ).symm.trans h0))

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open Classical in
def bdet (X : Data E r) (b : Frame X.Ψ r) : ℂ :=
  ∏ τ : X.Ψ, ∏ j : Fin r, b τ j j ^ (if X.p0 ≤ (j : ℕ) then (1 : ℤ) else -1)

end Per

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (M : ModelsOf F r)

abbrev PerAt : Prop :=
  ∀ k, ∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (pmOf e M k x)

def lieOf (hP : PerAt e F M) (k : Fin F.n) (x : (M.X k).dom) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left :=
  (derivAt_exists (hP k x.1 x.2) (eb e τ i)).choose

def LieEig : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ τ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u i P) v → IsEigAt c τ v →
      ∃ a : Fin (Dw.mult τ) → ℂ, IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, a j • eb e τ j) v

abbrev GenSec : Type :=
  ∀ k (x : (M.X k).dom), LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))

abbrev IsGenSec (s : GenSec e F M) : Prop :=
  ∀ k (x : (M.X k).dom) (s' : LB.Sec (PPx (S := CAt σ) (F.u k (pmOf e M k x.1)))),
    ∃! a : CAt σ, ∀ i, s'.f i = scal (S := CAt σ) (F.u k (pmOf e M k x.1)) a i * (s k x).f i


end Fam

section Red

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}
  (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) (s : GenSec e F M)
  (hs : IsGenSec e F M s)

end Red

section Row

variable {D : D7}

end Row

section Gam

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_map_ne (τ : E →+* ℂ) (γ : GL (Fin r) E) : ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 (Matrix.isUnits_det_units γ).ne_zero

end Gam

section GamL

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}


end GamL

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsBlockProd
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

structure LetterBlock where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw n}

def LetterBlock.poly (K : Type) [CommRing K] (B : LetterBlock Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P₁ : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → LetterBlock Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P₁ = ∏ j, (bs j).poly K

end GlobalTheory

section HeadContinuityAtZero

variable {D : D7} (T : Top D) (j : ℕ)


open Classical in
def FrameTie (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th : ℝ) {n : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  IsBlockProd P₁ → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom →
    ∃ x' : ((T.U j σ).X k).dom, (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x'.1 τ' i'‖ = 1) ∧
      (∀ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 = recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x) ∧
      ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x'.1 = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x ∧
      ∃ (W : UnfAt (T.U j σ) k x') (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x'.1)
        (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        TorusPins W Wu A L ∧
        A.T.l2 1 A.s = 1 ∧
        ∃ ρ : (Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) → ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim,
          (∀ y, L (Pi.single (W.e.symm y) 1) = EuclideanSpace.single (ρ y) 1) ∧
          ∃ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n A.T.dim),
            ReciprocityTheory.ChartRestriction.G.I2.Disj bs ∧
            MvPolynomial.rename (fun l : LtN (T.Q.Dw j) n =>
              ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter n A.T.dim)) (MvPolynomial.map ((starRingEnd ℂ).comp σ) P₁) =
              ReciprocityTheory.ChartRestriction.G.I2.P1 bs ∧
            ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree ∧
            ∃ K, ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T (T.Q.l.M ^ 2) n ((T.Q.l.M : ℂ) • LinearMap.id) K

end HeadContinuityAtZero

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Equiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ ((G.map τ) *ᵥ star w) := by
  simp [hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem star_mulVec' (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    star (A *ᵥ w) = (A.map (starRingEnd ℂ)) *ᵥ star w := by
  funext a
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

end Equiv

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Fam

end Formalism.L2.Pj
end
end

