module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CosetTheta

variable {D : D7}

theorem homL_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L₁) : M • A ∈ homL D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    rw [Matrix.smul_mulVec]
    exact hM _ (hA x hx)
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem YYl_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L₁) : M • A ∈ YYl D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M • A, homL_nsmul_mem M hM hA, smul_comm _ _ _⟩
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem La_nsmul_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L₁) : M • x ∈ La D (tor0 D cc δ) L L₂ := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w, hw, M • A, YYl_nsmul_mem M hM hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem skewLat_nsmul_le (𝔫 : Ideal (𝓞 D.host.E)) (h : D.host.conj • 𝔫 ≠ ⊥) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ skewLat D 𝔫 N, M • y ∈ stdL D N := by
  refine ⟨Ideal.absNorm (D.host.conj • 𝔫), Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h),
    fun y hy => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  rw [Pi.smul_apply]
  have hyi := hy i
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero
    (by simpa using h)] at hyi
  have hmem := hyi (algebraMap (𝓞 D.host.E) D.host.E (Ideal.absNorm (D.host.conj • 𝔫) : 𝓞 D.host.E))
    ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem _, rfl⟩)
  obtain ⟨x', -, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  rw [Submodule.mem_one]
  refine ⟨x', ?_⟩
  rw [hx', nsmul_eq_mul, mul_comm, map_natCast]

end GlobalTheory.BotPairSmall.CosetTheta

namespace GlobalTheory.BotPairSmall.CosetTheta

theorem iop_mem_TT {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {B : AddSubgroup (VC D a d)} {M : ℕ} (hM : 0 < M)
    (hB : ∀ x ∈ B, M • x ∈ La0 D (tor0 D ⊤ δ) a d) {e0 : VC D a d → ℂ} (heT : e0 ∈ TT D (tor0 D ⊤ δ) a d) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) B e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  set T := tor0 D ⊤ δ
  set A := La0 D T a d
  have h0 : (0 : VC D a d → ℂ) ∈ TT D T a d := by
    have := hlc.2.2.2 0 e0 heT
    rwa [zero_smul] at this
  by_cases hfin : Finite (B ⧸ A.addSubgroupOf B)
  · haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    have e : Iop D T A B e0 = ∑ q : B ⧸ A.addSubgroupOf B,
        ((((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) e0) := by
      funext z
      simp only [Iop, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Wd]
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
      field_simp
    rw [e]
    refine Finset.sum_induction _ (· ∈ TT D T a d) (fun F G hF hG => hlc.2.2.1 F hF G hG) h0 fun q _ => ?_
    exact hlc.2.2.2 _ _ (GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT hc hM (hB _ (Quotient.out q : B).2) heT)
  · have hi : (A.addSubgroupOf B).index = 0 :=
      AddSubgroup.index_eq_zero_iff_infinite.2 (not_finite_iff_infinite.1 hfin)
    have e : Iop D T A B e0 = 0 := by
      funext z
      simp [Iop, hi]
    rw [e]; exact h0

end GlobalTheory.BotPairSmall.CosetTheta

theorem GlobalTheory.BotPairSmall.cvec_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  have hI := GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
  unfold GlobalTheory.BotPairSmall.cvec
  exact hlc.2.2.2 _ _ (hlc.2.1 _ _ hI)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLiftStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_vertical_deformation_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : GlobalTheory.FlagTan.FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O), (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  first | exact @GlobalTheory.CompHS.der_fun_ver | exact GlobalTheory.CompHS.der_fun_ver | (intros; apply GlobalTheory.CompHS.der_fun_ver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

noncomputable section

theorem _root_.GlobalTheory.CompHS.det_tanLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho Q hz v hv zv hl i O hO g hzO hzv hJ
  obtain ⟨O₁, hzO₁, x, w, hw, hdx⟩ := _root_.GlobalTheory.TanVec.exists_tangent_matrix M.str (dimFlag Dw) z
  have hzi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => hO (hzO hs)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun s hs => ⟨hzO₁ hs, hzi hs⟩
  let x' : Fin (dimFlag Dw) → Γ(M.X, O₁ ⊓ M.K.bundle.U i) := fun a => resG M.X inf_le_left (x a)
  have hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO)
  have hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO')
  have hwO₁ : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O₁ := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO₁)
  have e1 : (Matrix.of fun a b => (evalPt (w b) (O₁ ⊓ M.K.bundle.U i) (hwO' b) (x' a)).snd) =
      Matrix.of fun a b => (evalPt (w b) O₁ (hwO₁ b) (x a)).snd := by
    ext a b
    simp only [Matrix.of_apply, x']
    rw [evalPt_res (w b) inf_le_left (hwO₁ b) (hwO' b)]
  have hjc := _root_.GlobalTheory.TanJac.det_mul_jacobian_comm M z i w hw O (O₁ ⊓ M.K.bundle.U i) hO inf_le_right g x' hzO hzO' hwO hwO'
  rw [e1] at hjc
  have hdg : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjc
    exact mul_ne_zero (hdx hwO₁) hJ hjc.symm
  have hQ := hKS K Q
  have hspan : ∀ c0 : Fin (dimFlag Dw), ∃ C : TIx Dw (psiSet H) → K, ∀ a,
      (evalPt (w c0) O (hwO c0) (g a)).snd = ∑ t, C t * (evalPt (zv t) O (hzv t) (g a)).snd := by
    intro c0
    obtain ⟨wf, hdef, hlw⟩ := _root_.GlobalTheory.CompHS.exists_isDef_lift_dualNumber M z ho hz (w c0) (hw c0)
    obtain ⟨Mx, hMx, -⟩ := hQ.existsUnique hdef.isTanX
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompHS.der_fun_hor M z ho hQ hz hv hl hdef hMx hlw
    refine ⟨Sum.elim Mx C, fun a => ?_⟩
    rw [hC O (g a) (hwO c0) hzv, Fintype.sum_sum_type]
    rfl
  choose C hC using hspan
  have hmat : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) *
        Matrix.of (fun b c0 => C c0 (tanOrd Dw b)) := by
    ext a c0
    rw [Matrix.mul_apply, Matrix.of_apply, hC c0 a, ← Equiv.sum_comp (tanOrd Dw)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.of_apply]
    ring
  intro h0
  apply hdg
  rw [hmat, Matrix.det_mul, h0, zero_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecRe
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped Matrix

theorem GlobalTheory.det_gram_lowerTriangular_coordVec_re : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  intro g m f hf a C hC
  classical
  set A : Matrix (Fin m) (Fin m) ℂ := Matrix.of C with hA
  set P : Matrix (Fin m) (Fin g) ℂ := Matrix.of fun l k => (Pi.single (f l) (1:ℂ) : Fin g → ℂ) k with hP
  have hX : ∀ i, (∑ l, C i l • Pi.single (f l) (1:ℂ)) = fun k => (A * P) i k := by
    intro i; ext k; simp [Matrix.mul_apply, hP, hA, Finset.sum_apply]
  have hPP : P * Pᴴ = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, hP, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    simp [Pi.single_apply, hf.eq_iff, eq_comm]
  have hH : ∀ u v : Fin g → ℂ, hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) u v = (a:ℂ) * (u ⬝ᵥ star v) := by
    intro u v
    rw [hermForm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hE : (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))) = ((Real.pi : ℂ) * a) • (A * Aᴴ)ᵀ := by
    ext i j
    rw [Matrix.of_apply, hX, hX, hH]
    have : (fun k => (A * P) j k) ⬝ᵥ star (fun k => (A * P) i k) = ((A * P) * (A * P)ᴴ) j i := by
      rw [Matrix.mul_apply]; simp only [dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
    rw [this, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]; ring
  have hlow : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hC i j hij
  rw [hE, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_lowerTriangular A hlow]
  have : (∏ i, A i i) * star (∏ i, A i i) = ((∏ i, ‖C i i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    simp [hA, Finset.prod_pow, norm_prod]
  rw [this, Fintype.card_fin]
  rw [show ((Real.pi : ℂ) * a) ^ m = (((Real.pi * a) ^ m : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul, Complex.ofReal_re]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLattice
section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.TwoBasesDet

theorem exists_leftInv {K : Type} [Field K] {n g : ℕ} (b : Fin n → Fin g → K)
    (hb : LinearIndependent K b) :
    ∃ A : Matrix (Fin n) (Fin g) K, ∀ i j, ∑ k, A i k * b j k = if i = j then 1 else 0 := by
  let lc : (Fin n → K) →ₗ[K] (Fin g → K) := Fintype.linearCombination K b
  have hinj : LinearMap.ker lc = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by simpa [lc, Fintype.linearCombination_apply] using hc))
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective lc hinj
  refine ⟨LinearMap.toMatrix' f, fun i j => ?_⟩
  have h1 : f (b j) = Pi.single j 1 := by
    have : lc (Pi.single j 1) = b j := by simp [lc, Fintype.linearCombination_apply_single]
    rw [← this, ← LinearMap.comp_apply, hf, LinearMap.id_apply]
  have h3 : (Matrix.mulVec (LinearMap.toMatrix' f) (b j)) = f (b j) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h2 := congrFun (h3.trans h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem vV_algebraMap_unit (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {u : V} (hu : IsUnit u) :
    vV V (algebraMap V K' u) = 0 := by
  unfold vV valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2]
  · simp
  · exact fun h => (HeightOneSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem valuation_div_le_one {K : Type} [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K))
    (c d : 𝓞 K) (hd : d ∉ 𝔓.asIdeal) : 𝔓.valuation K ((c : K) / d) ≤ 1 := by
  rw [map_div₀]
  have h1 : 𝔓.valuation K (d : K) = 1 := by
    rw [show (d : K) = algebraMap (𝓞 K) K d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hd
  rw [h1, div_one, show (c : K) = algebraMap (𝓞 K) K c from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem det_vV_add_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  intro K _ _ 𝔓 T iK hiK g n L b hb M u hu C hW hL
  set B : Fin n → Fin g → T.Fr := fun l k => iK (b l k) with hBdef
  obtain ⟨A, hA⟩ := exists_leftInv b hb.2.1

  have key : ∀ z : Fin n → T.Fr, ∀ i, z i = ∑ k, iK (A i k) * ∑ l, z l * B l k := by
    intro z i
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ k, iK (A i k) * (z l * B l k) = if i = l then z l else 0 := by
      intro l
      have h := congrArg iK (hA i l)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      simp only [map_mul] at h
      calc ∑ k, iK (A i k) * (z l * B l k) = z l * ∑ k, iK (A i k) * iK (b l k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hBdef]; ring
        _ = _ := by rw [h]; split_ifs <;> simp
    simp_rw [h]; simp
  have hinj : ∀ x y : Fin n → T.Fr, (∀ k, ∑ l, x l * B l k = ∑ l, y l * B l k) → x = y := by
    intro x y hxy
    funext i
    rw [key x i, key y i]
    exact Finset.sum_congr rfl fun k _ => by rw [hxy k]

  set P : Matrix (Fin n) (Fin n) T.Fr := C * M.map iK with hPdef
  have hWP : ∀ i k, (∑ j, C i j • fun k => iK (u j k)) k = ∑ l, P i l * B l k := by
    intro i k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu, map_sum, map_mul, hPdef, Matrix.mul_apply,
      Matrix.map_apply, hBdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  have hint : ∀ x ∈ L, ∃ p : Fin n → T.V, ∀ k, iK (x k) = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hb.2.2 x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hdx
    have hd0 : (d : K) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      rw [this]; exact Submodule.zero_mem _
    choose p hp using fun l => (hiK ((c l : K) / d)).2 (valuation_div_le_one 𝔓 (c l) d hd)
    refine ⟨p, fun k => ?_⟩
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at hk
    have hx' : x k = ∑ l, ((c l : K) / d) * b l k := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      rw [eq_div_iff hd0]
      convert hk.symm using 1
      · ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hp, hBdef, hx', map_sum, map_mul]
  have hspan : ∀ w ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K))),
      ∃ p : Fin n → T.V, ∀ k, w k = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact hint x hx
    | zero => exact ⟨0, fun k => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨p, hp⟩ := h
      obtain ⟨p', hp'⟩ := h'
      exact ⟨p + p', fun k => by simp [hp, hp', add_mul, Finset.sum_add_distrib]⟩
    | smul a w _ h =>
      obtain ⟨p, hp⟩ := h
      refine ⟨a • p, fun k => ?_⟩
      simp only [Pi.smul_apply, Algebra.smul_def, hp, Finset.mul_sum, smul_eq_mul, map_mul, mul_assoc]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Algebra.algebraMap_self, RingHom.id_apply]

  have hPint : ∀ i, ∃ p : Fin n → T.V, ∀ l, P i l = algebraMap T.V T.Fr (p l) := by
    intro i
    obtain ⟨p, hp⟩ := hspan _ (hW i)
    refine ⟨p, fun l => congrFun (hinj (P i) (fun l => algebraMap T.V T.Fr (p l)) fun k => ?_) l⟩
    rw [← hWP, hp]
  choose Pv hPv using hPint
  have hPeq : P = (Matrix.of Pv).map (algebraMap T.V T.Fr) := by
    ext i l; simp [hPv i l]

  have hQint : ∀ l, ∃ q : Fin n → T.V, ∀ m, ∑ i, algebraMap T.V T.Fr (q i) * P i m = if l = m then 1 else 0 := by
    intro l
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hL (b l) (hb.1 l))
    refine ⟨q, fun m => congrFun (hinj (fun m => ∑ i, algebraMap T.V T.Fr (q i) * P i m)
      (fun m => if l = m then 1 else 0) fun k => ?_) m⟩
    have hk : ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k = iK (b l k) := by
      rw [← congrFun hq k, Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ m, algebraMap T.V T.Fr (q i) * P i m * B m k
        = ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hWP, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = B l k := hk
  choose Qv hQv using hQint
  have hQP : Matrix.of Qv * Matrix.of Pv = 1 := by
    apply (Matrix.map_injective (IsFractionRing.injective T.V T.Fr))
    show (Matrix.of Qv * Matrix.of Pv).map (algebraMap T.V T.Fr) = (1 : Matrix (Fin n) (Fin n) T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, ← hPeq, Matrix.map_one _ (map_zero _) (map_one _)]
    ext l m
    simpa [Matrix.mul_apply, Matrix.one_apply] using hQv l m
  have hunit : IsUnit (Matrix.of Pv).det := by
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact ⟨⟨_, _, by rw [mul_comm]; exact this, this⟩, rfl⟩
  have hdetP : P.det = algebraMap T.V T.Fr (Matrix.of Pv).det := by
    rw [hPeq, RingHom.map_det]; rfl
  have hdetP' : P.det = C.det * iK M.det := by
    rw [hPdef, Matrix.det_mul, RingHom.map_det]; rfl
  have hP0 : P.det ≠ 0 := by
    rw [hdetP]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hunit.ne_zero
  have hC0 : C.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, zero_mul])
  have hM0 : iK M.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, mul_zero])
  refine ⟨fun h => hM0 (by rw [h, map_zero]), hC0, ?_⟩
  rw [← vV_mul hC0 hM0, ← hdetP', hdetP]
  exact vV_algebraMap_unit T.V hunit

end GlobalTheory.TwoBasesDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertLagChar

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

def diagW (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x) ∂μ

def lagInt (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) {N : ℕ} (ν : @Measure (Fin N → Fv F v) (borel _))
    (j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v)) (Φ : (κ ⊕ κ → Fv F v) → ℂ) : ℂ :=
  ∫ y, diagW ψ μ Φ (j y) ∂ν


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct Matrix in
variable {F : Type} [Field F] [NumberField F] {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {κ : Type} [Fintype κ] in
theorem _root_.GlobalTheory.InertLagChar.diagW_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ)
    (μ : @Measure (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (borel _)) (Φ : (κ ⊕ κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) :
    _root_.GlobalTheory.InertLagChar.diagW ψ μ Φ 0 = ∫ x, Φ (Sum.elim x x) ∂μ := by
  unfold _root_.GlobalTheory.InertLagChar.diagW _root_.GlobalTheory.WeilM.schr
  simp

end GlobalTheory.InertLagChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewLStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ, ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧ x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' := by
  first | exact @GlobalTheory.SkewMove.exists_skew_move | exact GlobalTheory.SkewMove.exists_skew_move | (intros; apply GlobalTheory.SkewMove.exists_skew_move <;> assumption)
end

