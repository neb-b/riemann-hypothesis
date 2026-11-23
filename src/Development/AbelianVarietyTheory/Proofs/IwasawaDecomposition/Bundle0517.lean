module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0499
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section Unif

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_unif_of_frame {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s)
    {θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ u : HolUnif Φ.key.P.A Φ.key.P.L g, u.Λ = P.range.toIntSubmodule ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ ∀ z, (u.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := LB.isLB_pull Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  refine ⟨carry u₁ hM hL hw', rfl, ?_, ?_, hex⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))

end Unif

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (a : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas a) = (fun i => (a (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (a (Sum.inr i) : ℂ)) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : a = ∑ s, a s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [h1 (fun i => a (Sum.inl i)), h1 (fun i => a (Sum.inr i))]
  conv_lhs => rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add (f := _), Matrix.mulVec_add, Matrix.mulVec_sum,
    Matrix.mulVec_smul, (hn _).1, (hn _).2]

theorem normalAt_of_coord (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {La : Type} [AddCommGroup La]
    (P : La →+ (Fin x.P.g → ℂ)) (bas : (Fin x.P.g ⊕ Fin x.P.g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₁ c₂ : Fin x.P.g → ℂ) (a : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => a * thetaChar τ c₁ c₂ (h *ᵥ z)) (hD : ∀ i, u.IsDiff (Pi.single i 1) (x.v i)) :
    KeyPow.NormalAt x τ ((2 * Real.pi * Complex.I : ℂ) • hᵀ) c₁ c₂ a := by
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  refine ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • hᵀ) i = h *ᵥ Pi.single i 1 := by
      funext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hD i

theorem value_at_thetaPt : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  intro κ hH hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb a y Φ ha ⟨hx, hder, hsec⟩ ⟨ht, hg, hv⟩
  subst hg
  have hP := T.isPer _ hb
  obtain ⟨hu, hsymm, hpos, hn⟩ := T.norm b hb
  have hj : Differentiable ℂ (fun z : Fin Φ.T.g → ℂ => (b, z)) := by fun_prop
  obtain ⟨u, hΛ, hR, hF, hex⟩ := exists_unif_of_frame F k hP hx Φ ht
    (θ := fun z => a * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fr := fun j z => T.fr j (b, z))
    (fun j => (T.fr_hol j).comp hj.differentiableOn fun z hz => ⟨hb, hz⟩)
    (fun j z hz => T.fr_ne j b z hb hz) (fun j j' z hz => T.fr_coc j j' b z hb hz)
    (fun j hj => (T.fr_rig j b hb hj).trans (congrArg (fun q => valAt' q _ _) hx.symm)) hsec
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hN := normalAt_of_coord Φ.key u _ T.bas (T.h b) (T.ta b) T.c₁ T.c₂ a hu hsymm hpos hn hΛ hR hF fun i => by
    obtain ⟨W, hW, -⟩ := (existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.basis.1 i)
    have d := OrthoMetric.isDerivAt0_comp u Φ.m.φ (e := fun z => (F.ex k (T.Pf (T.co b)) z).left) hex (Φ.basis.1 i) hW
    have d' := hder (e i).1 (e i).2
    rw [show e.symm ⟨(e i).1, (e i).2⟩ = i from e.symm_apply_apply i,
      ← show _ = y.u (e i).1 (e i).2 from hv i] at d'
    obtain ⟨t₁, -, t₃⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ F k _ hP
    have hWi : W = Pi.single i 1 := (t₃ _ (t₁ _ _ d)).unique d d'
    exact hWi ▸ hW
  have hdet : ((2 * Real.pi * Complex.I : ℂ) • (T.h b)ᵀ).det = (2 * Real.pi * Complex.I) ^ Φ.T.g * (T.h b).det := by
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have key := KeyCl.value_of_normalAt hH hT Φ.key ⟨T.half₁, T.half₂⟩ ha
    (hdet.trans_ne (mul_ne_zero (pow_ne_zero _ hπ) hu.ne_zero)) hN
  rw [key, mul_div_cancel₀ _ (pow_ne_zero 8 ha)]
  exact congrArg (· ^ 4) hdet

end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam

def shimXOfPkg {D : D7} {G : DV.Geo D.what₂.LL} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {N j : ℕ} {Comp : Type} [Fintype Comp] [Nonempty Comp] (cx : CxPkg D.what₂.Tau N j Comp)
    (alg : AlgPkg G D.what₂.Tau N Comp) (pad : PadPkg D N j Comp jC ng) (h : 1 ≤ j ∧ j < N) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := Comp
  vol := cx.vol
  chern := cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N cx.vol P d hd hP
  arDeg := pad.arDeg
  arDeg_homog := pad.arDeg_homog
  arMix := pad.arMix
  arMix_HT := pad.arMix_HT
  arMix_DR := pad.arMix_DR
  CurveHT := pad.CurveHT
  degHT := pad.degHT
  CurveDR := pad.CurveDR
  degDR := pad.degDR
  FibComp := pad.FibComp
  fibInBd := pad.fibInBd
  Pt := pad.Pt
  phiDR := pad.phiDR
  phiMod := pad.phiMod
  phiFr := pad.phiFr
  XC := cx.XC
  rfn := cx.rfn
  rfn_ge := cx.rfn_ge
  hLo := cx.hLo
  hUp := cx.hUp
  hLo_le := cx.hLo_le
  connN := cx.connN
  curvN := cx.curvN
  compOf := cx.compOf
  normDetInf := cx.normDetInf
  compPt := pad.compPt
  normDetT := pad.normDetT
  normDetH := pad.normDetH
  htDetT := pad.htDetT
  ALB := alg.ALB
  arSelf := fun L => ∑ c, alg.arSelfC L c
  arSelfC := alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, alg.geoC L c
  geoC := alg.geoC
  geo_sum := fun _ => rfl
  arVol := alg.arVol
  semipos := alg.semipos
  nefFib := alg.nefFib
  arNef := alg.arNef
  Mbar := alg.Mbar

section
variable {D : D7} {A : Amb D} {F : SrcFam A} {L : CmList A} {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C)
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (k : Kits F L C jC ng)

end

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharacters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ToricTorsionCompare

theorem units_of_pow_eq_one : ∀ (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ), 1 ≤ k →
    ∀ (τ : Multiplicative X →* Kˣ), τ ^ k = 1 → ∃ τO : Multiplicative X →* Oˣ, ∀ x, ((τO x : O) : K) = (τ x : K) := by
  intro K _ O X _ k hk τ hτ
  have hpow : ∀ x, (τ x : K) ^ k = 1 := fun x => by
    have := congrArg (fun f => ((f x : Kˣ) : K)) hτ
    simpa [MonoidHom.pow_apply] using this
  have mem : ∀ x, (τ x : K) ∈ O := fun x => by
    rcases O.mem_or_inv_mem (τ x : K) with h | h
    · exact h
    · have h1 : (τ x : K) ^ (k - 1) * (τ x : K) = 1 := by rw [← pow_succ, Nat.sub_add_cancel hk, hpow]
      have h2 : ((τ x : K)⁻¹) ^ (k - 1) = τ x := by rw [inv_pow, inv_eq_of_mul_eq_one_right h1]
      rw [← h2]; exact O.pow_mem h _
  have vi : ∀ x, (τ x : K) * (τ x⁻¹ : K) = 1 := fun x => by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  let f : Multiplicative X → Oˣ := fun x =>
    ⟨⟨τ x, mem x⟩, ⟨τ x⁻¹, mem x⁻¹⟩, Subtype.ext (vi x), Subtype.ext ((mul_comm _ _).trans (vi x))⟩
  exact ⟨MonoidHom.mk' f (fun x y => Units.ext (Subtype.ext (by simp [f]))), fun x => rfl⟩

theorem toric_torsion_eq_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' _ _ hR hW g m V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hb hc hd he hf F _ _ _ _ O φ hφ hφW hgF k hk τ τ' q q' v v' hτ'k hττ' hqy hq hq'y hq' hv hv'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := _root_.GlobalTheory.ToricTorsionSec.main E H R t P hR k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := _root_.GlobalTheory.ToricTorsionSec.main E H W t' P' hW k hk1
  obtain ⟨fR, hfR, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨fW, hfW, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {G : Type} [CommGroup G] (f : Multiplicative P'.D.toPre.X →* G), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  have hv0 : v = (s F _ τ hτk).left :=
    ((hfR q v).1 hv).trans ((hfR q _).1 (s4 F _ τ hτk q rfl hqy hq)).symm
  have hv0' : v' = (s' F _ τ' hτ'k).left :=
    ((hfW q' v').1 hv').trans ((hfW q' _).1 (s4' F _ τ' hτ'k q' rfl hq'y hq')).symm

  obtain ⟨τO, hτO⟩ := units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl

  let bW : ResidueField W →+* Ω := Ideal.Quotient.lift (maximalIdeal W) β hβ
  obtain ⟨Ω', _, _, σ, κ₀, hσκ⟩ : ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (σ : Ω →+* Ω')
      (κ₀ : ResidueField O →+* Ω'), σ.comp bW = κ₀.comp (ResidueField.map φ) := by
    letI := bW.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (ResidueField W) Ω (ResidueField O))
    letI := Ideal.Quotient.field M
    let q0 : TensorProduct (ResidueField W) Ω (ResidueField O) →+* AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) :=
      (algebraMap (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) _).comp (Ideal.Quotient.mk M)
    refine ⟨AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M), inferInstance, inferInstance,
      q0.comp Algebra.TensorProduct.includeLeftRingHom, q0.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg q0.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  let κ : O →+* Ω' := κ₀.comp (residue O)
  have hκ : σ.comp β = κ.comp φ := by
    ext w
    have := congrArg (fun f => f (residue W w)) hσκ
    change σ (bW (residue W w)) = κ₀ (ResidueField.map φ (residue W w)) at this
    rw [ResidueField.map_residue] at this
    exact this
  have hκloc : IsLocalHom κ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : residue O a = 0 := (residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 hna)
    have h0 : κ a = 0 := by simp only [κ, RingHom.comp_apply, this, map_zero]
    rw [h0] at ha; exact not_isUnit_zero ha

  obtain ⟨U, hU, hUloc⟩ := IsLocalRing.exists_factor_valuationRing (σ.comp α)
  let u : V →+* U := (σ.comp α).codRestrict U.toSubring hU
  have hwu : U.subtype.comp u = σ.comp α := rfl
  let τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ := (Units.map κ.toMonoidHom).comp τO
  have h'' : τ'' ^ k = 1 := by
    rw [show τ'' ^ k = (Units.map κ.toMonoidHom).comp (τO ^ k) by ext x; simp [τ'']]
    rw [hτOk]; ext; simp
  obtain ⟨τU, hτU⟩ := units_of_pow_eq_one Ω' U _ k hk1 τ'' h''
  have hτUk : τU ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Ω'ˣ) : Ω')) h''
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτU, this]; rfl
  let zU : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom.toMonoidHom).comp τU)
  have hzU : ∀ χ, GlobalTheory.UU.chV zU χ = unitOn (τU (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, zU, MulEquiv.apply_symm_apply]; rfl
  have hkU : IsUnit (k : U) := by simpa using hk.map (u.comp ψ)
  let τRU := τU.comp ρm
  have hτRU : τRU ^ k = 1 := by
    exact powc τU hτUk
  have hG1 := _root_.GlobalTheory.TorSecLocal.toric_torsion_section_overLocal E H R t P k s s1 s2 s3 _ ρ V ψ tV mV j t₀ m₀ h₀ m₀' hc hd U u hUloc hkU τU τRU hτRU hτUk
    (fun χ => rfl) zU hzU
  have hG2 := _root_.GlobalTheory.ToricOverField.toric_section_eq_over_field E H W t' P' k s' s3' R t g m V ψ tV mV Ω α β hβ tΩ n n' j hb hf Ω' σ (κ.comp φ) hκ.symm
    U u U.subtype hwu τU τ'' h'' (fun χ => (hτU χ).symm) zU hzU
  let τRΩ := τ''.comp ρm
  have hτRΩ : τRΩ ^ k = 1 := by
    exact powc τ'' h''
  have hgU : (κ.comp φ).comp g = U.subtype.comp (u.comp ψ) := by
    ext r
    have := congrArg (fun f => σ f) (RingHom.congr_fun he r)
    have h2 := RingHom.congr_fun hκ (g r)
    simp only [RingHom.comp_apply] at this h2 ⊢
    rw [← h2, ← this]; rfl
  have h8 : (s Ω' ((κ.comp φ).comp g) τRΩ hτRΩ).left = spMap U.subtype ≫ (s U (u.comp ψ) τRU hτRU).left :=
    s2 U Ω' _ _ U.subtype τRU hτRU τRΩ hτRΩ hgU (fun χ => (hτU (ρm χ)).symm)

  let τOR := τO.comp ρm
  have hτOR : τOR ^ k = 1 := by
    exact powc τO hτOk
  obtain ⟨e, he'⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap φ)) (spMap (φ.comp g)) (spMap_comp g φ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hxy : s O (φ.comp g) τOR hτOR = e (s' O φ τO hτOk) := by
    refine _root_.GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' κ hκloc ?_
    · rw [s1, ← map_pow, s1', map_one]
    · rw [he', ← Category.assoc, ← s2' O Ω' φ (κ.comp φ) κ τO hτOk τ'' h'' rfl (fun χ => rfl), hG2,
        ← s2 O Ω' (φ.comp g) ((κ.comp φ).comp g) κ τOR hτOR τRΩ hτRΩ rfl (fun χ => rfl), h8, hG1]
  have hOR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    ext r; simp [hgF, hφW]
  have hOW : (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W)) = O.subtype.comp φ := by
    ext w; simp [hφW]
  rw [hv0, hv0', s2 O F _ _ O.subtype τOR hτOR τ hτk hOR (fun χ => by simp [τOR, hτ, hτO]),
    s2' O F _ _ O.subtype τO hτOk τ' hτ'k hOW (fun χ => by simp [hτO]), hxy, he', Category.assoc]

end GlobalTheory.ToricTorsionCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem antisymm_rename_sigmaCongrRight : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))),
    rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  intro ι _ m Q w
  classical
  unfold antisymm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun v => ?_)
  rw [map_zsmul, rename_rename, smul_smul]
  have hf : (⇑(Equiv.sigmaCongrRight w) ∘ fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) =
      fun x : Root m => (⟨x.1, (Equiv.mulLeft w v) x.1 x.2⟩ : Root m) := by
    funext x; rfl
  rw [hf]
  congr 1
  have hs : (∏ τ, Equiv.Perm.sign ((Equiv.mulLeft w v) τ) : ℤˣ) =
      (∏ τ, Equiv.Perm.sign (w τ)) * ∏ τ, Equiv.Perm.sign (v τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Equiv.Perm.sign_mul]
  rw [hs, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]

end GlobalTheory.GoodMetric
end

