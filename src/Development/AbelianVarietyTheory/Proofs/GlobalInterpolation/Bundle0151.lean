module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ObjCOfRecExObjO
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Formalism.LocalToGlobal.HermitianForms.Bundle0009
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h


open GlobalTheory.EX.DC in
theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb


open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in
theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PtCoMemIntSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PtCo

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem ptCo_one (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V) (hy : y ∈ (D.fm u).ptLat.L) (c : (D.fm u).clsP) :
    Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  obtain ⟨P, hP, hq⟩ := (Tf.valP.lat y).1 hy w c (B w c) (hB w c)
  rw [Matrix.coe_units_inv] at hq
  have e : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c = P := by
    simp only [Formalism.L2.GlobalTheoryTheory.Br.coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (Matrix.isUnits_det_units (B w c)))]
  rw [e]
  exact hP

theorem ptCo_mem_intSpan : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E), (∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c)) → ∀ w, ∀ y ∈ (D.fm u).SP w, ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  intro D u Ch chOf Tf B hB w y hy c
  induction hy using Submodule.span_induction with
  | mem y hy => exact ptCo_one D u Ch chOf Tf B hB w y hy c
  | zero => rw [map_zero, map_zero, Pi.zero_apply]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), Pi.add_apply]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : D.what₂.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply]
    exact intSpan_smul' D w _ (r : D.what₂.LL) r.2 _ hy

end GlobalTheory.PtCo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPair
section
noncomputable section

namespace GlobalTheory.PerRedTw

section Copied

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

theorem exists_orthonormal_frame_twisted (D : D7) : ∃ o : FrP D, o.IsON := by
  classical
  let _ := D.host.cmStar
  have hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ,
      IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1 := by
    intro τ
    have hs := D.sp.X'_sig (embT D τ)
    rw [D.X'_posDef (embT D τ)] at hs
    dsimp only at hs
    obtain ⟨e, P, hP⟩ := hs
    have hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1 := by
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [Formalism.UG.Jpq, Matrix.one_apply]
        · exact j.elim0
      · exact i.elim0
    have hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [hcT, hJ] at hP
    let f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1) := finCongr (rankP D)
    let g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0 := f.symm.trans e
    have hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e := by
      ext i j
      simp [g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine ⟨P.1.submatrix g g, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact Matrix.isUnits_det_units P
    · have h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g := by
        ext i j; simp
      rw [Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]
      exact Matrix.submatrix_one_equiv g
  choose Y hYu hY using hY
  exact ⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩

theorem nfAll_zero_tw {D : D7} (n : ℕ) (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

end Copied

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.MainNotions.RT.PeriodPointConditions GlobalTheory.PerQ

attribute [local instance] MemberForms.clsPFin

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
  {Tw : TwForms D} {Y : DivX D}

theorem eW_rep_o_tw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (o : FrP D)
    (z : (D.PTw u μ).Wrow) (hz : z ∈ (Tw.fm u μ).ptC) (c : (Tw.fm u μ).clsP) :
    ∃ Q ∈ CSpan (Tw.fm u μ).sg,
      (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := ((t.pt.val u μ hμ).ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((t.pt.cls u μ hμ).y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (Tw.fm u μ).sg := by
    have := CSpan_shW (Tw.fm u μ).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

open Classical in
theorem eW_resCTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) :
    (t.pt.val u μ hμ).eW (resCTw t u μ hμ c z) = fun c' => if c' = c then (t.pt.val u μ hμ).eW z c' else 0 := by
  classical
  unfold resCTw
  rw [LinearEquiv.apply_symm_apply]

theorem petersson_eq_sum_restrict_twist (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (a b : (D.PTw u μ).Wrow) (ha : a ∈ (Tw.fm u μ).ptC) (hb : b ∈ (Tw.fm u μ).ptC) :
    (Tw.fm u μ).ipP a b = ∑ c, (Tw.fm u μ).ipP (resCTw t u μ hμ c a) (resCTw t u μ hμ c b) := by
  classical
  obtain ⟨o, ho⟩ := exists_orthonormal_frame_twisted D
  choose P hP hPe using eW_rep_o_tw t u μ hμ o a ha
  choose Q hQ hQe using eW_rep_o_tw t u μ hμ o b hb
  rw [(t.pt.val u μ hμ).ipP o ho a b P Q hP hQ hPe hQe]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hP c'
    · exact Submodule.zero_mem _
  have hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hQ c'
    · exact Submodule.zero_mem _
  have hPe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c a) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hPe c'
    · exact (map_zero _).symm
  have hQe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c b) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hQe c'
    · exact (map_zero _).symm
  rw [(t.pt.val u μ hμ).ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc', nfAll_zero_tw]
  · intro h; exact absurd (Finset.mem_univ c) h

open Classical in
def pcTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  if z ∈ (Tw.fm u μ).ptC then pcLTw t u μ hμ c z G
  else if h : Nonempty (Tw.fm u μ).clsP then
    (if c = Classical.choice h then ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) * (D.PTw u μ).period z G else 0)
  else 0

theorem perDecTw_of_at (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : PerDecTwT Y t u μ hμ) : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  classical
  have hcard : ∀ c, ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) ≠ 0 := fun c =>
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨pcTw t u μ hμ, fun z G => ?_, fun x hx F hF c => ?_⟩
  · by_cases hz : z ∈ (Tw.fm u μ).ptC
    · have hG : t.ptE.jM u μ G ∈ (Tw.fm u μ).ptC := ((t.ptE.per u μ hμ).2.1) G
      rw [((t.ptE.per u μ hμ).2.2) z G, petersson_eq_sum_restrict_twist t u μ hμ _ _ hG hz]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [pcTw, if_pos hz, pcLTw]
      rw [← mul_assoc, inv_mul_cancel₀ (hcard c), one_mul]
    · by_cases hne : Nonempty (Tw.fm u μ).clsP
      · rw [Finset.sum_eq_single (Classical.choice hne)]
        · simp only [pcTw, if_neg hz, dif_pos hne, ↓reduceIte]
          rw [← mul_assoc, inv_mul_cancel₀ (hcard _), one_mul]
        · intro c _ hc
          simp only [pcTw, if_neg hz, dif_pos hne, if_neg hc, mul_zero]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · have hE : IsEmpty (Tw.fm u μ).clsP := not_nonempty_iff.mp hne
        have hz0 : z = 0 := (t.pt.val u μ hμ).eW.injective (funext fun c => hE.elim c)
        subst hz0
        simp
  · obtain ⟨y, hy, hv⟩ := h x hx F hF c
    have hz : (Tw.fm u μ).ptEmb x ∈ (Tw.fm u μ).ptC := (((t.pt.val u μ hμ).rat _).1 ⟨x, rfl⟩).1
    refine ⟨y, ?_, hv⟩
    simp only [pcTw, if_pos hz]
    exact hy

theorem reduction_perDecTw : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ :=
  fun _ _ _ _ _ _ t _ u μ hμ h => perDecTw_of_at t u μ hμ h

end GlobalTheory.PerRedTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
section
namespace GlobalTheory.VolIndepClosed

theorem volIndep (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  (GlobalTheory.VolIndepCompare.volumeIndependence_iff D).1 (GlobalTheory.VolumeIndep.volumeIndependence D)

end GlobalTheory.VolIndepClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem tameDistinctF_iff {eps : ℝ} (Fm : FamP eps) : DC.TameDistinctF Fm ↔ Formalism.MainNotions.TameDistinctF Fm := by
  unfold DC.TameDistinctF Formalism.MainNotions.TameDistinctF
  simp only [DQ.tameDistinct_iff]

theorem dGamDvdF_iff {eps : ℝ} (Fm : FamP eps) : DC.DGamDvdF Fm ↔ Formalism.MainNotions.DGamDvdF Fm := Iff.rfl

theorem codeUpF_iff {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : DC.CodeUpF Fm C0 CH ↔ Formalism.MainNotions.CodeUpF Fm C0 CH := Iff.rfl

theorem working_classes_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm) ∧ (Formalism.MainNotions.Des (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9) 3 Fm ↔ W3 𝒜 Fm)) ∧ (∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → DC.DesignChoices (DC.WithTw 𝒜) 3 cT) → Formalism.MainNotions.MinkDiv → Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw 𝒜) 3 cT) := by
  refine ⟨fun 𝒜 eps Fm => ?_, fun 𝒜 cT h hM => ?_⟩
  · have e1 : Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧
        Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm := by
      simp only [Formalism.MainNotions.WithTw, Formalism.MainNotions.WithSm, W1, tameDistinctF_iff, dGamDvdF_iff]
    refine ⟨e1, ?_⟩
    simp only [Formalism.MainNotions.Des, W3, ← e1]
  · obtain ⟨ε0, h0, h⟩ := h hM
    refine ⟨ε0, h0, fun eps he hle K => ?_⟩
    obtain ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h eps he hle K
    exact ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, (tameDistinctF_iff Fm).1 h15, h16,
      (codeUpF_iff Fm 3 CH).1 h17, h18⟩

end GlobalTheory.Fc
end

