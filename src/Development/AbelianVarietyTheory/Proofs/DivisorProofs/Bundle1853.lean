module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem isKSValue_act : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  intro R _ A _ A' _ i h O _ a a' hi z f w hf
  haveI := a.hom z
  haveI := a'.hom z
  obtain ⟨k, ⟨d, hd, e⟩, l⟩ := hf
  rw [act_apply]
  have hm := push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd
  have hl := l.push (a.act z)
  refine ⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩
  have kk : GrpMor (dp0 R) (𝟙 _) A (epsDP R) (DeRham.epsRed R) A
      (algebraMap R (DualNumber R)) (𝟙 _) (a.act z).left :=
    ⟨(constMor A).dp, (constMor A).base, by simpa using (Over.w (a.act z)),
      (homMor (dp0 R) (𝟙 _) (a.act z)).mul⟩
  have hM := homMor (epsDP R) (DeRham.epsRed R) (a.act z)
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, e]
  rfl
end GlobalTheory.KSExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearSystemRatioOfDegreeOfGeneratesByRatios
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open GlobalTheory.DegCmp

section

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def sameDegQuot (ev : V →ₗ[K] Ω) : IntermediateField K Ω where
  carrier := {x | ∃ (e : ℕ) (q : Ω), q ∈ (LinearMap.range ev) ^ e ∧ q ≠ 0 ∧ x * q ∈ (LinearMap.range ev) ^ e}
  mul_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show x * y * (q * q') = (x * q) * (y * q') by ring]
      exact Submodule.mul_mem_mul hxq hyq'
  add_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show (x + y) * (q * q') = (x * q) * q' + q * (y * q') by ring]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul hxq hq') (Submodule.mul_mem_mul hq hyq')
  algebraMap_mem' a := by
    refine ⟨0, 1, by simp [Submodule.one_eq_range], one_ne_zero, ?_⟩
    rw [pow_zero, mul_one]
    exact Submodule.algebraMap_mem a
  inv_mem' := by
    rintro x ⟨e, q, hq, hq0, hxq⟩
    by_cases hx : x = 0
    · subst hx
      exact ⟨e, q, hq, hq0, by simpa using hxq⟩
    · refine ⟨e, x * q, hxq, mul_ne_zero hx hq0, ?_⟩
      rwa [show x⁻¹ * (x * q) = q by field_simp]

theorem ratioField_le_sameDegQuot (ev : V →ₗ[K] Ω) : ratioField ev ≤ sameDegQuot ev := by
  rw [ratioField, IntermediateField.adjoin_le_iff]
  rintro a ⟨v, w, rfl⟩
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact (sameDegQuot ev).zero_mem
  · refine ⟨1, ev w, by simp, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]
    exact LinearMap.mem_range_self ev v

theorem isRatio_of_genRatios (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) : GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  rintro ⟨hev, htop⟩ τ t
  obtain ⟨w, hw⟩ : ∃ w, ev w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hev (LinearMap.ext h)
  have hmem : t / ev w ^ τ ∈ sameDegQuot ev := by
    apply ratioField_le_sameDegQuot ev
    rw [htop]; trivial
  obtain ⟨e, q, hq, hq0, hp⟩ := hmem
  refine ⟨e, q, hq, hq0, ?_⟩
  have : t * q = (t / ev w ^ τ * q) * ev w ^ τ := by
    field_simp
  rw [this, add_comm, pow_add]
  exact Submodule.mul_mem_mul hp (Submodule.pow_mem_pow _ (LinearMap.mem_range_self ev w) τ)

end

end GlobalTheory.DegVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldExt

variable {k E : Type} [Field k] [Field E] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra E Γ(Y, ⊤)]

theorem isNef_pull (hN : Published.NefNumerics) [IsProper (strHom k (X := X))] {L H : LB X} (h : IsNef k L)
    (hH : IsAmpleLB H) {H' : LB Y} (hH' : IsAmpleLB H') (g : Y ⟶ X) : IsNef E (L.pull g) := by
  have hL := LB.isLB_pull h.isLB g
  have hA := LB.isLB_pull hH.isLB g
  refine ⟨hL, fun C hC => ?_⟩
  let Z : Closeds X := Closeds.closure (g '' C)
  have hi : IsIrreducible (Z : Set X) := (hC.1.image g g.continuous.continuousOn).closure
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ g := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ g) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩

  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hi
  have hZp : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hHZ := hH.pull_of_isClosedImmersion (redι Z)
  have hproj := hHZ.isProjOver (strHom k _)
  have hLZ : IsNef k (L.pull (redι Z)) := h.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))

  letI := algebraΓAlong E (redι C)
  have := hC.isProper_strHom
  have := isIntegral_red hC.1

  have hdense : ∀ U : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
      genericPoint _ ∈ U → ∃ y, φ y ∈ U := fun U hU => by
    obtain ⟨V, hV, hUV⟩ := (redι Z).isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
    have h1 : redι Z (genericPoint _) ∈ V := by
      rw [← Set.mem_preimage, hUV]; exact hU
    have h2 : redι Z (genericPoint _) ∈ closure (g '' C) := by
      have := (range_redι Z).le ⟨genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme, rfl⟩
      exact this
    obtain ⟨_, hv, ⟨c, hc, rfl⟩⟩ := mem_closure_iff.1 h2 V hV h1
    obtain ⟨y, rfl⟩ := (range_redι C).ge hc
    refine ⟨y, ?_⟩
    rw [← SetLike.mem_coe, ← hUV, Set.mem_preimage]
    have e : redι Z (φ y) = g (redι C y) := congrArg (fun q => q y) hφ
    rw [e]; exact hv
  have key : ∀ m : ℕ, 0 ≤ m * interNumRed E C ![L.pull g] + interNumRed E C ![H.pull g] := fun m => by
    have hbig := (hLZ.pow hHZ m).isBig_tens_ample hN hproj hHZ
    obtain ⟨r, ⟨s, hs0⟩, hr⟩ :=
      (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
    obtain ⟨x, hx⟩ := hdense (nonzeroLocus s) ((sec_ne_zero_iff s).1 hs0)
    have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge hx
    have hLZ' := LB.isLB_pull h.isLB (redι Z)
    have hHZ' := LB.isLB_pull hH.isLB (redι Z)
    have hr' := isLB_lbPow (isLB_tens (isLB_lbPow hLZ' m) hHZ') r
    have h0 := (interNum_one_nonneg_of_sec (k := E) (hH'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hC.2) (LB.isLB_pull hr' φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).1
    have hT' := isLB_tens (isLB_lbPow hL m) hA
    have h1 : interNumRed E C ![lbPow (tens (lbPow (L.pull g) m) (H.pull g)) r] =
        interNum E (structureModule _) ![(lbPow (tens (lbPow (L.pull (redι Z)) m) (H.pull (redι Z))) r).pull φ] := by
      rw [interNumRed_one_eq (isLB_lbPow hT' r)]
      refine interNum_congr_cls E _ (isLB_vecOne (LB.isLB_pull (isLB_lbPow hT' r) _))
        (isLB_vecOne (LB.isLB_pull hr' φ)) fun i => ?_
      fin_cases i
      change pull (redι C) (cls _ (isLB_lbPow hT' r)) = pull φ (cls _ hr')
      rw [cls_lbPow_tens_lbPow hL hA, cls_lbPow_tens_lbPow hLZ' hHZ', cls_pull h.isLB, cls_pull hH.isLB,
        cls_pull h.isLB, cls_pull hH.isLB]
      simp only [map_nsmul, map_add (f := _), ← pull_comp, hφ]
    rw [← h1, hC.interNumRed_lbPow hH' hT', hC.interNumRed_of_cls_eq_add hH' hT' (isLB_lbPow hL m) hA rfl,
      hC.interNumRed_lbPow hH' hL] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  by_contra! hneg
  have := key ((interNumRed E C ![H.pull g]).natAbs + 1)
  have h2 := le_abs_self (interNumRed E C ![H.pull g])
  have h3 := abs_nonneg (interNumRed E C ![H.pull g])
  push_cast at this
  nlinarith

end GlobalTheory.NefFieldExt

namespace GlobalTheory.NefFieldExt

theorem isNef_baseChange : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0})
    (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p →
    letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  intro hN k E _ _ _ Y X p q π H hp
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  intro L hL
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsProper (strHom k (X := Y)) := by rw [strHom_eq (f := p) fun _ => rfl]; exact hpp
  have : IsAffineHom π := MorphismProperty.of_isPullback H.flip inferInstance
  exact isNef_pull hN hL hA (hA.pull_of_isAffineHom π) π

end GlobalTheory.NefFieldExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlatTw.Hol

theorem isSec_of_local_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (μ : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (h : ∀ x₀ ∈ X.dom, ∃ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P P' : Frame X.Ψ r → ℂ), X.IsSec (μ + la) P ∧
      X.IsSec la P' ∧ P' x₀ ≠ 0 ∧ ∀ x ∈ X.dom, Q x * P' x = P x) : X.IsSec μ Q := by
  refine ⟨?_, ?_, ?_⟩
  · intro x₀ hx₀
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x₀ hx₀
    have hd : DifferentiableWithinAt ℂ (fun y => P y * (P' y)⁻¹) X.dom x₀ :=
      (hP.1 x₀ hx₀).mul ((hP'.1 x₀ hx₀).inv hne)
    have hc : ContinuousWithinAt P' X.dom x₀ := hP'.1.continuousOn x₀ hx₀
    have hev := Filter.Tendsto.eventually hc (eventually_ne_nhds hne)
    have hd' : DifferentiableWithinAt ℂ Q (X.dom ∩ {z | P' z ≠ 0}) x₀ := by
      refine (hd.mono Set.inter_subset_left).congr (fun z hz => ?_) ?_
      · exact (eq_mul_inv_iff_mul_eq₀ hz.2).2 (hQ z hz.1)
      · exact (eq_mul_inv_iff_mul_eq₀ hne).2 (hQ x₀ hx₀)
    exact (differentiableWithinAt_inter' hev).1 hd'
  · intro x hx b hb
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x hx
    have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
    have hdiag : ∀ (τ : X.Ψ) (i : Fin r), b τ i i ≠ 0 := by
      intro τ i
      have hbt : (mat b τ).BlockTriangular id := fun a c hac => (hb' τ).2 a c hac
      have hdet := (hb' τ).1
      rw [Matrix.det_of_upperTriangular hbt] at hdet
      exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
    have hcl : bchar la b ≠ 0 := by
      unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ =>
        Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hdiag τ i)
    have hsplit : bchar (μ + la) b = bchar μ b * bchar la b := by
      unfold bchar
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
    have h1 := hQ (rmul x b) (dom_rmul X hx hb)
    rw [hP.2.1 x hx b hb, hP'.2.1 x hx b hb, ← hQ x hx, hsplit] at h1
    apply mul_right_cancel₀ (mul_ne_zero hcl hne)
    calc Q (rmul x b) * (bchar la b * P' x) = bchar μ b * bchar la b * (Q x * P' x) := h1
      _ = bchar μ b * Q x * (bchar la b * P' x) := by ring
  · intro γ hγ x hx
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x hx
    have hχ : X.χ la γ ≠ 0 := by
      obtain ⟨n, hn, hpow⟩ := X.χ_fin la
      intro h0
      have h2 := hpow γ hγ
      rw [h0, zero_pow hn.ne'] at h2
      exact zero_ne_one h2
    have h1 := hQ (lact γ x) (ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_dom X hγ hx)
    rw [hP.2.2 γ hγ x hx, hP'.2.2 γ hγ x hx, ← hQ x hx, X.χ_add μ la γ hγ] at h1
    apply mul_right_cancel₀ (mul_ne_zero hχ hne)
    calc Q (lact γ x) * (X.χ la γ * P' x) = X.χ μ γ * X.χ la γ * (Q x * P' x) := h1
      _ = X.χ μ γ * Q x * (X.χ la γ * P' x) := by ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) (N : ℕ) :
    g ^ (N + 1) ∈ GlobalTheory.AllWt.secZ Xo c ((N + 1) • e) :=
  by
  induction N with
  | zero => simpa using hg
  | succ N ih =>
    rw [pow_succ, succ_nsmul]
    exact GlobalTheory.AllWt.mul_mem_secZ ih hg

theorem rdU_pow_succ_apply (U : Unf Xo c σ r) (g : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) (N : ℕ) :
    rdU U (g ^ (N + 1)) k x = rdU U g k x ^ (N + 1) :=
  by
  induction N with
  | zero => simp only [zero_add, pow_one]
  | succ N ih =>
    calc rdU U (g ^ (N + 1 + 1)) k x = rdU U (g ^ (N + 1) * g) k x := by rw [pow_succ]
      _ = rdU U (g ^ (N + 1)) k x * rdU U g k x := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
      _ = rdU U g k x ^ (N + 1 + 1) := by rw [ih, ← pow_succ]

theorem isSec_modelWt_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Nonempty (KeySec Xo c) → GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ G : WTZ E, Even G.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) → ∀ f ∈ secZ Xo c (exZ Dw G), ∀ k, (U.X k).IsSec (modelWt U G k) (rdU U f k) := by
  intro E _ _ _ H Dw l Xo c σ r U hκ hσ hU hpq G hG hdec f hf k
  obtain ⟨κ⟩ := hκ
  have hU' := hU
  unfold IsUnf at hU'
  have hUsec := hU'.2.2.2.2.1
  have hsn : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), secZ Xo c (exZ Dw (wtZ a n)) = sec Xo c a n :=
    fun a n => by rw [GlobalTheory.AllWt.exZ_wtZ]; exact GlobalTheory.AllWt.secZ_nat Xo c a n
  have hG2 := hG
  obtain ⟨g2, hg2⟩ := hG2
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = |G.2| := ⟨G.2.natAbs, Int.natCast_natAbs _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), -(B : ℤ) ≤ G.1 (τ, j) := by
    refine ⟨∑ τ : E →+* ℂ, ∑ j : Fin (Dw.mult τ), (G.1 (τ, j)).natAbs, fun τ j => ?_⟩
    have h1 : (G.1 (τ, j)).natAbs ≤ ∑ j' : Fin (Dw.mult τ), (G.1 (τ, j')).natAbs :=
      Finset.single_le_sum (f := fun j' : Fin (Dw.mult τ) => (G.1 (τ, j')).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j' : Fin (Dw.mult τ), (G.1 (τ, j')).natAbs ≤
        ∑ τ' : E →+* ℂ, ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs :=
      Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    have h3 : -((G.1 (τ, j)).natAbs : ℤ) ≤ G.1 (τ, j) := by
      rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h4 : ((G.1 (τ, j)).natAbs : ℤ) ≤
        ((∑ τ' : E →+* ℂ, ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs : ℕ) : ℤ) := by
      exact_mod_cast h1.trans h2
    linarith
  apply isSec_of_local_quot (U.X k) (modelWt U G k) (rdU U f k)
  intro x₀ hx₀
  obtain ⟨m, f₀, hf₀, hne⟩ :=
    GlobalTheory.CuspFrom.KeyHol.exists_sec_rdU_ne_zero (Formalism.L2.PjFree.Unf.ofPj U) k x₀ hx₀
  have hne' : rdU U f₀ k x₀ ≠ 0 := hne
  obtain ⟨tg, htg⟩ : ∃ tg : ℕ, tg = (B + 1) * m + (N + 1) * (m + 1) := ⟨_, rfl⟩
  have htg1 : (N : ℤ) + 1 ≤ (tg : ℤ) := by
    rw [htg]; push_cast
    have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
    have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    nlinarith [mul_nonneg hB0 hm0, mul_nonneg hN0 hm0]
  have hnn : 0 ≤ g2 + (tg : ℤ) := by
    linarith [le_abs_self G.2, neg_le_abs G.2]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = g2 + tg := ⟨(g2 + tg).toNat, Int.toNat_of_nonneg hnn⟩
  obtain ⟨ag, hag⟩ : ∃ ag : (E →+* ℂ) × ℕ → ℕ, ∀ τ i, ag (τ, i) = if i < Dw.mult τ then B + 1 else 0 :=
    ⟨fun x => if x.2 < Dw.mult x.1 then B + 1 else 0, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (E →+* ℂ) × ℕ → ℕ, ∀ τ i,
      (a (τ, i) : ℤ) = if i < Dw.mult τ then G.1 (τ, i) + ((B : ℤ) + 1) else 0 := by
    refine ⟨fun x => if x.2 < Dw.mult x.1 then (G.1 x + ((B : ℤ) + 1)).toNat else 0, fun τ i => ?_⟩
    dsimp only
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      have h5 := hB τ ⟨i, h⟩
      simp only at h5
      linarith
    · simp

  have hf₀Z : f₀ ∈ secZ Xo c (exZ Dw (wtZ 0 (2 * (m + 1)))) := by rw [hsn]; exact hf₀
  have hgZ' : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈
      secZ Xo c ((fun i => ((B + 1 : ℕ) : ℤ) * keyEx Dw i) + (B + 1 + N + 1) • exZ Dw (wtZ 0 (2 * (m + 1)))) :=
    GlobalTheory.AllWt.mul_mem_secZ (κ.pow_mem (B + 1)) (pow_succ_mem_secZ hf₀Z (B + 1 + N))
  have hEg : exZ Dw (wtZ ag (2 * tg)) =
      (fun i => ((B + 1 : ℕ) : ℤ) * keyEx Dw i) + (B + 1 + N + 1) • exZ Dw (wtZ 0 (2 * (m + 1))) := by
    funext i
    rcases i with _ | ⟨τ, j⟩
    · simp [exZ, wtZ, keyEx, htg]
      ring
    · simp [exZ, wtZ, keyEx, hag]
  have hgZ : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈ secZ Xo c (exZ Dw (wtZ ag (2 * tg))) := by
    rw [hEg]; exact hgZ'
  have hgsec : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈ sec Xo c ag (2 * tg) := by
    rw [← hsn]; exact hgZ

  have hEa : exZ Dw (wtZ a (2 * t)) = exZ Dw G + exZ Dw (wtZ ag (2 * tg)) := by
    funext i
    rcases i with _ | ⟨τ, j⟩
    · simp [exZ, wtZ]
      linarith
    · simp [exZ, wtZ, hag]
      rw [ha τ j, if_pos j.isLt]
  have hfgsec : f * ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) ∈ sec Xo c a (2 * t) := by
    rw [← hsn, hEa]; exact GlobalTheory.AllWt.mul_mem_secZ hf hgZ

  have hDomG : Dom ag (2 * tg) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul tg⟩
    show ag (τ, j) ≤ ag (τ, i)
    rw [hag, hag]
    split_ifs <;> omega
  have hDomA : Dom a (2 * t) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul t⟩
    show a (τ, j) ≤ a (τ, i)
    have hi := ha τ i
    have hj := ha τ j
    by_cases hjm : j < Dw.mult τ
    · have him : i < Dw.mult τ := lt_of_le_of_lt hij hjm
      rw [if_pos hjm] at hj
      rw [if_pos him] at hi
      have hd := hdec τ i j hij hjm
      omega
    · rw [if_neg hjm] at hj
      omega

  have hWeven : Even (wtZ ag (2 * tg)).2 := ⟨(tg : ℤ), by simp [wtZ, two_mul]⟩
  have hEx : exZ Dw (wtZ a (2 * t)) = exZ Dw (G + wtZ ag (2 * tg)) := by
    rw [GlobalTheory.FlatTw.exZ_add_eq]; exact hEa
  have hwt : modelWt U G k + laU U ag (2 * tg) k = laU U a (2 * t) k := by
    rw [← GlobalTheory.AllWt.modelWt_wtZ U ag, ← GlobalTheory.AllWt.modelWt_wtZ U a, ← GlobalTheory.AllWt.modelWt_add U hG hWeven k, GlobalTheory.AllWt.modelWt_congr U hσ hU hEx]

  have h1ne : rdU U 1 k x₀ ≠ 0 := by
    intro h0
    apply hne'
    have h6 : rdU U (f₀ * 1) k x₀ = rdU U f₀ k x₀ * rdU U 1 k x₀ := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
    rw [mul_one, h0, mul_zero] at h6
    exact h6
  have hρne : rdU U (κ.ρ : Rul Xo c) k x₀ ≠ 0 := by
    intro h0
    apply h1ne
    have h6 : rdU U ((κ.ρ : Rul Xo c) * ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) k x₀ =
        rdU U (κ.ρ : Rul Xo c) k x₀ * rdU U ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) k x₀ := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
    rw [Units.mul_inv, h0, zero_mul] at h6
    exact h6
  have hgx : rdU U ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) k x₀ =
      rdU U (κ.ρ : Rul Xo c) k x₀ ^ (B + 1) * rdU U f₀ k x₀ ^ (B + 1 + N + 1) := by
    rw [← rdU_pow_succ_apply U (κ.ρ : Rul Xo c) k x₀ B, ← rdU_pow_succ_apply U f₀ k x₀ (B + 1 + N), GlobalTheory.AllWt.rdU_mul]
    rfl
  refine ⟨laU U ag (2 * tg) k, rdU U (f * ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1))) k,
    rdU U ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) k, ?_, ?_, ?_, ?_⟩
  · rw [hwt]; exact hUsec a (2 * t) hDomA _ hfgsec k
  · exact hUsec ag (2 * tg) hDomG _ hgsec k
  · rw [hgx]; exact mul_ne_zero (pow_ne_zero _ hρne) (pow_ne_zero _ hne')
  · intro x _
    exact (congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U f ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1))) k) x).symm

end GlobalTheory.FlatTw.Hol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_action_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  first | exact @GlobalTheory.TorusDilate.main | exact GlobalTheory.TorusDilate.main | (intros; apply GlobalTheory.TorusDilate.main <;> assumption)
end

