module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem logDet_eq_hor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  intro E _ _ _ H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single ε
  refine ⟨s ^ Dw.dim * ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ), ?_, ?_⟩
  · have : ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (κ.trans o.symm)) with h | h <;> simp [h]
    exact mul_ne_zero (pow_ne_zero _ hs) this
  intro x K _ _ P₀ P hU g hg hP hB w hw hwk
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.LogPole.exists_snd_ev_eq_sum_of_ksIso TF K P₀ (hKS K P₀) U.1 hU
  choose y' hy' hsnd hred hev using fun j => _root_.GlobalTheory.LogPole.exists_tanPt_of_logDer TF U (b j) K P₀ hU
  have hKSj : ∀ j, FlagTan.IsKS (psiSet H) P₀ (y' j ≫ pullback.fst _ _)
      (fun k => (s : K) * (Pi.single (κ j) (1 : K) : HIx Dw (psiSet H) → K) k) := by
    intro j
    have := hcmp U n e v hv (b j) _ (hb j) K P₀ hU hB (y' j) (hy' j) (hsnd j) (hev j)
    convert this using 3 with k
    rw [hκ (ev (frX P₀ ≫ TF.Y.j) U.1 hU) n e j k]
  have hL : ∀ i j, ev (frX P₀ ≫ TF.Y.j) U.1 hU ((b j).1 (x i)) = (s : K) * δ (κ j) (x i) := by
    intro i j
    have h1 := hδ (y' j) (hy' j) (hsnd j) (hred j) _ (hKSj j) (x i)
    rw [hev j] at h1
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h1
    rw [h1]
    simp [Pi.single_apply, mul_comm, mul_left_comm]
  have hx : P.x = P₀.x := hP.1
  have hR : ∀ i j, (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd =
      ∑ k, FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) k * δ k (x i) := by
    intro i j
    have hk := (FlagTan.isKS_frChg_iff (psiSet H) g 1 P₀ P hP _ _).1 (hwk (o j)).2
    refine hδ (frX (w (o j))) (hw _) (GlobalTheory.FlagMod.frX_snd _) ?_ _ ?_ (x i)
    · rw [GlobalTheory.FlagMod.frX_frMap (hwk (o j)).1]
      exact GlobalTheory.FlagMod.eq_frX P₀ (by rw [GlobalTheory.FlagMod.frX_fst, hx]) (GlobalTheory.FlagMod.frX_snd P)
    · rw [GlobalTheory.FlagMod.frX_fst]; exact hk
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin Dw.dim) (Fin Dw.dim) K, A = Matrix.of fun i j => δ (o j) (x i) := ⟨_, rfl⟩
  have eL : (ev (frX P₀ ≫ TF.Y.j) U.1 hU).mapMatrix (Matrix.of fun i j => (b j).1 (x i)) =
      (s : K) • A.submatrix id (κ.trans o.symm) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hL, hA]
    simp
  have eR : (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd) =
      A * Matrix.of fun i j => FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) (o i) := by
    ext i j
    rw [Matrix.of_apply, hR, Matrix.mul_apply, ← Equiv.sum_comp o, hA]
    simp only [Matrix.of_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [logDet, RingHom.map_det, eR, Matrix.det_mul, _root_.GlobalTheory.KSChgDet.det_ksChg_eq_one K g hg o, mul_one, eL, Matrix.det_smul,
    Matrix.det_permute', Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOneOfAbsoluteFrobeniusPullZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR.FrobKill

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow_local : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'


end GlobalTheory.CechDR.FrobKill

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero_local : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact _root_.GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩


theorem eq_sub_of_pow_eq_sub (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsReduced B]
    (hB : (p : B) = 0) {c x y : B} (h : c ^ p = x ^ p - y ^ p) : c = x - y := by
  have e : (c - (x - y)) ^ p = 0 := by
    rw [← frobR_apply p B hB, map_sub, map_sub, frobR_apply, frobR_apply, frobR_apply, h, sub_self]
  exact sub_eq_zero.1 (IsReduced.eq_zero _ ⟨p, e⟩)

theorem mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  intro p _ k _ _ hk X _ s _ hX h c hc
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  have hex : ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1,
      (∀ U, KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧
      ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V),
        (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p =
          u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) :=
    GlobalTheory.CechDR.FrobKill.exists_closed_pow_local p k hk X s hX h f hc
  obtain ⟨u, hu, hf⟩ := hex
  choose w hw using fun U : GlobalTheory.CechDR.AffOp X ↦ sec_exists_pow_of_D_eq_zero_local p k hk X s U.unop (u U) (hu U)
  refine LinearMap.mem_ker.2 (GlobalTheory.CechDR.cmpO_injective k X s ?_)
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine GlobalTheory.CatCoh.H1.mk_eq_zero.2 ⟨w, funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_⟩
  have : IsReduced (GlobalTheory.CechDR.Sec s V.unop.1) :=
    inferInstanceAs (_root_.IsReduced Γ(X, V.unop.1))
  have hp : (p : GlobalTheory.CechDR.Sec s V.unop.1) = 0 := by
    rw [← map_natCast (algebraMap k (GlobalTheory.CechDR.Sec s V.unop.1)), hk, map_zero]
  have e := hf U V a
  rw [← hw V, ← hw U, map_pow] at e
  exact (eq_sub_of_pow_eq_sub p hp e).symm

end GlobalTheory.ConjSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.MpDivTwist

theorem mem_Bl_of_mul_pow_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N (-c) → f * s ^ m ∈ P.Bl N (m - c) 2 → f ∈ P.Bl N (-c) (Real.exp (δ * N + C * m + C)) := by
  intro k _ X _ p D hX P c hc s hs hs0 δ hδ

  obtain ⟨n, v, ρ₁, hρ₁, hv, hcov⟩ := _root_.GlobalTheory.HSNef.GenLow.gen_low k X p D hX P c hc

  obtain ⟨ρ₂, hρ₂, hmax⟩ := _root_.GlobalTheory.VolBr.max_principle_global k X p D hX P s hs hs0 δ hδ
  have hnu0 : ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (g : X.functionField), 0 ≤ P.nu a b σ y g := by
    intro a b σ y g
    unfold Pair.nu
    positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, Real.exp A = ρ₂⁻¹ := ⟨_, Real.exp_log (inv_pos.2 hρ₂)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, Real.exp B = 2 * ρ₁⁻¹ * ρ₁⁻¹ := ⟨_, Real.exp_log (by positivity)⟩
  refine ⟨|A| + |B|, by positivity, ?_⟩
  intro N m f hf hfs
  obtain ⟨hsm, hsmnu⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P 0 1 s hs m
  obtain ⟨-, hfsnu⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P (N : ℤ) (-(c : ℤ)) ((m : ℤ) * 0) ((m : ℤ) * 1) f (s ^ m) hf hsm

  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ₂ ≤ P.nu 0 1 σ y s → P.nu N (-c) σ y f ≤ 2 * ρ₂⁻¹ ^ m := by
    intro σ y hy
    have h1 := hfsnu σ y
    rw [hsmnu σ y] at h1
    have h2 : P.nu ((N : ℤ) + (m : ℤ) * 0) (-(c : ℤ) + (m : ℤ) * 1) σ y (f * s ^ m) ≤ 2 := by
      have e1 : ((N : ℤ) + (m : ℤ) * 0) = N := by ring
      have e2 : (-(c : ℤ) + (m : ℤ) * 1) = (m : ℤ) - c := by ring
      rw [e1, e2]
      exact hfs.2 σ y
    rw [h1] at h2
    have h3 : P.nu N (-c) σ y f * ρ₂ ^ m ≤ 2 := by
      calc P.nu N (-c) σ y f * ρ₂ ^ m ≤ P.nu N (-c) σ y f * P.nu 0 1 σ y s ^ m := by
            gcongr
            exact hnu0 _ _ _ _ _
        _ ≤ 2 := h2
    calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₂ ^ m * ρ₂⁻¹ ^ m := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ₂.ne', one_pow, mul_one]
      _ ≤ 2 * ρ₂⁻¹ ^ m := by gcongr

  have hprod : ∀ i, ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu N (-c) σ y f * P.nu 0 c σ y (v i) ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) := by
    intro i
    obtain ⟨hfv, hfvnu⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P (N : ℤ) (-(c : ℤ)) 0 (c : ℤ) f (v i) hf (hv i).1
    have e1 : ((N : ℤ) + 0) = N := by ring
    have e2 : (-(c : ℤ) + c) = 0 := by ring
    rw [e1, e2] at hfv hfvnu
    have hb := hmax N (f * v i) (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) hfv (fun σ y hy => by
      rw [hfvnu σ y]
      exact mul_le_mul (key σ y hy) ((hv i).2 σ y) (hnu0 _ _ _ _ _) (by positivity))
    intro σ y
    rw [← hfvnu σ y]
    exact hb.2 σ y
  refine ⟨hf, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hcov σ y
  have h4 : P.nu N (-c) σ y f * ρ₁ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) :=
    calc P.nu N (-c) σ y f * ρ₁ ≤ P.nu N (-c) σ y f * P.nu 0 c σ y (v i) := by
          gcongr
          exact hnu0 _ _ _ _ _
      _ ≤ _ := hprod i σ y
  have hAC : A ≤ |A| + |B| := by
    have := le_abs_self A
    have := abs_nonneg B
    linarith
  have hBC : B ≤ |A| + |B| := by
    have := le_abs_self B
    have := abs_nonneg A
    linarith
  calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₁ * ρ₁⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hρ₁.ne', mul_one]
    _ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) * ρ₁⁻¹ := by gcongr
    _ = Real.exp (δ * N) * ρ₂⁻¹ ^ m * (2 * ρ₁⁻¹ * ρ₁⁻¹) := by ring
    _ = Real.exp (δ * N) * Real.exp (m * A) * Real.exp B := by rw [Real.exp_nat_mul, hA, hB]
    _ ≤ Real.exp (δ * N) * Real.exp (m * (|A| + |B|)) * Real.exp (|A| + |B|) := by
        gcongr
    _ = Real.exp (δ * N + (|A| + |B|) * m + (|A| + |B|)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end GlobalTheory.HSNef.MpDivTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ModelWtGap

def colRot (p q : ℕ) (a : Fin (p + q)) : Fin (p + q) :=
  if h : (a : ℕ) < q then ⟨p + a, by omega⟩ else ⟨a - q, by omega⟩

theorem colRot_val (p q : ℕ) (a : Fin (p + q)) :
    (colRot p q a : ℕ) = if (a : ℕ) < q then p + a else a - q := by
  unfold colRot
  split_ifs <;> rfl

theorem colRot_bijective (p q : ℕ) : Function.Bijective (colRot p q) := by
  refine Finite.injective_iff_bijective.1 fun a b h => ?_
  have h1 := congrArg Fin.val h
  rw [colRot_val, colRot_val] at h1
  have := a.2
  have := b.2
  apply Fin.ext
  split_ifs at h1 <;> omega

theorem model_weight_gap_l1_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hp hq u1 g hg k
  obtain rfl := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ ρ : E →+* ℂ, ρ (H.rt : E) = H.rt0 → relab c σ ρ (H.rt : E) = H.rt0 := fun ρ h =>
    (congrArg σ (Subtype.ext h)).trans hσ0
  let e : Psi H → (U.X k).Ψ := fun ρ => ⟨relab c σ ρ.1, (hΨ _).2 (hrel _ ρ.2)⟩
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (relab_injective σ (congrArg Subtype.val h)), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := hsurj τ.1
    have hρΨ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      have h3 := hrel _ (GlobalTheory.AllWt.conj_mem hn)
      rw [relab_conj, hρ] at h3
      exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
    exact ⟨⟨ρ, hρΨ⟩, Subtype.ext hρ⟩
  have hval : ∀ (ρ : Psi H) (a : Fin (Dw.p + Dw.q)),
      modelWt U (wtOf Dw u1 0) k (e ρ) a = u1 ρ (colRot Dw.p Dw.q a) := by
    rintro ρ ⟨a, ha⟩
    by_cases h : a < Dw.q
    · rw [modelWt_wtOf_small U u1 0 k hp0 ρ (e ρ).2 a h ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp [h]
    · obtain ⟨i, rfl⟩ : ∃ i, a = Dw.q + i := ⟨a - Dw.q, by omega⟩
      rw [modelWt_wtOf_big U u1 0 k hp0 ρ (e ρ).2 i (by omega) ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, ?_, ?_⟩
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    rw [hp0] at hb
    split_ifs <;> omega
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    split_ifs <;> omega
  · unfold GlobalTheory.CovHt.l1
    rw [← he.sum_comp]
    refine Finset.sum_congr (by congr) fun ρ _ => ?_
    simp only [hval]
    exact (colRot_bijective Dw.p Dw.q).sum_comp fun i => |(u1 ρ i : ℝ)|
  · rw [Nat.card_eq_of_bijective e he, Nat.card_eq_fintype_card, Fintype.card_coe]

end GlobalTheory.ModelWtGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.Pull

open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

theorem fnMap_algebraMap (y : Y) (a : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (j.stalkMap y a) := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [algebraMap_germ hx s, fnMap_fnOf j hη _ (gen_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem regAt_fnMap {y : Y} {t : X.functionField} (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, (fnMap_algebraMap j hη y a).symm⟩

theorem unitAt_fnMap {y : Y} {t : X.functionField} (h : UnitAt (j y) t) : UnitAt y (fnMap j hη t) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, ha.map _, (fnMap_algebraMap j hη y a).symm⟩

end

end GlobalTheory.FrameGlue.Pull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

open GlobalTheory.ArInt

end GlobalTheory.AmpleTwistNef
end
end

