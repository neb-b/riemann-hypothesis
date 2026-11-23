module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.FinPl.LastDiag (add_smul_mx exists_idemAt jX_pX_mem_latA mxAt_smul smul_eq_self smul_isHalf' symplO_add_right')
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG hne i hi
  have mxAt_mul_left : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x),
      MxAt P (y ⬝ x) := by
    intro D P a b c y x hx i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

  have mxAt_mul_right : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c),
      MxAt P (x ⬝ y) := by
    intro D P a b c x hx y i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

  have wittExtZero_inclusionX_mem_homLatticeCompletion : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
      {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
      (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T}
      (hw : w ∈ latO S₀ T (LS₀ : Set _) (LT : Set _) (· = v)),
      dS.ext0 T (dT.incX S₀ (dT.pX ⬝ w)) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
    intro D S S₀ T T₀ ρ σ dS dT LS LS₀ LT LT₀ v hS hT hS₀ hmS hmT w hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨?_, fun y hy => ?_⟩
    · rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply]
      exact mxAt_mul_right (mxAt_mul_left _ (mxAt_mul_left _ hx)) _
    · change (dT.jX * (dT.pX * w) * dS.p0) *ᵥ y ∈ latA T LT (· = v)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
      exact jX_pX_mem_latA dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

  have wittExtZero_inclusionX_smul : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (c : AE D)
      (ξ : Mx D σ S₀.rank),
      dS.ext0 T (dT.incX S₀ (c • ξ)) = c • dS.ext0 T (dT.incX S₀ ξ) := by
    intro D S S₀ T T₀ ρ σ dS dT c ξ
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, HypDec.incX_apply, Matrix.mul_smul, Matrix.smul_mul]

  have incAdj_smul : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (c : AE D) (y : Mx D S.rank ρ),
      d.incAdj S (c • y) = cA D c • d.incAdj S y := by
    intro D T T₀ ρ d S c y
    rw [HypDec.incAdj_apply, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incY_apply, adj_smul, Matrix.smul_mul,
      smul_comm (incA D (-D.host.xi0⁻¹)) (cA D c), Matrix.mul_smul]

  have symplO_incAdj_proj : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = symplO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
    intro D T T₀ ρ d S z w
    have key : hO S T (d.incAdj S z) w = hO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
      rw [d.hO_coordT S, d.hO_coordT S]
      simp only [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, HypDec.pX_jY,
        HypDec.p0_jY, HypDec.pY_jY, HypDec.pX_jX, HypDec.p0_jX, HypDec.pY_jX, Matrix.zero_mul, Matrix.one_mul]
      simp [pairT, hO]
    rw [symplO, symplO, key]

  have fix_char : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
      {P : Pl D → Prop} {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)} (h𝔉 : IsFlatBF s P 𝔉) {f : WO B.V J.W → ℂ}
      (hθ : IsThetaFunO ψ B.V J.W f) (t : GL (Fin ρ) (AE D)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
      (ξ : Mx D ρ B.V₀.rank) (hξ : MxAt P ξ) (hfix : heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f = f),
      ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    intro D ψ ρ B J s P 𝔉 h𝔉 f hθ t hne ξ hξ hfix
    have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hθ
    have hact : actO B.V J.W 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) =
        B.d.ext0 J.W (J.d.incX B.V₀ (t.1 ⬝ ξ)) := by
      rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply,
        HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
    have h1 := s.weil.om_heis 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f hθ
    rw [hfix, hact] at h1
    have h3 := h𝔉.Heisenberg₂.iso _ hg (t.1 ⬝ ξ) (mxAt_mul_left _ hξ)
    rw [← h1] at h3
    by_contra hc
    apply hne
    funext w
    have hw := congrFun h3 w
    rw [Pi.smul_apply, smul_eq_mul] at hw
    have h4 : (ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) - 1) *
        𝔉 (s.om (1, J.d.levi t) f) w = 0 := by
      rw [sub_mul, ← hw, one_mul, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)

  have yZero_mul_diag : ∀ {D : D7} (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) (t : Matrix (Fin ρ) (Fin ρ) (AE D))
      (ht : ∀ i j, i ≠ j → t i j = 0) (i : Fin ρ) (hi : i.1 + 1 = ρ),
      yZero S ρ z ⬝ t = t i i • yZero S ρ z := by
    intro D S ρ z t ht i hi
    classical
    have hell : ∀ j : Fin ρ, ell D ρ j = if j = i then 1 else 0 := fun j => by
      by_cases hj : j = i
      · subst hj; simp [ell, hi]
      · have hj' : ¬ (j.1 + 1 = ρ) := fun h => hj (Fin.ext (by omega))
        simp [ell, hj', hj]
    ext k l
    have hy : ∀ j, yZero S ρ z k j = if j = i then -ratV z k else 0 := fun j => by
      simp only [yZero, zEll, Matrix.neg_apply, Matrix.vecMulVec_apply, hell]
      split_ifs <;> simp
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hy l]
    simp only [hy, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hl : l = i
    · subst hl
      rw [ite_eq_left rfl, mul_comm]
    · rw [ite_eq_right hl, ht i l (Ne.symm hl), mul_zero, mul_zero]

  have symplO_incAdj_eq : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = -Algebra.trace (AF D.host.F) (AE D) (z ⬝ (d.pX ⬝ w)).trace := by
    intro D T T₀ ρ d S z w
    rw [symplO_incAdj_proj, GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj]

  have chi_add : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
      (y : Mx D S.rank ρ) (t : Matrix (Fin ρ) (Fin ρ) (AE D)) (ξ₁ ξ₂ : Mx D ρ S.rank),
      ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ (ξ₁ + ξ₂)))) =
        ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₁))) * ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₂))) := by
    intro D ψ T T₀ ρ d S y t ξ₁ ξ₂
    rw [Matrix.mul_add, map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul]

  obtain ⟨hθ, h2, hh⟩ := hf
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨eV, heV_int, heV_act, heV_cA, hhalf⟩ := exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (J.d.incAdj B.V₀ (c • yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun c hc k l => by
      rw [incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)

  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff J.W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt J.W (J.d.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = J.d.pX ⬝ (mt J.W (J.d.levi t) - 1) ⬝ J.d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, J.d.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := mxAt_mul_right (mxAt_mul_left J.d.pX hM) J.d.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hG.last hρ _ ha]
  refine (_root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = J.d.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : B.d.ext0 J.W (J.d.incX B.V₀ ξ) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ wittExtZero_inclusionX_mem_homLatticeCompletion B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hξe : eV • ξ = ξ := smul_eq_self (fun a ha => (mul_comm eV a).trans (heV_act a ha)) hξ

  have hχ : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    rcases hG.tame.2 with h2v | ⟨e, ε, he, hε, hes⟩
    · obtain ⟨c, hcc, hcl⟩ := hhalf h2v
      have hcu := hcl _ _ _ _ _ hu
      rw [← wittExtZero_inclusionX_smul] at hcu
      have hfix := h2 _ hcu
      rw [← map_nsmul (B.d.ext0 J.W), ← map_nsmul (J.d.incX B.V₀)] at hfix
      have h2c : 2 • (c • ξ) = ξ := by
        rw [two_nsmul, add_smul_mx, hcc, hξe]
      rw [h2c] at hfix
      exact fix_char s h𝔉 hθ t hne ξ hξ hfix
    · have hact := (GlobalTheory.FinPl.placeIdem_acts D v ε hε).1
      have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
      have hfixE : ∀ e' : AE D, IsSplitIdem D e' →
          heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ (e' • ξ))) f = f := by
        intro e' he'
        have hmem := GlobalTheory.LatticeStable.smul_mem_latO D B.V J.W _ _ (· = v) e'
          (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he'.1])) _ hu
        rw [← wittExtZero_inclusionX_smul] at hmem
        refine hh e' he' _ hmem ?_
        rw [wittExtZero_inclusionX_smul]
        exact smul_isHalf' he'.1 _
      have hMe : ∀ e' : AE D, MxAt (· = v) (e' • ξ) := fun e' => mxAt_smul e' hξ
      have h1 := fix_char s h𝔉 hθ t hne _ (hMe e) (hfixE e he)
      have h2' := fix_char s h𝔉 hθ t hne _ (hMe (cA D e)) (hfixE _ hce)
      have hsum : e • ξ + cA D e • ξ = ξ := by
        rw [add_smul_mx, hes]
        exact smul_eq_self (fun a ha => (hact a).1 ha) hξ
      have hk := chi_add ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) t.1 (e • ξ) (cA D e • ξ)
      rw [hsum, h1, h2', mul_one] at hk
      exact hk
  have hε' := (_root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ heV_id)).1
    ((hG.last hρ eV heV_id).2 heV_int) u' hu'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, ← Matrix.mul_smul, hξe] at hε'
  have hχ' := hχ
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at hχ'
  have hT : ψ (Algebra.trace (AF D.host.F) (AE D) (yZero B.V₀ ρ (vecB B.o B.ζ) ⬝ ξ).trace) = 1 := by
    rw [AddChar.map_neg_eq_inv] at hε'
    exact inv_eq_one.1 hε'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul, map_sub, neg_sub,
    sub_eq_add_neg, AddChar.map_add_eq_mul, hT, hχ', one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLoc

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : latO S T LS LT Q ≤ latO S T LS LT P := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hvan, rest⟩
  exact ⟨α, hα, fun v hv => hvan v fun hq => hv (h v hq), rest⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem pairA_add (a b : Af D.host.F) :
    pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b := by
  show ((0 : Ainf D.host.F), a + b) = ((0 : Ainf D.host.F), a) + ((0 : Ainf D.host.F), b)
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem pairA_zero : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl


open Classical in
theorem latVac_of_places (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hv : ∀ v, P v → Vac ψ S T LS LT (· = v) f) :
    IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f := by

  have one : ∀ (v : Pl D) (w : WO S T), w ∈ latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) →
      (heisO ψ S T (2 • w) f = f) ∧ ∀ e, IsSplitIdem D e → IsHalf e w → heisO ψ S T w f = f := by
    intro v w hw
    by_cases hP : P v
    · have hw' : w ∈ latO S T (LS : Set _) (LT : Set _) (· = v) :=
        latO_mono S T _ _ (fun v' h => h.2) hw
      exact ⟨(hv v hP).2.1 w hw', fun e he hh => (hv v hP).2.2 e he w hw' hh⟩
    · have h0 : w = 0 := ((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ _ w hw).2.2.2 fun v' h => hP (h.2 ▸ h.1)
      subst h0
      simp [heisO_zero]
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨U, hUo, hU⟩ := hf.level
    have h2u : 2 • u ∈ latO S T (LS : Set _) (LT : Set _) P := AddSubgroup.nsmul_mem _ hu 2
    obtain ⟨s, hs⟩ := (_root_.GlobalTheory.LatLevel.smul_mem_open_of_vanish) D S T _ _ P U hUo (2 • u) h2u
    have key : ∀ t : Finset (Pl D), t ⊆ s →
        heisO ψ S T (pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) • (2 • u)) f = f := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        have hγ : ∀ v ∈ s, evalV D.host.F v (indP D (↑(s \ ∅) : Set (Pl D))ᶜ) = 0 := by
          intro v hv; rw [evalV_indP]; simp [hv]
        have hm := hs _ (indicatorAdele_mem_integralAdeles _) hγ
        have hl := ((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ P _ h2u).1 _ (indicatorAdele_mem_integralAdeles ((↑(s \ ∅) : Set (Pl D))ᶜ))
        exact hU _ hm (((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ _ _ hl).2.2.1)
      | insert v t hvt ih =>
        intro hts
        have hvs : v ∈ s := hts (Finset.mem_insert_self v t)
        have ih' := ih (fun x hx => hts (Finset.mem_insert_of_mem hx))
        have hset : ((↑(s \ insert v t) : Set (Pl D))ᶜ) = {v} ∪ (↑(s \ t) : Set (Pl D))ᶜ := by
          ext x; simp only [Set.mem_compl_iff, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
            Finset.mem_insert, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · intro h; by_cases hx : x = v; · exact Or.inl hx
            right; intro h'; exact h ⟨h'.1, fun h'' => h''.elim hx h'.2⟩
          · rintro (rfl | h) h'; · exact h'.2 (Or.inl rfl)
            exact h ⟨h'.1, fun h'' => h'.2 (Or.inr h'')⟩
        have hdisj : Disjoint ({v} : Set (Pl D)) (↑(s \ t) : Set (Pl D))ᶜ := by
          rw [Set.disjoint_singleton_left]; simp [hvs, hvt]
        rw [hset, ← indicatorAdele_union_of_disjoint hdisj, pairA_add, add_smul]
        have hprod : pairA D.host.F 0 (indP D {v}) * pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) = 0 := by
          rw [pairA_mul, indicatorAdele_singleton_mul_singleton, Set.disjoint_iff_inter_eq_empty.mp hdisj, indicatorAdele_empty, pairA_zero]
        rw [(_root_.GlobalTheory.HeisDisj.heisO_smul_add_smul) D ψ S T _ _ _ _ f hprod, ih']
        have hw := ((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ P u hu).1 _ (indicatorAdele_mem_integralAdeles {v})
        have hw' : pairA D.host.F 0 (indP D {v}) • u ∈
            latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) := by
          refine latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw
          by_contra hne; apply h.2; rw [evalV_indP]; simp [hne]
        rw [smul_comm]
        exact (one v _ hw').1
    have := key s (subset_refl s)
    rwa [Finset.sdiff_self, Finset.coe_empty, Set.compl_empty, indicatorAdele_univ,
      ((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ P _ h2u).2.1] at this
  · intro e he u hu hh
    obtain ⟨hee, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he
    have hα : α ∈ intAf D.host.F := by
      intro v'; by_cases h : v' = v
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfix : pairA D.host.F 0 α • u = u := by
      ext i j
      show pairA D.host.F 0 α • u i j = u i j
      rw [Algebra.smul_def, ← hsum, ← hh i j, ← mul_assoc, add_mul, hee, mul_comm (cA D e) e, hec, add_zero]
    have hw := ((_root_.GlobalTheory.FinPl.latO_algebra) D S T _ _ P u hu).1 α hα
    rw [hfix] at hw
    refine (one v u (latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw)).2 e
      ⟨hee, hec, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩ hh
    by_contra hne; exact h.2 (hα0 v' hne)

theorem vac_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v) → ∀ f, (Vac ψ S T LS LT P f ↔ IsThetaFunO ψ S T f ∧ ∀ v, P v → Vac ψ S T LS LT (· = v) f) ∧ (Vac ψ S T LS LT P f → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, Vac ψ S T LS LT P (om (g, h) f)) ∧ (Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f)) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P _ f
  refine ⟨⟨fun h => ⟨h.1, fun v hv => ⟨h.1, ?_, ?_⟩⟩, fun h => ⟨h.1, latVac_of_places ψ S T LS LT P f h.1 h.2⟩⟩, ?_, ?_⟩
  · exact fun u hu => h.2.1 u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · exact fun e he u hu => h.2.2 e he u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · intro h g hg k hk
    exact (_root_.GlobalTheory.VacMove.vac_of_moves) D ψ S T χS χT om hW LS LT hLS hLT P f h g k LS LT hLS hLT
      ((_root_.GlobalTheory.fixes_latV_of_mem_grpOff) D S LS P g hg) ((_root_.GlobalTheory.fixes_latV_of_mem_grpOff) D T LT P k hk)
  · intro h g k MS MT hMS hMT hg hk
    exact (_root_.GlobalTheory.VacMove.vac_of_moves) D ψ S T χS χT om hW LS LT hLS hLT P f h g k MS MT hMS hMT hg hk

end GlobalTheory.VacLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TensSB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type}

theorem of_tensCol_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (ha : a ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, a y₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact ha (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => x.submatrix id Sum.inl) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (a y₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j) := by
      funext x₀
      show Ψ x₀ = (a y₀)⁻¹ * (Ψ x₀ * a y₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

theorem of_tensRow_mem {Ψ : Matrix n n' k → ℂ} {b : (n' → k) → ℂ}
    (h : tensRow Ψ b ∈ SB (Matrix (n ⊕ Fin 1) n' k)) (hb : b ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, b η₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hb (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i)
    (s := fun x : Matrix (n ⊕ Fin 1) n' k => x.submatrix Sum.inl id) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (b η₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensRow Ψ b (Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i) := by
      funext x₀
      show Ψ x₀ = (b η₀)⁻¹ * (Ψ x₀ * b η₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

end GlobalTheory.FinPl.TensSB

namespace GlobalTheory.FinPl

theorem tens_SB_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k) → a ≠ 0 → Ψ ∈ SB (Matrix n n' k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), Ψ ∈ SB (Matrix n' n k) → b ∈ SB (n → k) → tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k) → b ≠ 0 → Ψ ∈ SB (Matrix n' n k)) := by
  intro k _ _ _ _ n n' _ _ _ _
  exact ⟨fun Ψ a hΨ ha => Comm.tensCol_mem hΨ ha, fun Ψ a h ha => TensSB.of_tensCol_mem h ha,
    fun Ψ b hΨ hb => Comm.tensRow_mem hΨ hb, fun Ψ b h hb => TensSB.of_tensRow_mem h hb⟩

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.FinPlLoc Filter Topology
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PsiUnit

variable {D : D7}


open Formalism.IndefR.Fin.LevelGroupLemmas in
theorem char_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (t : AF D.host.F)
    (ht : fstA D.host.F t = 0) (h : ∀ v : Pl D, ψ (pairA D.host.F 0 (ePl D (· = v)) * t) = 1) : ψ t = 1 := by
  classical
  have h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]
    | insert v A hv ih =>
      have e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v)) := by
        unfold idemS
        rw [← pairA_add]
        congr 1
        refine RestrictedProduct.ext _ _ fun w => ?_
        change evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))
        rw [map_add (f := _), evalV_sglS, evalV_sglS, evalV_ePl]
        by_cases hw : w = v
        · subst hw; simp [hv]
        · simp [hw]
      rw [e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]
  have h2 := (hψ.tendsto 0).comp (tendsto_AF t ht)
  rw [AddChar.map_zero_eq_one] at h2
  refine tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)
  have e : t = idemS A * t + (1 - idemS A) * t := by ring
  change ψ ((1 - idemS A) * t) = ψ t
  conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]

theorem trace_idem (Q : Pl D → Prop) (s : AE D) : Algebra.trace (AF D.host.F) (AE D) (idem D Q * s) =
    pairA D.host.F 0 (ePl D Q) * Algebra.trace (AF D.host.F) (AE D) s := by
  rw [← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]
  rfl

theorem psiE_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) {P : Pl D → Prop} {s : AE D}
    (hs : s ∈ idAt D P) (h : ∀ v, P v → psiE ψ (idem D (· = v) * s) = 1) : psiE ψ s = 1 := by
  refine char_eq_one_of_local ψ hψ _ ?_ fun v => ?_
  · rw [← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]
    exact zero_mul _
  · rw [← trace_idem]
    by_cases hv : P v
    · exact h v hv
    · have h0 : idem D (· = v) * s = 0 := by
        refine (mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)
        exact compAt_of_idAt hs (by rw [w.2]; exact hv)
      rw [h0]
      exact psiE_zero ψ

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) : latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, h1, h2, h3⟩
  exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩

theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.FinPl.PsiUnit

end
end

