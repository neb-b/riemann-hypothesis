module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponent
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
open IsDedekindDomain GlobalTheory.LamT GlobalTheory.KeyFourth
open GlobalTheory.AllWt

namespace GlobalTheory.KeyPowTw

theorem exists_twSec_key (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (K : (Rul Xo c)ˣ) (C : (c.F →+* ℂ) → ℝ) (hP : HasPts U Z) (hks : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hpq : 1 ≤ Dw.p + Dw.q) (hKmem : (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw)) (hCpos : ∀ σ, 0 < C σ) (hCeq : ∀ σ, ∀ k, ∀ y ∈ ((U (goodOf c σ)).X k).dom, homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C σ) (hval : ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal)) :
    ∃ t : TwSec U x Z (wtOf Dw 0 (-4)), (∀ w, t.lo w = 0) ∧ ∀ σ, t.cInf σ = C σ := by
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · show (2 * (-4) : ℤ) = 4 * (-2)
      norm_num
    · show (wtOf Dw 0 (-4)).1 (τ, (i : ℕ)) = 4 * 1
      rw [hwt (-4) τ i i.2]; norm_num
  have hadd : wtOf Dw 0 (-4) + wtOf Dw 0 4 = 0 := by
    rw [← wtOf_add, add_zero, neg_add_cancel, wtOf_zero]
  have hneg : -wtOf Dw 0 (-4) = wtOf Dw 0 4 := neg_eq_of_add_eq_zero_right hadd
  have hi := idem_mul_idem Z
  set s : Rul Xo c := idem Z * (K : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-4))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hKmem
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex, ← exZ_neg_eq, hneg] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hss' : s * s' = idem Z := by rw [hs, hs', mul_mul_mul_comm, hi, Units.mul_inv, mul_one]
  have hnorm : ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z,
      homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ ∧ homN (U (goodOf c σ)) x (wtOf Dw 0 4) s' z = (C σ)⁻¹ := by
    intro σ z hz
    obtain ⟨hd, hl⟩ := hz
    have h1 := homN_idem (U (goodOf c σ)) x hd hl ((hP.1 σ).2 z ⟨hd, hl⟩ hd)
    have hm : ∀ (m m' : ℤ) (f g : Rul Xo c), homN (U (goodOf c σ)) x (wtOf Dw 0 (m + m')) (f * g) z =
        homN (U (goodOf c σ)) x (wtOf Dw 0 m) f z * homN (U (goodOf c σ)) x (wtOf Dw 0 m') g z := fun m m' f g => by
      rw [← homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) f g z hd, ← wtOf_add, add_zero]
    rw [← wtOf_zero (Dw := Dw)] at h1
    have h2 : homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ := by
      have := hm 0 (-4) (idem Z) K
      rw [zero_add, h1, one_mul] at this
      rw [hs, this, hCeq σ z.1 z.2 hd]
    refine ⟨h2, ?_⟩
    have h5 := hm (-4) 4 s s'
    rw [hss', neg_add_cancel, h1, h2] at h5
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h5.symm)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-4)) s z ≤ D := by
    intro σ hσ
    refine ⟨C σ, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 4) s' z ≤ D := by
    intro σ hσ
    refine ⟨(C σ)⁻¹, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hvs : ∀ w, ∀ v ∈ valOn Z w, v s = v (K : Rul Xo c) := fun w v hv => by
    rw [hs, (isVal_valOn hv).mul, val_idem hv, zero_add]
  let t : TwSec U x Z (wtOf Dw 0 (-4)) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by rw [← exZ_neg_eq, hneg]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, hi]
      idem_inv := by rw [hs', ← mul_assoc, hi]
      mul_inv := hss'
      cInf := C
      cInf_pos := hCpos
      norm_inf := fun σ z hz => (hnorm σ z hz).1
      cusp_sig := fun G hG f hf =>
        _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 (-4)) s hks hU hpq (even_wtOf _ _) (hmono (-4)) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 4) s' hks hU hpq (even_wtOf _ _) (hmono 4)
          hsm' hsupp' hbd' (G + wtOf Dw 0 (-4)) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun _ => 0
      hi := fun w => 4 * B w
      lo_le := fun w v hv => by
        rw [hvs w v hv]; exact_mod_cast (hval w v (valOn_subset Z w hv)).1
      le_hi := fun w v hv => by
        rw [hvs w v hv]; exact (hval w v (valOn_subset Z w hv)).2
      finite_lo := by simp
      finite_hi := by
        refine (Set.finite_iUnion fun τ => finite_ord (embF c τ)).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, Set.mem_iUnion, not_exists, not_not] at hn
        apply hw
        simp [B, hn]
      pts := hP }
  exact ⟨t, fun _ => rfl, fun _ => rfl⟩

theorem exists_twSec_keyPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := _root_.GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := _root_.GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => _root_.GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨ρ⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hpsi : Nat.card (Psi H) = Module.finrank ℚ E / 2 := GlobalTheory.PeriodCoord.card_cmType H
  have hCb : ∀ σ, Real.log (C σ) ≤ 2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi) :=
    fun σ => by rw [hpsi, hgE]; exact (abs_le.1 (hClog σ)).2
  refine ⟨⟨ρ⟩, fun Z m => ?_⟩
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := exists_twSec_key E H Dw l Xo c r U x Z K C hP ⟨ρ⟩ hU hpq hKmem hCpos hCeq hval
  induction m with
  | zero =>
    have h0 : (0 : WTZ E) = wtOf Dw 0 (-(4 * ((0 : ℕ) : ℤ))) := by simp [wtOf_zero]
    obtain ⟨-, h2, h3, -, -⟩ := TwSec.const_spec (x := x) hP 1 one_ne_zero
    refine ⟨(TwSec.const x hP 1 one_ne_zero).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ (TwSec.const x hP 1 one_ne_zero).lo w
      rw [h3]; simp [vAdd]
    · show Real.log ((TwSec.const x hP 1 one_ne_zero).cInf σ) ≤ _
      rw [h2]; simp
  | succ m ih =>
    obtain ⟨t, htlo, htc⟩ := ih
    have h0 : wtOf Dw 0 (-(4 * (m : ℤ))) + wtOf Dw 0 (-4) = wtOf Dw 0 (-(4 * ((m + 1 : ℕ) : ℤ))) := by
      rw [← wtOf_add, add_zero]; congr 1; push_cast; ring
    refine ⟨(t.mul t₁).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ t.lo w + t₁.lo w
      rw [ht₁lo]; linarith [htlo w]
    · show Real.log (t.cInf σ * t₁.cInf σ) ≤ _
      rw [Real.log_mul (t.cInf_pos σ).ne' (t₁.cInf_pos σ).ne', ht₁c]
      have h1 := htc σ
      have h2 := hCb σ
      push_cast at h1 h2 ⊢
      linarith

end GlobalTheory.KeyPowTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearForm
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_lie_comp_psi_eq :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c := by
  intro p _ R _ N hN A _ hab hLE hN' G t ψ hψ l
  obtain ⟨N', hc⟩ := hN'
  let h : HdR A := l ∘ₗ Submodule.projectionOnto (PrimitiveSubmodule A) N' hc
  obtain ⟨v, hv, -⟩ := hLE.1 h
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x, hx, -⟩ := t.existsUnique_lieCorr hv.1
  refine ⟨x, fun c => ?_⟩
  obtain ⟨⟨c, hc1⟩, hc2⟩ := c
  have hc3 : c ∈ F1 (A.hom ≫ 𝟙 _) := hc2
  rw [hodgeFiltration_eq_range] at hc3
  obtain ⟨β, rfl⟩ := hc3
  rw [GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent p R N hN A hab G t ψ hψ β hc1 hc2 x v hx, ← hv.2 β hc1]
  change l (Submodule.projectionOnto (PrimitiveSubmodule A) N' hc ⟨_, hc1⟩) = _
  exact congrArg l (Submodule.projectionOnto_apply_left hc ⟨⟨_, hc1⟩, hc2⟩)

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing

theorem GlobalTheory.HTSummand.Corep.mat_sum (n : ℕ) (α : Type) [CommRing α] : ∑ i : Fin n, Matrix.single i i (1:α) = 1 := by
  ext a c
  rw [Matrix.sum_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.single_apply, hb]) (by simp)]
    simp [Matrix.single_apply]
  · exact Finset.sum_eq_zero fun x _ => by
      simp only [Matrix.single_apply]; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

theorem GlobalTheory.HTSummand.Corep.mat_sand (n : ℕ) (α : Type) [CommRing α] (i j z : Fin n) (M : Matrix (Fin n) (Fin n) α) :
    Matrix.single z i 1 * M * Matrix.single j z 1 = Matrix.scalar _ (M i j) * Matrix.single z z 1 := by
  rw [Matrix.single_mul_mul_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single,
    smul_eq_mul, _root_.mul_one, _root_.mul_one, _root_.one_mul]

theorem GlobalTheory.HTSummand.Corep.exists_summand_lie_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ hP e he heρ _heω F hIF hFρ hFe hcompl hLie
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (p : C) ^ k = 0 := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have : (p : C) ^ k ∈ (maximalIdeal C) ^ k := Ideal.pow_mem_pow hp k
    rw [hk] at this; simpa using this
  obtain ⟨Ψ, hΨρ, hΨc, hΨN, hΨs⟩ := GlobalTheory.T.exists_matrixAction_of_padicOrderSplitting p D C k hk H ρ D.splitP.some
  haveI : NeZero D.m := ⟨D.m_pos.ne'⟩
  let σ : 𝓞 D.F →+* Module.End C H := ρ.comp (algebraMap (𝓞 D.F) D.O)
  let χ : Fin D.a → 𝓞 D.F →+* C := fun i => tR.comp (b.t i)
  let E : Fin D.m → Fin D.m → Module.End C H := fun i j => Ψ (Matrix.single i j 1)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    simp only [E, ← map_mul]
    split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, _root_.mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  have hsum : ∑ i, E i i = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, ← map_sum, GlobalTheory.HTSummand.Corep.mat_sum, map_one]
  have hρσ : ∀ c c', ρ c' * σ c = σ c * ρ c' := by
    intro c c'
    show ρ c' * ρ (algebraMap _ _ c) = ρ (algebraMap _ _ c) * ρ c'
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hEσ : ∀ i j c, E i j * σ c = σ c * E i j := fun i j c => hΨc (σ c) (hρσ c) _
  have hEe : ∀ i j, E i j * e = e * E i j := fun i j => hΨc e heρ _
  have hFE : ∀ i j, ∀ x ∈ F, E i j x ∈ F := fun i j => hΨN F hFρ _
  have hθ : ∀ (c : D.O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x →
      E 0 i (ρ c (E j 0 x)) ∈ N := by
    intro c i j N hN x hx h0
    have : E 0 i (ρ c (E j 0 x)) = Ψ (Matrix.scalar _ (D.splitP.some (c ⊗ₜ 1) i j)) (E 0 0 x) := by
      rw [← hΨρ c]
      show (Ψ (Matrix.single 0 i 1) * Ψ _ * Ψ (Matrix.single j 0 1)) x = _
      rw [← map_mul, ← map_mul, GlobalTheory.HTSummand.Corep.mat_sand, map_mul]; rfl
    rw [this, h0]
    exact hΨs _ N (fun a x hx => hN a x hx) x hx
  let π : Module.End C H := E 0 0 * e
  have hππ : π * π = π := by
    show E 0 0 * e * (E 0 0 * e) = E 0 0 * e
    rw [_root_.mul_assoc, ← _root_.mul_assoc e, ← hEe, _root_.mul_assoc, he, ← _root_.mul_assoc, hE]; simp
  have hπσ : ∀ c, σ c * π = π * σ c := by
    intro c
    show σ c * (E 0 0 * e) = E 0 0 * e * σ c
    have h1 : e * σ c = σ c * e := (heρ _).symm
    rw [_root_.mul_assoc, h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hEσ]
  have hFπ : ∀ x ∈ F, π x ∈ F := fun x hx => hFE 0 0 _ (hFe x hx)
  have hFσ : ∀ c, ∀ x ∈ F, σ c x ∈ F := fun c x hx => hFρ _ x hx
  have hπapp : ∀ c x, σ c (π x) = π (σ c x) := fun c x => LinearMap.congr_fun (hπσ c) x
  have hLieπ : ∀ d ∈ LinearMap.range π, ∃ w : Fin D.a → H,
      (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨x, rfl⟩
    have hde : π x ∈ LinearMap.range e := by
      refine ⟨π x, ?_⟩
      show e (E 0 0 (e x)) = E 0 0 (e x)
      rw [← Module.End.mul_apply, ← hEe, Module.End.mul_apply, ← Module.End.mul_apply e e, he]
    obtain ⟨w, hw1, hw2⟩ := hLie _ hde
    refine ⟨fun i => π (w i), fun i c => ?_, ?_⟩
    · have := hFπ _ (hw1 i c)
      rw [map_sub, map_smul] at this
      rw [hπapp]; exact this
    · have := hFπ _ hw2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, ← Module.End.mul_apply π π, hππ] at this
      exact this
  have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤ := by
    intro i j hij
    have h2 : Ideal.map tR (Ideal.span (Set.range fun x => b.t i x - b.t j x)) = ⊤ := by
      rw [b.comax i j hij, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at h2
    simpa [Function.comp_def, χ] using h2
  obtain ⟨n, κ, ℓ, y, h1, h2, h3, h4⟩ := _root_.GlobalTheory.exists_eigen_coordinates_range_quot I hI σ D.a χ hcomax π hππ hπσ F hIF hFσ hFπ hcompl hLieπ
  obtain ⟨G₀, M₀, g1, g2, g3, g4, g5⟩ := GlobalTheory.T.exists_sigmaStable_summand_from_lifted_eigenCoords I hI σ hP D.a χ π hππ hπσ F hIF n κ ℓ y h1 h2 h3 h4
  exact GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition I D.m E hE hsum σ hEσ ρ hθ e he hEe F hIF hFE hFe D.a χ G₀ M₀ g1 g2 g3 g4 g5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion
section
open IsLocalRing GlobalTheory.Poinc.Eq8
open scoped TensorProduct

namespace GlobalTheory.TraitLift

theorem exists_lift_adicCompletion (A V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra A V] :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V')
      (g : AdicCompletion (maximalIdeal A) A →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      g.comp (algebraMap A _) = h.comp (algebraMap A V) ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  let R := AdicCompletion (maximalIdeal A) A
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let C := V ⊗[A] R
  let e : (C ⧸ (maximalIdeal V).map (algebraMap V C)) ≃+* R ⊗[A] (V ⧸ maximalIdeal V) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal V)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A V V (V ⧸ maximalIdeal V) R).toRingEquiv).trans
      (Algebra.TensorProduct.comm A _ _).toRingEquiv
  haveI := formalFibre_isReduced_of_field A (V ⧸ maximalIdeal V)
  haveI : Nontrivial (R ⊗[A] (V ⧸ maximalIdeal V)) := inferInstance
  obtain ⟨V', i1, i2, i3, h₀, hc, hirr⟩ := GlobalTheory.ReducedFibre.exists_cdvr_of_flat_of_isReduced V C
    e.toEquiv.nontrivial (isReduced_of_injective e e.injective)
  refine ⟨V', i1, i2, i3, h₀.comp (algebraMap V C),
    h₀.comp (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).toRingHom, hc, ?_, hirr⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).commutes a

theorem isLocalHom_and_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] (h : V →+* V') (hh : ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ)) :
    Function.Injective h ∧ IsLocalHom h := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine ⟨(injective_iff_map_eq_zero h).mpr fun x hx => ?_, ⟨fun x hx => ?_⟩⟩
  · by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map h).ne_zero (pow_ne_zero n (hh ϖ hϖ).ne_zero) hx
  · by_contra hu
    have hm : x ∈ maximalIdeal V := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact (hh ϖ hϖ).not_isUnit (isUnit_of_dvd_unit (map_dvd h hm) hx)

theorem exists_lift_of_isCpl : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R] (j : A →+* R), IsCpl j → ∀ [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : A →+* V), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V') (g : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective h ∧ IsLocalHom h ∧ g.comp j = h.comp f ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  intro A R V _ _ _ _ j hj _ _ _ f
  obtain ⟨e, he⟩ := hj
  letI : Algebra A V := f.toAlgebra
  obtain ⟨V', i1, i2, i3, h, g, hc, hcomp, hirr⟩ := exists_lift_adicCompletion A V
  obtain ⟨hinj, hloc⟩ := isLocalHom_and_injective h hirr
  refine ⟨V', i1, i2, i3, h, g.comp e.symm.toRingHom, hc, hinj, hloc, ?_, hirr⟩
  ext a
  have := RingHom.congr_fun hcomp a
  simp only [RingHom.comp_apply] at this ⊢
  rw [← he a]
  simpa [RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.TraitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_point_finite_surjective : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (y : Sp K ⟶ X) (q : Y ⟶ X), IsFinite q → Surjective q → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (y' : Sp L ⟶ Y), y' ≫ q = spMap (algebraMap K L) ≫ y := by
  intro K _ X Y y q hq hs
  haveI := hq
  haveI := hs
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd q y).surjective x
  let pt : PrimeSpectrum Γ(pullback q y, ⊤) := e.hom.base p
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal pt.asIdeal pt.isPrime.ne_top
  let L := Γ(pullback q y, ⊤) ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ψ : K →+* L := (Ideal.Quotient.mk m).comp φ.hom
  letI : Algebra K L := ψ.toAlgebra
  have hψ : ψ.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hfin
  haveI : FiniteDimensional K L := hψ
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ e.inv ≫ pullback.fst q y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hφ,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoordsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  first | exact @GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | exact GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | (intros; apply GlobalTheory.LogPole.CellBir.exists_isOpenImmersion <;> assumption)
end

