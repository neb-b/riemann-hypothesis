module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Mathlib
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent
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

namespace GlobalTheory.KeyTwDeep


open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyRootTw in
theorem twSec_keyRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) →
    FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ Z : Comp Xo c, Nonempty (TwSec U x Z (wtOf Dw 0 1)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := _root_.GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := _root_.GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => _root_.GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  intro Z
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  exact ⟨t⟩

end GlobalTheory.KeyTwDeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAevalTraceFormLeFibreValues
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

variable {K : Type} [Field K] {D : ℕ}

theorem ratR_zero_eq_closure (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) :
    ratR x 0 = Subring.closure (Set.range fun j : Fin D => x j.succ / x 0) := by
  refine le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_mono ?_)
  · rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [div_self h0]; exact Subring.one_mem _
    · exact Subring.subset_closure ⟨i, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem ratR_zero_le_ratF (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) : ratR x 0 ≤ (ratF x).toSubring := by
  rw [ratR_zero_eq_closure x h0]
  exact Subring.closure_le.2 fun _ h => Subfield.subset_closure h

theorem exists_ringEquiv_ratR (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0)
    (hind : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    ∃ e : MvPolynomial (Fin D) ℤ ≃+* ratR x 0, ∀ j, (e (X j) : K) = x j.succ / x 0 := by
  have hS : (Algebra.adjoin ℤ (Set.range fun j : Fin D => x j.succ / x 0)).toSubring = ratR x 0 := by
    rw [Algebra.adjoin_int, ratR_zero_eq_closure x h0]; rfl
  refine ⟨hind.aevalEquiv.toRingEquiv.trans (RingEquiv.subringCongr hS), fun j => ?_⟩
  have := hind.algebraMap_aevalEquiv (X j)
  rw [aeval_X] at this
  exact this

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp


set_option maxHeartbeats 1000000 in
theorem norm_aeval_trace_le : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) →
    ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ),
    (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T →
    ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 →
    (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) →
    ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  intro K _ _ D x hx hind hfin B hB hint w T htr z M hz0 hM
  have h0 := hx 0
  have hAF := ratR_zero_le_ratF x h0
  have memA : ∀ l, x l / x 0 ∈ ratR x 0 := fun l => Subring.subset_closure ⟨l, rfl⟩
  have hAB : ratR x 0 ≤ B := Subring.closure_le.2 (by rintro _ ⟨l, rfl⟩; exact hB l)
  letI : Algebra (ratR x 0) (ratF x) := (Subring.inclusion hAF).toAlgebra
  letI : Algebra (ratR x 0) B := (Subring.inclusion hAB).toAlgebra
  haveI : IsScalarTower (ratR x 0) (ratF x) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ratR x 0) B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨e, he⟩ := exists_ringEquiv_ratR x h0 hind
  haveI : UniqueFactorizationMonoid (ratR x 0) := e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have hinjF : Function.Injective (algebraMap (ratR x 0) (ratF x)) := Subring.inclusion_injective hAF
  have hinjB : Function.Injective (algebraMap (ratR x 0) B) := Subring.inclusion_injective hAB
  haveI : FaithfulSMul (ratR x 0) (ratF x) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinjF
  haveI : IsFractionRing (ratR x 0) (ratF x) := by
    refine IsFractionRing.of_field _ _ fun y => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 y.2
    rw [← ratR_zero_eq_closure x h0] at ha hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext (by rw [Subfield.coe_div]; exact hab.symm)⟩
  have hwint : IsIntegral (ratR x 0) (w : K) := hint w w.2
  have hmin : minpoly (ratF x) (w : K) = (minpoly (ratR x 0) (w : K)).map (algebraMap (ratR x 0) (ratF x)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (ratF x) hwint
  have hminB : minpoly (ratR x 0) w = minpoly (ratR x 0) (w : K) :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective w).symm
  haveI : Algebra.IsIntegral (ratR x 0) B :=
    ⟨fun b => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective).1 (hint b b.2)⟩
  set p := minpoly (ratR x 0) (w : K) with hp
  have hpm : p.Monic := minpoly.monic hwint

  obtain ⟨m, htr', hmdeg⟩ : ∃ m : ℕ, Algebra.trace (ratF x) K (w : K) = m * -(minpoly (ratF x) (w : K)).nextCoeff ∧
      m * (minpoly (ratF x) (w : K)).natDegree = Module.finrank (ratF x) K :=
    ⟨_, trace_eq_finrank_mul_minpoly_nextCoeff (ratF x) (w : K), by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite (ratF x) (w : K)), mul_comm,
        Module.finrank_mul_finrank]⟩
  rw [hmin, hpm.natDegree_map] at hmdeg
  set c : ratR x 0 := m * -p.nextCoeff with hc
  have hcF : Algebra.trace (ratF x) K (w : K) = algebraMap (ratR x 0) (ratF x) c := by
    rw [htr', hmin, Polynomial.nextCoeff_map hinjF, hc, map_mul, map_neg, map_natCast]
  rw [hcF] at htr

  let a : Fin (D + 1) → ratR x 0 := fun l => ⟨x l / x 0, memA l⟩
  have hcT : c = aeval a T := by
    apply Subtype.val_injective
    refine htr.trans ?_
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a (ratR x 0).subtype.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    exact this.symm

  let ψ : ratR x 0 →+* ℂ := (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) fun j : Fin D => z j.succ).comp e.symm.toRingHom
  have hψ : ∀ l, ψ (a l) = z l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · have : a 0 = 1 := Subtype.ext (div_self h0)
      rw [this, map_one, hz0]
    · have : a j.succ = e (X j) := Subtype.ext (he j).symm
      rw [this]
      show MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : Fin D => z j.succ) (e.symm (e (X j))) = _
      rw [RingEquiv.symm_apply_apply, eval₂Hom_X']
  have hψc : ψ c = aeval z T := by
    rw [hcT]
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a ψ.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    refine this.trans ?_
    rw [show (fun i => ψ.toIntAlgHom (a i)) = z from funext fun l => hψ l]

  set q := p.map ψ with hq
  have hqm : q.Monic := hpm.map ψ
  have hsum : q.nextCoeff = -q.roots.sum :=
    (IsAlgClosed.splits q).nextCoeff_eq_neg_sum_roots_of_monic hqm
  have hqn : q.nextCoeff = ψ p.nextCoeff :=
    Polynomial.nextCoeff_map_of_leadingCoeff_ne_zero ψ (by rw [hpm.leadingCoeff, map_one]; exact one_ne_zero)
  have hcard : q.roots.card = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hpm.natDegree_map]
  have hroots : ∀ r ∈ q.roots, ‖r‖ ≤ M := by
    intro r hr
    have hr' : ((minpoly (ratR x 0) w).map ψ).IsRoot r := by
      rw [hminB]; exact (Polynomial.mem_roots hqm.ne_zero).1 hr
    obtain ⟨φ, hφ, hφw⟩ := (GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom (ratR x 0) B hinjB w ψ r).1 hr'
    rw [← hφw]
    refine hM φ fun l => ?_
    rw [← hψ l, ← hφ]
    rfl
  have hval : aeval z T = (m : ℂ) * q.roots.sum := by
    rw [← hψc, hc, map_mul, map_neg, map_natCast, ← hqn, hsum, neg_neg]
  rw [hval, norm_mul, Complex.norm_natCast, ← hmdeg, Nat.cast_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_multiset_sum_le _).trans ?_
  refine (Multiset.sum_le_card_nsmul _ M fun y hy => ?_).trans ?_
  · obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    exact hroots r hr
  · rw [Multiset.card_map, hcard, nsmul_eq_mul]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

variable {R : Type} [CommRing R] [IsDomain R]

theorem famMapTw_trPt (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {b b' : TF (R := R) (Kb R) ⟶ D.P.A}
    (hb : twF ρ ≫ b = b') : famMapTw D ρ ≫ DegPre.trPt D (Kb R) b = DegPre.trPt D (Kb R) b' ≫ famMapTw D ρ := by
  subst hb
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt]
  · simp [DegPre.trPt, padd, comp_lift_assoc]

theorem zF_famMapTw (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) :
    DegPre.zF D (Kb R) ≫ famMapTw D ρ = twF ρ ≫ DegPre.zF D (Kb R) := by
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem famMapTw_famφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) (β : D.X) (i : Fin 4) :
    (famMapTw D ρ).left ≫ DegPre.famφ D (Kb R) β i = DegPre.famφ D (Kb R) β i :=
  (famφ_famMap D (Kb R) (TwF ρ) β i).symm

theorem famMapTw_phiφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {y y₀ : D.X} (α : D.X)
    {b b₀ : TF (R := R) (Kb R) ⟶ D.P.A} (hy : y₀ = y) (hb : twF ρ ≫ b₀ = b) :
    (fun k => (famMapTw D ρ).left ≫ DegPre.phiφ D (Kb R) y₀ α b₀ k) = DegPre.phiφ D (Kb R) y α b := by
  subst hy
  funext k
  rcases k with i | i
  · exact famMapTw_famφ D ρ _ i
  · show (famMapTw D ρ).left ≫ (DegPre.trPt D (Kb R) b₀).left ≫ DegPre.famφ D (Kb R) α i =
      (DegPre.trPt D (Kb R) b).left ≫ DegPre.famφ D (Kb R) α i
    rw [← Category.assoc, ← Over.comp_left, famMapTw_trPt D ρ hb, Over.comp_left, Category.assoc,
      famMapTw_famφ]

theorem twF_left (ρ : Kb R →ₐ[FractionRing R] Kb R) : (twF ρ).left = spMap ρ.toRingHom := rfl

end GlobalTheory.Mum.Conj.PhiTw

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

theorem phiRel_famTw : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N),
    PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  intro R _ _ D N τ p p₀ h w s s' H α u hu hu0
  have hL := D.P.isLB
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  let σ : Kb R →ₐ[FractionRing R] Kb R := (e.symm : Kb R →ₐ[FractionRing R] Kb R)
  have hστ : ∀ x, σ (τ x) = x := fun x => e.symm_apply_apply x
  have hτσ : ∀ x, τ (σ x) = x := fun x => e.apply_symm_apply x
  have hb₀ : twF τ ≫ p.g.b = p₀.g.b := Over.OverMorphism.ext (by
    rw [Over.comp_left, twF_left]; exact h.2.1.symm)
  have hb : twF σ ≫ p₀.g.b = p.g.b := by
    rw [← hb₀, ← Category.assoc, twF_comp_eq_id hστ, Category.id_comp]
  have hφ := famMapTw_phiφ D σ α h.1 hb
  let u' := genCast hφ (LB.pullGen D.P.L _ _ u (famMapTw D σ).left)
  have hu' : u'.IsGen := genCast_isGen _ (DVR.pullGen_isGen _ _ _ u hu _)
  have hid : (twF σ).left ≫ spMap τ.toRingHom = 𝟙 _ := by
    rw [← twF_left, ← Over.comp_left, twF_comp_eq_id hστ]; rfl
  have hz : (DegPre.zF D (Kb R)).left ≫ (famMapTw D σ).left = (twF σ).left ≫ (DegPre.zF D (Kb R)).left := by
    rw [← Over.comp_left, zF_famMapTw, Over.comp_left]
  have hu'0 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (DegPre.zF D (Kb R)).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) := corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_genCast, val_pull hJ, Category.id_comp, hz, ← val_pull hJ, val_corr hJ hu0,
      val_mul hJ, val_mul hJ, val_corr hJ (h.2.2 α), val_pull hJ, frTw, val_genCast, val_pull hJ, hid]
  have H1 := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (H α u' hu' hu'0)
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e1 := H1 _ (famMapTw D τ).left y J hJ
  have hTT : (famMapTw D τ).left ≫ (famMapTw D σ).left = 𝟙 _ := by
    rw [← Over.comp_left, famMapTw_comp_eq_id D hτσ]; rfl
  rw [val_genCast, val_pull hJ, hTT] at e1
  rw [← h.1] at e1
  have hc : (famMapTw D τ).left ≫ (DegPre.trPt D (Kb R) p.g.b).left =
      (DegPre.trPt D (Kb R) p₀.g.b).left ≫ (famMapTw D τ).left := by
    rw [← Over.comp_left, famMapTw_trPt D τ hb₀, Over.comp_left]
  rw [sval_famTw _ _ _ _ _ _ hJ, sval_famTw _ _ _ _ _ _ hJ]
  simp only [Category.id_comp]
  rw [e1, hc]

end GlobalTheory.Mum.Conj.PhiTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PolModel

open GlobalTheory.SiegApprox GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem polarised_descends : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro R _ A _ _ P hA hP rig₁ rig₂ hsymm hamp
  classical
  obtain ⟨S, B, _, _, φ, φ₂, P₀, -, hS, hB, hφ, sq, hP₀, hw⟩ := model_exists R A ∅ hA P hP
  have one : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : B ⟶ B).left := one_comp hφ A B φ hφ.1.w
  have idφ : (𝟙 A : A ⟶ A).left ≫ φ = φ ≫ (𝟙 B : B ⟶ B).left := by simp
  obtain ⟨F₁, hF₁⟩ := rig_descends R S A B φ φ₂ P P₀ (lift 1 (𝟙 A)) (lift 1 (𝟙 B)) hB hφ sq hP hP₀ hw
    (lift_square sq one idφ) rig₁
  obtain ⟨F₂, hF₂⟩ := rig_descends R S A B φ φ₂ P P₀ (lift (𝟙 A) 1) (lift (𝟙 B) 1) hB hφ sq hP hP₀ hw
    (lift_square sq idφ one) rig₂
  obtain ⟨F₃, hF₃⟩ := symm_descends R S A B φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsymm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.proper
  have : Flat B.hom := by have := hB.smooth; infer_instance
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.AmpleApprox.relAmple_spread_subring (pull_isLB hP₀ _) hφ.1 (pull_isLB hP _)
    (GlobalTheory.SiegelPull.diag_iso sq hw) hamp
  let F : Finset R := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  obtain ⟨R₁, hSR, hFR, hR₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S F hS
  have hF₁R : (F₁ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₂R : (F₂ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₃R : (F₃ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₄R : (F₄ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  let iS : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion hSR)
  have hiS : spMap S.subtype = spMap R₁.subtype ≫ iS := by
    simp only [iS, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hφ' : IsGrpPullback A B (spMap R₁.subtype ≫ iS) φ := hiS ▸ hφ
  have hφ₁ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor iS (spMap R₁.subtype) hφ'
  set φ₁ := pullback.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [hφ'.1.w, Category.assoc]) with hφ₁def
  let B₁ := (Over.pullback iS).obj B
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.isAbelianScheme_pullback_obj iS B hB
  have hψφ : φ₁ ≫ pφ iS B = φ := pullback.lift_fst _ _ _
  let φ₂₁ := (GlobalTheory.GenericSpread.sqMap hφ₁).left
  have sq₁ : IsSquare φ₁ φ₂₁ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A))),
     congrArg (fun z => z.left) (lift_snd (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A)))⟩
  have hψ₂ : φ₂₁ ≫ pφ₂ iS B = φ₂ := by
    apply adelic_GL2_ext_of_local_components
    · rw [Category.assoc, pφ₂_fst, ← Category.assoc, sq₁.1, Category.assoc, hψφ, sq.1]
    · rw [Category.assoc, pφ₂_snd, ← Category.assoc, sq₁.2, Category.assoc, hψφ, sq.2]
  have hP₁ : (P₀.pull (pφ₂ iS B)).IsLB := pull_isLB hP₀ _
  have r₁ := hF₁ R₁ hSR hF₁R (lift 1 (𝟙 B₁)) (lift_one_id iS B)
  have r₂ := hF₂ R₁ hSR hF₂R (lift (𝟙 B₁) 1) (lift_id_one iS B)
  have s₁ := hF₃ R₁ hSR hF₃R
  have sqp : IsSquare (G' := B₁) (G := B) (pφ iS B) (pφ₂ iS B) := ⟨pφ₂_fst iS B, pφ₂_snd iS B⟩
  have := hB₁.proper
  have amp : Out.RelAmple B₁ ((P₀.pull (pφ₂ iS B)).pull (lift (𝟙 B₁) (𝟙 B₁)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₁ _)
      (GlobalTheory.SiegelPull.diag_iso sqp (GlobalTheory.lbIso_refl hP₁))
      (hF₄ R₁ hSR hF₄R B₁ (pφ iS B) (IsPullback.of_hasPullback B.hom iS))
  refine ⟨R₁, B₁, inferInstance, inferInstance, φ₁, φ₂₁, P₀.pull (pφ₂ iS B), hR₁, hB₁, hφ₁, sq₁, hP₁, ?_, r₁, r₂,
    s₁, amp⟩
  exact LBIso.trans hP (pull_isLB hP₀ _) (pull_isLB hP₁ _) hw
    (GlobalTheory.GenSpread.lbIso_pull_pull hP₀ φ₂₁ hψ₂.symm)

end GlobalTheory.PolModel
end
end

