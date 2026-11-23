module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilVacuumLocalModelIntegralMatrixPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)

noncomputable section
namespace GlobalTheory.TwBridge.LevOrb
open GlobalTheory.TwBridge.Lev

theorem inX_zero {E : Type} [Field E] (n : ℕ) (x : Fin n → E) : Loc.inX E n 0 x = x := by
  funext l
  simp [Loc.inX, show l.1 < n from l.2]

theorem mem_prX_zero {E : Type} [Field E] {n : ℕ} (J : Subgroup ((Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E)))
    (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : κ ∈ Loc.prX (Loc.Cbe J 1) ↔ (show (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E) from κ) ∈ J := by
  have hR : ∀ γ : (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E), Loc.R1cond E n 0 γ := fun γ => by
    rw [r1cond_iff]
    intro l l' h
    have := l.2
    have := l'.2
    omega
  constructor
  · rintro ⟨r, hr, hx⟩
    have h2 : r ∈ J := by simpa [MulAut.conj_apply] using hr.2
    have : r = κ := LinearEquiv.ext fun x => by simpa only [inX_zero] using hx x
    exact this ▸ h2
  · intro h
    refine ⟨κ, ⟨⟨hR _, hR _⟩, ?_⟩, fun x => by rw [inX_zero, inX_zero]⟩
    simpa [MulAut.conj_apply] using h

section Orb
variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
theorem mem_box_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M) ↔ ((q : E) ^ M)⁻¹ • v ∈ stdAt E n P := by
  rw [stdAt, StabRef.mem_locStd, mem_box]
  have key : ∀ a : E, valuation k (ι a) ≤ valuation k ((ϖ ^ M : kˣ) : k) ↔ IntAt P (((q : E) ^ M)⁻¹ * a) := fun a => by
    rw [← hc.int, map_mul, map_inv₀, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul, map_inv₀, Units.val_pow_eq_pow_val,
      inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  refine ⟨fun h l => ?_, fun h r => (key _).2 (h (e r))⟩
  obtain ⟨r, rfl⟩ := e.surjective l
  exact (key _).1 (h r)

omit [NumberField E] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem phi_mulVec (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (z : Fin n → E) : (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) = fun r => ι (γ z (e r)) := by
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    rw [apply_sum γ z, map_sum, ← e.sum_comp]
  simp [mulVec, dotProduct, toBlocks₁₁, phi_val, toLoc, he]

theorem mulVec_mem_box {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : A → k} (hy : y ∈ box A a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a)
    (J : Subgroup (GL (A ⊕ Fin 0) k)) (h1 : KOne k _ ≤ J) (h2 : J ≤ KO k _) (M : ℕ) (z z' : Sp E n) :
    GlobalTheory.QPl.SameOrb J (box _ (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔
      ∃ γ : Sp E n ≃ₗ[E] Sp E n, phi ι e' γ ∈ J ∧ ((q : E) ^ M)⁻¹ • (γ z - z') ∈ stdAt E n P := by
  have hsub : ∀ γ : Sp E n ≃ₗ[E] Sp E n, (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) =
      fun r => ι ((γ z - z') (e r)) := fun γ => by
    rw [phi_mulVec e e' he]
    funext r
    simp
  constructor
  · rintro ⟨g, hg, y, hy, hy'⟩
    rw [Submodule.Quotient.eq] at hy hy'
    have h0 : g.val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M) := by
      have := sub_mem hy' (mulVec_mem_box (h2 hg) _ hy)
      rw [mulVec_sub] at this
      convert this using 1
      abel
    have hU1 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k | MaxM ((g⁻¹).val * N - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => ((g⁻¹).val * N - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    have ho : IsOpen ((box A (ϖ ^ M) : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
      convert (isOpen_set_pi Set.finite_univ fun (_ : A) _ => isOpen_cball (ϖ ^ M)) using 1
      ext z; simp [mem_box, cball]
    have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M)} := by
      refine ho.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r)))) ?_
      have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
        continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
      exact (hb.matrix_mulVec continuous_const).sub continuous_const
    obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense g.val (hU1.inter hU2) ⟨by
      change MaxM _
      rw [Units.inv_mul, sub_self]
      exact maxM_zero, h0⟩
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne a1
    have ev : (g * u).val = M₀.map ι := by
      rw [Units.val_mul, eu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    obtain ⟨γ, hγ⟩ := exists_phi ι e' M₀ _ ev
    refine ⟨γ, hγ ▸ mul_mem hg (h1 hu), (mem_box_iff hc e M _).1 ?_⟩
    rw [← hsub, hγ, ev]
    exact a2
  · rintro ⟨γ, hγ, h⟩
    refine ⟨_, hγ, _, rfl, (Submodule.Quotient.eq _).2 ?_⟩
    rw [hsub]
    exact (mem_box_iff hc e M _).2 h

end Orb

theorem mem_prX_JQ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (hc : c = 0)
    (κ : Sp E n ≃ₗ[E] Sp E n) : κ ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ↔
      (show Sp E (n + 0) ≃ₗ[E] Sp E (n + 0) from κ) ∈ LocE.JQ P q kj n 0 := by
  subst hc
  exact mem_prX_zero _ κ

theorem sameOrb_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W hA L G hL b hQ e he z z'
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)), phi ι e' γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
      γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := fun γ => by
    rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ
  have hle : ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ := fun g hg => by
    have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  rw [sameOrb_iff hA.compl e e' (fun _ => rfl) _
    (fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) hle, hL.grpQ]
  constructor
  · rintro ⟨γ, h1, h2⟩
    have h3 := (hmem γ).1 h1
    exact ⟨⟨γ, hL.int _ b P h3⟩, h3, h2⟩
  · rintro ⟨κ, h1, h2⟩
    exact ⟨κ.1, (hmem _).2 h1, h2⟩

end GlobalTheory.TwBridge.LevOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContribute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Unf.cut_gram_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS vN x₀ Th hB hTh Ψ hΨ
  have lemR : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := _root_.GlobalTheory.Unf.tsum_offBase_invariant D ψ V V₀ W ρ d χV χW om om' hW hW' vS x₀ hB
  have lemQ : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := _root_.GlobalTheory.Unf.exists_central_ne D ψ hW.std V V₀ W ρ d x₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hH, hFD, h1⟩ := vN.unit

  have hBc : ∀ (c : skewA D ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∀ x,
      term ψ d W vS (om (d.nC c, 1) Φ) x = ψ (d.qS W c (rat x)) * term ψ d W vS Φ x := by
    intro c Φ hΦ x
    have h := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ).1 x 0 1 c
    rw [d.nB_zero, Subgroup.coe_one, map_one, mul_one, mul_one] at h
    rw [h]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, Matrix.mul_zero]
    rfl
  have hsplit : ∀ g h : GA D V, om (g * h, 1) Ψ = om (g, 1) (om (h, 1) Ψ) := by
    intro g h
    rw [show ((g * h, (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply]
  let F : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} → flagN d → ℂ :=
    fun i n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
  let a : skewA D ρ → Matrix (Fin W.rank) (Fin ρ) D.host.E → ℂ :=
    fun c x => star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x))
  have hE : ∀ i c (n : flagN d), F i (⟨d.nC c, d.nC_mem_NFlag c⟩ * n) = a c i.1 * F i n := by
    intro i c n
    simp only [F, a, Subgroup.coe_mul]
    rw [hTh.cen c n.1 n.2, hsplit, hBc c _ (hW.om_pres _ _ hΨ)]
    ring

  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hW hW' vS
  obtain ⟨-, hM⟩ := _root_.GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact D V V₀ ρ d
  obtain ⟨-, hcl, hnorm, K, hK, hKc⟩ := hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)
  have hdisc : DiscreteTopology (NFlagQ V d.e) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V))
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h)))
  have hcl' : IsClosed (((GlobalTheory.MixPer.centre d).subgroupOf (flagN d) : Subgroup (flagN d)) : Set (flagN d)) := by
    rw [Subgroup.coe_subgroupOf]; exact hcl.preimage continuous_subtype_val
  have hcpt : ∃ K' : Set ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), IsCompact K' ∧
      ∀ m, ∃ γ ∈ (NFlagQ V d.e).subgroupOf ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), ∃ k ∈ K', m = γ * k := by
    let φ : GlobalTheory.MixPer.centre d → (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) := fun c =>
      ⟨⟨c.1, (hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)).1 c.2⟩, Subgroup.mem_subgroupOf.2 c.2⟩
    have hφ : Continuous φ := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
    refine ⟨φ '' K, hK.image hφ, fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨φ γ, ?_, φ k, ⟨k, hk, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hγ))
    · refine Subtype.ext (Subtype.ext ?_)
      change m.1.1 = γ.1 * k.1
      exact congrArg Subtype.val e
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    (hTh.cont.mul ((hT Ψ hΨ).2.2.2.1 i.1 |>.comp (continuous_subtype_val.prodMk continuous_const))).measurable
  have hbd : ∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B := by
    obtain ⟨K, hK, hKc⟩ := (_root_.GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hTh.cont.continuousOn
    obtain ⟨C, A, hCA⟩ := _root_.GlobalTheory.Unf.sum_term_bound D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
    refine ⟨M.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal, fun n => ?_⟩
    have hTn : ‖Th n.1‖ₑ ≤ ENNReal.ofReal M := by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      rw [Subgroup.coe_mul, hTh.left γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 k.1 k.2, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM k hk)
    have hS := hCA 1 1 n.1 n.2
    rw [mul_one] at hS
    calc ∑' i, ‖F i n‖ₑ = ‖Th n.1‖ₑ * ∑' i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀},
          ‖term ψ d W vS (om (n.1, 1) Ψ) i.1‖ₑ := by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun i => enorm_mul _ _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
          mul_le_mul' hTn ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans hS)
      _ = _ := by rw [ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul]
  have hinv : ∀ γ ∈ NFlagQ V d.e, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n := by
    intro γ hγ n
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit, tsum_mul_left, tsum_mul_left,
      lemR γ.1 hγ' γ.2 _ (hW.om_pres _ _ hΨ)]
  have hcinv : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∀ γ ∈ NFlagQ V d.e, γ ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) → ∀ n,
      ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 (γ * n) =
        ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 n := by
    intro c γ hγ hγM n
    refine tsum_congr fun i => ?_
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hγM
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit]
    congr 1
    refine (hT _ (hW.om_pres _ _ hΨ)).2.1 γ.1 hγ' γ.2 i.1.1 i.1.1 ?_
    rw [blockX_of_fix d (mem_fixer.2 (hc' ▸ d.nC_jX c')), Matrix.mul_one]
  have heig : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∃ u ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∃ a : ℂ, a ≠ 1 ∧ ∀ i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, id i = c →
      ∀ m ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∀ n, F i (m * u * n) = a * F i (m * n) := by
    intro c
    obtain ⟨c', hc'⟩ := lemQ c.1 c.2
    refine ⟨⟨d.nC c', d.nC_mem_NFlag c'⟩, Subgroup.mem_subgroupOf.2 ⟨c', rfl⟩, a c' c.1, hc', ?_⟩
    intro i hi m hm n
    subst hi
    obtain ⟨c'', hc''⟩ := Subgroup.mem_subgroupOf.1 hm
    have : m = ⟨d.nC c'', d.nC_mem_NFlag c''⟩ := Subtype.ext hc''.symm
    subst this
    rw [mul_assoc, hE, hE, hE]
    simp only [id]
    ring
  exact _root_.GlobalTheory.CutSum.integral_tsum_eq_zero (flagN d) vN.ν (NFlagQ V d.e) ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)) j4 hdisc hnorm hcl' hcpt
    vN.𝓝 hFD (by rw [h1]; exact ENNReal.one_ne_top) _ _ id F hmeas hbd hinv hcinv heig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocProd

variable {D : D7}

theorem mem_congGrp_entries (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := fun g hg =>
  (mem_congGrp_entries V J g).2 fun i j => h ((mem_congGrp_entries V I g).1 hg i j)

theorem idAt_le_idOff (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : idAt D P ≤ idOff D P' := by
  intro a ha
  have h2 := (Submodule.mem_inf.1 ha).2
  rw [Submodule.mem_iInf] at h2
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact h2 ⟨w, fun h' => h w h' hw⟩

theorem grpAt_le_grpOff' (V : HSp D) (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : grpAt V P ≤ grpOff V P' :=
  congGrp_mono V (idAt_le_idOff P P' h)

theorem mem_idOff_of_forall (P : Pl D → Prop) (a : AE D) (h : ∀ w, P w → a ∈ idOff D (· = w)) : a ∈ idOff D P := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at h ⊢
  intro w hw
  exact h w hw w rfl

theorem mem_grpOff_of_forall (V : HSp D) (P : Pl D → Prop) (g : GA D V) (h : ∀ w, P w → g ∈ grpOff V (· = w)) :
    g ∈ grpOff V P := by
  unfold grpOff
  rw [mem_congGrp_entries]
  intro i j
  exact mem_idOff_of_forall P _ fun w hw => (mem_congGrp_entries V _ g).1 (h w hw) i j

theorem map_list_prod_eq_one {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) :
    ∀ J : List ι, (∀ i ∈ J, φ (f i) = 1) → φ (J.map f).prod = 1
  | [], _ => by simp
  | a :: J, h => by
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      map_list_prod_eq_one φ f J fun i hi => h i (List.mem_cons_of_mem a hi), one_mul]

theorem map_list_prod_single {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) (j : ι)
    (h1 : ∀ i, i ≠ j → φ (f i) = 1) : ∀ J : List ι, J.Nodup → j ∈ J → φ (J.map f).prod = φ (f j)
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: J, hn, hj => by
    have ha : a ∉ J := List.Nodup.notMem hn
    have hn' : J.Nodup := List.Nodup.of_cons hn
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases haj : a = j
    · subst haj
      rw [map_list_prod_eq_one φ f J fun i hi => h1 i fun e => ha (e ▸ hi), mul_one]
    · have hjJ : j ∈ J := by
        rcases List.mem_cons.1 hj with e | e
        · exact absurd e.symm haj
        · exact e
      rw [h1 a haj, one_mul, map_list_prod_single φ f j h1 J hn' hjJ]

theorem eq_prod_gl_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  intro D S k _ _ _ _ ι p n _ _ β hinj J hJ hall κ
  have hloc := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).1 κ
  have hcomm := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).2.1
  choose x hx y hy hxy using hloc
  have hfr := fun i => ((_root_.GlobalTheory.FrameAt.frame_facts D k (p i) S n (β i)).1 (x i)).1 (hx i)
  choose g hg using hfr
  have hglAt : ∀ i, (β i).gl (g i) ∈ grpAt S (· = (p i).v) := fun i =>
    ((_root_.GlobalTheory.FrameAt.frame_facts D k (p i) S n (β i)).1 _).2 ⟨g i, rfl⟩
  have key : ∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v) := by
    intro i
    rw [← hg i, hxy i, hcomm i (x i) (hx i) (y i) (hy i), mul_assoc, mul_inv_cancel, mul_one]
    exact hy i
  refine ⟨g, key, (J.map fun i => (β i).gl (g i)).prod⁻¹ * κ, ?_, (mul_inv_cancel_left _ _).symm⟩
  apply mem_grpOff_of_forall
  rintro w ⟨j, rfl⟩
  let φ := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idOff D (· = (p j).v)))).comp (matHom S)
  have hker : ∀ h, h ∈ grpOff S (· = (p j).v) ↔ φ h = 1 := fun h => MonoidHom.mem_ker
  have hκ : φ κ = φ ((β j).gl (g j)) := by
    have := (hker _).1 (key j)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have h1 : ∀ i, i ≠ j → φ ((β i).gl (g i)) = 1 := fun i hij =>
    (hker _).1 (grpAt_le_grpOff' S _ _ (fun w hw hw' => hij (hinj (hw.symm.trans hw'))) (hglAt i))
  rw [hker, map_mul, map_inv, map_list_prod_single φ (fun i => (β i).gl (g i)) j h1 J hJ (hall j), hκ, inv_mul_cancel]

end GlobalTheory.FinPl.LocProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm

theorem omLoc : ∀ (D : D7), OmLoc D := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT hμS hμT Y Y' _ _ _ _ FS FT Tm hTm g gk h hk hg hh Φ Φ' hΦ'
  have U := (_root_.GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hW.std).1
  have enl : ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk →
      LawLoc ω μS μT Tm g gk h hk := by
    intro g gk h hk hg hh he
    obtain ⟨T₂, hT₂, hT₂e⟩ := _root_.GlobalTheory.LocTwist.conj_isModel D k p ψ S T χS χT ω hW μS μT Y Y' FS FT Tm hTm g gk h hk hg hh
    obtain ⟨Φ₀, Φ₀', h0, h0', hv⟩ := _root_.GlobalTheory.LocOm.vacuum_move D k p ψ S T χS χT ω hW μS μT hμS hμT Y Y' FS FT Tm hTm g gk h hk hg hh he
    have inv1 : ∀ F, ω (g⁻¹, h⁻¹) (ω (g, h) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have inv2 : ∀ F, ω (g, h) (ω (g⁻¹, h⁻¹) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hT : T₂ = Tm := U T₂ Tm hT₂ hTm Φ₀ h0 (by rw [hT₂e Φ₀ Φ₀' h0', ← hv, inv1])
    intro Φ Φ' hΦ'
    have := hT₂e Φ Φ' hΦ'
    rw [hT] at this
    rw [this, inv2]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LocOm.enl_scalar_denominator k Y Y' gk hk
  obtain ⟨zk, hzk⟩ : ∃ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) :=
    ⟨Units.map (Matrix.scalar Y : k →+* Matrix Y Y k).toMonoidHom c, by
      simp [Matrix.smul_one_eq_diagonal]⟩
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.LocScalar.exists_isLoc_scalar D k p T Y FT c zk hzk
  have iS := _root_.GlobalTheory.LocOm.isLoc_one_mul_inv D k p S Y' FS
  have iT := _root_.GlobalTheory.LocOm.isLoc_one_mul_inv D k p T Y FT
  have l1 := enl g gk (h * z⁻¹) (hk * zk⁻¹) hg (iT.2.1 _ _ _ _ hh (iT.2.2 _ _ hz)) (hc zk hzk).1
  have l2 := enl 1 1 z⁻¹ zk⁻¹ iS.1 (iT.2.2 _ _ hz) (hc zk hzk).2
  have l3 := _root_.GlobalTheory.LocOm.LawMul.lawLoc_mul D k S T ω μS μT Y Y' Tm _ _ _ _ _ _ _ _ l1 (_root_.GlobalTheory.LocOm.lawLoc_inv D k S T ω μS μT Y Y' Tm _ _ _ _ l2)
  simp only [inv_one, mul_one, inv_inv, inv_mul_cancel_right] at l3
  exact l3 Φ Φ' hΦ'

end GlobalTheory.LocOm

end
end

