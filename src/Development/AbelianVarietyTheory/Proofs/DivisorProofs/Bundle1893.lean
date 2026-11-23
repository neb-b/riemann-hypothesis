module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Good

open scoped nonZeroDivisors

theorem exists_vAdd_ge {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℕ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w a) ∧ ∀ w ∈ S, (B : ℤ) ≤ vAdd w a := by
  classical
  let I : Ideal (𝓞 K) := ∏ w ∈ S, w.asIdeal ^ B
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0 : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hmem : algebraMap (𝓞 K) K r ∈
      (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) := by
    have e : (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [Equiv.refl_apply, neg_neg, zpow_natCast, I]
      rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
      simp [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [e]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hrI, rfl⟩
  refine ⟨_, ha0, fun w => ?_, fun w hw => ?_⟩
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg] at h
    split_ifs at h
    · exact le_trans (by positivity) h
    · exact h
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg, if_pos hw] at h
    exact h

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem exists_twist_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) :
    ∃ a : c.F, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) ∧ ∀ w, s.hi w ≤ (vAdd w a : ℝ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 c.F)) := s.finite_lo.toFinset ∪ s.finite_hi.toFinset
  let B : ℕ := ⌈∑ w ∈ S, (|s.lo w| + |s.hi w|)⌉₊
  have hB : ∀ w ∈ S, |s.lo w| + |s.hi w| ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => |s.lo w| + |s.hi w|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hw).trans (Nat.le_ceil _)
  obtain ⟨a, ha0, hpos, hS⟩ := exists_vAdd_ge S B
  refine ⟨a, ha0, fun w => ?_, fun w => ?_⟩
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := neg_abs_le (s.lo w)
      push_cast at h2
      linarith [abs_nonneg (s.hi w)]
    · have : s.lo w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_left _ (s.finite_lo.mem_toFinset.2 h))
      rw [this, add_zero]; exact_mod_cast hpos w
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := le_abs_self (s.hi w)
      push_cast at h2
      linarith [abs_nonneg (s.lo w)]
    · have : s.hi w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_right _ (s.finite_hi.mem_toFinset.2 h))
      rw [this]; exact_mod_cast hpos w

theorem cnorm_smul {ι : Type} [Fintype ι] (k : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (k • u) = ‖k‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have : ∑ i, ‖(k • u) i‖ ^ 2 = ‖k‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

section Abstract

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem lattice_transfer (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set V) = ⊤) :
    L'.FG ∧ Submodule.span K (L' : Set W) = ⊤ ∧ Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  let ψ : V →ₗ[𝓞 K] W :=
    { toFun := fun f => a⁻¹ • φ f
      map_add' := fun f f' => by rw [map_add (f := _), smul_add]
      map_smul' := fun m f => by
        rw [RingHom.id_apply, ← algebraMap_smul K m f, map_smul, ← algebraMap_smul K m (a⁻¹ • φ f),
          smul_smul, smul_smul, mul_comm] }
  have hle : L' ≤ L.map ψ := fun g hg => by
    refine ⟨a • φ.symm g, hout g hg, ?_⟩
    show a⁻¹ • φ (a • φ.symm g) = g
    rw [map_smul, φ.apply_symm_apply, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hFG' : L'.FG := by
    have := isNoetherian_of_fg_of_noetherian _ (hFG.map ψ)
    exact isNoetherian_submodule.mp this _ hle
  have hspan' : Submodule.span K (L' : Set W) = ⊤ := by
    have hsub : Submodule.span K (L : Set V) ≤ (Submodule.span K (L' : Set W)).comap (φ : V →ₗ[K] W) := by
      refine Submodule.span_le.2 fun f hf => Submodule.mem_comap.2 ?_
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    rw [eq_top_iff]
    intro g _
    have h := hsub (show φ.symm g ∈ Submodule.span K (L : Set V) by rw [hspan]; trivial)
    simpa using h
  refine ⟨hFG', hspan', ?_⟩
  unfold Formalism.HN.rkK
  rw [hspan, hspan', finrank_top, finrank_top]
  exact φ.symm.finrank_eq


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
theorem hasGram_transfer (φ : V ≃ₗ[K] W) (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (h : ∀ σ f, N' σ (φ f) = t σ * N σ f) (hN : HasGram N) : HasGram N' := by
  obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hN
  refine ⟨⟨n, ⟨(b.map φ, fun v => ((t v.embedding : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
  have hk : ((t v.embedding : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (ht _).ne')
  have hdet := (hX v).1
  refine ⟨?_, fun y => ?_⟩
  · show IsUnit ((((t v.embedding : ℂ)⁻¹) • X v).det)
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
  · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t v.embedding : ℂ)⁻¹) • X v) v y = N' v.embedding y
    have := invertibleOfNonzero hk
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
    have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
    rw [hvec, Matrix.smul_mulVec, cnorm_smul, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
      ← φ.apply_symm_apply y, h, φ.apply_symm_apply]
    rw [inv_inv, Complex.norm_real, Real.norm_of_nonneg (ht _).le]

end Abstract

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem twist_goodOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G _hU hG hgood
  obtain ⟨hGram, hFG, hspan⟩ := hgood
  obtain ⟨φ, hφ, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := exists_twist_scalar s
  obtain ⟨hFG', hspan', hrk⟩ := lattice_transfer φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _)) hFG hspan
  refine ⟨⟨hasGram_transfer φ _ _ s.cInf s.cInf_pos (fun σ f => ?_) hGram, hFG', hspan'⟩, hrk⟩
  show petOn U x V dict Z (G + G₀) σ (φ f : Rul Xo c) = s.cInf σ * petOn U x V dict Z G σ (f : Rul Xo c)
  rw [hφ, petOn, petOn, _root_.GlobalTheory.FlatTw.PetTw.petAt_mul_sig E H Dw l Xo c r U x Z G₀ s G hG _ f.2.2]

end GlobalTheory.FlatTw.Good
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FromComp

theorem core (ι : Type) [Finite ι] [Nonempty ι] (T D A cs X cc z ρ R Bn δ' E C1 C2 mu : ℝ) (h sl δ dc degc : ι → ℝ)
    (hD : 0 ≤ D) (hT : 3 * D + 5 ≤ T) (hA : 0 < A) (hcs : 0 ≤ cs) (hX : 0 ≤ X) (hcc : 0 ≤ cc) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R) (hBn : 0 < Bn) (hδ : 0 < δ') (hE : 1 ≤ E)
    (h1 : ∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) (h2 : ∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c)
    (h3 : ∀ c, 0 ≤ h c + cs) (h4 : ∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc)
    (h5 : -X ≤ (∑ᶠ c, sl c) / (Nat.card ι : ℝ))
    (h6 : ∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R) ≤ degc c)
    (h7 : T * X ≤ C1 * E) (h8 : T * cc ≤ C1 * E) (h9 : cs * (6 * D + 10 + T * (z + 2 * ρ)) ≤ C1 * E)
    (h10 : A * Real.log (max A 1) + R ≤ C2 * E)
    (h11 : 2 * ((∑ᶠ c, degc c) / ∑ᶠ c, dc c) ≤ mu) : -((2 * (3 * C1 + C2 + 4)) * E) ≤ mu := by
  letI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype] at h5
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h11
  rw [Nat.card_eq_fintype_card] at h5
  have := Formalism.ExtensionFiltration.mean_height_sum_bound ι T D A cs X cc z ρ R 0 Bn δ' h sl δ dc degc 0 0 (4 * ((3 * C1 + C2 + 4) * E)) 0 0 0
    (C1 * E) (C1 * E) mu hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR le_rfl hBn hδ h1 h2 h3 h4 h5
    (fun c => by simpa using h6 c) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (Y : Cov p i) (PP A C1 C2 : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hg : DeepGoodAt p i Y) (hs : SizeAt p i PP A)
    (hd : ∀ u1, Quo p i PP u1 → DegAt p i Y u1) (hsh : ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1)
    (hh : ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C1 u1) (hhs : ∀ u1, Quo p i PP u1 → HSAt p i Y PP C2 u1)
    (hsum : SumAt p i Y) : UAt p i Y (2 * (3 * C1 + C2 + 4)) := by
  obtain ⟨-, -, -, -, -, hfin, hne, -⟩ := hg
  obtain ⟨hb1, hbE, -, -, -, -, hq⟩ := hs
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨hTD, hρ0, hρ1, hz1⟩ := hq u1 hu
  obtain ⟨δ', hδ, h1⟩ := hd u1 hu
  obtain ⟨cs, cc, X, sl, hcs, hcc, hX, h3, h4, h5, h7, h8, h9⟩ := hh u1 hu
  obtain ⟨B, R, hB, hR, h10, h6⟩ := hhs u1 hu
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  have hBn : 0 < binT p i PP := by
    unfold binT
    exact_mod_cast Nat.choose_pos (by omega)
  exact core (Comp Y.d.Xo₂ Y.d.c₂) (lenT p i PP) (dimFlag (dat p i)) B cs X cc (zed p i PP u1) (rhoB (dat p i) u1) R
    (binT p i PP) δ' (unitE p) C1 C2 _ (fun Z => Y.ht u1 Z) sl (fun Z => Y.dg u1 Z) (fun Z => Y.rkC (uM p i) Z)
    (fun Z => Y.degC (uM p i) Z) (Nat.cast_nonneg _) (by exact_mod_cast hTD) hB hcs hX hcc hz0 hz1 hρ0 hρ1 hR hBn hδ
    (hb1.trans hbE) h1 (hsh u1 hu) h3 h4 h5 h6 h7 h8 h9 h10 hsum

end GlobalTheory.CovTop.FromComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullModelLaw

theorem om_apply_eq_smul_pull : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∀ (p : GA D S × GA D T) (κ : ℂ), (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull p Φ)) → om p f₀ = κ • Tm (actPull p (halfInd e (latAll S T ΛS ΛT))) → ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → om p (Tm Φ) = κ • Tm (actPull p Φ) := by
  intro D ψ S T χS χT om hW ΛS ΛT hsS hsT Q e he f₀ hf₀ _ Tm hTm p κ hsb hκ Φ hΦ
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hthm : ∀ Ψ, IsSBHalf e (latAll S T ΛS ΛT) Ψ → IsThetaFunO ψ S T (Tm Ψ) :=
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hsS hsT e hee hinf f₀ hf₀ Tm hTm
  have hqp : ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) * p = 1 := Prod.ext (by simp) (by simp)
  have hpq : p * ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) = 1 := Prod.ext (by simp) (by simp)
  have hback : ∀ x : WO S T, actO S T p.1⁻¹ p.2⁻¹ (actO S T p.1 p.2 x) = x := fun x => by
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have hsmul : ∀ (w : WO S T) (c : ℂ) (F : WO S T → ℂ), c • heisO ψ S T w F = heisO ψ S T w (c • F) :=
    fun w c F => by
      funext t
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
  let L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := actPull p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := κ • ((om (p.1⁻¹, p.2⁻¹)).comp (Tm.comp L))
  have hTm'ap : ∀ Ψ, Tm' Ψ = κ • om (p.1⁻¹, p.2⁻¹) (Tm (actPull p Ψ)) := fun Ψ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf e (actO S T p.1 p.2 x) := (isHalf_actO p.1 p.2 x).2 hx
      have e1 : actPull p (fun t => Ψ (t + x)) = fun t => actPull p Ψ (t + actO S T p.1 p.2 x) := by
        funext t
        show Ψ (actO S T p.1⁻¹ p.2⁻¹ t + x) = Ψ (actO S T p.1⁻¹ p.2⁻¹ (t + actO S T p.1 p.2 x))
        rw [actO_add, hback]
      rw [hTm'ap, hTm'ap, e1, hTm.trans _ (hsb Ψ hΨ) _ hx',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · have hy' : IsHalf (cA D e) (actO S T p.1 p.2 y) := (isHalf_actO p.1 p.2 y).2 hy
      have e1 : actPull p (fun t => ψ (symplO S T t y) * Ψ t) =
          fun t => ψ (symplO S T t (actO S T p.1 p.2 y)) * actPull p Ψ t := by
        funext t
        show ψ (symplO S T (actO S T p.1⁻¹ p.2⁻¹ t) y) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t) =
          ψ (symplO S T t (actO S T p.1 p.2 y)) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t)
        conv_lhs => rw [← hback y]
        rw [Formalism.IndefR.Eqv.symplO_actO]
      rw [hTm'ap, hTm'ap, e1, hTm.modul _ (hsb Ψ hΨ) _ hy',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · rw [one_smul, hTm'ap, ← map_smul, ← hκ, ← Module.End.mul_apply, ← map_mul, hqp, map_one,
        Module.End.one_apply]
  have e3 : Tm Φ = Tm' Φ := GlobalTheory.PlaceVec.placeModel_unique hW.std hsS hsT hee hinf hTm hTm' hΦ
  rw [e3, hTm'ap, map_smul, ← Module.End.mul_apply, ← map_mul, hpq, map_one, Module.End.one_apply]

end GlobalTheory.PullModelLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilThetaRat

theorem dbl_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (χ : Chr F E) (hχ : IsHecke F E χ)
    (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd g φ) = thetaSum F φ := by
  intro φ hφ
  obtain ⟨p, q, p', p₀, q₀, p₀', t, s, t', hp, hq, hp', ht, hs, ht', rfl⟩ :=
    GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product F E σ hσ b JB ε hJ hdet g g₀ hg
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc
    _ = thetaSum F (omd q (omd p' φ)) :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p p₀ hp t ht (omd q (omd p' φ)) (hS.pres q _ (hS.pres p' _ hφ))
    _ = thetaSum F (omd p' φ) :=
      GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR q q₀ hq s hs (omd p' φ) (hS.pres p' _ hφ)
    _ = thetaSum F φ :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p' p₀' hp' t' ht' φ hφ

theorem member_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (χ : Chr F E) (hχ : IsHecke F E χ) (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (γ : UG (cA σ) (incM F JB)) (γ₀ : Matrix (Fin b) (Fin b) E)
    (hγ : ((γ : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀) :
    ∀ Φ ∈ schA F κ, thetaSum F (om γ Φ) = thetaSum F Φ := by
  intro Φ hΦ
  obtain ⟨hom, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ) (Fin b) (incM F JB) γ
  have hgd0 : ((gd : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F (Matrix.fromBlocks γ₀ 0 0 1) := by
    rw [hgd, hγ]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨φ₂, hφ₂, hθ⟩ := _root_.GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e1 := dbl_rat σ hσ ψ hψ JA JB ε hJ hdet hκ d hd dd hdd χ hχ omd hS.toIsSplitting hR gd _ hgd0 _ hb
  rw [hres γ gd hgd Φ hΦ φ₂ hφ₂, _root_.GlobalTheory.ThetaBox.thetaSum_boxFun F κ κ _ (hom.pres γ Φ hΦ) φ₂ hφ₂, _root_.GlobalTheory.ThetaBox.thetaSum_boxFun F κ κ Φ hΦ φ₂ hφ₂] at e1
  exact mul_right_cancel₀ hθ e1

theorem rat_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, ((γ.1 : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨(g₀ : Matrix (Fin n) (Fin n) E), ?_⟩
  rw [← hg₀]
  ext i j
  rfl

theorem thetaSum_om_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := hom
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  have eW : ∀ i j, σ (JW j i) = (((-1 : ℤˣ) : ℤ) : E) * JW i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (JX j i) = (((1 : ℤˣ) : ℤ) : E) * JX i j := fun i j => by simp [hX i j]
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := by simp [incM, Matrix.transpose_map]
    rw [e, hd']
    exact hco xᵀ
  have hx : (γ, γ') = (γ, 1) * (1, γ') := by simp
  rw [hx, map_mul, Module.End.mul_apply]
  have e1 : om (γ, 1) = (om.comp (MonoidHom.inl _ _)) γ := rfl
  have e2 : om (1, γ') = (om.comp (MonoidHom.inr _ _)) γ' := rfl
  have hΦ' : om (1, γ') Φ ∈ schA F (Fin n × Fin d) := hB.1.pres γ' Φ hΦ
  rw [e1, member_rat σ hσ ψ hψ JW JX 1 eX hXd (by simp [Nat.mul_comm]) d' hco' χW hχW _ hA γ g₀ hg₀ _ hΦ', e2]
  exact member_rat σ hσ ψ hψ JX JW (-1) eW hWd (by simp) co hco χX hχX _ hB γ' g₀' hg₀' Φ hΦ

end GlobalTheory.WeilThetaRat
end
end

