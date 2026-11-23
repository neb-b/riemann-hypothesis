module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkGram

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem exists_inv_of_rank_one {m n : ℕ} (hm : m = 1) (hn : n = 1) (τ : Matrix (Fin m) (Fin n) D.host.E) (h : τ ≠ 0) :
    ∃ σ : Matrix (Fin n) (Fin m) D.host.E, σ * τ = 1 ∧ τ * σ = 1 := by
  subst hm; subst hn
  have hd : IsUnit τ.det := by
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    intro h0; apply h; ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h0]; rfl
  exact ⟨τ⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

theorem scalar_one : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
  have h := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
  rw [map_mul, map_one, cA_cA, mul_comm] at h
  exact h

theorem ofAdj_starAdj (L S : HSp D) (x : WO L S) : ofAdj L S (starAdj L S x) = x := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    scalar_one, one_smul]
  simp only [Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem link_gram : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' →
    ∀ l : Link B L' ζ', l.τᴴ * (B.L.gram * l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧
      ∀ S : HSp D, Function.Bijective (l.κ S) ∧
        ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  intro D ρ B L' ζ' h l
  refine ⟨by rw [Int.cast_one, one_mul]; exact GlobalTheory.Unf.StCheck.link_simil h l, fun S => ?_⟩
  have hτ : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : B.ζ = 0 := neg_eq_zero.mp e.symm
    apply B.line.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := exists_inv_of_rank_one B.line.1 h.1 l.τ hτ
  have key : ∀ w, (rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S (l.κ S w) = w := by
    intro w
    rw [Link.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  refine ⟨⟨fun w w' e => by rw [← key w, ← key w', e], fun x => ⟨(rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S x, ?_⟩⟩,
    fun w hw => ?_⟩
  · rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, ofAdj_starAdj]
  · rw [← key w]
    refine ratMx_mul (rat_mem σ) ?_
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 hw
    rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
    exact rat_mem _

end GlobalTheory.Unf.LinkGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T₀.rank → AE D} (hu : u ∈ latV T₀ L₀ (· = v)) :
    d.j0 *ᵥ u ∈ latV T L (· = v) := by
  refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h0 : (d.pX *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jX i ((d.pX *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · have h0 : (d.pY *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jY i ((d.pY *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec]; exact hu

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T₀.rank → AE D} (hz : z ∈ latA T₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.j0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.j0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (wittCoreInclusion_mem_latticeCompletionAtPlace d hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem wittExt_wittInc_mem_completed_hom_lattice {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T₀}
    (hw : w ∈ latO S₀ T₀ (LS₀ : Set _) (LT₀ : Set _) (· = v)) :
    dS.ext0 T (dT.inc0 S₀ w) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · change (dT.j0 * w * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

theorem wittExt_wittInc_isHalf {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {e : AE D}
    {w : WO S₀ T₀} (hw : IsHalf e w) : IsHalf e (dS.ext0 T (dT.inc0 S₀ w)) := by
  intro i j
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hw k l]
  ring

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

theorem flat_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf
  obtain ⟨hθ, h2, hh⟩ := hf
  have hmem : ∀ w ∈ latO B.V₀ J.W₀ (LV₀ : Set _) (LW₀ : Set _) (· = v),
      B.d.ext0 J.W (J.d.inc0 B.V₀ w) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) := fun w hw =>
    wittExt_wittInc_mem_completed_hom_lattice B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hw
  refine ⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩
  · have hx : MxAt (· = v) (2 • w) := fun i j => by
      rw [Matrix.smul_apply]
      exact nsmul_mem (GlobalTheory.FinPl.LatMem.latO_mxAt hw i j) 2
    rw [← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]
  · rw [← h𝔉.Heisenberg₂.core f hθ w (GlobalTheory.FinPl.LatMem.latO_mxAt hw),
      hh e he _ (hmem w hw) (wittExt_wittInc_isHalf B.d J.d hwe)]

end GlobalTheory.FinPl.VacFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSpherical
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalUnique

theorem genVal_top_ne_zero (q N : ℕ) (α : Fin N → ℂˣ) : genVal q 0 N (Finset.univ.val.map α) N ≠ 0 := by
  simp only [genVal, Nat.sub_self, mul_zero, zero_mul, add_zero, pow_zero, one_mul, Multiset.map_map]
  have e : (Multiset.map ((fun b : ℂˣ => (b : ℂ)) ∘ α) Finset.univ.val).esymm N = ∏ i, (α i : ℂ) := by
    rw [Finset.esymm_map_val]
    have : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rw [this, Finset.sum_singleton]; rfl
  rw [e, Finset.prod_ne_zero_iff]
  exact fun i _ => (α i).ne_zero

theorem eq_mul_zonalInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ϖ hϖ α
  have hq : (1 : ℕ) < resCard k := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hγ : ∀ i, borelParam (resCard k) α i ≠ 0 := by
    intro i
    unfold borelParam
    refine mul_ne_zero (α i).ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (show resCard k ≠ 0 by omega) (by exact_mod_cast h.1)
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.BorelSphExist.exists_isBorelSph k N _ hγ
  refine ⟨ψ, hψ, fun f hf he m => ?_⟩
  have hr : ∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g := hψ.1
  have hωb := _root_.GlobalTheory.ZonalBi.zonalInt_biInvariant k N μK hK ψ hr
  have hω1 := _root_.GlobalTheory.ZonalOne.zonalInt_one_eq_one k N μK hK _ ψ hψ
  have hωe : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, zonalInt μK ψ (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * zonalInt μK ψ m := by
    intro s R hR
    refine _root_.GlobalTheory.ZonalEig.zonalInt_eig k N μK hK ψ hr R _ fun m => ?_
    rw [_root_.GlobalTheory.ZonalSum.sum_mul_eq k N _ ψ hψ hγ _ R hR m, GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps k N ϖ hϖ _ ψ hψ hγ s R hR,
      _root_.GlobalTheory.SatakeSubsetSum.satake_subset_sum (resCard k) N (by omega) α s.card, mul_comm]
  have hcN : genVal (resCard k) 0 N (Finset.univ.val.map α) N ≠ 0 := genVal_top_ne_zero _ N α
  have key := GlobalTheory.T.cartan_decomposition_dominance_order k N ϖ (fun n => genVal (resCard k) 0 N (Finset.univ.val.map α) n) hcN
    (_root_.GlobalTheory.SortedCartan.cartan_antitone k N ϖ hϖ) (GlobalTheory.T.cartan_decomposition_dominance_local_field k N ϖ hϖ) (fun g => (_root_.GlobalTheory.ParHeckeReps.exists_reps_both k Unit (Fin N)).2 g)
    (fun m => f m - f 1 * zonalInt μK ψ m)
    (fun κ hκ m => ⟨by rw [(hf κ hκ m).1, (hωb κ hκ m).1], by rw [(hf κ hκ m).2, (hωb κ hκ m).2]⟩)
    (fun s R hR m => by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he s R hR m, hωe s R hR m]
      ring)
    (by simp [hω1]) m
  exact sub_eq_zero.1 key

end GlobalTheory.ZonalUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CaRepApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7}

def CA (A : HSp D) : Submodule ℂ (GA D A → ℂ) where
  carrier := {φ | GlobalTheory.Unf.IsContAut A φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g], hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ hφ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g], continuous_const.mul hφ.2⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n]

theorem rep_mem_CA {A : HSp D} (α : Frame p A n) (g : GL n k) {φ : GA D A → ℂ} (h : φ ∈ CA A) : α.rep g φ ∈ CA A :=
  ⟨fun γ hγ x => by
    change φ (γ * x * α.gl g) = φ (x * α.gl g)
    rw [mul_assoc, h.1 γ hγ], h.2.comp (continuous_mul_const _)⟩

def caRep {A : HSp D} (α : Frame p A n) : Representation ℂ (GL n k) (CA A) where
  toFun g := (α.rep g).restrict fun _ h => rep_mem_CA α g h
  map_one' := by ext φ x; simp
  map_mul' g h := by ext φ x; simp

@[simp] theorem caRep_apply {A : HSp D} (α : Frame p A n) (g : GL n k) (φ : CA A) :
    ((caRep α g φ : CA A) : GA D A → ℂ) = α.rep g φ := rfl

def blkHom : Matrix n n k →* Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k where
  toFun x := fromBlocks x 0 0 1
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def blk : GL n k →* GL (n ⊕ Fin 1) k := Units.map blkHom

@[simp] theorem blk_val (g : GL n k) : (blk g).val = fromBlocks g.val (0 : Matrix n (Fin 1) k) 0 1 := rfl

end GlobalTheory.FinPl.SrcGl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.fixes_latV_of_mem_grpOff : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  intro D S L P g hg y hy
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D P
  have hmul : ∀ a ∈ idOff D P, ∀ b ∈ idAt D P, a * b = 0 := by
    intro a ha b hb
    rw [← (hAt b).1 hb, ← mul_assoc, mul_comm a ε, (hOff a).1 ha, zero_mul]
  have hker := MonoidHom.mem_ker.1 hg
  have hent : ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idOff D P) => u.1 i j) hker
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
    have h3 : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
      by_cases hij : i = j
      · subst hij; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne hij, map_zero]
    rw [h3, ← h2]
    rfl
  have hfix : mt S g *ᵥ y = y := by
    funext i
    have e : (mt S g *ᵥ y) i = y i + ∑ j, (mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [e, Finset.sum_eq_zero (fun j _ => hmul _ (hent i j) _ (hy j)), add_zero]
  rw [hfix]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.CoCptOf

theorem coCpt_of_mul {D : D7} {V : HSp D}
    (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso_or_posDef :
    ∀ (D : D7) (V : HSp D), (IsAniso V → CoCpt V) ∧ ((∀ τ, (gramAt D V τ).PosDef) → CoCpt V) :=
  fun D V => ⟨fun h => coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h),
    fun h => coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)⟩

end GlobalTheory.Unf.CoCptOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionTensorRelativeBasisCoordsUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.CoordUnique

theorem coords_unique_of_field {K E A : Type*} [Field K] [Ring E] [Nontrivial E] [Algebra K E] [AddCommGroup A]
    [Module K A] (w : E) (hw : ∀ f : K, algebraMap K E f ≠ w) (a b : A)
    (h : a ⊗ₜ[K] (1 : E) + b ⊗ₜ[K] w = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (K × K) →ₗ[K] E, ∀ p, φ p = p.1 • (1 : E) + p.2 • w :=
    ⟨{ toFun := fun p => p.1 • (1 : E) + p.2 • w,
       map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel,
       map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply] },
      fun p => rfl⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ hst
    rw [hφ] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      simp [hst]
    · exfalso
      apply hw (-s / t)
      have h1 : t • w = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : w = t⁻¹ • (-(s • (1 : E))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, div_eq_mul_inv, neg_mul, neg_smul, mul_comm]
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := A) φ hinj
  have hx : φ.lTensor A (a ⊗ₜ[K] ((1 : K), (0 : K)) +
      b ⊗ₜ[K] ((0 : K), (1 : K))) = 0 := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hφ, hφ]
    simpa using h
  rw [← map_zero (φ.lTensor A)] at hx
  have hx0 := hinj' hx
  have ha : TensorProduct.rid K A
      ((LinearMap.fst K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = a := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.fst_apply, LinearMap.fst_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, add_zero]
  have hb : TensorProduct.rid K A
      ((LinearMap.snd K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = b := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.snd_apply, LinearMap.snd_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, zero_add]
  rw [hx0, map_zero, map_zero] at ha hb
  exact ⟨ha.symm, hb.symm⟩

theorem coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) →
    ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 :=
  fun _ _ w hw a b h => coords_unique_of_field w hw a b h

end GlobalTheory.CoordUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  first | exact @GlobalTheory.LatVHat.latV_mem_hatL | exact GlobalTheory.LatVHat.latV_mem_hatL | (intros; apply GlobalTheory.LatVHat.latV_mem_hatL <;> assumption)
end

