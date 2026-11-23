module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorph
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt_fderiv (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverse
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem Etale.contDiffAt_chart {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n} (hE : Etale A U z) {x : Y} (hx : x ∈ U)
    {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  rw [contDiffAt_euclidean]
  intro k
  have hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)
  exact (contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)

theorem etale_local_inverse : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  intro n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi
  set g : V n → V n := z ∘ (A.chart i).symm with hg_def
  have hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U)) := hE.contDiffAt_chart (e.symm v).2 hi
  have hdet : (jz A z i (e.symm v : U)).det ≠ 0 := hE.det_ne i _ (e.symm v).2 hi
  set f' : V n ≃L[ℂ] V n :=
    (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def
  have hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U)) := by
    ext w; rfl
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U)) := by
    rw [hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hg.hasStrictFDerivAt' hf' hn

  have hgv : g (A.chart i (e.symm v : U)) = v := by
    have h1 : z (e.symm v : U) = e (e.symm v) := he (e.map_target hv)
    show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v
    rw [(A.chart i).left_inv hi, h1, e.right_inv hv]

  set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def
  have hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hhc : ContinuousAt h v :=
    ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v)
      ((A.chart i).continuousAt hi) hcoe
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target := e.open_target.mem_nhds hv

  have hright : ∀ᶠ v' in 𝓝 v, g (h v') = v' := by
    filter_upwards [hsrc, htgt] with v' h1 h2
    have h3 : z (e.symm v') = e (e.symm v') := he (e.map_target h2)
    show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'
    rw [(A.chart i).left_inv h1, h3, e.right_inv h2]

  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v' :=
    hhc.tendsto.eventually hstrict.eventually_left_inverse
  have heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U)) := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hinv := hstrict.to_localInverse
  rw [hgv] at hinv
  have hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v := by
    have := hg.to_localInverse hf' hn
    rw [hgv] at this
    exact this
  refine ⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩
  have hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n) :=
    heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv
  change fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ
  rw [hfd]
  exact f'.symm_apply_apply ξ

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvResCounitCompatStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_res_counit_compat : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  first | exact @GlobalTheory.QLog.Chart.ev_res_counit | exact GlobalTheory.QLog.Chart.ev_res_counit | (intros; apply GlobalTheory.QLog.Chart.ev_res_counit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEqStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_swap_eq' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  first | exact @GlobalTheory.CommSwap.eval_swap_eq | exact GlobalTheory.CommSwap.eval_swap_eq | (intros; apply GlobalTheory.CommSwap.eval_swap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTop
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMu
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WTop

theorem mulVec_add_mul {R ι : Type} [CommRing R] [Fintype ι] (N : Matrix ι ι R) (a b : ι → R) (s : R) (i : ι) :
    N.mulVec (fun j => a j + s * b j) i = N.mulVec a i + s * N.mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 1000000 in
theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ N v0 hN h
  choose c hc using h
  obtain ⟨z, hz⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι N hN).1 c
  refine ⟨fun i => v0 i + Sandwich.mu ε * z i, fun i => ⟨z i, by ring⟩, fun i => ?_⟩
  have hw : (fun j => WittVector.frobenius (v0 j + Sandwich.mu ε * z j)) =
      fun j => WittVector.frobenius (v0 j) +
        (WittVector.frobenius (xi ε) * Sandwich.mu ε) * WittVector.frobenius (z j) := by
    funext j
    rw [map_add (f := _), map_mul, GlobalTheory.WinLift.frob_mu]
  rw [hw, mulVec_add_mul]
  linear_combination (-1 : Ainf p O) * hc i + WittVector.frobenius (xi ε) * Sandwich.mu ε * hz i

end GlobalTheory.WTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPow
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algHom_algebraicClosure_apply_eq_pow :
    ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m →
      ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  intro Ω _ K0 x hx m hm
  classical
  have h1 : AlgebraicIndepOn K0 id ({x} : Set Ω) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let i₀ : s := ⟨x, hxs rfl⟩
  have h2 := (algebraicIndependent_update_pow hs.1 i₀ hm).map'
    (f := IsScalarTower.toAlgHom K0 Ω (AlgebraicClosure Ω))
    (algebraMap Ω (AlgebraicClosure Ω)).injective
  obtain ⟨j, hj⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hs h2
  exact ⟨j, by simpa [i₀] using hj i₀⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharSeries
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ}

theorem res_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    G.res n (c.ev (n + 1) f) = c.ev n f := by
  haveI : IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval (n + 1)) (G.res n : G.A (n + 1) →ₐ[O] G.A n)
  have h' : IsEval p (c.x n) ((G.res n : G.A (n + 1) →ₐ[O] G.A n).comp (c.ev (n + 1))) := by
    convert h using 2 with i
    exact (c.res n i).symm
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] G.A n => E f)
    (GlobalTheory.CEval.eval_unique p (c.x n) _ _ h' (c.isEval n))

theorem counit_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f := by
  let E₂ : MvPowerSeries (Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r) = r
        rw [← c_eq_algebraMap]; simp }
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval n) (Bialgebra.counitAlgHom O (G.A n))
  have h₁ : IsEval p (fun _ : Fin d => (0 : O))
      ((Bialgebra.counitAlgHom O (G.A n)).comp (c.ev n)) := by
    convert h using 2 with i
    exact (c.aug n i).symm
  have h₂ : IsEval p (fun _ : Fin d => (0 : O)) E₂ := by
    refine ⟨fun i => by simp [E₂], fun m => ⟨1, fun g hg => ?_⟩⟩
    have : constantCoeff g = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hg 0 (by simp)
    show (p : O) ^ m ∣ constantCoeff g
    rw [this]
    exact dvd_zero _
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] O => E f)
    (GlobalTheory.CEval.eval_unique p (fun _ => (0 : O)) _ _ h₁ h₂)

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog

theorem exists_charSeries : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  intro p _ O _ _ _ G d c χ
  haveI : ∀ n, IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) := fun n =>
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  obtain ⟨u, hu⟩ := (GlobalTheory.Limits.exists_unique_of_compatible p O (Fin d) G.A
    (fun n => (G.res n : G.A (n + 1) →ₐ[O] G.A n)) c.x c.ev c.isEval
    (fun n f => c.res_ev n f) c.ker).2 c.surj (charElem χ) (fun n => res_charElem χ n)
  refine ⟨u, ?_, hu⟩
  rw [← c.counit_ev 0 u, hu 0]
  exact (isGroupLikeElem_charElem χ 0).counit_eq_one

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnected
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.exists_coords_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, hcou, hres, hspan, hl⟩ := GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates p C v O hv G
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O))
  have hmem : ∀ n i, ¬IsUnit (x n i) := by
    intro n i hu
    have h1 := hu.map (Bialgebra.counitAlgHom O (G.A n))
    rw [Bialgebra.counitAlgHom_apply, hcou n i] at h1
    exact not_isUnit_zero h1
  have hnil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N := fun n i => by
    haveI := hG n
    exact _root_.GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers p hp0 C v O hv (G.A n) (x n i) ((IsLocalRing.mem_maximalIdeal _).2 (hmem n i))
  have hex : ∀ n, ∃ E : MvPowerSeries (Fin d) O →ₐ[O] G.A n, IsEval p (x n) E := fun n => by
    haveI := _root_.GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective p O (G.A n)
    exact ((_root_.GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) (x n) (hnil n)).1).exists
  choose ev hev using hex
  have hpoly : ∀ n (P : MvPolynomial (Fin d) O),
      ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (x n) P := by
    intro n P
    have h : (ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (x n) :=
      MvPolynomial.algHom_ext fun i => by
        simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (hev n).1 i]
    exact DFunLike.congr_fun h P
  refine ⟨d, x, ev, hnil, hev, hres, hcou, fun n => ?_, fun m N => ?_⟩
  · haveI := hG n
    intro a
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.NakAug.surj O (G.A n) (p : O) hpm (Bialgebra.counitAlgHom O (G.A n)) d (x n)
      (fun i => by rw [Bialgebra.counitAlgHom_apply]; exact hcou n i)
      (fun i => by simpa [map_natCast] using hnil n i) (hspan n) a
    exact ⟨P, (hpoly n P).trans hP⟩
  · obtain ⟨K, hK0, hK⟩ := _root_.GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero d N
    obtain ⟨e, u, hu, hKu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0.ne' p (Fact.out : p.Prime).ne_one
    refine ⟨m + e, fun f hf α hα => ?_⟩
    obtain ⟨P, hPdeg, hPco, hPmem⟩ := _root_.GlobalTheory.trunc_dec p O (G.A (m + e)) d (x (m + e)) (ev (m + e)) (hev _) (m + e) N f hf
    obtain ⟨l, hlx⟩ := hl (m + e)
    let I : Ideal O := Ideal.span {(p : O) ^ (m + e)}
    let l' : Fin d → (G.A (m + e) →ₗ[O] O ⧸ I) :=
      fun i => l i ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (G.A (m + e)))
    obtain ⟨D, hD⟩ := GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra O (G.A (m + e)) I d l' (fun i a b => by
      simp only [l', LinearMap.comp_apply, AugCot.d_mul, map_add (f := _), map_smul, Bialgebra.counitAlgHom_apply])
    let φ : G.A (m + e) →ₐ[O] (O ⧸ I) ⊗[O] G.A (m + e) := Algebra.TensorProduct.includeRight
    have hy0 : ∀ j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (φ (x (m + e) j)) = 0 := by
      intro j
      simp [φ, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul, hcou]
    have hDy : ∀ i j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (D i (φ (x (m + e) j))) =
        if i = j then 1 else 0 := fun i j => (hD i _).trans (hlx i j)
    have hdeg : ∀ β : Fin d →₀ ℕ, N ≤ β.degree →
        AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap O (O ⧸ I)) P) β = 0 := fun β hβ => by
      rw [MvPolynomial.coeff_map, hPdeg β hβ, map_zero]
    have hmemB : MvPolynomial.aeval (fun j => φ (x (m + e) j)) (MvPolynomial.map (algebraMap O (O ⧸ I)) P) ∈
        RingHom.ker (Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e))) ^ N := by
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      refine (Ideal.map_le_iff_le_comap.1 ?_) hPmem
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
      refine sup_le (Ideal.pow_right_mono ?_ N) ?_
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hy0 j
      · rw [Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
        have h0 : φ ((p : G.A (m + e)) ^ (m + e)) = 0 := by
          rw [map_pow, map_natCast]
          have h1 : ((p : (O ⧸ I) ⊗[O] G.A (m + e))) ^ (m + e) =
              algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ((p : O) ^ (m + e))) := by
            rw [map_pow, map_pow, map_natCast, map_natCast]
          rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
        rw [SetLike.mem_coe, h0]
        exact zero_mem _
    have key := hK (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) _ _ D hy0 hDy _ hdeg hmemB α
    rw [MvPolynomial.coeff_map, ← map_natCast (algebraMap O (O ⧸ I)), ← map_mul,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at key
    rw [← hPco α hα]
    have hpO : (p : O) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at h2
      exact hp0 (by exact_mod_cast h2)
    have hunit : IsUnit (u : O) := by
      by_contra hnu
      have hcop : IsCoprime (u : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2
        ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hu)))
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
      have h3 : a * Int.castRingHom O u + b * Int.castRingHom O p ∈ IsLocalRing.maximalIdeal O := by
        refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using (IsLocalRing.mem_maximalIdeal _).2 hnu
        · simpa using hpm
      rw [hab] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [hKu, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm ((p : O) ^ m)] at key
    have key2 := (mul_dvd_mul_iff_left (pow_ne_zero e hpO)).1 key
    exact (hunit.dvd_mul_left).1 key2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrimeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  first | (exact @GlobalTheory.StrictHensPrime.exists_sh_indEt) | (exact GlobalTheory.StrictHensPrime.exists_sh_indEt) | (intros; apply GlobalTheory.StrictHensPrime.exists_sh_indEt  <;> assumption)
end

