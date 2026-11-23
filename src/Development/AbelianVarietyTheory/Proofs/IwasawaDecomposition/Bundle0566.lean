module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.eventually_mem_of_graph {n g : ℕ} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} {b₀ : Fin n → ℂ}
    {w₀ : Fin g → ℂ} {ζ : (Fin n → ℂ) → Fin g → ℂ} (hζ0 : ζ b₀ = w₀) (hζc : ContinuousAt ζ b₀)
    (hζ : ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1) : ∀ᶠ b in 𝓝 b₀, ζ b ∈ K b := by
  have ht : Filter.Tendsto (fun b => (b, ζ b)) (𝓝 b₀) (𝓝 (b₀, w₀)) := by
    have := (continuousAt_id.prodMk hζc).tendsto
    simpa [hζ0] using this
  filter_upwards [ht.eventually hζ] with b hb
  exact hb.2 rfl

theorem exists_isLatBasis_of_discrete {g : ℕ} (H : AddSubgroup (Fin g → ℂ))
    (hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H → w = 0)
    (hs : Submodule.span ℝ (H : Set (Fin g → ℂ)) = ⊤) :
    ∃ β : Fin (2 * g) → Fin g → ℂ, IsLatBasis (H : Set (Fin g → ℂ)) β := by
  set L : Submodule ℤ (Fin g → ℂ) := H.toIntSubmodule with hL
  have hLset : (L : Set (Fin g → ℂ)) = H := rfl
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hd
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext (hU x.1 hx x.2)
    · rintro rfl
      exact h0U
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hs⟩
  have hr : Module.finrank ℤ L = 2 * g := by
    rw [ZLattice.rank ℝ L, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨fun j => (b j : Fin g → ℂ), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have he : (fun j => (b j : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ L) :=
      funext fun j => (Module.Basis.ofZLatticeBasis_apply ℝ L b j).symm
    rw [he]
    exact (b.ofZLatticeBasis ℝ L).linearIndependent
  · refine ⟨b.repr ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun x : L => (x : Fin g → ℂ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · rintro ⟨m, rfl⟩
    exact H.sum_mem fun j _ => H.zsmul_mem (b j).2 _

theorem IsLatFam.eventually_intComb {n g r : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    {b₀ : Fin n → ℂ} (hK : IsLatFam B K) (hb₀ : b₀ ∈ B) {lam : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (hlc : ContinuousAt lam b₀) (hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, lam b j ∈ K b) (hβ : IsLatBasis (K b₀) (lam b₀))
    (y : Fin g → ℂ) :
    ∀ᶠ q in 𝓝 (b₀, y), q.2 ∈ K q.1 → ∃ m : Fin r → ℤ, q.2 = ∑ j, m j • lam q.1 j := by
  by_cases hy : y ∈ K b₀
  · obtain ⟨m, hm⟩ := (hβ.2 y).1 hy
    obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ y hy
    set f : (Fin n → ℂ) → Fin g → ℂ := fun b => ∑ j, m j • lam b j with hf
    have hfc : ContinuousAt f b₀ := by
      have : Continuous (fun v : Fin r → Fin g → ℂ => ∑ j, m j • v j) := by fun_prop
      exact this.continuousAt.comp hlc
    have hf0 : f b₀ = y := hm.symm
    have hfK : ∀ᶠ b in 𝓝 b₀, f b ∈ K b := by
      filter_upwards [hlK, hK.1.mem_nhds hb₀] with b hb hbB
      obtain ⟨H, hH⟩ := hK.2.1 b hbB
      rw [← hH] at hb ⊢
      exact H.sum_mem fun j _ => H.zsmul_mem (hb j) _
    have ht : Filter.Tendsto (fun b => (b, f b)) (𝓝 b₀) (𝓝 (b₀, y)) := by
      have := (continuousAt_id.prodMk hfc).tendsto
      simpa [hf0] using this
    have hfζ : ∀ᶠ b in 𝓝 b₀, f b = ζ b := by
      filter_upwards [ht.eventually hζ, hfK] with b h1 h2
      exact h1.1 h2
    have hq : ∀ᶠ q : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, y), f q.1 = ζ q.1 :=
      (continuous_fst.tendsto (b₀, y)).eventually hfζ
    filter_upwards [hq, hζ] with q h1 h2 h3
    exact ⟨m, (h2.1 h3).trans h1.symm⟩
  · have ho := hK.2.2.1.mem_nhds (show (b₀, y) ∈ {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} from ⟨hb₀, hy⟩)
    filter_upwards [ho] with q hq h
    exact absurd h hq.2

theorem isLatBasis_of_ball {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ) (R : ℝ)
    (hli : LinearIndependent ℝ lam) (hmem : ∀ j, lam j ∈ H) (hR : ∑ j, ‖lam j‖ ≤ R)
    (hball : ∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • lam j) :
    IsLatBasis (H : Set (Fin g → ℂ)) lam := by
  first
  | exact @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | (apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall ..)

theorem IsLatFam.exists_analytic_locBasis : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    ∃ lam : (Fin n → ℂ) → Fin (2 * g) → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b) := by
  intro n g B K b₀ hK hb₀ hs
  obtain ⟨H₀, hH₀⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH₀]; exact H₀.zero_mem
  obtain ⟨ζ₀, hζ₀0, -, hζ₀⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H₀ → w = 0 := by
    have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    filter_upwards [ht.eventually hζ₀] with w hw hwH
    have hwK : w ∈ K b₀ := by rw [← hH₀]; exact hwH
    rw [hw.1 hwK, hζ₀0]
  obtain ⟨β, hβ⟩ := exists_isLatBasis_of_discrete H₀ hd (by rw [hH₀]; exact hs)
  rw [hH₀] at hβ
  have hβK : ∀ j, β j ∈ K b₀ := fun j =>
    (hβ.2 (β j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  choose ζ hζ0 hζa hζ using fun j => hK.2.2.2 b₀ hb₀ (β j) (hβK j)
  have hla : AnalyticAt ℂ (fun b j => ζ j b) b₀ := AnalyticAt.pi hζa
  have hlc := hla.continuousAt
  have hl0 : (fun j => ζ j b₀) = β := funext hζ0
  have hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, ζ j b ∈ K b :=
    Filter.eventually_all.2 fun j => IsLatFam.eventually_mem_of_graph (hζ0 j) (hζa j).continuousAt (hζ j)
  have hβ' : IsLatBasis (K b₀) ((fun b j => ζ j b) b₀) := by
    show IsLatBasis (K b₀) (fun j => ζ j b₀)
    rw [hl0]; exact hβ
  set R : ℝ := ∑ j, (‖β j‖ + 1) with hR
  have hball := (isCompact_closedBall (0 : Fin g → ℂ) R).eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b w => w ∈ K b → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • ζ j b) fun y _ => IsLatFam.eventually_intComb hK hb₀ hlc hlK hβ' y
  have hli : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ (fun j => ζ j b) := by
    have h1 : LinearIndependent ℝ ((fun b j => ζ j b) b₀) := hβ'.1
    exact hlc.tendsto.eventually h1.eventually
  have hnorm : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖ζ j b‖ ≤ ‖β j‖ + 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => ‖ζ j b‖) b₀ := (hζa j).continuousAt.norm
    have hlt : (fun b => ‖ζ j b‖) b₀ < (fun _ => ‖β j‖ + 1) b₀ := by simp [hζ0 j]
    filter_upwards [hc.eventually_lt continuousAt_const hlt] with b hb
    exact hb.le
  refine ⟨fun b j => ζ j b, hla, ?_⟩
  filter_upwards [hball, hli, hnorm, hlK, hK.1.mem_nhds hb₀] with b h1 h2 h3 h4 h5
  obtain ⟨H, hH⟩ := hK.2.1 b h5
  rw [← hH]
  refine isLatBasis_of_ball H _ R h2 (fun j => ?_) (Finset.sum_le_sum fun j _ => h3 j) fun w hw hwH => ?_
  · show ζ j b ∈ (H : Set (Fin g → ℂ)); rw [hH]; exact h4 j
  · exact h1 w hw (by rw [← hH]; exact hwH)

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultiple
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

open GlobalTheory GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare

theorem exists_thetaChar_mulVec_ne {g : ℕ} (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hh : IsUnit h.det) : ∃ z, thetaChar τ c₁ c₂ (h.mulVec z) ≠ 0 := by
  have re : ∀ c : Fin g → ℂ, (∀ k, c k = 0 ∨ c k = 1 / 2) → (fun i => (((c i).re : ℝ) : ℂ)) = c := by
    intro c hc
    funext i
    rcases hc i with e | e <;> rw [e] <;> norm_num
  have hne := GlobalTheory.CanTh.thetaChar_ne_zero hs hp (fun i => (c₁ i).re) (fun i => (c₂ i).re)
  rw [re c₁ h₁, re c₂ h₂] at hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  refine ⟨h⁻¹.mulVec z₀, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  exact hz₀

theorem exists_unif_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hσ hty hP hover hgen hM
  have hh : IsUnit Θ.h.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
    ext i k
    have e := congrFun (Θ.per 0 k).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
  refine ⟨Ha.T, fun w hw yF hy₁ hy₂ hz x φ hx => ?_⟩
  have hPer := Ha.period w hw
  obtain ⟨fr, hf₁, hf₂, hf₃, -, s, hs⟩ := Θ.frame w hw
  obtain ⟨-, wx, -, hgp, hwx, -, -, -⟩ := hx
  obtain ⟨φ', hφ₁, hφ₂, hgp', hiso⟩ := _root_.GlobalTheory.GenericFibrePoint.fibre_map_univ E H Dw l Xo c _ _ Y yF x φ hgp ⟨wx, hwx⟩
  rw [hy₁] at hgp'
  have hL := Xo.univ.t.PP.isLB
  have hM' := LB.isLB_pull hL (φ' ≫ Y.m0.toSABMap.φ)
  let u₁ := fibreUnif hgp' (Fu.ex Ha.i (Ha.Pw w)) (Ha.Pw w).range fr (Fu.ex_add _ _ hPer) (Fu.ex_onto _ _ hPer)
    (Fu.ex_ker _ _ hPer) hPer.2.2.1 hPer.2.2.2.1 (isHolTo_exp Fu Ha.i hPer) hf₁ hf₂ hf₃
  obtain ⟨wI, hwI⟩ := LBIso.symm hiso
  let u₂ := carry u₁ hM' x.P.isLB hwI
  have hex₁ : ∀ z, (u₂.ex z).left ≫ φ' ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left := fun z =>
    liftPt_comp hgp' _
  obtain hθ : ∃ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) ≠ 0 :=
    exists_thetaChar_mulVec_ne _ _ _ _ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ hh

  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.FibreKeyTheta.th_isFn_const_mul x _ Xo.univ.t.G Xo.univ.t.PP.L (Fu.u Ha.i (Ha.Pw w)) (φ' ≫ Y.m0.toSABMap.φ) g u₂ wI
    (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr s hL hgp'.1 hwI hθ
    (fun j z hj => hf₂ j z (by rwa [hex₁] at hj))
    (fun k j z hkj => by
      obtain ⟨hk, hj⟩ := (top_le_preimage_inf _ _ _).1 hkj
      exact carry_fr u₁ hM' x.P.isLB hwI k j z hk hj)
    (fun j z p hp₁ hp₂ hj => hs j z p (hp₁.trans (hex₁ z)) hp₂ (by rwa [hex₁] at hj))
  obtain ⟨u₃, lam, hlam, hex, hΛ, hR, hfr⟩ := _root_.GlobalTheory.RigRescale.exists_rescale_rig x.P.A x.P.L g u₂ x.rig x.P.isLB x.rig_gen
  have hFn : u₃.IsFn x.th fun z => c₁ / lam * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) := by
    intro i z hi
    rw [hex] at hi ⊢
    rw [hc₁ i z hi, hfr]
    field_simp
  have hdim : g = x.P.g := by
    obtain ⟨u₀, -, -, -, -, -, hv, hw', -⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
    obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g g u₀ hv hw' u₃.ex u₃.ex_add
      (fun U f => by simpa only [Set.mem_univ, true_and] using u₃.hol U f)
    exact AHWeil.dim_eq u₃ u₀ F hF
  refine ⟨hdim.symm, u₃, c₁ / lam, hR, fun z => ⟨(u₃.ex z).left ≫ φ', ?_, ?_, ?_⟩, hΛ, hFn⟩
  · rw [Category.assoc, hex]
    exact hex₁ z
  · rw [Category.assoc, ← Category.assoc φ', hφ₂, Category.assoc, ← Category.assoc (u₃.ex z).left, Over.w (u₃.ex z),
      hy₂]
    exact Category.id_comp _
  · rw [Category.assoc, hφ₁]

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim


open scoped CategoryTheory.MonObj in
theorem exists_transfer {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 → ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z hz => ?_⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _

theorem eventually_eq_of_lattice {B La V : Type} [TopologicalSpace B] [AddCommGroup La] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : B → (La →+ V)) (hP : ∀ a, Continuous fun b => P b a)
    (b₀ : B) (hinj : Function.Injective (P b₀)) (hd : DiscreteTopology (P b₀).range)
    (hs : Submodule.span ℝ (Set.range (P b₀)) = ⊤) (a : B → La) (ha : Continuous fun b => P b (a b)) :
    ∀ᶠ b in 𝓝 b₀, a b = a b₀ := by
  classical
  let L : Submodule ℤ V := (P b₀).range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  let bz := Module.Free.chooseBasis ℤ L
  let bR := bz.ofZLatticeBasis ℝ L
  have hc : ∀ i, ∃ c, P b₀ c = bR i := fun i => by
    rw [Module.Basis.ofZLatticeBasis_apply]; exact (bz i).2
  choose c hc using hc
  let T : B → V →L[ℝ] V := fun b => ∑ i, (LinearMap.toContinuousLinearMap (bR.coord i)).smulRight (P b (c i))
  have hT : ∀ b x, T b x = ∑ i, bR.repr x i • P b (c i) := fun b x => by simp [T]
  have hTc : Continuous T := continuous_finsetSum _ fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ V V (LinearMap.toContinuousLinearMap (bR.coord i))).continuous.comp (hP _)
  have hT0 : T b₀ = ContinuousLinearMap.id ℝ V := by
    ext x
    rw [hT]
    simp only [hc]
    exact bR.sum_repr x
  have hTP : ∀ b x, T b (P b₀ x) = P b x := fun b x => by
    let xl : L := ⟨P b₀ x, x, rfl⟩
    have h1 : ∀ i, bR.repr (P b₀ x) i = (bz.repr xl i : ℝ) := fun i => bz.ofZLatticeBasis_repr_apply ℝ L xl i
    have h2 : x = ∑ i, bz.repr xl i • c i := hinj (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul, hc]
      rw [← bR.sum_repr (P b₀ x)]
      exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul])
    rw [hT]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [h2, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul, map_zsmul]
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set L)) 0 rfl
  have h1 : ∀ᶠ b in 𝓝 b₀, ‖T b - T b₀‖ < 1 / 2 := by
    have : Tendsto (fun b => ‖T b - T b₀‖) (𝓝 b₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hTc.tendsto b₀)
    exact this.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ b in 𝓝 b₀, ‖P b (a b) - P b (a b₀)‖ < ε / 2 := by
    have : Tendsto (fun b => ‖P b (a b) - P b (a b₀)‖) (𝓝 b₀) (𝓝 ‖P b₀ (a b₀) - P b₀ (a b₀)‖) :=
      ((ha.sub (hP _)).norm.tendsto b₀)
    rw [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [h1, h2] with b h1 h2
  rw [← map_sub, ← hTP] at h2
  set x := P b₀ (a b - a b₀) with hx
  have h3 : ‖T b x - x‖ ≤ 1 / 2 * ‖x‖ := by
    have := (T b - T b₀).le_of_opNorm_le h1.le x
    rwa [hT0] at this
  have h4 : ‖x‖ ≤ ‖T b x‖ + ‖T b x - x‖ := by
    have := norm_sub_le (T b x) (T b x - x)
    rwa [sub_sub_cancel] at this
  have h5 : (⟨x, _, rfl⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [mem_ball_zero_iff]
    show ‖x‖ < ε
    linarith
  have h6 : x = 0 := congrArg Subtype.val (hb h5)
  exact sub_eq_zero.1 (hinj (h6.trans (map_zero _).symm))

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun w => ‖eTwoPi w‖) = fun w : ℂ => Real.exp (-(2 * Real.pi * w.im)) := funext fun w => by
    rw [eTwoPi, Complex.norm_exp]
    simp
  rw [h]
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_comap (f := Complex.im) (x := atTop)).const_mul_atTop (by positivity))

theorem span_proj {n g m : ℕ} (lam : Fin n → Fin g → ℂ) (h : Submodule.span ℂ (Set.range lam) = ⊤) (s : Fin m → Fin g)
    (hs : Function.Injective s) : Submodule.span ℂ (Set.range fun j i => lam j (s i)) = ⊤ := by
  have : (fun j i => lam j (s i)) = LinearMap.funLeft ℂ ℂ s ∘ lam := rfl
  rw [this, Set.range_comp, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact LinearMap.funLeft_surjective_of_injective ℂ ℂ s hs

theorem continuous_perFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {B : Type}
    [TopologicalSpace B] {x : B → Frame X.Ψ r} (hx : ∀ b, x b ∈ X.dom) (hc : Continuous x) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ) : Continuous fun b => perFr X (x b) v τ i := by
  have hm : ∀ t, Continuous fun b => mat (x b) t := fun t => (continuous_apply t).comp hc
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · refine (continuous_apply (⟨X.p0 + i, h2⟩ : Fin r)).comp
      (Continuous.matrix_mulVec (A := fun b => (mat (x b) ⟨τ, h1⟩)⁻¹) ?_ continuous_const)
    refine continuous_iff_continuousAt.2 fun b => (continuousAt_matrix_inv _ ?_).comp (hm _).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx b _).1
  · exact continuous_const
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
      (((hm _).matrix_elem _ _).mul continuous_const).mul continuous_const
  · exact continuous_const
  · exact continuous_const

theorem exists_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  obtain ⟨ρ, n, lam, hρ, hρr, hcont, hspan, hker⟩ := _root_.GlobalTheory.ShFam.BdArc.exists_lattice_sections E H Dw l Xo c O β Z σ A φ x fr ψ r g e harc
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → T < w.im ∧ eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := by
    have h1 : ∀ᶠ w in imTop, eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := tendsto_eTwoPi.eventually (Metric.ball_mem_nhds 0 hρ)
    obtain ⟨a, ha⟩ := eventually_atTop.1 (eventually_comap.1 h1)
    exact ⟨max a T, fun w hw => ⟨(le_max_right _ _).trans_lt hw, ha _ ((le_max_left _ _).trans hw.le) w rfl⟩⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  have key : ∀ (b : B) j, lam j (eTwoPi b) ∈ (Pm b).range := fun b j => by
    have hb := (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ (Metric.ball_subset_ball hρr hb) (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    refine (F.ex_ker _ _ (hper b) _).1 (a4 _ (hker _ hb ex a1 a2 (fun jj => ?_) j))
    obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
    have hd := hder b (e jj).1 (e jj).2
    rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
    exact w3 ▸ a3 _ w w1 hd
  choose a ha using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact continuous_perFr _ hdom hxc _ _ _
  have hec : Continuous eTwoPi := by unfold eTwoPi; fun_prop
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ j b, a b j = a b₀ j := fun j b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := fun b => a b j)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    refine eventually_eq_of_lattice Pm hPc b' (hper b').2.1 (hper b').2.2.1 (hper b').2.2.2.1 (fun b => a b j) ?_
    simp only [ha]
    exact (hcont j).comp_continuous (hec.comp continuous_subtype_val) fun b => (hT₁ b b.2).2
  have hlim : ∀ j jj, Tendsto (fun w => perFr (U.X k) (xx w) (φL k (a b₀ j) : Fin N → E) (relab c σ (e jj).1) (e jj).2)
      imTop (𝓝 (lam j 0 jj)) := fun j jj => by
    have h1 : Tendsto (fun w => lam j (eTwoPi w) jj) imTop (𝓝 (lam j 0 jj)) :=
      ((continuous_apply jj).tendsto _).comp
        ((((hcont j).continuousAt (Metric.ball_mem_nhds 0 hρ)).tendsto).comp tendsto_eTwoPi)
    refine h1.congr' ?_
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)] with w hw
    rw [← ha ⟨w, hw⟩ j, hconst, hPm]
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  choose sp hsp hsp' using fun τ : (U.X k).Ψ => hidx τ.1 (N - (U.X k).p0) (by
    rw [if_pos (((hX k).2 _).1 τ.2), (hX k).1, hN, Nat.add_sub_cancel])
  choose sm hsm hsm' using fun τ : (U.X k).Ψ => hidx (conjEmb τ.1) (U.X k).p0 (by
    rw [if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 (((hX k).2 (conjEmb τ.1)).2 h), (hX k).1])
  refine ⟨n, fun j => φL k (a b₀ j), fun j τ i => lam j 0 (sp τ i), fun j τ i => lam j 0 (sm τ i), fun j τ i => ?_,
    fun j τ i => ?_, fun τ => ⟨span_proj _ hspan _ (hsp τ), span_proj _ hspan _ (hsm τ)⟩⟩
  · have := hlim j (sp τ i)
    rwa [(hsp' τ i).1, (hsp' τ i).2] at this
  · have := hlim j (sm τ i)
    rwa [(hsm' τ i).1, (hsm' τ i).2] at this

end GlobalTheory.ShFam.PerLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) → ∑ i, c i • toReal (γ i) ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | exact GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | (intros; apply GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone <;> assumption)
end

