module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.JacMeas

open GlobalTheory.SemiHaar

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def lv : UX D ρ →* GA D S := d.levi.comp (UX D ρ).subtype

theorem lv_mem (u : UX D ρ) : lv d u ∈ flagN d := d.levi_mem_NFlag u.2

theorem radX_le : radX d ≤ flagN d := inf_le_left

theorem lv_conj (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : lv d u * n * (lv d u)⁻¹ ∈ radX d := by
  refine ⟨(flagN d).mul_mem ((flagN d).mul_mem (lv_mem d u) hn.1) ((flagN d).inv_mem (lv_mem d u)), ?_⟩
  change mt S (d.levi u.1 * n * (d.levi u.1)⁻¹) ⬝ d.jX = d.jX
  rw [← map_inv, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n),
    mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem anisotropicEmbedding_conj_wittFlagUnipotentFixer (n : GA D S) (hn : n ∈ radX d) (h : GA D S₀) : d.emb0 h * n * (d.emb0 h)⁻¹ ∈ radX d :=
  ⟨(flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n hn.1 h,
    (stabX d).mul_mem ((stabX d).mul_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h) hn.2) ((stabX d).inv_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h))⟩

theorem radX_sup_lv : radX d ⊔ (lv d).range = flagN d := by
  refine le_antisymm (sup_le (radX_le d) (by rintro _ ⟨u, rfl⟩; exact lv_mem d u)) fun n hn => ?_
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  exact mul_mem (Subgroup.mem_sup_right ⟨⟨u, hu⟩, rfl⟩)
    (Subgroup.mem_sup_left (mul_mem (nB_mem_radX d b) (nC_mem_radX d c)))

theorem wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer : radX d ⊔ d.emb0.range = stabX d := by
  refine le_antisymm (sup_le (radX_le_stabX d) (by rintro _ ⟨u, rfl⟩; exact wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d u)) fun g hg => ?_
  obtain ⟨n, hn, h, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 g).1 hg
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem blockX_mul_lv {n : GA D S} (hn : n ∈ radX d) (u : UX D ρ) : blockX d (n * lv d u) = u.1.1 := by
  change d.pX ⬝ (mt S (n * d.levi u.1) ⬝ d.jX) = _
  rw [mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n), mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.pX_jX,
    Matrix.one_mul]

theorem exists_rad_lv {n : GA D S} (hn : n ∈ flagN d) : ∃ n₀ ∈ radX d, ∃ u, n = n₀ * lv d u :=
  exists_mul_of_mem_sup_range (radX d) (lv d) (lv_conj d) (by rw [radX_sup_lv]; exact hn)

theorem continuous_blockX : Continuous (blockX d) :=
  continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)

theorem isClosed_stabX : IsClosed (stabX d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  exact isClosed_eq ((continuous_mt S).matrix_mul continuous_const) continuous_const

theorem isClosed_flagN : IsClosed (flagN d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  haveI := (lattice_Mx D S₀.rank S₀.rank).2.2.2.1
  have e : (flagN d : Set (GA D S)) = (blockX d ⁻¹' GlobalTheory.UnitU.uniSet D ρ) ∩
      ({g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g} ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) = 1}) := by
    ext g
    constructor
    · intro hg
      refine ⟨?_, ?_, (GlobalTheory.JacProj.flag_le d hg).2⟩
      · obtain ⟨n, hn, u, rfl⟩ := exists_rad_lv d hg
        rw [Set.mem_preimage, blockX_mul_lv d hn]
        exact u.2
      · exact GlobalTheory.JacProj.keeps_jX d (GlobalTheory.JacProj.flag_le d hg).1
    · rintro ⟨h1, h2, h3⟩
      let u : UX D ρ := ⟨GlobalTheory.UnitU.toUnit _ h1, h1⟩
      have hs : (lv d u)⁻¹ * g ∈ stabX d := by
        change mt S ((lv d u)⁻¹ * g) ⬝ d.jX = d.jX
        have h4 : mt S g ⬝ d.jX = mt S (lv d u) ⬝ d.jX := (show _ = _ from h2).trans (d.levi_jX u.1).symm
        rw [mt_mul, Matrix.mul_assoc, h4, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
      obtain ⟨n, hn, h, he⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hs
      have hg : g = lv d u * n * d.emb0 h := by rw [mul_assoc, ← he, mul_inv_cancel_left]
      have hn' : lv d u * n ∈ flagN d := mul_mem (lv_mem d u) hn.1
      have h5 := GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn' h
      rw [← hg, show d.p0 ⬝ (mt S g ⬝ d.j0) = 1 from h3] at h5
      have h6 : h = 1 := mt_injective S₀ (h5.symm.trans (mt_one S₀).symm)
      rw [hg, h6, map_one, mul_one]
      exact hn'
  rw [e]
  exact ((GlobalTheory.UnitU.isClosed_uniSet D ρ).preimage (continuous_blockX d)).inter
    ((isClosed_eq ((continuous_mt S).matrix_mul continuous_const) (continuous_const.matrix_mul (continuous_blockX d))).inter
      (isClosed_eq (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)) continuous_const))

theorem isClosed_radX : IsClosed (radX d : Set (GA D S)) := (isClosed_flagN d).inter (isClosed_stabX d)

theorem exists_proj_lv : ∃ p : flagN d → UX D ρ, Continuous p ∧
    ∀ (u : UX D ρ) (n : radX d) (hm : n.1 * lv d u ∈ flagN d), p ⟨n.1 * lv d u, hm⟩ = u := by
  choose n₀ hn₀ p hp using fun g : flagN d => exists_rad_lv d g.2
  have hb : ∀ g, (p g).1.1 = blockX d g.1 := fun g => by rw [hp g, blockX_mul_lv d (hn₀ g)]
  refine ⟨p, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isInducing.continuous_iff.2 ?_, fun u n hm => ?_⟩
  · exact ((continuous_blockX d).comp continuous_subtype_val).congr fun g => (hb g).symm
  · exact Subtype.ext (Units.ext ((hb _).trans (blockX_mul_lv d n.2 u)))

theorem rat_lv (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : n * lv d u ∈ GQ S ↔ n ∈ GQ S ∧ u ∈ UXQ D ρ := by
  have hb : ∀ g ∈ GQ S, blockX d g ∈ ratMx D ρ ρ := fun g hg =>
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S g).1 hg) (rat_mem _))
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (d.levi_mem_GQ h.2.1 h.2.2)⟩
  have h1 := hb _ h
  have h2 := hb _ (inv_mem h)
  rw [show (n * lv d u)⁻¹ = (lv d u⁻¹ * n⁻¹ * (lv d u⁻¹)⁻¹) * lv d u⁻¹ by simp,
    blockX_mul_lv d (lv_conj d _ (inv_mem hn) _)] at h2
  rw [blockX_mul_lv d hn] at h1
  refine ⟨?_, h1, h2⟩
  rw [show n = n * lv d u * (lv d u)⁻¹ by simp]
  exact mul_mem h (inv_mem (d.levi_mem_GQ h1 h2))

theorem jac_measure : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  intro D ρ J vU ν₀ 𝓝₀ hν₀ h𝓝₀ h𝓝₀1
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have k4 := (GlobalTheory.UnitU.rational D ρ).1
  have k5 : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨hU, 𝓤, h𝓤, h𝓤1⟩ := vU.unit
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hle : radX J.d ⊔ J.d.emb0.range ≤ flagN J.d ⊔ J.d.emb0.range := sup_le_sup_right (radX_le J.d) _
  have H0 := semiMeas_haar_inv (radX J.d) J.d.emb0 (isClosed_radX J.d) J.d.continuous_embed (anisotropicEmbedding_conj_wittFlagUnipotentFixer J.d)
    ⟨fun g => p (Subgroup.inclusion hle g), hpc.comp (continuous_inclusion hle), fun h n => hp h ⟨n.1, n.2.1⟩⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund ν₀ h𝓝₀
    (by rw [h𝓝₀1]; exact ENNReal.one_ne_top)
  have H1 := semiMeas_haar_inv (flagN J.d) J.d.emb0 (isClosed_flagN J.d) J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  refine ⟨by rw [wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer]; exact isClosed_stabX J.d, H0.1, H0.2, H1.2, fun F hF => ?_⟩
  have l1 : LocallyCompactSpace (radX J.d) := (isClosed_radX J.d).locallyCompactSpace
  have l2 : SecondCountableTopology (radX J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have l3 : LocallyCompactSpace (flagN J.d) := (isClosed_flagN J.d).locallyCompactSpace
  have l4 : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hlv : Continuous (lv J.d) := J.d.continuous_levi.comp continuous_subtype_val
  have hs := J.d.continuous_embed
  have e1 : ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ :=
    lintegral_semiMeas (flagN J.d) J.d.emb0 hs J.v0.μ J.vN.ν F hF
  have e2 : ∀ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν = ∫⁻ u, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂vU.ν := fun h =>
    lintegral_of_covolOne (radX J.d) (lv J.d) (isClosed_radX J.d) hlv (lv_conj J.d) (flagN J.d) (radX_sup_lv J.d)
      (exists_proj_lv J.d) (GQ J.W) (UXQ D ρ) (rat_lv J.d) vU.ν h𝓤 h𝓤1 ν₀ h𝓝₀ h𝓝₀1 J.vN.ν h𝓝 h𝓝1
      (fun g => F (g * J.d.emb0 h)) (hF.comp (continuous_mul_const _).measurable)
  have e3 : ∀ u : UX D ρ, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1)
      ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) = ∫⁻ h, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂J.v0.μ := fun u => by
    rw [lintegral_semiMeas (radX J.d) J.d.emb0 hs J.v0.μ ν₀ (fun g => F (g * J.d.levi u.1))
      (hF.comp (continuous_mul_const _).measurable)]
    simp only [mul_assoc, J.d.wittHyperbolic_anisotropic_commute_levi]
    rfl
  have hm : Measurable fun q : (GA D J.W₀ × UX D ρ) × radX J.d => F (q.2.1 * lv J.d q.1.2 * J.d.emb0 q.1.1) :=
    hF.comp (Continuous.measurable (((continuous_subtype_val.comp continuous_snd).mul
      (hlv.comp (continuous_snd.comp continuous_fst))).mul (hs.comp (continuous_fst.comp continuous_fst))))
  rw [e1]
  simp only [e2, e3]
  exact lintegral_lintegral_swap (hm.lintegral_prod_right' (ν := ν₀)).aemeasurable

end GlobalTheory.JacMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem gramQ_unitri : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  intro D W ρ x₀ hb u hd hl
  have htri : (rat u : Mx D ρ ρ).BlockTriangular id := fun i j (h : j < i) => by
    show incA D (u i j) = 0
    rw [hl i j h, map_zero]
  have hdiag : ∀ i, (rat u : Mx D ρ ρ) i i = 1 := fun i => by
    show incA D (u i i) = 1
    rw [hd i, map_one]
  have hu : IsUnit (rat u : Mx D ρ ρ) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => ⟨fun h => htri h, hdiag i⟩
  have h := hb.2 _ hmem
  rw [IsUnit.unit_spec] at h
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, Matrix.mul_assoc]
  exact h

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMemInverseHalfDifferent
section
open NumberField Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.DgenNe

theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have h1 : H.sigmaOf g = H.sigmaOf g' :=
    AlgEquiv.ext fun x => H.φ₀.injective (RingHom.congr_fun h x)
  exact (H.gal).symm.injective h1

theorem embT_injective {R : Ranks} (H : Host R) : Function.Injective (embT H) := fun τ τ' h =>
  Subtype.ext (emb_injective H h)

theorem bb_ne_bot {R : Ranks} (H : Host R) : H.𝔟 ≠ ⊥ := by
  intro h
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem int_mem_inverse_half_different {R : Ranks} (H : Host R) (t : 𝓞 H.E) :
    ((t : H.E)) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  have h0 : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (bb_ne_bot H)
  have h1 : (1 : H.E) ∈ H.AA0 := by
    unfold Host.AA0
    rw [FractionalIdeal.mem_inv_iff h0]
    intro y hy
    obtain ⟨x, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [one_mul]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
  have h2 : t • (1 : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := Submodule.smul_mem _ t h1
  simpa [Algebra.smul_def] using h2

end GlobalTheory.Mem.Col2.DgenNe

namespace GlobalTheory.Mem.Col2.DgenNe

theorem dgen_ne_zero : ∀ {R : Ranks} (H : Host R) (cD : Tau R → ℂ), Th.IsDgen H (embT H) cD → ∀ τ, cD τ ≠ 0 := by
  intro R H cD hD τ hτ
  classical
  obtain ⟨M, hM, hemb, hgen⟩ := hD
  obtain ⟨s, hs, hell⟩ := hgen τ
  have hs0 : s = 0 := Subtype.ext (hs.trans hτ)
  rw [hs0, Submodule.span_zero_singleton] at hell
  let e : Tau R → H.E →+* M := fun σ => (embT H σ).codRestrict M (hemb σ)
  have hlift : ∀ σ (x : H.E), Formalism.MainNotions.TaylorLogMetric.liftM M (embT H σ x) = e σ x := by
    intro σ x
    simp only [Formalism.MainNotions.TaylorLogMetric.liftM, dif_pos (hemb σ x)]
    rfl
  let f : Tau R → (𝓞 H.E →* M) := fun σ => ((e σ).comp (algebraMap (𝓞 H.E) H.E)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective H
    have h2 : e σ = e σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E))
      (RingHom.ext fun x => DFunLike.congr_fun h x)
    ext x
    exact congrArg Subtype.val (RingHom.congr_fun h2 x)
  have hli := (linearIndependent_monoidHom (𝓞 H.E) M).comp f hf
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  let N := Th.mmM H (embT H) M
  let P : Submodule M (Tau R → M) :=
    { carrier := {v | ∃ b : 𝓞 M, b ≠ 0 ∧ b • v ∈ N}
      add_mem' := by
        rintro v w ⟨b, hb, hv⟩ ⟨b', hb', hw⟩
        refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
        have : (b * b') • (v + w) = b' • (b • v) + b • (b' • w) := by
          rw [smul_add, mul_smul, mul_smul, smul_comm b b' v]
        rw [this]
        exact N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro m v ⟨b, hb, hv⟩
        obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
        have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
        have hy1 : algebraMap (𝓞 M) M y ≠ 0 := by
          intro h0
          exact hy0 (IsFractionRing.injective (𝓞 M) M (by rw [h0, map_zero]))
        refine ⟨y * b, mul_ne_zero hy0 hb, ?_⟩
        have : (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) • v) = x • (b • v) := by
          funext σ
          change (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) * v σ) = x • (b • v σ)
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          field_simp
        rw [this]
        exact N.smul_mem _ hv }
  have hP : ∀ t : 𝓞 H.E, (fun σ => e σ t) ∈ P := fun t =>
    ⟨1, one_ne_zero, by
      rw [one_smul]
      exact Submodule.subset_span ⟨(t : H.E), int_mem_inverse_half_different H t, funext fun σ => (hlift σ t).symm⟩⟩
  have hsingle : (Pi.single τ 1 : Tau R → M) ∈ P := by
    have hle : Submodule.span M (Set.range (flip ((fun g : 𝓞 H.E →* M => (g : 𝓞 H.E → M)) ∘ f))) ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact hP t
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨b, hb, hbN⟩ := hsingle
  have hmem : algebraMap (𝓞 M) M b ∈ Th.ellT H (embT H) M τ := by
    rw [Th.ellT, Submodule.mem_comap]
    convert hbN using 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp [Algebra.smul_def]
    · simp [h]
  rw [hell, Submodule.mem_bot] at hmem
  exact hb (IsFractionRing.injective (𝓞 M) M (by rw [hmem, map_zero]))

end GlobalTheory.Mem.Col2.DgenNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.QuotFubini

theorem existsUnique_mul_mem {G : Type} [Group G] {Γ R : Subgroup G} (hΓ : Γ ≤ R) {S : Set G}
    (hS : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ S) (h : G) (r : R) :
    ∃! γ : Γ.subgroupOf R, γ • r ∈ {r : R | (r : G) * h ∈ S} := by
  obtain ⟨γ, h1, h2⟩ := hS ((r : G) * h)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, γ.2⟩, ?_, fun δ hδ => ?_⟩
  · change ((γ : G) * r) * h ∈ S
    rw [mul_assoc]; exact h1
  · have h3 : (⟨((δ : R) : G), δ.2⟩ : Γ) = γ := by
      refine h2 _ ?_
      have : (((δ : R) : G) * r) * h ∈ S := hδ
      rw [mul_assoc] at this
      exact this
    ext
    exact congrArg (fun x : Γ => (x : G)) h3

end GlobalTheory.QuotFubini

namespace GlobalTheory


open GlobalTheory.QuotFubini in
theorem quot_fubini_mean : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  intro G _ _ _ _ _ _ _ _ μ _ R Γ hΓR hR hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hf hfΓ hf𝓑 hf𝓡
  obtain ⟨-, S, hSm, hS⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hfΓ' : ∀ (γ : Γ) (x : G), f (γ • x) = f x := fun γ x => hfΓ γ γ.2 x
  have hmh : ∀ h : G, Measurable (fun r : R => (r : G) * h) := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h => hmh h hSm
  have hShfd : ∀ h : G, IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR := fun h =>
    IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (existsUnique_mul_mem hΓR hS h)
  have hfR : ∀ h : G, ∀ (γ : Γ.subgroupOf R) (r : R), f (((γ • r : R) : G) * h) = f ((r : G) * h) := by
    intro h γ r
    change f ((((γ : R) : G) * r) * h) = _
    rw [mul_assoc]; exact hfΓ _ γ.2 _
  have hind : ∀ h : G, (fun r : R => S.indicator f ((r : G) * h)) =
      {r : R | (r : G) * h ∈ S}.indicator (fun r : R => f ((r : G) * h)) := by
    intro h; ext r
    by_cases hr : (r : G) * h ∈ S
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ {r : R | (r : G) * h ∈ S} from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ {r : R | (r : G) * h ∈ S} from hr)]
  refine ⟨S.indicator f, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hSm).2 ((hSfd.integrableOn_iff h𝓑 hfΓ').2 hf𝓑)
  · rw [hind h]
    exact (integrable_indicator_iff (hSh h)).2 (((hShfd h).integrableOn_iff h𝓡 (hfR h)).2 (hf𝓡 h))
  · rw [hind h, integral_indicator (hSh h)]
    exact (h𝓡.setIntegral_eq (hShfd h) (hfR h))
  · rw [integral_indicator hSm]
    exact h𝓑.setIntegral_eq hSfd hfΓ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhereStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattices_agree_almost_everywhere : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  first
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM.toIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerIntegralToIntegralCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem lowerIntegral_to_integral_coords : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  intro X U Y _ _ _ G _ ν νU μ _ _ i p Inv hi hp Dom H f hf hinv hfi
  have hpm : Measurable (fun q : U × Y => p q.1 q.2) := hp

  have hprod : ∀ g : G → ENNReal, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      ∫⁻ x, g (i x) ∂ν = ∫⁻ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi
    rw [H g hg hgi, lintegral_prod (fun q : U × Y => g (p q.1 q.2)) (hg.comp hpm).aemeasurable]
  have hint : Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) := by
    refine ⟨(hf.comp hpm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have := hprod (fun n => ‖f n‖ₑ) hf.enorm (fun t ht n hn => by simp only [hinv t ht n hn])
    rw [← this]
    exact hfi.2
  refine ⟨hint, ?_⟩
  rw [← integral_prod _ hint]

  have hreal : ∀ g : G → ℝ, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      Integrable (fun x => g (i x)) ν → Integrable (fun q : U × Y => g (p q.1 q.2)) (νU.prod μ) →
      ∫ x, g (i x) ∂ν = ∫ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi h1 h2
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
    have e1 := hprod (fun n => ENNReal.ofReal (g n)) (ENNReal.measurable_ofReal.comp hg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    have e2 := hprod (fun n => ENNReal.ofReal (- g n)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    rw [e1, e2]
  apply Complex.ext
  · have a := integral_re hfi; have b := integral_re hint
    simp only [RCLike.re_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).re) (Complex.measurable_re.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.re hint.re
  · have a := integral_im hfi; have b := integral_im hint
    simp only [RCLike.im_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).im) (Complex.measurable_im.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.im hint.im

end GlobalTheory
end

