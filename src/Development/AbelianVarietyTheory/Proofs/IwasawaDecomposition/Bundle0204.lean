module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerApprox
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem Std.exists_inner_approx {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) :
    ∃ (m : ℕ) (S : Fin m → List (Mx n)), (∀ i, ∀ X ∈ S i, X ∈ lieSet ε) ∧ ∀ δ : ℝ, 0 < δ → ∃ u : H,
      ∀ z, Sm ε σ z → ‖ℓ z - ⟪u, z⟫_ℂ‖ ≤ δ * ∑ i, ‖Dw σ (S i) z‖ := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  refine ⟨m, S, hS, fun δ hδ => ?_⟩
  have hx : ∀ i, ∃ x ∈ smooth (Jm ε) σ, dist ((InnerProductSpace.toDual ℂ H).symm (Λ i)) x < δ := fun i =>
    Metric.mem_closure_iff.1 (h.dense_smooth _) δ hδ
  choose x hxs hxd using hx
  choose u hu using fun i => exists_adjoint (isUnit_Jm ε) h.1 (S i) (hS i) (x i) (hxs i)
  refine ⟨∑ i, u i, fun z hz => ?_⟩
  rw [hΛ z hz, sum_inner, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← hu i z hz, ← InnerProductSpace.toDual_symm_apply, ← inner_sub_left]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [← dist_eq_norm]
  exact (hxd i).le

theorem avgBd_sobCont : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (T : H → H) (Z : Set (Mx n)) (C : ℝ), IsCompact Z →
    Z ⊆ UJset ε → 0 ≤ C → AvgBd σ T Z C → ∀ (ι : Type) [Fintype ι] (ℓ : ι → (H →ₗ[ℂ] ℂ)) (w : ι → H),
    (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (w j)) → (∀ j, Sm ε σ (T (w j))) → ∀ M : ℝ, 0 ≤ M →
    (∀ y ∈ Z, ‖∑ j, ℓ j (σ y (w j))‖ ≤ M) → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M := by
  intro n ε H _ _ _ σ h T Z C hZ hZU hC hA ι _ ℓ w hℓ hw hTw M hM hb
  choose m S hS hap using fun j => h.exists_inner_approx (hℓ j)
  have hc : ContinuousOn (fun y => ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖) Z :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
      ((h.continuousOn_Dw (hS j i) (hw j)).mono hZU).norm
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn hc
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖ ≤ K := fun y hy =>
    ((le_abs_self _).trans (hK₀ y hy)).trans (le_max_left _ _)
  set K' := ∑ j, ∑ i, ‖Dw σ (S j i) (T (w j))‖ with hK'
  have key : ∀ δ : ℝ, 0 < δ → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M + δ * (C * K + K') := by
    intro δ hδ
    choose u hu using fun j => hap j δ hδ
    have hd : ∀ z : ι → H, (∀ j, Sm ε σ (z j)) →
        ‖∑ j, ℓ j (z j) - ∑ j, ⟪u j, z j⟫_ℂ‖ ≤ δ * ∑ j, ∑ i, ‖Dw σ (S j i) (z j)‖ := fun z hz => by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hu j _ (hz j))
    have h1 := hA ι u w (M + δ * K) (by positivity) fun y hy => by
      have e1 := hd (fun j => σ y (w j)) fun j => (hw j).translate h.1 (hZU hy)
      have e2 := norm_le_norm_add_norm_sub (∑ j, ℓ j (σ y (w j))) (∑ j, ⟪u j, σ y (w j)⟫_ℂ)
      have e3 := mul_le_mul_of_nonneg_left (hK y hy) hδ.le
      have e4 := hb y hy
      linarith
    have h2 := hd (fun j => T (w j)) hTw
    have h3 := norm_le_norm_add_norm_sub' (∑ j, ℓ j (T (w j))) (∑ j, ⟪u j, T (w j)⟫_ℂ)
    nlinarith
  have ht : Tendsto (fun δ : ℝ => C * M + δ * (C * K + K')) (𝓝[>] 0) (𝓝 (C * M + 0 * (C * K + K'))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)

end GlobalTheory.TypeSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelMeasure

theorem isMinf_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : Lev.IsMinf m) (h' : Lev.IsMinf m') : m' = m := by
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  haveI := h.1
  haveI := h'.1
  have e : m' = ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) • m := Measure.isMulLeftInvariant_eq_smul m' m
  have h1 := GlobalTheory.OmegaDensityScale.omegaDensity_smul h.2 (Measure.haarScalarFactor m' m)
  rw [← e] at h1
  have h2 := GlobalTheory.OmegaDensityScale.omegaDensity_unique h'.2 h1
  have h0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hc : ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (h2.trans (one_mul _).symm)
  rw [e, hc, one_smul]

theorem exists_isMeasLevW (D : D7) (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hKo : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hKc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (m : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hm : ∀ ρ, (m ρ).IsHaarMeasure) (hg : ∀ ρ, good ρ (m ρ)) (hu : ∀ ρ m', good ρ m' → m' = m ρ) :
    ∃ μ, Lev.IsMeasLevW V K good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hV (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  let j : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Continuous j := e0.symm.continuous.comp (Continuous.prodMk_right 1)
  have hj0 : ∀ k, e0 (j k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, Lev.finE V (j (e0 h).2) = Lev.finE V h := by
    intro h
    have h1 : finHom V (j (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (j (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [Lev.finE_eq, Lev.finE_eq, h1]
  have hinf : ∀ k, j k ∈ GfC V := by
    intro k
    have a1 := (he0 (j k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  let K' := (K.comap (Lev.finE V)).comap j
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K' ↔ Lev.finE V h ∈ K := fun h => by
    rw [← hfin h]; rfl
  have hK'o : IsOpen (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := hKo.preimage hj
  have hK'c : IsCompact (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have h1 := hKc.image (continuous_snd.comp e0.continuous)
    convert h1 using 1
    ext k
    constructor
    · intro hk
      exact ⟨j k, ⟨hinf k, hk⟩, congrArg Prod.snd (hj0 k)⟩
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  let e : GA D V ≃ₜ* (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) ×
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := GlobalTheory.Mem.VolExists.exists_haar_prod m e K' hK'o hK'c
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨m, hg⟩, fun m' hm' B hB => ?_⟩⟩
  obtain rfl : m' = m := funext fun i => hu i _ (hm' i)
  have hv : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact GlobalTheory.Mem.VolExists.exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hv using hv
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m' i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m' i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hm i)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hv i, ← Matrix.mul_assoc, ← GlobalTheory.Mem.VolExists.mat_mul, inv_mul_cancel, GlobalTheory.Mem.VolExists.mat_one,
        Matrix.one_mul]
    rw [GlobalTheory.Mem.VolExists.mat_mul, GlobalTheory.Mem.VolExists.mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, hv i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.LevelMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelAction

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

variable {D : D7}

theorem finCong_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) : GlobalTheory.Member.FinCong V 1 k := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k) := hy
  intro z hz
  refine ⟨(finHom V k).1 *ᵥ z - z, sub_mem ?_ hz, (one_nsmul _).symm⟩
  rw [hl] at hz ⊢
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ
      (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i

theorem exists_endo {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {k : GA D V}
    (hk : GlobalTheory.Member.FinCong V 1 k) : ∃ f : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w := by
  have hh := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hk
  have hL := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hh
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V k
  rw [hL] at h3
  obtain ⟨f, hf, -⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V k)
    (latG V 1) h1 h2 h3
  let e : La ≃ₗ[𝓞 D.host.E] latG V 1 := (LinearEquiv.ofInjective ι hι.1).trans (LinearEquiv.ofEq _ _ hι.2)
  have he : ∀ a, (e a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  refine ⟨e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, ew⟩ := hf M hM (e a)
  refine ⟨(finHom V k).1 *ᵥ w, ?_, ?_⟩
  · rw [← hh]
    exact (GlobalTheory.Member.LatMove.mem_hat_iff V k _).2 ⟨w, h5 ▸ hw, rfl⟩
  · have e1 : ι ((e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap) a) = (f M (e a) : Fin V.rank → D.host.E) := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    rw [e1]
    have e2 : finVec V (f M (e a) : Fin V.rank → D.host.E) = (finHom V k).1 *ᵥ (finVec V (ι a) + M • w) := ew
    rw [e2, Matrix.mulVec_add, add_sub_cancel_left]
    exact map_nsmul (finHom V k).1.mulVecLin M w

theorem not_isConjPl {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    {PP PP' : Pl D.host.E} (h : l.Mb ≤ PP.asIdeal) (h' : l.Mb ≤ PP'.asIdeal) : ¬ Lev.IsConjPl PP PP' := by
  intro hc
  apply PP'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h' (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_)
  obtain ⟨c', h1, h2⟩ := hc c (h hc')
  have e : H.bar c = c' := RingOfIntegers.ext ((H.bar_eq c).trans h2.symm)
  change H.bar c ∈ PP'.asIdeal
  rwa [e]

theorem latEmb_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) := by
    rintro V hr rfl h
    exact h
  exact key _ hr hV h

theorem exists_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ hpb i
  have hT := tie.laws
  have hβ := hR.lev.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => exists_endo (iotaW T i) (latEmb_iotaW T hT i) hM
    (finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩

end GlobalTheory.LevelAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLog
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.LocalLog

theorem exists_local_log (n : ℕ) : ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    (∀ᶠ g in 𝓝 (1 : Mx n), NormedSpace.exp (L g) = g) ∧
    ∀ᶠ X in 𝓝 (0 : Mx n), L (NormedSpace.exp X) = X := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n)
      ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have h0 : NormedSpace.exp (0 : Mx n) = 1 := NormedSpace.exp_zero
  refine ⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩
  · have := h.localInverse_continuousAt
    rwa [h0] at this
  · have := h.localInverse_apply_image
    rwa [h0] at this
  · have := h.eventually_right_inverse
    rwa [h0] at this

theorem local_log_UJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    ∀ᶠ g in 𝓝 (1 : Mx n), g ∈ UJset ε → L g ∈ lieSet ε ∧ NormedSpace.exp (L g) = g := by
  intro n ε
  obtain ⟨L, hc, h1, hr, hl⟩ := exists_local_log n
  refine ⟨L, hc, h1, ?_⟩
  have hJ := Jm_mul_self ε
  have ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0) := by
    have hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε := by fun_prop
    have := (hcont.tendsto 0).comp (h1 ▸ hc.tendsto)
    simpa [Function.comp_def] using this
  filter_upwards [hr, ht.eventually hl] with g hg hg' hU
  refine ⟨?_, hg⟩
  have hU' : gᴴ * Jm ε * g = Jm ε := hU
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g := by
    have h2 := Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)
    rw [hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg] at h2
    rw [h2]
    have h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]
    rw [h3]
    calc Jm ε * (Jm ε * g * Jm ε) * Jm ε = (Jm ε * Jm ε) * g * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hJ]; simp
  rw [he] at hg'
  show (L g)ᴴ * Jm ε + Jm ε * L g = 0
  nth_rewrite 2 [hg']
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  simp

end GlobalTheory.LocalLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  first | exact @GlobalTheory.FockHol.main | exact GlobalTheory.FockHol.main | (intros; apply GlobalTheory.FockHol.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeTransport
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Transport

variable {n : ℕ}

theorem conj_lie {A B G G' Y : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hY : Y ∈ lieOf G) :
    B * Y * A ∈ lieOf G' := by
  have hY' : Yᴴ * G + G * Y = 0 := hY
  show (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY']; simp

theorem conj_UH {A B G G' g : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    B * g * A ∈ Formalism.QuantumDeterminants.UH G' := by
  have hg' : gᴴ * G * g = G := hg
  show (B * g * A)ᴴ * G' * (B * g * A) = G'
  rw [← hG]
  calc (B * g * A)ᴴ * (Aᴴ * G * A) * (B * g * A)
      = Aᴴ * (gᴴ * (A * B)ᴴ * G * (A * B) * g) * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, hg']

theorem prod_conj {Q : Mx n} (h1 : Q⁻¹ * Q = 1) (h2 : Q * Q⁻¹ = 1) (l : List (Mx n)) :
    (l.map fun x => Q * x * Q⁻¹).prod = Q * l.prod * Q⁻¹ := by
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc Q * a * Q⁻¹ * (Q * l.prod * Q⁻¹) = Q * a * (Q⁻¹ * Q) * l.prod * Q⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exp_smul_conj {Q : Mx n} (hQ : IsUnit Q) (X : Mx n) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Q⁻¹)) = Q * NormedSpace.exp (t • X) * Q⁻¹ := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.TypeSum.Transport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  first | exact @GlobalTheory.JointHarm.weights_of_minors | exact GlobalTheory.JointHarm.weights_of_minors | (intros; apply GlobalTheory.JointHarm.weights_of_minors <;> assumption)
end

