module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
open Ad3.R Ad3

theorem countable_range : Countable (AdelicGLn.diagonal ℚ 2).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) := Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u.val, u.inv)) (fun a b h => Units.ext (congrArg Prod.fst h))
  exact (Set.countable_range (AdelicGLn.diagonal ℚ 2)).to_subtype

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2
theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]
theorem md_one : md 1 = 1 := by simp [md]
theorem continuous_md : Continuous md := continuous_subtype_val.comp IdeleGroup.continuous_ideleModule
theorem continuous_Dt : Continuous Dt := continuous_md.comp (AdelicGLn.continuous_det ℚ 2)
theorem Dt_pos (g : G2) : 0 < Dt g := md_pos _
theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, map_mul, md_mul]
theorem Dt_inv (g : G2) : Dt g⁻¹ = (Dt g)⁻¹ := by
  have := Dt_mul g g⁻¹
  have h1 : Dt (1 : G2) = 1 := by simp [Dt, md_one]
  rw [mul_inv_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm
theorem Dt_dia (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have := Reduction.rationalGL_le_normOneGL (K := ℚ) (n := 2) ⟨γ, rfl⟩
  rw [Reduction.mem_normOneGL] at this
  exact this
theorem Dt_central (z : Jd) : Dt (dg2 z z) = md z ^ 2 := by
  have : GeneralLinearGroup.det (dg2 z z) = z * z := by
    ext
    simp [dg2, Matrix.det_fin_two]
  rw [Dt, this, md_mul, sq]

theorem exists_ne_one {η : HeckeCharacter ℚ} (h : η ≠ 1) : ∃ z : Jd, η.toIdele z ≠ 1 := by
  by_contra hc
  push_neg at hc
  apply h
  ext x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have := hc z
  rw [HeckeCharacter.toIdele_apply] at this
  show ((η (IdeleClassGroup.mk ℚ z) : Circle) : ℂ) = ((1 : Circle) : ℂ)
  rw [this]

open scoped Pointwise

theorem measurableSet_band : MeasurableSet band := by
  have : band = Dt ⁻¹' Set.Ico 1 2 := by
    ext g; simp [band]
  rw [this]
  exact continuous_Dt.measurable measurableSet_Ico

theorem mem_band_dia {γ : GL (Fin 2) ℚ} {g : G2} : dia2 γ * g ∈ band ↔ g ∈ band := by
  simp [band, Dt_mul, Dt_dia]

theorem fundamental_domain_integral_central_vanishing : Ad3.R.G1a → Ad3.R.G1 := by
  intro hA μ 𝓕 mK 𝓓 hS F hF hB hL
  haveI := hS.haar
  haveI := hS.right
  obtain ⟨-, hz, hT⟩ := hA μ 𝓕 mK 𝓓 hS
  have hbM := measurableSet_band
  have Fm : Measurable F := hF.measurable
  have hIndL : LInv (band.indicator F) := by
    intro γ g
    by_cases hg : g ∈ band
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (mem_band_dia.2 hg), hL]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (mem_band_dia.1 h))]
  have hIndM : Measurable (band.indicator F) := Fm.indicator hbM
  have hI : ∀ f : G2 → ℂ, ∫ g in 𝓕 ∩ band, f g ∂μ = ∫ g in 𝓕, band.indicator f g ∂μ :=
    fun f => (setIntegral_indicator hbM).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hC h
    obtain ⟨z, hz1, -⟩ := hz (Dt h)⁻¹ (inv_pos.2 (Dt_pos h))
    set Bh : Set G2 := {g | g * h⁻¹ ∈ band} with hBh
    have hBhM : MeasurableSet Bh :=
      hbM.preimage (continuous_id.mul continuous_const).measurable
    have hBhL : LInv (Bh.indicator F) := by
      intro γ g
      have hm : dia2 γ * g ∈ Bh ↔ g ∈ Bh := by
        simp only [hBh, Set.mem_setOf_eq, mul_assoc, mem_band_dia]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hL]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e1 : ∀ g, Bh.indicator F (g * h) = band.indicator (fun g => F (g * h)) g := by
      intro g
      have hm : g * h ∈ Bh ↔ g ∈ band := by simp [hBh]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg)]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e2 : ∀ g, band.indicator F (dg2 z z * g) = Bh.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ Bh := by
        have : Dt (dg2 z z * g) = Dt (g * h⁻¹) := by
          rw [Dt_mul, Dt_mul, Dt_central, hz1, Dt_inv, mul_comm]
        simp only [hBh, Set.mem_setOf_eq, band, this]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hC]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    rw [hI, hI]
    simp_rw [← e1]
    rw [(hT (fun g => g * h) (Or.inr (Or.inl ⟨h, rfl⟩))).2 _ (Fm.indicator hBhM) hBhL]
    simp_rw [← e2]
    exact (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
  · intro η hη hc hne
    obtain ⟨z0, h0⟩ := exists_ne_one hne
    obtain ⟨z1, hz1, hz1'⟩ := hz ((md z0) ^ 2)⁻¹ (inv_pos.2 (pow_pos (md_pos _) 2))
    set z : Jd := z0 * z1 with hzdef
    have hmd : md z ^ 2 = 1 := by
      rw [hzdef, md_mul, mul_pow, hz1]
      exact mul_inv_cancel₀ (pow_pos (md_pos _) 2).ne'
    have hηz : η.toIdele z ≠ 1 := by
      rw [hzdef, map_mul, hz1' η hη, mul_one]
      exact h0
    have hηz' : (η.toIdele z : ℂ) ≠ 1 := fun h => hηz (Circle.ext (by simpa using h))
    have e : ∀ g, band.indicator F (dg2 z z * g) = (η.toIdele z : ℂ) * band.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ band := by
        have : Dt (dg2 z z * g) = Dt g := by rw [Dt_mul, Dt_central, hmd, one_mul]
        simp only [band, Set.mem_setOf_eq, this]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hc]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]
    have key := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
    simp_rw [e] at key
    rw [integral_const_mul] at key
    rw [hI]
    have : ((η.toIdele z : ℂ) - 1) * ∫ g in 𝓕, band.indicator F g ∂μ = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hηz')
  · intro hC hne hI0
    apply hne
    have hn : ∀ g, F g * conj (F g) = ((Complex.normSq (F g) : ℝ) : ℂ) := fun g => Complex.mul_conj _
    simp_rw [hn] at hI0
    rw [integral_complex_ofReal] at hI0
    have hI1 : ∫ g in 𝓕 ∩ band, Complex.normSq (F g) ∂μ = 0 := by exact_mod_cast hI0
    obtain ⟨C, hCb⟩ := hB
    have hmeas : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hbM
    have hint : IntegrableOn (fun g => Complex.normSq (F g)) (𝓕 ∩ band) μ := by
      refine Measure.integrableOn_of_bounded (M := C ^ 2) hS.vol.ne
        (Complex.continuous_normSq.comp hF).aestronglyMeasurable ?_
      refine Eventually.of_forall fun g => ?_
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCb g) 2
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun g => Complex.normSq_nonneg (F g)) hint).1 hI1
    set t : Set G2 := band ∩ {g | F g ≠ 0} with ht
    have h0 : μ (t ∩ 𝓕) = 0 := by
      have h1 := (ae_iff.1 ((ae_restrict_iff' hmeas).1 hae))
      refine measure_mono_null ?_ h1
      rintro g ⟨⟨hb, hf⟩, hg⟩
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨⟨hg, hb⟩, by simpa using hf⟩
    have hinv : ∀ γ ∈ (AdelicGLn.diagonal ℚ 2).range, ∀ x : G2, γ * x ∈ t ↔ x ∈ t := by
      rintro _ ⟨δ, rfl⟩ x
      have e1 := hL δ x
      simp only [ht, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [show AdelicGLn.diagonal ℚ 2 δ * x = dia2 δ * x from rfl, mem_band_dia, e1]
    have hts : ∀ γ : (AdelicGLn.diagonal ℚ 2).range, γ • t = t := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
      exact hinv _ (γ⁻¹).2 x
    haveI := countable_range
    set_option synthInstance.maxHeartbeats 200000 in
    have hμt : μ t = 0 := hS.fd.measure_zero_of_invariant t hts h0
    set U : Set G2 := {g | 1 < Dt g ∧ Dt g < 2 ∧ F g ≠ 0} with hU
    have hUo : IsOpen U := by
      refine (isOpen_lt continuous_const continuous_Dt).inter
        ((isOpen_lt continuous_Dt continuous_const).inter (isOpen_ne_fun hF continuous_const))
    have hU0 : U = ∅ := hUo.eq_empty_of_measure_zero
      (measure_mono_null (show U ⊆ t from fun g hg => ⟨⟨hg.1.le, hg.2.1⟩, hg.2.2⟩) hμt)
    funext g
    by_contra hg
    obtain ⟨z, hz1, -⟩ := hz (3 / 2 / Dt g) (div_pos (by norm_num) (Dt_pos g))
    have hD : Dt (dg2 z z * g) = 3 / 2 := by
      rw [Dt_mul, Dt_central, hz1, div_mul_cancel₀ _ (Dt_pos g).ne']
    have hmem : dg2 z z * g ∈ U := by
      refine ⟨by rw [hD]; norm_num, by rw [hD]; norm_num, ?_⟩
      rw [hC]
      exact hg
    rw [hU0] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacter
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem hgp_twist_tE {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n)
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h)
    (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈
      parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  have hL : leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩ =
      leviTwo k (Fin (i + 1)) (Fin (j + 1)) ((gpProjg k h g).1, ((gpProjg k h g).2 : GL (Fin (j + 1)) k)) := by
    have e : (⟨_, hq⟩ : parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) = hgpInclg k h g :=
      Subtype.ext (by simp [hgpInclg])
    rw [e]
    funext x
    cases x <;> rfl
  have key : ∀ x : ∀ b, TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    set g₁ : GL (Fin (i + 1)) k := (gpProjg k h g).1 with hg₁
    set g₂ : Mir k j := (gpProjg k h g).2 with hg₂
    have hl : ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
        ((twist π₁ (dpow (i + 1) (((j + 1 : ℕ) : ℝ) / 2)) g₁ (x false) : V) ⊗ₜ[ℂ]
          (twist (π₂.comp (Mir k j).subtype) (dpowM j (-((i + 1 : ℕ) : ℝ) / 2)) g₂ (x true) : W) : V ⊗[ℂ] W) :=
      (congrArg _ (Exponents.boolTensorEquiv_tprod x)).trans (extTensor_tmul _ _ _ _ _)
    have hr : tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviTwo k (Fin (i + 1)) (Fin (j + 1)) (g₁, (g₂ : GL (Fin (j + 1)) k))) : ℂˣ) : ℂ) •
          ((π₁ g₁ (x false) : V) ⊗ₜ[ℂ] (π₂ (g₂ : GL (Fin (j + 1)) k) (x true) : W) : V ⊗[ℂ] W) := by
      show tE V W (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))))
        (leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [hL, twist_apply, piTensor_tprod, map_smul]
      exact congrArg _ (Exponents.boolTensorEquiv_tprod _)
    rw [hl, hr, deltaHalf_two]
    simp only [twist_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, MonoidHom.comp_apply,
      Units.val_mul, dpow, dpowM, detChar_apply]
    have c₁ : ((((j + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = (Fintype.card (Fin (j + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    have c₂ : ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = -(Fintype.card (Fin (i + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    rw [c₁, c₂, mul_comm]
    rfl
  have := LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext key) :
    ((((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g) ∘ₗ (tE V W).toLinearMap) =
      (tE V W).toLinearMap ∘ₗ (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩)) v
  exact this

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterion
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

theorem eLast_vecMul {k : Type} [Field k] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [eLast, vecMul, dotProduct, Pi.single_apply]

theorem mem_two_iff {k : Type} [Field k] {r t N : ℕ} (h : r + t = N) (g : GL (Fin N) k) :
    g ∈ parab k (two (stdSum h)) ↔
      ∀ a b : Fin N, r ≤ (a : ℕ) → (b : ℕ) < r → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hg a b ha hb
    have hlt : (a : ℕ) - r < t := by have := a.isLt; omega
    have ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a := Fin.ext (by rw [stdSum_inr]; simp only []; omega)
    have eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b := Fin.ext (by rw [stdSum_inl])
    have := mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)
    rw [two_true, two_false, ea, eb] at this
    exact this
  · intro hg
    refine mem_parab_iff.2 ?_
    intro x y u v hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
    refine hg _ _ ?_ ?_
    · show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)
      rw [stdSum_inr]; omega
    · show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r
      rw [stdSum_inl]; exact v.isLt

theorem mem_dcos_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔
      ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  intro k _ _ _ _ i t h ht g
  have hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ) := by
    rw [Fin.val_last]; omega
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩ a
    have hpi : p⁻¹ ∈ Mir k (i + t) := inv_mem hp
    have hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        eLast k (i + t) := hpi
    have e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹ := by simp
    have h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
      rw [Units.val_mul, ← vecMul_vecMul, hpi']
    have hrow := (eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))
    rw [e]
    refine (congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)
    rw [stdSum_inl]; exact a.isLt
  · intro hy
    classical
    let y : Fin (i + t + 1) → k :=
      ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))
    have hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
      have : y = vecMul (eLast k (i + t))
          ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := (eLast_vecMul _ _).symm
      rw [this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
    have hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0 := by
      intro c hc
      have e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c := Fin.ext (by rw [stdSum_inl])
      have := hy ⟨(c : ℕ), hc⟩
      rw [e] at this
      exact this
    obtain ⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : y = 0 := funext hcon
      rw [h0, zero_vecMul] at hyg
      have := congrFun hyg (Fin.last (i + t))
      simp [eLast] at this
    have hblock : i + 1 ≤ (a₀ : ℕ) := by
      by_contra hlt
      exact ha₀ (hfirst a₀ (by omega))
    let σ : Equiv.Perm (Fin (i + t + 1)) := Equiv.swap a₀ (Fin.last (i + t))
    have hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ) := by
      intro r hr
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · exact hlast
      · exact hblock
      · exact hr
    let B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
      ((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id
    have hdet : B.det ≠ 0 := by
      simp only [B]
      rw [Matrix.det_permute, det_updateRow_one]
      refine mul_ne_zero ?_ ha₀
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    let b : GL (Fin (i + t + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B := rfl
    have hbQ : b ∈ parab k (two (stdSum h)) := by
      refine (mem_two_iff h b).2 fun r c hr hc => ?_
      rw [hb]
      simp only [B, submatrix_apply, id]
      by_cases e : σ r = a₀
      · rw [e, updateRow_self]
        exact hfirst c hc
      · rw [updateRow_ne e, one_apply_ne]
        intro e2
        have := hσ r hr
        rw [e2] at this
        omega
    refine ⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩
    show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)
    have hB : B (Fin.last (i + t)) = y := by
      funext c
      simp [B, σ]
    rw [Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]
    exact hyg

end GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanishStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_vanish : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ), r ≠ a → Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapVan.van | exact GlobalTheory.CompanionTheory.CapVan.van | (intros; apply GlobalTheory.CompanionTheory.CapVan.van <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompactStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f) := by
  first | exact @GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | exact GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | (intros; apply GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    Function.Surjective (leadE K j a (n := a + j)) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | exact GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_restrict_open_bijective : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ),
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  first | exact @GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | exact GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | (intros; apply GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective <;> assumption)
end

