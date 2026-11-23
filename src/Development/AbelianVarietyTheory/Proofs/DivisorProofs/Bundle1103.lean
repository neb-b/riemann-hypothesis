module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intF_half {x : AF F} {M : ℕ} (h : 2 • x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨c, hc, ?_⟩
  change 2 • x.2 = (2 * M) • c at e
  have h2 : IsUnit (2 : Af F) := by
    have : algebraMap F (Af F) 2 = 2 := map_ofNat _ 2
    rw [← this]
    exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, mul_assoc, Nat.cast_ofNat] at e
  rw [nsmul_eq_mul]
  exact h2.mul_left_cancel e

theorem intF_le {x : AF F} {M : ℕ} (h : x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨2 • c, fun v => ?_, ?_⟩
  · have : (2 • c) v = c v + c v := by rw [two_nsmul]; rfl
    rw [this]
    exact add_mem (hc v) (hc v)
  · rw [e, smul_smul, mul_comm]

theorem CE_cA (σ : E →ₐ[F] E) {N : ℕ} {z : AF F ⊗[F] E} (h : z ∈ CE F E N) : cA σ z ∈ CE F E N := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  exact mem_CE.2 ⟨cA σ s, cA_mem_SE σ hs, by rw [← e, map_nsmul]⟩

theorem incAF_algebraMap (y : F) :
    incAF F E (algebraMap F E y) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E y) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E)]

theorem exists_emb_ext (φ : F →+* ℂ) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = φ := by
  letI : Algebra F ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  exact ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, (IsAlgClosed.lift : E →ₐ[F] ℂ).comp_algebraMap⟩

theorem key (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (hM : 0 < M)
    (lam : (AF F)ˣ →* Circle) (h1 : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1)
    (hMk : ∀ b : (AF F)ˣ, (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1)
    (a : (AF F)ˣ) (ha : idFF F E a ∈ (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)) :
    lam a = 1 := by
  obtain ⟨hσσ, hfix⟩ := _root_.GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hcm
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have htr : ∀ (N : ℕ) (x : AF F), algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E (2 * (2 * N)) → x ∈ intF F N := by
    intro N x hx
    have := _root_.GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF F E _ x hx
    rw [h2] at this
    exact intF_le (intF_half this)
  have hcongF : ∀ b : (AF F)ˣ, idFF F E b ∈ WE F E (8 * M) → lam b = 1 := by
    intro b hb
    have e8 : 8 * M = 2 * (2 * (2 * M)) := by ring
    refine hMk b (intF_le (htr (2 * M) _ ?_)) (intF_le (htr (2 * M) _ ?_))
    · rw [← e8, map_sub, map_one]
      exact hb.1
    · rw [← e8, map_sub, map_one]
      have := hb.2
      rwa [← map_inv] at this
  obtain ⟨y, ⟨k, rfl⟩, w, hw, hyw⟩ := Subgroup.mem_sup.1 ha
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : ∀ z ∈ WE F E (8 * M), cU z ∈ WE F E (8 * M) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hz.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hz.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hζW : Units.map (incAF F E).toMonoidHom ζ ∈ WE F E (8 * M) := by
    have e1 := congrArg cU hyw
    rw [map_mul, hfixa, hcinc, ← hyw] at e1
    have : Units.map (incAF F E).toMonoidHom ζ = w * (cU w)⁻¹ := by
      simp only [ζ, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, e1, mul_comm]
    rw [this]
    exact mul_mem hw (inv_mem (hcW w hw))
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  have hζ1 : (ζ : E) = 1 := by
    by_contra hne
    set x : E := (ζ : E) - 1 with hxdef
    have hx0 : x ≠ 0 := sub_ne_zero.2 hne
    have hxC : incAF F E x ∈ CE F E (8 * M) := by
      have := hζW.1
      rw [hxdef, map_sub, map_one]
      exact this
    obtain ⟨s, hs, hsx⟩ := mem_CE.1 hxC
    have hσx : incAF F E (σ x) = cA σ (incAF F E x) := rfl
    obtain ⟨y, hy⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
    have hyC : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ CE F E (2 * (2 * (16 * M * M))) := by
      rw [← incAF_algebraMap, hy, map_mul, hσx, ← hsx, map_nsmul]
      refine mem_CE.2 ⟨s * cA σ s, SE_mul hs (cA_mem_SE σ hs), ?_⟩
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hyI := htr (16 * M * M) _ hyC
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.HeckeExtend.exists_int_of_mem_intF F y (16 * M * M) (by positivity) hyI
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact mul_ne_zero hx0 ((map_ne_zero σ).2 hx0) hy.symm
    have hbound : ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4 := by
      intro φ
      obtain ⟨τ, hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ
      have hk0 : τ (k : E) ≠ 0 := (map_ne_zero τ).2 k.ne_zero
      have hζn : ‖τ (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ x‖ ≤ 2 := by
        calc ‖τ x‖ = ‖τ (ζ : E) - 1‖ := by rw [hxdef, map_sub, map_one]
        _ ≤ ‖τ (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      nlinarith [norm_nonneg (τ x)]
    have := _root_.GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four F y (16 * M * M) r hy0 hr hbound
    nlinarith
  have hk : σ k = (k : E) := by
    rw [hζv] at hζ1
    exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1
  obtain ⟨f, hf⟩ := hfix k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  have hw' : w = idFF F E (fU⁻¹ * a) := by
    rw [map_mul, map_inv, ← hinc, ← hyw]
    group
  have hb := hcongF (fU⁻¹ * a) (hw' ▸ hw)
  have hfU : lam fU = 1 := h1 (Units.mk0 f hf0)
  have : a = fU * (fU⁻¹ * a) := by group
  rw [this, map_mul, hfU, hb, mul_one]

theorem exists_extend_hecke : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := _root_.GlobalTheory.HeckeExtend.CE_isOpen F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo

  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨_root_.GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf F E _ hN' _ hz, _root_.GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]

end GlobalTheory.HeckeExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZero
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

theorem exists_orthonormal_of_selfDual (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z) (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (L : Submodule K.O V) (hfg : L.FG)
    (hsp : Submodule.span K.E (L : Set V) = ⊤) (hsd : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  have key : ∀ k, k ≤ Module.finrank K.E V → ∃ f : Fin k → V, (∀ i, f i ∈ L) ∧
      (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfo, hfu⟩ := ih (by omega)
      obtain ⟨y, hyL, hyo, hyu⟩ := _root_.GlobalTheory.selfDual_orthogonal_unit_step K V h hadd hsmul hsym L hfg hsp hsd k f hfL hfo hfu (by omega)
      refine ⟨Fin.snoc f y, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyL
        | cast i => simpa using hfL i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hyo j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hsym, hyo i, map_zero]
          | cast j =>
            simp only [Fin.snoc_castSucc]
            exact hfo i j fun e => hij (by rw [e])
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyu
        | cast i => simpa using hfu i
  obtain ⟨f, -, hfo, hfu⟩ := key _ le_rfl
  choose t ht hft using hfu
  choose v hv using fun i => _root_.GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm K (t i) (ht i) (by rw [← hft, ← hsym])
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hsmul, map_mul, hsym z y]
  have ht0 : ∀ i, algebraMap K.O K.E (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (ht i).ne_zero
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    apply ht0 i
    rw [← hv i, h0, zero_mul]
  let g : Fin (Module.finrank K.E V) → V := fun i => (v i)⁻¹ • f i
  have hg : ∀ i j, h (g i) (g j) = if i = j then 1 else 0 := by
    intro i j
    simp only [g, hsmul, hsmul2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hft, ← hv i, map_inv₀]
      have : K.c (v i) ≠ 0 := by simpa using hv0 i
      field_simp
      exact div_self (hv0 i)
    · rw [if_neg hij, hfo i j hij, mul_zero, mul_zero]
  let φ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z
      map_add' := fun y y' => hadd y y' z
      map_smul' := fun a y => by simp [hsmul] }
  have hli : LinearIndependent K.E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (φ (g i)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero] at this
    simpa [φ, hg] using this
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i j => ?_⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
  exact hg i j

theorem X_nonempty_of_N_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (hN : B.N x ≠ 0) :
    (B.X x).Nonempty := by
  by_contra hX
  rw [Set.not_nonempty_iff_eq_empty] at hX
  apply hN
  haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) :=
    ⟨fun o => by
      induction o using Quot.ind with
      | mk L => exact Set.eq_empty_iff_forall_notMem.1 hX L.1 L.2⟩
  unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
  exact finsum_of_isEmpty _

theorem exists_model_of_N_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hB n Q B u x hF hn hσx _ hN
  obtain ⟨L, hlat, -, hsd⟩ := X_nonempty_of_N_ne_zero B x hN
  obtain ⟨b, hb⟩ := exists_orthonormal_of_selfDual K B.A (B.herm x)
    (fun y y' z => by unfold GlobalTheory.UnitLemma.InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)])
    (fun a y z => GlobalTheory.UnitLemma.Basic.herm_smul_left B x y z a)
    (fun y z => GlobalTheory.UnitLemma.Basic.herm_symm B x hσx y z) L hlat.1 hlat.2 hsd
  have hd : Module.finrank K.E B.A = n := hF.2.2.1.trans hn
  refine _root_.GlobalTheory.KapLat.exists_model_of_orthonormal_basis E w hw K e hB n B u x hF.2.2.2 (b.reindex (finCongr hd)) fun i j => ?_
  simp only [Module.Basis.reindex_apply, hb, EmbeddingLike.apply_eq_iff_eq]

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadratic
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem diag_re_le_of_near_min {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (G : ι → ι → Module.End ℂ M) (α β : ℂ) (R : ℝ)
    (hR : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F →
      (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ,
      (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) →
      ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) →
      (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R)
    (hG : IsGl G) (hq : ∀ a b, qop G α β a b = 0) (hL : LocU s G) (U : Submodule ℂ M) (hU : UnitOn s G U) (ω : ℝ)
    (hω : ∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s G v = (ω' : ℂ) • v → ω < ω' + 1)
    (hUe : ∀ u ∈ U, cas s G u = (ω : ℂ) • u) :
    ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, G a a u = m • u → m.re ≤ R :=
  _root_.GlobalTheory.HoweR.re_diag_le_of_eigen_bound ι M s G U R hU (fun x y hy hyU hf hs => hR M G hG hq hL ω hω x y hy hf hs (fun a => hUe _ (hyU a)))

theorem exists_unitOn_diag_bounded : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ,
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F →
    (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F →
    ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  intro ι _ _ s α β α' β'
  obtain ⟨R1, h1⟩ := _root_.GlobalTheory.HoweR.diag_eig_le_of_cas_min ι s α β
  obtain ⟨R2, h2⟩ := _root_.GlobalTheory.HoweR.diag_eig_le_of_cas_min ι (fun a => !s a) α β
  obtain ⟨R3, h3⟩ := _root_.GlobalTheory.HoweR.diag_eig_le_of_cas_min ι s α' β'
  obtain ⟨R4, h4⟩ := _root_.GlobalTheory.HoweR.diag_eig_le_of_cas_min ι (fun a => !s a) α' β'
  refine ⟨max (max R1 R2) (max R3 R4), ?_⟩
  intro M _ _ F hnt hG hq hq' hL
  obtain ⟨hGn, hcn, hcs, hUs, hLs⟩ := sym_negT_swap ι M s F
  obtain ⟨-, hcn', hcs', hUs', hLs'⟩ := sym_negT_swap ι M s (negT F)
  let S : Set ℝ := {ω' | ∃ v : M, v ≠ 0 ∧ cas s F v = (ω' : ℂ) • v}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨U, hxU, hU⟩ := hL {x}
    have hne : U ≠ ⊥ := by
      intro h
      have := hxU x (Finset.mem_singleton_self x)
      rw [h, Submodule.mem_bot] at this
      exact hx this
    obtain ⟨ω, v, -, hv, hcv⟩ := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).2 hne
    exact ⟨ω, v, hv, hcv⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, fun ω' hω' => ?_⟩
    obtain ⟨v, hv, hcv⟩ := hω'
    obtain ⟨U, hvU, hU⟩ := hL {v}
    have := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).1 (ω' : ℂ) v (hvU v (Finset.mem_singleton_self v)) hv hcv
    simpa using this.2
  obtain ⟨ω, ⟨v, hv, hcv⟩, hωlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_one (sInf S))
  have hω : ∀ (ω' : ℝ) (w : M), w ≠ 0 → cas s F w = (ω' : ℂ) • w → ω < ω' + 1 := fun ω' w hw hcw => by
    have := csInf_le hSbdd ⟨w, hw, hcw⟩
    linarith
  obtain ⟨U0, hvU0, hU0⟩ := hL {v}
  let U : Submodule ℂ M := U0 ⊓ LinearMap.ker (cas s F - (ω : ℂ) • (1 : Module.End ℂ M))
  have hUe : ∀ u ∈ U, cas s F u = (ω : ℂ) • u := fun u hu => by
    have h2 := hu.2
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    simpa using h2
  have hvU : v ∈ U := ⟨hvU0 v (Finset.mem_singleton_self v), by
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; simpa using hcv⟩
  have hUst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U := by
    intro a b hab u hu
    refine ⟨hU0.2.1 a b hab u hu.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ M => T u) (_root_.GlobalTheory.HoweR.cas_mul_comm_of_block ι M s F hG a b hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hUe u hu]
    simp
  have hU : UnitOn s F U := _root_.GlobalTheory.HoweR.unitOn_of_le ι M s F U0 U hU0 inf_le_left hUst
  refine ⟨U, fun h => hv (by rw [h, Submodule.mem_bot] at hvU; exact hvU), hU, ?_⟩
  intro a u hu hu0 m hm
  have b1 := diag_re_le_of_near_min s F α β R1 h1 hG hq hL U hU ω hω hUe
  have b2 := diag_re_le_of_near_min (fun a => !s a) F α β R2 h2 hG hq (hLs hL).2 U (hUs U hU).2 ω
    (by rw [hcs]; exact hω) (by rw [hcs]; exact hUe)
  have b3 := diag_re_le_of_near_min s (negT F) α' β' R3 h3 (hGn hG) hq' (hLs hL).1 U (hUs U hU).1 ω
    (by rw [hcn]; exact hω) (by rw [hcn]; exact hUe)
  have b4 := diag_re_le_of_near_min (fun a => !s a) (negT F) α' β' R4 h4 (hGn hG) hq' (hLs' (hLs hL).1).2 U
    (hUs' U (hUs U hU).1).2 ω (by rw [hcs', hcn]; exact hω) (by rw [hcs', hcn]; exact hUe)
  have hmn : negT F a a u = (-m) • u := by simp [negT, hm]
  have l1 : R1 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_left _ _)
  have l2 : R2 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_left _ _)
  have l3 : R3 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_right _ _)
  have l4 : R4 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_right _ _)
  rw [abs_le]
  cases hsa : s a
  · have e1 := b2 a (by simp [hsa]) u hu hu0 m hm
    have e2 := b4 a (by simp [hsa]) u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith
  · have e1 := b1 a hsa u hu hu0 m hm
    have e2 := b3 a hsa u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleByO1
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_veryAmpleBy_O1 : ∀ Y : Var ℂ, ∃ s : Fin (Y.N + 1) → ((ProjSpace.O1 ℂ Y.N).pull Y.ι).Sec, GlobalTheory.AbLaw.VeryAmpleBy Y.str ((ProjSpace.O1 ℂ Y.N).pull Y.ι) s :=
  fun Y => ⟨_, ProjSpace.veryAmpleBy_secPull_coord Y.ι⟩

end GlobalTheory.ProjVar
end

