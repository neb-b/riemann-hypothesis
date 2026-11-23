module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped NNReal

namespace GlobalTheory.RatCount

theorem gl_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ))
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.Finite ∧
      (({γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C0, k, hk⟩ := hA F E
  obtain ⟨c, a, ha⟩ := hB F E
  refine ⟨C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)), a * k * (N * N), fun T hT => ?_⟩
  set B : ℝ := max 1 c * T ^ a with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)
  obtain ⟨hXf, hXc⟩ := hk B hB1
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set S := {γ : GL (Fin N) E | (heightGL F (bc (inclR (F := F) (AF F)) γ) : ℝ) ≤ T} with hSdef
  have hmem : ∀ γ ∈ S, ∀ p : Fin N × Fin N, (γ : Matrix (Fin N) (Fin N) E) p.1 p.2 ∈ X := by
    intro γ hγ p j
    refine (ha _ j).trans ?_
    have h1 : (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ≤ T :=
      (NNReal.coe_le_coe.2 (hC F E N γ p.1 p.2)).trans hγ
    calc c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a
        ≤ max 1 c * (htE F ((γ : Matrix (Fin N) (Fin N) E) p.1 p.2) : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 a)
          (zero_le_one.trans (le_max_left _ _))
  let f : GL (Fin N) E → (Fin N × Fin N → E) := fun γ p => (γ : Matrix (Fin N) (Fin N) E) p.1 p.2
  have hinj : Set.InjOn f S := fun γ _ δ _ h => Units.ext (Matrix.ext fun i j => congrFun h (i, j))
  set P : Finset (Fin N × Fin N → E) := Fintype.piFinset fun _ => hXf.toFinset with hPdef
  have hmaps : ∀ γ ∈ S, f γ ∈ (P : Set (Fin N × Fin N → E)) := fun γ hγ => by
    simp only [P, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun p => hmem γ hγ p
  have hSf : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset (by
    rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj
  refine ⟨hSf, ?_⟩
  have h1 : S.ncard ≤ (P : Set (Fin N × Fin N → E)).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj P.finite_toSet
  rw [Set.ncard_coe_finset, hPdef, Fintype.card_piFinset] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [← Set.ncard_eq_toFinset_card X hXf] at h1
  have hC0 : 0 ≤ C0 := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans hXc
    exact nonneg_of_mul_nonneg_left this (by positivity)
  calc ((S.ncard : ℕ) : ℝ) ≤ ((X.ncard : ℝ)) ^ (N * N) := by exact_mod_cast h1
    _ ≤ (C0 * B ^ k) ^ (N * N) := pow_le_pow_left₀ (by positivity) hXc _
    _ = C0 ^ (N * N) * (max 1 c) ^ (k * (N * N)) * T ^ (a * k * (N * N)) := by
        rw [hBdef]; ring

theorem gq_count (hA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k) (hB : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a) (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ)) {D : D7} (V : HSp D) :
    ∃ (C : ℝ) (A : ℕ), ∀ T : ℝ, 1 ≤ T →
      {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.Finite ∧
      (({γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T}.ncard : ℕ) : ℝ) ≤ C * T ^ A := by
  obtain ⟨C, A, h⟩ := gl_count hA hB hC D.host.F D.host.E V.rank
  refine ⟨C, A, fun T hT => ?_⟩
  obtain ⟨hf, hc⟩ := h T hT
  have hex : ∀ γ : GQ V, ∃ δ : GL (Fin V.rank) D.host.E,
      bc (inclR (F := D.host.F) (AF D.host.F)) δ = matHom V (γ : GA D V) := by
    intro γ
    have h1 := γ.2
    simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1
    obtain ⟨δ, -, hδ⟩ := h1
    exact ⟨δ, hδ⟩
  choose φ hφ using hex
  have hmaps : ∀ γ ∈ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T},
      φ γ ∈ {δ : GL (Fin V.rank) D.host.E | (heightGL D.host.F (bc (inclR (F := D.host.F) (AF D.host.F)) δ) : ℝ) ≤ T} := by
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    rw [hφ]
    exact hγ
  have hinj : Set.InjOn φ {γ : GQ V | GlobalTheory.Grow.height V (γ : GA D V) ≤ T} := by
    intro a _ b _ hab
    have h2 : matHom V (a : GA D V) = matHom V (b : GA D V) := by rw [← hφ, ← hφ, hab]
    unfold Formalism.L2.Theta.matHom at h2
    exact Subtype.ext (Subgroup.subtype_injective _ h2)
  refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
  exact (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)).trans hc

theorem ncard_rat_mem_translate_le : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  intro D V Ω hΩ
  obtain ⟨C, A, hcount⟩ := gq_count _root_.GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le _root_.GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL V
  have hK : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω)) :=
    (hΩ.prod hΩ).image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  have hC : 0 ≤ C := by
    have := (Nat.cast_nonneg (α := ℝ) _).trans (hcount 1 le_rfl).2
    simpa using this
  refine ⟨A, C * max C₀ 1 ^ A, fun g x => ?_⟩
  rcases Set.eq_empty_or_nonempty {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} with hS | ⟨γ₀, hγ₀⟩
  · rw [hS]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    have := GlobalTheory.Grow.height_pos V g
    positivity
  · set T : ℝ := max C₀ 1 * GlobalTheory.Grow.height V g ^ 2 with hTdef
    have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ (GlobalTheory.Grow.one_le_height V g))
    obtain ⟨hf, hc⟩ := hcount T hT
    let φ : GQ V → GQ V := fun γ => γ * γ₀⁻¹
    obtain ⟨y₀, hy₀, e₀⟩ := hγ₀
    have hmaps : ∀ γ ∈ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω},
        φ γ ∈ {δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T} := by
      intro γ hγ
      obtain ⟨y, hy, e⟩ := hγ
      have h1 : ((φ γ : GQ V) : GA D V) = g * (y * y₀⁻¹) * g⁻¹ := by
        have e' : (γ : GA D V) = g * y * x⁻¹ := by
          rw [show g * y = (γ : GA D V) * x from e, mul_inv_cancel_right]
        have e₀' : (γ₀ : GA D V) = g * y₀ * x⁻¹ := by
          rw [show g * y₀ = (γ₀ : GA D V) * x from e₀, mul_inv_cancel_right]
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, e', e₀']
        group
      have hyy : GlobalTheory.Grow.height V (y * y₀⁻¹) ≤ max C₀ 1 :=
        (hC₀ _ ⟨(y, y₀), ⟨hy, hy₀⟩, rfl⟩).trans (le_max_left _ _)
      show GlobalTheory.Grow.height V ((φ γ : GQ V) : GA D V) ≤ T
      rw [h1]
      calc GlobalTheory.Grow.height V (g * (y * y₀⁻¹) * g⁻¹)
          ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height V (y * y₀⁻¹) * GlobalTheory.Grow.height V g⁻¹ :=
            (GlobalTheory.Grow.height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le V _ _)
              (GlobalTheory.Grow.height_pos V _).le)
        _ ≤ GlobalTheory.Grow.height V g * max C₀ 1 * GlobalTheory.Grow.height V g := by
            rw [GlobalTheory.Grow.height_inv]
            have := GlobalTheory.Grow.height_pos V g
            gcongr
        _ = T := by rw [hTdef]; ring
    have hinj : Set.InjOn φ {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω} :=
      fun a _ b _ hab => mul_right_cancel hab
    refine ⟨Set.Finite.of_finite_image (hf.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmaps γ hγ)) hinj, ?_⟩
    calc (({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℕ) : ℝ)
        ≤ (({δ : GQ V | GlobalTheory.Grow.height V (δ : GA D V) ≤ T}.ncard : ℕ) : ℝ) :=
          Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn φ hmaps hinj hf)
      _ ≤ C * T ^ A := hc
      _ = C * max C₀ 1 ^ A * GlobalTheory.Grow.height V g ^ (2 * A) := by rw [hTdef]; ring

end GlobalTheory.RatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantThetaPairingOfNoTensorIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairVanish

open GlobalTheory.ArchRec.PairTensor (ext_ctr exists_map)
open GlobalTheory.Chain.IoLift.UImg (sumAct sumMod sumAct_single)

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map_right {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    (g : U →ₗ[ℂ] U') (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ctr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_universal (M : GKMod r s) (a : Mat p q →ₗ[ℂ] Module.End ℂ M.V)
    (hc : ∀ Y Z, a Y * M.act Z = M.act Z * a Y) (U : Type) [AddCommGroup U] [Module ℂ U] :
    ∃ (Q : GKMod r s) (B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] Q.V), PInv a R B₀ ∧
      (∀ Z P v, B₀ (M.act Z P) v = Q.act Z (B₀ P v)) ∧
      ∀ P v, B₀ P v = 0 → ∀ B : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B → B P v = 0 := by

  obtain ⟨G, hG⟩ : ∃ G : Set (R.HK.V →₀ M.V), G =
      {x | (∃ (P : M.V) (v w : R.HK.V),
          x = Finsupp.single (v + w) P - Finsupp.single v P - Finsupp.single w P) ∨
        (∃ (P : M.V) (v : R.HK.V) (c : ℂ),
          x = Finsupp.single (c • v) P - starRingEnd ℂ c • Finsupp.single v P) ∨
        ∃ (P : M.V) (v : R.HK.V) (Z : Mat p q),
          Z ∈ upq p q ∧ x = Finsupp.single v (a Z P) + Finsupp.single (R.HK.act Z v) P} := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ (R.HK.V →₀ M.V), N = Submodule.span ℂ G := ⟨_, rfl⟩
  have hGN : ∀ x ∈ G, x ∈ N := fun x hx => hNdef ▸ Submodule.subset_span hx

  have hN : ∀ Z : Mat r s, N ≤ N.comap (sumAct M R.HK.V Z) := by
    intro Z
    conv_lhs => rw [hNdef]
    rw [Submodule.span_le]
    intro x hx
    rw [hG] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rcases hx with ⟨P, v, w, rfl⟩ | ⟨P, v, c, rfl⟩ | ⟨P, v, Y, hY, rfl⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inl ⟨M.act Z P, v, w, by simp [sumAct_single]⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inr (Or.inl ⟨M.act Z P, v, c, by simp [sumAct_single]⟩)
    · refine hGN _ ?_
      rw [hG]
      have hcomm : a Y (M.act Z P) = M.act Z (a Y P) := LinearMap.congr_fun (hc Y Z) P
      exact Or.inr (Or.inr ⟨M.act Z P, v, Y, hY, by simp [sumAct_single, hcomm]⟩)
  let actQ : Mat r s →ₗ[ℂ] Module.End ℂ ((R.HK.V →₀ M.V) ⧸ N) :=
    { toFun := fun Z => N.mapQ N (sumAct M R.HK.V Z) (hN Z)
      map_add' := fun Z Z' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply]
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply] }
  have hQ : ∀ Z y, actQ Z (Submodule.Quotient.mk y) = Submodule.Quotient.mk (sumAct M R.HK.V Z y) :=
    fun _ _ => rfl
  let Q : GKMod r s :=
    { V := (R.HK.V →₀ M.V) ⧸ N
      act := actQ
      lie := fun X Y => by
        have h : sumAct M R.HK.V (X * Y - Y * X) =
            sumAct M R.HK.V X * sumAct M R.HK.V Y - sumAct M R.HK.V Y * sumAct M R.HK.V X :=
          (sumMod M R.HK.V).lie X Y
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply, hQ]
        rw [h]
        simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.Quotient.mk_sub]
      kfin := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        obtain ⟨W, hW, hy, hK⟩ : ∃ W : Submodule ℂ (R.HK.V →₀ M.V), FiniteDimensional ℂ W ∧ y ∈ W ∧
            KStable (sumAct M R.HK.V) W := (sumMod M R.HK.V).kfin y
        refine ⟨W.map N.mkQ, Module.Finite.map W N.mkQ, Submodule.mem_map_of_mem hy, ?_⟩
        intro X hX w hw
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
        exact Submodule.mem_map_of_mem (hK X hX u hu)
      wts := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        have hy : y ∈ ⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ := (sumMod M R.HK.V).wts y
        have hle : (⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ).map N.mkQ ≤
            ⨆ μ : Ix r s → ℚ, wtSub actQ μ := by
          rw [Submodule.map_iSup]
          refine iSup_mono fun μ => ?_
          rw [Submodule.map_le_iff_le_comap]
          intro u hu
          rw [Submodule.mem_comap]
          simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hu ⊢
          intro i
          have hi := hu i
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hi ⊢
          rw [Submodule.mkQ_apply, hQ, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, hi,
            Submodule.Quotient.mk_zero]
        exact hle (Submodule.mem_map_of_mem hy) }
  let B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] ((R.HK.V →₀ M.V) ⧸ N) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P v => N.mkQ (Finsupp.single v P))
      (fun P P' v => by simp [Finsupp.single_add])
      (fun c P v => by
        simp only [RingHom.id_apply]
        rw [← Finsupp.smul_single, map_smul])
      (fun P v w => by
        rw [← map_add (f := _), ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inl ⟨P, v, w, by abel⟩)
      (fun c P v => by
        rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inr (Or.inl ⟨P, v, c, rfl⟩))
  refine ⟨Q, B₀, ?_, ?_, ?_⟩
  · intro Z hZ P v
    show N.mkQ (Finsupp.single v (a Z P)) + N.mkQ (Finsupp.single (R.HK.act Z v) P) = 0
    rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine hGN _ ?_
    rw [hG]
    exact Or.inr (Or.inr ⟨P, v, Z, hZ, rfl⟩)
  · intro Z P v
    show N.mkQ (Finsupp.single v (M.act Z P)) = actQ Z (N.mkQ (Finsupp.single v P))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, hQ, sumAct_single]
  · intro P v h B hB
    let L : (R.HK.V →₀ M.V) →ₗ[ℂ] U := Finsupp.lsum ℂ fun w => B.flip w
    have hL : ∀ w (P' : M.V), L (Finsupp.single w P') = B P' w := by
      intro w P'
      simp [L]
    have hNL : N ≤ LinearMap.ker L := by
      rw [hNdef, Submodule.span_le]
      intro x hx
      rw [hG] at hx
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hx with ⟨P', w, w', rfl⟩ | ⟨P', w, c, rfl⟩ | ⟨P', w, Z, hZ, rfl⟩
      · simp [hL]
      · simp [hL]
      · rw [map_add (f := _), hL, hL]
        exact hB Z hZ P' w
    have h' : N.mkQ (Finsupp.single v P) = 0 := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
    have := hNL h'
    rw [LinearMap.mem_ker, hL] at this
    exact this

theorem pairNo_of_tensNo : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁), IsGK a₁ → IsGK a₂ → (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → AdmGK R₁.HK → TensNo a₁ a₂ R₁ → PairNo a₁ R₁ := by
  intro p q r s T₁ σ a₁ a₂ R₁ h₁ h₂ hc hA hT U _ _ B hB

  let M : GKMod r s :=
    { V := MvPolynomial σ ℂ
      act := a₂
      lie := h₂.1
      kfin := h₂.2.1
      wts := h₂.2.2 }
  obtain ⟨Q, B₀, hB₀, hZ, huniv⟩ := exists_universal R₁ M a₁ hc U
  obtain ⟨f, hf, hfB⟩ := GlobalTheory.ArchRec.PairTensor.exists_map R₁ a₁ h₁ hA B₀ hB₀
  have hT' : TIntw a₁ a₂ R₁.HK Q f := by
    refine ⟨hf, fun Y => LinearMap.ext fun P => ?_⟩
    refine GlobalTheory.ArchRec.PairTensor.ext_ctr R₁ Q.V _ _ fun v => ?_
    simp only [LinearMap.comp_apply]
    rw [← hfB, ctr_map_right, ← hfB]
    exact hZ Y P v
  have hf0 : f = 0 := hT Q f hT'
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  refine huniv P v ?_ B hB
  rw [hfB, hf0, LinearMap.zero_apply, map_zero]

end GlobalTheory.ArchRec.PairVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConvRDeriv

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem oneP_add' (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  have e : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun r =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX r
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (e s) (e t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

theorem leftDeriv (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    starFn (Rder θ V τ X (starFn f)) ∈ CcGA V ∧ ∀ z t, HasDerivAt (fun s => f ((oneP θ V τ X s)⁻¹ * z))
      (starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z)) t := by
  have hh : starFn f ∈ CcGA V := starFn_mem_ccAd hf
  have hsm := ccGA_smooth_and_Rder_mem D V θ hθ _ hh
  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => starFn f (w * oneP θ V τ X t)) (Rder θ V τ X (starFn f) w) 0 := fun w =>
    (((isSmoothRealFam_oneP hθ hX).1.contDiff hh w).differentiable (by simp) 0).hasDerivAt
  refine ⟨starFn_mem_ccAd (hsm.2 τ X hX), fun z t => ?_⟩
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0 (z⁻¹ * oneP θ V τ X t))
  have h2 : HasDerivAt (fun s : ℝ => starFn f (z⁻¹ * oneP θ V τ X s)) (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) t :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [mul_assoc, ← oneP_add' hθ hX, add_sub_cancel])
  have h3 := h2.star
  have ef : (fun s => f ((oneP θ V τ X s)⁻¹ * z)) = fun s => star (starFn f (z⁻¹ * oneP θ V τ X s)) := by
    funext s; simp [starFn, mul_inv_rev, Complex.star_def]
  have ev : starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z) =
      star (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) := by
    simp [starFn, mul_inv_rev, Complex.star_def]
  rw [ef, ev]; exact h3

theorem Rder_convR : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  intro D V μ _ _ θ hθ f hf τ X hX
  obtain ⟨hf', hD⟩ := leftDeriv hθ hX hf
  set f' := starFn (Rder θ V τ X (starFn f)) with hf'_def
  set u := oneP θ V τ X with hu_def
  have hu := isSmoothRealFam_oneP hθ hX
  have huc : Continuous u := hu.2.1
  have hu0 : u 0 = 1 := hu.2.2
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨hf'c, hf's⟩ := continuous_of_mem_ccAd hf'
  refine ⟨f', hf', ?_, fun F => ?_⟩
  · refine closure_minimal (fun y hy => ?_) (isClosed_tsupport f)
    by_contra hy'
    apply hy
    have ht : Tendsto (fun s : ℝ => (u s)⁻¹ * y) (𝓝 0) (𝓝 y) := by
      simpa [hu0] using ((huc.inv.mul continuous_const).tendsto (f := fun s : ℝ => (u s)⁻¹ * y) 0)
    have hev : (fun s : ℝ => f ((u s)⁻¹ * y)) =ᶠ[𝓝 0] fun _ => 0 :=
      ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hy')
    have h1 := (hD y 0).deriv
    rw [hu0, inv_one, one_mul, hev.deriv_eq, deriv_const] at h1
    exact h1.symm
  · set φ := lift (GQ V) F
    have hφ : LocallyIntegrable φ μ :=
      locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
    funext g
    obtain ⟨M, hM⟩ := hf'c.bounded_above_of_compact_support hf's
    have hK : IsCompact ((fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')) :=
      ((isCompact_closedBall 0 1).prod hf's.isCompact).image (by fun_prop)
    set K := (fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (F := fun t y => f ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (F' := fun t y => f' ((u t)⁻¹ * (g⁻¹ * y)) * φ y)
      (bound := K.indicator fun y => M * ‖φ y‖) (s := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (.of_forall fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (by simpa [hu0] using (GlobalTheory.AutomorphicL2Local.continuous_integral_inv_mul_of_locallyIntegrable hfc hfs hφ).1 g)
      ((hf'c.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (.of_forall fun y t ht => ?_)
      ((integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M))
      (.of_forall fun y t _ => (hD (g⁻¹ * y) t).mul_const (φ y))
    · have e1 : (fun t : ℝ => convR μ f φ (g * u t)) = fun t => ∫ y, f ((u t)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        funext t; rw [convR_eq]; simp only [mul_inv_rev, mul_assoc]
      have e2 : convR μ f' φ g = ∫ y, f' ((u 0)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        rw [convR_eq, hu0]; simp
      show deriv (fun t : ℝ => convR μ f φ (g * u t)) 0 = _
      rw [e1, e2]
      exact key.2.deriv
    · by_cases hy : y ∈ K
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (f := f') fun h => hy ⟨(t, _), ⟨?_, h⟩, ?_⟩]
        · simp
        · exact ht
        · simp [mul_assoc]

end GlobalTheory.ConvRDeriv
end
end

