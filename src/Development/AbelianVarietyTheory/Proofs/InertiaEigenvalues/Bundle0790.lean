module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJointHighestWeightHarmonicSliceOuterVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.Slice

open MvPolynomial GlobalTheory.Capelli

variable {σ σ₀ : Type} (ι : σ₀ → σ)

abbrev Outer := {v : σ // v ∉ Set.range ι}

noncomputable def sliceVar (v : σ) : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) := by
  classical
  exact if h : v ∈ Set.range ι then C (X h.choose) else X ⟨v, h⟩

noncomputable def slice : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) :=
  aeval (sliceVar ι)

variable {ι}

theorem slice_X_inner (hι : Function.Injective ι) (u : σ₀) : slice ι (X (ι u)) = C (X u) := by
  have h : ι u ∈ Set.range ι := ⟨u, rfl⟩
  simp only [slice, aeval_X, sliceVar, dite_eq_left h]
  rw [hι h.choose_spec]

theorem slice_X_outer {v : σ} (hv : v ∉ Set.range ι) : slice ι (X v) = X ⟨v, hv⟩ := by
  simp only [slice, aeval_X, sliceVar, dite_eq_right hv]

theorem slice_C (a : ℂ) : slice ι (C a) = C (C a) := by
  simp [slice, MvPolynomial.algebraMap_apply]

variable (ι)

noncomputable def coefAt (t : Outer ι →₀ ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ₀ ℂ where
  toFun Q := AddMonoidAlgebra.coeff (slice ι Q) t
  map_add' _ _ := by simp
  map_smul' c Q := by simp

variable {ι}

theorem coefAt_X_mul (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) (u : σ₀)
    (Q : MvPolynomial σ ℂ) : coefAt ι t (X (ι u) * Q) = X u * coefAt ι t Q := by
  simp [coefAt, map_mul, slice_X_inner hι, coeff_C_mul]

theorem coefAt_pderiv (hι : Function.Injective ι) (u : σ₀) (Q : MvPolynomial σ ℂ) :
    ∀ t, coefAt ι t (pderiv (ι u) Q) = pderiv u (coefAt ι t Q) := by
  classical
  simp only [coefAt, LinearMap.coe_mk, AddHom.coe_mk]
  induction Q using MvPolynomial.induction_on with
  | C a => intro t; simp only [pderiv_C, map_zero, AddMonoidAlgebra.coeff_zero, slice_C, coeff_C]; split_ifs <;> simp
  | add p q hp hq => intro t; simp [hp, hq]
  | mul_X p v hp =>
    intro t
    by_cases hv : v ∈ Set.range ι
    · obtain ⟨w, rfl⟩ := hv
      by_cases huw : w = u
      · subst huw
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X, coeff_C_mul,
          mul_comm (slice ι p) (C (X w))]
        ring
      · have h1 : ι u ≠ ι w := fun h => huw (hι h).symm
        have h2 : u ≠ w := fun h => huw h.symm
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X,
          h1, h2, coeff_C_mul, mul_comm (slice ι p) (C (X w))]
    · have h1 : ι u ≠ v := fun h => hv ⟨u, h⟩
      simp only [Derivation.leibniz, map_mul, smul_eq_mul, pderiv_X, Pi.single_apply,
        ite_eq_right h1.symm, mul_zero, zero_add, slice_X_outer hv]
      rw [coeff_X_mul', coeff_mul_X']
      split_ifs
      · rw [hp]
      · simp

theorem coefAt_jointTop (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) {k l N : ℕ}
    (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ)
    (β : Fin l → ℂ) (P : MvPolynomial σ ℂ)
    (h : GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P) :
    GlobalTheory.CompactHarm.JointTop z y κ α β (coefAt ι t P) := by
  have hm : ∀ i j, coefAt ι t (mixedOp ℂ (ι ∘ z) (ι ∘ y) i j P) =
      mixedOp ℂ z y i j (coefAt ι t P) := fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mixedOp_apply, map_sub, map_sum, Function.comp_apply, coefAt_X_mul hι,
      coefAt_pderiv hι]
  have hr : ∀ {K : ℕ} (w : Fin K × Fin N → σ₀) (a b : Fin K),
      coefAt ι t (rowOp ℂ (ι ∘ w) a b P) = rowOp ℂ w a b (coefAt ι t P) := fun w a b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rowOp_apply, map_sum, Function.comp_apply, coefAt_X_mul hι, coefAt_pderiv hι]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' hc => ?_, fun c => ?_, fun d d' hd => ?_,
    fun d => ?_, fun c d => ?_⟩
  · rw [← hm, h1 i j hij, map_zero]
  · rw [← hm, h2 i, map_smul]
  · rw [← hr, h3 c c' hc, map_zero]
  · rw [← hr, h4 c, map_smul]
  · rw [← hr, h5 d d' hd, map_zero]
  · rw [← hr, h6 d, map_smul]
  · have := congrArg (coefAt ι t) (h7 c d)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, Function.comp_apply, coefAt_pderiv hι, map_zero] using this

variable (ι)

noncomputable def unslice : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) →+* MvPolynomial σ ℂ :=
  eval₂Hom (rename ι).toRingHom (fun r => X r.1)

variable {ι}

theorem unslice_slice_X (hι : Function.Injective ι) (v : σ) : unslice ι (slice ι (X v)) = X v := by
  by_cases hv : v ∈ Set.range ι
  · obtain ⟨w, rfl⟩ := hv
    rw [slice_X_inner hι]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
  · rw [slice_X_outer hv]
    simp only [unslice, coe_eval₂Hom, eval₂_X]

theorem unslice_slice (hι : Function.Injective ι) (Q : MvPolynomial σ ℂ) :
    unslice ι (slice ι Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [slice_C]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, unslice_slice_X hι]

theorem slice_decomp (hι : Function.Injective ι) (P : MvPolynomial σ ℂ) :
    P = ∑ t ∈ (slice ι P).support,
      rename ι (coefAt ι t P) * t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← unslice_slice hι P, (slice ι P).as_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [unslice, eval₂_monomial, coefAt]

theorem vars_outer_prod (t : Outer ι →₀ ℕ) :
    ∀ v ∈ (t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e)).vars, v ∉ Set.range ι := by
  classical
  intro v hv
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 (vars_prod _ hv)
  have := vars_pow _ _ hr
  rw [vars_X, Finset.mem_singleton] at this
  exact this ▸ r.2

noncomputable def outerEmb : (Outer ι →₀ ℕ) ↪ (σ →₀ ℕ) :=
  ⟨Finsupp.mapDomain Subtype.val, Finsupp.mapDomain_injective Subtype.val_injective⟩

noncomputable def outerBack (i : σ →₀ ℕ) : Outer ι →₀ ℕ :=
  Finsupp.comapDomain Subtype.val i Subtype.val_injective.injOn

theorem outerBack_emb (t : Outer ι →₀ ℕ) : outerBack (outerEmb t) = t :=
  Finsupp.comapDomain_mapDomain _ Subtype.val_injective t

end GlobalTheory.Slice

open GlobalTheory.Slice in
theorem GlobalTheory.jointTop_slice : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι →
    ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ)
    (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ),
    GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P →
    ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ),
      P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧
      (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧
      ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  intro σ σ₀ _ ι hι k l N z y κ α β P hP
  refine ⟨(slice ι P).support.map (outerEmb (ι := ι)), fun i => coefAt ι (outerBack (ι := ι) i) P,
    fun i => (outerBack (ι := ι) i).prod (fun r n => (MvPolynomial.X r.1 : MvPolynomial σ ℂ) ^ n), ?_, ?_, ?_⟩
  · rw [Finset.sum_map]
    simp only [outerBack_emb]
    exact slice_decomp hι P
  · intro i _
    exact coefAt_jointTop hι _ z y κ α β P hP
  · intro i _
    exact vars_outer_prod _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicMultiplicityOneCoverin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.CompactHarm

theorem fst_eq_of_mixedWeight {k l p q : ℕ} (N : ℕ) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (hpq : p + q ≤ N) (ha : ∀ c, 0 < a c ↔ (c : ℕ) < p) (hb : ∀ d, 0 < b d ↔ (d : ℕ) < q)
    (c : Fin k) :
    a c = if h : (c : ℕ) < N then (mixedWeight N a b ⟨c, h⟩).toNat else 0 := by
  have hac := ha c
  split_ifs with h
  · rw [mixedWeight_apply]
    simp only [c.2, dif_pos, Fin.eta]
    split_ifs with h2
    · have hb' : (0 : ℤ) ≤ (b ⟨N - 1 - c, h2⟩ : ℤ) := by positivity
      have h4 : (c : ℕ) < N := h
      by_cases hcp : (c : ℕ) < p
      · have hbc := hb ⟨N - 1 - c, h2⟩
        have : b ⟨N - 1 - c, h2⟩ = 0 := by simp only at hbc; omega
        rw [this]; omega
      · have : a c = 0 := by omega
        rw [this]; omega
    · omega
  · omega

theorem snd_eq_of_mixedWeight {k l p q : ℕ} (N : ℕ) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (hpq : p + q ≤ N) (ha : ∀ c, 0 < a c ↔ (c : ℕ) < p) (hb : ∀ d, 0 < b d ↔ (d : ℕ) < q)
    (d : Fin l) :
    b d = if h : (d : ℕ) < N then (-mixedWeight N a b ⟨N - 1 - d, by omega⟩).toNat else 0 := by
  have hbd := hb d
  split_ifs with h
  · rw [mixedWeight_apply]
    have e : N - 1 - (N - 1 - (d : ℕ)) = d := by omega
    have hd : N - 1 - (N - 1 - (d : ℕ)) < l := by omega
    rw [dif_pos hd]
    have hbe : b ⟨N - 1 - (N - 1 - (d : ℕ)), hd⟩ = b d := congrArg b (Fin.ext e)
    simp only [hbe]
    split_ifs with h1
    · have ha' : (0 : ℤ) ≤ (a ⟨N - 1 - d, h1⟩ : ℤ) := by positivity
      have hac := ha ⟨N - 1 - d, h1⟩
      by_cases hdq : (d : ℕ) < q
      · have : a ⟨N - 1 - d, h1⟩ = 0 := by simp only at hac; omega
        rw [this]; omega
      · have : b d = 0 := by omega
        rw [this]; omega
    · omega
  · omega

theorem jointTop_line : ∀ {σ : Type} {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ),
    Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) →
    (∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) → ∀ κ : Fin N → ℂ, ∃ Q₀ : MvPolynomial σ ℂ,
    ∀ (α : Fin k → ℂ) (β : Fin l → ℂ) (f : MvPolynomial σ ℂ),
      GlobalTheory.CompactHarm.JointTop z y κ α β f → ∃ r : ℂ, f = r • Q₀ := by
  intro σ k l N z y hz hy hzy hs κ
  classical
  by_cases hex : ∃ α β f, f ≠ 0 ∧ JointTop z y κ α β f
  · obtain ⟨α₀, β₀, f₀, hf0, hJ0⟩ := hex
    obtain ⟨a, b, p, q, hpq, hp, hq, hpa, hqb, hκ, rfl, rfl, hhom⟩ :=
      weights_of_jointTop z hz y hy hzy hs κ α₀ β₀ hf0 hJ0
    have hbij : Function.Bijective (Sum.elim z y) := by
      refine ⟨hz.sumElim hy hzy, fun s => ?_⟩
      rcases hs s with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨.inl u, rfl⟩
      · exact ⟨.inr u, rfl⟩
    have : Finite σ := Finite.of_surjective _ hbij.2
    have := finite_homog (σ := σ) (∑ c, a c + ∑ d, b d)
    have ha : Antitone a := fun i j hij => by
      have := highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (homogeneousSubmodule σ ℂ _)
        (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) f₀ hhom hf0
        (fun c => a c) hJ0.2.2.1 (fun c => by simpa using hJ0.2.2.2.1 c) hij
      exact Int.ofNat_le.1 this
    have hb : Antitone b := fun i j hij => by
      have := highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) (homogeneousSubmodule σ ℂ _)
        (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) f₀ hhom hf0
        (fun c => b c) hJ0.2.2.2.2.1 (fun c => by simpa using hJ0.2.2.2.2.2.1 c) hij
      exact Int.ofNat_le.1 this
    obtain ⟨P₀, -, -, hu⟩ := exists_unique_jointTop z hz y hy hzy hs hpq hp hq a b ha hb
      (fun c hc => by have := hpa c; omega) (fun d hd => by have := hqb d; omega)
    subst hκ
    refine ⟨P₀, fun α β f hJ => ?_⟩
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    obtain ⟨a', b', p', q', hpq', -, -, hpa', hqb', hκ', rfl, rfl, -⟩ :=
      weights_of_jointTop z hz y hy hzy hs _ α β hf hJ
    have hw : mixedWeight N a b = mixedWeight N a' b' :=
      funext fun i => by exact_mod_cast congrFun hκ' i
    have e1 : a' = a := funext fun c => by
      rw [fst_eq_of_mixedWeight N a' b' hpq' hpa' hqb' c, fst_eq_of_mixedWeight N a b hpq hpa hqb c,
        hw]
    have e2 : b' = b := funext fun d => by
      rw [snd_eq_of_mixedWeight N a' b' hpq' hpa' hqb' d, snd_eq_of_mixedWeight N a b hpq hpa hqb d,
        hw]
    subst e1 e2
    exact hu f hJ
  · refine ⟨0, fun α β f hJ => ⟨0, ?_⟩⟩
    by_contra hf
    exact hex ⟨α, β, f, by simpa using hf, hJ⟩

end GlobalTheory.CompactHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntegralFormsOfRationalAndLocalSpans
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.SpanInt

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f g : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (f + g) = C.rd a f + C.rd a g := by
  simp only [Cover.rd, map_add (f := _), smul_add]

theorem rd_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (x : C.d.c₂.F) (f : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (x • f) = C.σ₂ x • C.rd a f := by
  simp only [Cover.rd, LinearMap.map_smulₛₗ, map_smul]
  exact smul_comm _ _ _

theorem rd_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : C.rd a 0 = 0 := by
  simp only [Cover.rd, map_zero, smul_zero]

theorem vAdd_nonneg {k : Type} [Field k] [NumberField k] (la : HeightOneSpectrum (𝓞 k)) {x : k} (hx0 : x ≠ 0)
    (hx : la.valuation k x ≤ 1) : 0 ≤ vAdd la x := by
  unfold vAdd
  have h2 : (la.valuation k) x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr hx
  rw [WithZero.log_one] at h3
  omega

theorem cuspSec_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {f g : Rul C.d.Xo₂ C.d.c₂}
    (hf : f ∈ C.cuspSec a n) (hg : g ∈ C.cuspSec a n) : f + g ∈ C.cuspSec a n :=
  ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2 hg.2⟩

theorem cuspSec_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {f : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ C.cuspSec a n) : x • f ∈ C.cuspSec a n :=
  ⟨Submodule.smul_mem _ x hf.1, by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩

theorem cuspSec_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (0 : Rul C.d.Xo₂ C.d.c₂) ∈ C.cuspSec a n :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem exists_of_mem_span_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ Submodule.span C.σ₂.range (C.ratForms a n)) :
    ∃ f ∈ C.cuspSec a n, C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, cuspSec_zero C a n, rd_zero C a⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg, rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨s, y, rfl⟩ := s
    exact ⟨y • f, cuspSec_smul C a n y hf, by rw [rd_smul]; rfl⟩

theorem exists_of_mem_span_intForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) {φ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms a n {la})) :
    ∃ f ∈ C.cuspSec a n, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f) ∧ C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, ⟨hf, hv⟩, rfl⟩ := hx
    exact ⟨f, hf, hv la rfl, rfl⟩
  | zero =>
    refine ⟨0, cuspSec_zero C a n, fun v hv => ?_, rd_zero C a⟩
    rw [(isVal_valSet la v hv).zero]
    exact le_top
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨g, hg, hvg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg,
      fun v hv => (le_min (hvf v hv) (hvg v hv)).trans ((isVal_valSet la v hv).add _ _), rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨s, y, hy, rfl⟩ := s
    refine ⟨y • f, cuspSec_smul C a n y hf, fun v hv => ?_, by rw [rd_smul]; rfl⟩
    by_cases h0 : y = 0
    · rw [h0, zero_smul, (isVal_valSet la v hv).zero]
      exact le_top
    · rw [(isVal_valSet la v hv).smul y f h0]
      exact add_nonneg (by exact_mod_cast vAdd_nonneg la h0 hy) (hvf v hv)

theorem eq_of_rd_eq (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : Formalism.L2.Pj.InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif) (hcc : CUnit C.cc₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ha : Dom a n) {f g : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ sec C.d.Xo₂ C.d.c₂ a n) (hg : g ∈ sec C.d.Xo₂ C.d.c₂ a n)
    (h : C.rd a f = C.rd a g) : f = g := by
  by_contra hne
  have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f - g) :=
    LinearIndependent.of_subsingleton 0 (sub_ne_zero.2 hne)
  have h2 := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hT j hj σ hσ C hC hcc a n ha 1 (fun _ => f - g)
    (fun _ => sub_mem hf hg) hli
  have h3 : C.rd a (f - g) = 0 := by
    have e := rd_add C a (f - g) g
    rw [sub_add_cancel, h] at e
    calc C.rd a (f - g) = (C.rd a (f - g) + C.rd a g) - C.rd a g := by abel
      _ = 0 := by rw [← e, sub_self]
  exact h2.ne_zero 0 h3

theorem mem_intForms_of_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  intro D T hT j hj σ hσ C hC hcc wa n hn S φ hφ hS
  obtain ⟨f, hf, rfl⟩ := exists_of_mem_span_ratForms C wa n hφ
  refine ⟨f, ⟨hf, fun la hla => ?_⟩, rfl⟩
  obtain ⟨g, hg, hvg, hfg⟩ := exists_of_mem_span_intForms C wa n la (hS la hla)
  rw [eq_of_rd_eq D T hT j hj σ hσ C hC hcc wa n hn hf.1 hg.1 hfg.symm]
  exact hvg

end GlobalTheory.LevelSeries.SpanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdVal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem xiR_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (t : T0) (PP : Pl D.host.E) (hP : PP ∈ R.Q t) (u : (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ((R.xiR t PP u : ℂˣ) : ℂ) = ((R.xi t s : Circle) : ℂ) := by
  obtain ⟨a, k, hk, hx⟩ := GlobalTheory.ConjRes.exists_lift PP u
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 PP
  refine ⟨Formalism.L2.JoinChr.locU he.1 k, ?_⟩
  rw [hC.lev.xiR t PP hP a k u hk hx, (hC.lev.xi t).2 PP e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)]

theorem prod_val {D : D7} (ξ : (AE D)ˣ →* Circle) (S : Finset (Pl D.host.E)) (v : Pl D.host.E → ℂ)
    (hv : ∀ PP ∈ S, ∃ s : (AE D)ˣ, v PP = ((ξ s : Circle) : ℂ)) :
    ∃ s : (AE D)ˣ, ∏ PP ∈ S, v PP = ((ξ s : Circle) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨s0, h0⟩ := hv a (Finset.mem_insert_self a S)
    obtain ⟨s1, h1⟩ := ih fun PP hP => hv PP (Finset.mem_insert_of_mem hP)
    refine ⟨s0 * s1, ?_⟩
    rw [Finset.prod_insert ha, h0, h1, map_mul, Circle.coe_mul]

end GlobalTheory.FlatConj
end

