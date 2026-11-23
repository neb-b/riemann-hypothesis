module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactData
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.TwoOrbit

theorem exists_equivariant_extension :
    ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  intro G _ W₁ _ _ Q P x σ φ C K h1 h2
  classical
  let Ω : G → Prop := fun g =>
    ∃ (q : Q) (c : P), c ∈ C ∧ ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ
  have wd : ∀ (q q' : Q) (c c' : P), c ∈ C → c' ∈ C → ∀ κ ∈ K, ∀ κ' ∈ K,
      (q : G) * x * (c : G) * κ = (q' : G) * x * (c' : G) * κ' →
        σ q (φ c) = σ q' (φ c') := by
    intro q q' c c' hc hc' κ hκ κ' hκ' e
    have e' : ((q'⁻¹ * q : Q) : G) * x * (c : G) * (κ * κ'⁻¹) = x * (c' : G) := by
      have e2 : (q : G) * x * (c : G) * κ * κ'⁻¹ = (q' : G) * x * (c' : G) := by
        rw [e]; group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((q' : G)⁻¹ * q) * x * c * (κ * κ'⁻¹)
          = (q' : G)⁻¹ * ((q : G) * x * (c : G) * κ * κ'⁻¹) := by group
        _ = x * (c' : G) := by rw [e2]; group
    have e3 := h1 c hc (κ * κ'⁻¹) (K.mul_mem hκ (K.inv_mem hκ')) (q'⁻¹ * q) c' e'
    rw [e3, ← Module.End.mul_apply, ← map_mul]
    simp
  let f : G → W₁ := fun g =>
    if h : Ω g then σ h.choose (φ h.choose_spec.choose) else 0
  have hf : ∀ (q : Q) (c : P), c ∈ C → ∀ κ ∈ K,
      f ((q : G) * x * (c : G) * κ) = σ q (φ c) := by
    intro q c hc κ hκ
    have h : Ω ((q : G) * x * (c : G) * κ) := ⟨q, c, hc, κ, hκ, rfl⟩
    simp only [f]
    rw [dite_eq_left h]
    obtain ⟨hc', κ', hκ', e⟩ := h.choose_spec.choose_spec
    exact wd _ _ _ _ hc' hc κ' hκ' κ hκ e.symm
  have h0 : ∀ g, ¬ Ω g → f g = 0 := fun g h => dif_neg h
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro q g
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ, hκ, rfl⟩ := h
      have e : (q : G) * ((q₁ : G) * x * (c : G) * κ)
          = ((q * q₁ : Q) : G) * x * (c : G) * κ := by
        simp only [Subgroup.coe_mul]; group
      rw [e, hf _ _ hc _ hκ, hf _ _ hc _ hκ, map_mul, Module.End.mul_apply]
    · have h' : ¬ Ω ((q : G) * g) := by
        rintro ⟨q₁, c, hc, κ, hκ, e⟩
        refine h ⟨q⁻¹ * q₁, c, hc, κ, hκ, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (q : G)⁻¹ * ((q : G) * g) := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h', map_zero]
  · intro g κ hκ
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ₁, hκ₁, rfl⟩ := h
      have e : (q₁ : G) * x * (c : G) * κ₁ * κ = (q₁ : G) * x * (c : G) * (κ₁ * κ) := by group
      rw [e, hf _ _ hc _ (K.mul_mem hκ₁ hκ), hf _ _ hc _ hκ₁]
    · have h' : ¬ Ω (g * κ) := by
        rintro ⟨q₁, c, hc, κ₁, hκ₁, e⟩
        refine h ⟨q₁, c, hc, κ₁ * κ⁻¹, K.mul_mem hκ₁ (K.inv_mem hκ), ?_⟩
        calc g = (g * κ) * κ⁻¹ := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h']
  · intro p
    by_cases h : Ω (x * (p : G))
    · obtain ⟨q, c, hc, κ, hκ, e⟩ := h
      rw [e, hf _ _ hc _ hκ]
      exact (h1 c hc κ hκ q p e.symm).symm
    · rw [h0 _ h]
      by_contra hne
      obtain ⟨c, hc, q, e⟩ := h2 p (fun hz => hne hz.symm)
      exact h ⟨q, c, hc, 1, K.one_mem, by rw [e, mul_one]⟩
  · intro g hg
    by_contra hcon
    refine hg (h0 g ?_)
    rintro ⟨q, c, hc, κ, hκ, e⟩
    exact hcon ⟨q, c, hc, κ, hκ, e⟩

end GlobalTheory.CompanionTheory.BZRes.TwoOrbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeries
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp.PsBridge

section SlopeTestRemainingChoices

open ValuativeRel Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_uniformizerUnit :
    valuation k ((uniformizerUnit k : kˣ) : k) = ValuativeRel.uniformizer k := by
  apply le_antisymm
  · exact le_uniformizer_iff.2 (GLnLocal.valuation_uniformizer_lt_one k)
  · obtain ⟨ϖ, hϖ⟩ := valuation_surjective (ValuativeRel.uniformizer k)
    have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
    let y : 𝒪[k] := ⟨ϖ, hlt.le⟩
    have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 := by
      rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact hlt.ne
    have h := (GLnLocal.mem_maximalIdeal_pow_iff k).1 hy
    rw [pow_one] at h
    rw [← hϖ]
    exact h

theorem ord_zpow' (x : kˣ) (m : ℤ) : ord k (x ^ m) = m * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x m
  have h2 : ord k (x ^ m) = m • ord k x := congrArg Multiplicative.toAdd h
  simpa using h2

variable {n : ℕ}

def diagUnit (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) : kˣ :=
  Units.mk0 (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i)
    (apply_self_ne_zero_of_mem_borel k n p.2 i)

def toParab (p : blockUpper k n (id : Fin n → Fin n)) : parab k (points (Fin n)) :=
  ⟨p.1, fun _ _ h => p.2 h⟩

theorem det_leviProj (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p) i) = diagUnit p i := by
  ext
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  rfl

theorem deltaHalf_eq (p : blockUpper k n (id : Fin n → Fin n)) :
    (deltaHalf k (fun _ : Fin n => Unit) (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) : ℂ) =
      GroundTheory.Automorphic.Parabolic.sqrtModular k n id p := by
  rw [val_deltaHalf]
  change _ = ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ)
  congr 1
  rw [Real.coe_sqrt]
  congr 1
  rw [Measures.modularCharacter_borel, GlobalTheory.SmGL.modulus]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviProj, modExp_fin _ (fun _ => by simp)]
  have h := Measures.modulus_units (diagUnit p i)
  have h2 : Measures.modulus (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) =
      MeasureTheory.distribHaarChar k (diagUnit p i) := h
  rw [h2]
  rfl

theorem paramChar_leviProj (α : Fin n → ℂˣ) (p : blockUpper k n (id : Fin n → Fin n)) :
    paramChar k α (GroundTheory.Automorphic.Parabolic.leviProj k n id p) = ∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ) := by
  set l : Fin n → ℤ := fun i => ord k (diagUnit p i) with hl
  let e : Fin n → kˣ := fun i => diagUnit p i * uniformizerUnit k ^ (-l i)
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => ord_eq_zero_iff.1 (by
    have h1 : ord k (uniformizerUnit k) = 1 := ord_eq_one valuation_uniformizerUnit
    have h2 : ord k (e i) = l i + ord k ((uniformizerUnit k) ^ (-l i)) := ord_mul k _ _
    rw [h2, ord_zpow', h1]
    ring)
  let u : GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n) := ⟨diagGL k n e, GroundTheory.Automorphic.Parabolic.diagGL_mem_levi e⟩
  have hdec : GroundTheory.Automorphic.Parabolic.leviProj k n id p = torusLevi k n l * u := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change ((GroundTheory.Automorphic.Parabolic.leviProj k n id p :
        GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n)) : GL (Fin n) k) i j =
      ((torusPow k n l : Matrix (Fin n) (Fin n) k) * (diagGL k n e : Matrix (Fin n) (Fin n) k)) i j
    rw [GroundTheory.Automorphic.Parabolic.leviProj_apply, coe_torusPow, coe_diagGL, diagonal_mul_diagonal,
      diagonal_apply]
    by_cases h : i = j
    · subst h
      have hϖ : (GLnLocal.uniformizer k : k) ≠ 0 := (uniformizerUnit k).ne_zero
      have he' : ((e i : kˣ) : k) = ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i *
          (GLnLocal.uniformizer k : k) ^ (-l i) := by
        simp only [e, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]
        rfl
      rw [if_pos rfl, if_pos rfl, he', mul_left_comm, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero,
        mul_one]
    · simp [h]
  have hu : (u : GL (Fin n) k) ∈ GLnLocal.integralGL k n := by
    have key : ∀ d : Fin n → kˣ, (∀ i, valuation k (d i : k) = 1) →
        ∀ i j, (diagGL k n d : GL (Fin n) k) i j ∈ 𝒪[k] := by
      intro d hd i j
      change (diagGL k n d : Matrix (Fin n) (Fin n) k) i j ∈ _
      rw [coe_diagGL, diagonal_apply]
      split_ifs
      · exact (hd i).le
      · exact (𝒪[k]).zero_mem
    rw [GLnLocal.mem_integralGL_iff]
    refine ⟨key e he, ?_⟩
    change ∀ i j, ((diagGL k n e)⁻¹ : GL (Fin n) k) i j ∈ 𝒪[k]
    rw [← map_inv]
    exact key _ fun i => by simp [he i]
  rw [hdec, map_mul, paramChar_torusLevi, isUnramified_paramChar α u hu, mul_one,
    monomialChar_apply]

theorem exists_open_fix {G V : Type} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (v : V) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ x ∈ K, ρ x v = v :=
  ⟨stabilizerOf ρ v, hρ v, fun _ h => mem_stabilizerOf.1 h⟩

end SlopeTestRemainingChoices

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem char_apply (α : Fin n → ℂˣ) (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (z : ℂ) :
    ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)
        (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) z =
      (∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ)) * z := by
  have h1 : ∀ i, ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) i =
      diagUnit p i := det_leviProj p
  change GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))
    ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) z = _
  rw [GlobalTheory.SmGL.ofChar_apply, torusChar_apply, Units.coe_prod]
  simp only [h1, unrChar_apply]

theorem addChar_theta_law_rearrangement_identity (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom))
    (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (g : GL (Fin n) k) :
    f.1.1 ((p : GL (Fin n) k) * g) = borelChar (paramChar k α) p * f.1.1 g := by
  have h := parInd_law (points (Fin n)) _ f (toParab p) g
  have h2 : f.1.1 ((p : GL (Fin n) k) * g) = _ := h
  rw [h2, borelChar_apply, paramChar_leviProj, ← deltaHalf_eq, smul_eq_mul, char_apply, mul_assoc]

theorem induced_vector_smooth_open_subgroup (ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ)
    (f : IndSp (points (Fin n)) ρ) :
    ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧
      ∀ x ∈ K, ∀ g, f.1.1 (g * x) = f.1.1 g := by
  obtain ⟨K, hK, hKf⟩ := exists_open_fix _ (isSmooth_parInd (points (Fin n)) ρ) f
  refine ⟨K, hK, fun x hx g => ?_⟩
  have h := congrArg (fun v : IndSp (points (Fin n)) ρ => v.1.1 g) (hKf x hx)
  exact (parInd_apply (points (Fin n)) ρ x g f).symm.trans h
end

theorem indSp_mem_principalSeriesSpace : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  intro k _ _ _ _ n α f
  rw [mem_principalSeriesSpace]
  exact ⟨fun p g => addChar_theta_law_rearrangement_identity α f p g, induced_vector_smooth_open_subgroup _ f⟩

end GlobalTheory.CompanionTheory.SphSupp.PsBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.JoinInfProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infOf (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Multiset ℂ :=
  if h : ∃ m, HasInfCharGL x.2 τ m then h.choose else 0

theorem infOf_eq {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} (h0 : x.2 ≠ ⊥) {m : Multiset ℂ}
    (h : HasInfCharGL x.2 τ m) : infOf τ x = m := by
  have hex : ∃ m, HasInfCharGL x.2 τ m := ⟨m, h⟩
  unfold infOf
  rw [dite_eq_left hex]
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 hex.choose_spec h

theorem sum_m {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : ∑ i, P.m i τ = ((parts P).map (infOf τ)).sum := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (infOf_eq (P.discrete i).ne_bot (P.inf i τ)).symm

theorem infOf_twPart {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) (i : Fin P.c) :
    infOf τ (twPart χ ⟨P.N i, P.V i⟩) = (P.m i τ).map (· + expo χ τ) := by
  have hne : Submodule.map ((GlobalTheory.CuspRep.mulChi (P.N i) χ : Sm E (P.N i) ≃ₗ[ℂ] Sm E (P.N i)) :
      Sm E (P.N i) →ₗ[ℂ] Sm E (P.N i)) (P.V i) ≠ ⊥ := by
    intro hb
    exact (P.discrete i).ne_bot (Submodule.map_eq_bot_iff.1 hb)
  exact infOf_eq hne (GlobalTheory.BCT.TwistDisc.hasInfCharGL_map (P.inf i τ) χ)

theorem sum_tw {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) :
    (((parts P).map (twPart χ)).map (infOf τ)).sum = (∑ i, P.m i τ).map (· + expo χ τ) := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  have hmap : ∀ s : Finset (Fin P.c), (∑ i ∈ s, P.m i τ).map (· + expo χ τ) =
      ∑ i ∈ s, (P.m i τ).map (· + expo χ τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add (f := _), ih]
  rw [hmap Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact infOf_twPart P χ τ i

end GlobalTheory.CompanionTheory.JoinInfProof

theorem GlobalTheory.CompanionTheory.JoinInfProof.joinInf : PositivityTheory.Rg.BcB.F.RS.JoinInf := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D hJ τ
  rw [sum_m D τ, hJ, List.map_append, List.sum_append, sum_tw Pa χ₁ τ, sum_tw Pb χ₂ τ]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

def IsInt {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r s : Type}
    (M : Matrix r s (w.adicCompletion E)) : Prop :=
  ∀ i j, M i j ∈ Ov E w

def coef (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  (c : ℂ) ^ (i * b + j * a) * (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j)

def pairs (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal k).filter fun p => p.1 ≤ a ∧ p.2 ≤ b

theorem mem_pairs {a b k : ℕ} {p : ℕ × ℕ} : p ∈ pairs a b k ↔ p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [pairs, Finset.mem_filter]

theorem IsInt.add {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M N : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M + N) :=
  fun i j => (Ov E w).add_mem (hM i j) (hN i j)

theorem IsInt.neg {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) : IsInt w (-M) :=
  fun i j => (Ov E w).neg_mem (hM i j)

theorem isInt_zero {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r s : Type) :
    IsInt w (0 : Matrix r s (w.adicCompletion E)) :=
  fun _ _ => (Ov E w).zero_mem

def intSub {E : Type} [Field E] [NumberField E] (a b : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w X}
  zero_mem' := isInt_zero w _ _
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg

def latM {E : Type} [Field E] [NumberField E] {a b : ℕ} {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E)
    (m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val))}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using isInt_zero w _ _
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_add]; exact h1.add h3
    · rw [Matrix.add_mul, smul_add]; exact h2.add h4
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_neg]; exact h1.neg
    · rw [Matrix.neg_mul, smul_neg]; exact h2.neg

def latD {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E) (a b i j : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {W | ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w}
  zero_mem' := by
    intro r s
    simp only [Matrix.zero_apply, mul_zero, ite_self]
    exact (Ov E w).zero_mem
  add_mem' := by
    intro X Y h1 h2 r s
    have e1 := h1 r s
    have e2 := h2 r s
    simp only [Matrix.add_apply]
    split_ifs at e1 e2 ⊢
    · rw [mul_add]; exact (Ov E w).add_mem e1 e2
    · exact (Ov E w).add_mem e1 e2
  neg_mem' := by
    intro X h1 r s
    have e1 := h1 r s
    simp only [Matrix.neg_apply]
    split_ifs at e1 ⊢
    · rw [mul_neg]; exact (Ov E w).neg_mem e1
    · exact (Ov E w).neg_mem e1

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem wGL_conj_apply (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * g * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e1 : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  have e2 : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2]
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (x : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) x) = ePG i t x := by
  simp [wPerm]

theorem mem_HPG_iff_conj_mem_parab (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)) :
    p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  show (p : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t) ↔ _
  rw [mem_parab_iff, mem_parab_iff]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun x => forall_congr' fun y => ?_
  rw [wGL_conj_apply, wPerm_two, wPerm_two]

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.MirClosed

theorem isClosed_mirabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
      IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  intro k _ _ _ _ n
  haveI : T2Space k := GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField (k := k)
  have e : (Mir k n : Set (GL (Fin (n + 1)) k)) =
      ⋂ j : Fin (n + 1), {g : GL (Fin (n + 1)) k |
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = eLast k n j} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rw [mem_Mir_iff k g]
    exact funext_iff
  rw [e]
  have hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val
  refine isClosed_iInter fun j => ?_
  exact isClosed_eq ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval))
    continuous_const

end GlobalTheory.CompanionTheory.BZRes.MirClosed
end

