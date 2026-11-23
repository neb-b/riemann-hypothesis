module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open MvPolynomial

theorem exists_weightedMonomialPlace : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z wt hN hm hz hw0 hw
  haveI := hN
  have hz0 : (z 0 : L) ≠ 0 := by
    intro h
    have h1 : z 0 = 0 := Subtype.ext h
    have := _root_.GlobalTheory.weightedRelation_coeff_mem_span z wt hw hz (wt 0) (X 0) (isWeightedHomogeneous_X Q wt 0)
      (by simp [h1]) (Finsupp.single 0 1)
    rw [coeff_X, if_pos rfl, hm] at this
    exact (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  set u : Fin r → L := fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ with hu
  have key0 : ∀ P : MvPolynomial (Fin r) Q, eval₂ Q.subtype u P = 0 →
      ∀ α, P.coeff α ∈ IsLocalRing.maximalIdeal Q := by
    intro P hP α
    obtain ⟨N, F, hF, hFe, hc⟩ := GlobalTheory.T.exists_weightedHomogeneous_homogenisation Q r z wt hw0 hz0 P
    obtain ⟨β, hβ⟩ := hc α
    rw [← hβ, ← hm]
    refine _root_.GlobalTheory.weightedRelation_coeff_mem_span z wt hw hz N F hF ?_ β
    apply Subtype.ext
    rw [hFe, hP, mul_zero]
    rfl
  set e : MvPolynomial (Fin r) Q →+* L := eval₂Hom Q.subtype u with he
  set A : Subring L := e.range with hA
  set eA : MvPolynomial (Fin r) Q →+* A := e.rangeRestrict with heA
  have heA_surj : Function.Surjective eA := e.rangeRestrict_surjective
  have heA_val : ∀ P, ((eA P : A) : L) = e P := fun P => rfl
  have hQA : ∀ q ∈ Q, q ∈ A := fun q hq => ⟨C ⟨q, hq⟩, by simp [he]⟩
  have huA : ∀ i, u i ∈ A := fun i => ⟨X i, by simp [he]⟩
  let t : A := ⟨z 0, hQA _ (z 0).2⟩
  have hzA : ∀ j, ∃ a : A, ((z j : Q) : L) = (z 0 : L) * a := by
    intro j
    refine Fin.cases ⟨1, by simp⟩ (fun i => ?_) j
    refine ⟨⟨(z 0 : L) ^ (wt i.succ - 1) * u i, A.mul_mem (A.pow_mem (hQA _ (z 0).2) _) (huA i)⟩, ?_⟩
    show ((z i.succ : Q) : L) = (z 0 : L) * ((z 0 : L) ^ (wt i.succ - 1) * ((z i.succ : L) / (z 0 : L) ^ wt i.succ))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hw i.succ), mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
  have hmA : Ideal.map (eA.comp C) (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {t} := by
    rw [Ideal.map_le_iff_le_comap, ← hm, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hzA j
    show eA (C (z j)) ∈ Ideal.span {t}
    rw [Ideal.mem_span_singleton']
    exact ⟨a, Subtype.ext (by rw [heA_val]; simp [he, ha, mul_comm, t])⟩
  have hspan : Ideal.span {t} = Ideal.map eA (Ideal.map C (IsLocalRing.maximalIdeal Q)) := by
    rw [Ideal.map_map]
    refine le_antisymm ?_ hmA
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : t = (eA.comp C) (z 0) := Subtype.ext (by rw [RingHom.comp_apply, heA_val]; simp [he, t])
    rw [SetLike.mem_coe, this]
    exact Ideal.mem_map_of_mem _ (by rw [← hm]; exact Ideal.subset_span ⟨0, rfl⟩)
  have hker : RingHom.ker eA ≤ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [MvPolynomial.mem_map_C_iff]
    refine key0 P ?_
    have := congrArg Subtype.val ((RingHom.mem_ker).mp hP)
    simpa [heA_val, he] using this
  have hprimeC : (Ideal.map (C : Q →+* MvPolynomial (Fin r) Q) (IsLocalRing.maximalIdeal Q)).IsPrime := by
    have := MvPolynomial.ker_map (σ := Fin r) (IsLocalRing.residue Q)
    rw [IsLocalRing.ker_residue] at this
    rw [← this]
    exact RingHom.ker_isPrime _
  have hprime : (Ideal.span {t}).IsPrime := by
    rw [hspan]
    exact Ideal.map_isPrime_of_surjective heA_surj hker
  have key1 : ∀ P : MvPolynomial (Fin r) Q, eA P ∈ Ideal.span {t} →
      P ∈ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [hspan] at hP
    obtain ⟨x, hx, hxP⟩ := (Ideal.mem_map_iff_of_surjective eA heA_surj).mp hP
    have : P - x ∈ RingHom.ker eA := by rw [RingHom.mem_ker, map_sub, hxP, sub_self]
    simpa using Ideal.add_mem _ (hker this) hx
  have hNA : IsNoetherianRing A := isNoetherianRing_of_surjective _ _ eA heA_surj
  have hfracA : ∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
    intro f
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hQ.frac f
    exact ⟨a, hQA a ha, b, hQA b hb, hb0, hab⟩
  obtain ⟨V, hAV, hdvr, hirr, hunit, hfrV, hess⟩ :=
    _root_.GlobalTheory.dvr_loc_principal_prime A t hNA hz0 hprime hfracA
  have hQAf : (Q.subtype.codRestrict A fun q => hQA _ q.2).FiniteType := by
    have h1 : (Q.subtype.codRestrict A fun q => hQA _ q.2) = eA.comp C := by
      ext q; simp [heA_val, he]
    rw [h1]
    exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance) heA_surj
  have hconst : ∀ a, c a ∈ V := fun a => hAV _ (hQA _ (hQ.const_mem a))
  have hessV : (c.codRestrict V hconst).EssFiniteType := by
    have h := (hQ.essFiniteType.comp hQAf.essFiniteType).comp hess
    exact h
  let P0 : Place c := ⟨V, hconst, hdvr, hessV⟩
  have hC : P0.Contains Q := fun f hf => hAV _ (hQA _ hf)
  let uV : Fin r → P0.ring := fun i => ⟨u i, hAV _ (huA i)⟩
  have hev : ∀ P : MvPolynomial (Fin r) Q,
      ((MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P : P0.ring) : L) =
        e P := by
    intro P
    exact MvPolynomial.eval₂_comp_left (P0.ring.subtype)
      (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P
  refine ⟨P0, hC, uV, fun i => ?_, ?_, fun q hq => ?_, fun P hP => ?_, fun f => ?_⟩
  · exact div_mul_cancel₀ _ (pow_ne_zero _ hz0)
  · exact hirr
  · obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton').mp (hmA (Ideal.mem_map_of_mem _ hq))
    have hmt : (⟨(t : L), hAV _ t.2⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit
    have : (⟨(q : L), hC _ q.2⟩ : P0.ring) = ⟨(a : L), hAV _ a.2⟩ * ⟨(t : L), hAV _ t.2⟩ :=
      Subtype.ext (by have := congrArg Subtype.val ha; simpa [heA_val, he] using this.symm)
    rw [this]
    exact Ideal.mul_mem_left _ _ hmt
  · have hs : eA P ∉ Ideal.span {t} := fun h => by
      obtain ⟨α, hα⟩ := hP
      exact hα ((MvPolynomial.mem_map_C_iff.mp (key1 P h)) α)
    have := hunit _ hs
    convert this using 1
    exact Subtype.ext (hev P)
  · obtain ⟨a, s, hs, hfs⟩ := hfrV f
    obtain ⟨P, rfl⟩ := heA_surj a
    obtain ⟨R, rfl⟩ := heA_surj s
    refine ⟨P, R, ?_, Subtype.ext ?_⟩
    · convert hunit _ hs using 1
      exact Subtype.ext (hev R)
    · calc ((f * MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV R : P0.ring) : L)
          = (f : L) * e R := by rw [← hev R]; rfl
        _ = e P := hfs
        _ = _ := (hev P).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.CoefExt

open GlobalTheory.HolDict.HolTo

section General

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {H : ι → Type}
  [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] {σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)} {v : ∀ τ, H τ}

omit [Fintype ι] in
theorem prod_single_apply (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n) (t : Fin k → ℝ) (ρ : ι) :
    (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ρ =
      (List.ofFn fun i => NormedSpace.exp (t i • (if ρ = τs i then Xs i else 0))).prod := by
  rw [Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  by_cases h : ρ = τs i
  · subst h
    simp
  · simp [h]

theorem smFn_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) :
    SmFn Hm fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG Hm _ (hX i) _
  refine contDiff_prod fun ρ _ => ?_
  simp only [Pi.mul_apply, (hσ ρ).2 _ (hu ρ) _ (hmem _ ρ), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply]
  have h1 := hv ρ k (fun i => if ρ = τs i then Xs i else 0) fun i => by
    split_ifs with h
    · subst h
      exact hX i
    · show _ = _
      simp
  exact (((innerSL ℂ (v ρ)).comp (σ ρ (u ρ))).restrictScalars ℝ).contDiff.comp h1

theorem hasDerivAt_of_smooth {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {L : Set (Mt n)}
    {π : Mt n → (K →L[ℂ] K)} {x : K} (hx : SmoothVec L π x) {X : Mt n} (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 := by
  have h1 := hx 1 (fun _ => X) fun _ => hX
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => (fun _ => r : Fin 1 → ℝ)) := by fun_prop
  have h3 := (h1.comp h2).differentiable (by simp)
  have h4 : Differentiable ℝ fun t : ℝ => π (NormedSpace.exp (t • X)) x := by
    have e : (fun t : ℝ => π (NormedSpace.exp (t • X)) x) = ((fun t : Fin 1 → ℝ =>
        π ((List.ofFn fun i => NormedSpace.exp (t i • X)).prod) x) ∘ fun r _ => r) := by
      funext r
      simp
    rw [e]
    exact h3
  exact (h4 0).hasDerivAt

theorem der_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) {u : ι → Mt n}
    (hu : u ∈ UG Hm) :
    der τ X (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRep (σ τ) X (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ∏ ρ, ⟪v ρ, σ ρ ((u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n)) ρ) (v ρ)⟫_ℂ) =
      fun t : ℝ => ⟪v τ, σ τ (u τ) (σ τ (NormedSpace.exp (t • X)) (v τ))⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Pi.mul_apply,
      (hσ τ).2 _ (hu τ) _ (single_mem_UG Hm τ hX t τ), Pi.mulSingle_eq_same]
    congr 1
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hρ), mul_one]
  rw [e]
  have h1 := (((innerSL ℂ (v τ)).comp (σ τ (u τ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth (hv τ) hX)
  exact (h1.mul_const _).deriv

theorem derC_coef {q : ι → ℕ} {x₀ : ι → Mt n} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) (Z : Mt n) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    derC Hm τ Z (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRepC (Hm τ) (σ τ) Z (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth (h τ)) (dets_ne (h τ)).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv τ hA hu, der_coef hσ hv τ hB hu, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
  ring

theorem killedFn_coef {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ))
    (hk : ∀ τ (a c : Fin n), a ≤ c → dRepC (Hm τ) (σ τ) (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) (v τ) =
      if a = c then (w τ a : ℂ) • v τ else 0) :
    KilledFn Hm x₀ w fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro τ a c hac u hu
  rw [derC_coef h hσ hv τ _ hu, hk τ a c hac]
  split_ifs
  · rw [map_smul, inner_smul_right, mul_assoc]
    beta_reduce
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  · simp

end General

theorem arr_bijective {n q : ℕ} (hq : q ≤ n) : Function.Bijective (arr (n := n) q) := by
  refine Finite.injective_iff_bijective.1 fun a b hab => ?_
  have h := congrArg Fin.val hab
  have := a.2
  have := b.2
  unfold arr at h
  apply Fin.ext
  split_ifs at h <;> simp only at h <;> omega

theorem diagonal_mem_Kset {n : ℕ} (ε : Fin n → Bool) (s : Fin n → ℝ) :
    diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    change Complex.exp ((s i : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((s i : ℂ) * Complex.I)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · unfold Formalism.REAL.Jm
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem torus_ext {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    {v : M.Vec} (hw : WtIs M w) (hv : IsExtVec M v) (s : D.what₂.Tau → Fin V.rank → ℝ) (τ : D.what₂.Tau)
    (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) =
      (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (x0Mat M) s τ * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep
  rw [h3, (hv τ).2.2 (fun a => s τ (e.symm a)) (diagonal_mem_Kset _ _)]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

end GlobalTheory.HolDict.CoefExt

namespace GlobalTheory.HolDict


open CoefExt in
theorem holFn_coef_extVec : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  intro D θ V S M w v hθ hM hw hv
  classical
  have ho : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hM).1
  have hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1.1
  have hk := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hw hv
  refine ⟨_root_.GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ ho _ (smFn_coef hσ fun τ => (hk τ).1)
    (killedFn_coef ho hσ (fun τ => (hk τ).1) fun τ => (hk τ).2), fun s τ => ?_⟩
  exact torus_ext M hw hv s τ (HolTo.dets_ne (ho τ)).2

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def eqvM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) : Submodule ℂ (G → V) where
  carrier := {φ | (∀ h x, φ (ι h * x) = ρ h (φ x)) ∧ ∀ k ∈ K, ∀ x, φ (x * k) = φ x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 h x, hb.1 h x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 h x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def stabCard (ι : H →* G) (K : Subgroup G) (x : G) : ℕ :=
  Nat.card (ι.range ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)

def secM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) : V →ₗ[ℂ] (G → V) where
  toFun v y := ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v
  map_add' a b := by
    funext y
    simp only [map_add (f := _), smul_add, Pi.add_apply]
  map_smul' c a := by
    funext y
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPtHom : UE E n →* finU (E := E) (n := n) where
  toFun := finPt
  map_one' := by
    apply Subtype.ext
    rw [FinPtLoc.finPt_eq]
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq]
    apply Subtype.ext
    exact (congrArg (finGL E n) (map_mul (ratF E n) a.1 b.1)).trans (map_mul _ _ _)

theorem finPtHom_apply (γ : UE E n) : finPtHom γ = finPt γ := rfl

theorem wAt_mul (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    GlobalTheory.BCT.TrKer.wAt lam (a * b) = GlobalTheory.BCT.TrKer.wAt lam a ∘ₗ GlobalTheory.BCT.TrKer.wAt lam b := by
  unfold GlobalTheory.BCT.TrKer.wAt
  rw [← PiTensorProduct.map_comp]
  refine congrArg PiTensorProduct.map (funext fun v => ?_)
  change GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding (a.1 * b.1)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]

theorem wAt_one (lam : InfinitePlace E → DomWeight n) : GlobalTheory.BCT.TrKer.wAt lam 1 = LinearMap.id := by
  unfold GlobalTheory.BCT.TrKer.wAt
  simp only [OneMemClass.coe_one, map_one]
  exact PiTensorProduct.map_id

def wDual (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UE E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam)) where
  toFun γ := (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹).dualMap
  map_one' := by
    rw [inv_one, wAt_one]
    rfl
  map_mul' a b := by
    rw [_root_.mul_inv_rev, wAt_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl

end GlobalTheory.BCT.TraceBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChart
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodTop

theorem gram_smooth_isUnit_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  intro F _ σ X m E O H hH e he y hyO hye A hA
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := hH.smooth y hyO A hA () a b
    have h1 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).re) (e y) := contDiffAt_holoChart he hye hre
    have h2 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).im) (e y) := contDiffAt_holoChart he hye him
    have h3 : ContDiffAt ℝ ∞ (fun v => ((H A (e.symm v) () a b).re : ℂ) + ((H A (e.symm v) () a b).im : ℂ) * Complex.I)
        (e y) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h2).mul contDiffAt_const)
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (Complex.re_add_im _).symm)
  · rw [e.left_inv hye]
    exact isUnit_iff_ne_zero.mpr (hH.posDef y hyO A hA ()).det_pos.ne'

end GlobalTheory.GoodTop
end
end

