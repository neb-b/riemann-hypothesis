module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AddCharHalfTraceTensorLatticeHeisenbergCocycle
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.VacCocycle
open _root_.GlobalTheory

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem sum_four_comm (f : α → β → α → β → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have h := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun (p q : α × β) => f p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type] using h

theorem conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) (x y : Matrix α β A) :
    c (GlobalTheory.WeilM.hTens c JA JB y x) = -GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, hA, hB, ← Finset.sum_neg_distrib]
  rw [sum_four_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem trace_conj (hc : ∀ z, c (c z) = z) (z : A) : Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

theorem symp_swap (hc : ∀ z, c (c z) = z) {JA : Matrix α α A} {JB : Matrix β β A}
    (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j) {ξ : A} (hξ : ξ + c ξ = 1)
    (x y : Matrix α β A) :
    GlobalTheory.WeilM.symp (R := R) c ξ JA JB y x =
      GlobalTheory.WeilM.symp (R := R) c ξ JA JB x y + GlobalTheory.WeilM.symp (R := R) c (-1) JA JB x y := by
  unfold GlobalTheory.WeilM.symp
  rw [← trace_conj c hc, map_mul, conj_hTens c hc hA hB, ← map_add (f := _)]
  congr 1
  linear_combination (-GlobalTheory.WeilM.hTens c JA JB x y) * hξ

end General

theorem psi_half_symp_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hsw := symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hX.herm])
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hY.skew, map_neg])
    (ξ := inclR (F := F) (AF F) (θ : E)) (by rw [hi, ← map_add (f := _), hθ, map_one]) γ γ'
  have h1 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have h2 := Tw.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have hm : inclR (F := F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by
    rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]
  rw [hm] at h2
  rw [Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw,
    ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  have h : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = t at h ⊢
  linear_combination (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') * h

end Tw.VacCocycle

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsSchwartzBruhatSchroedingerFixedLocalField
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrTestVec
open _root_.GlobalTheory

theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end Tw.SchrTestVec
end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.SchroedingerMemSchwartzBruhatFinitePlace
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrSBFin
open _root_.GlobalTheory

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_id.add continuous_const)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end Tw.SchrSBFin
end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.PsiNontriv
open _root_.GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := Tw.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [Tw.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end Tw.PsiNontriv
end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.LatParam
open _root_.GlobalTheory

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply,
    zsmul_eq_mul]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, Pi.intCast_apply]
  push_cast
  ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  classical
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  have memX : ∀ x, x ∈ X.L ↔ ∃ c : Fin kx → ℤ, ∑ i, c i • ex i = x := by
    intro x
    rw [← Submodule.restrictScalars_mem ℤ, ← hex, Submodule.mem_span_range_iff_exists_fun]
  have memY : ∀ y, y ∈ Y.L ↔ ∃ c : Fin ky → ℤ, ∑ j, c j • fy j = y := by
    intro y
    rw [← Submodule.restrictScalars_mem ℤ, ← hfy, Submodule.mem_span_range_iff_exists_fun]
  have exX : ∀ i, ex i ∈ X.L := by
    intro i
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := ex) i)
    rw [hex] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  have exY : ∀ j, fy j ∈ Y.L := by
    intro j
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := fy) j)
    rw [hfy] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), ?_⟩
  intro γ
  let φ : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toAddMonoidHom.mapMatrix
  have hφ : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = φ J := fun J => rfl
  have hsupp : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a →
      a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
      rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h2 := ha _ h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
    calc a = GlobalTheory.EmbChart.atPlace v 1 * a := h2
      _ = GlobalTheory.EmbChart.atPlace v (1 * GlobalTheory.AdelicU.evFin F v a) := GlobalTheory.EmbChart.atPlace_mul_right v 1 a
      _ = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by rw [one_mul]
  have hdef : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v = AddSubgroup.closure {z |
      ∃ a, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a ∧
        (GlobalTheory.AdelicU.evFin F v) a ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v ∧
          ∃ x ∈ X.L, ∃ y ∈ Y.L, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (Matrix.vecMulVec x y)} := rfl
  rw [hdef]
  constructor
  · intro hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (memX x).1 hx
      obtain ⟨c', rfl⟩ := (memY y).1 hy
      refine ⟨fun m => (c m.1 * c' m.2) • ⟨_, hav⟩, ?_⟩
      beta_reduce
      set_option synthInstance.maxHeartbeats 100000 in
        rw [vecMulVec_sum_zsmul, hφ, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_zsmul, smul_comm, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc, ← hsupp a ha, hφ]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [Finset.sum_add_distrib, add_smul]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp [neg_smul]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨GlobalTheory.EmbChart.atPlace v (a m), ?_, ?_, ex m.1, exX _, fy m.2, exY _, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [GlobalTheory.EmbChart.evFin_atPlace]
      exact (a m).2

end Tw.LatParam
end

