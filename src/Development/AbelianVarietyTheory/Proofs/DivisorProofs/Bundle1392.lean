module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFixedInvariantOpenCompactCompactSuppor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Filter Topology

theorem fixSupp_exists_box {κ X : Type} [Fintype κ] [TopologicalSpace X] {S : Set (κ → X)} {x0 : X}
    (hS : S ∈ 𝓝 (fun _ : κ => x0)) : ∃ O ∈ 𝓝 x0, ∀ u : κ → X, (∀ i, u i ∈ O) → u ∈ S := by
  rw [nhds_pi, Filter.mem_pi] at hS
  obtain ⟨I, -, t, ht, hsub⟩ := hS
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i⟩

variable {F : Type} [Field F] [NumberField F]

theorem fixSupp_finE_zero {κ : Type} : finE F (0 : κ → FiniteAdeleRing (𝓞 F) F) = 0 := by
  funext i; rfl

theorem fixSupp_finE_single {κ : Type} [DecidableEq κ] (j : κ) (t : FiniteAdeleRing (𝓞 F) F) :
    finE F (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) = Pi.single j (pairA F 0 t) := by
  funext i
  by_cases hij : i = j
  · subst hij
    show pairA F 0 ((Pi.single i t : κ → FiniteAdeleRing (𝓞 F) F) i) = (Pi.single i (pairA F 0 t) : κ → AdeleRing (𝓞 F) F) i
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · simp only [finE, Pi.single_eq_of_ne hij]; rfl

theorem fixed_schroedinger_invariant_compactSupport_bounded_annihilator (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hann : ∀ O ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x : FiniteAdeleRing (𝓞 F) F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K)
    (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  classical
  have hc1 : Continuous fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    continuous_id.prodMk continuous_const
  have hc2 : Continuous fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v) :=
    continuous_const.prodMk continuous_id
  have hM1 : (fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F))) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc1).mem_nhds M.zero_mem
  have hM2 : (fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v)) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc2).mem_nhds M.zero_mem
  obtain ⟨O₁, hO₁, hbox₁⟩ := fixSupp_exists_box hM1
  obtain ⟨O₂, hO₂, hbox₂⟩ := fixSupp_exists_box hM2
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O₁ hO₁
  obtain ⟨K₀, hK₀, hK₀mem⟩ := hann O₂ hO₂
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, Set.univ.pi fun _ => K₀, ?_, ?_, isCompact_univ_pi fun _ => hK₀, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro x u hu
    have hu1 : ∀ i, u i ∈ O₁ := by
      intro i
      have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
      have := hNO (c * u i) hi
      rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this
    have hm : (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M := hbox₁ u hu1
    have := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul] at this
    exact this
  · intro x hx
    by_contra hne
    apply hx
    intro j _
    apply hK₀mem
    intro t ht
    have hv : ∀ i, (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) i ∈ O₂ := by
      intro i
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact ht
      · rw [Pi.single_eq_of_ne hij]; exact mem_of_mem_nhds hO₂
    have hm : ((0 : κ → FiniteAdeleRing (𝓞 F) F), (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M :=
      hbox₂ _ hv
    have h1 := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, zero_dotProduct, mul_zero, add_zero] at h1
    rw [fixSupp_finE_single, dotProduct_single] at h1
    have hdot : x j * pairA F 0 t = pairA F 0 (t * (x j).2) :=
      Prod.ext (by show (x j).1 * 0 = 0; exact mul_zero _) (by show (x j).2 * t = t * (x j).2; exact mul_comm _ _)
    rw [hdot] at h1
    exact mul_right_cancel₀ hne (h1.trans (one_mul _).symm)

theorem fixed_invariant_compactSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  intro D ψ hψ κ _ M hM
  exact fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ (GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ) κ M hM

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_map_eq_H {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ * H.map τ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem gramOn_det_totallyPositive_of_posDef {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E)
    (hH : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q)
    (V : Submodule E (Fin n → E)) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det ≠ 0 ∧
      ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det = r := by
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det := by
    intro τ
    obtain ⟨Q, hQ, hHQ⟩ := hH τ
    rw [RingHom.map_det]
    have e1 : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ := rfl
    have e2 : cT (starRingEnd ℂ) Q = Qᴴ := by
      ext i j; simp [cT, Matrix.conjTranspose_apply]
    set A : Matrix (Fin n) (Fin (Module.finrank E V)) ℂ :=
      Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) with hA
    have e3 : Aᴴ * (Qᴴ * Q) * A = (Q * A)ᴴ * (Q * A) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, gramOn_map_eq_H, ← hA, hHQ, e2, e3]
    have hQi : Function.Injective Q.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hQ
    have hinj : Function.Injective (Q * A).mulVec := by
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact gramOn_basis_mulVec_injective V τ (hQi hvw)
    exact (Matrix.PosDef.conjTranspose_mul_self _ hinj).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

theorem refSign_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  intro E _ _ _ hU S hS n γ₀ _ H₀ _ _ _ hpos P₁ _ _
  obtain ⟨hd0, hdpos⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine Eq.trans ?_ (_root_.GlobalTheory.UnitaryClasses.signProd_totPos E hU S hS _ hd0 hdpos)
  apply finprod_mem_congr rfl
  intro w _
  split_ifs with hw
  · rfl
  · unfold sgnOn
    rw [aeval_map_mat]
    exact _root_.GlobalTheory.UnitaryClasses.BaseChangeSign.main E hU w hw n H₀ (aeval γ₀.val P₁)

end GlobalTheory.UnitaryClasses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalForm
section
open Matrix

namespace GlobalTheory.SimNormal

theorem diagonal_comm_of_comm {n : ℕ} {d f : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (h : diagonal d * g = g * diagonal d) (hf : ∀ i j, d i = d j → f i = f j) :
    diagonal f * g = g * diagonal f := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [diagonal_mul, mul_diagonal] at e ⊢
  by_cases hg : g i j = 0
  · simp [hg]
  · have : d i = d j := mul_right_cancel₀ hg (e.trans (mul_comm _ _))
    rw [hf i j this, mul_comm]

theorem simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  intro n J P hJ hJd hP hpos
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.ThK.SqIntMaxCpt.exists_congr_one hP hpos
  set M := Q₀.1ᴴ * J * Q₀.1 with hMdef
  have hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul _ hJ
  set U : Matrix (Fin n) (Fin n) ℂ := hM.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.2
  set d : Fin n → ℝ := hM.eigenvalues with hd
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (d i : ℂ) with hD
  have h3 : Uᴴ * M * U = D := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have hdne : ∀ i, d i ≠ 0 := by
    have hUd : Uᴴ.det * U.det = 1 := by rw [← det_mul, h1, det_one]
    have hQd : Q₀.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
    have hDd : D.det ≠ 0 := by
      rw [← h3, hMdef, det_mul, det_mul, det_mul, det_mul]
      have hU1 : Uᴴ.det ≠ 0 := left_ne_zero_of_mul_eq_one hUd
      have hU2 : U.det ≠ 0 := right_ne_zero_of_mul_eq_one hUd
      have hQ2 : Q₀.1ᴴ.det ≠ 0 := by rw [det_conjTranspose]; simpa using hQd
      simp only [ne_eq, mul_eq_zero, not_or]; tauto
    intro i hi
    apply hDd
    rw [hD, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hMU : U * D * Uᴴ = M := by
    rw [← h3]; simp only [← Matrix.mul_assoc, h1', Matrix.one_mul]; rw [Matrix.mul_assoc, h1', Matrix.mul_one]
  set s : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hs
  have hsq : ∀ i, 0 < Real.sqrt |d i| := fun i => Real.sqrt_pos.2 (abs_pos.2 (hdne i))
  let S : GL (Fin n) ℂ := ⟨diagonal fun i => (s i : ℂ), diagonal fun i => (Real.sqrt |d i| : ℂ), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact inv_mul_cancel₀ (by exact_mod_cast (hsq i).ne'), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast (hsq i).ne')⟩
  let Ug : GL (Fin n) ℂ := ⟨U, Uᴴ, h1', h1⟩
  refine ⟨fun i => decide (0 < d i), Q₀ * Ug * S, ?_, fun g hgP hgJ => ?_⟩
  · have hSh : (S.1)ᴴ = S.1 := by
      show (diagonal fun i => (s i : ℂ))ᴴ = _
      rw [diagonal_conjTranspose]; congr 1; funext i; simp
    have : (Q₀ * Ug * S).1ᴴ * J * (Q₀ * Ug * S).1 = S.1 * (Uᴴ * M * U) * S.1 := by
      simp only [Units.val_mul, conjTranspose_mul, hSh, Matrix.mul_assoc, hMdef]; rfl
    rw [this, h3]
    show diagonal _ * diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    have hsi : s i * s i = |d i|⁻¹ := by
      simp only [hs]; rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
    have : (s i : ℂ) * d i * s i = ((d i * (s i * s i) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsi]
    rcases lt_or_gt_of_ne (hdne i) with h | h
    · simp [h, not_lt.2 h.le, abs_of_neg h, (hdne i)]
    · simp [h, abs_of_pos h, (hdne i)]
  · have hi : (Q₀⁻¹).1ᴴ * Q₀.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have hPi : (Q₀⁻¹).1ᴴ * (Q₀⁻¹).1 = P := by
      have := congrArg (fun A => (Q₀⁻¹).1ᴴ * A * (Q₀⁻¹).1) hQ₀
      simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this.symm
    have hJi : (Q₀⁻¹).1ᴴ * M * (Q₀⁻¹).1 = J := by
      rw [hMdef]
      simp only [← Matrix.mul_assoc, hi, Matrix.one_mul, Units.mul_inv_cancel_right]
    set g' := Uᴴ * (Q₀⁻¹).1 * g * Q₀.1 * U with hg'
    have hg'1 : g'ᴴ * g' = 1 := by
      calc g'ᴴ * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * P * Q₀.1) * U := by
            rw [h1', Matrix.mul_one, hPi, hgP]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ₀, Matrix.mul_one, h1]
    have hg'D : g'ᴴ * D * g' = D := by
      calc g'ᴴ * D * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * D * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * J * Q₀.1) * U := by
            rw [hMU, hJi, hgJ]; simp only [Matrix.mul_assoc]
        _ = D := by rw [← hMdef, h3]
    have hg'2 : g' * g'ᴴ = 1 := mul_eq_one_comm.1 hg'1
    have hcomm : D * g' = g' * D := by
      calc D * g' = g' * g'ᴴ * D * g' := by rw [hg'2, Matrix.one_mul]
        _ = g' * (g'ᴴ * D * g') := by simp only [Matrix.mul_assoc]
        _ = g' * D := by rw [hg'D]
    have hQinv : ((Q₀ * Ug * S)⁻¹).1 * g * (Q₀ * Ug * S).1 = (S⁻¹).1 * g' * S.1 := by
      simp only [_root_.mul_inv_rev, Units.val_mul, hg', Matrix.mul_assoc]; rfl
    have hSc : (S⁻¹).1 * g' = g' * (S⁻¹).1 :=
      diagonal_comm_of_comm (f := fun i => (Real.sqrt |d i| : ℂ)) hcomm fun i j h => by
        have : d i = d j := by exact_mod_cast h
        simp [this]
    have hfin : (S⁻¹).1 * g' * S.1 = g' := by
      rw [hSc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hQinv, hfin]
    exact hg'1

end GlobalTheory.SimNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyGrowthTwist
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.NefRR.hdim_twist_twist_bound : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ M : LB X, M.IsLB → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twist F M) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL hE F _ hF M hM hFb i hi
  have := isNoetherian_of_isProjOver hp
  obtain ⟨_, _, hAmp⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, B, hA, hB, s, t, hs, ht, hc⟩ := hAmp.exists_sub_of_mono_cutHom F (cls M hM)
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' k X hp d L hL hE F hF B hB t ht hFb i hi
  have : Mono (cutHom F hA s) := hs
  have hcut : suppDim (cut F hA s) ≤ d := suppDim_cut_le F hA s hF
  have := isFiniteQC_cut F hA s
  have := isFiniteQC_twist (F := cut F hA s) hM
  obtain ⟨C₂, h₂⟩ := hE (twist (cut F hA s) M) (by rwa [suppDim_twist hM]) i hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hLm := isLB_lbPow hL m
  have hN := isLB_tens hM hLm
  have hBi := isLB_lbZPow hB (-1)
  have hN' := isLB_tens hBi hLm
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (tens M (lbPow L m)) (tens (lbZPow B (-1)) (lbPow L m)) hA hN hN' s hs
    (by
      change cls M hM + cls _ hLm = (cls _ hBi + cls _ hLm) + cls A hA
      rw [hc, cls_lbZPow hB]; abel)).1 i
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hM hLm hN rfl
  obtain ⟨e₂⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hLm hN' rfl
  obtain ⟨e₃⟩ := nonempty_twist_twist_iso_of_cls_eq (cut F hA s) hM hLm hN rfl
  rw [hdim_congr k i e₁]
  rw [← hdim_congr k i e₂, ← hdim_congr k i e₃] at key
  have h₁m := h₁ m
  have h₂m := h₂ m
  have hpow : d * (m + 1) ^ (d - 1) ≤ (d + 1) * (m + 1) ^ d :=
    Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  calc _ ≤ _ := key
    _ ≤ C₁ * ((d + 1) * (m + 1) ^ d) + C₂ * ((d + 1) * (m + 1) ^ d) :=
        Nat.add_le_add h₁m (h₂m.trans (Nat.mul_le_mul_left _ hpow))
    _ = _ := (Nat.add_mul _ _ _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePrope
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem main : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro S Z z hfin hflat hlfp r
  refine GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover S Z z hfin hflat hlfp r fun s => ?_
  obtain ⟨W, A, B, _, _, _, _, _, eW, eZ, hs, hc⟩ := _root_.GlobalTheory.FiniteFlatLocal.exists_finFree_local S Z z hfin hflat hlfp s
  refine ⟨W, hs, _root_.GlobalTheory.HilbertSch.isHilbRep_transfer (z ∣_ W) (Spec.map (CommRingCat.ofHom (algebraMap A B))) eW.symm eZ.symm ?_ r
    (GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists A B r)⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end GlobalTheory.HilbertSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.HolAtlas

theorem del_finset_sum {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ}
    (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) : A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [GlobalTheory.CxForm.HolAtlas.loc, hw, dif_pos]
      exact Finset.sum_apply _ _ _
    · simp [GlobalTheory.CxForm.HolAtlas.loc, hw]
  have hx : x.crd ∈ (A.e x.1.1).target := x.ch.map_source x.2
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt
      ((A.e x.1.1).open_target.mem_nhds hx)
  have key : ∀ S u, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
      ∑ j, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have e : (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j ∈ Finset.univ, (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w; rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.del_sum (fun j _ => hdiff j S), ContinuousLinearMap.sum_apply]
  rw [Finset.sum_apply]
  simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.delAt, GlobalTheory.CxForm.coefwise, key, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end GlobalTheory.CxForm.HolAtlas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDetStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  first | exact @GlobalTheory.JacSubst.integral_mulVec | exact GlobalTheory.JacSubst.integral_mulVec | (intros; apply GlobalTheory.JacSubst.integral_mulVec <;> assumption)
end

