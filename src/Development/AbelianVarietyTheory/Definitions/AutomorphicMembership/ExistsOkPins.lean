module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TrueColsTest

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Normal

variable {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)

end Normal

variable {B : Base} {X : PreX B.toPre} {I : TC B X}


section Gen
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mt_finite {R : Ranks} {J : ChainIn E K ι R} (Q : PerIn J) (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) :
    FiniteDimensional ℂ (Q.Mt emb σ) := by
  letI := Q.clFin h
  haveI : FiniteDimensional ℂ (VV ℂ Q.sgT) := Module.Finite.of_basis (bVV ℂ Q.sgT)
  let r : Q.Mt emb σ →ₗ[ℂ] (Q.S'.Cl → VV ℂ Q.sgT) :=
    { toFun := fun F c => ⟨F.1 c.1 (Q.S'.rep c), (F.2 c.1 _).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective r ((injective_iff_map_eq_zero r).2 fun F hF => ?_)
  apply Subtype.ext
  funext b d
  have h0 : F.1 b (Q.S'.rep (Q.S'.cl b d)) = 0 := congrArg Subtype.val (congrFun hF (Q.S'.cl b d))
  have h1 := (F.2 b (Q.S'.rep (Q.S'.cl b d))).2 (Q.S'.mv b d) (by rw [hH]; trivial)
  rw [h0, map_zero, smul_zero] at h1
  exact (congrArg (F.1 b) (Q.S'.mv_smul b d)).symm.trans h1
end Gen


theorem ipC_herm (l : I.Laws) (u : B.Word) (x y) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 y x) = ((I.cols l).fm u).ipC 0 x y := by
  unfold MemberForms.ipC
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  congr 1
  · simp [ColumnChain.wt]
  · exact (ClassSumPos.ipVal_herm _ _ _ _ _).symm

theorem ipC_pos (l : I.Laws) (u : B.Word) (x) (hx : x ∈ ((I.cols l).mem u).A.Mu0) (h0 : x ≠ 0) :
    0 < (((I.cols l).fm u).ipC 0 x x).re := by
  letI := (I.chIn u I.mu0).clFin (l.ch u _) 0
  exact (ClassSumPos.classSum_pos_herm (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (base_fOk B) ((l.ch u _).step 0)).1 x hx h0

theorem fits (l : I.Laws) : RowsRestModel.Fits (I.cols l)
    fun a => Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL) := by
  have key : ∀ u a, Nonempty (((I.cols l).PTw u a).Mt ≃ₗ[ℂ]
      RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) := fun u a => by
    haveI := mt_finite B.fields.emb B.embLL (I.perIn B.u₀ a) (l.per _ a) fun _ => rfl
    have key : Nonempty ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL ≃ₗ[ℂ]
        RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq finrank_euclideanSpace_fin.symm
    exact key
  refine ⟨fun u => key u I.mu0, key, fun u x y => ipC_herm l u _ _, fun u x => ?_, fun u x hx => ?_⟩
  · by_cases h0 : x.1 = 0
    · simp [h0, MemberForms.ipC]
    · exact (ipC_pos l u x.1 x.2.1 h0).le
  · by_contra h0
    have := ipC_pos l u x.1 x.2.1 fun e => h0 (Subtype.ext e)
    rw [hx] at this
    simp at this

theorem later (l : I.Laws) (hB : StagesInhab.HasLetters B.toPre) : Nonempty (TC.Later B (I.cols l)) := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  let W := RowsRestModel.model (fits l) 1 1 1
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => ipC_herm l u x y) (fun u x hx h => ipC_pos l u x hx h) (show 1 ≤ 2 * 1 by omega)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨GaloisStage.adapt W, V, S, N, G⟩⟩

theorem kStd_spec (X : PreX B.toPre) (u : B.Word) (n : ℕ) :
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (kStd X u n) p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (kStd X u n) = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 (((kStd X u n)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) :=
  Classical.epsilon_spec (BasePoint.exists_kStd X (base_fields_primes_ok B X).2.1 u n)

end GlobalTheory.Mem.Col2.TrueColsTest

end
