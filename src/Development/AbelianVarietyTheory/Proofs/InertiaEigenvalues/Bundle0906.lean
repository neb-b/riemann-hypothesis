module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie.BallDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sum

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} {iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]} {b : Bool}
  (j : Fin D.R.m)

theorem valC_cuspOf_sum (z : FrC YS iC b ((j : ℕ) + 1)) {ι : Type} (s : Finset ι) (g : ι → NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (∑ t ∈ s, g t) : T0.R ((j : ℕ) + 1)) =
      ∑ t ∈ s, valC z (cuspOf YS fw j (g t) : T0.R ((j : ℕ) + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero, ZeroMemClass.coe_zero, valC_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add (f := _), Submodule.coe_add, valC_add, ih]

end Sum

theorem ball_descent : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _hiC b j hball F' _ _ _ φ' hφ' hv n a f hz
  have := GlobalTheory.SupDescent.liesOver (K := S.Ks) (K' := F') (la := placeAt (embS S iC b)) (la' := placeAt φ') hv
  obtain ⟨d, bb, hb1, hb2⟩ := GlobalTheory.SupDescent.exists_residue_basis (la := placeAt (embS S iC b)) (la' := placeAt φ')
  choose c hc0 hcB using fun s => hball (f s)
  choose x ρ hρ hx using fun s => GlobalTheory.SupDescent.exists_approx (K := S.Ks) (K' := F') hv hb2 (a s) (hc0 s)
  let F : Fin d → NX.FmK S ((j : ℕ) + 1) := fun t => ∑ s, x s t • f s
  have hmem : ∀ g : NX.FmK S ((j : ℕ) + 1), (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) ∈
      sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n := cuspOf_mem_sec YS fw j
  have hF : ∀ t, F t ∈ locBall YS fw iC b j := by
    intro t z
    obtain ⟨T, io, k, hR, y, u, hT, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
    rw [hval _ (hmem _), norm_mul, hu, one_mul]
    let io' : S.Ks →+* T.Fr := io.comp (eKs YS).toRingHom
    have hR' : IsReading (embS S iC b) T io' k :=
      ⟨fun a => (hR.comp (eKs YS a)).trans (embC_eKs YS iC b a), hR.int⟩
    obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt_of_isReading (embS S iC b) hR'
    refine (hR.int _).2 ?_
    refine GlobalTheory.SupDescent.inV_of_forall_emb (K := S.Ks) (K' := F') hb1 hT ho
      (fun t => evI y (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1))) ?_ t
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, ψ, hψ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ _ _ T T' io y i e' he' hi
    obtain ⟨k', hk'⟩ := GlobalTheory.GeoTie.ReadExist.exists_isReading _ F' φ' T' σ e'' ho' hT'
    have hR₁ : IsReading (embC YS iC b) T' (i.comp io) k' := by
      refine ⟨fun a => ?_, hk'.int⟩
      obtain ⟨a0, rfl⟩ := (eKs YS).surjective a
      rw [embC_eKs, ← hφ' a0, ← hk'.comp, hσ a0]
      rfl
    obtain ⟨z', hz'⟩ := PtC.exists_of_reading hR₁ y₁ hT'
    have h4 : ∀ g : NX.FmK S ((j : ℕ) + 1),
        k' (i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)))) = valC z'.1 (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
      intro g
      have h5 : i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1))) = evI y₁ (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
        letI := io.toAlgebra
        letI := (i.comp io).toAlgebra
        exact (DFunLike.congr_fun hψ _).symm.trans (GlobalTheory.FlagTan.evR_frMap (hmem g).1 hmap).symm
      rw [h5, hz' _ _ _ (hmem g)]
    refine (hk'.int _).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, hk'.comp, h4]
    have hid : ∑ t, φ' (bb t : F') * valC z'.1 (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1)) =
        ∑ s, φ' (a s) * valC z'.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1)) -
          ∑ s, φ' (ρ s) * valC z'.1 (cuspOf YS fw j (c s • f s) : T0.R ((j : ℕ) + 1)) := by
      rw [eq_sub_iff_add_eq]
      simp only [F, valC_cuspOf_sum YS fw j, valC_cuspOf_smul YS fw j, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hx s]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, hφ', Finset.sum_mul, add_mul]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => by ring
      · ring
    rw [hid]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz z') ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ s)) (norm_nonneg _) (hcB s z')
  refine ⟨d + n, Fin.append (fun t => (bb t : F')) ρ, Fin.append F fun s => c s • f s, fun t => ?_, fun t => ?_, ?_⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact norm_int_le_one φ' (bb t)
    · rw [Fin.append_right]; exact GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ t)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact hF t
    · rw [Fin.append_right]; exact hcB t
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e : ∀ s, a s = ∑ t, x s t • (bb t : F') + c s • ρ s := fun s => by
      rw [hx s]; simp only [Algebra.smul_def]; rw [mul_comm (algebraMap _ _ (c s))]
    have h1 : ∀ t s, (bb t : F') ⊗ₜ[S.Ks] (x s t • f s) = (x s t • (bb t : F')) ⊗ₜ[S.Ks] f s :=
      fun t s => (TensorProduct.smul_tmul _ _ _).symm
    have h2 : ∀ s, ρ s ⊗ₜ[S.Ks] (c s • f s) = (c s • ρ s) ⊗ₜ[S.Ks] f s := fun s => (TensorProduct.smul_tmul _ _ _).symm
    simp only [F, TensorProduct.tmul_sum, h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← TensorProduct.sum_tmul, ← TensorProduct.add_tmul, ← e s]

end GlobalTheory.GeoTie.BallDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumReadingConstantsLevelCoverRelateCore
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
open CategoryTheory

noncomputable section

namespace GlobalTheory.CoverConstMove

theorem kappa_eq {D : D7} {r : ℕ} (X X' : Data D.host.E r) (hψ : X.Ψ = X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h0 : D.host.φ₀ ∈ X.Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt (X.cmType _).2 h0)⟩
  have s₁ := X.κ0_sign ⟨τ, hτ⟩
  have s₂ := X'.κ0_sign ⟨τ, hψ ▸ hτ⟩
  simp only at s₁ s₂
  rcases X.κ0_xi with h1 | h1 <;> rcases X'.κ0_xi with h2 | h2
  · rw [h1, h2, hξ]
  · exfalso
    rw [h1, hξ] at s₁
    rw [h2, map_neg, Complex.neg_im] at s₂
    linarith
  · exfalso
    rw [h2, ← hξ] at s₂
    rw [h1, map_neg, Complex.neg_im] at s₁
    linarith
  · rw [h1, h2, hξ]


set_option maxHeartbeats 2000000 in
theorem const_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D (T.V j σ) →* Module.End ℂ (WO V (T.V j σ) → ℂ)), IsPair ψ θ V (T.V j σ) χV χW om → ∀ hr : (T.V j σ).rank = D.R.r, (∀ k, IsMod (T.V j σ) hr ((T.U j σ).X k)) → ∀ (h : GA D (T.V j σ)) (δ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ γ : GA D (T.V j σ), (∀ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt (T.V j σ) γ) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) → ∀ (hx₁ : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom) (hx₂ : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom), IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 → ∀ (F₁ F₂ : WO V (T.V j σ) → ℂ) (m₁ m₂ : ℂ), (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (C.U₂.X (C.dict₂ h).1).Λ) (idx : Fin g ≃ (C.U₂.X (C.dict₂ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl (C.U₂.X (C.dict₂ h).1) bas → IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads C.U₂ (C.dict₂ h).1 bas idx e ⟨(C.dict₂ h).2, hx₂⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₁ w = m₁ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (C.U₂.X (C.dict₂ h).1) bas idx (C.dict₂ h).2 (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b) (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) → (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((T.U j σ).X (T.dict j σ h).1).Λ) (idx : Fin g ≃ ((T.U j σ).X (T.dict j σ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl ((T.U j σ).X (T.dict j σ h).1) bas → IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads (T.U j σ) (T.dict j σ h).1 bas idx e ⟨(T.dict j σ h).2, hx₁⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₂ w = m₂ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx ((T.U j σ).X (T.dict j σ h).1) bas idx (T.dict j σ h).2 (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b) (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) → (∀ w, F₂ (actO V (T.V j σ) 1 γ w) = F₁ w) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a V.rank, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank, C.IsPull f f₂ → m₁ * rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = m₂ * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  intro D T hT j hj σ hσ C hC ψ θ V χV χW om hP hr hM h δ hΛ hiso hfr γ hγ hx₁ hx₂ hu F₁ F₂ m₁ m₂ c₁ c₂ hF a f hf f₂ hf₂ hp
  obtain ⟨o₁, o₂⟩ := GlobalTheory.CoverFrameOver.un_over D T hT j hj σ hσ C hC h δ hΛ hiso hfr _ _ hx₂ hx₁ hfr
  obtain ⟨t, ht, hval, hlift⟩ := GlobalTheory.T.exists_scalar_levelCover_analyticFibre D T j σ C hC.1 hC.2.2.1 _ _ o₁ o₂
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂', ik₂, φ₂, th₂, hW₂, hth₂, -⟩ := hC
  have hU := hT.unf j hj σ hσ
  obtain ⟨-, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hr1 : 1 ≤ D.R.r := (hnum _ hj).2.1
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU
  have hSD : ∀ k, SelfD ((T.U j σ).X k) ((T.U j σ).X k).Λ := fun k => (_root_.GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt k).2.1
  obtain ⟨Dc, hDc, -⟩ := GlobalTheory.Dict.exists_dic _ _ _ _ _ σ _ Wt.g 0 ((T.U j σ).X (T.dict j σ h).1) 0 Wt.e hσ hU.1
    (hU.2.1 _).1 (hU.2.1 _).2 (hSD _) ⟨fun _ => antitone_const, Even.zero⟩
  have hi : IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) Dc.idx Wt.e := hDc ▸ ⟨Dc.per_eq, Dc.ty_eq⟩
  obtain ⟨A, hmk, ϑ, hϑ, hone⟩ := GlobalTheory.Dict.uw_anFib _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt _
    Dc.bas Dc.idx Dc.sympl hi.1 hi.2 ⟨_, hx₁⟩ hu
  obtain ⟨A₂, r₂⟩ := hlift _ _ _ Dc.bas Dc.idx Wt.e _ _ (Wt.mark _) Dc.sympl hx₁ (hSD _) ϑ ⟨A, hmk, hϑ⟩
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hξ : ((T.U j σ).X (T.dict j σ h).1).ξ0 = (C.U₂.X (C.dict₂ h).1).ξ0 := (hM _).model.2.trans (hW₂ _).2.symm
  have hS : SameSp ((T.U j σ).X (T.dict j σ h).1) (C.U₂.X (C.dict₂ h).1) :=
    ⟨Finset.ext hΨ, (hM _).model.1.trans (hW₂ _).1.symm, (hU.2.1 _).1.trans (hU₂.2.1 _).1.symm, hξ,
      kappa_eq _ _ (Finset.ext hΨ) hξ⟩
  have hS' : SameSp (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) :=
    ⟨hS.psi.symm, hS.gm.symm, hS.p0.symm, hS.xi.symm, hS.ka.symm⟩
  have hδ₂ : IsUn (C.U₂.X (C.dict₂ h).1) δ⁻¹ := fun u v => by
    have e := hiso ((δ⁻¹).1 *ᵥ u) ((δ⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec, hS.gm] at e
    exact e.symm
  have hδ₁ : IsUn ((T.U j σ).X (T.dict j σ h).1) δ := fun u v => by
    rw [hiso u v, hS.gm]
  obtain ⟨idx₂, hi₂, hpv, hty, hidx⟩ := GlobalTheory.FrameConstMove.exists_idx hS hi
  have hSD₁₂ : SelfD (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1).Λ := by
    refine ⟨(hSD _).1, fun v => ((hSD (T.dict j σ h).1).2 v).trans ?_⟩
    exact forall₂_congr fun y _ => by rw [hS.EF_eq]
  have hmt : GlobalTheory.LevelCusp.IsMatch (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) δ := by
    refine ⟨hS.psi.symm, hS.p0.symm, hS.xi.symm, hiso, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · show δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E))
      rw [hΛ]
      exact ⟨v, hv, rfl⟩
    · have hv' : δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) := hv
      rw [hΛ] at hv'
      obtain ⟨u, hu', e⟩ := hv'
      have e' := congrArg (fun w => (δ⁻¹).1 *ᵥ w) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e'
      exact e' ▸ hu'
  have hlat : mapL δ⁻¹ ((T.U j σ).X (T.dict j σ h).1).Λ = (C.U₂.X (C.dict₂ h).1).Λ := by
    ext v
    rw [Lev.mem_mapL, Lev.lin_apply, inv_inv]
    exact (hmt.lat v).symm
  have hSD₂ : SelfD (C.U₂.X (C.dict₂ h).1) (C.U₂.X (C.dict₂ h).1).Λ := hlat ▸ Lev.selfD_mapL hδ₂ hSD₁₂
  obtain ⟨bas₂, hb₂⟩ := GlobalTheory.Dict.Letters.exists_isSympl (C.U₂.X (C.dict₂ h).1) hSD₂ idx₂
  have hx1eq : (T.dict j σ h).2 = lact δ (castFr hmt.psi (C.dict₂ h).2) := funext fun τ => by
    change mat (T.dict j σ h).2 τ = δ.1.map τ.1 * mat (C.dict₂ h).2 ⟨τ.1, _⟩
    exact hfr τ.1 _ τ.2
  have hfr₂ : lact δ⁻¹ (castFr hS.psi (T.dict j σ h).2) = (C.dict₂ h).2 := funext fun τ => by
    change (δ⁻¹).1.map τ.1 * mat (T.dict j σ h).2 ⟨τ.1, _⟩ = mat (C.dict₂ h).2 τ
    rw [hfr τ.1 τ.2, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul]
  obtain ⟨-, -, -, A₃, r₃, -, -⟩ := letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra
    GlobalTheory.Dict.anFib_move _ _ _ _ _ _ _ _ _ _ hS Dc.bas Dc.idx bas₂ idx₂ Wt.e _ _ _ A₂ δ⁻¹ Dc.sympl hb₂ hx₁ (hSD _) hδ₂
      (hpv _) hty
  have g₂ : GenReads C.U₂ (C.dict₂ h).1 bas₂ idx₂ Wt.e ⟨_, hx₂⟩ fun z => t * ϑ z := by
    have := r₃ _ r₂
    clear r₃
    revert A₃
    rw [hlat, hfr₂]
    exact fun A₃ h => ⟨A₃, h⟩
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  have hi₂' : IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx₂ Wt.e :=
    ⟨fun x v j' => (hi₂.1 x v j').trans (by rw [hrel]), fun j' => (hi₂.2 j').trans (hrel _)⟩
  have hM₂ : IsMod (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) :=
    ⟨hW₂ _, fun τ => (hΨ τ).symm.trans ((hM _).psi τ), hS.ka.symm.trans (hM _).kap⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FrameConstMove.exists_ne_zero_of_meanOne hone
  obtain ⟨pt, -, hpt, -⟩ := (GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V (T.V j σ) _ _ hr (C.U₂.X (C.dict₂ h).1) bas₂ idx₂
    hP.weil.std hP.inf hP.std hP.even hM₂ hb₂ (C.dict₂ h).2).2.2.2.2 hx₂
  obtain ⟨w0, wz⟩ := hpt fun _ => z
  generalize pt (fun _ => z) = w at w0 wz
  have wz' : zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) Dc.idx (T.dict j σ h).2 (actO V (T.V j σ) 1 γ w) =
      fun _ => z := by
    rw [← wz]
    funext b j'
    have hid : Dc.idx j' = (⟨(idx₂ j').1.1, hmt.psi.le (idx₂ j').1.2⟩, (idx₂ j').2) := by
      have e := hidx j'
      refine Prod.ext (Subtype.ext ?_) ?_
      · rw [e]
      · rw [e]
    refine Eq.trans ?_ (GlobalTheory.FrameConstMove.perC_match hmt (C.dict₂ h).2
      (fun τ a => realM θ w τ (Fin.cast hr.symm a) b) (idx₂ j').1 (idx₂ j').2)
    show perC _ _ _ (Dc.idx j') = _
    rw [hid, hx1eq]
    refine congrArg (fun u => perC _ _ u _) (funext fun τ => funext fun a' => ?_)
    rw [GlobalTheory.FrameConstMove.actO_one_left, GlobalTheory.FrameConstMove.realM_mul, ← hγ τ.1 τ.2]
    exact Fintype.sum_equiv (finCongr hr) _ _ fun c => rfl
  have v₂ := c₂ _ Dc.bas Dc.idx Wt.e Dc.sympl hi ϑ ⟨A, hϑ⟩ (actO V (T.V j σ) 1 γ w)
    (by rw [GlobalTheory.FrameConstMove.actO_one_left, Matrix.map_mul, w0, Matrix.mul_zero])
  have v₁ := c₁ _ bas₂ idx₂ Wt.e hb₂ hi₂' _ g₂ w w0
  rw [hF, wz'] at v₂
  rw [v₂, wz] at v₁
  have hxx : ∀ z w, hx ((T.U j σ).X (T.dict j σ h).1) Dc.bas Dc.idx (T.dict j σ h).2 z w =
      hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z w := by
    intro z' w'
    rw [hx1eq]
    exact GlobalTheory.FrameConstMove.hx_match hS' hb₂ Dc.sympl hx₂ (fun v => (hpv (castFr hS'.psi (C.dict₂ h).2) v).symm) hδ₁ z' w'
  simp only [hxx, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at v₁
  have key : m₁ * t ^ V.rank = m₂ := by
    have hne : cexp (-(Real.pi / 2 : ℂ) * ∑ b : Fin V.rank, hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z z) *
        ϑ z ^ V.rank ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ hz)
    apply mul_right_cancel₀ hne
    linear_combination -v₁
  have u₁ : rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = toC (evR C.d.Xo₂ C.d.c₂ f₂ (C.U₂.un _ ⟨_, hx₂⟩)) := dif_pos hx₂
  have u₂ : rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 =
      toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un _ ⟨_, hx₁⟩)) := dif_pos hx₁
  rw [u₁, u₂, hval V.rank a f hf f₂ hp, ← key]
  ring

end GlobalTheory.CoverConstMove
end
end

