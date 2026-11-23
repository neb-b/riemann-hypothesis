module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleLiftSplitPlaceConjugatePair
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.AdmLift

theorem exists_admissible_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  intro F E _ _ _ _ _ σ d W v hskew π₁ π₂ b₁ b₂ h12 h21 inj surj S hS X₁ X₂ hX

  let c : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).toSubring.subtype
  have hc : ∀ A : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), A.map (fun x => (x : Fv F v)) = A.map c := fun _ => rfl
  set B₁ : Matrix (Fin d) (Fin d) (Fv F v) := (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₁
  set B₂ : Matrix (Fin d) (Fin d) (Fv F v) := (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₂
  set C₁ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₁
  set C₂ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₂
  have hBC₂ : B₂ * C₂ = 1 := b₂.mul_inv
  have hCB₁ : C₁ᵀ * B₁ᵀ = 1 := by rw [← Matrix.transpose_mul, show B₁ * C₁ = 1 from b₁.mul_inv, Matrix.transpose_one]
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  set M₁ : Matrix (Fin d) (Fin d) (Fv F v) := B₁ * X₁.map (fun x => (x : Fv F v)) * C₁ with hM₁
  set M₂ : Matrix (Fin d) (Fin d) (Fv F v) := B₂ * X₂.map (fun x => (x : Fv F v)) * C₂ with hM₂

  have hX' : (X₁.map c)ᵀ * S.map c + S.map c * X₂.map c = 0 := by
    have := congrArg (fun A => A.map c) hX
    simpa [Matrix.map_add (f := _), Matrix.map_mul, Matrix.transpose_map] using this
  rw [hc] at hS
  have key₁ : M₁ᵀ * J₁ + J₁ * M₂ = 0 := by
    have e : M₁ᵀ * J₁ + J₁ * M₂ = C₁ᵀ * ((X₁.map c)ᵀ * S.map c + S.map c * X₂.map c) * C₂ := by
      rw [hS, hM₁, hM₂, hc, hc]
      simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      congr 1
      · rw [hBC₂, Matrix.mul_one]
      · rw [← Matrix.mul_assoc C₁ᵀ, hCB₁, Matrix.one_mul]
    rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

  have hJ₂ : (incM F W.J).map π₂ = -J₁ᵀ := by
    ext i j
    have h1 : cA σ (inclR (F := F) (AF F) (W.J i j)) = inclR (F := F) (AF F) (σ (W.J i j)) := by simp [cA, inclR]
    simp only [incM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, hJ₁]
    rw [← h12, h1, hskew j i, map_neg, map_neg]
  have key₂ : M₂ᵀ * (-J₁ᵀ) + (-J₁ᵀ) * M₁ = 0 := by
    have gen : ∀ A B K : Matrix (Fin d) (Fin d) (Fv F v), Bᵀ * (-Kᵀ) + (-Kᵀ) * A = -(Aᵀ * K + K * B)ᵀ := by
      intro A B K
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, neg_add,
        Matrix.mul_neg, Matrix.neg_mul, add_comm]
    rw [gen, key₁, Matrix.transpose_zero, neg_zero]

  choose z hzA hz1 hz2 using surj
  let Y : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of fun i j => z (M₁ i j) (M₂ i j)
  have hY1 : Y.map π₁ = M₁ := by ext i j; simp [Y, hz1]
  have hY2 : Y.map π₂ = M₂ := by ext i j; simp [Y, hz2]
  have hAtE : ∀ i j, At (evFin F v) (Y i j) := fun i j => hzA _ _
  have atMulR : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) (a * b) := fun a b ha u hu => by
    rw [← smul_mul_assoc, ha u hu, zero_mul]
  have atMulL : ∀ a b : AE F E, At (evFin F v) b → At (evFin F v) (a * b) := fun a b hb u hu => by
    rw [← mul_smul_comm, hb u hu, mul_zero]
  have atCA : ∀ a : AE F E, At (evFin F v) a → At (evFin F v) (cA σ a) := fun a ha u hu => by
    rw [← map_smul, ha u hu, map_zero]
  have atSum : ∀ f : Fin d → AE F E, (∀ k, At (evFin F v) (f k)) → At (evFin F v) (∑ k, f k) := fun f hf u hu => by
    rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun k _ => hf k u hu
  have atAdd : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) b → At (evFin F v) (a + b) := fun a b ha hb u hu => by
    rw [smul_add, ha u hu, hb u hu, add_zero]
  refine ⟨Y, ?_, hY1, hY2, ?_⟩
  · intro u hu
    ext i j
    rw [Matrix.smul_apply, Matrix.zero_apply]
    exact hAtE i j u hu
  · set Q := Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) with hQ
    have hcomp₁ : (Y.map (cA σ)).map π₁ = M₂ := by
      rw [← hY2]; ext i j; simp [h12]
    have hcomp₂ : (Y.map (cA σ)).map π₂ = M₁ := by
      rw [← hY1]; ext i j; simp [h21]
    have hQ1 : Q.map π₁ = 0 := by
      rw [hQ, Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY1, hcomp₁, ← hJ₁, key₁]
      exact fun a b => map_add π₁ a b
    have hQ2 : Q.map π₂ = 0 := by
      rw [hQ, Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY2, hcomp₂, hJ₂, key₂]
      exact fun a b => map_add π₂ a b
    ext i j
    apply inj
    · simp only [hQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      exact atAdd _ _ (atSum _ fun k => atMulR _ _ (hAtE k i)) (atSum _ fun k => atMulL _ _ (atCA _ (hAtE k j)))
    · have := congrFun (congrFun hQ1 i) j
      simpa using this
    · have := congrFun (congrFun hQ2 i) j
      simpa using this

end GlobalTheory.AdmLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ConjIdeal

variable {E : Type} [Field E] [NumberField E]

theorem map_mem_mul (c : E →+* E) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', c x ∈ A) (hB : ∀ x ∈ B', c x ∈ B) : ∀ x ∈ A' * B', c x ∈ A * B := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun y z hy hz => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)
  · rw [map_add (f := _)]
    exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hy) (FractionalIdeal.mem_coe.2 hz))

theorem conj_symm (c : E →+* E) (hc : ∀ x, c (c x) = x) {I I' : FractionalIdeal (𝓞 E)⁰ E}
    (h : ∀ x, x ∈ I' ↔ c x ∈ I) : ∀ x, x ∈ I ↔ c x ∈ I' := fun x => by rw [h, hc]

theorem conj_mul (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hB : ∀ x, x ∈ B' ↔ c x ∈ B) : ∀ x, x ∈ A' * B' ↔ c x ∈ A * B := by
  intro x
  refine ⟨map_mem_mul c (fun y hy => (hA y).1 hy) (fun y hy => (hB y).1 hy) x, fun h => ?_⟩
  have := map_mem_mul c (fun y hy => (conj_symm c hc hA y).1 hy) (fun y hy => (conj_symm c hc hB y).1 hy) _ h
  rwa [hc] at this

theorem conj_pow (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {A A' : FractionalIdeal (𝓞 E)⁰ E} (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (n : ℕ) : ∀ x, x ∈ A' ^ n ↔ c x ∈ A ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact h1
  | succ n ih => simpa only [pow_succ] using conj_mul c hc ih hA

theorem conj_ne_zero (c : E →+* E) (hc : ∀ x, c (c x) = x) {B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) : B' ≠ 0 := by
  intro h
  apply h0
  rw [FractionalIdeal.eq_zero_iff] at h ⊢
  intro x hx
  have := h (c x) ((hB (c x)).2 (by rwa [hc]))
  rw [← hc x, this, map_zero]

theorem conj_inv (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) :
    ∀ x, x ∈ B'⁻¹ ↔ c x ∈ B⁻¹ := by
  intro x
  have := GlobalTheory.ChiGrid.StairConj.mem_mul_inv_iff c hc (map_mul c) h0 (conj_ne_zero c hc hB h0) h1 hB x
  simpa only [one_mul] using this

end GlobalTheory.ConjIdeal

namespace GlobalTheory.ConjIdeal

theorem stA_modul_conj_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  intro D T L P sc a b
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  let c : D.host.E →+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom
  have hcx : ∀ x, c x = D.host.conj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Formalism.L2.Pj.conj_conj D x
  have h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have k : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) → c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      intro x hx
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).1 hx
      exact (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).2 ⟨D.host.conj • z, Formalism.L2.Pj.algebraMap_gal_smul D _ z⟩
    exact fun x => ⟨k x, fun h => by simpa only [hc] using k _ h⟩
  obtain ⟨hA0, hA⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  have hA' : ∀ x, x ∈ P.stAbar sc ↔ c x ∈ P.stA sc := fun x => by rw [hcx, ← hs]; exact hA x
  set M : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMdef
  set Mb : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMbdef
  have hM : ∀ x, x ∈ M ↔ c x ∈ Mb := fun x => GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ x
  have hM0 : M ≠ 0 := by rw [hMdef, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hMb0 : Mb ≠ 0 := conj_ne_zero c hc (conj_symm c hc hM) hM0
  have hAb0 : P.stAbar sc ≠ 0 := conj_ne_zero c hc hA' hA0
  refine ⟨P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹), ?_, ?_⟩
  · have e1 : P.stA sc ^ a ≠ 0 := pow_ne_zero _ hA0
    have e2 : P.stAbar sc ^ a ≠ 0 := pow_ne_zero _ hAb0
    have e3 : M ^ b ≠ 0 := pow_ne_zero _ hM0
    have e4 : Mb ^ b ≠ 0 := pow_ne_zero _ hMb0
    calc P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (M ^ b * (Mb ^ b)⁻¹) *
          (P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹))
        = (P.stA sc ^ a * (P.stA sc ^ a)⁻¹) * (P.stAbar sc ^ a * (P.stAbar sc ^ a)⁻¹) *
          ((M ^ b * (M ^ b)⁻¹) * (Mb ^ b * (Mb ^ b)⁻¹)) := by ac_rfl
      _ = 1 := by rw [mul_inv_cancel₀ e1, mul_inv_cancel₀ e2, mul_inv_cancel₀ e3, mul_inv_cancel₀ e4]; simp
  · intro x
    rw [hs]
    exact conj_mul c hc (conj_mul c hc (conj_pow c hc h1 hA' a) (conj_inv c hc h1 (conj_pow c hc h1 (conj_symm c hc hA') a) (pow_ne_zero _ hAb0)))
      (conj_mul c hc (conj_pow c hc h1 (conj_symm c hc hM) b) (conj_inv c hc h1 (conj_pow c hc h1 hM b) (pow_ne_zero _ hMb0))) x

end GlobalTheory.ConjIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowRepR

private theorem lamS_eq_lamAt (R : Ranks) (P : HCParam R) (i : Fin R.r) :
    Formalism.MainNotions.S.lamS R P i = ((Formalism.L2.NTheta.lamAt P i.val : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
  by_cases h1 : i.val < R.k - 1
  · simp [h1]
  · by_cases h2 : i.val - (R.k - 1) < R.m
    · simp [h1, h2]
    · simp [h1, h2]

private theorem lamAt_gap_of_lt {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau)
    {i j : ℕ} (hij : i < j) (hj : j < D.R.r) :
    100 * (D.R.r : ℚ) ^ 4 ≤
      Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  induction j, hij using Nat.le_induction with
  | base => exact hH.gapR τ i hj
  | succ j _ ih =>
    exact (ih (Nat.lt_of_succ_lt hj)).trans
      (sub_le_sub_left (Formalism.L2.NTheta.lamAt_lt (D.hc τ) j hj).le _)

private theorem gapGe_hundred_mul_r_pow_four {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hH : HostHyp D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  intro v
  unfold Formalism.QuantumDeterminants.GapAtLeast
  intro a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq, lamS_eq_lamAt, lamS_eq_lamAt]
  have key : ∀ i j : Fin D.R.r, i.val < j.val →
      100 * (D.R.r : ℝ) ^ 4 ≤ |((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ)| := by
    intro i j hij
    have hq := lamAt_gap_of_lt hH (X.pl v) hij j.isLt
    have hr : 100 * (D.R.r : ℝ) ^ 4 ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ) := by exact_mod_cast hq
    exact hr.trans (le_abs_self _)
  have hne : (Fin.cast X.n_eq a).val ≠ (Fin.cast X.n_eq b).val := fun hv => hab (congrArg _ (Fin.ext hv))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key _ _ hlt
  · rw [abs_sub_comm]
    exact key _ _ hgt

theorem exists_contRep_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM hH hE t c ht hconj hc Φ hΦ u
  exact GlobalTheory.ConjRowRep.exists_contRep hDS D X h R.θ _ (MP R) _ _ t c rfl hM.inf (gapGe_hundred_mul_r_pow_four X hH) hE
    ⟨ht, hconj⟩ hc Φ hΦ u

end GlobalTheory.ConjRowRepR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CongrOrbit

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem quot_mapMatrix_eq_one_iff (I : Ideal O) (A : Matrix n n O) :
    (Ideal.Quotient.mk I).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ I := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simpa [Matrix.one_apply, apply_ite] using this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simpa [Matrix.one_apply, apply_ite] using this

theorem isUnit_det_of_sub_one_mem (I : Ideal O) (hI : I ≤ Ideal.jacobson ⊥) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) : IsUnit A.det := by
  have h1 := (quot_mapMatrix_eq_one_iff I A).2 hA
  have h2 : Ideal.Quotient.mk I A.det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have h3 : A.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, h2, map_one]
  have h4 := (Ideal.mem_jacobson_bot.1 (hI h3)) 1
  simpa using h4

variable {a b : Type} [Fintype a] [Fintype b]

def colFix (f : a → n) (ξ : a → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ p, (ξ p i - if i = f p then 1 else 0) * (if j = f p then 1 else 0)

def rowFix (g : b → n) (ζ : b → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ q, (if i = g q then 1 else 0) * (ζ q j - if g q = j then 1 else 0)

theorem colFix_sub_one_mem (I : Ideal O) (f : a → n) (ξ : a → n → O)
    (hξ : ∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) (i j : n) :
    (colFix f ξ - 1) i j ∈ I := by
  simp only [colFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hξ p i)

theorem colFix_apply_col {f : a → n} (hf : Function.Injective f) (ξ : a → n → O) (i : n)
    (p₀ : a) : colFix f ξ i (f p₀) = ξ p₀ i := by
  simp only [colFix, Matrix.of_apply]
  rw [Finset.sum_eq_single p₀]
  · rw [if_pos rfl, mul_one]; ring
  · intro p _ hp
    rw [if_neg (fun h => hp (hf h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowFix_sub_one_mem (I : Ideal O) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I) (i j : n) :
    (rowFix g ζ - 1) i j ∈ I := by
  simp only [rowFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hζ q j)

theorem rowFix_apply_row {g : b → n} (hg : Function.Injective g) (ζ : b → n → O) (j : n)
    (q₀ : b) : rowFix g ζ (g q₀) j = ζ q₀ j := by
  simp only [rowFix, Matrix.of_apply]
  rw [Finset.sum_eq_single q₀]
  · rw [if_pos rfl, one_mul]; ring
  · intro q _ hq
    rw [if_neg (fun h => hq (hg h).symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowFix_apply_col (f : a → n) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0) (i : n) (p : a) :
    rowFix g ζ i (f p) = if i = f p then 1 else 0 := by
  simp only [rowFix, Matrix.of_apply, hζ, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem vecMul_sub_single_mem (I : Ideal O) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) (v : n → O) (c : n)
    (hv : ∀ i, v i - (if i = c then 1 else 0) ∈ I) (j : n) :
    (v ᵥ* A) j - (if c = j then 1 else 0) ∈ I := by
  have e1 : (v ᵥ* A) j = (v ᵥ* (A - 1)) j + v j := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]; ring
  have e2 : (if c = j then (1 : O) else 0) = if j = c then 1 else 0 := by
    by_cases h : c = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e1, e2, add_sub_assoc]
  refine add_mem ?_ (hv j)
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hA i j)

end GlobalTheory.AscFin.CongrOrbit

theorem GlobalTheory.AscFin.exists_gl_congr_cols_rows : ∀ (O : Type) [CommRing O] (I : Ideal O), I ≤ Ideal.jacobson ⊥ → ∀ (n a b : Type) [Fintype n] [DecidableEq n] [Fintype a] [Fintype b] (f : a → n) (g : b → n), Function.Injective f → Function.Injective g → ∀ (ξ : a → n → O) (η : b → n → O), (∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) → (∀ q i, η q i - (if i = g q then 1 else 0) ∈ I) → (∀ p q, η q ⬝ᵥ ξ p = if g q = f p then 1 else 0) → ∃ k : GL n O, (∀ i j, (k.1 - 1) i j ∈ I) ∧ (∀ p i, k.1 i (f p) = ξ p i) ∧ ∀ q, η q ᵥ* k.1 = fun i => if i = g q then 1 else 0 := by
  intro O _ I hI n a b _ _ _ _ f g hf hg ξ η hξ hη hηξ
  open GlobalTheory.AscFin.CongrOrbit in
  set k₁ := colFix f ξ with hk₁
  have hk₁I := colFix_sub_one_mem I f ξ hξ
  set ζ : b → n → O := fun q => η q ᵥ* k₁ with hζdef
  have hζI : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I := fun q j =>
    vecMul_sub_single_mem I k₁ hk₁I (η q) (g q) (hη q) j
  have hζcol : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0 := by
    intro q p
    have hc : (fun i => k₁ i (f p)) = ξ p := funext fun i => colFix_apply_col hf ξ i p
    simp only [hζdef, Matrix.vecMul]
    rw [hc, hηξ]
  set m := rowFix g ζ with hm
  have hmI := rowFix_sub_one_mem I g ζ hζI
  have hmcol : ∀ i p, m i (f p) = if i = f p then 1 else 0 := rowFix_apply_col f g ζ hζcol
  have u₁ := isUnit_det_of_sub_one_mem I hI k₁ hk₁I
  have um := isUnit_det_of_sub_one_mem I hI m hmI
  set U₁ := Matrix.nonsingInvUnit k₁ u₁
  set Um := Matrix.nonsingInvUnit m um
  set Wm : Matrix n n O := ((Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) with hWm
  have hWmm : Wm * m = 1 := Um.inv_mul
  have hmWm : m * Wm = 1 := Um.mul_inv
  have hval : ((U₁ * Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) = k₁ * Wm := rfl
  refine ⟨U₁ * Um⁻¹, ?_, ?_, ?_⟩
  · rw [hval, ← quot_mapMatrix_eq_one_iff]
    have e1 := (quot_mapMatrix_eq_one_iff I k₁).2 hk₁I
    have e2 := (quot_mapMatrix_eq_one_iff I m).2 hmI
    have eW : (Ideal.Quotient.mk I).mapMatrix Wm = 1 := by
      calc (Ideal.Quotient.mk I).mapMatrix Wm
          = (Ideal.Quotient.mk I).mapMatrix Wm * (Ideal.Quotient.mk I).mapMatrix m := by
            rw [e2, mul_one]
        _ = 1 := by rw [← map_mul, hWmm, map_one]
    rw [map_mul, e1, eW, one_mul]
  · intro p i
    rw [hval]
    have hWcol : ∀ l, Wm l (f p) = if l = f p then 1 else 0 := by
      intro l
      have := congrFun (congrFun hWmm l) (f p)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simpa only [hmcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] using this
    rw [Matrix.mul_apply]
    simp only [hWcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact colFix_apply_col hf ξ i p
  · intro q
    rw [hval, ← Matrix.vecMul_vecMul]
    funext j
    have hrow : η q ᵥ* k₁ = fun l => m (g q) l := by
      funext l; rw [hm, rowFix_apply_row hg]
    rw [hrow]
    have := congrFun (congrFun hmWm (g q)) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.vecMul, dotProduct]
    rw [this]
    by_cases h : g q = j
    · simp [h]
    · simp [h, Ne.symm h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.VacSub

theorem exists_vacG_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Γ ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ f, VacG ψ S T Γ f ∧ f ≠ 0 := by
  intro D ψ hψ S T LS LT dS dT Γ hΓ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) LS LT dS dT
  obtain ⟨h1, h2, -⟩ := hf 1
  simp only [one_mul] at h1 h2
  exact ⟨f, ⟨h1, fun u hu => h2.1 u (hΓ hu), fun e he u hu hh => h2.2 e he u (hΓ hu) hh⟩, f0⟩

end GlobalTheory.AscFin.VacSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.LeviNorm.norm_levi | exact GlobalTheory.LeviNorm.norm_levi | (intros; apply GlobalTheory.LeviNorm.norm_levi <;> assumption)
end

