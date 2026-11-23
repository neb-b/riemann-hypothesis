module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponent
section
noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

end GlobalTheory.BotLValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSelfDualLatticeFixedFunctionsLineStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  first | exact @GlobalTheory.LatVacLine.vacuum_line | exact GlobalTheory.LatVacLine.vacuum_line | (intros; apply GlobalTheory.LatVacLine.vacuum_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanish
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DblTrace

open Matrix

theorem hTens_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) x y = hTens c JA JB x.toCols₁ y.toCols₁ + hTens c JA (-JB) x.toCols₂ y.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, toCols₁, toCols₂,
    of_apply, ← Finset.sum_add_distrib]

theorem rhs_dbl {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m K)
    (X U : Matrix m (n ⊕ n) K) (B : Matrix n n K) :
    ∑ k, ∑ l, (-(A * X * (fromBlocks B 0 0 (-B))ᵀ)) k l * U k l =
      ∑ k, ∑ l, (-(A * X.toCols₁ * Bᵀ)) k l * U.toCols₁ k l +
        ∑ k, ∑ l, (-(A * X.toCols₂ * (-B)ᵀ)) k l * U.toCols₂ k l := by
  have hX : A * X = fromCols (A * X.toCols₁) (A * X.toCols₂) := by
    conv_lhs => rw [← fromCols_toCols X]
    rw [mul_fromCols]
  rw [hX, fromBlocks_transpose, fromCols_mul_fromBlocks]
  simp [Fintype.sum_sum_type, Finset.sum_add_distrib, toCols₁, toCols₂]
  ring

end GlobalTheory.DblTrace

open GlobalTheory.DblTrace in
theorem GlobalTheory.DblTrace.trace_pairing_dbl : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  intro F E _ _ _ _ _ σ hcm v τ m n JA JB hA hB x u hx hu
  have hneg : incM F (-JB) = -incM F JB := by
    simp [incM, Matrix.map_neg]
  have hB' : ∀ i j, σ ((-JB) j i) = -(-JB) i j := by
    intro i j; simp [hB]
  have h1 : x.toCols₁.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inl j)
  have h2 : u.toCols₁.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inl j)
  have h3 : x.toCols₂.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inr j)
  have h4 : u.toCols₂.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inr j)
  have hd : (dbl JB).map τ = Matrix.fromBlocks (JB.map τ) 0 0 (-(JB.map τ)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  rw [hTens_dbl, ← hneg, map_add (f := _), map_add (f := _), add_add_add_comm, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA JB hA hB _ _ h1 h2,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA (-JB) hA hB' _ _ h3 h4, hd, rhs_dbl]
  have hm : (-JB).map τ = -(JB.map τ) := by ext i j; simp
  rw [hm]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuumStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∀ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), Reads ψ θ hS hT ⊤ δ 1 G v → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm →
  Reads ψ θ hS hT ⊤ δ 1 (cosV δ 𝔪 0 G) (Tm (cosInd e 𝔪 hS hT 0)) := by
  first | exact @GlobalTheory.IopRead.indicator_reads | exact GlobalTheory.IopRead.indicator_reads | (intros; apply GlobalTheory.IopRead.indicator_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
section
noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_smul_mul {A : Type} [CommRing A] [Algebra (AF F) A] {ε : AF F} (hε : ε * ε = ε) (a b : A) :
    (ε • a + (1 - ε) • (1 : A)) * (ε • b + (1 - ε) • (1 : A)) = ε • (a * b) + (1 - ε) • (1 : A) := by
  simp only [Algebra.smul_def, mul_one]
  have he : algebraMap (AF F) A ε * algebraMap (AF F) A ε = algebraMap (AF F) A ε := by rw [← map_mul, hε]
  rw [map_sub, map_one]
  linear_combination (a * b - a - b + 1) * he


variable (E) in
def idemUnit (ε : AF F) (hε : ε * ε = ε) : (AE F E)ˣ →* (AE F E)ˣ where
  toFun l := ⟨ε • l.1 + (1 - ε) • 1, ε • (l⁻¹ : (AE F E)ˣ).1 + (1 - ε) • 1,
    by rw [idem_smul_mul hε, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [idem_smul_mul hε, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩
  map_one' := Units.ext (by simp only [Units.val_one, Units.val_mk]; rw [← add_smul, add_sub_cancel, one_smul])
  map_mul' a b := Units.ext (by simp only [Units.val_mul, Units.val_mk]; rw [idem_smul_mul hε])


def eFin (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

def eInf (F : Type) [Field F] [NumberField F] : AF F := realAd F 1

theorem eFin_idem (v : Pl F) : eFin v * eFin v = eFin v := by
  have h := GlobalTheory.LatVac.at_liftV v 1 (eFin v - 1) (by
    rw [eFin, map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem eInf_idem : eInf F * eInf F = eInf F := by
  have h := at_partInf (M := AF F) (1 : AF F) (eInf F - 1) (by
    rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  simp only [partInf, smul_eq_mul, mul_one] at h
  unfold eInf at h ⊢
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h


variable (E) in
def unitAt (v : Pl F) : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eFin v) (eFin_idem v)


variable (F E) in
def unitArch : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eInf F) eInf_idem



theorem unitAt_mem (v : Pl F) (l : (AE F E)ˣ) : unitAt E v l ∈ idelesAt E (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  change u • (eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1) = 0
  rw [show eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1 = eFin v • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem unitArch_mem (l : (AE F E)ˣ) : unitArch F E l ∈ idelesAt E (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  change u • (eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1) = 0
  rw [show eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1 = eInf F • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

end GlobalTheory.ThK.ConeEuler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def ptAt (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) : w.adicCompletion E →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.AdelicU.Supp.singleTens E v).comp (InertChart.complEquiv hw h).symm.toRingHom.toNonUnitalRingHom

def locW (h : w.under (𝓞 F) = v) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

def kap (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    Matrix (Fin n) (Fin m) (w.adicCompletion E) →+ Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom).comp
    { toFun := fun x => A * xᵀ * Bᵀ
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul] }

variable (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem kap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x : Matrix (Fin n) (Fin m) (w.adicCompletion E)) : kap hw h A B x = (A * xᵀ * Bᵀ).map (ptAt hw h) := rfl

theorem ptAt_apply (z : w.adicCompletion E) :
    ptAt hw h z = GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z) := rfl

theorem locW_ptAt (z : w.adicCompletion E) : locW h (ptAt hw h z) = z := by
  change toCompl h (compFin F E v (GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
  exact (InertChart.complEquiv hw h).apply_symm_apply z

theorem at_ptAt (z : w.adicCompletion E) : At (evFin F v) (ptAt hw h z) :=
  GlobalTheory.ThK.at_evFin_iff.2 ⟨fun u => GlobalTheory.AdelicU.Supp.compInf_singleTens u v _,
    fun u hu => GlobalTheory.AdelicU.Supp.compFin_singleTens_ne hu _⟩

theorem ptAt_locW {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : ptAt hw h (locW h z) = z := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.at_evFin_iff.1 hz
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun u => ?_) fun u => ?_
  · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compInf_singleTens, h1 u]
  · by_cases e : u = v
    · subst e
      rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
      exact (InertChart.complEquiv hw h).symm_apply_apply _
    · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_ne e, h2 u e]

end GlobalTheory.InertCoord

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem cA_ptAt (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : w.adicCompletion E) :
    cA σ (ptAt hw h z) = ptAt hw h (c z) := by
  have e1 : ∀ y : AE F E, cA σ y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e1, ptAt_apply, GlobalTheory.AdelicU.Supp.sigR_singleTens, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((InertChart.complEquiv hw h).symm z)
  change c (InertChart.complEquiv hw h ((InertChart.complEquiv hw h).symm z)) = _ at this
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

theorem inclR_mul_ptAt (x : E) (z : w.adicCompletion E) :
    inclR (F := F) (AF F) x * ptAt hw h z = ptAt hw h (algebraMap E (w.adicCompletion E) x * z) := by
  rw [mul_comm, ptAt_apply, GlobalTheory.AdelicU.Supp.singleTens_mul, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  congr 1
  change toCompl h (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [GlobalTheory.AdelicU.Supp.compFin_one_tmul, toCompl_tmul, map_one, one_mul]

end GlobalTheory.InertCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledFirstFactorMemSiegelClosure
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDblGen

theorem inlD_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv k hk
  obtain ⟨k₁, hk₁, k₂, hk₂, h₁, h₂, rfl⟩ := GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition F E σ B a a' G X om om' hT v w hv k hk
  rw [map_mul]
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₁ hk₁ h₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₂ hk₂ h₂
  rw [e₁, e₂]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s _ (Or.inr hn₁)) (s _ (Or.inl hp₁)))
    (Subgroup.mul_mem _ (s _ (Or.inr hn₂)) (s _ (Or.inl hp₂)))

end GlobalTheory.InertDblGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLawStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_localHeisenbergOperators_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  first | exact @GlobalTheory.InertRhoLaw.rho_law | exact GlobalTheory.InertRhoLaw.rho_law | (intros; apply GlobalTheory.InertRhoLaw.rho_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChartStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_vacuum_isLocalVacuum_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  first | exact @GlobalTheory.InertBridgeVac.vac_locVac | exact GlobalTheory.InertBridgeVac.vac_locVac | (intros; apply GlobalTheory.InertBridgeVac.vac_locVac <;> assumption)
end

