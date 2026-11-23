module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCore
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.GlobImage
variable {D : D7}

theorem mulVec_mem {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem infPart_pure (α : Af D.host.F) (e : D.host.E) :
    infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = 0 := by
  unfold infPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  have : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compFin_pure (w : Pl D) (α : Af D.host.F) (e : D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] e) = (evalV D.host.F w α) ⊗ₜ[D.host.F] e := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem compAt_pure (w : Pl D) (α : Af D.host.F) (e : D.host.E) :
    compAt D w ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = (evalV D.host.F w α) ⊗ₜ[D.host.F] e := by
  unfold compAt
  rw [RingHom.comp_apply, finPart_pure, compFin_pure]

theorem pure_mem (P : Pl D → Prop) (α : Af D.host.F) (hα : ∀ v, ¬ P v → evalV D.host.F v α = 0) (e : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e ∈ idAt D P := by
  refine Ideal.mem_inf.2 ⟨?_, ?_⟩
  · rw [RingHom.mem_ker, infPart_pure]
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    rw [RingHom.mem_ker, compAt_pure, hα w.1 w.2, TensorProduct.zero_tmul]

theorem latV_supp : ∀ (D : D7) (S : HSp D) (M : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    y ∈ latV S M P → ∀ i, y i ∈ idAt D P := by
  intro D S M P y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, -, hα, a, ha, x, -, rfl⟩ := hz
    exact fun i => pure_mem P α hα _
  | zero => exact fun i => (idAt D P).zero_mem
  | add a b _ _ ha hb => exact fun i => (idAt D P).add_mem (ha i) (hb i)
  | neg a _ ha => exact fun i => (idAt D P).neg_mem (ha i)

theorem latV_toHat : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice
theorem latV_ofHat : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice
theorem finRep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := _root_.GlobalTheory.GlobFin.fin_rep

theorem latV_iff_hat (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨latV_toHat D S L P y, latV_ofHat D S L P y hy⟩

theorem finE_mulVec (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

set_option maxHeartbeats 400000 in
theorem image_moves (S : HSp D) (L : Lat S) (hL : IsSelfDualC S L) (g : GA D S) :
    ∃ M : Lat S, IsSelfDualC S M ∧ ∀ P : Pl D → Prop, Moves S g L M P := by
  obtain ⟨x, hx, hgx⟩ := finRep D S g
  have hI := GlobalTheory.AdIsomImage.imageSt D S L hL x hx
  obtain ⟨⟨M, hMl, hM⟩, hsd⟩ := hI
  refine ⟨M, hsd M hMl hM, fun P y hy => ?_⟩
  have hy' : ∀ i, (mt S x *ᵥ y) i ∈ idAt D P := mulVec_mem _ hy
  rw [hgx P y hy, latV_iff_hat S L P y hy, latV_iff_hat S M P _ hy', finE_mulVec]
  show _ ∈ Formalism.L2.Herm.hatL L ↔ _ ∈ Formalism.L2.Herm.hatL M
  rw [hM, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

section Gen
variable {R : Type} [CommRing R] {m n l : ℕ}
theorem mulVec_col (A : Matrix (Fin l) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) (i : Fin n) (a : R) :
    A *ᵥ (fun k => a * x k i) = fun k => a * (A * x) k i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mulVec_eq_sum (x : Matrix (Fin m) (Fin n) R) (w : Fin n → R) :
    x *ᵥ w = ∑ i, fun k => w i * x k i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by ring
end Gen

theorem colMul_eq {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : colMul x i a = fun k => a * x k i := rfl

set_option maxHeartbeats 400000 in
theorem supp_of {S : HSp D} {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S) (M₀ : Lat S₀) (v : Pl D)
    (y : Fin S.rank → AE D)
    (hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S M (· = v))
    (hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S M (· = v)) (h0' : d.p0 *ᵥ y ∈ latV S₀ M₀ (· = v)) :
    ∀ k, y k ∈ idAt D (· = v) := by
  intro k
  have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
      d.sum_eq_one, Matrix.one_mulVec]
  rw [e, Pi.add_apply, Pi.add_apply]
  refine add_mem (add_mem ?_ (mulVec_mem _ (latV_supp D S₀ M₀ _ _ h0') k)) ?_
  · rw [mulVec_eq_sum, Finset.sum_apply]
    exact Ideal.sum_mem _ fun i _ => latV_supp D S M _ _ (hX i) k
  · rw [mulVec_eq_sum, Finset.sum_apply]
    exact Ideal.sum_mem _ fun i _ => latV_supp D S M _ _ (hY i) k

set_option maxHeartbeats 400000 in
theorem col_iff {S : HSp D} (L M : Lat S) (g : GA D S) (v : Pl D) {n : ℕ} (x : Mx D S.rank n)
    (hg : HMul.hMul (mt S g) x = x) (h1 : Moves S g L M (· = v)) (i : Fin n) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    colMul x i a ∈ latV S L (· = v) ↔ colMul x i a ∈ latV S M (· = v) := by
  have hs : ∀ k, colMul x i a k ∈ idAt D (· = v) := fun k => (idAt D _).mul_mem_right _ ha
  rw [h1 _ hs, colMul_eq, mulVec_col, hg]

set_option maxHeartbeats 400000 in
theorem wittEmbedding_carries_latticeCompletion (S : HSp D) (L : Lat S) (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ M₀ : Lat S₀) (M : Lat S)
    (γ : GA D S₀) (v : Pl D) (hL : MonoAt d L L₀ v) (h0 : Moves S₀ γ L₀ M₀ (· = v))
    (h1 : Moves S (d.emb0 γ) L M (· = v)) : MonoAt d M M₀ v := by
  intro y
  by_cases hy : ∀ k, y k ∈ idAt D (· = v)
  · have hy' : ∀ k, (mt S (d.emb0 γ⁻¹) *ᵥ y) k ∈ idAt D (· = v) := mulVec_mem _ hy
    have hgy : mt S (d.emb0 γ) *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.one_mulVec]
    have hX' : d.pX *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have hY' : d.pY *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have h0y : d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = mt S₀ γ⁻¹ *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
    have hp0 : ∀ k, (d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y)) k ∈ idAt D (· = v) := mulVec_mem _ hy'
    have hcore : d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) ∈ latV S₀ L₀ (· = v) ↔ d.p0 *ᵥ y ∈ latV S₀ M₀ (· = v) := by
      rw [h0 _ hp0, h0y, Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have key := h1 _ hy'
    rw [hgy] at key
    rw [← key, hL, hX', hY', hcore]
    exact and_congr (forall_congr' fun i => col_iff L M _ v d.jX (d.wittDecomp_anisotropicEmbedding_inclX γ) h1 i _ (mulVec_mem _ hy i))
      (and_congr (forall_congr' fun i => col_iff L M _ v d.jY (d.wittDecomp_anisotropicEmbedding_inclY γ) h1 i _ (mulVec_mem _ hy i)) Iff.rfl)
  · constructor
    · intro h; exact absurd (latV_supp D S M _ y h) hy
    · rintro ⟨hX, hY, h0'⟩; exact absurd (supp_of d M M₀ v y hX hY h0') hy

theorem glob : ∀ (D : D7) (S : HSp D) (L : Lat S), IsSelfDualC S L → (∀ g : GA D S, ∃ M : Lat S, IsSelfDualC S M ∧ ∀ P : Pl D → Prop, Moves S g L M P) ∧ ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ M₀ : Lat S₀) (M : Lat S) (γ : GA D S₀) (v : Pl D), MonoAt d L L₀ v → Moves S₀ γ L₀ M₀ (· = v) → Moves S (d.emb0 γ) L M (· = v) → MonoAt d M M₀ v :=
  fun _ S L hL => ⟨image_moves S L hL, fun S₀ ρ d L₀ M₀ M γ v => wittEmbedding_carries_latticeCompletion S L S₀ ρ d L₀ M₀ M γ v⟩

end GlobalTheory.FinPl.GlobImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOne
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped Topology

noncomputable section

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

theorem eq_zero_of_le_pow {γ t : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (h : ∀ m : ℕ, t ≤ γ ^ m) : t = 0 := by
  by_contra ht
  by_cases hγ0 : γ = 0
  · have := h 1
    rw [hγ0, pow_one] at this
    exact ht (le_antisymm this zero_le')
  have hg : γ.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hγ0]
    simpa using hγ
  set N : ℕ := (-t.log).toNat + 1 with hN
  have hm : t.log ≤ (N : ℤ) * γ.log := by
    have h3 : WithZero.exp t.log ≤ WithZero.exp (N • γ.log) := by
      rw [WithZero.exp_nsmul, WithZero.exp_log ht, WithZero.exp_log hγ0]
      exact h N
    rw [WithZero.exp_le_exp, nsmul_eq_mul] at h3
    exact h3
  have h1 : (N : ℤ) * γ.log ≤ -(N : ℤ) := by
    have : (0 : ℤ) ≤ (N : ℤ) := by positivity
    nlinarith
  have h2 := Int.self_le_toNat (-t.log)
  have h4 : (N : ℤ) = ((-t.log).toNat : ℤ) + 1 := by rw [hN]; push_cast; ring
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmallAt (Q : Finset (HeightOneSpectrum (𝓞 E))) (d : ℕ) : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  {a | (∀ w ∉ Q, adAt F w a = 0) ∧ ∀ w ∈ Q, Valued.v (adAt F w a) ≤ WithZero.exp (-(d : ℤ))}

theorem exists_smallAt_subset (Q : Finset (HeightOneSpectrum (𝓞 E))) {V : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hV : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      V ∈ 𝓝 (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : ℕ, SmallAt (F := F) Q d ⊆ V := by
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI := Formalism.L2.Col.adeles_t2Space (F := F) (E := E)
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : 𝓞 E, β ≠ 0 ∧ ∀ P ∈ Q, β ∈ P.asIdeal := by
    choose f hf hf0 using fun P : HeightOneSpectrum (𝓞 E) => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact ⟨∏ P ∈ Q, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP =>
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)⟩
  set b : E := algebraMap (𝓞 E) E β with hb
  have hb0 : b ≠ 0 := by simpa [hb] using hβ0
  let ι : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
  set e : E ⊗[F] FiniteAdeleRing (𝓞 F) F := ∑ P ∈ Q, PtExist.idem F P with he_def
  have he : ∀ w, adAt F w e = if w ∈ Q then 1 else 0 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he_def, map_sum]
    simp only [PtExist.adAt_idem]
    exact Finset.sum_ite_eq Q w (fun _ => (1 : w.adicCompletion E))
  have hint : ∀ y ∈ Formalism.L2.Herm.intAf F E, ∀ w, Valued.v (adAt F w y) ≤ 1 := fun y hy w =>
    (mem_rInt_iff F E y).1 hy w
  have hbw : ∀ w ∈ Q, Valued.v (adAt F w (ι b)) < 1 := fun w hw => by
    rw [adAt_inclE, valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 (hβ w hw)
  have hbne : ∀ w, adAt F w (ι b) ≠ 0 := fun w => by
    rw [adAt_inclE]
    exact (map_ne_zero _).2 hb0
  let c : ℕ → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun m => e * ι b ^ m
  let K : ℕ → Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := fun m => (c m * ·) '' (Formalism.L2.Herm.intAf F E : Set _)
  have hKc : ∀ m, IsCompact (K m) := fun m => Formalism.L2.Col.rlt_isCompact_intAf.image (continuous_const_mul (c m))
  have hKa : Antitone K := by
    refine antitone_nat_of_succ_le fun m => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨ι b * y, mul_mem (Formalism.L2.Col.iA_mem β) hy, ?_⟩
    simp only [c, pow_succ]
    ring
  have hK0 : ∀ x ∈ ⋂ m, K m, V ∈ 𝓝 x := by
    intro x hx
    have : x = 0 := by
      refine PtExist.ad_ext fun w => ?_
      rw [map_zero]
      by_cases hw : w ∈ Q
      · have h0 : Valued.v (adAt F w x) = 0 := eq_zero_of_le_pow (hbw w hw) fun m => by
          obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.1 hx m
          rw [← hxy]
          simp only [c, map_mul, map_pow, he, if_pos hw, one_mul]
          exact mul_le_of_le_one_right' (hint y hy w)
        exact (Valuation.zero_iff _).1 h0
      · obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.1 hx 0
        simp only [c, map_mul, he, if_neg hw, zero_mul]
    rw [this]
    exact hV
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact hKa.directed_ge hKc (mem_nhdsSet_iff_forall.2 hK0)

  let D : ℕ := ∑ w ∈ Q, (-(Valued.v (adAt F w (ι b))).log).toNat
  have hD : ∀ w ∈ Q, WithZero.exp (-(D : ℤ)) ≤ Valued.v (adAt F w (ι b)) := fun w hw => by
    have h0 : Valued.v (adAt F w (ι b)) ≠ 0 := (Valuation.ne_zero_iff _).2 (hbne w)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    have h1 : (-(Valued.v (adAt F w (ι b))).log).toNat ≤ D :=
      Finset.single_le_sum (f := fun w => (-(Valued.v (adAt F w (ι b))).log).toNat) (fun _ _ => Nat.zero_le _) hw
    have h2 := Int.self_le_toNat (-(Valued.v (adAt F w (ι b))).log)
    omega
  refine ⟨m * D, fun a ha => hm ?_⟩
  have hinv : ∀ w, adAt F w (ι b⁻¹) = (adAt F w (ι b))⁻¹ := fun w => by
    rw [adAt_inclE, adAt_inclE, map_inv₀]
  refine ⟨e * ι b⁻¹ ^ m * a, (mem_rInt_iff F E _).2 fun w => ?_, ?_⟩
  · show Valued.v (adAt F w _) ≤ 1
    by_cases hw : w ∈ Q
    · simp only [map_mul, map_pow, he, hinv, if_pos hw, one_mul, map_inv₀, inv_pow, map_one]
      have hv : 0 < Valued.v (adAt F w (ι b)) ^ m :=
        pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hbne w))) m
      rw [inv_mul_le_one₀ hv]
      refine (ha.2 w hw).trans ?_
      have : WithZero.exp (-((m * D : ℕ) : ℤ)) = WithZero.exp (-(D : ℤ)) ^ m := by
        rw [← WithZero.exp_nsmul]
        congr 1
        push_cast
        ring
      rw [this]
      exact pow_le_pow_left₀ zero_le' (hD w hw) m
    · rw [map_mul, ha.1 w hw, mul_zero, map_zero]
      exact zero_le'
  · refine PtExist.ad_ext fun w => ?_
    simp only [c, map_mul, map_pow, he, hinv]
    by_cases hw : w ∈ Q
    · rw [if_pos hw, one_mul, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hbne w), one_pow, one_mul]
    · rw [ha.1 w hw, mul_zero, mul_zero]

end GlobalTheory.LevelApprox

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_entry_sub_one {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin n) :
    adAt F w ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) = (locM w z - 1) i j := by
  rw [map_sub, Matrix.sub_apply]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem entry_mem_smallAt {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} {d : ℕ}
    {z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h1 : ∀ w ∉ Q, locM w z = 1)
    (h2 : ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1)) (i j : Fin n) :
    (z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j ∈ SmallAt (F := F) Q d := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [adAt_entry_sub_one, h1 w hw, sub_self, Matrix.zero_apply]
  · rw [adAt_entry_sub_one]
    exact h2 w hw i j

theorem mem_U_of_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) →
    (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧
      GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  intro F E _ _ _ _ _ σ n J T f bad S Q
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  let A : ℕ → Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := fun d => {z | (∀ w ∉ Q, locM w z = 1) ∧
    ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z⁻¹ - 1)}
  have hexp : Antitone fun d : ℕ => WithZero.exp (-(d : ℤ)) := fun a b h =>
    WithZero.exp_le_exp.2 (by simpa using h)
  have hA : Antitone A := fun a b h z hz => ⟨hz.1, fun w hw => ⟨(hz.2 w hw).1.mono (hexp h), (hz.2 w hw).2.mono (hexp h)⟩⟩
  have hinv1 : ∀ z ∈ A 0, ∀ w ∉ Q, locM w z⁻¹ = 1 := fun z hz w hw => by
    have := locM_mul (P := w) z z⁻¹
    rw [mul_inv_cancel, locM_one, hz.1 w hw, one_mul] at this
    exact this.symm
  let G : Filter (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := ⨅ d, Filter.principal (A d)
  have hsmall : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ d, ∀ z ∈ A d, g z ∈ SmallAt (F := F) Q d) → Filter.Tendsto g G (𝓝 0) := fun g hg V hV => by
    obtain ⟨d, hd⟩ := exists_smallAt_subset (F := F) Q hV
    exact Filter.mem_iInf_of_mem d (Filter.mem_principal.2 fun z hz => hd (hg d z hz))
  have hentry : ∀ (M : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      (∀ i j, Filter.Tendsto (fun z => M z i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) G (𝓝 0)) →
      Filter.Tendsto M G (𝓝 1) := fun M hM =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
      have := (hM i j).add_const ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j)
      simpa using this
  have hT : Filter.Tendsto id G (𝓝 (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · refine hentry _ fun i j => hsmall _ fun d z hz => entry_mem_smallAt hz.1 (fun w hw => (hz.2 w hw).1) i j
    · refine hentry (fun z => ((z⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) fun i j => hsmall _ fun d z hz => ?_
      exact entry_mem_smallAt (fun w hw => hinv1 z (hA (Nat.zero_le d) hz) w hw) (fun w hw => (hz.2 w hw).2) i j
  have h1 : {x : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} ∈
      𝓝 (1 : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := S.U_open.mem_nhds S.U.one_mem
  obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 h1
  have hdir : Directed (· ≥ ·) fun d => Filter.principal (A d) :=
    Antitone.directed_ge (f := fun d => Filter.principal (A d)) fun a b h => Filter.principal_mono.2 (hA h)
  obtain ⟨d, hd⟩ := (Filter.mem_iInf_of_directed hdir _).1 (hT ht)
  exact ⟨d, fun z hz h1 h2 => hts (show (⟨z, hz⟩ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ Subtype.val ⁻¹' t from
    hd ⟨h1, h2⟩)⟩

end GlobalTheory.LevelApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChainFr

namespace GlobalTheory.Corev.LiftUp

theorem liftUp_mult : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  intro hDS hHC hCD hCW D k V W S S' M M' θ ψ ω f hS hS' hθ hch hω hf ν 𝓕 hν h𝓕
  subst hS hS'
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hIn : Inputs D X := _root_.GlobalTheory.PairLift.inputs_of_chosenSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (_root_.GlobalTheory.PairLift.cuspAll_of_lowAll D X hIn (_root_.GlobalTheory.PairLift.lowAll_of_lowFock D X hIn (_root_.GlobalTheory.LowerMembersRule.lowFock D X hIn)))
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hadj : AdjLaw ψ V W := _root_.GlobalTheory.AdjLawPf.adjLaw D ψ hstd V W
  have h0 : adjO V W 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := _root_.GlobalTheory.WeilConj.exists_conj_weilDatum D ψ V W χS χT ω hW
  obtain ⟨j, -, hj⟩ := _root_.GlobalTheory.FockAdjoint.fock_dag D ψ θ hstd hθ V W (Fr.ofModel M) (Fr.ofModel M')
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hf)
  have hω'e : IsWeilExp ψ W V (expT D k) (expS D k) ω' :=
    ⟨χT, χS, hW', fun τ => ⟨(hexp τ).2, (hexp τ).1⟩⟩
  have hne : dag V W f ≠ 0 := by
    intro hz
    apply hf.ne
    funext x
    have hx := congrFun hz (adjO W V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec ψ θ M' M (dag V W f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := _root_.GlobalTheory.Chain.RealIt.itPairUp hDS hHC D k V W _ _ M M' θ ψ rfl rfl hθ hch
  have hItW := hIt ω' (dag V W f) hω'e hf'
  have hrule : ∀ τ, RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) :=
    fun τ => (_root_.GlobalTheory.StepRule.rulePar_step D X h3 h4 h5 k hch τ).2
  have hL := hPL _ _ _ _ hrule W V M' M θ ψ hθ ω' hω'e (dag V W f) It hf' hItW ν 𝓕 hν h𝓕 (dag V W f)
    (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v => _root_.GlobalTheory.ItKFin.itKFin D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW (j P) v,
    ?_, ?_⟩
  · refine (_root_.GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW).trans
      (Submodule.span_mono ?_)
    rintro w ⟨P, v, hv, rfl⟩
    exact ⟨j.symm P, v, hv, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf ψ θ M M' f P)) =
        thetaKO ω' h g (ptOf ψ θ M' M (dag V W f) (j P)) := by
      intro g
      have e1 : ptOf ψ θ M' M (dag V W f) (j P) = dag V W (ptOf ψ θ M M' f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.Corev.LiftUp

end
end

