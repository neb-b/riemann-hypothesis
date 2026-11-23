module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EmbGramDetConjugate
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramMean

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def embGramDet {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (E : Matrix (Fin d) (Fin j) K)
    (φ : K →+* ℂ) : ℂ :=
  ((E.map φ)ᴴ * H.map φ * E.map φ).det

omit [NumberField K] [StarRing K] in
theorem embGramDet_conjugate {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    embGramDet H E (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (embGramDet H E φ) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) K),
      M.map (ComplexEmbedding.conjugate φ) = (M.map φ).map (starRingEnd ℂ) := by
    intro a b M
    ext i k
    simp [ComplexEmbedding.conjugate_coe_eq]
  unfold embGramDet
  rw [hm E, hm H, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  congr 2

omit [NumberField K] [StarRing K] in
theorem embGramDet_re_mk {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    (embGramDet H E (InfinitePlace.mk φ).embedding).re = (embGramDet H E φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, embGramDet_conjugate, Complex.conj_re]

theorem gram_eq_mul {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = (((Matrix.of e)ᵀ).map v.embedding)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) *
      ((Matrix.of e)ᵀ).map v.embedding := by
  ext a c
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, Formalism.DivisionValues.majAt_eq, metMat, cv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem map_gramR {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (e : Fin j → Fin d → K)
    (φ : K →+* ℂ) :
    φ (gramR H e) = ((((Matrix.of e)ᵀ).map (Rb.tw φ))ᴴ * H.map φ *
      ((Matrix.of e)ᵀ).map φ).det := by
  unfold gramR
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul,
    Rb.tw_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

private theorem det_gram_eq_embGramDet {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) :
    (gram X v e).det = embGramDet H ((Matrix.of e)ᵀ) v.embedding := by
  rw [gram_eq_mul, hX v]
  rfl

private theorem det_gram_re_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v : InfinitePlace K, IsUnit (X v).det)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  have hP : (((X v)⁻¹)ᴴ * (X v)⁻¹).PosDef := Rb.metMat_posDef X v (hX v)
  have hS := hP.posSemidef.conjTranspose_mul_mul_same (((Matrix.of e)ᵀ).map v.embedding)
  rw [← gram_eq_mul] at hS
  exact (Complex.le_def.mp hS.det_nonneg).1

theorem prod_norm_gramR_le (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hR : IsRatHerm (cmMax K) H X) (e : Fin j → Fin d → K) :
    ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ≤
      ∏ v : InfinitePlace K, (gram X v e).det.re := by
  have hU : ∀ v : InfinitePlace K, IsUnit (X v).det := fun v => (hR.2 v).1
  have hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding := fun v => (hR.2 v).2
  have hK0 : IsCMSub (cmMax K) := fun σ a ha => ha σ
  set E : Matrix (Fin d) (Fin j) K := (Matrix.of e)ᵀ with hE
  set g : InfinitePlace K → ℝ := fun v => (gram X v e).det.re with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => det_gram_re_nonneg' X hU e v
  have hloc : ∀ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ^ 2 ≤ g (Rb.plc v) * g v := by
    intro v
    have hPD : (H.map v.embedding).PosDef := by
      rw [← hX v]; exact Rb.metMat_posDef X v (hU v)
    have hcs := determinant_cauchy_schwarz d j (H.map v.embedding) hPD ((E.map (Rb.tw v.embedding))ᴴ)
      ((E.map v.embedding)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at hcs
    rw [map_gramR]
    have h1 : g (Rb.plc v) = (embGramDet H E (Rb.tw v.embedding)).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e, Rb.plc, embGramDet_re_mk]
    have h2 : g v = (embGramDet H E v.embedding).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e]
    rw [h1, h2]
    unfold embGramDet
    rw [Rb.Hmap_tw (cmMax K) hK0 H hR.1]
    exact hcs
  have hperm : ∏ v : InfinitePlace K, g (Rb.plc v) = ∏ v : InfinitePlace K, g v :=
    Equiv.prod_comp (Function.Involutive.toPerm _ (fun v => Rb.plc_plc v)) g
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, g v) ^ 2 := by
    have hsq2 : (∏ v : InfinitePlace K, g v) ^ 2 = ∏ v : InfinitePlace K, (g (Rb.plc v) * g v) := by
      rw [Finset.prod_mul_distrib, hperm, sq]
    rw [← Finset.prod_pow, hsq2]
    exact Finset.prod_le_prod₀ (fun v _ => by positivity) (fun v _ => hloc v)
  have ha : 0 ≤ ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ :=
    Finset.prod_nonneg fun v _ => norm_nonneg _
  have hb : 0 ≤ ∏ v : InfinitePlace K, g v := Finset.prod_nonneg fun v _ => hg0 v
  nlinarith

end GlobalTheory.GramMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
section
noncomputable section

namespace GlobalTheory.Cmp.JumpDict

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Cmp.SmallJumps

section Split

variable {Qp K LL M : Type} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
  [AddCommGroup M] [Module LL M] [Module Qp M] [IsScalarTower Qp LL M] [FiniteDimensional Qp K]

theorem finrank_eq_sum_emb (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (m : K →ₐ[Qp] Module.End LL M) (U : Submodule LL M) (hU : ∀ c, ∀ x ∈ U, m c x ∈ U)
    (E : (K →ₐ[Qp] LL) → Submodule LL M) (hE : ∀ τ x, x ∈ E τ ↔ x ∈ U ∧ ∀ c, m c x = τ c • x)
    [∀ τ, FiniteDimensional LL (E τ)] : finrank LL U = ∑ τ, finrank LL (E τ) := by
  classical
  let Φ : LL ⊗[Qp] K →ₐ[LL] ((K →ₐ[Qp] LL) → LL) :=
    Pi.algHom _ _ fun τ => Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => Commute.all _ _
  have hΦ : ∀ (a : LL) (c : K) τ, Φ (a ⊗ₜ c) τ = a * τ c := fun a c τ => by simp [Φ]
  have hsurj : Function.Surjective Φ := by
    have hli : LinearIndependent LL (fun τ : K →ₐ[Qp] LL => (τ : K → LL)) :=
      (linearIndependent_monoidHom K LL).comp (fun τ : K →ₐ[Qp] LL => (τ : K →* LL))
        (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range Φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ c, funext fun τ => by simp [hΦ, flip]⟩
    exact LinearMap.range_eq_top.1 this
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap) (by
      simp [hcard])).2 hsurj
  let Ψ : LL ⊗[Qp] K →ₐ[LL] Module.End LL M :=
    Algebra.TensorProduct.lift (Algebra.ofId LL _) m fun a c => Algebra.commutes a (m c)
  have hΨ : ∀ (a : LL) (c : K) x, Ψ (a ⊗ₜ c) x = a • m c x := fun a c x =>
    (LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId LL _) m
      (fun a c => Algebra.commutes a (m c)) a c) x).trans (by simp)
  have hΨU : ∀ z, ∀ x ∈ U, Ψ z x ∈ U := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact U.smul_mem _ (hU c x hx)
    | add y z hy hz => rw [map_add (f := _)]; exact U.add_mem hy hz
  have hΨE : ∀ τ z, ∀ x ∈ E τ, Ψ z x = Φ z τ • x := by
    intro τ z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, hΦ, ((hE τ x).1 hx).2 c, smul_smul]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, hy, hz, add_smul]
  choose e he using fun τ : K →ₐ[Qp] LL => hsurj (Pi.single τ 1)
  have he1 : ∑ τ, e τ = 1 := hinj (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : LL)))
  have he2 : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := fun τ c => hinj (by
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [hΦ]
    · simp [h])
  have hmem : ∀ τ, ∀ x ∈ U, Ψ (e τ) x ∈ E τ := fun τ x hx =>
    (hE τ _).2 ⟨hΨU _ x hx, fun c => by
      have := congrArg (fun z => Ψ z x) (he2 τ c)
      simpa only [map_mul, map_smul, Module.End.mul_apply, hΨ, one_smul, LinearMap.smul_apply] using this⟩
  let f : U ≃ₗ[LL] (∀ τ, E τ) :=
    { toFun := fun x τ => ⟨Ψ (e τ) x, hmem τ x x.2⟩
      map_add' := fun x y => funext fun τ => Subtype.ext (by simp)
      map_smul' := fun a x => funext fun τ => Subtype.ext (by simp)
      invFun := fun y => ⟨∑ τ, (y τ : M), U.sum_mem fun τ _ => ((hE τ _).1 (y τ).2).1⟩
      left_inv := fun x => Subtype.ext (by
        change ∑ τ, Ψ (e τ) x = x
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← LinearMap.sum_apply, ← map_sum, he1, map_one, Module.End.one_apply])
      right_inv := fun y => funext fun τ => Subtype.ext (by
        change Ψ (e τ) (∑ σ, (y σ : M)) = y τ
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single τ]
        · rw [hΨE τ _ _ (y τ).2, he]; simp
        · intro σ _ h
          rw [hΨE σ _ _ (y σ).2, he]; simp [h]
        · simp) }
  rw [f.finrank_eq, Module.finrank_pi_fintype]

end Split

theorem finrank_eq_one_of_jump {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) [FiniteDimensional L U] (le : ∀ a, F a ≤ U) (anti : ∀ a, F (a + 1) ≤ F a)
    (exh : ∀ x ∈ U, ∃ a, x ∈ F a) (sep : ∀ x, (∀ a, x ∈ F a) → x = 0) (a₀ : ℤ)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = if a = a₀ then 1 else 0) :
    finrank L U = 1 := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  haveI : ∀ a, FiniteDimensional L (F a) := fun a => Submodule.finiteDimensional_of_le (le a)
  have hs : ∀ a, a ≠ a₀ → F (a + 1) = F a := fun a ha =>
    Submodule.eq_of_le_of_finrank_eq (anti a) (by have := h a; rw [if_neg ha] at this; omega)
  have hlo : ∀ a ≤ a₀, F a = F a₀ := by
    intro a ha
    induction a, ha using Int.leInductionDown with
    | base => rfl
    | pred a ha ih => rw [← ih, ← hs (a - 1) (by omega), sub_add_cancel]
  have hhi : ∀ a, a₀ + 1 ≤ a → F a = F (a₀ + 1) := by
    intro a ha
    induction a, ha using Int.leInduction with
    | base => rfl
    | succ a ha ih => rw [← ih, hs a (by omega)]
  have h1 : U = F a₀ := le_antisymm (fun x hx => by
    obtain ⟨a, ha⟩ := exh x hx
    rcases le_total a a₀ with hab | hab
    · rwa [← hlo a hab]
    · exact hA hab ha) (le _)
  have h2 : F (a₀ + 1) = ⊥ := eq_bot_iff.2 fun x hx => sep x fun a => by
    rcases le_total a (a₀ + 1) with hab | hab
    · exact hA hab hx
    · rwa [hhi a hab]
  have h3 := h a₀
  rw [h2, if_pos rfl, finrank_bot] at h3
  rw [h1]
  omega

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := BdR) b).injective
  rw [map_zero]
  ext i
  refine PD.Fil_sep _ fun a => ?_
  obtain ⟨y, rfl⟩ := hx a
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    have : (equivFinsuppOfBasisLeft (N := BdR) b) (v ⊗ₜ (c : BdR)) i ∈ PD.Fil a := by
      rw [equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ c.2
    exact this
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]; exact Submodule.add_mem _ hy hz

theorem finrank_ddR_of_one_jump [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V)
    (h : ∀ τ : K →ₐ[Qp] LL, ∃ a₀ : ℤ, ∀ a, multV PD ρ τ a = if a = a₀ then 1 else 0) :
    finrank LL (DdR PD ρ) = finrank Qp K := by
  choose a₀ h using h
  haveI : ∀ τ, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    finite_ddRE_of_multV PD ρ τ {a₀ τ} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have h1 : ∀ τ, finrank LL (DdRE PD ρ τ) = 1 := fun τ =>
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left)
      (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) (a₀ τ) (h τ)
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [finrank_eq_sum_emb hcard m (DdR PD ρ) (fun c x hx => (hD _).2 fun g => by rw [hc, (hD x).1 hx g])
    (DdRE PD ρ) (fun τ x => by
      simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rfl)]
  simp [h1, hcard]

end Periods

variable (D : D7)

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Local

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.Cmp.JumpDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConj
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_coeff_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω),
    ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω),
      IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s
  obtain ⟨e, he_inj, he⟩ := _root_.GlobalTheory.FN.expansion_injective_ringHom Ω ε
  have hmem := (_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1
  have key : ∀ t : Ω ≃+* Ω, ∃ c : ring ε.range → ring ε.range, ∀ a,
      (∀ r, (e (c a)).coeff r = t ((e a).coeff r)) ∧
      ∀ h h' : HahnSeries ℚ Ω, IsExp ε a h → IsExp ε (c a : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
    intro t
    have hex : ∀ a : ring ε.range, ∃ b : ring ε.range, ∀ h h' : HahnSeries ℚ Ω,
        IsExp ε a h → IsExp ε (b : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
      intro a
      obtain ⟨f', hf', hp⟩ := _root_.GlobalTheory.FN.exists_conj_of_inR Ω ε t a ((hmem a).1 a.2)
      exact ⟨⟨f', (hmem f').2 hf'⟩, hp⟩
    choose c hc using hex
    exact ⟨c, fun a => ⟨hc a (e a) (e (c a)) (he a) (he (c a)), hc a⟩⟩
  have mapc : ∀ t : Ω ≃+* Ω, ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω, ∀ h r, (Φ h).coeff r = t (h.coeff r) := by
    intro t
    obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω t.toRingHom 1 (fun _ => 1) one_pos rfl (by simp)
    exact ⟨Φ, fun h r => by simpa using hΦ h r⟩
  obtain ⟨c, hc⟩ := key s
  obtain ⟨d, hd⟩ := key s.symm
  obtain ⟨Φ, hΦ⟩ := mapc s
  have ec : ∀ a, e (c a) = Φ (e a) := fun a => by
    ext r
    rw [(hc a).1, hΦ]
  refine ⟨{ toFun := c, invFun := d, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_mul' := ?_ },
    fun a h h' => (hc a).2 h h'⟩
  · intro a
    apply he_inj
    ext r
    rw [(hd _).1, (hc a).1]
    simp
  · intro a
    apply he_inj
    ext r
    rw [(hc _).1, (hd a).1]
    simp
  · intro a b
    apply he_inj
    simp only [map_mul, ec]
  · intro a b
    apply he_inj
    simp only [map_add (f := _), ec]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankLeFinrankDirectSumBelow
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem finrank_nablaSq_eq_card (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Module.finrank K (nablaSq K N lam) = Nat.card (ssIdx N N lam.natW) := by
  obtain ⟨b, ⟨hli, hb, -⟩, -⟩ := sSBasis K N N lam.natW
  have : Finite (ssIdx N N lam.natW) := (sSIdxFinite N N _).to_subtype
  have := Fintype.ofFinite (ssIdx N N lam.natW)
  unfold nablaSq
  rw [← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

theorem finrank_le_finrank_directSum_below (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    Module.finrank ℂ (nablaSq ℂ N lam) ≤ Module.finrank ℂ (⨁ mu : Below h lam, nablaSq ℂ n mu.1) := by
  obtain ⟨F, hF⟩ := GlobalTheory.Branching.exists_ssIdx_injective n N h lam
  have := Fintype.ofFinite (Below h lam)
  have : ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW) := fun mu => (sSIdxFinite n n _).to_subtype
  rw [Module.finrank_directSum, finrank_nablaSq_eq_card]
  simp only [finrank_nablaSq_eq_card]
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective F hF

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSelfDualEColLatOne
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat.Inhabitant

theorem colLat_one_eq {K : Type} [Field K] [NumberField K] {n : ℕ} :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (algebraMap (𝓞 K) K).range := by
  rw [colLat_one_eq, Module.Basis.mem_span_iff_repr_mem]
  simp

end GlobalTheory.TestLat.Inhabitant
end

