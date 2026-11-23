module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.AbsIrrOfAlgClosed

theorem span_restrict_eq_top_of_isIrrSub_map {k Γ L : Type} [Field k] [Group Γ] [Field L]
    [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W)
    (habs : IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))))) :
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  classical
  letI : Algebra k L := f.toAlgebra
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun
  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl
  let Li : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective Li := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' Li
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = Li c := fun c => LinearMap.toMatrix'_mulVec Li c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  have hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f)
      (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) =
      fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L) := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

theorem absIrrSub_of_isIrrSub_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L]
    (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W →
    IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) →
    AbsIrrSub ρ W := by
  intro k Γ L _ _ _ _ f a ρ W hinv hirr
  have hW : Stable (matRep ((Units.coeHom _).comp ρ)) W := fun g v hv => by
    have := hinv g v hv
    simpa [GlobalTheory.BurnsideSub.matRep_apply] using this
  have hne : W ≠ ⊥ := by
    intro h0
    apply hirr.1
    rw [h0]
    simp
  have hsp := span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr
  unfold AbsIrrSub
  exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp

end GlobalTheory.AbsIrrOfAlgClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvForm
section
open NumberField

namespace GlobalTheory

theorem algWt_exists_invForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  intro L _ _ _ n a
  exact _root_.GlobalTheory.InvFormBdd.exists_isInvForm L n a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
section
open Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem

namespace GlobalTheory.Mem.Col2

theorem fOk_of_fieldsOk {X : Fields} (hX : X.Ok) (σ : X.K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) :
    FOk X.emb σ :=
  ⟨hX.conjE, hX.emb_star, hσ⟩

theorem base_fOk (B : Base) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  fOk_of_fieldsOk (GlobalTheory.Mem.FieldsLaws.fields_ok B) B.embLL B.starLL_cx

theorem base_fields_primes_ok : ∀ (B : Base) (X : PreX B.toPre),
    B.fields.Ok ∧ (B.primes X).Ok ∧ B.wts.Ok ∧ (letI := B.host.cmStar; FOk B.tauLL B.embLL) ∧
      2 * B.fields.f * B.R.k < (B.primes X).g 0 - 1 := fun B X =>
  ⟨GlobalTheory.Mem.FieldsLaws.fields_ok B, (GlobalTheory.BasePrimes.primes_ok B X).1,
    { row_ok τ := ⟨B.hc τ, rfl⟩
      hc_row u τ := by
        show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
        unfold RowPar.of
        rw [B.hcW_v, B.hcW_b, B.hcW_e]
      u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
      u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm },
    base_fOk B, by rw [B.fields_f]; exact X.g_big 0⟩

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CdScaleEqCdScaleOf
section
open Formalism.BasicNotions

namespace GlobalTheory.Mem.SRe

theorem cdScale_eq_cdScaleOf : ∀ D : D7, cdScaleTie D → D.s.cdScale = Formalism.L2.SG.PairVal.cdScaleOf D := by
  intro D h
  exact GlobalTheory.Mem.Vol.Scale.cdScaleIs_unique D.cd ((GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 h)
    (fun n ε => (Formalism.L2.SG.PairVal.cdScaleOf_tie D (Formalism.L2.SG.PairVal.cdScaleExists_of_tie D h) n ε).2)

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumPosHerm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open scoped ComplexOrder

namespace GlobalTheory.Mem.Col2.ClassSumPos

theorem ipVal_pos {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) (hf : f ∈ ValC (Gr emb σ n) lam) (h0 : f ≠ 0) :
    0 < ipVal emb σ lam f f := by
  obtain ⟨P, -, rfl⟩ := hf
  have hP : P ≠ 0 := by
    rintro rfl
    exact h0 (map_zero _)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    show (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ = 1
    exact inv_one
  have h1 := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) P
  rw [e] at h1
  unfold ipVal
  rw [ipFr_apply, h1, ← nfL_apply]
  exact ps_nfL_pos lam P hP

theorem ipVal_herm {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (φ ψ : Fr emb σ n → ℂ) :
    ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  unfold ipVal
  rw [ipFr_apply, ipFr_apply, ← nfL_apply, ← nfL_apply, starRingEnd_apply, ps_nfL_symm]

theorem classSum_pos_herm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ [Fintype S.Cl], (∀ φ ∈ S.Fi emb σ lam, φ ≠ 0 → 0 < (∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c)).re) ∧ ∀ φ ψ : Fr emb σ n → ℂ, ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam _ hS _
  refine ⟨fun φ hφ h0 => ?_, ipVal_herm emb σ lam⟩
  have hw : ∀ c : S.Cl, (0 : ℂ) < ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ := fun c => by
    haveI := hS.fin_stab c.1 (S.rep c)
    have hc : (0 : ℝ) < ((Nat.card (S.Stab c) : ℕ) : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
    have := Complex.zero_lt_real.2 hc
    simpa using this
  have hpos : (0 : ℂ) < ∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c) := by
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 h0
    refine Finset.sum_pos' (fun c _ => ?_) ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (ipVal_pos emb σ lam _ (hφ c0).1 hc0)⟩
    by_cases h : φ c = 0
    · rw [h, map_zero, mul_zero]
    · exact (mul_pos (hw c) (ipVal_pos emb σ lam _ (hφ c).1 h)).le
  exact (Complex.lt_def.1 hpos).1

end GlobalTheory.Mem.Col2.ClassSumPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingDualWeyl
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducingSym

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

private theorem det_mul_eq_sum_det_submatrix_mul_prod {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ p : Fin h → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp_rw [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.submatrix_apply, id, Finset.prod_mul_distrib]
  ring

private theorem sum_perm_det_submatrix_mul_prod_eq_det_mul_det {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) (e : Fin h ↪o Fin n) :
    ∑ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  have hA : ∀ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det =
      Equiv.Perm.sign τ * (A.submatrix id e).det := fun τ => by
    rw [← Matrix.det_permute' τ (A.submatrix id e), Matrix.submatrix_submatrix]
    rfl
  simp_rw [hA, Matrix.det_apply' (B.submatrix e id), Finset.mul_sum, Matrix.submatrix_apply, id]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem cauchyBinet_oe {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  rw [det_mul_eq_sum_det_submatrix_mul_prod]
  simp_rw [← sum_perm_det_submatrix_mul_prod_eq_det_mul_det A B]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⇑x.1 ∘ ⇑x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨e, τ⟩ _ _ ⟨e', τ'⟩ _ _ hx
    have hr : Set.range ⇑e = Set.range ⇑e' := by
      have h1 : Set.range (⇑e ∘ ⇑τ) = Set.range (⇑e' ∘ ⇑τ') := congrArg Set.range hx
      rwa [τ.surjective.range_comp, τ'.surjective.range_comp] at h1
    obtain rfl : e = e' := OrderEmbedding.range_inj.mp hr
    obtain rfl : τ = τ' := Equiv.ext fun i => e.injective (congrFun hx i)
    rfl
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      apply hp
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, id, hij]),
        zero_mul]
    have hc : (Finset.univ.image p).card = h := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, ∃ j, (Finset.univ.image p).orderEmbOfFin hc j = p i := by
      intro i
      have : p i ∈ Set.range ((Finset.univ.image p).orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        simp
      exact this
    choose t ht using hmem
    have tinj : Function.Injective t := by
      intro i j hij
      apply hinj
      rw [← ht i, ← ht j, hij]
    have tbij : Function.Bijective t := Finite.injective_iff_bijective.mp tinj
    have hp' : ⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij) = p :=
      funext ht
    refine ⟨((Finset.univ.image p).orderEmbOfFin hc, Equiv.ofBijective t tbij), Finset.mem_univ _, ?_, hp'⟩
    show (A.submatrix id (⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij))).det *
      ∏ i, B ((⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij)) i) i ≠ 0
    rw [hp']
    exact hp
  · intro x _ _
    rfl

theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  have h1 : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose
      (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ((Matrix.of fun (p : Fin h) (b : Fin N) => (C (x (b, Fin.castLE hh p)) : MvPolynomial (Fin N × Fin N) ℚ)) *
        Matrix.of fun (b : Fin N) (q : Fin h) => (X (b, Fin.castLE hh q) : MvPolynomial (Fin N × Fin N) ℚ)).det := by
    rw [initMinor, AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, aeval_X]
  rw [h1, cauchyBinet_oe]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  rw [initMinor, RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp

theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hb := bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
    (fun c => Fin.castLE (colLen_le hY c)) (fun _ _ => rfl)
  rw [shapeDeg_colLen] at hb
  rw [← hb, bideterminant, map_prod]
  simp only [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [colProd, bideterminant, map_prod, Finset.prod_mul_distrib]

theorem reproducing_left : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ),
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) →
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f := by
  intro N Y hY f hf
  have hsum : ∀ {ι : Type} (s : Finset ι) (F : ι → MvPolynomial (Fin N × Fin N) ℚ)
      (g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g :=
    fun s F g => map_sum (AddMonoidHom.mk' (fun p => fockQ p g)
      (fun a b => (Formalism.GradedWeylDivisibility.fockQBilin _ a b g 0).1)) F s
  have hsmul : ∀ (c : ℚ) (p g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (c • p) g = c * fockQ p g :=
    fun c p g => (Formalism.GradedWeylDivisibility.fockQBilin _ p p g c).2
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  apply MvPolynomial.funext
  intro x
  have hev : eval (idFrame ℚ N N) (rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)) f) = eval x f := by
    have hcomp : (aeval (idFrame ℚ N N)).comp (rowAct ℚ (n := N) (Matrix.of fun a s : Fin N => x (a, s))) =
        aeval x := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [rowAct, idFrame, aeval_X, Fin.val_inj]
    have h3 := congrArg (fun φ => φ f) hcomp
    simpa [MvPolynomial.coe_aeval_eq_eval] using h3
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ N N _ (Matrix.of fun a s : Fin N => x (a, s)) f hf
  have h1 := Formalism.GradedWeylDivisibility.fock_space_highest_weight N N le_rfl (fun r : Fin N => Y.rowLen r) hanti _ hmem
  have h2 := Formalism.GradedWeylDivisibility.fock_space_row_action N N (Matrix.of fun a s : Fin N => x (a, s)).transpose
    (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) f
  rw [Matrix.transpose_transpose, h1, hev, rowAct_hw_expand N Y hY x, hsum] at h2
  simp only [MvPolynomial.C_mul', hsmul] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.smul_eval]
  rw [mul_comm (fockQ _ _) (eval x f), ← h2]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

end GlobalTheory.WeylReproducingSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem valC_finiteDimensional {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by
  classical
  have h := span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ
  have h2 : ValC (Gr emb σ n) lam ≤
      Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr F, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))
  exact Submodule.finiteDimensional_of_le h2

theorem GStep.fi_finiteDimensional {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K]
    [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (_hF : FOk emb σ) (hS : S.Ok) : FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := hS.fin_orb
  haveI := valC_finiteDimensional emb σ lam
  let f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun a b hab => ?_
  apply Subtype.ext
  funext c
  exact congrArg Subtype.val (congrFun hab c)

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSdLatReps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetEx

theorem exists_finset_sdLat_reps : ∀ (X : Fields), X.Ok → ∀ n : ℕ, ∃ T : Finset (Submodule (𝓞 X.E) (Sp X.E n)), (∀ N ∈ T, IsSdLat N) ∧ ∀ N : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat N → ∃ N₀ ∈ T, ∃ γ : UF X.E n, N = gmap γ.1 N₀ := by
  intro X hX n
  obtain ⟨s, hs, H⟩ := unimod_finite (E := X.E) (posStar_of_conj hX.conjE) n
  refine ⟨s, hs, fun N hN => ?_⟩
  obtain ⟨N₀, h₀, g, hg, e⟩ := H N hN.1 hN.2
  exact ⟨N₀, h₀, ⟨g, hg⟩, e.symm⟩

end GlobalTheory.Mem.Col2.JetEx
end

