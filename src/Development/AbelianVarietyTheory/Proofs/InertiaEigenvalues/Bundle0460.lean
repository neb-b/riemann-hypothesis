module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulBcrisGaloisLatticeInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TContInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, -, -⟩ := GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  haveI : Nontrivial (Per.BdR l) := ⟨(_root_.GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.exists_pair_ne⟩
  exact ι.domain_nontrivial

theorem zl_bcris_injective (l : ℕ) [Fact l.Prime] : Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  haveI := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) z) := by
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]
    exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)
  exact hu.ne_zero hz

theorem includeLeft_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (zl_bcris_injective l)
  intro x y hxy
  apply (TensorProduct.rid ℤ_[l] O).symm.injective
  apply h
  simpa [Algebra.TensorProduct.algebraMap_apply] using hxy

theorem one_tmul_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] :
    Function.Injective (fun x : M => (1 : OB l O) ⊗ₜ[O] x) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap O (OB l O)) (includeLeft_injective l O)
  intro x y hxy
  apply (TensorProduct.lid O M).symm.injective
  apply h
  simpa [← Algebra.TensorProduct.one_def] using hxy

end GlobalTheory.TContInj

theorem GlobalTheory.TContInj.main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  intro l _ LL T
  haveI : Module.Free (↥(OL LL)) ↥T.L.T := T.L.free
  exact GlobalTheory.TContInj.one_tmul_injective l ↥(OL LL) ↥T.L.T
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElementStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  first | (exact @GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (exact GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (intros; apply GlobalTheory.HodgeAt.exists_idem_phiS_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiModuleHomShortExactSplitWittTilt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem phiModuleHom_shortExact_split_wittTilt {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type}
    [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) :
    (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧
      (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  classical

  let g₁ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T := (g.f.restrictScalars O).restrict g.T_le
  let f₁ : ↥T₀.L.T →ₗ[O] ↥T₁.L.T := (f.f.restrictScalars O).restrict f.T_le
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hS.2.2.1 y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Module.Free O ↥T₂.L.T := T₂.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g₁ LinearMap.id hg₁s
  have hs' : ∀ y, g₁ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hf₁i : Function.Injective f₁ := fun x y h => Subtype.ext (hS.1 (congrArg Subtype.val h))
  have hgf : ∀ y, g₁ (f₁ y) = 0 := fun y => Subtype.ext ((hS.2.2.2.1 _).2 ⟨y, rfl⟩)
  let p : ↥T₁.L.T →ₗ[O] ↥T₁.L.T := LinearMap.id - s ∘ₗ g₁
  have hp : ∀ x, p x ∈ LinearMap.range f₁ := by
    intro x
    have h0 : g₁ (p x) = 0 := by
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    obtain ⟨y, hy⟩ := (hS.2.2.2.1 _).1 (congrArg Subtype.val h0)
    have hy0 : y ∈ T₀.L.T := hS.2.2.2.2 y (hy ▸ (p x).2)
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T :=
    (LinearEquiv.ofInjective f₁ hf₁i).symm.toLinearMap ∘ₗ p.codRestrict (LinearMap.range f₁) hp
  have hr : ∀ y, r (f₁ y) = y := by
    intro y
    have h1 : p.codRestrict (LinearMap.range f₁) hp (f₁ y) = LinearEquiv.ofInjective f₁ hf₁i y := by
      apply Subtype.ext
      simp [p, hgf]
    simp only [r, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

  let Sw := s.baseChange (OW l O)
  let Rw := r.baseChange (OW l O)
  have hSw : ∀ x, latW g (Sw x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Sw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hs' y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hRw : ∀ x, Rw (latW f x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Rw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hr y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

  let SL : (μ → OW l O) →ₗ[OW l O] (κ → OW l O) := I₁.j.symm.toLinearMap ∘ₗ Sw ∘ₗ I₂.j.toLinearMap
  let RL : (κ → OW l O) →ₗ[OW l O] (ι → OW l O) := I₀.j.symm.toLinearMap ∘ₗ Rw ∘ₗ I₁.j.toLinearMap
  have hSL : homW t ϖ H ∘ₗ SL = LinearMap.id := by
    refine LinearMap.ext fun v => I₂.j.injective ?_
    rw [LinearMap.comp_apply, hH]
    simp only [SL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hSw,
      LinearMap.id_apply]
  have hRL : RL ∘ₗ homW t ϖ F = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change I₀.j.symm (Rw (I₁.j (homW t ϖ F v))) = v
    rw [hF, hRw, LinearEquiv.symm_apply_apply]
  have hM : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (M : Matrix α β (OW l O)), LinearMap.toMatrix' M.mulVecLin = M := fun M => LinearMap.toMatrix'_toLin' M
  refine ⟨⟨LinearMap.toMatrix' SL, ?_⟩, ⟨LinearMap.toMatrix' RL, ?_⟩⟩
  · have h := congrArg LinearMap.toMatrix' hSL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]
  · have h := congrArg LinearMap.toMatrix' hRL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiWInclLEPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal

theorem phiW_inclL_E_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α Y hY c
  set s0 : OW l O := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hs0

  have key : Y.map (inclO l O) = s0 ^ α • frobMat t ϖ P := by
    ext i j
    obtain ⟨f, hf, hYij⟩ := hY i j
    rw [Matrix.map_apply, hYij, ← ϖ.iW_of_mem t K, Matrix.smul_apply, smul_eq_mul, hs0, ← ϖ.iTot_E t K,
      ← ϖ.iW_of_mem t K, ← map_pow, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp only [Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, hf τ]
    rfl
  have key2 : (Y.map (frobOA l O)).map (inclO l O) =
      inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • (frobMat t ϖ P).map (frobOW l O) := by
    have h1 : (Y.map (frobOA l O)).map (inclO l O) = (Y.map (inclO l O)).map (frobOW l O) := by
      ext i j; simp only [Matrix.map_apply, frobOW_inclO]
    rw [h1, key]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hs0, frobOW_inclO]
  rw [inclL_apply, phiW_apply, inclL_apply]
  have h2 : (fun i => frobOW l O ((frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i)) =
      (frobMat t ϖ P).map (frobOW l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, frobOW_inclO]
  have h3 : (fun i => inclO l O ((Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) i)) =
      (Y.map (frobOA l O)).map (inclO l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [h2, h3, key2, Matrix.smul_mulVec, Matrix.mulVec_smul]

end GlobalTheory.BKReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionField
section
noncomputable section

namespace GlobalTheory.PointRepConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem exists_gl_of_equiv {K Γ : Type} [Field K] {n : ℕ} (A B : Γ → Matrix (Fin n) (Fin n) K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ g u, e (Matrix.toLin' (A g) u) = Matrix.toLin' (B g) (e u)) :
    ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * A g = B g * (P : Matrix (Fin n) (Fin n) K) := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simpa [Matrix.toLin'_mul] using he g u

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  intro hC R H what₂ N i r r' hr hr' x
  have h₁ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r x)).1 (hr x)
  have h₂ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r' x)).1 (hr' x)
  obtain ⟨e, he⟩ := GlobalTheory.ComplementCompare.isRx_unique N hC i x _ _ h₁ h₂
  exact exists_gl_of_equiv _ _ e he

end GlobalTheory.PointRepConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutator
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

private lemma commutator_le_of_forall_commutator_mem {G : Type*} [Group G] (C : Subgroup G)
    (hC : ∀ σ τ : G, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a _ b _ => by
    rw [commutatorElement_def]
    exact hC a b

theorem pow_mem_upper_mod_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p e v C hC hv hpe σ hσ

  let H : Subgroup (L ≃ₐ[F] L) := ⁅(⊤ : Subgroup (L ≃ₐ[F] L)), ⊤⁆
  let Q : IntermediateField F L := IntermediateField.fixedField H
  haveI : IsGalois F Q := IsGalois.of_fixedField_normal_subgroup H
  have hker : (AlgEquiv.restrictNormalHom Q).ker = H := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_fixedField H
  have hab : ∀ s t : Q ≃ₐ[F] Q, s * t = t * s := by
    intro s t
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) s
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) t
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ (AlgEquiv.restrictNormalHom Q).ker := by
      rw [hker]
      have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [commutatorElement_def] at h
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  have hσQ : AlgEquiv.restrictNormalHom Q σ ∈ upperRamificationGroup F Q v := by
    rw [← GroundTheory.LocalField.map_upperRamificationGroup Q v]
    exact Subgroup.mem_map_of_mem _ hσ
  have hpow := _root_.GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm F Q p e v hab hv hpe _ hσQ
  rw [← map_pow, ← GroundTheory.LocalField.map_upperRamificationGroup Q] at hpow
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hpow
  refine ⟨τ, hτ, commutator_le_of_forall_commutator_mem C hC ?_⟩
  have hk : τ⁻¹ * σ ^ p ∈ (AlgEquiv.restrictNormalHom Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
  rw [hker] at hk
  exact hk

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.RootFactorProduct

private lemma map_sub_smul_E_mulVec_eq {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (a : ℕ) (v : Fin n → FractionRing O) :
    e (((X₀ - ρ a • E).map (toFr O)).mulVec v) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1) - ρ a) * (e v).2 c) := by
  have hm : (X₀ - ρ a • E).map (toFr O) = X₀.map (toFr O) - toFr O (ρ a) • E.map (toFr O) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  have hs : ((toFr O (ρ a)) • E.map (toFr O)).mulVec v = toFr O (ρ a) • (E.map (toFr O)).mulVec v := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum,
      mul_assoc]
  rw [hm, Matrix.sub_mulVec, hs, map_sub, map_smul, hX, hE]
  refine Prod.ext (by simp) ?_
  funext c
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  ring

theorem prod_cons_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (s : List ℕ) : ∀ (a : ℕ) (u : Fin n → FractionRing O),
      e (((((a :: s).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
        (0, fun c : Fin t =>
          toFr O (((a :: s).map fun c' => ρ ((c : ℕ) + 1) - ρ c').prod) * (e u).2 c) := by
  induction s with
  | nil =>
    intro a u
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a u
  | cons b s ih =>
    intro a u
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a, ih b u]
    refine Prod.ext rfl ?_
    funext c
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]

private lemma list_prod_range'_eq_prod_Ico {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ((List.range' m n).map g).prod = ∏ k ∈ Finset.Ico m (m + n), g k := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, show m + (n + 1) = m + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (show m < m + 1 + n by omega)]

theorem prod_other_factors_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (ht : 2 ≤ t)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) (u : Fin n → FractionRing O) :
    e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
      (0, fun c : Fin t => if (c : ℕ) = 0 then
        toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  have hl : List.range' 2 (t - 1) = 2 :: List.range' 3 (t - 2) := by
    rw [show t - 1 = (t - 2) + 1 by omega, List.range'_succ]
  rw [hl, prod_cons_action e E X₀ ρ hE hX, ← hl]
  refine Prod.ext rfl ?_
  funext c
  dsimp only
  split_ifs with h0
  · simp only [h0, zero_add]
    congr 2
    all_goals
      rw [list_prod_range'_eq_prod_Ico]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
  · have hc := c.isLt
    rw [List.prod_eq_zero, map_zero, zero_mul]
    exact List.mem_map.2 ⟨(c : ℕ) + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, sub_self _⟩

end GlobalTheory.RootFactorProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem _root_.GlobalTheory.rank_eq_of_acts_through_first_block {K : Type} [Field K] {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K)
    (ε : Matrix (Fin r) (Fin r) K) (h : ∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) :
    F.rank = ε.rank := by
  have key : (LinearMap.range F.mulVecLin).map (e : (Fin n → K) →ₗ[K] _) =
      (LinearMap.range ε.mulVecLin).map (LinearMap.inl K (Fin r → K) (Fin t → K)) := by
    ext ⟨a, b⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hx⟩
      rw [LinearEquiv.coe_coe, h] at hx
      exact ⟨_, ⟨(e u).1, rfl⟩, by simpa using hx⟩
    · rintro ⟨_, ⟨v, rfl⟩, hx⟩
      refine ⟨_, ⟨e.symm (v, 0), rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, h]
      simpa using hx
  unfold Matrix.rank
  rw [← LinearEquiv.finrank_map_eq e, key]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTop
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem span_matrix_eq_top_of_residue_span {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (f i).map (IsLocalRing.residue A))) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | (apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)

theorem span_mat_eq_top_of_residue {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  span_matrix_eq_top_of_residue_span (mat ρ) h

end GlobalTheory
end

