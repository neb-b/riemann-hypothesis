module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisOfIsDeRhamLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem toMatrix_qRep {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (Pi.basisFun ℚ_[l] (Fin d)) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ g) =
      (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.toLin' ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]))) = _
  rw [LinearMap.toMatrix'_toLin']

theorem invariant_basis_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∃ x : Fin d → Fin d → P.R.BdR, LinearIndependent ↥K.1 x ∧ (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) ∧ ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ∈ Submodule.span ↥K.1 (Set.range x) := by
  intro l _ P AI T K d ρ hDR
  obtain ⟨Q, hQ⟩ := exists_period_matrix_of_isDR l P AI T (Fin d) K (Fin d → ℚ_[l])
    (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hQ' : ∀ g : ↥(GK K), M g * (Q : Matrix (Fin d) (Fin d) P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
    intro g
    have h := hQ g
    rw [toMatrix_qRep, Matrix.map_map] at h
    exact h
  letI : Field P.R.BdR := (_root_.GlobalTheory.PMon.bdR_tied l P AI T).1.toField
  set Qm : Matrix (Fin d) (Fin d) P.R.BdR := (Q : Matrix (Fin d) (Fin d) P.R.BdR) with hQm
  have hQinj : ∀ v w : Fin d → P.R.BdR, Qm *ᵥ v = Qm *ᵥ w → v = w := by
    intro v w h
    have := congrArg (fun u => ((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, hQm] at this
    rwa [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  refine ⟨fun j i => Qm i j, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Qm *ᵥ (fun j => algebraMap ↥K.1 P.R.BdR (c j)) = Qm *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at this
      simp only [Algebra.smul_def] at this
      rw [Pi.zero_apply, ← this]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h0 := hQinj _ _ hv
    intro j
    have := congrFun h0 j
    simp only [Pi.zero_apply] at this
    exact (FaithfulSMul.algebraMap_injective ↥K.1 P.R.BdR) (by rw [this, map_zero])
  · intro j g
    funext i
    have h := congrFun (congrFun (hQ' g) i) j
    simpa [hM, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  · intro c hc
    obtain ⟨w, hw⟩ : ∃ w, Qm *ᵥ w = c :=
      ⟨((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ c, by
        rw [Matrix.mulVec_mulVec, hQm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]⟩
    have hfix : ∀ (g : ↥(GK K)) j, P.actQdR (g : GQ l) (w j) = w j := by
      intro g
      have key : Qm *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) = Qm *ᵥ w := by
        have hact : (fun i => P.actQdR (g : GQ l) (c i)) =
            Qm.map (P.actQdR (g : GQ l)) *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) := by
          funext i
          rw [← hw]
          exact RingHom.map_mulVec ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR) Qm w i
        have := hc g
        rw [hact, Matrix.mulVec_mulVec, hQ' g] at this
        rw [this, hw]
      exact congrFun (hQinj _ _ key)
    have hwK : ∀ j, ∃ k : ↥K.1, algebraMap ↥K.1 P.R.BdR k = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hfix g j
    choose k hk using hwK
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨k, ?_⟩
    rw [← hw]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    simp only [Algebra.smul_def, hk]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.DRMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BcrisInv

theorem map_smul_matrix {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (a : R)
    (M : Matrix (Fin d) (Fin d) R) : (a • M).map f = f a • M.map f := by
  ext i j; simp

theorem invariant_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  intro l _ K bk τ hτ N d k ρ Y Y' ε Q Q' hYY hgal hQQ hε
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf
  set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg
  obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
  have hne : e ≠ 1 := by
    rintro rfl; apply he2; simp
  have hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1)) :=
    GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
  have hw : IsUnit (f τ) := by
    have : f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  obtain ⟨W, hW⟩ := hw.pow N

  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ?_, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)

    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG

    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    have e2 : (⇑alg ∘ fun a => (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) = ⇑f := by
      funext a; simp only [Function.comp_apply, hFφ, hf, halg, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
    rw [e2] at hE

    have eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) =
        (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]

end GlobalTheory.BcrisInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelLatticeEquivariantModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

def kerMod {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Submodule ℤ_[l] (Fin d' → ℤ_[l]) where
  carrier := {v | ∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ v) i}
  add_mem' {a b} ha hb i := by
    rw [Matrix.mulVec_add]; exact dvd_add (ha i) (hb i)
  zero_mem' i := by simp
  smul_mem' c v hv i := by
    rw [Matrix.mulVec_smul]; exact Dvd.dvd.mul_left (hv i) c

theorem mulVec_mem_kerMod {d d' n : ℕ} {P : Matrix (Fin d) (Fin d') ℤ_[l]}
    {A : Matrix (Fin d') (Fin d') ℤ_[l]} {B : Matrix (Fin d) (Fin d) ℤ_[l]}
    (h : ∀ i j, (l : ℤ_[l]) ^ n ∣ (P * A - B * P) i j) {v : Fin d' → ℤ_[l]} (hv : v ∈ kerMod P n) :
    A *ᵥ v ∈ kerMod P n := by
  intro i
  have e : P *ᵥ (A *ᵥ v) = (P * A - B * P) *ᵥ v + B *ᵥ (P *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; abel
  rw [e, Pi.add_apply]
  refine dvd_add ?_ ?_
  · show _ ∣ ∑ j, (P * A - B * P) i j * v j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _
  · show _ ∣ ∑ j, B i j * (P *ᵥ v) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hv j) _

theorem pow_ne_zero' (n : ℕ) : ((l : ℤ_[l]) ^ n) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

theorem finrank_kerMod {d d' n : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) :
    Module.finrank ℤ_[l] (kerMod P n) = d' := by
  apply le_antisymm
  · calc Module.finrank ℤ_[l] (kerMod P n) ≤ Module.finrank ℤ_[l] (Fin d' → ℤ_[l]) :=
          Submodule.finrank_le _
      _ = d' := by simp
  · have hm : ∀ v : Fin d' → ℤ_[l], ((l : ℤ_[l]) ^ n • LinearMap.id : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] _) v ∈ kerMod P n := by
      intro v i
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    let φ : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] kerMod P n :=
      LinearMap.codRestrict (kerMod P n) ((l : ℤ_[l]) ^ n • LinearMap.id) hm
    have hinj : Function.Injective φ := by
      intro a b hab
      have h2 := congrArg Subtype.val hab
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
      exact smul_right_injective _ (pow_ne_zero' n) h2
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

end GlobalTheory.KerLat

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def kerBasis {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Module.Basis (Fin d') ℤ_[l] (kerMod P n) :=
  Module.finBasisOfFinrankEq ℤ_[l] (kerMod P n) (finrank_kerMod P)

noncomputable def kerMat {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Matrix (Fin d') (Fin d') ℤ_[l] :=
  Matrix.of fun i j => ((kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) i

theorem kerMat_mulVec {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) (w : Fin d' → ℤ_[l]) :
    kerMat P n *ᵥ w = ((∑ j, w j • kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) := by
  ext i
  simp [kerMat, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]

theorem exists_kernel_lattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  intro l _ Γ _ d d' n ρ ρ' P hP
  set b := kerBasis P n
  set f := kerMat P n
  have hf : ∀ w, f *ᵥ w = ((∑ j, w j • b j : kerMod P n) : Fin d' → ℤ_[l]) := kerMat_mulVec P n
  have hiff : ∀ v, v ∈ kerMod P n ↔ ∃ w, v = f *ᵥ w := by
    intro v; constructor
    · intro hv; refine ⟨b.repr ⟨v, hv⟩, ?_⟩
      rw [hf, b.sum_repr]
    · rintro ⟨w, rfl⟩; rw [hf]; exact Submodule.coe_mem _
  have hinj : ∀ w, f *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [hf] at hw
    have h0 : (∑ j, w j • b j) = 0 := Subtype.ext hw
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent w h0 j
  have hdet : f.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hw0 (hinj w hw)
  have hcancel : ∀ X Y : Matrix (Fin d') (Fin d') ℤ_[l], f * X = f * Y → X = Y := by
    intro X Y h
    have h2 := congrArg (fun M => f.adjugate * M) h
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul] at h2
    apply Matrix.ext
    intro i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ hdet h3
  have hcol : ∀ g j, ∃ w, (ρ' g).val *ᵥ (fun i => f i j) = f *ᵥ w := by
    intro g j
    apply (hiff _).mp
    apply mulVec_mem_kerMod (A := (ρ' g).val) (B := (ρ g).val) (hP.equi g)
    exact Submodule.coe_mem (b j)
  choose W hW using hcol
  let R : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun i j => W g j i
  have hR : ∀ g, f * R g = (ρ' g).val * f := by
    intro g
    apply Matrix.ext
    intro i j
    have := congrFun (hW g j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, R, Matrix.of_apply]
    exact this.symm
  have hR1 : R 1 = 1 := hcancel _ _ (by rw [hR, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  have hRm : ∀ g h, R (g * h) = R g * R h := fun g h => hcancel _ _ (by
    rw [hR, map_mul, Units.val_mul, Matrix.mul_assoc, ← hR h, ← Matrix.mul_assoc, ← hR g, Matrix.mul_assoc])
  let Rm : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] := { toFun := R, map_one' := hR1, map_mul' := hRm }
  refine ⟨f, Rm.toHomUnits, hdet, fun g => hR g, fun v => hiff v⟩

end GlobalTheory.KerLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneAddPrimePowMulNotRootOfUnity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.SmallRootCl

variable {l : ℕ} [Fact l.Prime]

theorem norm_one_add_pow_sub_one_le (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖(1 + x) ^ m - 1‖ ≤ ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ‖1 + x‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hx)
    have e : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) * (1 + x) + x := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖(1 + x) ^ m - 1‖ * ‖1 + x‖ ≤ ‖x‖ * 1 :=
          mul_le_mul ih h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _

theorem inv_le_norm_prime (q : ℕ) (hq : q.Prime) : (l : ℝ)⁻¹ ≤ ‖(q : ℂ_[l])‖ := by
  have hl : l.Prime := Fact.out
  have h := PadicComplex.norm_extends' l (q : ℚ_[l])
  rw [map_natCast, PadicComplex.coe_natCast] at h
  rw [h]
  by_cases hql : q = l
  · subst hql; rw [Padic.norm_p]
  · have hc : Nat.Coprime l q := (Nat.coprime_primes hl hq).2 (Ne.symm hql)
    rw [(Padic.norm_natCast_eq_one_iff).2 hc]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le)

theorem not_root (x : ℂ_[l]) (hx0 : x ≠ 0) (hx : ‖x‖ < (l : ℝ)⁻¹) (i : ℕ) (hi : 1 ≤ i) :
    (1 + x) ^ i ≠ 1 := by
  intro hpow
  have hl : l.Prime := Fact.out
  have hx1 : ‖x‖ ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le))
  set ζ := 1 + x with hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hpow⟩
  set d := orderOf ζ with hd
  have hdpos : 0 < d := hfin.orderOf_pos
  have hd1 : d ≠ 1 := by
    intro h
    rw [hd, orderOf_eq_one_iff, hζ] at h
    exact hx0 (by linear_combination h)
  set q := d.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hd1
  have hqd : q ∣ d := Nat.minFac_dvd d
  set η := ζ ^ (d / q) with hη
  have hηq : η ^ q = 1 := by
    rw [hη, ← pow_mul, Nat.div_mul_cancel hqd, hd]; exact pow_orderOf_eq_one ζ
  have hη1 : η ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hdpos hqd) hq.pos).ne'
    · exact Nat.div_lt_self hdpos hq.one_lt
  have hsum : ∑ j ∈ Finset.range q, η ^ j = 0 := by
    have h := geom_sum_mul η q
    rw [hηq, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hη1)
  have hsmall : ∀ j, ‖η ^ j - 1‖ ≤ ‖x‖ := fun j => by
    rw [hη, ← pow_mul]; exact norm_one_add_pow_sub_one_le x hx1 _
  have hqeq : (q : ℂ_[l]) = -∑ j ∈ Finset.range q, (η ^ j - 1) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have hle : ‖(q : ℂ_[l])‖ ≤ ‖x‖ := by
    rw [hqeq, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => hsmall j
  have := inv_le_norm_prime (l := l) q hq
  linarith

theorem exists_one_add_pow_mul_not_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℂ_[l]), a ≠ 0 → ∃ k : ℕ, 1 + (l : ℂ_[l]) ^ k * a ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i → (1 + (l : ℂ_[l]) ^ k * a) ^ i ≠ 1 := by
  intro l _ a ha
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
    exact h
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (inv_pos.2 hl0) ha0)
    (inv_lt_one_of_one_lt₀ hl1)
  set x := (l : ℂ_[l]) ^ k * a with hxdef
  have hxn : ‖x‖ < (l : ℝ)⁻¹ := by
    rw [hxdef, norm_mul, norm_pow, hnl]
    exact (lt_div_iff₀ ha0).1 hk
  have hl0' : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0') ha
  refine ⟨k, ?_, fun i hi => not_root x hx0 hxn i hi⟩
  intro h
  have : x = -1 := by linear_combination h
  have h1 : ‖x‖ = 1 := by rw [this, norm_neg, norm_one]
  have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.SmallRootCl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfTheta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
end
end

