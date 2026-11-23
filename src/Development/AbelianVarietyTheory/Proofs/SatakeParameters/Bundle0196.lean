module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

abbrev sizes (r t : ℕ) : Fin (t + 1) → ℕ := Fin.cons r (fun _ => 1)

theorem sum_sizes (r t : ℕ) : ∑ a, sizes r t a = r + t := by simp [sizes, Fin.sum_cons]

def blocks (r t : ℕ) : (Σ a : Fin (t + 1), Fin (sizes r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sizes r t)

theorem blocks_zero (r t : ℕ) (i : Fin r) : blocks r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  have hv := stdBlocks_val (sizes r t) (sum_sizes r t) 0 i
  haveI : IsEmpty (Fin ((0 : Fin (t + 1)) : ℕ)) := by simp only [Fin.val_zero]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hv
  exact hv

theorem blocks_succ (r t : ℕ) (j : Fin t) (i : Fin (sizes r t j.succ)) :
    blocks r t ⟨j.succ, i⟩ = Fin.natAdd r j := by
  ext
  have hi : (i : ℕ) = 0 := by have := i.2; simp [sizes] at this; omega
  simp [blocks, stdBlocks_val, hi, Fin.sum_univ_succ, sizes]

def zeroIdx (r t : ℕ) (j : Fin t) : Fin (sizes r t j.succ) := ⟨0, by simp [sizes]⟩

theorem natAdd_eq (r t : ℕ) (j : Fin t) : Fin.natAdd r j = blocks r t ⟨j.succ, zeroIdx r t j⟩ :=
  (blocks_succ r t j _).symm

theorem blk_castAdd (r t : ℕ) (i : Fin r) : blk (blocks r t) (Fin.castAdd t i) = 0 := by
  unfold blk; rw [← blocks_zero, Equiv.symm_apply_apply]

theorem blk_natAdd (r t : ℕ) (j : Fin t) : blk (blocks r t) (Fin.natAdd r j) = j.succ := by
  unfold blk; rw [natAdd_eq, Equiv.symm_apply_apply]

theorem natAdd_ne_castAdd {r t : ℕ} (i : Fin t) (j : Fin r) : Fin.natAdd r i ≠ Fin.castAdd t j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem det_of_lowerLeft {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0) :
    M.det = (M.submatrix (Fin.castAdd t) (Fin.castAdd t)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁, h0]
  rw [this, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem det_lowerRight {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (h1 : M.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1) :
    (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = M.det := by
  rw [det_of_lowerLeft M h0, h1, det_one, one_mul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stab {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (v : W) : Subgroup G :=
  GlobalTheory.DoubleCosetSetoid.repStabilizer ρ v

theorem KOne_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsTame χ) {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    KOne k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  have hKO := GlobalTheory.StepData.KOne_le_KO hh
  have hm := GlobalTheory.StepData.mem_KOne.1 hh
  have hM : GlobalTheory.StepData.MaxM (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) - 1) := by
    intro i j
    have := hm (Fin.natAdd r i) (Fin.natAdd r j)
    simpa [Matrix.one_apply] using this
  obtain ⟨g', hg', hgv⟩ := GlobalTheory.StepData.exists_mem_KOne hM
  have hu := GlobalTheory.StepData.det_of_mem_KOne hg'
  have key := hv h hKO (fun i j => by
      have := hm (Fin.natAdd r i) (Fin.castAdd t j)
      simpa [Matrix.one_apply, natAdd_ne_castAdd i j] using this)
    (fun i j => by
      have := hm (Fin.castAdd t i) (Fin.castAdd t j)
      simpa [Matrix.one_apply] using this)
    (Matrix.GeneralLinearGroup.det g') (by rw [Matrix.GeneralLinearGroup.val_det_apply, hgv])
  show π h v = v
  rw [key, hχ _ hu, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipRad_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (blocks r t) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hh.1
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j =>
    mem_parab.1 hP _ _ (by rw [blk_castAdd, blk_natAdd]; exact Fin.succ_pos i)
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [← blocks_zero]
      exact (hD 0 i i).trans (Matrix.one_apply_eq _)
    · rw [if_neg hij]
      rw [← blocks_zero, ← blocks_zero]
      exact (hD 0 i j).trans (Matrix.one_apply_ne hij)
  have hdet : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 1 := by
    rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, det_eq_one_of_mem_unipRad k hh.1,
      Units.val_one]
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) 1 (by rw [hdet, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_leviEmb {α n : Type} {m : α → Type} [Fintype α] [DecidableEq α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (y : Levi k m) (hy : ∀ a, GlobalTheory.StepData.IntM (y a).val) :
    GlobalTheory.StepData.IntM (leviEmb k e y).val := by
  intro p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective q
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    exact hy a i j
  · rw [leviEmb_apply_ne k e y h]
    exact zero_mem _

abbrev single {r t : ℕ} (j : Fin t) (g : GL (Fin (sizes r t j.succ)) k) : Levi k (fun a => Fin (sizes r t a)) :=
  Pi.mulSingle j.succ g

theorem single_mem_KO {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) (a : Fin (t + 1)) : single j g a ∈ KO k (Fin (sizes r t a)) := by
  by_cases ha : a = j.succ
  · subst ha
    rw [single, Pi.mulSingle_eq_same]
    exact hg
  · rw [single, Pi.mulSingle_eq_of_ne ha]
    exact one_mem _

theorem deltaHalf_single {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) : deltaHalf k (fun a => Fin (sizes r t a)) (single j g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (single_mem_KO j hg a)

theorem act_single {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) (j : Fin t)
    {g : GL (Fin (sizes r t j.succ)) k} (hg : g ∈ KO k (Fin (sizes r t j.succ))) :
    π (leviEmb k (blocks r t) (single j g)) v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (blocks r t) (single j g) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (single_mem_KO j hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (single_mem_KO j hg a))
  have h0 : ∀ (i : Fin t) (j' : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j') = 0 := fun i j' => by
    rw [natAdd_eq, ← blocks_zero]
    exact leviEmb_apply_ne k _ _ (Fin.succ_ne_zero i) _ _
  have hx0 : single j g 0 = 1 := Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm _
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    have hx0' : ((single j g 0 : GL (Fin (sizes r t 0)) k) : Matrix (Fin (sizes r t 0)) (Fin (sizes r t 0)) k) = 1 := by
      rw [hx0, Units.val_one]
    ext i i'
    rw [Matrix.submatrix_apply, ← blocks_zero, ← blocks_zero, hdef]
    exact (leviEmb_apply_same k (blocks r t) (single j g) 0 i i').trans (congrFun (congrFun hx0' i) i')
  have key := hv h hKO (fun i j' => by simp [h0]) (fun i j' => by
      have := congrFun (congrFun h1 i) j'
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) (Matrix.GeneralLinearGroup.det g) (by
      rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply h, hdef, det_leviEmb k,
        Finset.prod_eq_single j.succ (fun b _ hb => by rw [single, Pi.mulSingle_eq_of_ne hb, map_one]) (by simp),
        single, Pi.mulSingle_eq_same])
  exact key

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

theorem exists_jacquet_ne_zero_of_isBlockVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  intro hP k _ _ _ _ r t χ π v hχ hv0 hv
  refine ⟨blocks r t, Submodule.Quotient.mk v, ?_, ?_⟩
  · intro hx
    apply hv0
    refine hP k (r + t) (t + 1) _ (blocks r t) π v ?_ hx
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro j g hg
    rw [GlobalTheory.SmGL.jac_mk, deltaHalf_single j hg, act_single hv j hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFrobeniusSemisimplification
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.WeilDeligne

theorem isNilpotent_map_left {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X : Module.End K U} (Y : Module.End K W) (hX : IsNilpotent X) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem isNilpotent_map_right {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (X : Module.End K U) {Y : Module.End K W} (hY : IsNilpotent Y) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem commute_map {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X X' : Module.End K U} {Y Y' : Module.End K W}
    (hX : Commute X X') (hY : Commute Y Y') :
    Commute (TensorProduct.map X Y) (TensorProduct.map X' Y') := by
  show TensorProduct.map X Y * TensorProduct.map X' Y' = TensorProduct.map X' Y' * TensorProduct.map X Y
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hX.eq, hY.eq]

theorem IsFrobSS.tensor : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → Module.End ℂ V} {N : Module.End ℂ V} {a : WDRep h V} {ρ' : ↥(Weil h) → Module.End ℂ V'} {N' : Module.End ℂ V'} {b : WDRep h V'}, IsFrobSS ρ N a → IsFrobSS ρ' N' b → IsFrobSS (fun g => TensorProduct.map (ρ g) (ρ' g)) (N.rTensor V' + N'.lTensor V) (a.tensor b) := by
  intro E Ω _ _ _ _ _ A w h V V' _ _ _ _ _ _ ρ N a ρ' N' b ha hb
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ]
    exact commute_map (ha.2 g).1 (hb.2 g).1
  · rw [WDRep.tensor_ρ]
    have e : TensorProduct.map (ρ g) (ρ' g) - TensorProduct.map (a.ρ g) (b.ρ g) =
        TensorProduct.map (ρ g - a.ρ g) (ρ' g) + TensorProduct.map (a.ρ g) (ρ' g - b.ρ g) :=
      TensorProduct.ext' fun x y => by
        simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    rw [e]
    refine Commute.isNilpotent_add ?_ (isNilpotent_map_left _ (ha.2 g).2)
      (isNilpotent_map_right _ (hb.2 g).2)
    exact commute_map ((ha.2 g).1.symm.sub_left (Commute.refl _))
      ((Commute.refl _).sub_right (hb.2 g).1.symm)

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.ThetaRiesz

theorem thetaPair_of_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  intro k _ _ _ _ r n V W _ _ _ _ μ σ π hadm hunit hμ b hb hb_inv
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hunit
  obtain ⟨hone, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ

  have huniq : ∀ u u' : V, (∀ w, Bf u w = Bf u' w) → u = u' := by
    intro u u' h
    by_contra hne
    have hne' : u - u' ≠ 0 := sub_ne_zero.2 hne
    have hfun : Bf (u - u') = 0 := by rw [map_sub, LinearMap.ext h, sub_self]
    have h0 : Bf (u - u') (u - u') = 0 := by rw [hfun, LinearMap.zero_apply]
    have := hpos _ hne'
    rw [h0] at this
    simp at this

  let S : SB (Matrix (Fin n) (Fin r) k) → Subgroup (GL (Fin r) k) := fun Φ =>
    { carrier := {g | om μ g 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ}
      one_mem' := hone _
      mul_mem' := by
        intro x y hx hy
        show om μ (x * y) 1 _ = _
        have := hmul x y 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [mul_one] at this
        rw [this]
        have hy' : om μ y 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hy
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        rw [hy', hx']
      inv_mem' := by
        intro x hx
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        show om μ x⁻¹ 1 _ = _
        have := hmul x⁻¹ x 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [inv_mul_cancel, mul_one, hx', hone] at this
        exact this.symm }
  have hSo : ∀ Φ, IsOpen ((S Φ : Subgroup _) : Set (GL (Fin r) k)) := by
    intro Φ
    have h1 := hop _ Φ.2
    have hc : Continuous (fun g : GL (Fin r) k => (g, (1 : GL (Fin n) k))) :=
      continuous_id.prodMk continuous_const
    exact h1.preimage hc
  have hL : ∀ Φ a, ∀ s ∈ S Φ, ∀ w, b Φ a (σ s w) = b Φ a w := by
    intro Φ a s hs w
    have hs' : om μ s 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hs
    have := hb_inv s 1 Φ Φ hs'.symm a w
    simpa using this
  have hex : ∀ Φ a, ∃ u : V, ∀ w, b Φ a w = Bf u w := fun Φ a =>
    exists_vector_of_smooth_antilinear k r V σ Bf hadm hsym hpos hinv (b Φ a) (S Φ) (hSo Φ) (hL Φ a)
  choose f hf using hex
  have hadd1 : ∀ Φ Ψ a, f (Φ + Ψ) a = f Φ a + f Ψ a := fun Φ Ψ a =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul1 : ∀ (z : ℂ) Φ a, f (z • Φ) a = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  have hadd2 : ∀ Φ a a', f Φ (a + a') = f Φ a + f Φ a' := fun Φ a a' =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul2 : ∀ (z : ℂ) Φ a, f Φ (z • a) = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  let B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V :=
    LinearMap.mk₂ ℂ f hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ Φ a, B Φ a = f Φ a := fun _ _ => rfl
  refine ⟨B, ?_, ?_⟩
  · intro h0
    apply hb
    ext Φ a w
    rw [hf, ← hB, h0]
    simp
  · intro g h Φ Φ' hΦ F
    rw [hB, hB]
    apply huniq
    intro c
    have hc : σ g (σ g⁻¹ c) = c := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← hf, ← hc, hb_inv g h Φ Φ' hΦ F, hf, ← hinv g (f Φ F) (σ g⁻¹ c)]

end GlobalTheory.ThetaRiesz
end

