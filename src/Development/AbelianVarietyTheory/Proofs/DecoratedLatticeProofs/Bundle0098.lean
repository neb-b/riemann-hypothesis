module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOne
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
open scoped Pointwise

namespace GlobalTheory.LatPair.Det

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_of_mem_latStab_std {g : GL n k} (hg : g ∈ latStab (stdLat k n)) : g.val.det ∈ 𝒪[k] := by
  rw [MulAction.mem_stabilizer_iff] at hg
  have t2 : ∀ v : n → k, v ∈ stdLat k n ↔ ∀ i, v i ∈ 𝒪[k] := by
    intro v
    simp only [stdLat, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro h
      exact ⟨fun i => ⟨v i, h i⟩, rfl⟩
  have hent : ∀ i j, (g : Matrix n n k) i j ∈ 𝒪[k] := by
    intro i j
    have hs : Pi.single j (1 : k) ∈ stdLat k n := by
      rw [t2]
      intro i'
      by_cases h : i' = j
      · subst h
        simp only [Pi.single_eq_same]
        exact one_mem _
      · simp only [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h1 : g • Pi.single j (1 : k) ∈ stdLat k n := by
      rw [← hg]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hs
    rw [t2] at h1
    have h2 := h1 i
    change ((g : Matrix n n k) *ᵥ Pi.single j 1) i ∈ 𝒪[k] at h2
    simpa [Matrix.mulVec_single] using h2
  let A : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨(g : Matrix n n k) i j, hent i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (g : Matrix n n k) := by
    ext i j
    rfl
  rw [← hA, ← RingHom.map_det]
  exact (A.det).2

theorem exists_smul_stdLat_eq (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : ∃ h : GL n k, h • stdLat k n = L := by
  classical
  letI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  letI : Module.Finite 𝒪[k] L := Submodule.IsLattice.finite k L
  let b := Module.Free.chooseBasis 𝒪[k] L
  let B := b.extendOfIsFullLattice k
  have hc : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[k] L) = Fintype.card n := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e := Fintype.equivOfCardEq hc
  let B' := B.reindex e
  let P := (Pi.basisFun k n).toMatrix B'
  let Q := B'.toMatrix (Pi.basisFun k n)
  let h : GL n k := ⟨P, Q, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hB' : ∀ j, B' j = (b (e.symm j) : n → k) := by
    intro j
    simp [B', B]
  have key : ∀ y : n → k, h • y = ∑ j, y j • B' j := by
    intro y
    change P *ᵥ y = _
    ext i
    simp [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
  refine ⟨h, ?_⟩
  ext x
  simp only [HSMul.hSMul, SMul.smul]
  rw [Submodule.mem_map]
  simp only [DistribSMul.toLinearMap_apply]
  change (∃ y ∈ stdLat k n, h • y = x) ↔ x ∈ L
  simp only [key]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine L.sum_mem fun j _ => ?_
    rw [hB']
    change algebraMap 𝒪[k] k (c j) • (b (e.symm j) : n → k) ∈ L
    rw [algebraMap_smul]
    exact L.smul_mem (c j) (b (e.symm j)).2
  · intro hx
    let c := b.repr ⟨x, hx⟩
    refine ⟨fun j => (c (e.symm j) : k), ⟨fun j => c (e.symm j), rfl⟩, ?_⟩
    simp_rw [hB']
    have hsum := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
    rw [Equiv.sum_comp e.symm (fun i => ((c i : 𝒪[k]) : k) • (b i : n → k))]
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul k (c i) _

theorem det_mem_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ 𝒪[k] := by
  obtain ⟨h, rfl⟩ := exists_smul_stdLat_eq L
  have hs : h⁻¹ * g * h ∈ latStab (stdLat k n) := by
    simp only [latStab, MulAction.mem_stabilizer_iff] at hg ⊢
    rw [mul_smul, mul_smul, hg, inv_smul_smul]
  have h1 := det_mem_of_mem_latStab_std hs
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at h1
  have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * g * h) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [hdet] at h1

theorem valuation_det_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 := det_mem_of_mem_latStab hg
  have h2 := det_mem_of_mem_latStab (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  set d : k := ((Matrix.GeneralLinearGroup.det g : kˣ) : k) with hd
  have hd0 : d ≠ 0 := Units.ne_zero _
  have hu : IsUnit (⟨d, h1⟩ : 𝒪[k]) :=
    ⟨⟨⟨d, h1⟩, ⟨d⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu

end

theorem isUnram_det_latStab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  exact hμ _ (valuation_det_of_mem_latStab hg)

end GlobalTheory.LatPair.Det
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_rat_mul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ * w * mt S γ) := by
  intro D ψ S T χ χ' om H f hf γ hγ γ' hγ' g h w
  have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ H.std S T χ χ' om H γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)
    (mt T γ'⁻¹ * w * mt S γ)
  have h2 : actO S T γ γ' (mt T γ'⁻¹ * w * mt S γ) = w := by
    change mt T γ' * (mt T γ'⁻¹ * w * mt S γ) * mt S γ⁻¹ = w
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_inv,
      Matrix.one_mul]
  rw [h2] at h1
  rw [← h1, ← Prod.mk_mul_mk, map_mul, mul_apply_eq_comp]

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel Matrix

namespace GlobalTheory.IwaPlace

variable {D : D7}

def hermAt (S : HSp D) (x y : Fin S.rank → AE D) : AE D := ∑ i, ∑ j, cA D (y i) * gA S i j * x j

def IsSDAt (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)) : Prop :=
  (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) ∧
    (∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) ∧
    ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v))

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Mx D V.rank V.rank) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have e1 : ((1 : Mx D V.rank V.rank).map (Ideal.Quotient.mk I)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e2 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V) g).1 = (mt V g).map (Ideal.Quotient.mk I) := rfl
  constructor
  · intro h i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [e2, Units.val_one] at this
    rw [← e1] at this
    exact this
  · intro h
    ext i j
    rw [e2, Units.val_one, ← e1]
    exact Ideal.Quotient.eq.2 (h i j)

theorem mulVec_mem_idAt {P : Pl D → Prop} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (M *ᵥ y) i ∈ idAt D P :=
  by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {γ : GA D S₀}
    (hγ : γ ∈ grpAt S₀ P) : d.emb0 γ ∈ grpAt S P := by
  have hγ' := (mem_congGrp_iff S₀ (idAt D P) γ).1 hγ
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (d.emb0 γ) - 1 = d.j0 ⬝ (mt S₀ γ - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact hγ' l k)

end GlobalTheory.IwaPlace

end
end

