module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_one : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at h
  rw [h, ← mul_assoc, e_mul_ι]

theorem xi_ne : p.xi ≠ 0 :=
  (_root_.map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem mul_aux (x y : k) : (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have h1 := e_mul_ι p x
  have h2 := e_mul_ι p y
  have h3 : p.e * p.e = p.e := p.split.1
  rw [ι_mul]
  linear_combination (-1 : AE D) * h1 + (-1 : AE D) * h2 + h3

def unitsHom : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι ↑x⁻¹ + (1 - p.e),
    by rw [mul_aux, Units.mul_inv, ι_one, add_sub_cancel],
    by rw [mul_aux, Units.inv_mul, ι_one, add_sub_cancel]⟩
  map_one' := by
    ext
    simp only [Units.val_one, ι_one, Units.val_mk, add_sub_cancel]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk]
    rw [mul_aux]

def wchar (ψ : AddChar (AF D.host.F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar k Circle where
  toFun x := (⟨psiE ψ (incA D D.host.xi0 * p.ι x), mem_sphere_zero_iff_norm.2 (h _)⟩ : Submonoid.unitSphere ℂ)
  map_zero_eq_one' := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι 0) = 1
    simp [psiE]
  map_add_eq_mul' x y := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι (x + y)) = psiE ψ (incA D D.host.xi0 * p.ι x) * psiE ψ (incA D D.host.xi0 * p.ι y)
    simp only [psiE, map_add (f := _), mul_add, AddChar.map_add_eq_mul]

end GlobalTheory.LocChar

namespace GlobalTheory.LocChar

theorem weil_char_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  intro D k _ _ _ _ p ψ hψ
  refine ⟨⟨wchar p ψ hψ.1.2.1, fun x => rfl⟩, fun ψk hk => ⟨?_, ?_⟩, xi_ne p, ι_mul p, fun χ =>
    ⟨(Circle.toUnits.comp χ).comp (unitsHom p), fun x a ha => ?_⟩⟩
  · have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    have hT : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap _
    have hc : Continuous fun x => ((ψk x : Circle) : ℂ) := by
      rw [funext hk]
      exact hψ.1.1.comp (hT.comp (continuous_const.mul p.cont_ι))
    exact continuous_induced_rng.2 hc
  · intro h1
    obtain ⟨v, he⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff p.e).1 p.split
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
    have hta := GlobalTheory.SplitAnnihilator.trace_split he y 1
    rw [mul_one] at hta
    have hea : p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e)) =
        GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) := by
      linear_combination (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) * he.1
    generalize GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) = a at hea hta
    have hu0 : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)
    obtain ⟨u, hu⟩ := hu0
    have hx : incA D D.host.xi0 * p.ι (p.π (↑u⁻¹ * a)) = a := by
      rw [p.ι_π, ← hu]
      calc (u : AE D) * (p.e * (↑u⁻¹ * a)) = ((u : AE D) * ↑u⁻¹) * (p.e * a) := by ring
        _ = a := by rw [Units.mul_inv, one_mul, hea]
    have h2 := hk (p.π (↑u⁻¹ * a))
    rw [h1, AddChar.one_apply, Circle.coe_one, hx] at h2
    exact hy (by rw [psiV, ← hta]; exact h2.symm)
  · have : unitsHom p x = a := Units.ext ha.symm
    simp only [MonoidHom.comp_apply, this]
    rfl

end GlobalTheory.LocChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.LeviUnitK

variable {D : D7}

theorem mul_mem_of_sub_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) : (fun k => c * z k) ∈ latV S L P := by
  have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hc hz
  have e : (fun k => c * z k) = z + fun k => (c - 1) * z k := by
    funext k; simp only [Pi.add_apply]; ring
  rw [e]; exact add_mem hz h

theorem mem_iff_of_unit {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c c' : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    (hc' : finPart D (c' - 1) ∈ intAE D) (h1 : c' * c = 1) (z : Fin S.rank → AE D) :
    z ∈ latV S L P ↔ (fun k => c * z k) ∈ latV S L P := by
  refine ⟨mul_mem_of_sub_one hc, fun h => ?_⟩
  have h2 := mul_mem_of_sub_one hc' h
  have e : (fun k => c' * (c * z k)) = z := by funext k; rw [← mul_assoc, h1, one_mul]
  rwa [e] at h2

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (i : Fin n) (c a : AE D) :
    colMul x i (c * a) = fun k => c * colMul x i a k := by
  funext k; simp only [colMul, mul_assoc]

theorem diag_mulVec {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, i ≠ j → M i j = 0) (w : Fin n → R) (i : Fin n) : (M *ᵥ w) i = M i i * w i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj => by rw [h i j (Ne.symm hj), zero_mul]) (by simp)

theorem inv_offdiag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    ∀ i j, i ≠ j → (t⁻¹).1 i j = 0 := by
  intro i j hij
  have h1 : ((t⁻¹).1 * t.1) i j = 0 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne hij]
  have h2 : (t.1 * (t⁻¹).1) j j = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht k j hk, mul_zero]) (by simp)] at h1
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht j k (Ne.symm hk), zero_mul]) (by simp)] at h2
  calc (t⁻¹).1 i j = (t⁻¹).1 i j * (t.1 j j * (t⁻¹).1 j j) := by rw [h2, mul_one]
    _ = 0 := by rw [← mul_assoc, h1, zero_mul]

theorem inv_mul_diag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i : Fin n) :
    (t⁻¹).1 i i * t.1 i i = 1 := by
  have h1 : ((t⁻¹).1 * t.1) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [ht k i hk, mul_zero]) (by simp)] at h1

theorem adj_apply' {m n : ℕ} (x : Mx D m n) (i : Fin n) (j : Fin m) : GlobalTheory.MixModel.adj x i j = cA D (x j i) := rfl

theorem cA_sub_one {a : AE D} (h : finPart D (a - 1) ∈ intAE D) : finPart D (cA D a - 1) ∈ intAE D := by
  rw [← map_one (cA D), ← map_sub]
  exact (GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 h

end GlobalTheory.FinPl.LeviUnitK


open GlobalTheory.FinPl.LeviUnitK in
theorem GlobalTheory.FinPl.LeviUnitK.inK_levi : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  intro D S S₀ ρ d L L₀ v _hL hM t ht hg hu
  refine ⟨hg, fun y _ => ?_⟩
  have ht' := inv_offdiag t ht
  have hadj : ∀ i j, i ≠ j → GlobalTheory.MixModel.adj (t⁻¹).1 i j = 0 := fun i j hij => by
    rw [adj_apply', ht' j i (Ne.symm hij), map_zero]
  have eX : ∀ i, (d.pX *ᵥ (mt S (d.levi t) *ᵥ y)) i = t.1 i i * (d.pX *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pX_levi t, ← Matrix.mulVec_mulVec, diag_mulVec ht]
  have eY : ∀ i, (d.pY *ᵥ (mt S (d.levi t) *ᵥ y)) i = cA D ((t⁻¹).1 i i) * (d.pY *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pY_levi t, ← Matrix.mulVec_mulVec, diag_mulVec hadj, adj_apply']
  have e0 : d.p0 *ᵥ (mt S (d.levi t) *ᵥ y) = d.p0 *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi t]
  rw [hM y, hM (mt S (d.levi t) *ᵥ y), e0]
  simp only [eX, eY, colMul_mul]
  have hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => t.1 i i * colMul d.jX i ((d.pX *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (hu i).1.2 (hu i).2.2 (inv_mul_diag t ht i) _
  have hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => cA D ((t⁻¹).1 i i) * colMul d.jY i ((d.pY *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (cA_sub_one (hu i).2.2) (cA_sub_one (hu i).1.2)
      (by rw [← map_mul, mul_comm, inv_mul_diag t ht i, map_one]) _
  exact and_congr (forall_congr' hX) (and_congr (forall_congr' hY) Iff.rfl)

end
end

