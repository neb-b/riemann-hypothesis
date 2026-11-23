module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOne
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.DetPG

def sumSig (a b : Type) : a ⊕ b ≃ Σ x, Two a b x where
  toFun y := match y with
    | Sum.inl i => ⟨false, i⟩
    | Sum.inr j => ⟨true, j⟩
  invFun x := match x with
    | ⟨false, i⟩ => Sum.inl i
    | ⟨true, j⟩ => Sum.inr j
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_hpg (i T : ℕ) (h : HPG k i T) :
    GeneralLinearGroup.det ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
      GeneralLinearGroup.det ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
        GeneralLinearGroup.det (pgProj k i T h).2 := by
  ext
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_det_apply]
  let φ : Fin (i + 1) ⊕ Fin T ≃ Fin (i + T + 1) := (sumSig _ _).trans (ePG i T)
  have hz : ∀ (b : Fin T) (a : Fin (i + 1)),
      (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) : Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k)
        (ePG i T ⟨true, b⟩) (ePG i T ⟨false, a⟩) = 0 := fun b a =>
    mem_parab_iff.1 h.2 true false b a (by decide)
  have hb : (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
        Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k).submatrix φ φ =
      fromBlocks (((pgProj k i T h).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)
        (Matrix.of fun a b => (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
          Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k) (φ (Sum.inl a)) (φ (Sum.inr b))) 0
        ((pgProj k i T h).2 : Matrix (Fin T) (Fin T) k) := by
    ext x y
    rcases x with a | b <;> rcases y with c | d
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) false a c).symm
    · rfl
    · exact hz b c
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) true b d).symm
  rw [← det_submatrix_equiv_self φ, hb]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem dpowM_hpg (i T : ℕ) (s : ℝ) (h : HPG k i T) :
    dpowM (i + T) s (h : Mir k (i + T)) = dpowM i s (pgProj k i T h).1 * dpow T s (pgProj k i T h).2 := by
  show detChar (Fin (i + T + 1)) (absPow k (s : ℂ)) ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
    detChar (Fin (i + 1)) (absPow k (s : ℂ)) ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
      detChar (Fin T) (absPow k (s : ℂ)) (pgProj k i T h).2
  rw [detChar_apply, detChar_apply, detChar_apply, det_hpg, map_mul]

theorem dpow_add' (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem dpow_zero' (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow, absPow_zero]

theorem dpowM_add' (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n s * dpowM n t := by
  ext g
  simp [dpowM, dpow_add']

theorem dpowM_zero' (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero']

theorem complex_units_mul_eq_one_of_mul_eq_one (A B X Y Z : ℂˣ) (h₁ : A * B = 1) (h₂ : X * Y * Z = 1) : A * X * Y * (B * Z) = 1 := by
  have : A * X * Y * (B * Z) = (A * B) * (X * Y * Z) := by ac_rfl
  rw [this, h₁, h₂, one_mul]

theorem exponents_cancel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (h : HPG k i (t + 1)) :
    ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
      (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  have e1 : dpowM (k := k) i (-1 / 2) (pgProj k i (t + 1) h).1 * dpowM i (1 / 2) (pgProj k i (t + 1) h).1 = 1 := by
    have : dpowM (k := k) i (-1 / 2 + 1 / 2) = dpowM i (-1 / 2) * dpowM i (1 / 2) := dpowM_add' _ _ _
    rw [show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpowM_zero'] at this
    rw [← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e2 : dpow (k := k) (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 = 1 := by
    have : dpow (k := k) (t + 1) (-1 / 2 + 1 + -1 / 2) = dpow (t + 1) (-1 / 2) * dpow (t + 1) 1 * dpow (t + 1) (-1 / 2) := by
      rw [dpow_add', dpow_add']
    rw [show (-1 / 2 + 1 + -1 / 2 : ℝ) = 0 by norm_num, dpow_zero'] at this
    rw [← MonoidHom.mul_apply, ← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e : dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      (dpowM i (1 / 2) (pgProj k i (t + 1) h).1 * dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2) = 1 := by
    rw [dpowM_hpg]
    exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ e1 e2
  have := congrArg (Units.val) e
  simpa only [Units.val_mul, Units.val_one] using this

end GlobalTheory.CompanionTheory.BZPhiPG.DetPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactor
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvEqOfCentral
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have : T2Space (GA E N) := by
    have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have : T1Space (GA E N) := T2Space.t1Space
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
section
noncomputable section

open Matrix GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

theorem mul_mem_ball {s : kˣ} (hs : valuation k (s : k) ≤ 1) {x y : k} (hx : x ∈ cball s)
    (hy : y ∈ cball s) : x * y ∈ cball s := by
  show valuation k (x * y) ≤ valuation k (s : k)
  rw [map_mul]
  calc valuation k x * valuation k y ≤ valuation k (s : k) * 1 :=
        mul_le_mul' hx (le_trans hy hs)
    _ = valuation k (s : k) := mul_one _

def NearOne (s : kˣ) {m : ℕ} (A : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ cball s

theorem NearOne.mul {s : kˣ} (hs : valuation k (s : k) ≤ 1) {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) k} (hA : NearOne s A) (hB : NearOne s B) : NearOne s (A * B) := by
  intro a b
  have e : (A * B) a b - (1 : Matrix (Fin m) (Fin m) k) a b =
      ((A - 1) * (B - 1)) a b + (A a b - (1 : Matrix (Fin m) (Fin m) k) a b) +
        (B a b - (1 : Matrix (Fin m) (Fin m) k) a b) := by
    have : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    exact congrFun (congrFun this a) b
  rw [e]
  refine add_mem_cball (add_mem_cball ?_ (hA a b)) (hB a b)
  rw [Matrix.mul_apply]
  exact (ballSub s).sum_mem fun l _ => mul_mem_ball hs (hA a l) (hB l b)


variable (k) in
def congGL (s : kˣ) (hs : valuation k (s : k) ≤ 1) (m : ℕ) : Subgroup (GL (Fin m) k) where
  carrier := {g | NearOne s (g : Matrix (Fin m) (Fin m) k) ∧
    NearOne s ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)}
  one_mem' := by
    constructor <;> intro a b <;> simp [cball]
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact g1.mul hs h1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact h2.mul hs g2
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    exact ⟨g2, by simpa using g1⟩


variable (k) in
def congM (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) : Subgroup (Mir k n) :=
  (congGL k s hs (n + 1)).comap (Mir k n).subtype

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal
section
noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes

variable {n : ℕ}

theorem wtB_union {S T : Finset (Fin n × Fin n)} (h : Disjoint S T) : wtB (S ∪ T) = wtB S + wtB T := by
  funext c
  simp only [wtB, Pi.add_apply, Finset.filter_union]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
  push_cast
  ring

theorem wtB_sdiff {S T : Finset (Fin n × Fin n)} (h : T ⊆ S) : wtB (S \ T) = wtB S - wtB T := by
  have h1 : wtB (S \ T ∪ T) = wtB (S \ T) + wtB T :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset h] at h1
  rw [h1, add_sub_cancel_right]

theorem wtB_lev (lev : Fin n → ℕ) :
    wtB (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) = fun c => 2 * rhoU lev c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev c < lev b).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev b < lev c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  simp only [wtB, rhoU, e1, e2]
  ring

theorem wtB_pos :
    wtB (univ.filter fun p : Fin n × Fin n => p.1 < p.2) = fun c => 2 * rhoV n c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Ioi c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    ext b
    simp
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Iio c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    ext b
    simp
  have hc : (c : ℕ) < n := c.isLt
  simp only [wtB, rhoV, e1, e2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.cast_sub (by omega : (c : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem domC_eq {y z : Fin n → ℝ} (hz : StrictAnti z) {w : Equiv.Perm (Fin n)} (h : z = y ∘ w) : domC y = z := by
  subst h
  have hm : Monotone ((fun a => -y a) ∘ ⇑w) := by
    intro a b hab
    have := hz.antitone hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  have key := (Tuple.comp_sort_eq_comp_iff_monotone (f := fun a => -y a) (σ := w)).mpr hm
  funext a
  have ha := congrFun key a
  simp only [Function.comp_apply, neg_inj] at ha
  simp only [domC, Function.comp_apply]
  exact ha.symm

theorem nsq_eq (x : Fin n → ℝ) : PositivityTheory.RgBcC.RealD.nsq x = Formalism.REAL.nsq x := by
  simp [PositivityTheory.RgBcC.RealD.nsq, Formalism.REAL.nsq, Formalism.REAL.dot, sq]

theorem mem_topTypes {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {ν : Fin n → ℝ}
    (h : IsSecondTypeWeight lam lev ν) : ν ∈ topTypes lam := by
  have hmono : Monotone lev := by
    unfold PositivityTheory.RgBcC.RealD.IsLev at hl
    exact hl.1
  unfold PositivityTheory.RgBcC.RealD.IsSecondTypeWeight at h
  obtain ⟨B, _hB, hBlev, hanti, w, hw⟩ := h
  have hLP : (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)
      ⊆ (univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hmono.reflect_lt hp
  have hBL : B ⊆ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBlev p hp
  have hdisj : Disjoint ((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) B :=
    Finset.sdiff_disjoint.mono_right hBL
  have hid : muQ lam lev + rhoV n - wtB B =
      (fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B) := by
    rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union hdisj, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_sdiff hLP,
      GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_pos, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_lev]
    funext a
    simp only [muQ, Pi.add_apply, Pi.sub_apply]
    ring
  have hdom : domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B)) = ν + rhoV n :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.domC_eq (w := w) hanti (by rw [hw, hid])
  unfold PositivityTheory.RgBcC.RealD.topTypes
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B, ?_, ?_⟩, hanti⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2
    · exact hmono.reflect_lt (hBlev p h1)
  · simp only [hdom, add_sub_cancel_right]

theorem n2T : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  unfold PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter
  intro m lam hlam lev hl ν h
  refine ⟨GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.mem_topTypes hl h, ?_⟩
  rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq]
  exact GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.nsq_lt m lam hlam lev hl ν h

end GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
section
open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
end

