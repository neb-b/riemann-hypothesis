module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesBorelSphericalIntegralCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapRowEqZeroUnlessRowMemDualLattice
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

theorem val_row_le_of_Phi_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + 1 + c = s) (r : ℕ)
    (hc : c = 2 * r) (w : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hw : (S.T t).Phi j (c + 1) (by omega) w ≠ 0) (y : XIx (Fin κ) t j) :
    valuation k (w (Sum.inr ⟨r, by omega⟩) (Sum.inl y)) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : (S.T t).Phi j (c + 1) (by omega) w = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') w).submatrix (ixSucc _ t j) id) := rfl
  rw [hΦ] at hw
  have hI := TypeDatum.intM_of_Phi_ne_zero _ _ hw ((ixSucc _ t j).symm (o.symm (Sum.inr ⟨r, by omega⟩)))
    (o'.symm (Sum.inl y))
  have hw' : w = fromBlocks w.toBlocks₁₁ w.toBlocks₁₂ w.toBlocks₂₁ w.toBlocks₂₂ := (fromBlocks_toBlocks w).symm
  rw [hw'] at hI
  simp [LatFrame.coords, typeFrame, embA, GlobalTheory.SplitFlip.diagGL, fromBlocks_multiply] at hI
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀] at hI
  have hv : 0 < valuation k ((S.ϖ : k) ^ (r + 1)) := by
    rw [zero_lt_iff]; simp
  rw [Units.val_pow_eq_pow_val]
  change valuation k (w.toBlocks₂₁ ⟨r, by omega⟩ y) ≤ _
  rwa [inv_mul_le_iff₀ hv, mul_one] at hI

theorem flRow_eq_zero_of_not_mem_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by
  intro k _ _ _ _ _ _ ν s κ S t _ _ j c H r hc x hx
  obtain ⟨y, hy⟩ : ∃ y, ¬ valuation k (x (Sum.inr ()) y) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
    by_contra h
    push_neg at h
    exact hx fun i => h i
  unfold flRow opE
  refine (integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)).trans (integral_zero _ _)
  simp only [Pi.zero_apply]
  refine mul_eq_zero_of_left ?_ _
  by_contra hne
  have h1 := val_row_le_of_Phi_ne_zero S t j c H r hc _ hne y
  apply hy
  convert h1 using 2
  simp [affPt, basePt, rowAt, Free]
end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslate
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat


open GlobalTheory.RootEx.Exchange in
theorem flRow_eq_opE_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp hpc Φ hΦ x
  have := hν
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  have h := opE_rowE hψ ν 1 q (χ := fun _ => (1 : ℂ)) continuous_const hΦ.1.continuous x.toRows₁
    (x (Sum.inr ()))
  refine Eq.trans ?_ (h.symm.trans ?_)
  swap
  · rw [one_mul]
    congr 1
    funext z
    exact om_rowE _ _ _ _ _
  unfold flRow opE
  congr 1
  funext e
  have key : affPt (q.val + 1) x.toRows₁ e + rowAt n c (q.val + 1) (x (Sum.inr ())) =
      mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ()))) := by
    rw [affPt_eq]
    ext r s
    rcases r with r | r <;> rcases s with s | s <;>
      simp [mat, rowAt, gRow, Fin.val_inj, add_assoc]
  have hch : ch (mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ())))) =
      ch (affPt (q.val + 1) x.toRows₁ e) := by
    rw [affPt_eq]
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mat, gRow]
  simp only [big]
  rw [key, hch, one_mul]

end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalEigenfunction
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev IntCos (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :=
  {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k]}


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem int_mul {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j : Fin n) :
    (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨g, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem out_smul (y : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), ((y • c).out : GL (Fin n) k) = y * c.out * κ := by
  refine ⟨(y * c.out)⁻¹ * (y • c).out, ?_, by group⟩
  have h : (QuotientGroup.mk (y * c.out) : GL (Fin n) k ⧸ KO k (Fin n)) = y • c := by
    conv_rhs => rw [← QuotientGroup.out_eq' c]
    rfl
  exact QuotientGroup.eq.1 (h.trans (QuotientGroup.out_eq' _).symm)

theorem int_out_smul {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) (c : IntCos k n) (i j : Fin n) :
    ((y • c.1).out : GL (Fin n) k).1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, hκ, e⟩ := out_smul y c.1
  rw [e, Units.val_mul, Units.val_mul]
  exact int_mul (int_mul ((SplitFlip.mem_KO_iff y).1 hy).1 c.2) ((SplitFlip.mem_KO_iff κ).1 hκ).1 i j

def smulEquiv {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) : IntCos k n ≃ IntCos k n where
  toFun c := ⟨y • c.1, int_out_smul hy c⟩
  invFun c := ⟨y⁻¹ • c.1, int_out_smul (inv_mem hy) c⟩
  left_inv c := Subtype.ext (inv_smul_smul y c.1)
  right_inv c := Subtype.ext (smul_inv_smul y c.1)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_mul_upper {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA i j h, zero_mul]
    · rw [hB j i h, mul_zero]
  · simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have h := Matrix.det_of_upperTriangular (M := (b : Matrix (Fin n) (Fin n) k)) (fun i j h => (mem_borel k).1 hb i j h)
  have hd : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero b
  rw [h] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def diagU {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : kˣ := Units.mk0 _ (diag_ne_zero hb i)

theorem exists_borel_mul (h : GL (Fin n) k) : ∃ b ∈ borel k (Fin n), ∃ x ∈ KO k (Fin n), h = b * x := by
  obtain ⟨b, hbT, x, hx, e⟩ := iwasawa_blockTriangular k (Fin n) (fun i => (i : ℕ)) h
  exact ⟨b, (mem_borel k).2 fun i j hij => hbT (show (j : ℕ) < i from hij), x, hx, e⟩

theorem sph_borel_mul {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (h : GL (Fin n) k) :
    φ (b * h) = (∏ i, γ i ^ ord k (diagU hb i)) * φ h := by
  obtain ⟨b', hb', x, hx, rfl⟩ := exists_borel_mul h
  have hbb : b * b' ∈ borel k (Fin n) := mul_mem hb hb'
  rw [← mul_assoc, hφ.1 _ x hx, hφ.1 _ x hx, hφ.2 b' hb' (diagU hb') fun i => rfl,
    hφ.2 (b * b') hbb (fun i => diagU hb i * diagU hb' i) fun i => ?_, ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [ord_mul, zpow_add₀ (hγ i)]
  · rw [Units.val_mul, Units.val_mul]
    exact diag_mul_upper ((mem_borel k).1 hb) ((mem_borel k).1 hb') i

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

theorem hasSum_hecke_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  intro k _ _ _ _ n γ φ hφ hγ X hX g
  obtain ⟨b, hb, x, hx, rfl⟩ := exists_borel_mul g
  have hI := (_root_.GlobalTheory.HeckeSeries.hasSum_integral_cosets k n γ φ hφ X hX).mul_left (∏ i, γ i ^ ord k (diagU hb i))
  have key : ∀ c : IntCos k n,
      X ^ (ord k (Matrix.GeneralLinearGroup.det (smulEquiv (inv_mem hx) c).1.out)).toNat *
          φ (b * x * (smulEquiv (inv_mem hx) c).1.out) =
        (∏ i, γ i ^ ord k (diagU hb i)) * (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := by
    intro c
    obtain ⟨κ, hκ, e⟩ := out_smul x⁻¹ c.1
    have e' : (smulEquiv (inv_mem hx) c).1.out = x⁻¹ * c.1.out * κ := e
    have hd : ord k (Matrix.GeneralLinearGroup.det (x⁻¹ * c.1.out * κ)) =
        ord k (Matrix.GeneralLinearGroup.det c.1.out) := by
      rw [map_mul, map_mul, ord_mul, ord_mul, ord_det_of_mem_KO (inv_mem hx), ord_det_of_mem_KO hκ]
      ring
    rw [e', hd, show b * x * (x⁻¹ * c.1.out * κ) = b * c.1.out * κ by group, hφ.1 _ κ hκ,
      sph_borel_mul hφ hγ hb]
    ring
  have h1 : HasSum ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
      φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx))
      ((∏ i, γ i ^ ord k (diagU hb i)) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
    have hf : ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx)) = fun c : IntCos k n => (∏ i, γ i ^ ord k (diagU hb i)) *
          (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := funext key
    rw [hf]
    exact hI
  have h2 := (Equiv.hasSum_iff (smulEquiv (inv_mem hx))).1 h1
  rw [hφ.1 b x hx, hφ.2 b hb (diagU hb) fun i => rfl, mul_comm]
  exact h2

end GlobalTheory.HeckeShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverse
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeDual

open GlobalTheory.SatakeFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma isBorelSph_comp_invRevT {γ : Fin n → ℂ}
    {φ : GL (Fin n) k → ℂ} (hφ : _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ) :
    _root_.GlobalTheory.SatakeBound.IsBorelSph k (fun i => (γ i.rev)⁻¹)
      (fun g => φ (_root_.GlobalTheory.SatakeFlip.invRevT g)) := by
  obtain ⟨hK, hB⟩ := hφ
  refine ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩
  · show φ (_root_.GlobalTheory.SatakeFlip.invRevT (g * x)) = φ (_root_.GlobalTheory.SatakeFlip.invRevT g)
    rw [map_mul]
    exact hK _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx)
  · have hb' := _root_.GlobalTheory.SatakeFlip.invRevT_mem_borel hb
    show φ (_root_.GlobalTheory.SatakeFlip.invRevT b) = _
    rw [hB _ hb' (fun i => (t i.rev)⁻¹) ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp [_root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg, zpow_neg, inv_zpow]
    · intro i
      rw [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
      have hi := _root_.GlobalTheory.SatakeFlip.inv_diag_mul hb i.rev
      rw [ht] at hi
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hi

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma exists_cosetMap_out_eq_invRevT_mul
    (c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
      (_root_.GlobalTheory.SatakeFlip.cosetMap c).out = _root_.GlobalTheory.SatakeFlip.invRevT c.out * x := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
    (_root_.GlobalTheory.SatakeFlip.invRevT c.out)
  refine ⟨x, x.2, ?_⟩
  rw [← hx, ← _root_.GlobalTheory.SatakeFlip.cosetMap_mk, QuotientGroup.out_eq']

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma mul_entries_integral {g h : GL (Fin n) k}
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k])
    (hh : ∀ i j, (h : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]) :
    ∀ i j, ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg i l) (hh l j)

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma invRevT_entries_integral_iff_inv (g : GL (Fin n) k) :
    (∀ i j, ((_root_.GlobalTheory.SatakeFlip.invRevT g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈
      𝒪[k]) ↔ ∀ i j, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
  constructor
  · intro h i j
    simpa using h j.rev i.rev
  · intro h i j
    exact h _ _

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma det_invRevT' (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeFlip.invRevT g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det ((↑g⁻¹ : Matrix (Fin n) (Fin n) k).transpose.submatrix Fin.rev Fin.rev) = _
  exact (Matrix.det_submatrix_equiv_self Fin.revPerm _).trans (Matrix.det_transpose _)

open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma ord_det_eq_zero_of_mem_KO {x : GL (Fin n) k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det x) = 0 := by
  have h := _root_.GlobalTheory.GLDoubling.nabs_det_of_mem_KO hx
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow] at h
  have hq : (1 : ℝ) < _root_.GlobalTheory.SplitWeil.resCard k := by
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  have := zpow_right_injective₀ (by positivity) hq.ne' (h.trans (zpow_zero _).symm)
  simpa using this


open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
theorem _root_.GlobalTheory.HeckeDual.hasSum_dual : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (-_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  intro k _ _ _ _ n γ φ hφ _ X hX
  have hrev : ∀ i : Fin n, (i.rev : ℕ) = n - 1 - i := fun i => by rw [Fin.val_rev]; omega
  have hX' : ∀ i : Fin n,
      ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (γ i.rev)⁻¹ * X‖ < 1 := by
    intro i
    have hi := hX i.rev
    rwa [hrev] at hi
  have H := _root_.GlobalTheory.HeckeSeries.hasSum_integral_cosets k n _ _
    (isBorelSph_comp_invRevT hφ) X hX'
  have hprod : ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) *
      (γ i.rev)⁻¹ * X)⁻¹ =
      ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹ :=
    Fintype.prod_equiv Fin.revPerm _ _ fun i => by rw [Fin.revPerm_apply, hrev]
  rw [hprod] at H
  let e : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} ≃
      {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    { toFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc]
        exact mul_entries_integral
          ((invRevT_entries_integral_iff_inv _).mpr c.2)
          ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).1⟩
      invFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc, mul_inv_rev, ← map_inv]
        refine mul_entries_integral ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).2 ?_
        refine (invRevT_entries_integral_iff_inv _).mpr ?_
        simpa using c.2⟩
      left_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1)
      right_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1) }
  convert e.hasSum_iff.mpr H using 1
  funext c
  obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
  show _ = X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det
      (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)).toNat *
    φ (_root_.GlobalTheory.SatakeFlip.invRevT (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)
  rw [hc, map_mul _root_.GlobalTheory.SatakeFlip.invRevT, _root_.GlobalTheory.SatakeFlip.invRevT_invRevT,
    hφ.1 _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx), map_mul,
    _root_.GlobalTheory.SmGL.ord_mul, det_invRevT', _root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg,
    ord_det_eq_zero_of_mem_KO hx, add_zero]

end GlobalTheory.HeckeDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchange
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL step_two)

noncomputable section
namespace GlobalTheory.PosOne.RrStep

theorem rr_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hc ψ hψ hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B B₁ hB hB₁ F ρ' hρ' Rr hRr Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  let ω : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :=
    (omR μ).comp (MonoidHom.inl _ _)
  obtain rfl : ρ' = ω :=
    MonoidHom.ext fun g => LinearMap.ext fun Φ => Subtype.ext (hρ' g Φ)
  have hω : IsSmoothRep ω := fun Φ =>
    (omR_smooth hμ Φ).preimage (continuous_id.prodMk continuous_const)

  let π' : Representation ℂ (GL n' k) (GL n' k →₀ ℂ) :=
    { toFun := fun g => Finsupp.lmapDomain ℂ ℂ (g * ·)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  let π : Representation ℂ (GL n k) (SB (Matrix n n' k)) := (omR μ).comp (MonoidHom.inr _ _)
  let θ : (GL n' k →₀ ℂ) →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n n' k) :=
    Finsupp.lsum ℂ fun g₀ => LinearMap.toSpanSingleton ℂ _ (omR μ (g₀⁻¹, 1))
  have hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ) := by
    intro g h φ Ψ Ψ' e
    obtain rfl : Ψ' = omR μ (g, h) Ψ := Subtype.ext e
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂]
    | single g₀ a =>
      simp only [π', MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, θ, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, map_smul, π, MonoidHom.coe_comp,
        Function.comp_apply, MonoidHom.inr_apply, omR_mul, smul_eq_mul]
      rw [show ((g * g₀)⁻¹ * g, 1 * h) = (1 * g₀⁻¹, h * 1) from Prod.ext (by group) (by group)]
  have hθ1 : ∀ Ψ, θ (Finsupp.single 1 1) Ψ = Ψ := fun Ψ => by
    simp only [θ, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul, inv_one]
    exact Subtype.ext (om_one μ Ψ.1)
  have hb : IsPos ψ p π σ B := ⟨hB.1, fun g φ v => hB.2 g φ (π g φ) v rfl⟩
  have happ : ∀ (q : ℕ) (B₀ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ)
      (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ q σ B₀ F Φ.1 = fun h => B₀ (opL hψ ν q (omR μ (1, h) Φ)) (σ h F) := by
    intro q B₀ Φ
    funext h
    exact GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe B₀ (opL hψ ν q (omR μ (1, h) Φ)) ▸ rfl
  have uniq := fun q h1 h2 f => (GlobalTheory.QuotInt.quotInt_unique_exists k n c q h1 h2 ν μX μG f).1
  have hRr' : ∀ Φ, IsQuotInt ν μX μG p (fun h => B (opL hψ ν p (omR μ (1, h) Φ)) (σ h F)) (Rr Φ) :=
    fun Φ => happ p B Φ ▸ hRr Φ

  have hL : IsNEquiv ψ p ω Rr := fun g hg Φ => by
    rw [← smul_eq_mul, ← map_smul]
    refine uniq p hp hc.le _ _ _ (hRr' _) ?_
    have e : ∀ h, opL hψ ν p (omR μ (1, h) (ω g Φ)) =
        opL hψ ν p (omR μ (1, h) ((ψ (simpleSum g) : ℂ) • Φ)) := fun h => by
      have := GlobalTheory.RootExSource.opE_om_source k n n' c p hp hc.le ψ ν μ (omR μ (1, h) Φ).1 g hg
      rw [← omR_val, omR_mul, mul_one, one_mul] at this
      show opL hψ ν p (omR μ (1, h) (omR μ (g, 1) Φ)) = _
      rw [omR_mul, mul_one, one_mul, map_smul, map_smul]
      exact Subtype.ext this
    exact (funext fun h => congrArg (fun Ψ => B Ψ (σ h F)) (e h)) ▸ hRr' _

  obtain ⟨C, hC, H⟩ := step_two hψ ν (Finsupp.single 1 1) F hp hc hψ1 hμ hσ μX μG hθ hb hB₁ Φ
  have s1 := ((ExchangeSupport.exchange_support k n' (c + 1) p hp (by omega) ψ hψ hψ1 ν _ ω hω Rr Φ).1 hL).1
  obtain ⟨χ, hχ, h1⟩ := _root_.GlobalTheory.RootEx.exists_mem_SB_eq_one_on_compact k n' _ (hC.union s1.2)
  have hT : IsLocallyConstant fun u : n' → k => χ u • ω (rowE (c + 1) p u) Φ :=
    (hχ.1.prodMk ((orbit_locallyConstant hω Φ).comp_continuous ExchangeSupport.continuous_rowE)).comp
      fun q => q.1 • q.2
  obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
    (Measure.pi fun _ => ν) _ _ hT _ hχ.2
    fun u hu => by simp only [image_eq_zero_of_notMem_tsupport hu, zero_smul]
  simp only [map_smul, smul_eq_mul] at hΦ'
  obtain ⟨z, hz1, hz2⟩ := H χ hχ.1 (fun u hu => h1 u (Or.inl hu)) Φ' hΦ'
  have e : exUp ν p ω Rr Φ = Rr Φ' := by
    rw [hΦ', exUp]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ tsupport fun u : n' → k => Rr (ω (rowE (c + 1) p u) Φ)
    · simp only [h1 u (Or.inr hu), one_mul]
    · have := image_eq_zero_of_notMem_tsupport hu
      simp only [this, mul_zero]
  simp only [hθ1] at hz1 hz2
  rw [happ, e, ← uniq p hp hc.le _ _ _ hz1 (hRr' Φ')]
  exact hz2

end GlobalTheory.PosOne.RrStep
end
end

