module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotent
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibQ

section Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mulVecHomeo {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₜ (Fin t → k) where
  toFun v := (w : Matrix (Fin t) (Fin t) k).mulVec v
  invFun v := ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v
  left_inv v := by
    show ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec ((w : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    show (w : Matrix (Fin t) (Fin t) k).mulVec (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem smInt_transform {t : ℕ} [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Φ Ψ : (Fin t → k) → X) (B : X →ₗ[ℂ] Y) (A : Y →ₗ[ℂ] Y) (w : GL (Fin t) k)
    (lΦ : IsLocallyConstant Φ) (cΦ : HasCompactSupport Φ)
    (lΨ : IsLocallyConstant Ψ) (cΨ : HasCompactSupport Ψ)
    (h : ∀ v, B (Φ v) = A (B (Ψ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)))) :
    B (smInt μ Φ) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) := by
  have lG : IsLocallyConstant (B ∘ Ψ) := lΨ.comp B
  have cG : HasCompactSupport (B ∘ Ψ) := cΨ.comp_left (map_zero B)
  have lGL : IsLocallyConstant ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := lG.comp_continuous (mulVecHomeo w⁻¹).continuous
  have cGL : HasCompactSupport ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := cG.comp_homeomorph (mulVecHomeo w⁻¹)
  calc B (smInt μ Φ) = smInt μ (B ∘ Φ) := (SmIntEl.smInt_linear μ B lΦ cΦ).symm
    _ = smInt μ (A ∘ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := congrArg (smInt μ) (funext h)
    _ = A (smInt μ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := SmIntEl.smInt_linear μ A lGL cGL
    _ = A (((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ (B ∘ Ψ)) :=
        congrArg A (_root_.GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec k t μ w (B ∘ Ψ) lG cG)
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (smInt μ (B ∘ Ψ)) := map_smul A _ _
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) :=
        congrArg (fun z => ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A z) (SmIntEl.smInt_linear μ B lΨ cΨ)

end Abstract

section Group

variable (k : Type) [Field k]

theorem point_eq (i t : ℕ) (q g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (u : Fin t → k)
    (hx : ((q⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t u) :
    uM k (i + t) y * levi k (i + t) (q * g) =
      levi k (i + t) q * uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t u) * levi k (i + t) g) := by
  have h := levi_mul_uM k (i + t) q⁻¹ y
  rw [hx, uM_add, map_inv] at h
  have h2 : uM k (i + t) y =
      levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) :=
    inv_mul_eq_iff_eq_mul.mp h
  calc uM k (i + t) y * levi k (i + t) (q * g)
      = levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) *
          (levi k (i + t) q * levi k (i + t) g) := by rw [map_mul, ← h2]
    _ = _ := by group

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : GL (Fin i) k) (x : Fin i → k) (w : GL (Fin t) k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (levi k i a * uM k i x, w) z) =
      extTensor (psiMinus k τ) σ (a, w) (clT τ W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v u =>
    have e : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) v) = (twKer τ (MirUin k i) 1).mkQ v := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨uM k i x, uM_mem k i x⟩, v, ?_⟩)
      simp
    have e2 : (twKer τ (MirUin k i) 1).mkQ (τ (levi k i a * uM k i x) v) =
        psiMinus k τ a ((twKer τ (MirUin k i) 1).mkQ v) := by
      rw [← e, map_mul]
      rfl
    simp only [clT, extTensor_tmul, LinearMap.rTensor_tmul]
    rw [e2]

theorem fibV_mul (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k) (v u : Fin t → k) (x : Fin i → k)
    (hx : (((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t u) :
    fibV f ((q : GL (Fin (i + t)) k) * g) v =
      extTensor τ σ (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) (fibV f g u) := by
  obtain ⟨m1, p1⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj k i t q
  obtain ⟨m2, p2⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main k i t x
  have key := f.1.1.2 ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) (uM k (i + t) (midV k i t u) * levi k (i + t) g)
  have e : pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) =
      (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) := by
    rw [map_mul, p1, p2]
    simp
  calc fibV f ((q : GL (Fin (i + t)) k) * g) v
      = f.1.1.1 (levi k (i + t) (q : GL (Fin (i + t)) k) * uM k (i + t) (topV k i t x) *
          (uM k (i + t) (midV k i t u) * levi k (i + t) g)) :=
        congrArg f.1.1.1 (point_eq k i t _ g _ x u hx)
    _ = extTensor τ σ (pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩)) (fibV f g u) := key
    _ = _ := congrArg (fun y => extTensor τ σ y (fibV f g u)) e

end Rep

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k), fibInt μ f ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (fibInt μ f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f q g
  have h1 := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main k i t τ σ hτ hσ f ((q : GL (Fin (i + t)) k) * g)
  have h2 := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main k i t τ σ hτ hσ f g
  have hpt : ∀ v, clT τ W (fibV f ((q : GL (Fin (i + t)) k) * g) v) =
      extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)
        (clT τ W (fibV f g ((((qBlocks k i t q).2⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v))) := by
    intro v
    obtain ⟨x, hx⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top k i t q⁻¹ v
    have hb : (qBlocks k i t q⁻¹).2 = (qBlocks k i t q).2⁻¹ := by
      rw [map_inv, Prod.snd_inv]
    rw [hb] at hx
    have e := fibV_mul τ σ f q g v _ x hx
    exact (congrArg (clT τ W) e).trans (clT_extTensor τ σ _ x _ _)
  exact smInt_transform μ _ _ (clT τ W)
    (extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)) (qBlocks k i t q).2
    h1.1 h1.2 h2.1 h2.2 hpt

end GlobalTheory.CompanionTheory.BZPsiPG.FibQ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteJacquetKernelCommonLattice
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section Exhaust

variable {k : Type} [Field k] [ValuativeRel k]

theorem Lc_le_Lc_mul (n : ℕ) (c : k) {d : k} (hd : d ∈ 𝒪[k]) : Lc n c ≤ Lc n (c * d) := by
  intro y hy j
  have h : c * d * y.toAdd j = d * (c * y.toAdd j) := by ring
  rw [h]
  exact mul_mem hd (hy j)

theorem exists_integral_mul (y : k) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ c * y ∈ 𝒪[k] := by
  by_cases hy : y ∈ 𝒪[k]
  · exact ⟨1, one_mem _, one_ne_zero, by rwa [one_mul]⟩
  · have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
    refine ⟨y⁻¹, ?_, inv_ne_zero hy0, ?_⟩
    · rw [Valuation.mem_integer_iff] at hy ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hy))
    · rw [inv_mul_cancel₀ hy0]
      exact one_mem _

theorem exists_mem_Lc (n : ℕ) (y : Multiplicative (Fin n → k)) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ y ∈ Lc n c := by
  choose f hf hf0 hfy using fun j => exists_integral_mul (y.toAdd j)
  refine ⟨∏ j, f j, prod_mem fun j _ => hf j, Finset.prod_ne_zero_iff.2 fun j _ => hf0 j, ?_⟩
  intro j
  have h : (∏ i, f i) * y.toAdd j = (∏ i ∈ Finset.univ.erase j, f i) * (f j * y.toAdd j) := by
    rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ j)]
    ring
  rw [h]
  exact mul_mem (prod_mem fun i _ => hf i) (hfy j)

variable {X : Type} [AddCommGroup X] [Module ℂ X]

theorem twKer_Lc_mono {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) {d : k}
    (hd : d ∈ 𝒪[k]) : twKer ρ (Lc n c) 1 ≤ twKer ρ (Lc n (c * d)) 1 := by
  refine Submodule.span_mono ?_
  rintro w ⟨m, v, rfl⟩
  exact ⟨⟨m.1, Lc_le_Lc_mul n c hd m.2⟩, v, rfl⟩

theorem exists_mem_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) {x : X}
    (hx : x ∈ twKer ρ ⊤ 1) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ x ∈ twKer ρ (Lc n c) 1 := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, v, rfl⟩ := hw
    obtain ⟨c, hc, hc0, hm⟩ := exists_mem_Lc n m.1
    exact ⟨c, hc, hc0, Submodule.subset_span ⟨⟨m.1, hm⟩, v, rfl⟩⟩
  | zero => exact ⟨1, one_mem _, one_ne_zero, zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc0, hca⟩ := ha
    obtain ⟨d, hd, hd0, hdb⟩ := hb
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, add_mem (twKer_Lc_mono ρ c hd hca) ?_⟩
    rw [mul_comm c d]
    exact twKer_Lc_mono ρ d hc hdb
  | smul a b _ hb =>
    obtain ⟨c, hc, hc0, hcb⟩ := hb
    exact ⟨c, hc, hc0, Submodule.smul_mem _ a hcb⟩

theorem exists_integral_finite_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X)
    {S : Set X} (hS : S.Finite) (h : ∀ x ∈ S, x ∈ twKer ρ ⊤ 1) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, one_ne_zero, fun x hx => absurd hx (Set.notMem_empty x)⟩
  | @insert a s _ _ ih =>
    obtain ⟨c, hc, hc0, hcs⟩ := ih fun x hx => h x (Set.mem_insert_of_mem a hx)
    obtain ⟨d, hd, hd0, hda⟩ := exists_mem_twKer_Lc ρ (h a (Set.mem_insert a s))
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, ?_⟩
    rintro x (rfl | hx)
    · rw [mul_comm c d]
      exact twKer_Lc_mono ρ d hc hda
    · exact twKer_Lc_mono ρ c hd (hcs x hx)

end Exhaust

theorem exists_Lc_finite_twKer :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ S hS h
  obtain ⟨c, -, hc0, hc⟩ := exists_integral_finite_twKer_Lc ρ hS h
  exact ⟨c, hc0, hc⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.NodeFlat

theorem flatFn_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  intro E _ _ _ r s e₁ e₂ h₁ h₂
  have ap : ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
      (c : GL (Fin (r + s)) (Af E)), c ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s) →
      nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 :=
    fun u m k c hc => _root_.GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply e₁ e₂ h₁ h₂ u m k c hc
  have hleft : ∀ (v : BlockIx (r + s) r → Ad E) (x : GA E (r + s)),
      nodeFn e₁ e₂ (unip v * x) = nodeFn e₁ e₂ x := by
    intro v x
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [← mul_assoc, ← mul_assoc, ← PositivityTheory.Rg.Rs.InducedTensorMap.D.unip_add', ap _ _ _ _ hc, ap _ _ _ _ hc]
  have hright : ∀ (x : GA E (r + s)) (k' : Kinf E (r + s)), ∀ c' ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s),
      nodeFn e₁ e₂ (x * cf (r + s) k' c') = nodeFn e₁ e₂ x := by
    intro x k' c' hc'
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [mul_assoc _ (cf (r + s) k c), PositivityTheory.Rg.Rs.InducedTensorMap.cf_mul,
      ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).mul_mem hc hc'), ap _ _ _ _ hc]
  have key : ∀ m : GA E r × GA E s,
      ContDiffAt ℝ ∞ (chart (nodeFn e₁ e₂) (lev (Ad E) r s m)) (oneL E (r + s)) := by
    intro m
    obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
    have c₁ : ContDiffAt ℝ ∞ (fun y => e₁ (m.1 * infGL E r (b₁ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₁.sm m.1 (val_mem_invSet (b₁ (oneL E (r + s))))).comp (oneL E (r + s)) hb₁
      simpa only [Function.comp_def, chart_val] using this
    have c₂ : ContDiffAt ℝ ∞ (fun y => e₂ (m.2 * infGL E s (b₂ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₂.sm m.2 (val_mem_invSet (b₂ (oneL E (r + s))))).comp (oneL E (r + s)) hb₂
      simpa only [Function.comp_def, chart_val] using this
    refine ContDiffAt.congr_of_eventuallyEq (c₁.mul c₂) ?_
    filter_upwards [hloc] with y hy
    have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
      show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
      rw [← hy]
      rfl
    conv_lhs => rw [hyw, chart_val]
    obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
    rw [hv, ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).one_mem)]
  refine ⟨fun x => ?_, hright, ?_⟩
  · obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [ap _ _ _ _ hc]
    exact mul_ne_zero (h₁.ne _) (h₂.ne _)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, hg, rfl⟩ := exists_iw x
  have e1 : chart (nodeFn e₁ e₂) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (nodeFn e₁ e₂) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact hleft u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => nodeFn e₁ e₂ (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      nodeFn e₁ e₂ := by
    funext z
    show nodeFn e₁ e₂ (z * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k)) = nodeFn e₁ e₂ z
    rw [mul_assoc, ← infGL_comm]
    exact hright z k g hg
  rw [e2]
  exact key m

end GlobalTheory.CompanionTheory.LimV.NodeFlat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlock
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HtPull

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_one)
open GlobalTheory.StdUnn.Model

def leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) : GL (Fin n) R :=
  ⟨bl hn a.1 0 0 1, bl hn (a⁻¹).1 0 0 1,
    by rw [blockMatrix_multiply]; simp [blockMatrix_one], by rw [blockMatrix_multiply]; simp [blockMatrix_one]⟩

theorem det_leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) :
    Matrix.GeneralLinearGroup.det (leviBl hn a) = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, leviBl, bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMatrix_zero {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero, Matrix.submatrix_zero, Pi.zero_apply]

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem isHt_blockPull : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  intro D n ρ p hn ι hc hblk H hH
  refine ⟨hH.1.comp hc, fun g => hH.2.1 _, ?_⟩
  intro q hq a ha g
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  rw [ha] at hm
  have hι := hblk q a.1 b 0 d hm
  rw [blockMatrix_zero] at hι
  have hqP : ι q ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hι
  have hA : blkA (mat (ι q)) = (leviBl hn a).1 := by
    rw [hι, blkA_blk4]
    rfl
  show H (ι (q * g)) = _ * H (ι g)
  rw [map_mul, hH.2.2 _ hqP (leviBl hn a) hA, det_leviBl]

end GlobalTheory.CompanionTheory.HtPull

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermScaleMain
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem hermScale_main : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Em.TopX → PositivityTheory.Rg.Rsw.Em.HermScale := by
  intro hid htop D t S e he lam hlam g hg
  obtain ⟨hee, hce⟩ := (hid D S).2 e he
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t t) := i1
  haveI : LocallyCompactSpace (Mx D t t) := i2
  haveI : SecondCountableTopology (Mx D t t) := i3
  haveI : T2Space (Mx D t t) := i4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D t) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D t) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D t) :=
    (isClosed_hermA (D := D) (r := t)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨-, -, -, -, -, -, hb, hs2, hlc⟩ := htop D 0 0 t e
  haveI : BorelSpace (hermS D t e) := hb
  haveI : SecondCountableTopology (hermS D t e) := hs2
  haveI : LocallyCompactSpace (hermS D t e) := hlc
  haveI : T2Space (hermS D t e) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : lam.IsAddHaarMeasure := hlam
  set U := restr (hermA D t) (GlobalTheory.ModuLR.lrCE g (ad g)⁻¹) (lr_herm g) (lr_herm_symm g) with hUdef
  have hU : ∀ s ∈ hermS D t e, U s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hU' : ∀ s ∈ hermS D t e, U.symm s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hPm : ∀ x, smulH (n := t) e hce x ∈ hermS D t e := fun x => by
    change e • e • x.1 = e • x.1
    rw [smul_smul, hee]
  have hPs : ∀ s ∈ hermS D t e, smulH (n := t) e hce s = s := fun s hs => Subtype.ext hs
  have hfix : ∀ x, smulH (n := t) e hce x = 0 → U x = x := fun x hx =>
    Subtype.ext (sandwich_fix g hg x (congrArg Subtype.val hx))
  have hchar := char_restr (hermS D t e) (smulH e hce) (continuous_smulH e hce) hPm hPs U hU hU' hfix
  rw [char_herm g] at hchar
  set c := restr (hermS D t e) U hU hU' with hc
  refine ⟨c, fun x => rfl, ?_⟩
  have key := addEquivAddHaarChar_smul_map lam c
  have hne : addEquivAddHaarChar c ≠ 0 := (addEquivAddHaarChar_pos c).ne'
  have hmap : lam.map c = (addEquivAddHaarChar c)⁻¹ • lam := by
    calc lam.map c = ((addEquivAddHaarChar c)⁻¹ * addEquivAddHaarChar c) • lam.map c := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar c)⁻¹ • lam := by rw [mul_smul, key]
  rw [hmap, hchar, inv_pow]

end Main

end GlobalTheory.CompanionTheory.HermSc
end
end

