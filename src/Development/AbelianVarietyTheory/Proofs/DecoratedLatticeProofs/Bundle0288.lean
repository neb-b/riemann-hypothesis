module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSmulOfUnitaryEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.BranchMultOne

def blkMat (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if hi : i.1 < n then (if hj : j.1 < n then h ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0)
    else (if j.1 < n then 0 else 1)

def blkPoly (N n : ℕ) (v : Fin N × Fin N) : MvPolynomial (Fin n × Fin n) ℂ :=
  if hi : v.1.1 < n then (if hj : v.2.1 < n then MvPolynomial.X (⟨v.1.1, hi⟩, ⟨v.2.1, hj⟩) else 0)
    else (if v.2.1 < n then 0 else 1)

theorem eval_blkPoly (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (v : Fin N × Fin N) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v) = blkMat N n h v.1 v.2 := by
  simp only [blkPoly, blkMat, Matrix.of_apply]
  split_ifs <;> simp_all

theorem isBlock_blkMat {N n : ℕ} (hN : N = n + 1) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (blkMat N n h) h 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;>
    simp [blkMat, Formalism.L2.Col.Br.iC, Formalism.L2.Col.Br.iL]

theorem eq_blkMat_of_isBlock {N n : ℕ} (hN : N = n + 1) {kt : Matrix (Fin N) (Fin N) ℂ}
    {k : Matrix (Fin n) (Fin n) ℂ} (H : GlobalTheory.BranchFormula.IsBlock hN kt k 1) : kt = blkMat N n k := by
  ext i j
  simp only [blkMat, Matrix.of_apply]
  by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
  · rw [dite_eq_left hi, dite_eq_left hj]
    have := H.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dite_eq_left hi, dite_eq_right hj]
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨i.1, hi⟩).1
    rw [ej]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dite_eq_right hi, if_pos hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨j.1, hj⟩).2
    rw [ei]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dite_eq_right hi, if_neg hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    rw [ei, ej]
    exact H.2.2

theorem pow_toNat_eq (x : ℂ) (hx : x ≠ 0) (c m : ℤ) (hc : 0 ≤ c + m) :
    x ^ (c + m).toNat = x ^ m * x ^ c := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hc, zpow_add₀ hx, mul_comm]

theorem det_eval_mvPolynomialX (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = h.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_ne_zero_of_unitary {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u.det ≠ 0 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact right_ne_zero_of_mul_eq_one h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

open Formalism.BasicNotions

theorem unitary_to_all {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (u : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg)
    (E : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hE : ∀ f : delSq ℂ N lam, E f.1 = (u f).1)
    (hu : ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 →
      ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 →
        k.det ^ lam.detShift • (u f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (u f).1)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.det ≠ 0) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ delSq ℂ N lam) :
    g.det ^ lam.detShift • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g) f) =
      g.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ g (E f) := by
  set a := lam.detShift
  set b := sg.detShift
  set m : ℤ := |a| + |b|
  have ha : 0 ≤ a + m := by
    have := neg_abs_le a; have := abs_nonneg b; omega
  have hb : 0 ≤ b + m := by
    have := neg_abs_le b; have := abs_nonneg a; omega
  have poly : ∀ g' : Matrix (Fin n) (Fin n) ℂ,
      g'.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g') f) =
        g'.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ g' (E f) := by
    intro g'
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef N N f (l ∘ₗ E)
    obtain ⟨P₂, hP₂⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n (E f) l
    let D := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
    let Q := D ^ (a + m).toNat * MvPolynomial.bind₁ (blkPoly N n) P₁ - D ^ (b + m).toNat * P₂
    have hQ : ∀ h : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => h x.1 x.2) Q =
        l (h.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n h) f) -
          h.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ h (E f)) := by
      intro h
      have hbind : MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (MvPolynomial.bind₁ (blkPoly N n) P₁) =
          MvPolynomial.eval (fun v => MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v)) P₁ :=
        MvPolynomial.eval₂Hom_bind₁ _ _ _ P₁
      simp only [Q, D, map_sub, map_mul, map_pow, det_eval_mvPolynomialX, map_smul, smul_eq_mul, hbind, eval_blkPoly]
      rw [← hP₁ (blkMat N n h), ← hP₂ h]
      rfl
    have Q0 : Q = 0 := by
      refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Q fun v hv => ?_
      rw [hQ]
      have hv0 := det_ne_zero_of_unitary hv
      have key := hu v hv (blkMat N n v) (isBlock_blkMat hN v) ⟨f, hf⟩
        ⟨Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n v) f, GlobalTheory.ValueSpaceCoordinates.rowAct_mem_delSq lam _ f hf⟩ rfl
      rw [← hE, ← hE] at key
      rw [pow_toNat_eq _ hv0 a m ha, pow_toNat_eq _ hv0 b m hb, mul_smul, mul_smul, ← smul_sub]
      simp only at key
      rw [key, sub_self, smul_zero, map_zero]
    have := hQ g'
    rw [Q0, map_zero] at this
    exact this.symm
  have h := poly g
  rw [pow_toNat_eq _ hg a m ha, pow_toNat_eq _ hg b m hb, mul_smul, mul_smul] at h
  exact smul_right_injective _ (zpow_ne_zero m hg) h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

theorem eq_smul_of_unitary_equivariant : ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Formalism.L2.Col.Br.Interlace hN lam sg → ∀ t t₀ : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg, (∀ s, s = t ∨ s = t₀ → ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 → ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 → k.det ^ lam.detShift • (s f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (s f).1) → t₀ ≠ 0 → ∃ c : ℂ, t = c • t₀ := by
  intro N n hN lam sg hI t t₀ H h0
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (delSq ℂ N lam)
  let π := (delSq ℂ N lam).linearProjOfIsCompl C hC
  let E : (delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg) → MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    fun u => (delSq ℂ n sg).subtype ∘ₗ u ∘ₗ π
  have hE : ∀ u (f : delSq ℂ N lam), E u f.1 = (u f).1 := fun u f => by
    show (u (π f.1)).1 = (u f).1
    exact congrArg (fun x => (u x).1) (Submodule.linearProjOfIsCompl_apply_left hC f)
  have hN' : Formalism.BasicNotions.nablaSq ℂ N lam = delSq ℂ N lam := Formalism.L2.Col.nablaSq_eq_delSq ℂ lam
  have hn' : Formalism.BasicNotions.nablaSq ℂ n sg = delSq ℂ n sg := Formalism.L2.Col.nablaSq_eq_delSq ℂ sg
  have key : ∀ s, s = E t ∨ s = E t₀ → (∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, s f ∈ Formalism.BasicNotions.nablaSq ℂ n sg) ∧
      ∀ (g : GL (Fin n) ℂ), ∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam,
        s (Formalism.BasicNotions.sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) f) = Formalism.BasicNotions.sqAct ℂ n sg g (s f) := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ : ∃ u, (u = t ∨ u = t₀) ∧ s = E u := by
      rcases hs with hs | hs
      · exact ⟨t, Or.inl rfl, hs⟩
      · exact ⟨t₀, Or.inr rfl, hs⟩
    refine ⟨fun f hf => ?_, fun g f hf => ?_⟩
    · rw [hN'] at hf
      rw [hn', hE u ⟨f, hf⟩]
      exact (u _).2
    · rw [hN'] at hf
      have hb := (GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).transpose
      have hdet : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ).det =
          (g : Matrix (Fin n) (Fin n) ℂ).det := by
        rw [(GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).det, mul_one]
      have hg0 : (g : Matrix (Fin n) (Fin n) ℂ).transpose.det ≠ 0 := by
        rw [Matrix.det_transpose]
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      have main := unitary_to_all hN lam sg u (E u) (hE u) (H u hu) _ hg0 f hf
      rw [← eq_blkMat_of_isBlock hN hb, Matrix.det_transpose] at main
      simp only [Formalism.BasicNotions.sqAct, Formalism.BasicNotions.detPow, map_smul, Units.val_zpow_eq_zpow_val,
        Matrix.GeneralLinearGroup.val_det_apply, hdet]
      exact main
  have hne : ∃ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, E t₀ f ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := hc f.1 (by rw [hN']; exact f.2)
    rw [hE] at this
    simpa using this
  obtain ⟨c, hc⟩ := GlobalTheory.Branching.equivariant_map_eq_smul n N hN.symm lam sg
    ((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.interlace_iff hN lam sg).1 hI) (E t) (E t₀) key hne
  refine ⟨c, LinearMap.ext fun f => Subtype.ext ?_⟩
  have := hc f.1 (by rw [hN']; exact f.2)
  rw [hE, hE] at this
  simpa using this

end GlobalTheory.BranchMultOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (c : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * c ∈ 𝒪[k] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[k]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : b ∣ ((Nat.card 𝓀[k] ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[k] ^ m, pow_pos Nat.card_pos m, ?_⟩
  have hb' : (algebraMap 𝒪[k] k b) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
  have : ((Nat.card 𝓀[k] ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) =
      algebraMap 𝒪[k] k (d * a) := by
    rw [← map_natCast (algebraMap 𝒪[k] k), hd, map_mul, map_mul]
    field_simp
  rw [this]
  exact (d * a).2

theorem exists_nat_mul_mem_fin {ι : Type} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  choose N hN h using fun i => exists_nat_mul_mem (c i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_mem {n n' m m' : Type} [Fintype n] [Fintype n'] {N : ℕ} (b : Matrix m n k) (b' : Matrix n' m' k)
    (hb : ∀ i a, (N : k) * b i a ∈ 𝒪[k]) (hb' : ∀ a j, (N : k) * b' a j ∈ 𝒪[k]) (x : Matrix n n' k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) (i : m) (j : m') : ((N * N : ℕ) : k) * (b * x * b') i j ∈ 𝒪[k] := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine sum_mem fun a _ => sum_mem fun c _ => ?_
  have : ((N * N : ℕ) : k) * (b i c * x c a * b' a j) = ((N : k) * b i c) * x c a * ((N : k) * b' a j) := by
    push_cast; ring
  rw [this]
  exact mul_mem (mul_mem (hb i c) (hx c a)) (hb' a j)

end GlobalTheory.FinPl.RdInt

theorem GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × n => β.b x.1 x.2) (fun x : n' × Fin S.rank => α.b' x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  refine ⟨K * (N₀ * N₀), Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀), fun t ht hrd => ?_⟩
  have hent := GlobalTheory.FinPl.RdInt.entry_mem β.b α.b' (fun i a => h₀ (Sum.inl (i, a))) (fun a j => h₀ (Sum.inr (a, j)))
    (rd α β t) hrd
  have htw := GlobalTheory.FinPl.HalfInd.wr_rd α β ht
  have hu : IsHalf p.e ((N₀ * N₀) • t) := (GlobalTheory.PlaceModel.isHalf_iff S T).2
    ((GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) _)
  have hui : ∀ i j, toEAf D (((N₀ * N₀) • t) i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have h1 : ((N₀ * N₀) • t) i j = p.sec (((N₀ * N₀ : ℕ) : k) * (β.b * rd α β t * α.b') i j) := by
      rw [← nsmul_eq_mul, map_nsmul, ← GlobalTheory.FinPl.HalfInd.wr_apply, htw]
      rfl
    rw [h1]
    exact GlobalTheory.PlaceCoord.toEAf_mem ((p.int_iff _).1 (hent i j))
  have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) hu) hui
  have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h1).1
  have hh : K • (N₀ * N₀) • t ∈ GlobalTheory.PlaceModel.half S T p.e :=
    (GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) _
  rw [(GlobalTheory.PlaceModel.mem_half S T).1 hh] at h2
  rwa [mul_nsmul']

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm

variable {D : D7}

theorem coe_colStdLat (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  have hfull (n : ℕ) : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.stdLat D.host.E n) := by
    letI := Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := n)
    constructor
    apply eq_top_iff.mpr
    intro x _
    rw [pi_eq_sum_univ' x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simpa using Formalism.L2.Col.single_mem_stdLat (E := D.host.E) i 1))
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (hfull S.rank) (hfull T.rank)
  refine ⟨K, hK, fun t ht hi => ?_⟩
  have := h t ht hi
  rwa [coe_colStdLat, coe_colStdLat] at this

theorem infPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (GlobalTheory.LatticeStable.liftFin D x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => exact GlobalTheory.LatVac.infPart_pair a m
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem finPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.LatticeStable.liftFin D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem toEAf_eq_comm (z : AE D) :
    toEAf D z = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D z) := rfl

theorem toEAf_liftFin (r : EAf D) :
    toEAf D (GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm r)) = r := by
  rw [toEAf_eq_comm, finPart_liftFin, AlgEquiv.apply_symm_apply]

theorem toEAf_approx_eq_zero (t L : AE D) (x : D.host.E) (M : ℕ) (r : EAf D)
    (ht : toEAf D t = eToEAf D x + (M : EAf D) * r) (hL : toEAf D L = -r) :
    toEAf D (incA D x - t - (M : AE D) * L) = 0 := by
  have hi : toEAf D (incA D x) = eToEAf D x := rfl
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, map_natCast, hi, ht, hL]
  ring

theorem approx_entry (t : AE D) (M : ℕ) (hM : 0 < M) : ∃ (x : D.host.E) (w : AE D), infPart D w = 0 ∧
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ finPart D (incA D x - t - (M : AE D) * w) = 0 := by
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨x, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E)
    (eToEAf D (M : D.host.E)⁻¹ * toEAf D t)
  let c := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  refine ⟨M * x, GlobalTheory.LatticeStable.liftFin D (c.symm (-r)), infPart_liftFin _, ?_, ?_⟩
  · rw [toEAf_liftFin]
    exact neg_mem hr
  · have ht : toEAf D t = eToEAf D (M * x) + (M : EAf D) * r := by
      have e2 := congrArg (eToEAf D (M : D.host.E) * ·) e
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at e2
      rw [e2, map_mul, map_natCast, mul_add]
      rfl
    have hz := toEAf_approx_eq_zero t _ (M * x) M r ht (toEAf_liftFin (-r))
    rw [toEAf_eq_comm] at hz
    exact c.injective (hz.trans (map_zero c).symm)

theorem exists_rat_half_approx : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ (N : ℕ), 0 < N → ∀ y : WO S T, ∃ (γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ γ₀.map (fun r => e * incA D r) = e • y + N • v := by
  intro D S T e P he N hN y
  obtain ⟨K, hK, hKm⟩ := exists_nsmul_mem_stdHom S T
  choose x w hw0 hwi hz using fun i j => approx_entry (y i j) (N * K) (Nat.mul_pos hN hK)
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hKw : K • (Matrix.of fun i j => w i j) ∈ stdHom S T := hKm _ (Matrix.ext fun i j => hw0 i j) hwi
  refine ⟨Matrix.of x, e • (K • Matrix.of fun i j => w i j), ?_, ?_, ?_⟩
  · exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hKw
  · intro i j
    change e * (e * _) = e * _
    rw [← mul_assoc, hee]
  · ext i j
    have h0 : e * (incA D (x i j) - y i j - ((N * K : ℕ) : AE D) * w i j) = 0 := by
      refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
      · rw [map_mul, hinf, zero_mul]
      · rw [map_mul, hz i j, mul_zero]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast at h0
    linear_combination h0

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatSubTwoNsmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatApprox

theorem two_nsmul_cancel {D : D7} (a b : AE D) (h : (2 : ℕ) • a = (2 : ℕ) • b) : a = b := by
  have key : ∀ c : AE D, c = algebraMap D.host.F (AE D) (2 : D.host.F)⁻¹ * ((2 : ℕ) • c) := by
    intro c
    rw [nsmul_eq_mul, ← mul_assoc, Nat.cast_ofNat, show (2 : AE D) = algebraMap D.host.F (AE D) 2 from (map_ofNat _ 2).symm,
      ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  rw [key a, key b, h]

theorem map_eq_zero_apply {D : D7} {S T : HSp D} {R : Type} [Semiring R] (f : AE D →+* R) {x : WO S T}
    (hx : x.map f = 0) (i : Fin T.rank) (j : Fin S.rank) : f (x i j) = 0 := by
  have := congrFun (congrFun hx i) j
  rwa [Matrix.map_apply, Matrix.zero_apply] at this

theorem eq_two_nsmul {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x l : WO S T} (hx : x.map (infPart D) = 0) (hl : l ∈ latO S T LS LT fun _ => True)
    (hf : (x - (2 : ℕ) • l).map (finPart D) = 0) : x = (2 : ℕ) • l := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ (map_eq_zero_apply _ hf i j)
  rw [Matrix.sub_apply, Matrix.smul_apply, map_sub, map_nsmul, map_eq_zero_apply _ hx i j,
    GlobalTheory.LatVac.infPart_of_mem hl i j, nsmul_zero, sub_zero]

theorem exists_rat_sub_two_nsmul : ∀ (D : D7) (S T : HSp D) (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ γ, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ u - GlobalTheory.LatVac.finTens 1 γ = 2 • l := by
  intro D S T ΛS ΛS' ΛT ΛT' hS hS' hT hT' u hu
  let H : AddSubgroup (WO S T) :=
    ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓
      (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True)).map
      (nsmulAddMonoidHom 2)
  have hH : ∃ U : Set (WO S T), IsOpen U ∧ ∀ x : WO S T, x.map (infPart D) = 0 → (x ∈ H ↔ x ∈ U) := by
    refine ⟨_, (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos).inter
      (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS' ΛT' hS' hT' 2 two_pos), fun x hx => ⟨?_, ?_⟩⟩
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l, hl.1, ?_⟩, ⟨l, hl.2, ?_⟩⟩ <;>
        rw [nsmulAddMonoidHom_apply, sub_self, Matrix.map_zero _ (map_zero _)]
    · rintro ⟨⟨l, hl, hf⟩, ⟨l', hl', hf'⟩⟩
      have e1 := eq_two_nsmul hx hl hf
      have e2 := eq_two_nsmul hx hl' hf'
      have hll : l = l' := by
        ext i j
        exact two_nsmul_cancel _ _ (by rw [← Matrix.smul_apply, ← Matrix.smul_apply, ← e1, ← e2])
      subst hll
      exact ⟨l, ⟨hl, hl'⟩, by rw [nsmulAddMonoidHom_apply, ← e1]⟩
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.AdTh.SplitClass.exists_rat_sub_mem (LS := (ΛS' : Set (Fin S.rank → D.host.E)))
    (LT := (ΛT' : Set (Fin T.rank → D.host.E))) hH hu
  obtain ⟨l, hl, hle⟩ := hγ
  exact ⟨γ, l, hl.1, hl.2, by rw [← hle, nsmulAddMonoidHom_apply]⟩

end GlobalTheory.LatApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D) (κ : GA D S), IsSelfDualC S L → InK S L (· = v) κ → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.InStabAt S L v κ := by
  first | exact @GlobalTheory.KStabBridge.inStabAt_of_inK | exact GlobalTheory.KStabBridge.inStabAt_of_inK | (intros; apply GlobalTheory.KStabBridge.inStabAt_of_inK <;> assumption)
end

