module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0069
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.GPMem

theorem mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  have hlast : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
      (Fin.last (m + j)) = GlobalTheory.BZMir.eLast k (m + j) :=
    (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (m + j + 1)) k)).1 g.2
  have hproj : ∀ a b : Fin (m + j),
      ((GlobalTheory.BZMir.mirabolicProjection k (m + j) g : GL (Fin (m + j)) k) : Matrix (Fin (m + j)) (Fin (m + j)) k) a b =
        ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
  simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
    Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
  constructor
  · intro h b a
    convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
      simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      have h0 : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.last (m + j))
          (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : m + j = m + j) (Sum.inl a))) = 0 := by
        rw [hlast]
        simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
        rw [if_neg (Fin.castSucc_lt_last _).ne]
      convert h0 using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    | cast b =>
      convert h b a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]

end GlobalTheory.CompanionTheory.GPMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat (n : ℕ) :
    Continuous (fun v : Multiplicative (Fin n → k) => colMat k n v.toAdd) := by
  refine continuous_matrix fun i j => ?_
  simp only [colMat]
  split_ifs
  · induction i using Fin.lastCases with
    | last => simpa using continuous_const
    | cast i => simpa [Function.comp_def] using (continuous_apply i).comp (continuous_toAdd (X := Fin n → k))
  · exact continuous_const

theorem continuous_unipIn (n : ℕ) : Continuous (unipIn k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat n)
  · exact continuous_const.sub (continuous_colMat n)

theorem smooth_comp {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (hτ : IsSmooth τ) : IsSmooth (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) :=
  fun v => (hτ v).preimage (continuous_unipIn n)

theorem twKer_le_top (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) :
    twKer τ (MirUin k n) (thetaA k ψ a) ≤
      twKer (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) ⊤ (resChr ψ a ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, w₀, rfl⟩
  set x : Multiplicative (Fin n → k) :=
    (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) with hx
  have hu : unipIn k n x = (u : Mir k n) := by
    have h := (unipEquiv k n).apply_symm_apply ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)
    have h2 := congrArg (Subtype.val : MirU k n → GL (Fin (n + 1)) k) h
    apply Subtype.ext
    exact h2
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w₀, ?_⟩
  show τ (u : Mir k n) w₀ - _ = τ (unipIn k n x) w₀ - _
  rw [hu]
  rfl

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (t : kˣ) :
    IsOpen (ann ψ n t : Set (Multiplicative (Fin n → k))) := by
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  refine Subgroup.isOpen_mono (H₁ := polyBall n (t⁻¹ * c)) ?_ (isOpen_polyBall n _)
  intro x hx a ha
  refine hc _ ?_
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (a.toAdd i * x.toAdd i) ≤ valuation k (c : k)
  have h1 : (t : k) * ((t⁻¹ * c : kˣ) : k) = c := by simp
  rw [map_mul, ← h1, map_mul (valuation k) (t : k)]
  exact mul_le_mul' (ha i) (hx i)

end GlobalTheory.CompanionTheory.MirFourier


open GlobalTheory.CompanionTheory.MirFourier in
theorem GlobalTheory.CompanionTheory.MirFourier.fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Fourier k := by
  intro k _ _ _ _ ψ hψ h1 n V _ _ τ hτ v hv
  have hρ := smooth_comp τ hτ
  set ρ : Representation ℂ (Multiplicative (Fin n → k)) V := τ.comp (unipIn k n) with hρdef
  have hv1 : ∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) :=
    fun a => exists_mem_twKer_polyBall ψ ρ a v (twKer_le_top ψ τ a (hv a))
  have hS : {x | ρ x v = v} ∈ 𝓝 (1 : Multiplicative (Fin n → k)) :=
    (hρ v).mem_nhds (by simp)
  obtain ⟨t, ht⟩ := ann_subset_of_mem_nhds ψ h1 n hS
  obtain ⟨s, hs⟩ := exists_polyBall_twKer_uniform ψ hψ ρ v t hv1
  obtain ⟨R, hRne, hRt, hRsum⟩ := exists_reps_sum_eq_zero ψ hψ n t s
  refine GlobalTheory.CompanionTheory.FiniteFourier.eq_zero_of_twKer ρ hρ (polyBall n s) (isCompact_polyBall n s) ((ann ψ n t).subgroupOf _) ?_ v ?_ R hRne
    (fun a => resChr ψ a (polyBall n s)) ?_ (fun a ha => hs a (hRt a ha)) (fun x hx => hRsum x hx)
  · exact (isOpen_ann ψ hψ n t).preimage continuous_subtype_val
  · intro x hx
    exact ht hx
  · intro a ha x hx
    have h2 := hx (Multiplicative.ofAdd a) (hRt a ha)
    show Circle.toUnits (ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)) = 1
    have h3 : ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 := h2
    rw [h3, map_one]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [_root_.GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact _root_.GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (_root_.GlobalTheory.CompanionTheory.BZMirExhaust.exhaust k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolic
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ModCompactParab

theorem deltaHalf_leviProj_eq_one_of_isCompact :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ)
      (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) →
      ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K →
        deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  intro k _ _ _ _ a b n e K hK p hp
  let χ : parab k (two e) →* ℂˣ := (deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))
  have hχ : Continuous (leviProj k (two e)) := GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k) :=
    (GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal
  let H : Subgroup (parab k (two e)) := K.subgroupOf (parab k (two e))
  have hH : IsCompact (H : Set (parab k (two e))) := hemb.isCompact_preimage hK
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H) :=
    (isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)
  haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : (χ.ker.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)
  have hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1 := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa [χ, MonoidHom.mem_ker, map_pow] using h
  have hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hpow
    simp only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h
    exact_mod_cast h
  have hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1 :=
    (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal
  ext
  rw [val_deltaHalf, hone]
  simp

end GlobalTheory.CompanionTheory.ModCompactParab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
section
noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier
namespace GlobalTheory.CompanionTheory.MirLevi
variable {k : Type} [Field k]

def uv (n : ℕ) (v : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd v)


variable (k) in
def LH (n : ℕ) : Subgroup (Mir k n) := (levi k n).range


variable (k) in
def lv (n : ℕ) : GL (Fin n) k →* LH k n := (levi k n).rangeRestrict

def colv {n : ℕ} (g : Mir k n) : Fin n → k :=
  fun i => ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

def mvec {n : ℕ} (g : Mir k n) : Fin n → k :=
  (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec (colv g)

theorem mirProj_levi (n : ℕ) (m : GL (Fin n) k) : mirabolicProjection k n (levi k n m) = m := by
  apply Units.ext
  ext i j
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
  simp [GlobalTheory.BZMir.glEmbMat]

theorem mirProj_uv (n : ℕ) (v : Fin n → k) : mirabolicProjection k n (uv n v) = 1 := by
  apply Units.ext
  ext i j
  show (1 + GlobalTheory.BZMir.colMat k n v) (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem coe_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    (((levi k n m * uv n v : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (m : Matrix (Fin n) (Fin n) k) + colMat k n ((m : Matrix (Fin n) (Fin n) k).mulVec v) := by
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) * (1 + GlobalTheory.BZMir.colMat k n v) = _
  rw [mul_add, mul_one, GlobalTheory.BZMir.glEmbMat_mul_colMat]

theorem colv_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    colv (levi k n m * uv n v) = (m : Matrix (Fin n) (Fin n) k).mulVec v := by
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv]
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat]

theorem mvec_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    mvec (levi k n m * uv n v) = v := by
  unfold GlobalTheory.CompanionTheory.MirLevi.mvec
  rw [GlobalTheory.CompanionTheory.MirLevi.colv_levi_mul_uv, map_mul, GlobalTheory.CompanionTheory.MirLevi.mirProj_levi,
    GlobalTheory.CompanionTheory.MirLevi.mirProj_uv, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem decomp {n : ℕ} (g : Mir k n) : g = levi k n (mirabolicProjection k n g) * uv n (mvec g) := by
  have hA : ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      (GlobalTheory.CompanionTheory.MirLevi.mvec g) = GlobalTheory.CompanionTheory.MirLevi.colv g := by
    unfold GlobalTheory.CompanionTheory.MirLevi.mvec
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : ∀ i j, ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) :=
    fun _ _ => rfl
  have hlast := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv, hA]
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [congrFun hlast j]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast, Pi.single_apply,
        Fin.castSucc_ne_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.CompanionTheory.MirLevi.colv]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, hP, Fin.castSucc_ne_last]

theorem mvec_uv (n : ℕ) (v : Fin n → k) : mvec (uv n v) = v := by
  have h := GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv n (1 : GL (Fin n) k) v
  rwa [map_one, one_mul] at h

theorem mvec_levi_mul (n : ℕ) (m : GL (Fin n) k) (g : Mir k n) : mvec (levi k n m * g) = mvec g := by
  conv_lhs => rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, ← mul_assoc, ← map_mul]
  rw [GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv]

theorem uv_add (n : ℕ) (v w : Fin n → k) : uv n (v + w) = uv n v * uv n w := by
  simp only [GlobalTheory.CompanionTheory.MirLevi.uv, ofAdd_add, map_mul]

theorem uv_zero (n : ℕ) : uv n (0 : Fin n → k) = 1 := by
  simp [GlobalTheory.CompanionTheory.MirLevi.uv]

theorem uv_mul_levi (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    uv n v * levi k n m = levi k n m * uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) := by
  apply Subtype.ext
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n m
    (Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v))
  rw [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)

def restr : cIndSpace (LH k n) ρ →ₗ[ℂ] (Fin n → k) → E where
  toFun f v := f.1.1.1 (uv n v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_injective : Function.Injective (restr ρ) := by
  intro f f' h
  have key : ∀ (F : GlobalTheory.PRep.cIndSpace (GlobalTheory.CompanionTheory.MirLevi.LH k n) ρ)
      (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      F.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (F.1.1.1 g) := by
    intro F x g
    first
    | exact F.1.1.2 x g
    | exact F.1.2 x g
    | exact F.2 x g
    | simpa using F.1.1.2 x g
  have hv : ∀ v, f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) = f'.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) :=
    fun v => congrFun h v
  have hall : ∀ g, f.1.1.1 g = f'.1.1.1 g := by
    intro g
    have e : GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n g) =
        ((GlobalTheory.CompanionTheory.MirLevi.lv k n (GlobalTheory.BZMir.mirabolicProjection k n g) :
          GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
    rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, e, key f, key f', hv]
  first
  | exact Subtype.ext (Subtype.ext (Subtype.ext (funext hall)))
  | exact Subtype.ext (Subtype.ext (Subtype.ext (by ext g; exact hall g)))

theorem restr_uv (a : Fin n → k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (uv n a) f) v = restr ρ f (v + a) := by
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.CompanionTheory.MirLevi.uv n a) = _
  exact congrArg (fun g => f.1.1.1 g) (GlobalTheory.CompanionTheory.MirLevi.uv_add n v a).symm

theorem restr_levi (m : GL (Fin n) k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (levi k n m) f) v =
      ρ (lv k n m) (restr ρ f (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)) := by
  have key : ∀ (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      f.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (f.1.1.1 g) := by
    intro x g
    first
    | exact f.1.1.2 x g
    | exact f.1.2 x g
    | exact f.2 x g
    | simpa using f.1.1.2 x g
  have e : GlobalTheory.BZMir.levi k n m =
      ((GlobalTheory.CompanionTheory.MirLevi.lv k n m : GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.BZMir.levi k n m) = _
  rw [GlobalTheory.CompanionTheory.MirLevi.uv_mul_levi, e, key]
  rfl

end Rep

end GlobalTheory.CompanionTheory.MirLevi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
section
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open CompanionTheory.D.LK (Pos)

namespace GlobalTheory.CompanionTheory.PairMult.TopCycQ

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem mem_omQ (lev : Fin n → ℕ) (l : Lt n) :
    l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

theorem insert_ne_omQ (lev : Fin n → ℕ) (s t : Bool) (i j k : Pos n)
    (ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2) (C : Finset (Lt n)) :
    insert (s, i) (insert (t, j) (C.erase ((s == t), k))) ≠ omQ lev := by
  intro e
  have hi := (mem_omQ lev _).1 (e ▸ mem_insert_self _ _)
  have hj := (mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
  obtain ⟨t1, t2, t3⟩ := ht
  have hs : s = true := hi.1
  have htt : t = true := hj.1
  subst hs htt
  have ck : ((true == true), k) ∈ omQ lev := (mem_omQ lev _).2
    ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩
  rw [← e] at ck
  rcases mem_insert.1 ck with h | h
  · have hk : k = i := congrArg Prod.snd h
    subst hk
    have pj := j.2
    rw [← t1, t3] at pj
    exact lt_irrefl _ pj
  · rcases mem_insert.1 h with h | h
    · have hk : k = j := congrArg Prod.snd h
      subst hk
      have pi := i.2
      rw [← t2, t1] at pi
      exact lt_irrefl _ pi
    · exact notMem_erase _ _ h

theorem topCyc : TopCyc := by
  intro n lev V _ _ E1 E2 _ v hv
  funext A
  simp only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro s _
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    split_ifs with ht
    · rw [Module.End.mul_apply, Module.End.mul_apply, creq_app]
      split_ifs with hk
      · rw [annq_app]
        split_ifs with h1
        · exact smul_zero _
        · rw [annq_app]
          split_ifs with h2
          · simp
          · rw [topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]
      · rfl
    · rfl
  · intro l _
    show Tl E1 E2 l (annq l (topq lev v) A) = 0
    rw [annq_app]
    split_ifs with hl
    · exact map_zero _
    · by_cases e : insert l A = omQ lev
      · have hlK := (mem_omQ lev l).1 (e ▸ mem_insert_self l A)
        rw [topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]
      · rw [topq, Pi.single_eq_of_ne e, smul_zero, map_zero]

end GlobalTheory.CompanionTheory.PairMult.TopCycQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSmoothingStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ), Ker ν β → (∀ i, Continuous (f i)) →
  UBnd f m → UBnd (fun i => sm ν β (f i)) m := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uBnd_sm | exact GlobalTheory.CompanionTheory.Conc.uBnd_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uBnd_sm <;> assumption)
end

