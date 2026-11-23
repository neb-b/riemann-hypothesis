module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PMuFrames
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.KronDetScalar
section
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.Col

section Kron

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι → ℕ}

def kron (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : Matrix (∀ τ, Fin (r τ)) (∀ τ, Fin (r τ)) ℝ :=
  Matrix.of fun I I' => ∏ τ, A τ (I τ) (I' τ)

theorem kron_mul (A B : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : kron A * kron B = kron fun τ => A τ * B τ := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun I' _ => Finset.prod_mul_distrib.symm

theorem kron_one : kron (fun τ => (1 : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)) = 1 := by
  ext I I'
  simp only [kron, Matrix.of_apply]
  by_cases h : I = I'
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (Matrix.one_apply_ne hτ)

theorem kron_smul (c : ι → ℝ) (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : kron (fun τ => c τ • A τ) = (∏ τ, c τ) • kron A := by
  ext I I'
  simp only [kron, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib

def kronDet : (∀ τ, GL (Fin (r τ)) ℝ) →* ℝ where
  toFun g := (kron fun τ => ((g τ : GL (Fin (r τ)) ℝ) : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)).det
  map_one' := by
    have : (fun τ => (((1 : ∀ τ, GL (Fin (r τ)) ℝ) τ : GL (Fin (r τ)) ℝ) : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)) = fun τ => 1 := by
      funext τ; rfl
    rw [this, kron_one, Matrix.det_one]
  map_mul' g h := by
    rw [← Matrix.det_mul, kron_mul]
    rfl

theorem kronDet_scalar (τ : ι) (t : ℝˣ) :
    kronDet (r := r) (Pi.mulSingle τ (brpSc ℝ t)) = (t : ℝ) ^ ((Fintype.card (∀ τ, Fin (r τ)) : ℕ) : ℤ) := by
  show (kron fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) :
    Matrix (Fin (r σ)) (Fin (r σ)) ℝ)).det = _
  have h : (fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) :
      Matrix (Fin (r σ)) (Fin (r σ)) ℝ)) = fun σ => (if σ = τ then (t : ℝ) else 1) • (1 : Matrix (Fin (r σ)) (Fin (r σ)) ℝ) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ
      rw [Pi.mulSingle_eq_same, if_pos rfl, brpSc_coe]
    · rw [Pi.mulSingle_eq_of_ne hσ, if_neg hσ, one_smul]; rfl
  rw [h, kron_smul, kron_one, Finset.prod_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ), Matrix.det_smul, Matrix.det_one, mul_one,
    zpow_natCast]

theorem log_kron (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) (hA : ∀ τ, (A τ).det ≠ 0) (hr : ∀ τ, 0 < r τ) :
    Real.log (kron A).det / (Fintype.card (∀ τ, Fin (r τ)) : ℝ) = ∑ τ, Real.log (A τ).det / (r τ : ℝ) := by
  let g : ∀ τ, GL (Fin (r τ)) ℝ := fun τ => brpGL ℝ (A τ) (isUnit_iff_ne_zero.2 (hA τ))
  have h0 := Finset.map_noncommProd Finset.univ (fun i => Pi.mulSingle i (g i))
    (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j) (kronDet (r := r))
  rw [Finset.noncommProd_mulSingle g, Finset.noncommProd_eq_prod] at h0
  have h1 : kronDet g = (kron A).det := rfl
  rw [h1] at h0
  have h2 : ∀ τ, kronDet (r := r) (Pi.mulSingle τ (g τ)) ^ r τ = (A τ).det ^ ((Fintype.card (∀ τ, Fin (r τ)) : ℕ) : ℤ) := fun τ =>
    glChar_pow ℝ ((kronDet (r := r)).comp (MonoidHom.mulSingle (fun τ => GL (Fin (r τ)) ℝ) τ)) _ (kronDet_scalar τ) (g τ)
  have hne : ∀ τ, kronDet (r := r) (Pi.mulSingle τ (g τ)) ≠ 0 := by
    intro τ h
    have := h2 τ
    rw [h, zero_pow (hr τ).ne'] at this
    exact (zpow_ne_zero _ (hA τ)) this.symm
  have hD : (0 : ℝ) < (Fintype.card (∀ τ, Fin (r τ)) : ℝ) := by
    have : Nonempty (∀ τ, Fin (r τ)) := ⟨fun τ => ⟨0, hr τ⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [h0, Real.log_prod (fun τ _ => hne τ), Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h3 := congrArg Real.log (h2 τ)
  rw [Real.log_pow, Real.log_zpow] at h3
  have hrτ : (0 : ℝ) < (r τ : ℝ) := by exact_mod_cast hr τ
  push_cast at h3
  field_simp
  linarith

end Kron

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PTenFrames
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

def sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) : Basis (J0 × Cl) K V :=
  ((Pi.basis fun _ : Cl => BK).map coE.symm).reindex ((Equiv.sigmaEquivProd Cl J0).trans (Equiv.prodComm Cl J0))

theorem sumBasis_apply (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (i : J0) (c : Cl) :
    sumBasis coE BK (i, c) = coE.symm (Pi.single c (BK i)) := by
  simp [sumBasis, Basis.reindex_apply, Basis.map_apply, Pi.basis_apply, Equiv.prodComm, Equiv.sigmaEquivProd]

theorem famOf_sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (φ : Cl → Module.End K W) :
    famOf (sumBasis coE BK) (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ c)) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ j.2 (BK j.1))) := by
  funext j
  obtain ⟨i, c⟩ := j
  have hφ : φ c (BK i) = ∑ i', LinearMap.toMatrix BK BK (φ c) i' i • BK i' := by
    simp [LinearMap.toMatrix_apply, BK.sum_repr]
  have hs : ∀ (f : J0 → W), Pi.single (M := fun _ : Cl => W) c (∑ i', f i') = ∑ i', Pi.single c (f i') := by
    intro f
    exact (map_sum (LinearMap.single K (fun _ : Cl => W) c) f Finset.univ)
  simp only [famOf, sumBasis_apply]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.blockDiagonal_apply, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, hs, map_sum]
  simp only [Pi.single_smul, map_smul, sumBasis_apply]

end Gen

section Sum

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
  {ι : Type} [Fintype ι] {W : Type} [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem conj_mul_real_mul (z : ℂ) (r : ℝ) : starRingEnd ℂ z * (r : ℂ) * z = ((Complex.normSq z * r : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

def ownFrame (Q : HLat K) {n : ℕ} (eQ : Q.ι ≃ Fin n) (g : FinPl K → Matrix (Fin n) (Fin n) K) (hg : ∀ p, (g p).det ≠ 0)
    (hloc : ∀ p, localization₂ (toH p).asIdeal Q.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i))) : FrameData Q Q.ι where
  e := Q.b
  Γ := fun p => (g p).submatrix eQ eQ
  det_ne := fun p => by rw [Matrix.det_submatrix_equiv_self]; exact hg p
  loc := fun p => by
    rw [hloc p]
    congr 1
    unfold latOf
    congr 1
    have h : famOf Q.b ((g p).submatrix eQ eQ) = (fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i)) ∘ eQ := by
      funext i'
      unfold famOf
      simp only [Function.comp_apply, Matrix.submatrix_apply]
      exact Fintype.sum_equiv eQ _ _ fun k => by simp
    rw [h, EquivLike.range_comp]

private theorem det_gramJ_self_basis_eq_normSq_det_inv (Q : HLat K) (v : InfinitePlace K) :
    (gramJ Q (⇑Q.b) v).det = ((Complex.normSq ((Q.X v)⁻¹).det : ℝ) : ℂ) := by
  have h : gramJ Q (⇑Q.b) v = ((Q.X v)⁻¹)ᴴ * (Q.X v)⁻¹ := by
    ext a c
    simp [gramJ, majAt, fcoord, vecAt, Matrix.mul_apply, Basis.repr_self, Finsupp.single_apply, Matrix.mulVec, dotProduct]
  rw [h, Matrix.det_mul, Matrix.det_conjTranspose]
  have := conj_mul_real_mul ((Q.X v)⁻¹).det 1
  simpa [Complex.star_def] using this

theorem mu_sum_functor [Nonempty J0] [Nonempty Cl] (A : HLat K) (hA : A.Good) (coE : A.V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W)
    (Q : Cl → ι → HLat K) (hQ : ∀ c τ, (Q c τ).Good) (n : ℕ) (hn : 0 < n) (eQ : ∀ c τ, (Q c τ).ι ≃ Fin n) (a : ι → ℤ)
    (g : FinPl K → Cl → ι → Matrix (Fin n) (Fin n) K) (hg : ∀ p c τ, (g p c τ).det ≠ 0)
    (hQloc : ∀ p c τ, localization₂ (toH p).asIdeal (Q c τ).L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p c τ i a' • (Q c τ).b ((eQ c τ).symm i)))
    (φ : FinPl K → Cl → Module.End K W)
    (hφ : ∀ p c, LinearMap.det (φ p c) ^ n = ∏ τ, (g p c τ).det ^ a τ)
    (hAloc : ∀ p, localization₂ (toH p).asIdeal A.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ p j.2 (BK j.1)))))
    (G0 : Matrix J0 J0 ℝ) (N : InfinitePlace K → Cl → Matrix J0 J0 ℂ)
    (hN : ∀ v c, (N v c).det ^ n = ∏ τ, (((Q c τ).X v)⁻¹).det ^ a τ)
    (hGram : ∀ v (i i' : J0) (c c' : Cl),
      majAt A.b A.X v (coE.symm (Pi.single c (BK i))) (coE.symm (Pi.single c' (BK i'))) =
        if c = c' then ((N v c)ᴴ * G0.map Complex.ofReal * N v c) i i' else 0) :
    ((Fintype.card J0 : ℝ) * Fintype.card Cl) * A.mu =
      -((Fintype.card Cl : ℝ) * Real.log G0.det) + ∑ c, ∑ τ, (a τ : ℝ) * (Q c τ).mu := by
  have hne : ∀ p c, LinearMap.det (φ p c) ≠ 0 := by
    intro p c h
    have h1 := hφ p c
    rw [h, zero_pow hn.ne'] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hg p c τ)) h1.symm
  let FA : FrameData A (J0 × Cl) :=
    { e := sumBasis coE BK
      Γ := fun p => Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)
      det_ne := fun p => by
        rw [Matrix.det_blockDiagonal]
        exact Finset.prod_ne_zero_iff.mpr fun c _ => by rw [LinearMap.det_toMatrix]; exact hne p c
      loc := fun p => by rw [hAloc p, famOf_sumBasis] }
  let FQ : (s : Cl × ι) → FrameData (Q s.1 s.2) (Q s.1 s.2).ι := fun s =>
    ownFrame (Q s.1 s.2) (eQ s.1 s.2) (fun p => g p s.1 s.2) (fun p => hg p s.1 s.2) (fun p => hQloc p s.1 s.2)
  have hdet : ∀ v c, ((N v c)ᴴ * G0.map Complex.ofReal * N v c).det =
      ((Complex.normSq (N v c).det * G0.det : ℝ) : ℂ) := by
    intro v c
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← conj_mul_real_mul]
    have hm : (G0.map Complex.ofReal).det = (G0.det : ℂ) := by
      rw [show G0.map Complex.ofReal = Complex.ofRealHom.mapMatrix G0 from rfl, ← RingHom.map_det]
      rfl
    rw [hm, Complex.star_def]
  have hgramA : ∀ v, (gramJ A (⇑FA.e) v).det.re =
      (∏ c, Complex.normSq (N v c).det) * G0.det ^ Fintype.card Cl := by
    intro v
    have h1 : gramJ A (⇑FA.e) v = Matrix.blockDiagonal fun c => (N v c)ᴴ * G0.map Complex.ofReal * N v c := by
      ext ⟨i, c⟩ ⟨i', c'⟩
      simp only [gramJ, Matrix.of_apply, Matrix.blockDiagonal_apply]
      show majAt A.b A.X v (sumBasis coE BK (i, c)) (sumBasis coE BK (i', c')) = _
      rw [sumBasis_apply, sumBasis_apply, hGram]
    rw [h1, Matrix.det_blockDiagonal]
    simp_rw [hdet]
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hgramQ : ∀ (s : Cl × ι) v, (gramJ (Q s.1 s.2) (⇑(FQ s).e) v).det.re =
      Complex.normSq ((Q s.1 s.2).X v)⁻¹.det := by
    intro s v
    rw [show (FQ s).e = (Q s.1 s.2).b from rfl, det_gramJ_self_basis_eq_normSq_det_inv, Complex.ofReal_re]
  have hpos : 0 < G0.det ^ Fintype.card Cl := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have h := (mu_of_frames A hA FA).1 v
    rw [hgramA] at h
    have h0 : 0 ≤ ∏ c, Complex.normSq (N v c).det := Finset.prod_nonneg fun c _ => Complex.normSq_nonneg _
    rcases lt_or_ge 0 (G0.det ^ Fintype.card Cl) with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h0 h2))
  have key := mu_functor A hA FA (fun s : Cl × ι => Q s.1 s.2) (fun s => hQ s.1 s.2) n hn
    (fun s => (Fintype.card_congr (eQ s.1 s.2)).trans (Fintype.card_fin n)) FQ (fun s => a s.2)
    (G0.det ^ Fintype.card Cl) hpos ?_ ?_
  · rw [Fintype.card_prod, Real.log_pow, Fintype.sum_prod_type] at key
    push_cast at key
    linarith [key]
  · intro p
    show (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)).det ^ n =
      ∏ s : Cl × ι, ((g p s.1 s.2).submatrix (eQ s.1 s.2) (eQ s.1 s.2)).det ^ a s.2
    rw [Matrix.det_blockDiagonal, ← Finset.prod_pow, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [LinearMap.det_toMatrix, hφ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_submatrix_equiv_self]
  · intro v
    rw [hgramA]
    simp_rw [hgramQ]
    rw [Fintype.prod_prod_type, mul_pow, mul_comm, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← map_pow, hN, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀]

end Sum

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

