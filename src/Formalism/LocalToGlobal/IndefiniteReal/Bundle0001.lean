module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
section
noncomputable section

open Matrix

namespace Formalism.IndefR.DeterminantProjection

section Ring

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_of_proj (σ : A →+* A) (J R : Matrix n n A) (hRR : R * R = R)
    (hJR : J * R = (R.map σ)ᵀ * J) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • R).map σ)ᵀ * J * (1 + (x - 1) • R) = J := by
  have hm : ((1 + (x - 1) • R).map σ)ᵀ = 1 + (σ x - 1) • (R.map σ)ᵀ := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have h1 : (R.map σ)ᵀ * J = J * R := hJR.symm
  have h2 : (R.map σ)ᵀ * J * R = J * R := by rw [h1, Matrix.mul_assoc, hRR]
  have e : (1 + (σ x - 1) • (R.map σ)ᵀ) * J * (1 + (x - 1) • R)
      = J + (x - 1) • (J * R) + (σ x - 1) • ((R.map σ)ᵀ * J)
        + ((σ x - 1) * (x - 1)) • ((R.map σ)ᵀ * J * R) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hs : (x - 1) + ((σ x - 1) + (σ x - 1) * (x - 1)) = 0 := by linear_combination hx
  rw [hm, e, h2, h1, add_assoc, add_assoc, ← add_smul, ← add_smul, hs, zero_smul, add_zero]

theorem det_proj (u r : n → A) (hru : r ⬝ᵥ u = 1) (x : A) :
    (1 + (x - 1) • (replicateCol Unit u * replicateRow Unit r)).det = x := by
  rw [← Matrix.smul_mul, ← Matrix.replicateCol_smul, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, hru, smul_eq_mul, mul_one]
  ring

theorem proj_idem (u r : n → A) (hru : r ⬝ᵥ u = 1) :
    (replicateCol Unit u * replicateRow Unit r) * (replicateCol Unit u * replicateRow Unit r) =
      replicateCol Unit u * replicateRow Unit r := by
  ext i j
  simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
    Finset.sum_singleton]
  rw [show (∑ k, u i * r k * (u k * r j)) = u i * (∑ k, r k * u k) * r j by
    rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
  rw [show (∑ k, r k * u k) = r ⬝ᵥ u from rfl, hru, mul_one]

end Ring

section Herm

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

def rowJ (σ : A →+* A) (J : Matrix n n A) (u : n → A) : n → A := (fun i => σ (u i)) ᵥ* J

def hsq (σ : A →+* A) (J : Matrix n n A) (u : n → A) : A := rowJ σ J u ⬝ᵥ u

def proj (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) : Matrix n n A :=
  replicateCol Unit u * replicateRow Unit (ainv • rowJ σ J u)

theorem sigma_rowJ (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (i : n) : σ (rowJ σ J u i) = (J *ᵥ u) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowJ, vecMul, mulVec, dotProduct, map_sum, map_mul, hσ, hJ]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sigma_hsq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) : σ (hsq σ J u) = hsq σ J u := by
  have h1 : σ (hsq σ J u) = ∑ i, (J *ᵥ u) i * σ (u i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hsq, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
  rw [h1]
  show _ = rowJ σ J u ⬝ᵥ u
  rw [rowJ, ← dotProduct_mulVec]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem proj_idem' (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) :
    proj σ J u ainv * proj σ J u ainv = proj σ J u ainv :=
  proj_idem u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha)

theorem det_proj' (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (x : A) :
    (1 + (x - 1) • proj σ J u ainv).det = x :=
  det_proj u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha) x

theorem proj_herm (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (hainv : σ ainv = ainv) :
    J * proj σ J u ainv = ((proj σ J u ainv).map σ)ᵀ * J := by
  ext i j
  have lhs : (J * proj σ J u ainv) i j = (J *ᵥ u) i * (ainv * rowJ σ J u j) := by
    simp only [proj, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul,
      Finset.univ_unique, Finset.sum_singleton, mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hrow : rowJ σ J u j = ∑ k, σ (u k) * J k j := rfl
  have rhs : (((proj σ J u ainv).map σ)ᵀ * J) i j = σ (ainv * rowJ σ J u i) * rowJ σ J u j := by
    rw [hrow, Finset.mul_sum]
    simp only [proj, Matrix.mul_apply, transpose_apply, map_apply, replicateCol_apply, replicateRow_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [lhs, rhs, map_mul, hainv, sigma_rowJ σ hσ J hJ]
  ring

theorem proj_unitary (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (hainv : σ ainv = ainv) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • proj σ J u ainv).map σ)ᵀ * J * (1 + (x - 1) • proj σ J u ainv) = J :=
  unitary_of_proj σ J _ (proj_idem' σ J u ainv ha) (proj_herm σ hσ J hJ u ainv hainv) x hx

theorem rowJ_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (j : n) :
    f (rowJ σ J u j) = rowJ σ' (J.map f) (fun i => f (u i)) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowJ, vecMul, dotProduct, map_sum, map_mul, hf, Matrix.map_apply]

theorem proj_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (ainv : A) :
    (proj σ J u ainv).map f = proj σ' (J.map f) (fun i => f (u i)) (f ainv) := by
  ext i j
  simp only [proj, Matrix.map_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply,
    smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul, rowJ_map f σ σ' hf]

theorem hsq_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) :
    f (hsq σ J u) = hsq σ' (J.map f) (fun i => f (u i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hsq, dotProduct, map_sum, map_mul, rowJ_map f σ σ' hf]

end Herm

section Field

variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_aniso (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n K) (hJ : ∀ i j, σ (J i j) = J j i)
    (hdet : J.det ≠ 0) [Nonempty n] : ∃ u : n → K, hsq σ J u ≠ 0 := by
  by_contra hcon
  push Not at hcon

  set B : (n → K) → (n → K) → K := fun u v => rowJ σ J u ⬝ᵥ v with hB
  have hadd : ∀ u v, hsq σ J (u + v) = hsq σ J u + hsq σ J v + B u v + B v u := by
    intro u v
    simp only [hsq, hB, rowJ, Pi.add_apply, map_add (f := _)]
    rw [show (fun i => σ (u i) + σ (v i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from rfl, add_vecMul,
      add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hsym : ∀ u v, B v u = σ (B u v) := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hB, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
    simp only [rowJ, vecMul, mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hlin : ∀ u v (t : K), B u (t • v) = t * B u v := by
    intro u v t; simp only [hB, dotProduct_smul, smul_eq_mul]
  have hzero : ∀ u v, B u v = 0 := by
    intro u v
    have h0 : ∀ t : K, t * B u v + σ (t * B u v) = 0 := by
      intro t
      have := hadd u (t • v)
      rw [hcon, hcon, hcon, hsym u (t • v), hlin] at this
      linear_combination -this
    by_contra hb
    have := h0 (B u v)⁻¹
    rw [inv_mul_cancel₀ hb, map_one] at this
    norm_num at this
  apply hdet
  have hJ0 : J = 0 := by
    ext i j
    have := hzero (Pi.single i 1) (Pi.single j 1)
    simp only [hB, rowJ] at this
    rw [show (fun k => σ ((Pi.single i (1 : K) : n → K) k)) = Pi.single i 1 by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]] at this
    simpa [single_one_vecMul] using this
  rw [hJ0, Matrix.det_zero]

end Field

end Formalism.IndefR.DeterminantProjection

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.EigenDecomposition
section
open scoped InnerProductSpace

namespace Formalism.IndefR.EigenDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem exists_onb_of_parts {I : Type*} [Finite I] (P : I → Submodule ℂ H)
    (horth : ∀ i j, i ≠ j → P i ⟂ P j) (htop : ⨆ i, P i = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → I), ∀ k, b k ∈ P (lab k) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hV : OrthogonalFamily ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) :=
    fun i j hij v w => (horth i j hij).inner_eq v.2 w.2
  have hint : DirectSum.IsInternal (fun i => P i) := by
    rw [hV.isInternal_iff, htop, Submodule.top_orthogonal_eq_bot]
  let b := hint.collectedOrthonormalBasis hV (fun i => stdOrthonormalBasis ℂ (P i))
  let e := Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (P i)))
  refine ⟨_, b.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  exact hint.collectedOrthonormalBasis_mem hV _ _

theorem exists_onb_of_parts_set {L : Type*} (S : Set L) (hS : S.Finite) (P : L → Submodule ℂ H)
    (horth : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → P c ⟂ P d) (htop : ⨆ c ∈ S, P c = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → L),
      (∀ k, lab k ∈ S) ∧ ∀ k, b k ∈ P (lab k) := by
  classical
  have hfin : Finite S := hS.to_subtype
  obtain ⟨n, b, lab, hb⟩ := exists_onb_of_parts (fun c : S => P c.1)
    (fun c d hcd => horth c.1 c.2 d.1 d.2 (fun h => hcd (Subtype.ext h)))
    (by rw [← htop, iSup_subtype'])
  exact ⟨n, b, fun k => (lab k).1, fun k => (lab k).2, hb⟩

noncomputable def reIm (T : H →ₗ[ℂ] H) (b : Bool) : H →ₗ[ℂ] H :=
  if b then T + LinearMap.adjoint T else Complex.I • (T - LinearMap.adjoint T)

theorem reIm_isSymmetric (T : H →ₗ[ℂ] H) (b : Bool) : (reIm T b).IsSymmetric := by
  intro x y
  cases b <;>
    simp [reIm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right] <;> ring

theorem exists_onb_of_commuting (A : Set (H →ₗ[ℂ] H))
    (hcomm : ∀ S ∈ A, ∀ T ∈ A, Commute S T)
    (hadj : ∀ T ∈ A, LinearMap.adjoint T ∈ A) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H), ∀ k, ∀ T ∈ A, ∃ μ : ℂ, T (b k) = μ • b k := by
  classical
  obtain ⟨B, hBA, hspan, hli⟩ := exists_linearIndependent ℂ A
  have hBfin : B.Finite := hli.setFinite
  have : Fintype B := hBfin.fintype
  have r1 : ∀ S : H →ₗ[ℂ] H, reIm S true = S + LinearMap.adjoint S := fun S => by simp [reIm]
  have r2 : ∀ S : H →ₗ[ℂ] H, reIm S false = Complex.I • (S - LinearMap.adjoint S) :=
    fun S => by simp [reIm]

  have cl : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute S X → Commute (LinearMap.adjoint S) X →
      Commute (reIm S β) X := by
    intro S X β h1 h2
    cases β
    · rw [r2]; exact (h1.sub_left h2).smul_left _
    · rw [r1]; exact h1.add_left h2
  have cr : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute X S → Commute X (LinearMap.adjoint S) →
      Commute X (reIm S β) := fun S X β h1 h2 => (cl S X β h1.symm h2.symm).symm
  have hc : ∀ S ∈ A, ∀ S' ∈ A, ∀ β β', Commute (reIm S β) (reIm S' β') := by
    intro S hS S' hS' β β'
    exact cl _ _ _ (cr _ _ _ (hcomm S hS S' hS') (hcomm S hS _ (hadj S' hS')))
      (cr _ _ _ (hcomm _ (hadj S hS) S' hS') (hcomm _ (hadj S hS) _ (hadj S' hS')))
  let F : B × Bool → Module.End ℂ H := fun p => reIm p.1.1 p.2
  have hsym : ∀ p, (F p).IsSymmetric := fun p => reIm_isSymmetric _ _
  have hpair : Pairwise (Function.onFun Commute F) := fun p q _ =>
    hc _ (hBA p.1.2) _ (hBA q.1.2) p.2 q.2
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hsym hpair
  have hV := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  let E : (B × Bool → ℂ) → Submodule ℂ H := fun α => ⨅ j, (F j).eigenspace (α j)
  have hfinS : ({α | E α ≠ ⊥} : Set (B × Bool → ℂ)).Finite := by
    have : Fintype {α // E α ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (Finite.of_fintype {α // E α ≠ ⊥})
  have hortho : ∀ c ∈ {α | E α ≠ ⊥}, ∀ d ∈ {α | E α ≠ ⊥}, c ≠ d → E c ⟂ E d :=
    fun c _ d _ hcd => hV.isOrtho hcd
  have htop' : ⨆ c ∈ {α | E α ≠ ⊥}, E c = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hint.submodule_iSup_eq_top]
    refine iSup_le fun α => ?_
    by_cases h : E α = ⊥
    · show E α ≤ _
      rw [h]; exact bot_le
    · exact le_biSup E (show α ∈ {α | E α ≠ ⊥} from h)
  obtain ⟨n, b, lab, -, hb⟩ := exists_onb_of_parts_set _ hfinS E hortho htop'
  refine ⟨n, b, fun k => ?_⟩
  have hv : ∀ p, F p (b k) = lab k p • b k := fun p =>
    Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 (hb k) p)

  have hB : ∀ S (hS : S ∈ B), ∃ μ : ℂ, S (b k) = μ • b k := by
    intro S hS
    have e1 : S (b k) + LinearMap.adjoint S (b k) = lab k (⟨S, hS⟩, true) • b k := by
      have := hv (⟨S, hS⟩, true)
      simpa [F, r1] using this
    have e2 : Complex.I • (S (b k) - LinearMap.adjoint S (b k)) = lab k (⟨S, hS⟩, false) • b k := by
      have := hv (⟨S, hS⟩, false)
      simpa [F, r2] using this
    have e2' : S (b k) - LinearMap.adjoint S (b k) = (-Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [mul_smul, ← e2, smul_smul]
      simp
    have e3 : (2 : ℂ) • S (b k) =
        (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [two_smul, add_smul, ← e1, ← e2']
      abel
    refine ⟨(1 / 2 : ℂ) * (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)), ?_⟩
    calc S (b k) = (1 / 2 : ℂ) • ((2 : ℂ) • S (b k)) := by rw [smul_smul]; norm_num
      _ = _ := by rw [e3, smul_smul]
  intro T hT
  have hT' : T ∈ Submodule.span ℂ B := hspan ▸ Submodule.subset_span hT
  clear hT
  induction hT' using Submodule.span_induction with
  | mem x hx => exact hB x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨μ₁, h₁⟩ := hx
    obtain ⟨μ₂, h₂⟩ := hy
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨μ, h⟩ := hx
    exact ⟨a * μ, by rw [LinearMap.smul_apply, h, smul_smul]⟩

end Formalism.IndefR.EigenDecomposition
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
section
noncomputable section

open NumberField IsDedekindDomain Module
open scoped InnerProductSpace Matrix

namespace Formalism.IndefR.Arith

section Data

variable (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable (WL : Type) [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
variable (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable (G0 : Type) [Group G0]

structure FormsL where

  WK : Submodule Ks WL

  Pt : HeightOneSpectrum (𝓞 Ks) → Type

  nrm : ∀ lp, Pt lp → WK → ℝ
  nrm_nonneg : ∀ lp y f, 0 ≤ nrm lp y f
  nrm_zero : ∀ lp y, nrm lp y 0 = 0
  nrm_add : ∀ lp y f g, nrm lp y (f + g) ≤ max (nrm lp y f) (nrm lp y g)
  nrm_smul : ∀ lp y (a : Ks) f, nrm lp y (a • f) = FinitePlace.mk lp a * nrm lp y f

  towKs : IsScalarTower Ks LL WL

  ρ : G0 →* (WL →ₗ[LL] WL)

  chi : G0 →* LLˣ

  j : ∀ σ : LL →+* ℂ, WL →ₛₗ[σ] W σ

end Data

section Defs

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)

namespace FormsL

def IsKsForm : Prop :=
  ∃ (n : ℕ) (b : Fin n → WL), (∀ i, b i ∈ A.WK) ∧ LinearIndependent Ks b ∧
    Submodule.span Ks (Set.range b) = A.WK ∧ LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = ⊤

def MK : Submodule (𝓞 Ks) WL where
  carrier := {f | ∃ h : f ∈ A.WK, ∀ lp (y : A.Pt lp), A.nrm lp y ⟨f, h⟩ ≤ 1}
  zero_mem' := ⟨A.WK.zero_mem, fun lp y => by
    rw [show (⟨0, A.WK.zero_mem⟩ : A.WK) = 0 from rfl, A.nrm_zero]; exact zero_le_one⟩
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨A.WK.add_mem hf hg, fun lp y => ?_⟩
    have := A.nrm_add lp y ⟨f, hf⟩ ⟨g, hg⟩
    exact this.trans (max_le (hf' lp y) (hg' lp y))
  smul_mem' := by
    rintro a f ⟨hf, hf'⟩
    have hs : a • f = ((a : Ks)) • f := (algebraMap_smul Ks a f).symm
    have hm : a • f ∈ A.WK := by rw [hs]; exact A.WK.smul_mem _ hf
    refine ⟨hm, fun lp y => ?_⟩
    have h1 : (⟨a • f, hm⟩ : A.WK) = (a : Ks) • ⟨f, hf⟩ := Subtype.ext hs
    rw [h1, A.nrm_smul]
    have h2 : FinitePlace.mk lp (a : Ks) ≤ 1 := by
      rw [FinitePlace.mk_apply]; exact FinitePlace.norm_le_one Ks (v := lp) a
    calc FinitePlace.mk lp (a : Ks) * A.nrm lp y ⟨f, hf⟩ ≤ 1 * 1 :=
          mul_le_mul h2 (hf' lp y) (A.nrm_nonneg lp y _) zero_le_one
      _ = 1 := one_mul 1

def typeP (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) : Submodule LL WL where
  carrier := {F | ∀ p : J0, A.ρ p F = ((A.chi p * lam0 p : LLˣ) : LL) • F}
  zero_mem' := fun p => by simp
  add_mem' := fun {F G} hF hG p => by
    show A.ρ p (F + G) = _
    rw [map_add (f := _), hF p, hG p, smul_add]
  smul_mem' := fun a F hF p => by
    show A.ρ p (a • F) = _
    rw [LinearMap.map_smul, hF p, smul_comm]

def eOp (eC : G0 → LL) : WL →ₗ[LL] WL := ∑ g, (eC g * ((A.chi g)⁻¹ : LLˣ)) • A.ρ g

def good (eC : G0 → LL) : Submodule LL WL := LinearMap.range (A.eOp eC)

def Wgood (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) : Submodule LL WL :=
  A.typeP J0 lam0 ⊓ A.good eC

def Mall (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) : Submodule (𝓞 LL) WL :=
  Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL)

def Mj (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) : Submodule (𝓞 LL) WL :=
  A.Mall J0 lam0 ⊓ (A.good eC).restrictScalars (𝓞 LL)

def nrmAt (σ : LL →+* ℂ) (x : WL) : ℝ := ‖A.j σ x‖


def Mcoord (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {d : ℕ} (b : Fin d → WL) :
    Submodule (𝓞 LL) (Fin d → LL) :=
  (A.Mj J0 lam0 eC).comap ((Fintype.linearCombination LL b).restrictScalars (𝓞 LL))

theorem mem_MK {f : WL} : f ∈ A.MK ↔ ∃ h : f ∈ A.WK, ∀ lp (y : A.Pt lp), A.nrm lp y ⟨f, h⟩ ≤ 1 := Iff.rfl

theorem MK_le_WK {f : WL} (hf : f ∈ A.MK) : f ∈ A.WK := hf.1

theorem mem_typeP (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) {F : WL} :
    F ∈ A.typeP J0 lam0 ↔ ∀ p : J0, A.ρ p F = ((A.chi p * lam0 p : LLˣ) : LL) • F := Iff.rfl

theorem eOp_apply (eC : G0 → LL) (x : WL) :
    A.eOp eC x = ∑ g, (eC g * ((A.chi g)⁻¹ : LLˣ)) • A.ρ g x := by
  simp [eOp, LinearMap.sum_apply]

theorem Mj_sub_Wgood (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {x : WL}
    (hx : x ∈ A.Mj J0 lam0 eC) : x ∈ A.Wgood J0 lam0 eC :=
  ⟨hx.1.2, hx.2⟩

theorem mem_Mcoord (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {d : ℕ} (b : Fin d → WL)
    (c : Fin d → LL) : c ∈ A.Mcoord J0 lam0 eC b ↔ ∑ i, c i • b i ∈ A.Mj J0 lam0 eC := by
  simp [Mcoord, Fintype.linearCombination_apply]

end FormsL

end Defs

section EEMetric

variable {LL : Type} [Field LL]
variable {QL : Type} [AddCommGroup QL] [Module LL QL]
variable {Ix J : Type} [Fintype Ix] [Fintype J]

end EEMetric

section Statements

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)

namespace FormsL

def ChiKs : Prop :=
  ∀ g, ((A.chi g : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)

def GalA : Prop :=
  ∀ (σ : LL →+* ℂ) (x : WL), A.nrmAt ((starRingEnd ℂ).comp σ) x = A.nrmAt σ x

def MKFull : Prop :=
  (A.MK : Submodule (𝓞 Ks) WL).FG ∧ Submodule.span Ks (A.MK : Set WL) = A.WK

def MKStable : Prop :=
  ∀ g f, (f ∈ A.WK → A.ρ g f ∈ A.WK) ∧ (f ∈ A.MK → A.ρ g f ∈ A.MK)

end FormsL

end Statements

end Formalism.IndefR.Arith
end
end

