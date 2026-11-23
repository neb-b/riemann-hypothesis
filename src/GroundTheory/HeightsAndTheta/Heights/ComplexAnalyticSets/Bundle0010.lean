module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CutOffNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Set Topology MvPolynomial ComplexSets
open scoped ContDiff Manifold

theorem exists_cutoff_near {n : ℕ} {S U : Set (Fin n → ℂ)} (hS : IsClosed S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V, hV, hSV, hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨f, hf1, hf0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Fin n → ℂ) (n := ⊤) hS (t := closure V) (hSV.trans (interior_maximal subset_closure hV))
  refine ⟨f, f.contMDiff.contDiff, hf, ?_, ?_⟩
  · refine (closure_minimal (fun x hx => ?_) isClosed_closure).trans hVU
    by_contra h
    exact hx (hf0 x h)
  · obtain ⟨W, hW, hSW, hWf⟩ := mem_nhdsSet_iff_exists.1 hf1
    exact ⟨W, hW, hSW, fun x hx => hWf hx⟩

theorem exists_cutoff_near_zeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hIU : zeroSet I ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ zeroSet I ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  refine exists_cutoff_near ?_ hU hIU
  have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Pointwise

variable {n d : ℕ}

def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j

def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)

def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite

def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))

def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]

def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap

theorem lineMap_surjective : Function.Surjective lineMap := by
  intro p
  refine ⟨rename (fun _ : Fin 1 => (0 : Fin 2)) p, ?_⟩
  have h : ((![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) ℂ) ∘ fun _ : Fin 1 => (0 : Fin 2)) = X := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [lineMap, aeval_rename, h, aeval_X_left_apply]

def lineEquiv : (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective lineMap_surjective

theorem lineIdeal_dim : ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv lineEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

def lineProj : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.proj 0

theorem lineEquiv_projAlgHom (p : MvPolynomial (Fin 1) ℂ) :
    lineEquiv (projAlgHom lineIdeal lineProj p) = p := by
  have h : (lineEquiv.toAlgHom.comp (projAlgHom lineIdeal lineProj)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i]
    simp [projAlgHom, lineEquiv, linPoly, lineProj, lineMap, Fin.sum_univ_two]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk lineMap_surjective (X 0)).trans
      (by simp [lineMap])
  exact congrArg (fun f => f p) h

theorem lineProj_finite : IsFiniteProjection lineIdeal lineProj := by
  have hinj : Function.Injective (projAlgHom lineIdeal lineProj) :=
    Function.LeftInverse.injective lineEquiv_projAlgHom
  have hsurj : Function.Surjective (projAlgHom lineIdeal lineProj) := by
    intro q
    refine ⟨lineEquiv q, lineEquiv.injective ?_⟩
    rw [lineEquiv_projAlgHom]
  exact ⟨hinj, RingHom.Finite.of_surjective _ hsurj⟩

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval (0 : Fin n → ℂ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsLocalParametrisation {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ) : Prop :=
  IsOpen B ∧ w ∈ X ∩ B ∧ IsOpen D ∧ IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
    (∀ x ∈ X ∩ B, A x = A w → x = w) ∧
    AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
    (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
    (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
    X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem NormalModel.exists_clear_denominators {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hb : ∀ i, eval x (b i) ≠ 0) (q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (r : MvPolynomial (Fin n) ℂ),
      rename Sum.inl ((∏ i, b i) ^ N) * q - rename Sum.inl r ∈ M.ideal ∧
        eval x r = eval x (∏ i, b i) ^ N *
          eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q := by
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  set w : Fin n ⊕ Fin M.m → ℂ := Sum.elim x fun i => eval x (a i) / eval x (b i) with hw
  induction q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C c, ?_, ?_⟩
    · simp
    · simp
  | add p q hp hq =>
    obtain ⟨N₁, r₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, r₂, h₂, e₂⟩ := hq
    refine ⟨N₁ + N₂, B ^ N₂ * r₁ + B ^ N₁ * r₂, ?_, ?_⟩
    · have hid : rename Sum.inl (B ^ (N₁ + N₂)) * (p + q) - rename Sum.inl (B ^ N₂ * r₁ + B ^ N₁ * r₂) =
          rename Sum.inl (B ^ N₂) * (rename Sum.inl (B ^ N₁) * p - rename Sum.inl r₁) +
            rename Sum.inl (B ^ N₁) * (rename Sum.inl (B ^ N₂) * q - rename Sum.inl r₂) := by
        simp only [map_mul, map_add (f := _), map_pow]
        ring
      rw [hid]
      exact M.ideal.add_mem (M.ideal.mul_mem_left _ h₁) (M.ideal.mul_mem_left _ h₂)
    · rw [eval_add, eval_add, eval_mul, eval_mul, e₁, e₂, eval_pow, eval_pow]
      ring
  | mul_X p s hp =>
    obtain ⟨N, r, h, e⟩ := hp
    rcases s with j | i
    · refine ⟨N, r * X j, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ N) * (p * X (Sum.inl j)) - rename Sum.inl (r * X j) =
            X (Sum.inl j) * (rename Sum.inl (B ^ N) * p - rename Sum.inl r) := by
          simp only [map_mul, rename_X]
          ring
        rw [hid]
        exact M.ideal.mul_mem_left _ h
      · rw [eval_mul, eval_mul, e, eval_X, eval_X]
        simp only [hw, Sum.elim_inl]
        ring
    · set Cᵢ : MvPolynomial (Fin n) ℂ := ∏ j ∈ Finset.univ.erase i, b j with hC
      have hBC : B = b i * Cᵢ := (Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)).symm
      refine ⟨N + 1, r * a i * Cᵢ, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ (N + 1)) * (p * X (Sum.inr i)) - rename Sum.inl (r * a i * Cᵢ) =
            rename Sum.inl Cᵢ * (rename Sum.inl (b i) * X (Sum.inr i)) *
                (rename Sum.inl (B ^ N) * p - rename Sum.inl r) +
              rename Sum.inl Cᵢ * rename Sum.inl r *
                (rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i)) := by
          rw [pow_succ, hBC]
          simp only [map_mul, map_pow]
          ring
        rw [hid]
        exact M.ideal.add_mem (M.ideal.mul_mem_left _ h) (M.ideal.mul_mem_left _ (hab i))
      · rw [eval_mul, eval_mul, eval_mul, eval_X, pow_succ, hBC]
        have e' : eval x r = eval x (b i * Cᵢ) ^ N * eval w p := by rw [← hBC]; exact e
        rw [e']
        simp only [hw, Sum.elim_inr, eval_mul]
        field_simp [hb i]

theorem NormalModel.graph_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hx : x ∈ zeroSetIn J) (hb : ∀ i, eval x (b i) ≠ 0) :
    (Sum.elim x fun i => eval x (a i) / eval x (b i)) ∈ zeroSetIn M.ideal := by
  intro q hq
  obtain ⟨N, r, h, e⟩ := M.exists_clear_denominators a b hab x hb q
  have hr : rename Sum.inl r ∈ M.ideal := by
    have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl ((∏ i, b i) ^ N)) hq) h
    simpa using this
  have hrJ : r ∈ J := by
    rw [← M.comap_eq]
    exact hr
  have hBx : eval x (∏ i, b i) ^ N ≠ 0 := by
    rw [map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hb i)
  have h0 : eval x (∏ i, b i) ^ N * eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q = 0 := by
    rw [← e]
    exact hx r hrJ
  exact (mul_eq_zero.1 h0).resolve_left hBx

theorem NormalModel.eq_graph_of_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (w : Fin n ⊕ Fin M.m → ℂ) (hw : w ∈ zeroSetIn M.ideal) (hb : ∀ i, eval (firstCoords w) (b i) ≠ 0) :
    w = Sum.elim (firstCoords w) fun i => eval (firstCoords w) (a i) / eval (firstCoords w) (b i) := by
  funext s
  rcases s with j | i
  · rfl
  · have h := hw _ (hab i)
    simp only [map_sub, map_mul, eval_rename, eval_X] at h
    simp only [Sum.elim_inr]
    rw [eq_div_iff (hb i)]
    have hc : (w ∘ Sum.inl) = firstCoords w := rfl
    rw [hc] at h
    linear_combination h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticImplicitChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology
open scoped ContDiff

noncomputable section

namespace AnalyticImplicitChart

theorem pi_surjective_of_linearIndependent {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] {φ : ι → E →L[ℂ] ℂ} (hφ : LinearIndependent ℂ φ) :
    Function.Surjective (LinearMap.pi fun j => (φ j : E →ₗ[ℂ] ℂ)) := by
  classical
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hfx : ∀ x : ι → ℂ, f x = ∑ j, x j * f (Pi.single j 1) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have h0 : ∑ j, f (Pi.single j 1) • φ j = 0 := by
    ext z
    have := LinearMap.congr_fun hf z
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
    rw [hfx] at this
    simpa [mul_comm] using this
  have hc := Fintype.linearIndependent_iff.1 hφ _ h0
  refine LinearMap.ext fun x => ?_
  rw [hfx x]
  simp [hc]

theorem proof : AnalyticImplicitChart.Statement := by
  intro σ ι _ _ h a W hh h0 hli hW
  classical
  set φ : ι → (σ → ℂ) →L[ℂ] ℂ := fun j => fderiv ℂ (h j) a with hφ
  set L : (σ → ℂ) →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun j => (φ j : (σ → ℂ) →ₗ[ℂ] ℂ) with hL
  have hLs : Function.Surjective L := pi_surjective_of_linearIndependent hli
  set K := LinearMap.ker L with hK
  obtain ⟨q, hq⟩ := K.exists_isCompl
  set d := Module.finrank ℂ K with hd'
  have hd : d + Fintype.card ι = Fintype.card σ := by
    have := L.finrank_range_add_finrank_ker
    have hKk : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker L) := rfl
    rw [LinearMap.range_eq_top.2 hLs, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at this
    omega
  set eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq K (Fin d → ℂ) (by simp [d]) with heK
  set A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ K.projectionOnto q hq) with hA
  set P : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ) := A.prod (ContinuousLinearMap.pi φ) with hP
  have hPinj : Function.Injective P := by
    intro z w hzw
    rw [← sub_eq_zero]
    have h1 : A (z - w) = 0 := by rw [map_sub, sub_eq_zero]; exact congrArg Prod.fst hzw
    have h2 : z - w ∈ K := by
      rw [hK, LinearMap.mem_ker]
      funext j
      have := congrFun (congrArg Prod.snd hzw) j
      simp only [hP, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply] at this
      simp [hL, map_sub, this]
    have h3 : K.projectionOnto q hq (z - w) = 0 := eK.injective (by simpa [hA] using h1)
    rw [Submodule.projectionOnto_apply_of_mem_left hq h2] at h3
    simpa using congrArg Subtype.val h3
  have hPbij : Function.Bijective (P : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ) × (ι → ℂ)) :=
    ⟨hPinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, hd])).1 hPinj⟩
  set Pe : (σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ) :=
    (LinearEquiv.ofBijective _ hPbij).toContinuousLinearEquiv with hPe
  have hPeP : (Pe : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ)) = P := by ext1 x; rfl
  set F : (σ → ℂ) → (Fin d → ℂ) × (ι → ℂ) := fun z => (A z, fun j => h j z) with hF
  have hFan : ∀ z, (∀ j, AnalyticAt ℂ (h j) z) → AnalyticAt ℂ F z := fun z hz =>
    (A.analyticAt z).prod (analyticAt_pi_iff.2 hz)
  have hFd : HasFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    rw [hPeP]
    exact A.hasFDerivAt.prodMk (hasFDerivAt_pi.2 fun j => (hh j).differentiableAt.hasFDerivAt)
  have hst : HasStrictFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    have := (hFan a hh).hasStrictFDerivAt; rwa [hFd.fderiv] at this
  set Φ := hst.toOpenPartialHomeomorph F with hΦ
  have hev : ∀ᶠ t in 𝓝 a, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) := by
    refine (Filter.eventually_all.2 fun j => (hh j).eventually_analyticAt).and ((show ∀ᶠ t in 𝓝 a, t ∈ W from hW).and ?_)
    exact (hFan a hh).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨Pe, hFd.fderiv.symm⟩)
  obtain ⟨V₀, hV₀, hV₀o, haV₀⟩ := eventually_nhds_iff.1 hev
  set Ψ := Φ.restrOpen V₀ hV₀o with hΨ
  have hΨs : Ψ.source = Φ.source ∩ V₀ := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΨF : ∀ z, Ψ z = F z := fun z => rfl
  have haΨ : a ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, haV₀⟩
  have hsrc : ∀ t ∈ Ψ.source, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) :=
    fun t ht => hV₀ t (hΨs ▸ ht).2
  set O : Set (Fin d → ℂ) := (fun y => (y, (0 : ι → ℂ))) ⁻¹' Ψ.target with hO
  refine ⟨d, A, O, Ψ.source, fun y => Ψ.symm (y, 0), hd,
    Ψ.open_target.preimage (continuous_id.prodMk continuous_const), Ψ.open_source, haΨ,
    fun t ht => (hsrc t ht).2.1, ?_, ?_, ?_⟩
  · intro y hy
    have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
    obtain ⟨han, -, e', he'⟩ := hsrc _ (Ψ.map_target hp)
    have hFe : HasFDerivAt Ψ (e' : (σ → ℂ) →L[ℂ] _) (Ψ.symm (y, 0)) := by
      rw [he']; exact (hFan _ han).differentiableAt.hasFDerivAt
    have hc : ContDiffAt ℂ ω Ψ.symm (y, 0) :=
      Ψ.contDiffAt_symm hp hFe (hFan _ han).contDiffAt
    have hi : AnalyticAt ℂ (fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) y :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := Ψ.symm) (f := fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) (x := y)
      hc.analyticAt hi
  · intro y hy
    exact congrArg Prod.fst (Ψ.right_inv (show (y, (0 : ι → ℂ)) ∈ Ψ.target from hy))
  · ext z
    constructor
    · rintro ⟨hzV, hz0⟩
      have hFz : F z = (A z, 0) := by
        simp only [hF, Prod.mk.injEq, true_and]; funext j; exact hz0 j
      refine ⟨A z, ?_, ?_⟩
      · show (A z, (0 : ι → ℂ)) ∈ Ψ.target
        rw [← hFz, ← hΨF]; exact Ψ.map_source hzV
      · show Ψ.symm (A z, 0) = z
        rw [← hFz, ← hΨF]; exact Ψ.left_inv hzV
    · rintro ⟨y, hy, rfl⟩
      have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
      refine ⟨Ψ.map_target hp, fun j => ?_⟩
      have := congrFun (congrArg Prod.snd (Ψ.right_inv hp)) j
      simpa [hΨF, hF] using this

end AnalyticImplicitChart

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticSimpleRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology
open scoped ContDiff

noncomputable section

theorem AnalyticSimpleRootBranch.proof : AnalyticSimpleRootBranch.Statement := by
  intro d N a y τ ha hroot hder
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (y, τ) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (y, τ)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ ω F (y, τ) := hFa.contDiffAt
  have hpe : ∀ s, p.eval s = F (y, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    have h2 : (fun s : ℂ => F (y, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := hcd.implicitFunction hω hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self hω hinv
  have hψa : AnalyticAt ℂ ψ y := (hcd.contDiffAt_implicitFunction hω hinv).analyticAt
  have hF0 : F (y, τ) = 0 := hroot
  obtain ⟨U₁, B, hU₁o, hyU₁, hBo, hτB, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hcd.eventually_apply_eq_iff_implicitFunction hω hinv)
  set W : Set (Fin d → ℂ) := U₁ ∩ {x | AnalyticAt ℂ ψ x} with hW
  have hWo : IsOpen W := hU₁o.inter (isOpen_analyticAt ℂ ψ)
  have hWc : ContinuousOn ψ W := fun x hx => hx.2.continuousAt.continuousWithinAt
  refine ⟨W ∩ ψ ⁻¹' B, B, ψ, hWc.isOpen_inter_preimage hWo hBo, ⟨⟨hyU₁, hψa⟩, by simpa [hψy] using hτB⟩,
    hBo, hτB, fun x hx => hx.1.2, hψy, fun y' hy' => ⟨hy'.2, fun s hs => ?_⟩⟩
  have h := hsub (Set.mk_mem_prod hy'.1.1 hs)
  simp only [Set.mem_ofPred_eq] at h
  change F (y', s) = 0 ↔ s = ψ y'
  rw [← hF0, h]
  exact eq_comm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicInverse.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      IsOpen (f '' U) ∧
        ∃ g : (Fin k → ℂ) → Fin k → ℂ, DifferentiableOn ℂ g (f '' U) ∧ ∀ t ∈ U, g (f t) = t

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

