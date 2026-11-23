module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory

theorem goodModel_coords_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  intro F E _ _ _ _ _ σ ψ n d X W M M₁ hM hM₁
  classical
  let ι := algebraMap F (AF F)
  have hι : Function.Injective ι := AdeleRing.algebraMap_injective (𝓞 F) F
  let sp := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let Φ₀ := M.co.e.trans sp.symm
  let Φ₁ := M₁.co.e.trans sp.symm
  have hΦ₀ : ∀ u, Φ₀ u = Sum.elim (M.co.e u).1 (M.co.e u).2 := fun u => rfl
  have hΦ₁ : ∀ u, Φ₁ u = Sum.elim (M₁.co.e u).1 (M₁.co.e u).2 := fun u => rfl
  let A : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F) :=
    LinearMap.toMatrix' ((Φ₀.symm.trans Φ₁ : _ ≃ₗ[AF F] _) : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] _)
  have hA : ∀ u, A *ᵥ Φ₀ u = Φ₁ u := by
    intro u; simp [A, LinearMap.toMatrix'_mulVec]

  have hspan : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = ⊤ := by
    rw [eq_top_iff]; intro U _
    rw [Matrix.matrix_eq_sum_single U]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    generalize U i j = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply, inclR]
        split_ifs
        · simp [TensorProduct.smul_tmul']
        · simp
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  have hspan' : Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = ⊤ := by
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hrat0 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₀ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₀, h]; cases i <;> rfl
  have hrat1 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₁ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM₁.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₁, h]; cases i <;> rfl
  let G : Set ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) := {w | ∃ x, Φ₀ (incM F x) = fun i => ι (w i)}
  have hG : Submodule.span F G = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F := fun i => f (fun j => if i = j then 1 else 0)
    have hfc : ∀ w, f w = ∑ i, w i * c i := by
      intro w; rw [LinearMap.pi_apply_eq_sum_univ f w]; simp [c, smul_eq_mul]
    have hP : ∀ V ∈ Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
        ∑ i, V i * ι (c i) = 0 := by
      intro V hV
      induction hV using Submodule.span_induction with
      | mem V hV =>
        obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hV
        obtain ⟨w, hw⟩ := hrat0 x
        have h1 := hfk (Submodule.subset_span (show w ∈ G from ⟨x, hw⟩))
        rw [LinearMap.mem_ker, hfc] at h1
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, hw, ← map_mul, ← map_sum, h1, map_zero]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul a x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]
    have hc : ∀ i, c i = 0 := by
      intro i
      have h1 := hP (Pi.single i 1) (by rw [hspan']; trivial)
      simp [Pi.single_apply] at h1
      exact hι (by simpa using h1)
    exact hf0 (LinearMap.ext fun w => by simp [hfc, hc])

  have hrat : ∀ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, ∃ q : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
      A *ᵥ (fun i => ι (w i)) = fun i => ι (q i) := by
    intro w
    have hw : w ∈ Submodule.span F G := hG ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx⟩ := hw
      obtain ⟨q, hq⟩ := hrat1 x
      exact ⟨q, (congrArg (A *ᵥ ·) hx).symm.trans ((hA _).trans hq)⟩
    | zero => exact ⟨0, by funext i; simp [Matrix.mulVec, dotProduct]⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx; obtain ⟨q, hq⟩ := hy
      refine ⟨p + q, ?_⟩
      have : (fun i => ι ((x + y) i)) = (fun i => ι (x i)) + (fun i => ι (y i)) := by funext i; simp
      rw [this, Matrix.mulVec_add, hp, hq]; funext i; simp
    | smul c x _ hx =>
      obtain ⟨p, hp⟩ := hx
      refine ⟨c • p, ?_⟩
      have : (fun i => ι ((c • x) i)) = ι c • (fun i => ι (x i)) := by funext i; simp
      rw [this, Matrix.mulVec_smul, hp]; funext i; simp
  choose q hq using fun j : (Fin n × Fin d) ⊕ (Fin n × Fin d) => hrat (Pi.single j 1)
  let a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F := Matrix.of fun i j => q j i
  have haA : a.map ι = A := by
    ext i j
    have h1 : A *ᵥ Pi.single j 1 = fun i => ι (q j i) := by
      rw [← hq j]; congr 1; funext k; simp [Pi.single_apply]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one] at h2
    simpa [a] using h2.symm
  have hstd : ∀ w w' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      w ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ w') = (w ∘ Sum.inl) ⬝ᵥ (w' ∘ Sum.inr) - (w' ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) := by
    intro w w'
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, mul_comm, sub_eq_add_neg]
  have hform : ∀ u u', Φ₁ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₁ u') = Φ₀ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₀ u') := by
    intro u u'
    rw [hstd, hstd, hΦ₀, hΦ₀, hΦ₁, hΦ₁]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← M.co.form, ← M₁.co.form]
  have hsympA : Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 := by
    ext i j
    have key : ∀ N : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F),
        N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
      intro N; simp [Matrix.mulVec_single_one]
    rw [key (Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A), key (Matrix.fromBlocks 0 1 (-1) 0)]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e1 : ∀ s, A *ᵥ s = Φ₁ (Φ₀.symm s) := fun s => by rw [← hA, LinearEquiv.apply_symm_apply]
    rw [e1, e1, hform]
    simp
  refine ⟨a, ?_, ?_⟩
  · apply Matrix.map_injective hι
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map]
    rw [haA]
    simpa [Matrix.map_zero, Matrix.map_one, Matrix.map_neg] using hsympA
  · intro u
    rw [show a.map (algebraMap F (AF F)) = A from haA, ← hΦ₀, hA, hΦ₁]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacUnip

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell GlobalTheory.DblVacFactor

section Abstract

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β] [Invertible (2 : R)]

theorem mem_unitary_of_skew (f : R →+* R) (J : Matrix β β R) (K : Matrix (β ⊕ β) (β ⊕ β) R)
    (Δ N : Matrix (β ⊕ β) β R) (Δt Nt : Matrix β (β ⊕ β) R) (x : Matrix β β R)
    (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (hZ : xᵀ * J + J * x.map f = 0) :
    (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = K := by
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

end Abstract

theorem unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  intro F E _ _ _ _ _ σ d W v h2 Z hZat hZlat hZskew
  letI : Invertible (2 : AE F E) := invTwoE
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  have hskew : Zᵀ * J + J * Z.map f = 0 := hZskew
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1 Z
  have hmem := mem_unitary_of_skew f J (dbl J) _ _ _ _ Z hΔT hNT hΔf hNtf (e3 J) (e4 J) (e5 J) hskew
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hu' : u • Z = 0 := hZat u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (u • Z) *
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
  refine ⟨p, hpK, ⟨1, ?_⟩, ?_⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1,
        Matrix.mul_zero, smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
        ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
      rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
    show (1 + ⅟(2 : AE F E) • M) = _
    rw [hNt, invOf_two_eq, algebraMap_smul]
    rfl

end GlobalTheory.DblVacUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.UPel.HT.MapComp

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) : ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ :=
  ⟨_, congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

end GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def MapComp.comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := m₁.cart.comp m₂.cart
  sq := isSquare_comp m₁.sq m₂.sq
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem MapComp.cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : Nonempty (ObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

theorem objMap_comp_cancel (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂)
    (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (Nonempty (ObjMap o₁ o₂ f) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₃ (f ≫ g))) ∧
      (Nonempty (ObjMap o₁ o₃ (f ≫ g)) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₂ f)) :=
  ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun ⟨m⟩ ⟨m₂⟩ => MapComp.cancel m m₂⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamComplexTensorNormColumnUnitSpheresLe
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.ColNorm

theorem csq_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    csq h σ (fun i => c (e i)) (fun i => v (e i)) = csq h σ c v := by
  unfold csq
  congr 1
  exact Fintype.sum_equiv e _ _ fun i => Fintype.sum_equiv e _ _ fun k => rfl

theorem cnrm_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    cnrm h σ (fun i => c (e i)) (fun i => v (e i)) = cnrm h σ c v :=
  congrArg Real.sqrt (csq_equiv h σ e c v)

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (Fin.tail u) := by
  simp only [word, List.ofFn_succ, List.prod_cons]
  rfl

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A]

theorem cnrm_words_le (S : Sys F A) (hS : S.Hyp) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ)
    (hu : ∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) :
    ∀ (t : ℕ) (β : Fin t → Fin (S.D + 1)) (j l : ℕ), j + t = l → l ≤ S.T →
      ∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : (Fin t → Fin S.N) × Fin m → S.V l),
      (∀ e i, (g (e, i) : A) = word S.mul (fun q => Pi.single (e q) 1) (f i)) →
      cnrm (S.nm l) σ (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g ≤ Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f := by
  intro t
  induction t with
  | zero =>
    intro β j l hl _ m c f g hg
    obtain rfl : l = j := by omega
    have e : g = fun p => f p.2 := funext fun p => Subtype.ext (by
      rw [show p = (p.1, p.2) from rfl, hg]
      simp [word])
    subst e
    have := cnrm_equiv (S.nm l) σ (Equiv.uniqueProd (Fin m) (Fin 0 → Fin S.N)).symm
      (fun p => (∏ q, u (β q, p.1 q)) * c p.2) (fun p => f p.2)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, pow_zero] at this ⊢
    rw [← this]
    rfl
  | succ t ih =>
    intro β j l hl hlT m c f g hg
    obtain rfl : l = j + t + 1 := by omega
    have hmem := (_root_.GlobalTheory.HSShort.wordMem F A S hS j t (by omega)).1
    let g' : (Fin t → Fin S.N) × Fin m → S.V (j + t) := fun p =>
      ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (f p.2), hmem _ _ (f p.2).2⟩
    have h₀ := ih (Fin.tail β) j (j + t) rfl (by omega) m c f g' (fun _ _ => rfl)
    let eM : (Fin t → Fin S.N) × Fin m ≃ Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) := Fintype.equivFin _
    let E : Fin S.N × Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) ≃ (Fin (t + 1) → Fin S.N) × Fin m :=
      { toFun := fun p => (Fin.cons p.1 (eM.symm p.2).1, (eM.symm p.2).2)
        invFun := fun p => (p.1 0, eM (Fin.tail p.1, p.2))
        left_inv := fun p => by simp
        right_inv := fun p => by simp }
    have hE : ∀ k r, E (k, r) = (Fin.cons k (eM.symm r).1, (eM.symm r).2) := fun k r => rfl
    have hb := hS.bound σ (j + t) (by omega) (fun k => u (β 0, k)) _
      (fun r => (∏ q, u (Fin.tail β q, (eM.symm r).1 q)) * c (eM.symm r).2) (fun r => g' (eM.symm r))
      (fun p => g (E p)) (fun k r => by
        rw [hE, hg, word_succ]
        rfl)
    have hq := cnrm_equiv (S.nm (j + t)) σ eM.symm (fun p => (∏ q, u (Fin.tail β q, p.1 q)) * c p.2) g'
    have h1 := cnrm_equiv (S.nm (j + t + 1)) σ E (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g
    have hc : ∀ p, (∏ q, u (β q, (E p).1 q)) * c (E p).2 =
        u (β 0, p.1) * ((∏ q, u (Fin.tail β q, (eM.symm p.2).1 q)) * c (eM.symm p.2).2) := fun p => by
      obtain ⟨k, r⟩ := p
      rw [hE]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring
    simp only [hc] at h1
    rw [hu, mul_one, hq] at hb
    rw [← h1]
    calc _ ≤ _ := hb
      _ ≤ Real.sqrt S.beta * (Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f) :=
        mul_le_mul_of_nonneg_left h₀ (Real.sqrt_nonneg _)
      _ = _ := by ring

end GlobalTheory.HSShort.ColNorm


open GlobalTheory.HSShort.ColNorm in
theorem GlobalTheory.HSShort.cnrm_col_le : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (κ : S.Col) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ), (∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) → cnrm (S.nm S.T) σ (fun i => eval₂ σ u (coordP S.mul (c i) κ.β (κ.x : A))) b ≤ Real.sqrt S.beta ^ κ.t * (S.nm κ.j).nrm σ κ.x := by
  intro F A _ _ _ _ _ _ S hS d b c hc κ σ u hu
  obtain ⟨j, t, hjt, β, x⟩ := κ
  have hmem := (_root_.GlobalTheory.HSShort.wordMem F A S hS j t (by omega)).1
  let g : (Fin t → Fin S.N) × Fin 1 → S.V S.T := fun p =>
    ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (x : A), by rw [← hjt]; exact hmem _ _ x.2⟩
  have key := cnrm_words_le S hS σ u hu t β j S.T hjt le_rfl 1 (fun _ => 1) (fun _ => x) g (fun _ _ => rfl)
  have hr : cnrm (S.nm j) σ (fun _ : Fin 1 => (1 : ℂ)) (fun _ => x) = (S.nm j).nrm σ x := by
    simp [cnrm, csq, HermFam.nrm]
  rw [hr] at key
  refine le_of_eq_of_le ?_ key
  unfold cnrm
  congr 1
  calc _ = csq (S.nm S.T) σ (fun i => ∑ p, ((∏ q, u (β q, p.1 q)) * 1) * σ (b.repr (g p) i)) b := by
        congr 1
        funext i
        simp only [coordP, eval₂_sum, eval₂_mul, eval₂_C, eval₂_prod, eval₂_X, Fintype.sum_prod_type,
          Finset.univ_unique, Finset.sum_singleton, mul_one]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← hc i (g (e, default))]
        simp [g, mul_comm]
    _ = csq (S.nm S.T) σ (fun p => (∏ q, u (β q, p.1 q)) * 1) (fun p => ∑ i, b.repr (g p) i • b i) :=
        (csq_comb _ _ _ _ _).symm
    _ = _ := by simp only [b.sum_repr]
end
end

