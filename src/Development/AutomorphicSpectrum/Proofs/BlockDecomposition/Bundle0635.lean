module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0630
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRep

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

section Rep

variable {G : Type} [Group G] {K : Subgroup G} {V : Submodule ℂ (G → ℂ)}

def rt (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : K →* Module.End ℂ V where
  toFun k :=
    { toFun := fun v => ⟨fun x => v.1 (x * (k : G)), hV v.1 v.2 k⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp [mul_assoc]

theorem rt_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) (v : V) (x : G) :
    (rt hV k v).1 x = v.1 (x * (k : G)) := rfl

variable [FiniteDimensional ℂ V]

def mat (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) :
    Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (rt hV k)

theorem mat_mul (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (a b : K) :
    mat hV (a * b) = mat hV a * mat hV b := by
  simp only [mat, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem mat_one (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : mat hV 1 = 1 := by
  simp only [mat, map_one]
  exact LinearMap.toMatrix_one _

def rho (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) :
    K →* ((Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) where
  toFun k := LinearMap.toContinuousLinearMap (Matrix.toLin' (mat hV k⁻¹)ᵀ)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro a
    simp [mat_one]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_inv_rev, mat_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem rho_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (a : Fin (Module.finrank ℂ V) → ℂ) (i : Fin (Module.finrank ℂ V)) :
    rho hV k a i = ∑ j, (Module.finBasis ℂ V).repr (rt hV k⁻¹ (Module.finBasis ℂ V i)) j * a j := by
  change ((mat hV k⁻¹)ᵀ *ᵥ a) i = _
  simp [Matrix.mulVec, dotProduct, mat, LinearMap.toMatrix_apply]

theorem sum_repr_apply (z : V) (x : G) :
    ∑ j, (Module.finBasis ℂ V).repr z j * (Module.finBasis ℂ V j).1 x = z.1 x := by
  have h := congrArg (fun y : V => y.1 x) ((Module.finBasis ℂ V).sum_repr z)
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h

def w₀ (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] : Fin (Module.finrank ℂ V) → ℂ :=
  fun j => (Module.finBasis ℂ V j).1 1

theorem rho_w₀ (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (i : Fin (Module.finrank ℂ V)) : rho hV k (w₀ V) i = (Module.finBasis ℂ V i).1 ((k : G)⁻¹) := by
  rw [rho_apply]
  simp only [w₀]
  rw [sum_repr_apply, rt_apply]
  simp

end Rep

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
  {V : Submodule ℂ (G → ℂ)} [FiniteDimensional ℂ V]

def evl (V : Submodule ℂ (G → ℂ)) (x : G) : Module.Dual ℂ V := (LinearMap.proj x).comp V.subtype

theorem span_evl : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  have h : (Submodule.span ℂ (Set.range (evl V))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    have : v = 0 := by
      apply Subtype.ext
      funext x
      exact hv _ (Submodule.subset_span ⟨x, rfl⟩)
    simp [this]
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := Submodule.span ℂ (Set.range (evl V)))
  rw [h] at h2
  simpa using h2.symm

theorem cont_coef (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) (ℓ : Module.Dual ℂ V) (v : V) :
    Continuous fun k : K => ℓ (rt hV k⁻¹ v) := by
  have hℓ : ℓ ∈ Submodule.span ℂ (Set.range (evl V)) := by
    rw [span_evl]
    trivial
  induction hℓ using Submodule.span_induction with
  | mem ℓ h =>
    obtain ⟨x, rfl⟩ := h
    have h1 : Continuous fun k : K => x * (((k⁻¹ : K)) : G) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_inv)
    exact (hc v.1 v.2).comp h1
  | zero => simpa using continuous_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul a ℓ _ h => exact continuous_const.mul h

theorem rho_cont (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) : Continuous (rho hV) := by
  rw [continuous_clm_apply]
  intro a
  refine continuous_pi fun i => ?_
  simp only [rho_apply]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (cont_coef hV hc ((Module.finBasis ℂ V).coord j) _).mul continuous_const

end Cont

theorem ch_one {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ}
    (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)

theorem exists_rep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  intro G _ _ _ Γ K P c η hch hηK _ f u hf hlaw hfd
  obtain ⟨V, hVdef⟩ : ∃ V : Submodule ℂ (G → ℂ),
      V = Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))) := ⟨_, rfl⟩
  rw [← hVdef] at hfd
  have hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V := by
    intro v hv k
    rw [hVdef] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact Submodule.subset_span ⟨k * k', by funext x; simp [mul_assoc]⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a v _ hv => exact Submodule.smul_mem _ a hv
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    rw [hVdef] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact hf.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul a v _ hv => exact continuous_const.smul hv
  have hl : ∀ v ∈ V, ∀ p ∈ P, ∀ x, v (p * x) = c p * Complex.exp (u * η p) * v x := by
    intro v hv p hp x
    rw [hVdef] at hv
    induction hv using Submodule.span_induction generalizing x with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      change f (p * x * (k' : G)) = c p * Complex.exp (u * η p) * f (x * (k' : G))
      rw [mul_assoc, hlaw p hp]
    | zero => simp
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]; ring
    | smul a v _ hv => simp only [Pi.smul_apply, hv, smul_eq_mul]; ring
  have hfV : f ∈ V := by
    rw [hVdef]
    exact Submodule.subset_span ⟨1, by funext x; simp⟩
  refine ⟨Module.finrank ℂ V, rho hV, w₀ V,
    ∑ i, (Module.finBasis ℂ V).repr ⟨f, hfV⟩ i •
      (ContinuousLinearMap.proj i : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ),
    rho_cont hV hcont, ?_, ?_⟩
  · intro r hr
    funext i
    have hri : ((r : G))⁻¹ ∈ P := P.inv_mem hr
    have hrK : ((r : G))⁻¹ ∈ K := K.inv_mem r.2
    have h1 := hl _ (Module.finBasis ℂ V i).2 _ hri 1
    have h2 : c r * c ((r : G))⁻¹ = 1 := by
      rw [← hch.mul _ hr _ hri, mul_inv_cancel, ch_one hch]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [rho_w₀]
    rw [mul_one, hηK _ hri hrK] at h1
    rw [h1]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [← mul_assoc, h2, one_mul]
    rfl
  · intro k
    have h := sum_repr_apply (V := V) ⟨f, hfV⟩ (k : G)
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp only [rho_w₀]
    simpa using h

end GlobalTheory.CompanionTheory.SiegelRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitary
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Isotypic

variable {n : ℕ}

theorem exists_map_out (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (d : H) (hd : Formalism.REAL.KHighest (fun _ => true) G μ d) :
    ∃ T : L →ₗ[ℂ] H, T v = d ∧ ∀ a b w, T (K a b w) = G a b (T w) := by
  have hsp : ∀ x ∈ Submodule.span ℂ {v}, Formalism.REAL.KHighest (fun _ => true) K μ x := by
    intro x hx
    have hvm : v ∈ hwOf K μ := hv
    have : x ∈ hwOf K μ := (Submodule.span_singleton_le_iff_mem v (hwOf K μ)).2 hvm hx
    exact this
  let f : (Submodule.span ℂ {v}) →ₗ[ℂ] H :=
    ((innerₛₗ ℂ v).comp (Submodule.subtype _)).smulRight ((⟪v, v⟫_ℂ)⁻¹ • d)
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) G μ (f x) := by
    intro x
    have hdm : d ∈ hwOf G μ := hd
    have : f x ∈ hwOf G μ := by
      simp only [f, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hdm)
    exact this
  obtain ⟨T, hT, hi⟩ := _root_.GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend L H K G μ hK hG hKs hGs (Submodule.span ℂ {v}) hsp f hf
  refine ⟨T, ?_, hi⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have := hT ⟨v, Submodule.mem_span_singleton_self v⟩
  simp only at this
  rw [this]
  simp only [f, LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
  rw [smul_smul, mul_inv_cancel₀ hvv, one_smul]

theorem exists_map_in (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (D : Submodule ℂ H) (hD : ∀ x ∈ D, Formalism.REAL.KHighest (fun _ => true) G μ x) (φ : D →ₗ[ℂ] ℂ) :
    ∃ P : H →ₗ[ℂ] L, (∀ d : D, P d = φ d • v) ∧ ∀ a b w, P (G a b w) = K a b (P w) := by
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) K μ (φ.smulRight v x) := by
    intro x
    have hvm : v ∈ hwOf K μ := hv
    have : φ.smulRight v x ∈ hwOf K μ := by
      simp only [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hvm
    exact this
  obtain ⟨P, hP, hi⟩ := _root_.GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend H L G K μ hG hK hGs hKs D hD (φ.smulRight v) hf
  exact ⟨P, fun d => by rw [hP d, LinearMap.smulRight_apply], hi⟩

theorem eq_smul_id_of_apply (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (K : Fin n → Fin n → Module.End ℂ L) (hK : Formalism.REAL.GlRel K)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) (v : L)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (R : L →ₗ[ℂ] L) (hR : ∀ a b w, R (K a b w) = K a b (R w)) (r : ℂ) (hr : R v = r • v) :
    R = r • LinearMap.id := by
  have h0 := GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest L L K K hK hKs (R - r • LinearMap.id)
    (fun a b w => by simp [hR, map_smul]) (fun μ w hw => by
      obtain ⟨c, rfl⟩ := huniq w (fun a b hab => hw.2 a b hab rfl)
      simp [hr, smul_comm c r])
  exact sub_eq_zero.1 h0

theorem map_highest_eq_zero {H L : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup L] [Module ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ μ' : Fin n → ℝ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ' v)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (P : H →ₗ[ℂ] L) (hP : ∀ a b w, P (G a b w) = K a b (P w))
    (hne : μ ≠ μ') (w : H) (hw : Formalism.REAL.KHighest (fun _ => true) G μ w) : P w = 0 := by
  obtain ⟨c, hc⟩ := huniq (P w) (fun a b hab => by rw [← hP, hw.2 a b hab rfl, map_zero])
  by_contra hne0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne0 (by simpa using hc)
  apply hne
  funext a
  have h1 : K a a (P w) = (μ a : ℂ) • P w := by rw [← hP, hw.1 a, map_smul]
  rw [hc, map_smul, hv.1 a, smul_comm] at h1
  have h2 : ((μ' a : ℂ) - (μ a : ℂ)) • (c • v) = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (μ' a : ℂ) - (μ a : ℂ) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (smul_ne_zero hc0 hv0)
  have h4 : (μ' a : ℂ) = (μ a : ℂ) := sub_eq_zero.1 h3
  exact (Complex.ofReal_injective h4).symm

theorem map_mem_hwOf {H : Type} [AddCommGroup H] [Module ℂ H]
    (G : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (S : H →ₗ[ℂ] H)
    (hS : ∀ a b w, S (G a b w) = G a b (S w)) (x : H) (hx : x ∈ hwOf G μ) : S x ∈ hwOf G μ :=
  ⟨fun a => by rw [← hS, hx.1 a, map_smul],
    fun a b hab he => by rw [← hS, hx.2 a b hab he, map_zero]⟩

theorem exists_isotypic_projection {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ) :
    Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) →
    Antitone ν →
    ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  intro hG hGs hder hν
  obtain ⟨L, _, _, _, σ, K, v, hK, hKs, hσ, hv0, hv, huniq, htr⟩ := GlobalTheory.T.exists_highest_weight_hermitian_derivation ν hν
  have hD : ∀ x ∈ hwOf G (wtR ν), Formalism.REAL.KHighest (fun _ => true) G (wtR ν) x := fun x hx => hx
  let b := Module.finBasis ℂ (hwOf G (wtR ν))
  have ex1 : ∀ j, ∃ T : L →ₗ[ℂ] H, T v = (b j : H) ∧ ∀ a c w, T (K a c w) = G a c (T w) := fun j =>
    exists_map_out H L G K (wtR ν) hG hK hGs hKs v hv0 hv (b j : H) (b j).2
  choose T hTv hTi using ex1
  have ex2 : ∀ j, ∃ P : H →ₗ[ℂ] L, (∀ d : hwOf G (wtR ν), P d = b.coord j d • v) ∧
      ∀ a c w, P (G a c w) = K a c (P w) := fun j =>
    exists_map_in H L G K (wtR ν) hG hK hGs hKs v hv _ hD (b.coord j)
  choose P hPd hPi using ex2
  have hPk : ∀ j k w, P j (ρ k w) = σ k (P j w) := fun j =>
    _root_.GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary H L ρ G hder σ K hσ hKs (P j) (hPi j)
  have hp : ∀ w, (∑ j, T j ∘ₗ P j) w = ∑ j, T j (P j w) := fun w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ j, T j ∘ₗ P j, ?_, ?_, ?_, ?_⟩
  · intro a c w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, hp, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPi, hTi]
  · intro d hd
    rw [hp]
    have h1 : ∀ j, T j (P j d) = b.coord j ⟨d, hd⟩ • (b j : H) := fun j => by
      have := hPd j ⟨d, hd⟩
      simp only at this
      rw [this, map_smul, hTv]
    simp only [h1]
    have h2 : ∑ j, b.coord j ⟨d, hd⟩ • b j = ⟨d, hd⟩ := b.sum_repr _
    calc ∑ j, b.coord j ⟨d, hd⟩ • (b j : H)
        = ((∑ j, b.coord j ⟨d, hd⟩ • b j : hwOf G (wtR ν)) : H) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = d := by rw [h2]
  · intro μ w hne hw
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_highest_eq_zero G K μ (wtR ν) v hv0 hv huniq (P j) (hPi j) hne w hw, map_zero]
  · intro S hS k z hk hz
    have hSD : ∀ x ∈ hwOf G (wtR ν), S x ∈ hwOf G (wtR ν) := map_mem_hwOf G (wtR ν) S hS
    have hj : ∀ j, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j)) =
        b.coord j ⟨S (b j), hSD _ (b j).2⟩ * weylChar ν z := by
      intro j
      have hR : P j ∘ₗ S ∘ₗ T j = b.coord j ⟨S (b j), hSD _ (b j).2⟩ • LinearMap.id := by
        refine eq_smul_id_of_apply L K hK hKs v huniq _ (fun a c w => ?_) _ ?_
        · simp only [LinearMap.comp_apply]
          rw [hTi, hS, hPi]
        · simp only [LinearMap.comp_apply]
          rw [hTv]
          exact hPd j ⟨S (b j), hSD _ (b j).2⟩
      have e1 : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) = ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) ∘ₗ P j := rfl
      have e2 : P j ∘ₗ ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) = σ k ∘ₗ (P j ∘ₗ S ∘ₗ T j) := by
        ext w
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact hPk j k _
      rw [e1, LinearMap.trace_comp_comm', e2, hR, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
        htr k z hk hz, smul_eq_mul]
    have hsum : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (∑ j, T j ∘ₗ P j) =
        ∑ j, (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) := by
      ext w
      set_option synthInstance.maxHeartbeats 100000 in
        simp [LinearMap.sum_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
    congr 1
    unfold trOn
    rw [dite_eq_left hSD, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl

end GlobalTheory.CompanionTheory.RealCountG.Isotypic
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotientsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_product_same_subquotients : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | exact GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | (intros; apply GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev <;> assumption)
end

