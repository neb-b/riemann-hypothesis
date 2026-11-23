module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.PstLine

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) {M : Type} [AddCommGroup M] [Module F M]

end Letter

section St

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V')

def stMap : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := f.rTensor (Bst P)

@[simp] theorem stMap_tmul (v : V) (b : Bst P) : stMap P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem stMap_smul {a : ↥L.1} {a' : ↥L'.1} (h : ∀ x, f (a • x) = a' • f x) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (a • x) = a' • stMap P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [smul_tmul', stMap_tmul, h, stMap_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

variable {f ρ ρ'}

theorem stMap_stRep (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (stRep P ρ g x) = stRep P ρ' g (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [he]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem stMap_mem_Dpst (he : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρ) :
    stMap P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← stMap_stRep P he, hx g hg]⟩

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x))

include he

end St

section Fun

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

structure IsMor (hL : L.1 ≤ L'.1) (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V)
    (ρ' : Representation ↥L'.1 ↥(GK K) V') : Prop where
  smul : ∀ (a : ↥L.1) x, f (a • x) = IntermediateField.inclusion hL a • f x
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)

variable {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ')

section Decomp

variable {n : ℕ} {e : Fin n → ↥L'.1} {A : Fin n → V' →ₗ[ℚ_[l]] V}

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (hA : ∀ i g y, A i (ρ' g y) = ρ g (A i y))
  (hs : ∀ y, ∑ i, e i • f (A i y) = y)




end Decomp

end Fun

section Bridge

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥L'.1 ↥(GK Bw.Kw) V'}

end Bridge

section Model

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1) (m : ℕ) (r : ↥Gw →* GL (Fin m) ↥L.1)

def incV : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L'.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

abbrev upRep : ↥Gw →* GL (Fin m) ↥L'.1 := mapRep (IntermediateField.inclusion hL).toRingHom r

theorem isMor_incV : IsMor hL (incV hL m) (Bw.repE L r) (Bw.repE L' (upRep hL m r)) := by
  constructor
  · intro a x
    exact funext fun i => map_mul (IntermediateField.inclusion hL) a (x i)
  · intro g x
    funext i
    exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) x i

end Model

section Line

variable {l : ℕ} [Fact l.Prime]

variable {L₁ L : FinExt l} (hL : L₁.1 ≤ L.1) {a : ℕ}

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

end Line

section Models

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
  [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}

end Models

section Vec

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ}

end Vec

end GlobalTheory.PstLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHoms
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.EntryHomComb

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem det_map_isUnit (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {P : Matrix (Fin N) (Fin N) D.host.E}
    (h : P.det ≠ 0) : IsUnit (P.map ρ).det := by
  have := ρ.map_det P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact Ne.isUnit ((map_ne_zero ρ).2 h)

theorem coord_le_one (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (hP : LocBasisW D ρ L P) {x : Fin N → D.host.E} (hx : x ∈ L) (m : Fin N) :
    ‖((P.map ρ)⁻¹ *ᵥ fun i => ρ (x i)) m‖ ≤ 1 := by
  obtain ⟨s, hs, c, hc⟩ := hP.2.2 x hx
  have hs0 : ρ (s : D.host.E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact zero_ne_one hs
  have e : ∀ i, (s : D.host.E) * x i = ∑ a, (c a : D.host.E) * P i a := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
    exact this
  have h1 : (fun i => ρ (x i)) = (P.map ρ) *ᵥ fun a => (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have h2 := congrArg ρ (e i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum] at h2
    simp only [map_mul] at h2
    calc ρ (x i) = (ρ (s : D.host.E))⁻¹ * (ρ (s : D.host.E) * ρ (x i)) := by field_simp
      _ = _ := by
        rw [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_map_isUnit D ρ hP.1), Matrix.one_mulVec, norm_mul,
    norm_inv, hs, inv_one, one_mul]
  exact GlobalTheory.JetTieCompare.norm_int_le ρ (c m)

theorem inv_mul_le_one (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B P : Matrix (Fin N) (Fin N) _}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (m b : Fin N) : ‖((P.map ρ)⁻¹ * B) m b‖ ≤ 1 := by
  obtain ⟨n, r, x, hr, hx, hcol⟩ := hB.2.2 b
  have : ((P.map ρ)⁻¹ * B) m b = ∑ k, r k * ((P.map ρ)⁻¹ *ᵥ fun i => ρ (x k i)) m := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (coord_le_one D ρ hP (hx k) m)

theorem inv_mul_le_one' (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B : Matrix (Fin N) (Fin N) ℂ_[p]}
    {P : Matrix (Fin N) (Fin N) D.host.E}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (a i : Fin N) : ‖(B⁻¹ * P.map ρ) a i‖ ≤ 1 := by
  obtain ⟨s, hs, hmem⟩ := hP.2.1 i
  have h := hB.2.1 _ hmem a
  rw [hρ] at h
  have e : (fun j => ρ ((s • P.transpose i) j)) = ρ (s : D.host.E) • fun j => ρ (P j i) := by
    funext j
    change ρ ((s : D.host.E) * P j i) = ρ (s : D.host.E) * ρ (P j i)
    rw [map_mul]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hs, one_mul] at h
  convert h using 2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem entry_comb : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  intro D N N' L L' hA p _ lm τ B B' hB hB' a b
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lm τ
  obtain ⟨P, hP⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L hA.2.2.1.1 hA.2.2.1.2.1
  obtain ⟨P', hP'⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L' hA.2.2.2.1 hA.2.2.2.2.1
  have hex : ∀ q : Fin N' × Fin N, ∃ s : D.host.E, ‖ρ s‖ = 1 ∧
      (Matrix.of fun i j => s * (P' i q.1 * P⁻¹ q.2 j)) ∈ homL D L L' := fun q =>
    GlobalTheory.Proof.DirectionalDerivative.exists_smul_mem_homL D ρ hA.2.2.1.1 hP hP' q.2 q.1
  choose s hs hsA using hex
  have hs0 : ∀ q, ρ (s q) ≠ 0 := fun q h => by rw [← norm_eq_zero, hs q] at h; exact one_ne_zero h
  let e := Fintype.equivFin (Fin N' × Fin N)
  have hdet := det_map_isUnit D ρ hP.1
  have hdet' := det_map_isUnit D ρ hP'.1
  have hinv : (P.map ρ)⁻¹ = (P⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  refine ⟨Fintype.card (Fin N' × Fin N),
    fun j => ((P'.map ρ)⁻¹ * B') (e.symm j).1 b * (B⁻¹ * P.map ρ) a (e.symm j).2 * (ρ (s (e.symm j)))⁻¹,
    fun j => Matrix.of fun k l => s (e.symm j) * (P' k (e.symm j).1 * P⁻¹ (e.symm j).2 l), fun j => ?_,
    fun j => hsA _, fun k l => ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hs, inv_one, mul_one]
    exact mul_le_one₀ (inv_mul_le_one D ρ hρ hB' hP' _ b) (norm_nonneg _) (inv_mul_le_one' D ρ hρ hB hP a _)
  · have e1 : B' k b = ∑ m, ρ (P' k m) * ((P'.map ρ)⁻¹ * B') m b := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_left (P'.map ρ) B' hdet']
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    have e2 : B⁻¹ a l = ∑ i, (B⁻¹ * P.map ρ) a i * ρ (P⁻¹ i l) := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_right (P.map ρ) B⁻¹ hdet, hinv]
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    rw [e1, e2, Finset.sum_mul_sum, ← Fintype.sum_prod_type', hρ, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    field_simp [hs0 (e.symm j)]

end GlobalTheory.EntryHomComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfMemSq
section
open NumberField

noncomputable section

namespace GlobalTheory.EmbSepUnram

open GlobalTheory.Proof.IdempotentLatticeSequence (primeOf mem_primeOf primeOf_isMaximal natCast_mem_primeOf norm_int_le)

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_int_le {E : Type} [Field E] (φ ψ : E →+* ℂ_[p]) (y : 𝓞 E) : ‖φ (y : E) - ψ (y : E)‖ ≤ 1 :=
  by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le φ y) ?_)
  rw [norm_neg]; exact norm_int_le ψ y

theorem exists_algEquiv {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] [IsGalois ℚ E]
    (ψ₁ ψ₂ : E →+* ℂ_[p]) (h : ∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) :
    ∃ σ : E ≃ₐ[K] E, ∀ x, ψ₁ x = ψ₂ (σ x) := by
  let _ : Algebra E ℂ_[p] := ψ₂.toAlgebra
  have _ := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := E) (A := ℂ_[p]) fun x => by
    show algebraMap ℚ ℂ_[p] x = ψ₂ (algebraMap ℚ E x)
    rw [eq_ratCast (algebraMap ℚ ℂ_[p]), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let τ : E ≃ₐ[ℚ] E := (ψ₁.toRatAlgHom).restrictNormal' E
  have hτ : ∀ x, ψ₂ (τ x) = ψ₁ x := fun x => (ψ₁.toRatAlgHom).restrictNormal_commutes E x
  let σ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x => ψ₂.injective (by
    change ψ₂ (τ _) = _
    rw [hτ]; exact h x)
  exact ⟨σ, fun x => (hτ x).symm⟩

theorem norm_le_of_mem_sq {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ r) {z : 𝓞 E} (hz : z ∈ primeOf φ ^ 2) :
    ‖φ (z : E)‖ ≤ r * r := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · change ‖φ (algebraMap (𝓞 E) E (a * b))‖ ≤ r * r
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_mul (h a ha) (h b hb) (norm_nonneg _) hr
  · change ‖φ (algebraMap (𝓞 E) E (a + b))‖ ≤ r * r
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem embSep : Formalism.L2.Th1.GD.EmbSep := by
  intro p _ K E _ _ _ _ _ _ φ ψ₁ ψ₂ ⟨π, hπ1, hπ⟩ hK hφ hne
  by_contra hc
  push Not at hc
  have h1 : ∀ y : 𝓞 E, ‖ψ₂ (y : E) - ψ₁ (y : E)‖ < 1 := fun y => by
    have a := lt_of_le_of_ne (norm_sub_int_le φ ψ₁ y) (hc y)
    have e : ψ₂ (y : E) - ψ₁ (y : E) = (φ (y : E) - ψ₁ (y : E)) + -(φ (y : E) - ψ₂ (y : E)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a ?_)
    rw [norm_neg]; exact hφ y
  have hP : ∀ z : 𝓞 E, ‖ψ₂ (z : E)‖ < 1 → z ∈ primeOf φ := fun z hz => by
    change ‖φ (z : E)‖ < 1
    rw [← sub_add_cancel (φ (z : E)) (ψ₂ (z : E))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ z) hz)
  obtain ⟨σ, hσ⟩ := exists_algEquiv ψ₁ ψ₂ hK
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have := primeOf_isMaximal φ
  have hP0 : primeOf φ ≠ ⊥ := fun h => by
    have := natCast_mem_primeOf φ
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have : IsGaloisGroup (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) K E
  have hp0 : (primeOf φ).under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0

  set r := ‖φ (algebraMap K E (π : K))‖ with hr
  have hr0 : 0 < r := by
    refine lt_of_lt_of_le ?_ (hπ (p : 𝓞 E) (natCast_mem_primeOf φ))
    rw [norm_pos_iff]
    have : ((p : 𝓞 E) : E) = (p : E) := rfl
    rw [this, map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) ((primeOf φ).under (𝓞 K)) ≤ primeOf φ ^ 2 := fun hle => by
    have hπP : algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ ^ 2 :=
      hle (Ideal.mem_map_of_mem _ (show algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ from hπ1))
    have := norm_le_of_mem_sq φ hr0.le hπ hπP
    change r ≤ r * r at this
    nlinarith
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) ((primeOf φ).under (𝓞 K)) (primeOf φ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) (E ≃ₐ[K] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) hp0,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hsq)] at hcard
  have hs : σ ∈ (primeOf φ).inertia (E ≃ₐ[K] E) := AddSubgroup.mem_inertia.2 fun x => hP _ (by
    change ‖ψ₂ (σ (x : E) - (x : E))‖ < 1
    rw [map_sub, ← hσ]
    exact h1 x |> fun h => by rwa [norm_sub_rev] at h)
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hne (RingHom.ext fun x => by rw [hσ, hs]; rfl)

end GlobalTheory.EmbSepUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuDCardLeASq
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nuD_card_le_a_sq : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  have hr := h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := h2 x (le_trans (le_max_right _ _) hx) hx1 i
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoRGLeKOfSize
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem two_rG_le_k_of_size {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} (hS : Formalism.MainNotions.SizesAt L)
    (h : 70 < L.sc.x * L.sc.eps) : 2 * Formalism.MainNotions.G.rG L.sc ≤ D.R.k := by
  by_contra hk
  have hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc := not_le.1 hk
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk.le
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 he.le
  have h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps =
      2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps) := by
    field_simp
  rw [h7] at h6
  unfold Formalism.MainNotions.G.hG at h6
  linarith

theorem two_rG_le_k_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 2 * rG (Fm.L x i).sc ≤ (Fm.D x i).R.k := by
  refine ⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩
  have hs : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hp : 0 < eps := he ▸ (Fm.L x i).sc.eps_pos
  rw [hs, he]
  have : 71 ≤ x * eps := (div_le_iff₀ hp).1 hx
  linarith

end GlobalTheory.TwU
end
end

