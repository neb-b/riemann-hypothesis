module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2LocT
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix

theorem g_cast_ne_zero {D : D7} (X : HidaSetting D) : (X.B.g : X.B.I.F) ≠ 0 := by
  rw [X.g_eq]
  push_cast
  exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)

theorem ginv_int {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)) :
    (algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹)) ∈ v.adicCompletionIntegers X.B.I.F := by
  rw [mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero] at hv
  unfold IsTyped at hv
  rw [not_or] at hv
  have hg : ((X.B.g : 𝓞 X.B.I.F)) ∉ v.asIdeal := by
    rw [X.g_eq]
    push_cast
    intro h
    rcases v.isPrime.mem_or_mem h with h | h
    exacts [hv.1 h, hv.2 h]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹) =
      (((X.B.g : X.B.I.F)⁻¹ : X.B.I.F) : v.adicCompletion X.B.I.F) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : v.valuation X.B.I.F (X.B.g : X.B.I.F) = 1 := by
    rw [show (X.B.g : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (X.B.g : 𝓞 X.B.I.F) by simp,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hg]
  rw [this, inv_one]

theorem smul_latLoc {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1))
    (u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (hu : u ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    (fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) * u i) ∈
      latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have := Submodule.smul_mem _ (⟨_, ginv_int X v hv⟩ : v.adicCompletionIntegers X.B.I.F) hu
  convert this using 1
  funext i
  rw [Pi.smul_apply, IsScalarTower.algebraMap_apply X.B.I.F (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    ← Algebra.smul_def]
  rfl

theorem kgLoc_holds : KgLoc := by
  intro D X hb κ hκ hT
  refine ⟨hκ, fun y hy => ?_⟩
  let c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := algebraMap X.B.I.F _ ((X.B.g : X.B.I.F)⁻¹)
  refine ⟨fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i, ?_, ?_⟩
  · apply PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective
    intro v
    have hy' := PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy v
    have hmat : (X.B.I.fmat κ).map (PI.FinKW.psiV X.B.I v) =
        ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
      change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb κ) :
        GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
          (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
      rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb κ, Matrix.map_map]
      rfl
    have hvec : PI.FinKW.vecV X.B.I v (fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i) =
        fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) *
          ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v y) i := by
      funext i
      simp only [PI.FinKW.vecV, map_mul, c, AlgHom.commutes]
      congr 1
      have h1 := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat κ - 1) y i
      rw [← hmat, ← Matrix.map_one (PI.FinKW.psiV X.B.I v).toRingHom (map_zero _) (map_one _)]
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)] at h1
      exact h1
    rw [hvec]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec]
      simp only [Pi.zero_apply, mul_zero]
      exact Submodule.zero_mem _
    · apply smul_latLoc X v hv
      have hK := compK_holds X v (finHA X hb κ) (finHA_mem_Kf X hb κ hκ)
      have hm := (hK (PI.FinKW.vecV X.B.I v y)).1 hy'
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Submodule.sub_mem _ hm hy'
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, c, ← mul_assoc]
    rw [show ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = algebraMap X.B.I.F _ (X.B.g : X.B.I.F) by simp,
      ← map_mul, mul_inv_cancel₀ (g_cast_ne_zero X), map_one, one_mul]

theorem globProd_of_k2LocT (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_loc kgLoc_holds ht

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ParabolicPreservesIsotropic
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Levi

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r} {c : R ⊗[F] E} {T : F}

theorem parabolic_preserves_isotropic {s : HA R σ J} (hs : s ∈ Ssub R σ J P) {x : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J s x ∈ spanR (F := F) R P.e Set.univ := by
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h1 := Submodule.span_mono (Set.image_mono (Set.subset_univ _)) (parabolic_unipotent_on_flag P hs b)
  have h2 := Submodule.add_mem _ h1 (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩ :
    ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e Set.univ)
  rwa [sub_add_cancel] at h2

theorem parabolic_fixes_modulo_span {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    lin R σ J s (ratV (F := F) R P.z) - ratV (F := F) R P.z ∈ spanR (F := F) R P.e Set.univ := by
  have h := hs (Fin.last r)
  have e : F0 P (Fin.last r) = P.z := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt ha)
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e Set.univ
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  rw [e']
  exact Submodule.subset_span ⟨a', Set.mem_univ _, rfl⟩

theorem isotropic_span_hermForm_zero (ht : FrameTab (σ := σ) (J := J) P c T) {x y : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) (hy : y ∈ spanR (F := F) R P.e Set.univ) : hR R σ J x y = 0 := by
  refine X_left hx fun b => ?_
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e y hy
  rw [hermForm_sum_right_alt]
  simp [ht.ee]

theorem parabolic_maps_complement (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    {a : Fin n → R ⊗[F] E} (ha : InW (σ := σ) (J := J) P a) :
    piRest (σ := σ) (J := J) P c (lin R σ J s a) ∈ spanR (F := F) R P.e Set.univ := by
  have h1 : ∀ b, hR R σ J (ratV (F := F) R (P.e b)) (lin R σ J s a) = 0 := fun b => by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R (P.e b)), hR_lin]
    exact X_left (parabolic_preserves_isotropic hs' (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)) ha.1
  have h3 : hR R σ J (ratV (F := F) R P.z) (lin R σ J s a) = 0 := by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R P.z), hR_lin]
    have e : lin R σ J s⁻¹ (ratV (F := F) R P.z) =
        ratV (F := F) R P.z + (lin R σ J s⁻¹ (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by abel
    rw [e, hR_add_left, ha.2.2, X_left (parabolic_fixes_modulo_span hs') ha.1, add_zero]
  rw [piRest_apply]
  simp only [h1, h3, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)

variable (P c)

def Lh (s : HA R σ J) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  piW (σ := σ) (J := J) P c ∘ₗ lin R σ J s ∘ₗ piW (σ := σ) (J := J) P c + piRest (σ := σ) (J := J) P c

variable {P c}

theorem Lh_apply (s : HA R σ J) (v : Fin n → R ⊗[F] E) : Lh P c s v =
    piW (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c v)) + piRest (σ := σ) (J := J) P c v := rfl

theorem piW_piRest (ht : FrameTab (σ := σ) (J := J) P c T) (v : Fin n → R ⊗[F] E) :
    piW (σ := σ) (J := J) P c (piRest (σ := σ) (J := J) P c v) = 0 := by
  have e : piRest (σ := σ) (J := J) P c v = v - piW (σ := σ) (J := J) P c v :=
    eq_sub_of_add_eq' (piW_add_rest (σ := σ) (J := J) P c v)
  rw [e, map_sub, piW_inW_eq ht (piW_inW ht v), sub_self]

theorem Lh_unitary (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    (u v : Fin n → R ⊗[F] E) : hR R σ J (Lh P c s u) (Lh P c s v) = hR R σ J u v := by
  set pu := piW (σ := σ) (J := J) P c u
  set pv := piW (σ := σ) (J := J) P c v
  have hpu := piW_inW (c := c) ht u
  have hpv := piW_inW (c := c) ht v

  have hmid : hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) =
      hR R σ J pu pv := by
    have eA := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pu)
    have eB := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pv)
    have hxa := parabolic_maps_complement ht hs' hpu
    have hxb := parabolic_maps_complement ht hs' hpv
    have key : hR R σ J (lin R σ J s pu) (lin R σ J s pv) =
        hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) := by
      conv_lhs => rw [← eA, ← eB]
      rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis,
        inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _), isotropic_span_hermForm_zero ht hxa hxb]
      ring
    rw [← key, hR_lin]
  rw [Lh_apply, Lh_apply, hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, hmid,
    inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _)]
  conv_rhs => rw [← piW_add_rest (σ := σ) (J := J) P c u, ← piW_add_rest (σ := σ) (J := J) P c v]
  rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, inW_left ht hpu, inW_right ht hpv]

theorem Lh_inv (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (v : Fin n → R ⊗[F] E) : Lh P c s (Lh P c s⁻¹ v) = v := by
  set w := piW (σ := σ) (J := J) P c v
  have hw := piW_inW (c := c) ht v
  set p := piW (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
  have hp := piW_inW (c := c) ht (lin R σ J s⁻¹ w)
  have e1 : Lh P c s⁻¹ v = p + piRest (σ := σ) (J := J) P c v := rfl
  have e2 : piW (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = p := by
    rw [map_add (f := _), piW_inW_eq ht hp, piW_piRest ht, add_zero]
  have e3 : piRest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = piRest (σ := σ) (J := J) P c v := by
    have := piW_add_rest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v)
    rw [e2] at this
    exact add_left_cancel this
  have hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P := by rw [inv_inv]; exact hs
  have hx := parabolic_maps_complement ht hs'' hw
  have e4 : lin R σ J s p = w - lin R σ J s (piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)) := by
    have := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
    have e5 : p = lin R σ J s⁻¹ w - piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w) :=
      eq_sub_of_add_eq this
    rw [e5, map_sub, lin_lin_inv R σ J s w]
  rw [e1, Lh_apply, e2, e3, e4, map_sub, piW_inW_eq ht hw, piW_X ht (parabolic_preserves_isotropic hs hx), sub_zero]
  exact piW_add_rest (σ := σ) (J := J) P c v

end Levi

end MassDataLevelSSteps
end
end

