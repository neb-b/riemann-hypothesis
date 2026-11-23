module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviFixesAnisotropic
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Pack

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r} {c : R ⊗[F] E} {T : F}

theorem Lh_fix_e (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) (b : Fin r) :
    Lh P c s (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R (P.e b)) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_e ht b, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_e ht b]

theorem Lh_fix_f (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) (b : Fin r) :
    Lh P c s (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R (P.f b)) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_f ht b, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_f ht b]

theorem levi_fixes_anisotropic (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) :
    Lh P c s (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R P.z) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_of_frameTab ht, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_of_frameTab ht]

def gL (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : GL (Fin n) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (Lh P c s)
  inv := LinearMap.toMatrix' (Lh P c s⁻¹)
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : Lh P c s ∘ₗ Lh P c s⁻¹ = LinearMap.id := LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      exact Lh_inv ht hs hs' v
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P := by rw [inv_inv]; exact hs
    have : Lh P c s⁻¹ ∘ₗ Lh P c s = LinearMap.id := LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      have := Lh_inv ht hs' hs'' v
      rwa [inv_inv] at this
    rw [this, LinearMap.toMatrix'_id]

theorem gL_mem (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : gL ht hs hs' ∈ HR R σ J := by
  change Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lh P c s)) * JR R J * LinearMap.toMatrix' (Lh P c s) = JR R J
  have key : ∀ x y, Formalism.UG.hform (sigR R σ)
      (Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lh P c s)) * JR R J * LinearMap.toMatrix' (Lh P c s)) x y =
      Formalism.UG.hform (sigR R σ) (JR R J) x y := by
    intro x y
    rw [← Formalism.UG.P.hform_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact Lh_unitary ht hs' x y
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  have hsg : ∀ k, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin n → R ⊗[F] E) k) =
      (Pi.single i (1 : R ⊗[F] E) : Fin n → R ⊗[F] E) k := fun k => by
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  simp only [Formalism.UG.hform, hsg] at this
  simpa [Pi.single_apply] using this

def hOf (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : HA R σ J := (⟨gL ht hs hs', gL_mem ht hs hs'⟩ : ↥(HR R σ J))

theorem lin_hOf (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (v : Fin n → R ⊗[F] E) : lin R σ J (hOf ht hs hs') v = Lh P c s v := by
  change Matrix.mulVec (LinearMap.toMatrix' (Lh P c s)) v = _
  exact LinearMap.toMatrix'_mulVec _ _

theorem hOf_mem (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : hOf ht hs hs' ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_hOf]
  induction b using Fin.addCases with
  | left i =>
    simp only [tupH, Fin.append_left]
    induction i using Fin.lastCases with
    | last => simp only [F0, Fin.snoc_last]; exact levi_fixes_anisotropic ht s
    | cast j => simp only [F0, Fin.snoc_castSucc]; exact Lh_fix_e ht s j
  | right j =>
    simp only [tupH, Fin.append_right]
    exact Lh_fix_f ht s j

theorem levi_diff (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (u : Fin n → R ⊗[F] E) (hu : InXperp R σ J P u) :
    lin R σ J s u - Lh P c s u ∈ spanR (F := F) R P.e Set.univ := by
  have hr : piRest (σ := σ) (J := J) P c u = (∑ a, hR R σ J (ratV (F := F) R (P.f a)) u • ratV (F := F) R (P.e a)) +
      (c * hR R σ J (ratV (F := F) R P.z) u) • ratV (F := F) R P.z := by
    rw [piRest_apply]
    simp [hu _]
  set xu := ∑ a, hR R σ J (ratV (F := F) R (P.f a)) u • ratV (F := F) R (P.e a)
  have hxu : xu ∈ spanR (F := F) R P.e Set.univ :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)
  set γ := c * hR R σ J (ratV (F := F) R P.z) u
  have e1 : lin R σ J s u = lin R σ J s (piW (σ := σ) (J := J) P c u) + lin R σ J s (piRest (σ := σ) (J := J) P c u) := by
    rw [← map_add (f := _), piW_add_rest]
  have e2 := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u))
  have e3 : piRest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) =
      lin R σ J s (piW (σ := σ) (J := J) P c u) - piW (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) :=
    eq_sub_of_add_eq' e2
  have key : lin R σ J s u - Lh P c s u =
      piRest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) + (lin R σ J s xu - xu) +
        γ • (lin R σ J s (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by
    rw [e3, Lh_apply, e1, hr, map_add (f := _), map_smul, smul_sub]
    abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (parabolic_maps_complement ht hs' (piW_inW ht u))
    (Submodule.sub_mem _ (parabolic_preserves_isotropic hs hxu) hxu)) (Submodule.smul_mem _ _ (parabolic_fixes_modulo_span hs))

end Pack

variable {D : D7}

theorem leviComp_holds : LeviComp := by
  intro D X w p s hs
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := FrameW.frameOf_isStd X w
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => by simp [FrameW.sig_apply]
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := (cmInst_holds X).2.1
  set T : X.B.I.F := (((D.mem w).A.T : ℕ) : X.B.I.F)
  have hne : algebraMap X.B.I.F X.B.I.E (-T) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact fun h => hT ((algebraMap X.B.I.F X.B.I.E).injective (by rw [h, map_zero]))
  set c : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E :=
    inclR (F := X.B.I.F) (Fv X.B.I.F p.1) ((algebraMap X.B.I.F X.B.I.E (-T))⁻¹)
  have ht : FrameTab (σ := X.B.I.cm.sig) (J := X.B.I.J) (frameOf X w) c T :=
    { ee := fun a b => by rw [hermForm_rational_vectors, hee, map_zero]
      ef := fun a b => by rw [hermForm_rational_vectors, hef]; split_ifs <;> simp
      fe := fun a b => by
        rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hef b a]
        split_ifs with h1 h2 h2 <;> simp_all
      ff := fun a b => by rw [hermForm_rational_vectors, hff, map_zero]
      ez := fun a => by rw [hermForm_rational_vectors, hez, map_zero]
      fz := fun a => by rw [hermForm_rational_vectors, hfz, map_zero]
      ze := fun a => by rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hez, map_zero, map_zero]
      zf := fun a => by rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hfz, map_zero, map_zero]
      zz := by rw [hermForm_rational_vectors, hzz, ← map_mul, inv_mul_cancel₀ hne, map_one]
      hσ := hσ
      hJ := hJ }
  have hs' := inv_mem hs
  exact ⟨hOf ht hs hs', hOf_mem ht hs hs', fun u hu => by rw [lin_hOf]; exact levi_diff ht hs hs' u hu⟩

theorem locLevi_of_NO (hN : UnipotentIntegralInLevel) : LocLevi := locLevi_of_comp leviComp_holds hN

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.PsiVMulVec
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix
open Classical

section Idem

variable {D : D7} (X : HidaSetting D)

def idemAf (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Af X.B.I.F :=
  RestrictedProduct.mk (fun v => if v = p then (1 : Fv X.B.I.F v) else 0)
    (Filter.Eventually.of_forall (fun v => by
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _))

theorem idemAf_int (p : HeightOneSpectrum (𝓞 X.B.I.F)) : idemAf X p ∈ Formalism.UG.intAd X.B.I.F := by
  intro v
  show (if v = p then (1 : Fv X.B.I.F v) else 0) ∈ v.adicCompletionIntegers X.B.I.F
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def idemT (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  ⟨(1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p,
    Subring.subset_closure (Or.inr ⟨⟨idemAf X p, idemAf_int X p⟩, rfl⟩)⟩

theorem psiV_idemT (p v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.psiV X.B.I v ((idemT X p : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      if v = p then 1 else 0 := by
  show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v) (AlgHom.id X.B.I.F X.B.I.E))
      ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F))
        ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p)) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v (idemAf X p) = if v = p then 1 else 0 := rfl
  rw [he]
  split_ifs
  · exact Algebra.TensorProduct.one_def.symm
  · exact TensorProduct.zero_tmul _ _

theorem fmat_psiV (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (X.B.I.fmat x).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
  change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb x) :
    GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
      (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
  rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb x, Matrix.map_map]
  rfl

theorem psiV_mulVec (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (i : Fin X.B.I.n) :
    PI.FinKW.psiV X.B.I v (((X.B.I.fmat x - 1) *ᵥ w) i) =
      ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
          PI.FinKW.vecV X.B.I v w) i := by
  rw [← fmat_psiV X hb x v]
  have h := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat x - 1) w i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext a b
  simp [Matrix.sub_apply, Matrix.one_apply]

end Idem

theorem level_congruence_typed_places : LevelCongruenceTypedPlaces := by
  intro D X hb hK hL κ hκ hO hloc
  classical
  choose κ' hκ' heq using hloc
  have decomp : ∀ w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (X.B.I.fmat κ - 1) *ᵥ w = ∑ p : TypX X, idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w) := by
    intro w
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective X.B.I
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, psiV_mulVec X hb κ v w i, Finset.sum_apply, map_sum]
    simp only [Pi.smul_apply]
    have hs : ∀ p : TypX X, PI.FinKW.psiV X.B.I v ((idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) i) =
        (if v = p.1 then 1 else 0) * ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb (κ' p))) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v w) i := by
      intro p
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, psiV_idemT, psiV_mulVec X hb (κ' p) v w i]
    simp only [Pi.smul_apply] at hs
    rw [Finset.sum_congr rfl (fun p _ => hs p)]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · rw [Finset.sum_eq_single (⟨v, hv⟩ : TypX X)]
      · rw [if_pos rfl, one_mul, ← heq ⟨v, hv⟩, sub_self]
      · intro p _ hp
        rw [if_neg (fun h => hp (Subtype.ext h.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero (fun p _ => by rw [if_neg (fun h => hv (by rw [h]; exact p.2)), zero_mul])]
      rw [hO v hv]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec, Pi.zero_apply, sub_zero]
  have hmem : ∀ (S : Set (Formalism.L2.SG.HidaSetting.VA X.B.I)) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ p : TypX X, InMod X.B.I X.B.g S ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) →
        InMod X.B.I X.B.g S ((X.B.I.fmat κ - 1) *ᵥ w) := by
    intro S w h
    unfold InMod at h ⊢
    rw [decomp w]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (h p))
  refine ⟨hκ, ?_, ?_, ?_⟩
  · exact fun a => hmem _ _ (fun p => (hκ' p).2.1 a)
  · exact hmem _ _ (fun p => (hκ' p).2.2.1)
  · exact fun i => hmem _ _ (fun p => (hκ' p).2.2.2 i)

theorem globProd_holds : GlobProd := globProd_of_k2LocT level_congruence_typed_places

end MassDataLevelSSteps
end
end

