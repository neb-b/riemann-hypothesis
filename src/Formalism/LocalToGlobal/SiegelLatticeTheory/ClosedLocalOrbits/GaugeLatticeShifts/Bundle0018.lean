module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfI
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cof

variable {D : D7}

theorem GZ_apply (u v : Fin (D.R.rS + 1) → (VS D).V) (a b : Fin (D.R.rS + 1)) :
    GZ u v a b = (VS D).hT (u a) (v b) := rfl

theorem GDl_top' (u v : Fin (D.R.rS + 1) → (VS D).V) : GDl u v (D.R.rS + 1) = (GZ u v).det := by
  unfold GDl
  rw [dite_eq_left le_rfl]
  congr 1

theorem GDl_r' (u v : Fin (D.R.rS + 1) → (VS D).V) :
    GDl u v D.R.rS = ((GZ u v).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold GDl
  rw [dite_eq_left (Nat.le_succ _)]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]

theorem om'_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (a : Fin (D.R.rS + 1)) :
    (VS D).hT (u a) (Gom' u v) = if a = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.mul_adjugate (GZ u v)) a) (Fin.last _)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [show (∑ b, (GZ u v).adjugate b (Fin.last _) * (VS D).hT (u a) (v b)) =
      ∑ b, GZ u v a b * (GZ u v).adjugate b (Fin.last _) from
    Finset.sum_congr rfl fun b _ => by rw [GZ_apply, mul_comm], key]
  split_ifs <;> simp

theorem om'_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom' u v - GDl u v D.R.rS • v (Fin.last _) ∈ Xs (S := VS D) v := by
  unfold Gom'
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [show (∑ a, (GZ u v).adjugate (Fin.last _) a * (VS D).hT (u a) (v b)) =
      ∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b from rfl, key]
  rcases eq_or_ne b (Fin.last _) with hb | hb
  · subst hb
    simp
  · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]

theorem om_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom u v - star (GDl u v D.R.rS) • u (Fin.last _) ∈ Xs (S := VS D) u := by
  unfold Gom
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem lemB (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range v)) (h : ∀ a, (VS D).hT (u a) q = 0) : q = 0 := by
  obtain ⟨π, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.mulVec (GZ u v) π = 0 := by
    funext a
    have := h a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, GZ_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [GDl_top'] at hdet
  have hπ := Matrix.eq_zero_of_mulVec_eq_zero hdet hm
  simp [hπ]

theorem eq_zero_of_orth_of_det_ne_zero (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range u)) (h : ∀ b, (VS D).hT q (v b) = 0) : q = 0 := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.vecMul (fun a => star (κ a)) (GZ u v) = 0 := by
    funext b
    have := h b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, GZ_apply]
    exact this
  rw [GDl_top'] at hdet
  have hκ := Matrix.eq_zero_of_vecMul_eq_zero hdet hm
  have : κ = 0 := by
    funext a
    have := congrFun hκ a
    simpa using this
  simp [this]

theorem lemC (v : Fin (D.R.rS + 1) → (VS D).V) (hv : LinearIndependent D.host.E v) {c : D.host.E}
    (h : c • v (Fin.last _) ∈ Xs (S := VS D) v) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have h0 : ∑ i, (Fin.snoc (α := fun _ => D.host.E) d (-c) i) • v i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_smul]
    rw [hd, add_neg_cancel]
  have := Fintype.linearIndependent_iff.1 hv _ h0 (Fin.last _)
  simpa using this

end Cof

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} (ε : Fin n → Bool)

structure Frm (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0
  pp : ∀ a b, hJ ε (p a) (p b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  pz : ∀ a, hJ ε (p a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ew : ∀ a j, hJ ε (e a) (w j) = 0
  pw : ∀ a j, hJ ε (p a) (w j) = 0
  zw : ∀ j, hJ ε z (w j) = 0
  ww : ∀ i j, hJ ε (w i) (w j) = if i = j then 1 else 0
  T_ne : T ≠ 0

variable {ε}

theorem hJ_swap0 {x y : Fin n → ℂ} (h : hJ ε x y = 0) : hJ ε y x = 0 := by
  rw [UnitaryIsometries.hJ_conj, h, map_zero]

theorem hJ_swapδ {ι : Type*} [DecidableEq ι] {x y : ι → Fin n → ℂ} (h : ∀ a b, hJ ε (x a) (y b) = if a = b then 1 else 0)
    (a b : ι) : hJ ε (y b) (x a) = if a = b then 1 else 0 := by
  rw [UnitaryIsometries.hJ_conj, h]
  split_ifs <;> simp

def syn (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ)
    (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) : Fin n → ℂ :=
  ∑ a, α a • e a + ∑ a, β a • p a + (-γ / (T : ℂ)) • z + ∑ j, δ j • w j

section Coord

variable {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ} {T : ℝ}

theorem hJ_syn (x : Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε x (syn e p z w T α β γ δ) = ∑ a, α a * hJ ε x (e a) + ∑ a, β a * hJ ε x (p a) +
      (-γ / (T : ℂ)) * hJ ε x z + ∑ j, δ j * hJ ε x (w j) := by
  simp only [syn, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_sum_right]

theorem syn_p (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (p c) (syn e p z w T α β γ δ) = α c := by
  rw [hJ_syn]
  simp [hJ_swapδ F.ep, F.pp, F.pz, F.pw]

theorem syn_e (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (e c) (syn e p z w T α β γ δ) = β c := by
  rw [hJ_syn]
  simp [F.ee, F.ep, F.ez, F.ew]

theorem synthesized_vector_z_pairing (F : Frm ε e p z w T) α β γ δ : hJ ε z (syn e p z w T α β γ δ) = γ := by
  rw [hJ_syn]
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F.T_ne
  simp only [fun a => hJ_swap0 (F.ez a), fun a => hJ_swap0 (F.pz a), F.zz, F.zw, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  field_simp

theorem syn_w (F : Frm ε e p z w T) (c : Fin k) α β γ δ : hJ ε (w c) (syn e p z w T α β γ δ) = δ c := by
  rw [hJ_syn]
  simp [fun a => hJ_swap0 (F.ew a c), fun a => hJ_swap0 (F.pw a c), hJ_swap0 (F.zw c), F.ww]

def crd (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ) :=
  (LinearMap.pi fun a => hJL ε (p a)).prod ((LinearMap.pi fun a => hJL ε (e a)).prod
    ((hJL ε z).prod (LinearMap.pi fun j => hJL ε (w j))))

theorem crd_syn (F : Frm ε e p z w T) α β γ δ :
    crd (ε := ε) e p z w (syn e p z w T α β γ δ) = (α, β, γ, δ) := by
  ext c
  · exact syn_p F c α β γ δ
  · exact syn_e F c α β γ δ
  · exact synthesized_vector_z_pairing F α β γ δ
  · exact syn_w F c α β γ δ

theorem recon (F : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) (v : Fin n → ℂ) :
    v = syn e p z w T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  have hsurj : Function.Surjective (crd (ε := ε) e p z w) := fun c =>
    ⟨syn e p z w T c.1 c.2.1 c.2.2.1 c.2.2.2, crd_syn F _ _ _ _⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  apply hinj
  rw [crd_syn F]
  rfl

end Coord

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceEqSumPlaces
section
noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then (starRingEnd ℂ).comp (φ p.1) else φ p.1

theorem embOf_injective [IsTotallyReal F] [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : Function.Injective (embOf φ) := by
  have hre : ∀ (v : InfinitePlace F) (a : F), starRingEnd ℂ (v.embedding a) = v.embedding a := by
    intro v a
    have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal v))
    exact RingHom.congr_fun h a
  have hres : ∀ p : InfinitePlace F × Bool, (embOf φ p).comp (algebraMap F E) = p.1.embedding := by
    rintro ⟨v, b⟩
    ext a
    cases b <;> simp [embOf, hφ, hre]
  have hnr : ∀ v, (starRingEnd ℂ).comp (φ v) ≠ φ v := by
    intro v h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk (φ v))
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc (RingHom.ext fun x => RingHom.congr_fun h x)
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have hv : v = v' := by
    have := congrArg (fun σ => σ.comp (algebraMap F E)) h
    simp only [hres] at this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', this]
  subst hv
  cases b <;> cases b' <;> simp [embOf] at h ⊢
  · exact hnr v h.symm
  · exact hnr v h

theorem embOf_bijective [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    Function.Bijective (embOf φ) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embOf_injective φ hφ, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bool, Embeddings.card E ℂ,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← Module.finrank_mul_finrank ℚ F E, h2]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [h]

theorem trace_eq_sum_places [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ v, (φ v x + starRingEnd ℂ (φ v x)) := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ∑ τ : E →ₐ[ℚ] ℂ, τ x := trace_eq_sum_embeddings ℂ
  have h3 : ∑ σ : E →+* ℂ, σ x = ∑ τ : E →ₐ[ℚ] ℂ, τ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun τ => τ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h4 : ∑ p : InfinitePlace F × Bool, embOf φ p x = ∑ σ : E →+* ℂ, σ x :=
    (embOf_bijective h2 φ hφ).sum_comp (fun σ => σ x)
  rw [show ((Algebra.trace ℚ E x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E x) from rfl, h1, ← h3, ← h4,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [embOf, add_comm]

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TraceSum_holds : Formalism.L2.SG.RealObj.RootCoordinateFrames.TraceSum := by
  intro D X g x
  have : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  have : IsTotallyComplex X.B.I.E := X.B.I.cm.cmUnram.1
  have htr : ((Algebra.trace ℚ D.host.E (X.ιE x) : ℚ) : ℂ) = ((Algebra.trace ℚ X.B.I.E x : ℚ) : ℂ) := by
    rw [show X.ιE x = X.ιE.toRatAlgEquiv x from rfl, Algebra.trace_eq_of_algEquiv]
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [htr, trace_eq_sum_places X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over x, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_div]
  rfl

end Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums
end
end

