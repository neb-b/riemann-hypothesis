module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompact
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem exists_conjInv_root (hCM : IsCMExt F E σ) (m : Fin r) :
    ∃ j, cxRoots τ.1 P j = (conj (cxRoots τ.1 P m))⁻¹ := by
  let φ : Fld P →+* ℂ := (starRingEnd ℂ).comp ((psiL P τ m).comp (star' P : Fld P →+* Fld P))
  have hE : φ.comp (algebraMap E (Fld P)) = τ.1 := by
    ext e
    change conj (psiL P τ m (star' P (algebraMap E (Fld P) e))) = τ.1 e
    rw [star'_algebraMap, psiL_algebraMap, hCM.2.2.2 τ.1 e]
    simp
  have hα : φ (alpha P) = (conj (cxRoots τ.1 P m))⁻¹ := by
    change conj (psiL P τ m (star' P (alpha P))) = _
    rw [star'_alpha, map_inv₀, psiL_alpha, map_inv₀]
  have h0 := congrArg φ (eval_alpha P)
  rw [hom_eval₂, hE, hα, map_zero, ← eval_map, cxRoots_spec, eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  refine ⟨j, ?_⟩
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  exact hj.symm

end GlobalTheory.TrEll.RealTorus


open GlobalTheory.TrEll.RealTorus in
theorem GlobalTheory.TrEll.realTorus_norm_cxRoots : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hB hK i
  have hw : w.IsReal := by haveI := hCM.1; exact IsTotallyReal.isReal w
  obtain ⟨π, hπ⟩ : ∃ π : Fin r → Fin r, ∀ m, cxRoots τ.1 P (π m) = (conj (cxRoots τ.1 P m))⁻¹ :=
    ⟨fun m => (exists_conjInv_root P τ hCM m).choose, fun m => (exists_conjInv_root P τ hCM m).choose_spec⟩
  have hinv : ∀ m, π (π m) = m := fun m =>
    cxRoots_injective P τ (by rw [hπ, hπ, map_inv₀, Complex.conj_conj, inv_inv])
  have hpsi : ∀ m, (psiL P τ m).comp (star' P : Fld P →+* Fld P) = (starRingEnd ℂ).comp (psiL P τ (π m)) := by
    intro m
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change psiL P τ m (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ (π m) (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · change psiL P τ m (star' P (alpha P)) = conj (psiL P τ (π m) (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha, psiL_alpha, hπ, map_inv₀, Complex.conj_conj]
  have hsig : ∀ m y, Psi P τ m (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y) = conj (Psi P τ (π m) y) := by
    intro m y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a l =>
      change Psi P τ m (a ⊗ₜ[F] star' P l) = _
      rw [Psi_tmul, Psi_tmul, map_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a,
        Complex.conj_ofReal]
      exact congrArg _ (RingHom.congr_fun (hpsi m) l)
  have h0 : cxRoots τ.1 P i ≠ 0 := by
    rw [← psiL_alpha P τ i]; exact (_root_.map_ne_zero _).2 (alpha_ne_zero P)
  suffices hfix : π i = i by
    have e := hπ i
    rw [hfix] at e
    have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
      nth_rw 1 [e]
      exact inv_mul_cancel₀ ((_root_.map_ne_zero _).2 h0)
    rw [Complex.mul_conj, ← Complex.sq_norm] at h1
    have h2 : ‖cxRoots τ.1 P i‖ ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [norm_nonneg (cxRoots τ.1 P i)]

  by_contra hji

  have hcont : Continuous (fun g : Tor P w.Completion => ‖Psi P τ i (g.1.1 0 0)‖) := by
    letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
    haveI : ContinuousSMul w.Completion ℂ :=
      continuousSMul_of_algebraMap _ _ (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] Fld P) := ⟨rfl⟩
    let L : w.Completion ⊗[F] Fld P →ₗ[w.Completion] ℂ :=
      { toFun := Psi P τ i
        map_add' := map_add _
        map_smul' := by
          intro c y
          have : c • y = (c ⊗ₜ[F] (1 : Fld P)) * y := by
            rw [Algebra.smul_def]; rfl
          rw [this, map_mul, Psi_tmul, map_one, mul_one]; rfl }
    have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
    have hv : Continuous (fun g : Tor P w.Completion => (g.1.1 : Matrix (Fin 1) (Fin 1) (w.Completion ⊗[F] Fld P))) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_norm.comp (hL.comp (hv.matrix_elem 0 0))
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  obtain ⟨j, hj⟩ : ∃ j, π i = j := ⟨_, rfl⟩
  have hji' : j ≠ i := by rw [← hj]; exact hji
  have hπj : π j = i := by rw [← hj]; exact hinv i
  have hne : ∀ m, m ≠ j → π m ≠ i := fun m hm h => hm (by have := hinv m; rw [h, hj] at this; exact this.symm)
  have hne' : ∀ m, m ≠ i → π m ≠ j := fun m hm h => hm (by have := hinv m; rw [h, hπj] at this; exact this.symm)
  set t : ℝ := max M 0 + 1 with ht
  have ht0 : 0 < t := by positivity
  let v : Fin r → ℂ := fun m => if m = i then (t : ℂ) else if m = j then (t : ℂ)⁻¹ else 1
  obtain ⟨y, hy⟩ := hB.2 v
  have hyv : ∀ m, Psi P τ m y = v m := fun m => congrFun hy m
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y * y = 1 := by
    apply hB.1
    funext m
    rw [map_mul, map_one, Pi.mul_apply, PsiAll_apply, PsiAll_apply, hsig, hyv, hyv, Pi.one_apply]
    by_cases hmi : m = i
    · rw [hmi, hj]
      simp [v, hji', htc]
    · by_cases hmj : m = j
      · rw [hmj, hπj]
        simp [v, hji', htc]
      · simp [v, hmi, hmj, hne m hmj, hne' m hmi]
  let u : (w.Completion ⊗[F] Fld P)ˣ := ⟨y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y, by rw [mul_comm]; exact hyy, hyy⟩
  let g : Tor P w.Completion := ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext a b
    simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0, JR, inclR, u, ← Algebra.TensorProduct.one_def, hyy]⟩
  have hg : ‖Psi P τ i (g.1.1 0 0)‖ = t := by
    have : g.1.1 0 0 = y := by simp [g, u]
    rw [this, hyv]
    simp [v, abs_of_pos ht0]
  have hle : ‖Psi P τ i (g.1.1 0 0)‖ ≤ M := hM ⟨g, rfl⟩
  rw [hg] at hle
  have : M < t := by rw [ht]; linarith [le_max_left M 0]
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoDim

theorem finrank_perp_add {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E)
    (W : Submodule E V.V) :
    Module.finrank E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) + Module.finrank E W = V.rank := by
  classical
  set a := Module.finrank E W
  let b := Module.finBasis E W
  let ψ : V.V →ₗ[E] (Fin a → E) := LinearMap.pi fun i => V.hT (b i : V.V)
  have hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W := by
    ext y
    simp only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]
    constructor
    · intro h w hw
      have e := congrArg (fun v : Fin a → E => v) h
      have hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i := (b.sum_repr _).symm
      have : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := congrFun h i
      simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro h
      funext i
      simpa [ψ] using h (b i) (b i).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    let c : Fin a → E := fun i => f (Pi.single i 1)
    have hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [smul_eq_mul, c]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0 := by
      intro y
      have h1 : f (ψ y) = 0 := by
        have : f (ψ y) ∈ (LinearMap.range ψ).map f := ⟨ψ y, ⟨y, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot E).1 this
      rw [hfc] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      simp [ψ, mul_comm]
    have hx := V.nondeg.1 _ hy
    have hli : LinearIndependent E (fun i => (b i : V.V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hc : ∀ i, star (c i) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx
      exact this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfc]
    simp [fun i => star_eq_zero.1 (hc i)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq] at hrn
  omega

end GlobalTheory.IsoDim

theorem GlobalTheory.IsoDim.isotropic_dim_bounds : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  intro D V hodd W hW
  have h := GlobalTheory.IsoDim.finrank_perp_add V W
  have hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) :=
    Submodule.finrank_mono hW.2
  have hpos : 0 < Module.finrank D.host.E W :=
    Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hpos, ?_⟩
  omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerate
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

theorem gramOne_herm_nd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  intro F E _ _ _ _ _ σ hcm r P
  have hσ : ∀ e, σ (σ e) = e := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hs := star'_star'_of_invol hσ P
  have htr := trace_star'_eq F E σ hσ r P
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [gramOne, Matrix.of_apply]
    rw [← htr, map_mul, hs, mul_comm]
  · intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hw0
    set b := powB P
    set z : Fld P := ∑ j, w j • b j with hz
    have h1 : ∀ i, Algebra.trace E (Fld P) (z * star' P (b i)) = 0 := by
      intro i
      have := congr_fun hw i
      simp only [Matrix.mulVec, dotProduct, gramOne, Matrix.of_apply, Pi.zero_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hz, Finset.sum_mul, map_sum]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
    have h2 : ∀ u : Fld P, Algebra.trace E (Fld P) (z * u) = 0 := by
      intro u
      have hu : u = ∑ i, σ (b.repr (star' P u) i) • star' P (b i) := by
        conv_lhs => rw [← hs u, ← b.sum_repr (star' P u)]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, star'_algebraMap]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hu, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mul_smul_comm, map_smul, h1, smul_zero]
    have hz0 : z = 0 := (traceForm_nondegenerate E (Fld P)).1 z fun u => by
      rw [Algebra.traceForm_apply]; exact h2 u
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent w (by rw [← hz0]) j

end GlobalTheory.TrUnitLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TestConstTerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}


open Classical in
theorem tensor_eq_mul_update {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ} (hf : IsFinFamily σ J L ff)
    (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) :
    tensor σ J fa ff g = ff v (proj σ J v g) * tensor σ J fa (Function.update ff v fun _ => 1) g := by
  have h1 : (Function.mulSupport fun u => ff u (proj σ J u g)).Finite := by
    simpa only [projFinLoc_projFin] using hf.finite_mulSupport (projFin σ J g)
  have h2 : (Function.mulSupport fun u => (Function.update ff v fun _ => 1) u (proj σ J u g)).Finite :=
    h1.subset fun u hu => by
      by_cases e : u = v
      · subst e; simp at hu
      · simpa [Function.update_of_ne e] using hu
  simp only [tensor]
  rw [← mul_finprod_cond_ne v h1, ← mul_finprod_cond_ne v h2]
  simp only [Function.update_self, one_mul]
  have : (∏ᶠ (i) (_ : i ≠ v), (Function.update ff v fun _ => 1) i (proj σ J i g)) =
      ∏ᶠ (i) (_ : i ≠ v), ff i (proj σ J i g) :=
    finprod_congr fun i => finprod_congr fun hi => by rw [Function.update_of_ne hi]
  rw [this]; ring


open Classical in
theorem tensor_update_mul_emb (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : GAd σ J) (h : GLoc σ J v) :
    tensor σ J fa (Function.update ff v fun _ => 1) (a * emb σ J v h * b) =
      tensor σ J fa (Function.update ff v fun _ => 1) (a * b) := by
  simp only [tensor]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp only [map_mul, projArch_emb, mul_one]
  · refine finprod_congr fun u => ?_
    by_cases e : u = v
    · subst e; simp only [Function.update_self]
    · simp only [map_mul, proj_emb_ne σ J e, mul_one]

end GlobalTheory.TestConstTerm

namespace GlobalTheory.TestConstTerm

variable {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (v : HeightOneSpectrum (𝓞 D.host.F))

def locIn : Subgroup (NA 𝔉) := (emb D.sp.cm.sig V.gram v).range.subgroupOf (NA 𝔉)

theorem isClosed_locIn : IsClosed (locIn 𝔉 v : Set (NA 𝔉)) := by
  have : (locIn 𝔉 v : Set (NA 𝔉)) = Subtype.val ⁻¹' Set.range (emb D.sp.cm.sig V.gram v) := by
    ext u; simp [locIn, Subgroup.mem_subgroupOf]
  rw [this]
  exact (isClosedEmbedding_emb D.sp.cm.sig V.gram v).isClosed_range.preimage continuous_subtype_val

theorem emb_proj_of_mem_locIn {u : NA 𝔉} (hu : u ∈ locIn 𝔉 v) :
    emb D.sp.cm.sig V.gram v (proj D.sp.cm.sig V.gram v u) = u := by
  obtain ⟨h, hh⟩ := Subgroup.mem_subgroupOf.1 hu
  rw [← hh, proj_emb_self]

def locInEquiv : locIn 𝔉 v ≃ₜ* NLoc 𝔉 v where
  toFun u := ⟨proj D.sp.cm.sig V.gram v u.1.1, IsoFlag.mapH_mem_unip _ u.1.2⟩
  invFun h := ⟨⟨emb D.sp.cm.sig V.gram v h, IsoFlag.emb_mem_unip.2 h.2⟩, Subgroup.mem_subgroupOf.2 ⟨h, rfl⟩⟩
  left_inv u := Subtype.ext (Subtype.ext (emb_proj_of_mem_locIn 𝔉 v u.2))
  right_inv h := Subtype.ext (proj_emb_self D.sp.cm.sig V.gram v (h : GLoc D.sp.cm.sig V.gram v))
  map_mul' a b := Subtype.ext (map_mul (proj D.sp.cm.sig V.gram v) _ _)
  continuous_toFun := ((continuous_proj D.sp.cm.sig V.gram v).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (((continuous_emb D.sp.cm.sig V.gram v).comp continuous_subtype_val).subtype_mk _).subtype_mk _

end GlobalTheory.TestConstTerm

namespace GlobalTheory.TestConstTerm

local instance {D : D7} (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) :=
  SelfDual.isLattice_frameLat V

open Classical in
theorem unipIntegralsVanish_tensor : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) →
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    (∀ (ν : Measure (NLoc 𝔉 v)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v),
      ∫ n : NLoc 𝔉 v, ff v (x * n * y) ∂ν = 0) →
    UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := by
  intro D V 𝔉 fa ff ha hf v hv ν _ x y
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc := continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)
  let φ : GAd D.sp.cm.sig V.gram ≃ₜ GAd D.sp.cm.sig V.gram := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
  have hcont : Continuous fun n : NA 𝔉 => f (x * n * y) :=
    hcc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hsupp : HasCompactSupport fun n : NA 𝔉 => f (x * n * y) :=
    (hcc.2.comp_homeomorph φ).comp_isClosedEmbedding
      (IsoFlag.isClosed_unip 𝔉 D.sp.cm _).isClosedEmbedding_subtypeVal
  refine ⟨hcont.integrable_of_hasCompactSupport hsupp, ?_⟩
  haveI : LocallyCompactSpace (locIn 𝔉 v) := (isClosed_locIn 𝔉 v).locallyCompactSpace
  have key : ∀ g : NA 𝔉, ∫ u : locIn 𝔉 v, f (x * ((u : NA 𝔉) * g : NA 𝔉) * y) ∂(Measure.haar) = 0 := by
    intro g
    have e1 : ∀ u : locIn 𝔉 v, f (x * ((u : NA 𝔉) * g : NA 𝔉) * y) =
        ff v (proj D.sp.cm.sig V.gram v x * (locInEquiv 𝔉 v u : GLoc D.sp.cm.sig V.gram v) *
          proj D.sp.cm.sig V.gram v ((g : GAd D.sp.cm.sig V.gram) * y)) *
        tensor D.sp.cm.sig V.gram fa (Function.update ff v fun _ => 1) (x * ((g : GAd D.sp.cm.sig V.gram) * y)) := by
      intro u
      rw [hfdef, tensor_eq_mul_update hf v]
      have hu := emb_proj_of_mem_locIn 𝔉 v u.2
      congr 1
      · simp only [Subgroup.coe_mul, map_mul, mul_assoc]; rfl
      · rw [Subgroup.coe_mul, ← hu, show ∀ a b c d : GAd D.sp.cm.sig V.gram, a * (b * c) * d = a * b * (c * d)
          from fun a b c d => by group, tensor_update_mul_emb]
    simp_rw [e1]
    rw [integral_mul_const]
    have hH : (Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v))).IsHaarMeasure :=
      ContinuousMulEquiv.isHaarMeasure_map _ _
    have := @hv (Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v))) hH (proj D.sp.cm.sig V.gram v x) (proj D.sp.cm.sig V.gram v ((g : GAd D.sp.cm.sig V.gram) * y))
    rw [show Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v)) =
      Measure.map ((locInEquiv 𝔉 v).toHomeomorph.toMeasurableEquiv) Measure.haar from rfl,
      integral_map_equiv] at this
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    exact this
  have := _root_.GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero (NA 𝔉) (locIn 𝔉 v) (isClosed_locIn 𝔉 v) Measure.haar ν (fun n => f (x * n * y)) (fun _ => 1)
    hcont hsupp (locallyIntegrable_const 1) (fun _ _ => Filter.EventuallyEq.rfl) key
  simpa using this

end GlobalTheory.TestConstTerm
end
end

