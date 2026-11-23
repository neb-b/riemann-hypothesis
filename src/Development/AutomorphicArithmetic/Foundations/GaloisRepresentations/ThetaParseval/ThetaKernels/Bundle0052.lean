module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLatA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0048
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutLatA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
namespace AutLatA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
theorem sgsg_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem mem_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ :=
  ⟨fun h => (hR y).2 fun M' hM' => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C y M').1 ((hA _).1 h _ (finRatF_mem_of hM')),
    finRatF_mem_of⟩
theorem sdQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ) : SelfDual (gamQF σ JS JT ξ₀ B.ψ) Λ := fun x =>
  (hR x).trans (forall₂_congr fun y _ => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C x y).symm)
theorem norm_emb_eq_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (φ : E →+* ℂ) (x : E) :
    ∃ v : InfinitePlace F, ‖φ x‖ = ‖tauB B v x‖ := by
  have hcm := hB.cm
  let ρ : F →+* ℂ := φ.comp (algebraMap F E)
  refine ⟨InfinitePlace.mk ρ, ?_⟩
  have hρ : ComplexEmbedding.IsReal ρ := by
    have := hcm.1.isReal (InfinitePlace.mk ρ)
    rwa [InfinitePlace.isReal_mk_iff] at this
  have he : (InfinitePlace.mk ρ).embedding = ρ := by
    rcases InfinitePlace.embedding_mk_eq ρ with h | h
    · exact h
    · rw [h]; exact hρ
  have hτ : (tauB B (InfinitePlace.mk ρ)).comp (algebraMap F E) = ρ := by
    exact (B.emb (InfinitePlace.mk ρ)).2.trans he
  obtain ⟨c, hc⟩ := PI.OmLocU.Red.fix_range σ hcm (y := x * σ x) (by rw [map_mul, _root_.PositivityTheory.ThKW.AutLatA.sgsg_k hB, mul_comm])
  have key : ∀ τ : E →+* ℂ, τ.comp (algebraMap F E) = ρ → Complex.normSq (τ x) = ρ c := fun τ hτ => by
    rw [← hτ, RingHom.comp_apply, hc, map_mul, hcm.2.2.2 τ]
    exact (Complex.mul_conj (τ x)).symm
  have h2 := (key φ rfl).trans (key _ hτ).symm
  rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
theorem finLat_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite := by
  obtain ⟨d, hd, hdi⟩ := exists_denomM hG.fg
  have hS := GlobalTheory.CompletedLatticeFinite.finite_of_denom d hd R
  refine (Set.Finite.pi fun _ : Fin nT => Set.Finite.pi fun _ : Fin nS => hS).subset ?_
  rintro y ⟨hy, hR⟩ i - j -
  refine ⟨hdi y hy i j, fun φ => ?_⟩
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.ThKW.AutLatA.norm_emb_eq_k hB φ (y i j)
  rw [hv]
  exact (norm_le_pi_norm (infRatF (tauB B) y) ((i, j), v)).trans hR
theorem isHeisQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (hw : w + sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamQF σ JS JT ξ₀ B.ψ) fun x => opFF hc w (finRatF F x) := by
  have H := isHeis_opFF (_root_.PositivityTheory.ThKW.AutLatA.sgsg_k C.good) C.hS C.hT C.hξ hc hw
  have e : ∀ x y, gamQF σ JS JT ξ₀ B.ψ x y = gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add (f := _), H.add_left],
    fun x y z => by rw [e, e, e, map_add (f := _), H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add (f := _)]⟩
theorem idx_eq_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      Λ.toAddSubgroup.relIndex (Λ.toAddSubgroup.comap (GlobalTheory.RatAut.sandw b a).toAddMonoidHom) := by
  have hmem := _root_.PositivityTheory.ThKW.AutLatA.mem_iff_k C hR hO.sd
  have hfin := hO.fin (g⁻¹, h⁻¹)
  have hmov : ∀ u ∈ latF F E nS nT Λ,
      idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u ∈
        (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := fun u hu => by
    rw [mem_map_rho, map_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem (latF F E nS nT Λ).toAddSubgroup (Submodule.mem_map_of_mem hu)
  rw [GlobalTheory.FinWeil.idx, ← GlobalTheory.RatLattice.relIndex_comap_comap (finRatF F (E := E) (nS := nS) (nT := nT)).toAddMonoidHom]
  · congr 1
    · ext x; exact hmem x
    · ext x
      show finRatF F x ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) ↔ b * x * a ∈ Λ
      rw [mem_map_rho, rhoFF_finRatF ha hb, hmem]
  · intro z hz
    have hN := Nat.pos_of_ne_zero hfin
    obtain ⟨γ, hγ⟩ := lat_approx hG _ (incAF F E ((idx (latF F E nS nT Λ)
      ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) : ℕ) : E)⁻¹ • z).fin
    obtain ⟨u, hu, e⟩ : ∃ u ∈ latF F E nS nT Λ, z = finRatF F (idx (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ) +
        idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u :=
      ⟨_, hγ, by rw [map_nsmul, ← nsmul_add, add_sub_cancel, nsmul_inv_smul' (F := F) (E := E) hN]⟩
    refine ⟨idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ, ?_, ?_⟩
    · show finRatF F _ ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hz (hmov u hu)
    · show z - finRatF F _ ∈ latF F E nS nT Λ
      rw [sub_eq_of_eq_add' e]
      exact nsmul_mem hu _
open GlobalTheory.RatAut in
theorem data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  have sd := _root_.PositivityTheory.ThKW.AutLatA.sdQ_k C hR
  obtain ⟨d, hd0, hdi⟩ := exists_denomM hG.fg
  have fg : Λ.toAddSubgroup.FG := GlobalTheory.RatLattice.fg_of_denom _ d hd0 hdi
  have full := hG.den
  rw [_root_.PositivityTheory.ThKW.AutLatA.idx_eq_k C hG hR hO ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := Λ.toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    suffices h : ∀ z : A, (∏ y ∈ s, k (sandw b a y)) • sandw b a z.1 ∈ A by
      exact h ⟨x, hx⟩
    intro z
    have hz : z ∈ AddSubsemigroup.closure (s : Set A) := by rw [hs]; trivial
    induction hz using AddSubsemigroup.closure_induction with
    | mem z hz =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y : A => k (sandw b a y)) (show z ∈ s from hz)
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | add x y _ _ hx hy =>
      change (∏ y ∈ s, k (sandw b a y)) • sandw b a (x.1 + y.1) ∈ A
      rw [map_add, smul_add]
      exact add_mem hx hy
  have i1 := _root_.GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := _root_.GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (_root_.PositivityTheory.ThKW.AutLatA.isHeisQ_k C hc hO.hw) hO.good sd ((sandw b a).restrictScalars (𝓞 E))
    (fun x y => by
      show gamFF σ JS JT ξ₀ B.ψ (finRatF F (b * x * a)) (finRatF F (b * y * a)) =
        gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y)
      rw [← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb]
      unfold gamFF
      rw [coe_rhoFF, coe_rhoFF, _root_.PositivityTheory.ThKW.symplOF_actOF_k C]) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩
end AutLatA
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutRealA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem exists_inf_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  have hB := C.good
  have hc : IsCharAF F B.ψ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).1
  have hθ := C.inf
  have hι := C.chart
  have hS := C.hS
  have hT := C.hT
  have hξ := C.h0
  have hξσ := C.hξ
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ
  have hHeis : IsHeis (fun x y => (star y ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => norm_rhoBF hc _ f, fun f => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι 0) f = f
      rw [iotaVF_zero, rhoBF_zero]
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) f) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι (u + v)) f
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hι)
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    _root_.GlobalTheory.RealWeil.UnitaryOsc.exists_osc (IxF F nS nT) (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)) hH.1 hH.2
      (BBF σ JS JT ξ₀ B.ψ) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hHeis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
      (_root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι)
  have sm := _root_.GlobalTheory.T.archimedean_chart_gaussian_norm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc
  have hfr := _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀
  have rcomm : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) =
        rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, (hfr u _ hu (real_iotaVF hι v)).2, add_comm]
  have radd : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc (u + iotaVF ι v) f = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, AddChar.map_zero_eq_one, one_smul]
  have hfin : ∀ p {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ f : BBF σ JS JT ξ₀ B.ψ,
      Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) f → Ω p (rhoBF σ JS JT ξ₀ B.ψ hc u f) = rhoBF σ JS JT ξ₀ B.ψ hc u (Ω p f) :=
    fun p u hu f hf => hcomm p _ (fun v g => rcomm hu v g) f hf
  have hth : ∀ p (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 → IsThetaFunOF σ JS JT ξ₀ B.ψ (Ω p f).1 := by
    intro p f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc _ (hsm p f (sm f hf)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoBF σ JS JT ξ₀ B.ψ hc u f = f := QB_ext fun x => congrFun ((coe_rhoBF hc u f).trans (hl u hu h0)) x
    rw [← coe_rhoBF hc, ← hfin p h0 f (sm f hf), e]
  have hbd := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hc
  obtain ⟨om, hom⟩ := exists_homF hbd Ω hth (fun p f f' h1 h2 => hadd p f f' (sm f h1) (sm f' h2))
    (fun p a f h1 => hsmul p a f (sm f h1)) (fun f h1 => hone f (sm f h1)) fun p p' f h1 => hmul p p' f (sm f h1)
  have lift : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ G : BBF σ JS JT ξ₀ B.ψ, (G.1 : WOF F E nS nT → ℂ) = f :=
    fun f hf => ⟨toBF f hf.cont (hbd f hf) hf.quasi, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_⟩, fun s hs hpos p hsc f hf hv => ?_⟩ <;> obtain ⟨G, rfl⟩ := lift f hf
  · rw [hom p G hf]
    exact hth p G hf
  · simp only [hom _ G hf]
    exact (ev _ _ w).continuous.comp
      (hcont (_root_.GlobalTheory.T.continuous_moment_map F E σ B hB nS nT JS JT θ hθ) G (sm G hf))
  · rw [hom p G hf]
    exact _root_.GlobalTheory.RealWeilF.lintegral_eq_of_normsF F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 _ _
      fun H _ _ _ Φ hΦ => hunit H Φ (fun v g => hΦ _ g) p G (sm G hf)
  · rw [hom _ G hf, htriv _ (mMF_fin θ hg hk) G (sm G hf)]
  · obtain ⟨u, v, hu, rfl⟩ := _root_.GlobalTheory.RealWeilF.exists_realZero_add_iotaVF F E nS nT θ ι hι w
    have h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoVF σ JS JT ξ₀ B.ψ hc ι v G).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ hf
    have h2 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v G)).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ h1
    have e1 : actOF σ JS JT g k (u + iotaVF ι v) = u + iotaVF ι (mMF σ JS JT θ (g, k) *ᵥ v) := by
      rw [GlobalTheory.RealWeilF.actOF_add, _root_.GlobalTheory.RealWeilFinFix.actOF_fin F E σ nS nT JS JT g k hg hk u hu, _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    rw [hom _ G hf, e1, ← coe_rhoBF hc _ G, ← coe_rhoBF hc _ (Ω (g, k) G), radd hu v G,
      radd hu _ (Ω (g, k) G), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm G hf)]
  · rw [hom _ G hf, hvac s p hs hpos hsc G (sm G hf) (fderiv_vacF hc ι s G (sm G hf) hv)]
    rfl
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutSubst
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem rat_subst_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    IsThetaFunOF σ JS JT ξ₀ B.ψ (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) ∧
    (∀ w₀, (fun x => heisOF σ JS JT ξ₀ B.ψ w₀ f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) =
      heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT γ γ' w₀) (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x))) ∧
    ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∫⁻ x in 𝓕, ‖f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  have hi := (GQF σ JS).inv_mem hγ
  have hi' := (GQF σ JT).inv_mem hγ'
  have hinv : ∀ x, actOF σ JS JT γ γ' (actOF σ JS JT γ⁻¹ γ'⁻¹ x) = x := fun x => by
    have := SubstA.actOF_inv_actOF (σ := σ) (JS := JS) (JT := JT) γ⁻¹ γ'⁻¹ x
    rwa [inv_inv, inv_inv] at this
  refine ⟨SubstA.isThetaFunOF_comp C.hS hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext x
    unfold heisOF
    beta_reduce
    rw [GlobalTheory.FinLatF.actOF_add, SubstA.actOF_inv_actOF, ← SubstA.symplOHF_actOF C.hS γ⁻¹ γ'⁻¹ x,
      SubstA.actOF_inv_actOF]
  · let e : WOF F E nS nT ≃+ WOF F E nS nT :=
      { toFun := actOF σ JS JT γ⁻¹ γ'⁻¹
        invFun := actOF σ JS JT γ γ'
        left_inv := hinv
        right_inv := SubstA.actOF_inv_actOF γ γ'
        map_add' := GlobalTheory.FinLatF.actOF_add _ _ }
    refine SubstA.setLIntegral_comp e (SubstA.continuous_actOF _ _) (SubstA.continuous_actOF _ _)
      (fun x => ⟨fun hx => ?_, SubstA.actOF_mem_ratLF hi hi'⟩) μ hμ h𝓕 (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact SubstA.actOF_mem_ratLF hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h7 : ‖f (ratWF y + x)‖ = ‖f x‖ := by
        rw [hf.quasi y x, norm_mul, hψ, one_mul]
      show ‖f (ratWF y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]
theorem schur_norm_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (h1 : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f))
    (h2 : ∀ u f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ u f) = heisOF σ JS JT ξ₀ B.ψ u (M f))
    (h3 : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ∫⁻ x in 𝓕, ‖M f x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.T.theta_preserving_endomorphism_scalar F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ M h1 h2 h3
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  by_cases h0 : ∃ f y, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ f y ≠ 0
  · obtain ⟨f, y, hf, hy⟩ := h0
    obtain ⟨μ, 𝓕, hμ, h𝓕, hI0, hIt⟩ := GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin hψ hf hy
    have h := h3 μ 𝓕 hμ h𝓕 f hf
    rw [hc f hf] at h
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)] at h
    have e1 : ‖c‖ₑ ^ 2 = 1 := by
      have := congrArg (· / ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) h
      rwa [ENNReal.mul_div_cancel_right hI0 hIt, ENNReal.div_self hI0 hIt] at this
    have e2 : (‖c‖₊ : ENNReal) ^ 2 = 1 := by rwa [enorm_eq_nnnorm] at e1
    have e3 : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast e2
    have e4 : ‖c‖ ^ 2 = 1 := by
      have := congrArg (fun t : NNReal => (t : ℝ)) e3
      simpa using this
    exact ⟨c, (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 e4, hc⟩
  · push_neg at h0
    refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => h0 f y hf
    subst this
    simp
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldChart
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem chartFacts_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h, (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix (Fin d.n ⊕ Fin d.n) _ (AE F E)) u v := by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

