module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsoluteHermitianVolumeBoundArith
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.VolArith

theorem volU_two : volU 2 = 8 * Real.pi ^ 3 := by
  unfold volU sphV
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  norm_num
  ring

theorem one_le_fDeg (E : Type) [Field E] [NumberField E] : 1 ≤ Formalism.HermitianLatticesTheory.fDeg E :=
  Fintype.card_pos

theorem one_le_rd (E : Type) [Field E] [NumberField E] : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have h : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E)) (by positivity)
  linarith

theorem sum_half (n : ℕ) (hn : 2 ≤ n) :
    ∑ M ∈ Finset.Ioc 2 n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - 4) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, ih]
    push_cast
    ring

theorem lVal_le (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (M : ℕ) (hM : 3 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      Formalism.HermitianLatticesTheory.lValEta E M ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  obtain ⟨-, h0, h1⟩ := Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound E hE M hM
  refine ⟨h0, ?_⟩
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
    simpa using this
  have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
    hs.tsum_pos (fun m => by positivity) 0 (by positivity)
  rw [← Real.log_le_log_iff h0 (pow_pos hz _), Real.log_pow]
  exact (le_abs_self _).trans h1

theorem prod_rankFac_le (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ ∏ M ∈ Finset.Ioc 2 n, rankFac E M ∧
    ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) *
        1.4 ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hr := one_le_rd E
  have hr0 : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E := by linarith
  have hL : ∀ M ∈ Finset.Ioc 2 n, 0 ≤ Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).1.le
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr0, ← Finset.mul_sum, sum_half n hn]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr0.le _) (Finset.prod_nonneg hL), ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
  refine (Finset.prod_le_prod₀ hL (fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).2)).trans ?_
  rw [Finset.prod_pow]
  refine pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l) ?_ _
  have e : Finset.Ioc 2 n = Finset.Icc 3 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [e]
  exact (GlobalTheory.zetaProd_sphereVolume_bounds.2.1 n).le

theorem volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE n X hn hX hrX hfX
  obtain ⟨hP0, hP⟩ := prod_rankFac_le E hE n (by omega)
  have hr := one_le_rd E
  have hf := one_le_fDeg E
  set r := 2 * Formalism.HermitianLatticesTheory.vInv E with hrdef
  set f := Formalism.HermitianLatticesTheory.fDeg E with hfdef
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlog1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA : 1 + f * Real.log r ≤ X ^ 2 := by nlinarith
  have hA0 : 0 ≤ 1 + f * Real.log r := by positivity
  have hpi : Real.pi ^ 3 ≤ 3.15 ^ 3 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3
  have hc : 8 * Real.pi ^ 3 * 4 * 1.4 ≤ X ^ 11 := by
    have : (2 : ℝ) ^ 11 ≤ X ^ 11 := pow_le_pow_left₀ (by norm_num) hX 11
    nlinarith
  have hpi0 := Real.pi_pos
  have he0 : 0 ≤ (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2) := mul_nonneg (by linarith) (by nlinarith)
  have h1 : (8 * Real.pi ^ 3 * 4 * 1.4) ^ f ≤ (X ^ 11) ^ f := pow_le_pow_left₀ (by positivity) hc f
  have h2 : r ^ (5 * f) ≤ X ^ (5 * f) := pow_le_pow_left₀ (by linarith) hrX _
  have h3 : (1 + f * Real.log r) ^ (5 * f) ≤ (X ^ 2) ^ (5 * f) := pow_le_pow_left₀ hA0 hA _
  have h4 : r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) ≤ X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) :=
    Real.rpow_le_rpow (by linarith) hrX he0
  have hr0 : 0 < r := by linarith
  rw [volU_two]
  calc (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        ∏ M ∈ Finset.Ioc 2 n, rankFac E M
      ≤ (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        (r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) * 1.4 ^ f) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (8 * Real.pi ^ 3 * 4 * 1.4) ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f) *
        r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [mul_pow (8 * Real.pi ^ 3 * 4), mul_pow (8 * Real.pi ^ 3)]
        ring
    _ ≤ (X ^ 11) ^ f * X ^ (5 * f) * (X ^ 2) ^ (5 * f) *
        X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        gcongr
    _ = X ^ (((26 * f : ℕ) : ℝ) + (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [Real.rpow_add hX0, Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 2
        ring
    _ ≤ X ^ ((n ^ 2 * f : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        push_cast
        have : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith
    _ = X ^ (n ^ 2 * f) := Real.rpow_natCast _ _

end GlobalTheory.VolArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormFromEquivariant
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForm_from_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → Function.Injective Jm → (∀ p ∈ ValC (gramC J emb) lam, ∃ ξ, Jm ξ = p) → ∀ g ∈ AdForms S emb lam, ∃ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) ∧ ∀ y : UPts σ J (FiniteAdeleRing (𝓞 F) F), g y = Jm (φ (Φ.symm (y * h0⁻¹))) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm
    hψ hK hχ hrat hint hinj hsurj g hg

  have hval : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_inf.mp hg).2 z (Set.mem_univ z)
  have hfun := (Submodule.mem_inf.mp hg).1
  choose pre hpre using fun z => hsurj (g z) (hval z)
  refine ⟨fun x => pre (Φ x * h0), ?_, ?_⟩
  · intro γ x κ
    obtain ⟨gr, hgrU, hgr⟩ := hrat γ
    apply hinj
    rw [hpre, LinearMap.map_smulₛₗ]
    funext y
    obtain ⟨y', hy'⟩ := exists_isTr' emb gr y
    rw [Pi.smul_apply, hint γ gr hgr (pre (Φ x * h0)) y y' hy', hpre]

    have hconj : (starRingEnd ℂ) ((((ψ κ)⁻¹ : ℂˣ) : ℂ)) = ((ψ κ : ℂˣ) : ℂ) := by
      rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ κ), Complex.conj_conj]
    rw [smul_eq_mul, hconj]
    have hk : ((h0⁻¹ * Φ κ.1 * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U :=
      (hK κ.1).1 κ.2
    have hx : (Φ (ιf γ * x * κ.1) * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
        Φ (ιf γ) * (Φ x * h0) * (h0⁻¹ * Φ κ.1 * h0) := by
      simp only [map_mul]; group
    have key := hfun gr hgrU (Φ x * h0) (Φ (ιf γ * x * κ.1) * h0) ⟨_, hk⟩
      (by rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, hgr]) y y' hy'
    rw [key, ← hχ κ.1 κ.2 hk]
  · intro y
    rw [hpre]
    congr 1
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlace
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Carry

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


omit [NumberField E] in
theorem prVec_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F)) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (y.1 *ᵥ x) = (bc (prV (E := E) v) y).1 *ᵥ prVec v x := by
  funext i
  exact RingHom.map_mulVec (prV (E := E) v) y.1 x i

omit [NumberField E] in
theorem prVec_single_self (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec v (fun i => Formalism.UG.P.afsplitIE v (x i)) = x := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE v (x i)

omit [NumberField E] in
theorem prVec_single_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec w (fun i => Formalism.UG.P.afsplitIE v (x i)) = 0 := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE_ne v w h (x i)

theorem carry_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ n L M hL hM y
  have lgL := _root_.GlobalTheory.St.G.mem_hat_iff_forall_loc F E n L hL
  have lgM := _root_.GlobalTheory.St.G.mem_hat_iff_forall_loc F E n M hM
  constructor
  · intro h v x
    have h1 := h (fun i => Formalism.UG.P.afsplitIE v (x i))
    rw [lgL, lgM] at h1
    constructor
    · intro hx
      have h2 := h1.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw]; exact Submodule.zero_mem _) v
      rwa [prVec_mulVec, prVec_single_self] at h2
    · intro hx
      have h2 := h1.2 (fun w => by
        rw [prVec_mulVec]
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw, Matrix.mulVec_zero]; exact Submodule.zero_mem _) v
      rwa [prVec_single_self] at h2
  · intro h x
    rw [lgL, lgM]
    refine forall_congr' fun v => ?_
    rw [prVec_mulVec]
    exact h v _

end GlobalTheory.St.G.Carry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.AdelicLattice

theorem adelicLattice_selfDual : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  intro I y
  have hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := by
    ext a
    rfl
  have hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L,
      Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈
        (algebraMap (𝓞 I.E) I.E).range := by
    rw [hsig]
    exact I.L_dual

  have hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) =
      (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E)
      ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by
    intro u
    show u ∈ Submodule.span _ _ ↔ _
    rw [hgen]
  constructor
  · intro hy y' hy'
    have hy'' := (hLf y').1 hy'
    unfold hAf
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      exact Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''
    | zero =>
      rw [Formalism.UG.P.csScale_hform_zero_right]
      exact zero_mem _
    | add u v _ _ hu hv =>
      rw [Formalism.UG.P.csScale_hform_add_right]
      exact add_mem hu hv
    | smul c v _ hv =>
      rw [Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]
      exact mul_mem c.2 hv
  · intro h
    have hmem := GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y
      (fun w hw => h w ((hLf w).2 hw))
    exact (hLf y).2 hmem

end GlobalTheory.AdelicLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem absArith_const (r : ℕ) (hr : 1 ≤ r) :
    (4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
      Real.exp 1 ^ (r * (r + 2)) ≤ (4 * r : ℝ) ^ (44 * r ^ 3) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ 4 * r := by linarith
  have h1 : ((r : ℝ) + 1) * 24 ≤ (4 * r : ℝ) ^ 3 := by
    have : (r : ℝ) ≤ (r : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
    nlinarith
  have he : Real.exp 1 ≤ 4 * r := by
    have := Real.exp_one_lt_d9
    linarith
  have hexp : 11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2) ≤ 44 * r ^ 3 := by
    have a1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have a2 : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    nlinarith
  calc _ ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * (4 * r : ℝ) ^ 3 * (4 * r : ℝ) ^ (24 * r ^ 3 + 1) *
        (4 * r : ℝ) ^ (2 * r) * (4 * r : ℝ) ^ (r * (r + 2)) := by
        gcongr
        linarith
    _ = (4 * r : ℝ) ^ (11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2)) := by
        simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hexp

theorem absArith_shift (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m ≤
      Real.exp 1 ^ (r * (r + 2)) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < ((m + r + 2 : ℕ) : ℝ) := by positivity
  have hpe : 0 < Real.pi * Real.exp 1 := by positivity
  have h1 : (((m + r + 2 : ℕ) : ℝ) / m) ^ m ≤ Real.exp 1 ^ (r + 2) := by
    have h2 : ((m + r + 2 : ℕ) : ℝ) / m ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) := by
      have := Real.add_one_le_exp (((r + 2 : ℕ) : ℝ) / m)
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) ^ m := by gcongr
      _ = Real.exp 1 ^ (r + 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        field_simp
  have h3 : (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) ≤ Real.exp 1 ^ (r * (r + 2)) := by
    rw [mul_comm r m, mul_comm r (r + 2), pow_mul, pow_mul]
    gcongr
  have h4 : (4 : ℝ) ^ m ≤ 4 ^ (r * m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hr)
  calc _ ≤ (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ (r * m) * (2 ^ r) ^ m := by gcongr
    _ = (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
        rw [← pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
        ring
    _ ≤ _ := by gcongr

theorem absArith : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  intro k r H₁ De D hr hk hH hDe hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + r + 2 := ⟨k - 2 - r, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmk : m + r + 2 - 2 - r = m := by omega
  unfold absBd
  rw [hmk]
  have hA := absArith_const r hr
  have hB := absArith_shift r m hr hm
  have hC : De ^ (12 * r ^ 2) * De ^ (2 * r) ≤ De ^ (14 * r ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hDe (by nlinarith)
  have hH0 : 0 ≤ H₁ := by linarith
  have hDe0 : 0 ≤ De := by linarith
  calc _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        ((Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m) *
        (De ^ (12 * r ^ 2) * De ^ (2 * r)) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by
        rw [div_pow (2 ^ r : ℝ) D m, div_eq_mul_inv ((2 ^ r : ℝ) ^ m)]
        ring
    _ ≤ ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        (Real.exp 1 ^ (r * (r + 2)) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m)) *
        De ^ (14 * r ^ 2) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by gcongr
    _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
        Real.exp 1 ^ (r * (r + 2))) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) * (D ^ m)⁻¹ := by
        ac_rfl
    _ ≤ _ := by gcongr

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_E_eq_F (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.E) = Fintype.card (InfinitePlace I.F) := by
  have hsurj : Function.Surjective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) :=
    fun v => InfinitePlace.comap_surjective v
  have hinj : Function.Injective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
    intro w₁ w₂ h
    have key : ∀ w : InfinitePlace I.E,
        w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases _root_.GlobalTheory.Count.Test.embedding_cases I w with hw | hw
      · rw [← hw, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← hw, InfinitePlace.mk_embedding]
    rw [key w₁, key w₂]
    simp only at h
    rw [h]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_F_eq_finrank (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.F) = Module.finrank ℚ I.F := by
  haveI := I.cm.totReal
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero] at *
  omega

open MeasureTheory NumberField Matrix Finset in
private theorem one_le_abs_discr_E (I : _root_.Formalism.MainNotions.S.AutInst) : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
  have h := discr_ne_zero I.E
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.instance_numbers : ∀ I : _root_.Formalism.MainNotions.S.AutInst, _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * _root_.Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, _root_.GlobalTheory.FlagMeas.HasSig I p q → p + q = I.n := by
  intro I
  have hdeg : _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [card_infinitePlace_E_eq_F, card_infinitePlace_F_eq_finrank]
  have hcardF : Fintype.card (InfinitePlace I.F) = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact card_infinitePlace_F_eq_finrank I
  have hfpos : 1 ≤ I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact Module.finrank_pos
  refine ⟨hdeg, ?_, ?_, hfpos, hcardF, ?_⟩
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd _root_.Formalism.HermitianLatticesTheory.vInv
    rw [hdeg]
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    ring
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd
    apply Real.one_le_rpow (one_le_abs_discr_E I)
    positivity
  · intro p q h
    unfold _root_.GlobalTheory.FlagMeas.HasSig at h
    have hne : Nonempty (InfinitePlace I.F) := by
      apply Fintype.card_pos_iff.mp
      omega
    obtain ⟨v⟩ := hne
    obtain ⟨hp, hq⟩ := h v
    rw [← hp, ← hq]
    unfold _root_.Formalism.MainNotions.S.AutInst.pAt _root_.Formalism.MainNotions.S.AutInst.qAt
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin I.n))) (fun a => I.ε v a = true)
    simpa using this

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autPointLatticeIntersection_selfDual_properties : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  first | exact @GlobalTheory.PointLattice.lamX_selfDual | exact GlobalTheory.PointLattice.lamX_selfDual | (intros; apply GlobalTheory.PointLattice.lamX_selfDual <;> assumption)
end

