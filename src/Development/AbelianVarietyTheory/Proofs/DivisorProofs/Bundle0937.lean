module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelesSelfDual
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.CentPos

theorem eq_smul_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hZ : M * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * diagonal lam)
    (μ : ℂ) (u w : Fin n → ℂ) (hu : M *ᵥ u = μ • u) (hw : M *ᵥ w = μ • w) (hu0 : u ≠ 0) :
    ∃ l : ℂ, w = l • u := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)
  set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : Zi * Zm = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have h2 : Zm * Zi = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have hD : Zi * M = diagonal lam * Zi := by
    calc Zi * M = Zi * (M * Zm) * Zi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Zi * (Zm * diagonal lam) * Zi := by rw [hZ]
      _ = diagonal lam * Zi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j := by
    intro a ha j
    have e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a) := by
      rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]
    have := congrFun e j
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a := by
    intro a; rw [mulVec_mulVec, h2, one_mulVec]
  set u' := Zi *ᵥ u
  set w' := Zi *ᵥ w
  have hu'0 : u' ≠ 0 := by
    intro h; apply hu0; rw [← hback u]; show Zm *ᵥ u' = 0; rw [h, mulVec_zero]
  obtain ⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu'0 (funext h)
  have hlam0 : lam i0 = μ := mul_right_cancel₀ hi0 (hcoord u hu i0)
  refine ⟨w' i0 / u' i0, ?_⟩
  have hw' : w' = (w' i0 / u' i0) • u' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i0
    · subst hj; field_simp
    · have hne : lam j - μ ≠ 0 := by
        intro h; apply hj; apply hlam; rw [hlam0]; exact sub_eq_zero.1 h
      have hu0j : u' j = 0 := by
        have := hcoord u hu j
        have h' : (lam j - μ) * u' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      have hw0j : w' j = 0 := by
        have := hcoord w hw j
        have h' : (lam j - μ) * w' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      rw [hu0j, hw0j, mul_zero]
  calc w = Zm *ᵥ w' := (hback w).symm
    _ = Zm *ᵥ ((w' i0 / u' i0) • u') := by rw [← hw']
    _ = (w' i0 / u' i0) • u := by rw [mulVec_smul, hback u]

theorem cent_form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F)
    (y : G.Cˣ × ℚˣ) (hy : y ∈ P.cent) :
    (G.psi v (y.1 : G.C))ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v (y.1 : G.C) =
      (((y.2 : ℚˣ) : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β := hy.2
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 =
      algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (y.1 * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (y.1 : G.C) * P.β * (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1)
        = ((y.1 : G.C) * P.β * sh G (y.1 : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 := by
          simp only [mul_assoc]
      _ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
          rw [hsim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (y.1 : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (y.1 : G.C)
      = G.gram v * (G.psi v (sh G (y.1 : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v (y.1 : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid.CentPos

namespace GlobalTheory.LKMid


open GlobalTheory.LKMid.CentPos in
theorem cent_sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := by
  intro p _ G P μ _ hm y hy
  obtain ⟨v, -, x, hx, hpos⟩ := hm
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef
  set M := G.psi v (P.γ : G.C) with hMdef
  set Y := G.psi v (y.1 : G.C) with hYdef
  have hc : (y.1 : G.C) * P.γ = P.γ * y.1 := by
    have := congrArg Units.val hy.1; simpa using this
  have hMY : M * Y = Y * M := by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]
  have hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H := cent_form_law G P v y hy
  obtain ⟨Z, lam, hinj, -, hZ⟩ := psi_eigenbasis p G P v
  have hx0 : x ≠ 0 := by rintro rfl; simp at hpos
  have hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) := by
    rw [mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨l, hl⟩ := eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0
  have key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
    simp only [hHdef, Matrix.mul_assoc]
  rw [hform, hl] at key
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  set q := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ) := by
    rw [← mul_assoc] at key; have := mul_right_cancel₀ hq0 key; rw [mul_comm] at this; exact this
  have hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ) := by simp
  have hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ) := by
    have : (star l * l).re = Complex.normSq l := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]; simp
    rw [hs] at this
    have h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ) := by simp
    rw [← h2, this]; exact Complex.normSq_nonneg l
  have hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ) := by exact_mod_cast hnn
  exact lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists
section
open Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.AdFormsModel

section

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {I : Type} {y : I → G}

theorem eq_zero_of_reps (hy : Bridge.IsReps ι J y) {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (h0 : ∀ i, F (y i) = 0) : F = 0 := by
  funext h
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy h
  have := hF γ (y i) k
  rw [this, h0 i]
  simp

theorem finiteDimensional_adForms [FiniteDimensional ℂ W] [Finite I] (hy : Bridge.IsReps ι J y) :
    FiniteDimensional ℂ (Bridge.AdForms ι ρ J χ) := by
  let ev : Bridge.AdForms ι ρ J χ →ₗ[ℂ] (I → W) :=
    (LinearMap.funLeft ℂ W y).comp (Bridge.AdForms ι ρ J χ).subtype
  refine FiniteDimensional.of_injective ev ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  exact Subtype.ext (eq_zero_of_reps hy F.2 fun i => congrFun hF i)

theorem adInner_self_pos [Fintype I] (hy : Bridge.IsReps ι J y) (hs : ∀ i, Finite (Bridge.stab ι J (y i)))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) (hne : F ≠ 0) : 0 < (Bridge.adInner ι J y F F).re := by
  have hre : (Bridge.adInner ι J y F F).re =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 := by
    unfold Bridge.adInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    have : ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ((‖F (y i)‖ : ℝ) : ℂ) ^ 2 =
        ((((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    exact (congrArg Complex.re this).trans (Complex.ofReal_re _)
  rw [hre]
  obtain ⟨i, hi⟩ : ∃ i, F (y i) ≠ 0 := by
    by_contra hcon
    exact hne (eq_zero_of_reps hy hF fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
  haveI := hs i
  have h1 : (0 : ℝ) < (Nat.card (Bridge.stab ι J (y i)) : ℝ) := by exact_mod_cast Nat.card_pos
  have h2 : 0 < ‖F (y i)‖ := norm_pos_iff.2 hi
  positivity

end

theorem exists_hmod_adForms : ∀ (G Γ W : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (I : Type)
    [Fintype I] (y : I → G), Bridge.IsReps ι J y → (∀ i, Finite (Bridge.stab ι J (y i))) →
    ∃ M : HMod (G → W), M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y) := by
  intro G Γ W _ _ _ _ _ ι ρ J χ I _ y hy hs
  refine GlobalTheory.HilbertModel.exists_hmod (G → W) _ _ (finiteDimensional_adForms hy) ?_
    (fun F hF hne => adInner_self_pos hy hs hF hne)
  intro a _ b _ d _ c
  constructor
  · simp only [Bridge.adInner, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [Bridge.adInner, star_sum, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm (b (y i)) (a (y i))]
    rfl

end GlobalTheory.AdFormsModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicModule_norm_rationalUnit_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (z : E), (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) u) = 1 := by
  first | exact @GlobalTheory.NormModule.modu_norm_rat | exact GlobalTheory.NormModule.modu_norm_rat | (intros; apply GlobalTheory.NormModule.modu_norm_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical Topology

noncomputable section

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem Bd_half_f (u y : Fin N → Af F) : Bd (Af F) (half F N) u y = u ⬝ᵥ y := by
  simp [Bd, half, dotProduct]

theorem annih_basis (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (u ⬝ᵥ y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨lam, ν, hc⟩ := ctx_exists F hF ψ hψ N (half F N) (fun l => half_ne_zero l)
  obtain ⟨-, h2, h3⟩ := _root_.GlobalTheory.SWQ.finite_annihilators F N ψ lam ν (half F N) hc
  refine ⟨fun K hK => ?_, h3⟩
  have := h2 K hK
  simpa only [Bd_half_f] using this

def levelSub (L : AddSubgroup (Af F)) : AddSubgroup (VA F N) where
  carrier := {u | ∀ l, sndA F (u.1 l) ∈ L ∧ sndA F (u.2 l) ∈ L}
  zero_mem' := fun l => by simp
  add_mem' := fun ha hb l => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]
    exact ⟨L.add_mem (ha l).1 (hb l).1, L.add_mem (ha l).2 (hb l).2⟩
  neg_mem' := fun ha l => by
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg]
    exact ⟨L.neg_mem (ha l).1, L.neg_mem (ha l).2⟩

theorem isOpen_levelSub {L : AddSubgroup (Af F)} (hL : IsOpen (L : Set (Af F))) :
    IsOpen (levelSub (N := N) L : Set (VA F N)) := by
  have hs : Continuous fun z : AF F => sndA F z := continuous_snd
  have e : (levelSub (N := N) L : Set (VA F N)) =
      ⋂ l, ((fun u : VA F N => sndA F (u.1 l)) ⁻¹' L ∩ (fun u : VA F N => sndA F (u.2 l)) ⁻¹' L) := by
    ext u; simp [levelSub]
  rw [e]
  refine isOpen_iInter_of_finite fun l => IsOpen.inter ?_ ?_
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_fst))
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_snd))

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem adele_ext {z z' : AF F} (h1 : fstA F z = fstA F z') (h2 : sndA F z = sndA F z') : z = z' := Prod.ext h1 h2

theorem pure_level [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) :
    ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 →
      GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  obtain ⟨hann, hbas⟩ := annih_basis (N := N) hF ψ hψ
  have hV := eventually_invariant hg.1 hg.2
  obtain ⟨L0, hL0o, hL0c, hL0V⟩ := hbas _ hV
  set c : Af F := algebraMap F (Af F) (1 / 2)
  have hK2 : IsCompact ((fun a : Fin N → Af F => c • a) '' {a | ∀ l, a l ∈ L0}) := by
    have : IsCompact {a : Fin N → Af F | ∀ l, a l ∈ L0} := by
      have := isCompact_univ_pi (fun _ : Fin N => hL0c)
      simpa [Set.pi] using this
    exact this.image (continuous_const_smul c)
  have hA1 := hann _ hg.2.isCompact
  have hA2 := hann _ hK2
  obtain ⟨L1, hL1o, -, hL1⟩ := hbas _ (Filter.inter_mem (Filter.inter_mem hV hA1) hA2)
  refine ⟨levelSub (L0 ⊓ L1), isOpen_levelSub (by rw [AddSubgroup.coe_inf]; exact hL0o.inter hL1o),
    fun u hu h1 h2 => ?_⟩
  set a : Fin N → Af F := fun l => sndA F (u.1 l)
  set b : Fin N → Af F := fun l => sndA F (u.2 l)
  have ha0 : ∀ l, a l ∈ L0 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).1
  have ha1 : ∀ l, a l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).2
  have hb1 : ∀ l, b l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).2).2
  obtain ⟨⟨hVa, -⟩, -⟩ := hL1 a ha1
  obtain ⟨⟨-, hAb⟩, hA2b⟩ := hL1 b hb1
  have i1 : ∀ l, fstA F (u.1 l) = 0 := fun l => congrFun h1 l
  have i2 : ∀ l, fstA F (u.2 l) = 0 := fun l => congrFun h2 l
  funext x
  set xf : Fin N → Af F := fun i => (x i).2
  have ex : (fun i => ((x + u.1) i).2) = xf + a := by
    funext i; rfl
  have ex' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    have : ((x + u.1) i).1 = (x i).1 := by
      show (x i).1 + (u.1 i).1 = (x i).1
      rw [show (u.1 i).1 = fstA F (u.1 i) from rfl, i1 i, add_zero]
    rw [this]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA]
  rw [ex, ex', hVa xf]
  by_cases hg0 : g xf = 0
  · rw [hg0]; simp
  have hxK : xf ∈ tsupport g := subset_tsupport g hg0
  have e : x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2) = pairA F 0 (xf ⬝ᵥ b) + pairA F 0 ((c • a) ⬝ᵥ b) := by
    apply adele_ext
    · simp only [map_add (f := _), map_mul]
      rw [show fstA F (x ⬝ᵥ u.2) = (fstA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show fstA F (u.1 ⬝ᵥ u.2) = (fstA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct]
      have : (fstA F).toRingHom ∘ u.2 = 0 := funext i2
      rw [this, dotProduct_zero, dotProduct_zero, mul_zero, add_zero]
      rw [show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, add_zero]
    · simp only [map_add (f := _), map_mul]
      rw [show sndA F (x ⬝ᵥ u.2) = (sndA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show sndA F (u.1 ⬝ᵥ u.2) = (sndA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct,
        invOf_two_eq, AlgHom.commutes, smul_dotProduct, smul_eq_mul]
      rw [show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl, show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl]
      rfl
  rw [e, AddChar.map_add_eq_mul, hAb _ hxK, hA2b _ ⟨a, ha0, rfl⟩]
  ring

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

theorem schA_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ),
    IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N),
      IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_level ψ hF hψ f g hg
  | zero =>
    exact ⟨⊤, isOpen_univ, fun u _ _ _ => by funext x; simp [GlobalTheory.WeilM.schr]⟩
  | add Φ Φ' _ _ h h' =>
    obtain ⟨U, hU, hUΦ⟩ := h
    obtain ⟨U', hU', hUΦ'⟩ := h'
    refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u (AddSubgroup.mem_inf.mp hu).1 h1 h2) x
    have e2 := congrFun (hUΦ' u (AddSubgroup.mem_inf.mp hu).2 h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c Φ _ h =>
    obtain ⟨U, hU, hUΦ⟩ := h
    refine ⟨U, hU, fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u hu h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]

end GlobalTheory.WeilLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventually
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem isIntB_of_trace_mem :
    ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  intro L _ _ κ bL
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have hd : Algebra.discr ℚ bL ≠ 0 := Algebra.discr_not_zero_of_basis ℚ bL
  obtain ⟨S, hS⟩ := exists_finset_algebraMap_mem
    (insert (Algebra.discr ℚ bL)⁻¹
      (Finset.univ.image fun p : κ × κ => Algebra.trace ℚ L (bL p.1 * bL p.2)))
  refine ⟨S, fun v hv E hE => ?_⟩
  set Q := v.adicCompletion ℚ
  let B := Algebra.TensorProduct.basis Q bL
  have hB : ∀ i, B i = (1 : Q) ⊗ₜ[ℚ] bL i := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have htr : ∀ i j, Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) =
      algebraMap ℚ Q (Algebra.trace ℚ L (bL i * bL j)) := fun i j => by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul']
  have hTM : Algebra.traceMatrix Q B = (algebraMap ℚ Q).mapMatrix (Algebra.traceMatrix ℚ bL) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    exact htr i j
  have hdet : (Algebra.traceMatrix Q B).det = algebraMap ℚ Q (Algebra.discr ℚ bL) := by
    rw [hTM, ← RingHom.map_det, Algebra.discr_def]
  have hG : ∀ i j, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) := fun i j =>
    ⟨⟨_, hS v hv _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩,
      (htr i j).symm⟩
  have hω : ∀ i, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (E * B i) := fun i => ⟨⟨_, by rw [hB]; exact hE i⟩, rfl⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum (v.adicCompletionIntegers ℚ) Q (Q ⊗[ℚ] L) κ B E hG hω
  intro j
  have hrep : B.repr E j = (algebraMap ℚ Q (Algebra.discr ℚ bL))⁻¹ *
      algebraMap (v.adicCompletionIntegers ℚ) Q (u j) := by
    have h1 := congrArg (fun x => B.repr x j) hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply', Module.Basis.repr_self, Finsupp.single_apply, hdet] at h1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h1
    simp only [if_true, mul_one] at h1
    have hne : algebraMap ℚ Q (Algebra.discr ℚ bL) ≠ 0 := (map_ne_zero _).2 hd
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show B.repr E j ∈ v.adicCompletionIntegers ℚ
  rw [hrep, ← map_inv₀]
  exact mul_mem (hS v hv _ (Finset.mem_insert_self _ _)) (u j).2

end GlobalTheory.LocIntSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitudeStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude : ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s → Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ, Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  first | (exact @GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (exact GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (intros; apply GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude  <;> assumption)
end

