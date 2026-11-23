module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NlenLeLenN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyValLeSumMulPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestriction
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDual


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isDR_of_summand (D : D7) (hFont : FontaineAtPlacesOverL (D := D)) (hP : PotDRL D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ)
    (hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n)
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) : IsDR (Br.PD D.loc D.nbr i w hw) X.ρ := by
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W'.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X hW'

section Lin

variable {LL : Type} [Field LL] {a n : ℕ}

def pr (LL : Type) [Field LL] (a n : ℕ) :
    (Fin a → Fin n → LL) →ₗ[LL] (Fin a → Fin n → LL) →ₗ[LL] LL :=
  LinearMap.mk₂ LL (fun u u' => ∑ b, u b ⬝ᵥ u' b)
    (fun u₁ u₂ u' => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun c u u' => by simp [smul_dotProduct, Finset.mul_sum])
    (fun u u₁ u₂ => by simp [dotProduct_add, Finset.sum_add_distrib])
    (fun c u u' => by simp [dotProduct_smul, Finset.mul_sum])

theorem pr_apply (u u' : Fin a → Fin n → LL) : pr LL a n u u' = ∑ b, u b ⬝ᵥ u' b := rfl

def ann (C : Submodule LL (Fin a → Fin n → LL)) : Submodule LL (Fin a → Fin n → LL) where
  carrier := {u' | ∀ u ∈ C, pr LL a n u u' = 0}
  add_mem' := fun h1 h2 u hu => by rw [map_add (f := _), h1 u hu, h2 u hu, add_zero]
  zero_mem' := fun u _ => by rw [map_zero]
  smul_mem' := fun c u' h u hu => by rw [map_smul, h u hu, smul_zero]

theorem pr_single (b : Fin a) (k : Fin n) (u' : Fin a → Fin n → LL) :
    pr LL a n (Pi.single b (Pi.single k 1)) u' = u' b k := by
  rw [pr_apply, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem exists_rep (φ : (Fin a → Fin n → LL) →ₗ[LL] LL) :
    ∃ u' : Fin a → Fin n → LL, ∀ u, φ u = pr LL a n u u' := by
  refine ⟨fun b k => φ (Pi.single b (Pi.single k 1)), fun u => ?_⟩
  have hu : u = ∑ b, ∑ k, u b k • (Pi.single b (Pi.single k 1) : Fin a → Fin n → LL) := by
    funext b' k'
    simp [Finset.sum_apply, Pi.single_apply, ite_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
  conv_lhs => rw [hu]
  rw [pr_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, dotProduct]

theorem eq_zero_of_pr (u' : Fin a → Fin n → LL) (h : ∀ u, pr LL a n u u' = 0) : u' = 0 := by
  funext b k
  rw [← pr_single b k u']
  exact h _

end Lin

section Lin2

variable {LL : Type} [Field LL] {a n : ℕ}

theorem left_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u : Fin a → Fin n → LL)
    (hu : u ∈ R) (h : ∀ u' ∈ ann C, pr LL a n u u' = 0) : u = 0 := by
  by_contra hne
  have hne' : (⟨u, hu⟩ : ↥R) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual LL ↥R, f ⟨u, hu⟩ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne' ((Module.forall_dual_apply_eq_zero_iff LL _).1 hall)
  obtain ⟨u', hu'⟩ := exists_rep (f ∘ₗ R.projectionOnto C hRC)
  have hann : u' ∈ ann C := by
    intro c hc
    rw [← hu', LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right hRC hc, map_zero]
  apply hf
  have := hu' u
  rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_left hRC ⟨u, hu⟩] at this
  rw [this]
  exact h u' hann

theorem right_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) (h : ∀ u ∈ R, pr LL a n u u' = 0) : u' = 0 := by
  apply eq_zero_of_pr
  intro u
  have hu : u ∈ R ⊔ C := by rw [hRC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add (f := _), LinearMap.add_apply, h y hy, hu' z hz, add_zero]

variable {G : Type} [Group G] (T U : Fin a → (G →* Matrix (Fin n) (Fin n) LL)) (χ : G → LL)

theorem pr_equiv (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (g : G) (u u' : Fin a → Fin n → LL) :
    pr LL a n (fun b => (T b g).mulVec (u b)) (fun b => (U b g).mulVec (u' b)) = χ g * pr LL a n u u' := by
  rw [pr_apply, pr_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
    dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
    inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem ann_stable (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (C : Submodule LL (Fin a → Fin n → LL))
    (hC : ∀ g, ∀ u ∈ C, (fun b => (T b g).mulVec (u b)) ∈ C) (g : G) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) : (fun b => (U b g).mulVec (u' b)) ∈ ann C := by
  intro u hu
  have e : u = fun b => (T b g).mulVec ((T b g⁻¹).mulVec (u b)) := by
    funext b
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  rw [e, pr_equiv T U χ hU, hu' _ (hC g⁻¹ u hu), mul_zero]

end Lin2

theorem finrank_eq_of_perfect {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    finrank LL V = finrank LL V' := by
  first
  | exact @_root_.GlobalTheory.NondegenerateFinrank.main
  | exact _root_.GlobalTheory.NondegenerateFinrank.main
  | (apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NondegenerateFinrank.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NondegenerateFinrank.main ..)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dual_of_summand (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) :
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  obtain ⟨a, x, j, hjinj, hjeq, C, hC, hcompl⟩ := hX
  let Ms : ↥Xs → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => Br.loc D.nbr i w hw (rDuO D.nd i r y)
  have hc : ∀ y v, Continuous fun g => (Ms y g).mulVec v := fun y v =>
    (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).2).matrix_mulVec continuous_const
  let T : Fin a → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun b => Br.loc D.nbr i w hw (rTwO D.nd i r (x b))
  let χ : Br.G D.nbr i w hw → Br.LL D.nbr i w hw := fun g =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw)
  have hU : ∀ b g, Ms (x b) g = χ g • (T b g⁻¹).transpose := fun b g =>
    GlobalTheory.JumpDual.loc_dual D i w hw r (x b) g
  let A := GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) Ms hc x
  have hstab : ∀ g, ∀ u ∈ ann C, A.ρ g u ∈ ann C := fun g u hu =>
    ann_stable T (fun b => Ms (x b)) χ hU C hC g u hu
  let X' := A.sub (ann C) hstab
  let PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw :=
    (pr (Br.LL D.nbr i w hw) a D.R.nV).compl₁₂ j (ann C).subtype
  have hPX : ∀ v (y : X'.V), PX v y = pr (Br.LL D.nbr i w hw) a D.R.nV (j v) ((ann C).subtype y) :=
    fun _ _ => rfl
  have h2 : ∀ v, (∀ y, PX v y = 0) → v = 0 := by
    intro v h
    apply hjinj
    rw [map_zero]
    exact left_nondeg (LinearMap.range j) C hcompl (j v) ⟨v, rfl⟩ fun u' hu' => h ⟨u', hu'⟩
  have h3 : ∀ y, (∀ v, PX v y = 0) → y = 0 := by
    intro y h
    apply Subtype.ext
    exact right_nondeg (LinearMap.range j) C hcompl y.1 y.2 (by
      rintro u ⟨v, rfl⟩
      exact h v)
  refine ⟨X', PX, ⟨fun g v y => ?_, h2, h3, finrank_eq_of_perfect PX h2 h3⟩, ?_⟩
  · rw [hPX, hPX, hjeq]
    exact pr_equiv T (fun b => Ms (x b)) χ hU g (j v) ((ann C).subtype y)
  · refine ⟨a, x, fun b => LinearMap.proj b ∘ₗ (ann C).subtype, fun b g v => rfl, fun v hv => ?_⟩
    exact Subtype.ext (funext hv)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem xdual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
      IsDR (Br.PD D.loc D.nbr i w hw) X.ρ ∧
      ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  intro D hFont hP i r hr Xs w hw n hPot X hX
  exact ⟨isDR_of_summand D hFont hP i r hr Xs w hw n hPot X hX, dual_of_summand D i r hr Xs w hw X hX⟩

end GlobalTheory.SummandDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTerm
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def rsTerm {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℂ :=
  ((sat σ w).map fun α => (α : ℂ) ^ (r + 1)).sum * ((sat σ' w).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (r + 1)).sum *
    (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1)

def logRS (T : Finset (HeightOneSpectrum (𝓞 E))) {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) : ℂ :=
  ∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, rsTerm σ σ' x p.1.1 p.2

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameCharEqOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtSel

theorem sameChar_eq_one {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    {f₁ : O₀ →+* O₁} {f₂ : O₀ →+* O₂} {ψ₁ : Γ →* O₁ˣ} {ψ₂ : Γ →* O₂ˣ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂) (g : Γ) (hg : ψ₁ g = 1) : ψ₂ g = 1 := by
  have h1 := h (Finsupp.single g 1 + Finsupp.single 1 (-1))
  rw [Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])] at h1
  simp only [Finsupp.sum_single_index, map_zero, zero_mul, map_one, one_mul, map_neg, hg, Units.val_one,
    mul_one, add_neg_cancel, true_iff] at h1
  ext
  rw [Units.val_one]
  exact add_neg_eq_zero.1 h1

theorem sel_at (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hT : TriplesGood D) (hG : GoodPtRow D) (hR : ResAbsIrr D)
    (a : D.nd.Loc) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a)
    (hπ : π ∈ D.nd.Zgood a) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π))
    (j : D.ntw.Tw) (hj : D.ntw.twOf a = j) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ)
    (f : D.ntw.O0 j →+* D.nd.O a) (hf : HEq f (D.ntw.twist₂ a))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ) :
    ∃ s : D.ntw.Sig j, BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) j s ∧ D.ntw.side _ s = D.ntw.twSide a ∧
      (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ≠ ⊤ → Br.sFin D.loc D.nbr a ρ π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr a ρ π : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ∧
      AttachedIn D a π j s := by
  subst hj
  obtain rfl := eq_of_heq hf
  obtain ⟨σ, Sg, hrow, hW, hX⟩ := hG a π hπ
  obtain ⟨s, htr, hgood⟩ := hT a σ Sg hrow hW
  obtain ⟨U, hU⟩ := GlobalTheory.PtCore.twistedRho_conj_latTpsi hC D a π ρ s Sg hρ hX htr (hR a π hπ _ hρ)
  have e1 := GlobalTheory.ConjLatticeSelmer.sPiTop_eq_sTLoc D a π ρ s U hU
  have e2 := GlobalTheory.SelmerSameChar.sTLoc_eq D a s k ψ hS
  have hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)),
      ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1 := by
    intro v hv g hg
    rw [D.ntw.twOf_l] at hv
    exact sameChar_eq_one hS g (D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v) g hg)
  obtain ⟨h1, h2⟩ := GlobalTheory.SelTwistLe.sT_le_sLen D _ s k (D.nd.Q a) ψ hψ
  rw [← e2, ← e1] at h1 h2
  refine ⟨s, hgood, htr.2.1, ?_, ?_, ⟨rfl, σ, Sg, hrow, hW, hX, htr⟩⟩
  · intro hne
    have h3 := h1 hne
    unfold Br.sFin
    rw [lt_top_iff_ne_top]
    intro h4
    exact h3 (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
  · by_cases h4 : Module.length (D.nd.O a) ↥(Br.selPi D.loc D.nbr a ρ π) = ⊤
    · have h5 : BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) _ s k (D.nd.Q a) ψ = ⊤ := by
        by_contra hne
        exact h1 hne (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
      rw [h5]
      exact le_top
    · exact h2 _ (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_false, Br.sPi])

theorem selCore : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D), NChTie D C → TriplesGood D → GoodPtRow D →
    ResAbsIrr D → SameTwist D C →
    ∀ ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ i, ∀ π ∈ D.nd.Zgood i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π)) → SelCore D C ρ := by
  intro hC D C hTie hT hG hR hS ρ hρ i π hπ
  obtain ⟨f, hf, hs⟩ := hS.exists_heq i
  obtain ⟨s, h1, h2, h3⟩ := sel_at hC D hT hG hR i (ρ i) π hπ (hρ i π hπ) _ (hTie.twOf_eq i) _ _ f hf hs
  rw [hTie.Q_eq i] at h3
  exact ⟨s, h1, h2.trans (hTie.twSide_eq i), h3⟩

end GlobalTheory.PtSel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_exponent_kills_invariants_of_good : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  first | exact @GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | exact GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | (intros; apply GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_cokernel_killed_by_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  first | exact @GlobalTheory.NL.CokerFin.coker_killed | exact GlobalTheory.NL.CokerFin.coker_killed | (intros; apply GlobalTheory.NL.CokerFin.coker_killed <;> assumption)
end

