module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem finrank_orth_add_finrank (U : Submodule E S.V) : finrank E (orth S U) + finrank E U = finrank E S.V := by
  classical
  let b := Module.finBasis E U
  let ℓ : Fin (finrank E U) → Module.Dual E S.V := fun a => S.hT (b a : S.V)
  have hind : LinearIndependent E (fun a => (b a : S.V)) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span E (Set.range fun a => (b a : S.V)) = U := by
    have : (Set.range fun a => (b a : S.V)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hℓ : LinearIndependent E ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h1 : S.hT (∑ a, star (c a) • (b a : S.V)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smulₛₗ, starRingEnd_apply, star_star]
    have h2 : ∑ a, star (c a) • (b a : S.V) = 0 := S.nondeg.1 _ (fun y => by rw [h1]; rfl)
    have h3 := Fintype.linearIndependent_iff.1 hind _ h2 a
    simpa using h3
  have hΦ : finrank E (Submodule.span E (Set.range ℓ)) = finrank E U := by
    rw [finrank_span_eq_card hℓ]; simp
  have hco : (Submodule.span E (Set.range ℓ)).dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      have hle : U ≤ LinearMap.ker (S.hT.flip v) := by
        rw [← hspan]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        have := h (ℓ a) (Submodule.subset_span ⟨_, rfl⟩)
        simpa [ℓ] using this
      intro x hx
      simpa using hle hx
    · intro h φ hφ
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨a, rfl⟩
        exact h _ (b a).2
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro c x _ hx
        simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range ℓ))
  rw [hΦ, hco] at this
  omega

theorem isCompl_orth_of_nondegenerate (U : Submodule E S.V) (hU : U ⊓ orth S U = ⊥) : IsCompl U (orth S U) := by
  have hd : Disjoint U (orth S U) := disjoint_iff.2 hU
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_disjoint U (orth S U) ?_ hd)⟩
  have := finrank_orth_add_finrank S U
  omega

end LinAlg

section Ext

variable (D : D7)

theorem embedding_isometry_W (x y : (D.sp.X 0).V) : (VS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (lt_of_lt_of_le (by norm_num) D.R.two_le_m) x y

theorem embedding_W_injective : Function.Injective (D.sp.iXY 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
  rw [← embedding_isometry_W D y x, hx, map_zero]

theorem isCompl_range_orth_range : IsCompl (LinearMap.range (D.sp.iXY 0)) (orth (hS D) (LinearMap.range (D.sp.iXY 0))) := by
  refine isCompl_orth_of_nondegenerate _ _ ?_
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  have h0 : x = 0 := (D.sp.X 0).nondeg.2 x (fun y => by rw [← embedding_isometry_W D y x]; exact hx' _ ⟨y, rfl⟩)
  rw [h0, map_zero]
  exact Submodule.zero_mem _

def conjEquivOnEmbeddingRange (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :
    LinearMap.range (D.sp.iXY 0) ≃ₗ[D.host.E] LinearMap.range (D.sp.iXY 0) :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm ≪≫ₗ γ ≪≫ₗ LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)

def extendByIdentity (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm ≪≫ₗ
    ((conjEquivOnEmbeddingRange D γ).prodCongr (LinearEquiv.refl _ _)) ≪≫ₗ Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)

theorem extendByIdentity_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    extendByIdentity D γ (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ w) + b := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold extendByIdentity
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.coe_prodEquivOfIsCompl']
  unfold conjEquivOnEmbeddingRange
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_apply]
  rfl

theorem exists_decomp_range_orth (x : (VS D).V) : ∃ (w : (D.sp.X 0).V) (b : (VS D).V),
    b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) ∧ x = D.sp.iXY 0 w + b := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).surjective x
  obtain ⟨w, hw⟩ := a.2
  exact ⟨w, b.1, b.2, by rw [Submodule.coe_prodEquivOfIsCompl', hw]⟩

theorem inner_decomp_orth_range (w w' : (D.sp.X 0).V) (b b' : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) (hb' : b' ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (VS D).hT (D.sp.iXY 0 w + b) (D.sp.iXY 0 w' + b') = (D.sp.X 0).hT w w' + (VS D).hT b b' := by
  have h1 : (VS D).hT (D.sp.iXY 0 w) b' = 0 := (Formalism.MainNotions.mem_orth_iff _ _).1 hb' _ ⟨w, rfl⟩
  have h2 : (VS D).hT b (D.sp.iXY 0 w') = 0 := Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 hb _ ⟨w', rfl⟩)
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [embedding_isometry_W, h1, h2]
  ring

theorem extendByIdentity_mem_isom (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ isom (VS D).hT := by
  intro x y
  obtain ⟨w, b, hb, rfl⟩ := exists_decomp_range_orth D x
  obtain ⟨w', b', hb', rfl⟩ := exists_decomp_range_orth D y
  rw [extendByIdentity_apply D γ w b hb, extendByIdentity_apply D γ w' b' hb', inner_decomp_orth_range D _ _ _ _ hb hb',
    inner_decomp_orth_range D _ _ _ _ hb hb', hγ w w']

theorem extendByIdentity_symm_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (extendByIdentity D γ).symm (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ.symm w) + b := by
  rw [LinearEquiv.symm_apply_eq, extendByIdentity_apply D γ _ b hb, LinearEquiv.apply_symm_apply]

theorem extendByIdentity_symm_fix_orth (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) : (extendByIdentity D γ).symm b = b := by
  have := extendByIdentity_symm_apply D γ 0 b hb
  simpa using this

end Ext

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)


include hw₁ hgen in
theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha


include hw₁ hgen hann in
theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    exact (Ideal.absNorm_eq_natCard P).symm
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_exp_nd {m f s r c mx cf C : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hf : 1 ≤ f) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hmx : 0 ≤ mx) (hcf : cf ≤ m) (hC : 4 + (c ^ 2 + 2 * mx) * (6 * c + 2) ≤ C ^ 2) :
    1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by
  have hm2 : 2 ≤ m := by linarith
  set Mx : ℝ := (s + m) * m with hMx
  have hMx1 : m ^ 2 ≤ Mx := by rw [hMx]; nlinarith
  have hMx2 : m ≤ Mx := by nlinarith
  have hMx0 : 0 ≤ Mx := by nlinarith
  have hr1 : r + 1 = m / 2 := by linarith
  have hrm : r ^ 2 ≤ Mx := by nlinarith
  have e1 : c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1)) = (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by rw [hr1]; ring
  have b1 : c * cf ≤ c * Mx := mul_le_mul_of_nonneg_left (hcf.trans hMx2) hc
  have b2 : c * r ^ 2 ≤ c * Mx := mul_le_mul_of_nonneg_left hrm hc
  have b3 : 6 * (r + 1) ^ 2 ≤ 2 * Mx := by rw [hr1]; nlinarith
  have br : 2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2 ≤ (6 * c + 2) * Mx := by
    have : c * (s + m) * m = c * Mx := by rw [hMx]; ring
    rw [this]; nlinarith
  have hK0 : 0 ≤ m ^ 3 * f := by positivity
  have hp0 : 0 ≤ (c ^ 2 + 2 * mx) * (m ^ 3 * f) := by positivity
  have t1 : (c ^ 2 + 2 * mx) * (m ^ 3 * f) * (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤
      (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := mul_le_mul_of_nonneg_left br hp0
  have hKM : 0 ≤ m ^ 3 * f * Mx := by positivity
  have t2 : 1 + 12 * f * (r + 1) ^ 2 ≤ 4 * (m ^ 3 * f * Mx) := by
    rw [hr1]
    have a1 : f * m ^ 2 ≤ m ^ 3 * f * Mx := by
      have : (1 : ℝ) ≤ m * Mx := by nlinarith
      calc f * m ^ 2 = f * m ^ 2 * 1 := by ring
        _ ≤ f * m ^ 2 * (m * Mx) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = m ^ 3 * f * Mx := by ring
    have a2 : (1 : ℝ) ≤ f * m ^ 2 := by nlinarith
    nlinarith
  have t3 : (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) ≤ C ^ 2 * (m ^ 3 * f * Mx) :=
    mul_le_mul_of_nonneg_right hC hKM
  rw [e1]
  calc 1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 + 2 * mx) * (m ^ 3 * f) *
        (2 * (c * (s + m) * m + c * cf) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2)
      ≤ 4 * (m ^ 3 * f * Mx) + (c ^ 2 + 2 * mx) * (m ^ 3 * f) * ((6 * c + 2) * Mx) := add_le_add t2 t1
    _ = (4 + (c ^ 2 + 2 * mx) * (6 * c + 2)) * (m ^ 3 * f * Mx) := by ring
    _ ≤ C ^ 2 * (m ^ 3 * f * Mx) := t3
    _ = C * m ^ 2 * f * (C * (s + m) * m ^ 2) := by rw [hMx]; ring

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_m_cast (D : D7) : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by
  have := d_m_eq D; exact_mod_cast this

theorem rows_cF_le {C' Cl Cg cb Cu cT CT C0 A : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    cF D.R.f ≤ D.R.m := by
  obtain ⟨_, _, _, _, h5, _⟩ := hH.1.1
  have h5' : Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.rS : ℝ) := h5
  have hr : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hH.2.1.1
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hsq : Real.sqrt (D.R.rS : ℝ) ≤ D.R.rS := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hl2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log (D.R.f : ℝ) := Real.log_nonneg hf
  have e : cF D.R.f = 2 + Real.log (D.R.f : ℝ) / Real.log 2 := by
    unfold cF lg2f Real.logb
    rw [Real.log_mul (by norm_num) (by linarith)]
    field_simp
    ring
  have h2 : Real.log (D.R.f : ℝ) / Real.log 2 ≤ 2 * Real.log (D.R.f : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [e, rows_m_cast]
  linarith

theorem rows_one_le_NT (D : D7) (w : D.what₂.Word) : 1 ≤ NT D w := by
  unfold NT
  exact one_le_pow₀ (by exact_mod_cast (D.mem w).A.T_prime.pos)

theorem rows_XiP_le (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c Ch C : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    (hC : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) (s : ℕ) :
    XiS D w (rows_P D large₂ c Ch ^ 2) c s ≤ XiB D large₂ w C s := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hP1 := rows_P_one_le D large₂ c Ch
  have hN := rows_one_le_NT D w
  have hPH : rows_P D large₂ c Ch ^ 2 ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) := by
    unfold rows_P Hb
    rw [rows_rpow_pow hb0, ← Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  unfold XiB XiS Xi
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ rows_P D large₂ c Ch ^ 2 * NT D w := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP1) hN
    have h2 : rows_P D large₂ c Ch ^ 2 * NT D w ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w :=
      mul_le_mul_of_nonneg_right hPH (by linarith)
    have h3 : (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ)) ≤
        (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (C * (D.R.k : ℝ)) :=
      calc (rows_P D large₂ c Ch ^ 2 * NT D w) ^ (c * (D.R.k : ℝ))
          ≤ (Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.m : ℝ)) * NT D w) ^ (c * (D.R.k : ℝ)) :=
            Real.rpow_le_rpow (by linarith) h2 (by positivity)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (h1.trans h2) (by gcongr)
    have h4 : (c * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) ≤ (C * (D.R.k : ℝ)) ^ (D.R.k * D.R.f) :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    exact mul_le_mul h4 h3 (Real.rpow_nonneg (by linarith) _) (by
      have : 0 ≤ C := hc.trans hcC
      positivity)
  · exact le_rfl

theorem rows_ndB_le {C' Cl Cg cb Cu cT CT C0 A c Ch δ C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (s : ℕ) :
    rows_ndB D large₂ u u' c Ch δ s ≤
      LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) * rDD D u' := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := gg D)
    (v := D.host.v) (Γ := GamS D large₂) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := δ) (rD := rDD D u') (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by linarith) (by linarith) hGam0.le hc hcC hC1 hδ0 hδ
    (rows_rDD_nonneg D u') (rows_XiS_nonneg D u (by positivity) hc s) (rows_XiP_le D large₂ u hc hcC hpe2 s)
    (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold rows_ndB rows_R rows_Phi
  exact this

theorem rows_RowBound_mono {Q : D.s.Pair u u' → Prop} {B B' : ℝ} (h : RowBound X Y Q B) (hB : B ≤ B')
    (hdim : 0 ≤ dimPi (hc := D.hcW) u) : RowBound X Y Q B' := fun S hS =>
  (h S hS).trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (rows_massRows_nonneg Y) hdim))

theorem rows_RowsND_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hδ : δ ≤ 1) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsND X Y C := by
  intro s hs hsk
  refine rows_RowBound_mono Y (rows_ND_record Y h s hs hsk ?_) (rows_ndB_le h.hH h.hc hcC hC1 h.hδ hδ hC s) h.hdim.le
  have : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
    have := h.hc
    gcongr
  linarith

end Rec

end Formalism.MainNotions.BridgeLemma₂

end
end

