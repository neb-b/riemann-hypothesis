module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_out_inv_congr {A : Type} [Group A] (U V : Subgroup A) (e : MulAut A) (f : A → ℂ)
    (he : ∀ a, a ∈ U ↔ e a ∈ V) (hV : ∀ v ∈ V, ∀ a, f (v * a) = f a) :
    ∑ᶠ y : A ⧸ U, f (e y.out)⁻¹ = ∑ᶠ y : A ⧸ V, f y.out⁻¹ := by
  let E : A ⧸ U ≃ A ⧸ V := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he, map_mul, map_inv]
    rfl)
  have hE : ∀ a : A, E (QuotientGroup.mk a) = QuotientGroup.mk (e a) := fun a => rfl
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun y => ?_
  have h1 : E y = QuotientGroup.mk (e y.out) := by
    rw [← hE, QuotientGroup.out_eq']
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V (e y.out)
  rw [h1, hv, mul_inv_rev, hV _ (V.inv_mem v.2)]

theorem chainSum_of_unimod : Unimod → ChainIndex → ChainSum := by
  classical
  intro hUn hCh A _ U c Q d f hc hQ hind hex hV hU hfin
  have hchain := hCh A U c Q hc hind
  have hmem : ∀ (j : ℤ) (a : A), a ∈ U.comap (c ^ j).toMonoidHom ↔ (c ^ j) a ∈ U := fun j a => Iff.rfl
  have hmono : ∀ j j' : ℤ, j ≤ j' → U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ j').toMonoidHom := by
    intro j j' h
    have := (hchain j (j' - j).toNat).1
    rwa [show j + ((j' - j).toNat : ℤ) = j' by omega] at this
  have h0 : U.comap (c ^ (0 : ℤ)).toMonoidHom = U := by
    ext a
    rw [hmem, zpow_zero, MulAut.one_apply]
  choose J hJ using hex
  obtain ⟨k, hkd, hk⟩ : ∃ k : ℕ, d ≤ k ∧ ∀ y : A ⧸ U, f y.out ≠ 0 → J y.out ≤ k := by
    refine ⟨hfin.toFinset.sup (fun y => J y.out) + d.toNat, by omega, fun y hy => ?_⟩
    exact le_trans (Finset.le_sup (f := fun y : A ⧸ U => J y.out) (hfin.mem_toFinset.2 hy)) (Nat.le_add_right _ _)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, d + l = k := ⟨(k - d).toNat, by omega⟩
  have hUΓ : U ≤ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    have := hmono 0 k (by omega)
    rwa [h0] at this
  have iU : U.relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ k := by
    have := (hchain 0 k).2
    rwa [h0, zero_add] at this
  have iV : (U.comap (c ^ d).toMonoidHom).relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ l := by
    have := (hchain d l).2
    rwa [hl] at this
  have hsupp : ∀ a, f a ≠ 0 → a ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    intro a ha
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U a
    have h1 : f (QuotientGroup.mk a : A ⧸ U).out ≠ 0 := by rwa [hu, hU _ u.2]
    have h2 : (QuotientGroup.mk a : A ⧸ U).out ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
      refine hmono (J (QuotientGroup.mk a : A ⧸ U).out : ℕ) k (by exact_mod_cast hk _ h1) ?_
      rw [hmem, zpow_natCast]
      exact hJ _
    rw [hu] at h2
    exact (Subgroup.mul_mem_cancel_right _ (hUΓ u.2)).1 h2
  have key := hUn A _ U (U.comap (c ^ d).toMonoidHom) f hUΓ (hmono d k hkd)
    (by rw [iU]; exact pow_ne_zero _ hQ) (by rw [iV]; exact pow_ne_zero _ hQ) hsupp
    (fun v hv => hV v hv) hU
  rw [finsum_out_inv_congr U (U.comap (c ^ d).toMonoidHom) (c ^ (-d)) f (fun a => by
    rw [hmem, ← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply])
    (fun v hv => hV v hv)]
  rw [iU, iV] at key
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hpow : (Q : ℂ) ^ l = (Q : ℂ) ^ k * (Q : ℂ) ^ (-d) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hQ']
    congr 1
    omega
  push_cast at key
  rw [hpow, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ hQ') key

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndex
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by
  ext a
  have h : (c ^ (j + 1)) a = c ((c ^ j) a) := by
    rw [add_comm, zpow_add, zpow_one, MulAut.mul_apply]
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]
  constructor
  · intro ha
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxa⟩
    rw [← c.injective hxa]
    exact hx

theorem chain_step {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective

theorem chainIndex : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6supp : DivisorSupportCondition := by
  intro q _ U V E f g hc n m i j a b ha hb
  exact GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q i j) ((_root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q i)).2.1)
    ((_root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q j)).2.1) f g hc rfl a b ha hb

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWordLeIntegralOfAevalCasimirEqZero
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.DerivBoundIntegral

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

noncomputable def wordEnd (w : List 𝔤) : Module.End ℂ (h.smoothFuns (F := ℂ)) :=
  (w.map (h.rightDerivEnd (F := ℂ))).prod

theorem coe_wordEnd (w : List 𝔤) (f : h.smoothFuns (F := ℂ)) :
    ((wordEnd h w f : h.smoothFuns (F := ℂ)) : G → ℂ) = w.foldr h.rightDeriv (f : G → ℂ) := by
  induction w with
  | nil => simp [wordEnd]
  | cons X w ih =>
    simp only [wordEnd, List.map_cons, List.prod_cons, Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
      List.foldr_cons] at ih ⊢
    rw [ih]

theorem wordEnd_mem (w : List 𝔤) :
    wordEnd h w ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := by
  apply Subalgebra.list_prod_mem
  intro x hx
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
  exact Algebra.subset_adjoin ⟨X, rfl⟩

end GlobalTheory.DerivBoundIntegral

namespace GlobalTheory


open GlobalTheory.DerivBoundIntegral in
theorem derivWord_le_integral_of_aeval_casimir_eq_zero :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  obtain ⟨Kc, hKc, hD⟩ := GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian 𝔸 G 𝔤 h d b P hP
  obtain ⟨ρ, hρ, hH⟩ := _root_.GlobalTheory.setIntegral_norm_prodExp_mul_le_haar 𝔸 G 𝔤 h d b μ hμ
  obtain ⟨C₀, K, hC₀, hK, hHK⟩ := hH Kc hKc
  obtain ⟨N, lw, κ, hκ, hrep⟩ := _root_.GlobalTheory.exists_sobolev_representation_prodExp 𝔸 G 𝔤 h ρ hρ d (⇑b)
  refine ⟨K, hK, fun l => ?_⟩
  have hS : ∀ i, ∃ S : ℝ, 0 ≤ S ∧ ∀ t, ‖κ i t‖ ≤ S := by
    intro i
    have hcs : HasCompactSupport (κ i) :=
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2
    obtain ⟨S, hS⟩ := (hκ i).1.bounded_above_of_compact_support hcs
    exact ⟨max S 0, le_max_right _ _, fun t => (hS t).trans (le_max_left _ _)⟩
  choose S hS0 hS using hS
  choose C hC0 hC using fun i => hD (lw i ++ l)
  set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔ
  set A := Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) with hA
  have hΔmem : Δ ∈ A := Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
  have hPmem : Polynomial.aeval Δ P ∈ A := by
    have := Polynomial.aeval_algHom_apply A.val (⟨Δ, hΔmem⟩ : A) P
    simp only [Subalgebra.coe_val] at this
    rw [this]
    exact (Polynomial.aeval (⟨Δ, hΔmem⟩ : A) P).2
  refine ⟨∑ i, C i * (S i * C₀), fun f hf => ?_⟩
  set I := ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ with hI
  have hfc : Continuous (f : G → ℂ) := by
    letI := h.chartedSpace
    exact ContMDiff.continuous f.2

  have hFs : h.IsSmoothFun ((wordEnd h l f : h.smoothFuns (F := ℂ)) : G → ℂ) := (wordEnd h l f).2
  have hrep1 := hrep _ hFs 1
  simp only [coe_wordEnd] at hrep1
  rw [hrep1]
  have hterm : ∀ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
      (1 * h.prodExp (⇑b) t)‖ ≤ C i * (S i * C₀) * I := by
    intro i
    obtain ⟨v, hv, hTv⟩ := GlobalTheory.T.leftSmoothing_prodExp_smooth_commute 𝔸 G 𝔤 h d (⇑b) (κ i) (hκ i).1
      ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2) f
    have hkill : Polynomial.aeval Δ P v = 0 := by
      apply Subtype.ext
      funext y
      rw [hTv _ hPmem y, hf]
      simp
    have heq : ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t) = (lw i ++ l).foldr h.rightDeriv (v : G → ℂ) 1 := by
      have e1 := hTv _ (wordEnd_mem h (lw i ++ l)) 1
      simp only [coe_wordEnd] at e1
      rw [e1]
      simp [List.foldr_append]
    rw [heq]
    have hvb : ∀ y ∈ Kc, ‖(v : G → ℂ) (1 * y)‖ ≤ S i * C₀ * I := by
      intro y hy
      rw [one_mul, hv y]
      have hcont : Continuous fun t : Fin d → ℝ => ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ :=
        (hfc.comp ((h.continuous_prodExp (⇑b)).mul continuous_const)).norm
      calc ‖∫ t, κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖
          ≤ ∫ t, ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := norm_integral_le_integral_norm _
        _ = ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro t ht
            have : κ i t = 0 := image_eq_zero_of_notMem_tsupport fun h' => ht ((hκ i).2 h')
            simp [this]
        _ ≤ ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              S i * ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun t => norm_nonneg _
            · exact (continuous_const.mul hcont).continuousOn.integrableOn_compact
                (isCompact_closedBall _ _)
            · refine Filter.Eventually.of_forall fun t => ?_
              simp only [norm_mul]
              exact mul_le_mul_of_nonneg_right (hS i t) (norm_nonneg _)
        _ = S i * ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := integral_const_mul _ _
        _ ≤ S i * (C₀ * I) := mul_le_mul_of_nonneg_left (hHK _ hfc y hy) (hS0 i)
        _ = S i * C₀ * I := by ring
    have := hC i v hkill 1 (S i * C₀ * I) hvb
    calc _ ≤ C i * (S i * C₀ * I) := this
      _ = _ := by ring
  calc ‖∑ i, ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖
      ≤ ∑ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * (S i * C₀) * I := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, C i * (S i * C₀)) * I := (Finset.sum_mul _ _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
section
noncomputable section

open NumberField

namespace GlobalTheory.HeckePoisson

variable {K : Type} [Field K] [NumberField K] {I : Type}

def embA (φ : I → K →+* ℂ) : 𝓞 K →+ EuclideanSpace ℂ I where
  toFun α := WithLp.toLp 2 (GlobalTheory.HeckeTheta.emb φ (α : K))
  map_zero' := by ext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by ext i; simp [GlobalTheory.HeckeTheta.emb]

def lat (φ : I → K →+* ℂ) (M : Ideal (𝓞 K)) : Submodule ℤ (EuclideanSpace ℂ I) :=
  AddSubgroup.toIntSubmodule (M.toAddSubgroup.map (embA φ))

theorem embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl

theorem mem_lat {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def kappa [Fintype I] (n : I → ℤ) : ℂ := ((2 : ℂ) ^ Fintype.card I)⁻¹ * (-Complex.I) ^ (∑ i, (n i).natAbs)

end GlobalTheory.HeckePoisson
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
section
noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix Polynomial GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_trace_of_isIntegral_matrix {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix n n K →ₐ[ℤ] Matrix n n L := ((algebraMap K L).mapMatrix).toIntAlgHom
  have hM' : IsIntegral ℤ (φ M) := hM.map φ
  have htr : algebraMap K L M.trace = (φ M).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := K) (B := L) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum L (φ M) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM'
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap ℤ L)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (φ M) (p.map (algebraMap ℤ L)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix n n L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_of_mapsTo_lattice (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (Y : Matrix (Fin r) (Fin r) E)
    (hY : ∀ x ∈ Λ, Y *ᵥ x ∈ Λ) : IsIntegral (𝓞 E) Y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  let f : Module.End (𝓞 E) Λ :=
    { toFun := fun x => ⟨Y *ᵥ (x : Fin r → E), hY _ x.2⟩
      map_add' := fun x y => by ext1; simp [mulVec_add]
      map_smul' := fun c x => by ext1; simp [mulVec_smul] }
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have key : ∀ q : (𝓞 E)[X], ∀ x (hx : x ∈ Λ), aeval Y q *ᵥ x = ((aeval f q ⟨x, hx⟩ : Λ) : Fin r → E) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x hx
      simp only [aeval_C]
      rw [show (algebraMap (𝓞 E) (Matrix (Fin r) (Fin r) E)) a = Matrix.diagonal (fun _ => (a : E)) from rfl]
      ext i
      rw [mulVec_diagonal, Module.algebraMap_end_apply]
      rfl
    | add p q hp hq =>
      intro x hx
      rw [map_add (f := _), add_mulVec, hp x hx, hq x hx, map_add (f := _)]
      rfl
    | monomial n a ih =>
      intro x hx
      have e1 : aeval Y (C a * X ^ (n + 1)) = aeval Y (C a * X ^ n) * Y := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      have e2 : aeval f (C a * X ^ (n + 1)) = aeval f (C a * X ^ n) * f := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [e1, e2, ← mulVec_mulVec, ih _ (hY x hx)]
      rfl
  have hker : ∀ v, aeval Y p *ᵥ v = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => rw [key p x hx, hp0]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mulVec_smul, hx, smul_zero]
  have hA : aeval Y p = 0 := by
    apply Matrix.toLin'.injective
    ext v i
    simp [Matrix.toLin'_apply, hker]
  exact ⟨p, hp, by rw [← aeval_def]; exact hA⟩

theorem isIntegral_trace_of_mem_endLat [IsCMField E] (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E) (hS : SelfDualLat G Λ)
    (hY : Y ∈ endLat Λ) : IsIntegral ℤ Y.trace :=
  isIntegral_trace_of_isIntegral_matrix Y
    (@isIntegral_trans ℤ (𝓞 E) _ _ _ _ _ _ _ AddCommGroup.intIsScalarTower _ Y
      (isIntegral_of_mapsTo_lattice Λ hS.2.2.1 hS.2.2.2.1 Y (mem_endLat.mp hY)))

theorem trace_integral_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E),
    SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace :=
  fun _ _ _ _ _ G Λ Y hS hY => isIntegral_trace_of_mem_endLat G Λ Y hS hY

end GlobalTheory.LieDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeLocalization

theorem cone_kinj (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (mappingCone (resMap R φ)).IsKInjective := by
  haveI := (_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.1
  haveI := (_root_.GlobalTheory.EtC.ResBasic.res_basic R G).2.1
  haveI := (_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.2.1
  haveI := (_root_.GlobalTheory.EtC.ResBasic.res_basic R G).2.2.1
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

theorem cone_loc (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) :
    ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec ((mappingCone (resMap R φ)).X n) U),
      Sec.map ((mappingCone (resMap R φ)).d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ a : Sec ((mappingCone (resMap R φ)).X (n - 1)) V,
        Sec.map ((mappingCone (resMap R φ)).d (n - 1) n) a = Sec.res g b := by
  intro U hU n b hb
  exact _root_.GlobalTheory.EtC.cone_sec_exact R (resMap R φ) U n (GlobalTheory.T.mappingCone_resolution_localChase_on_support R E φ hφ U hU n) b hb

end GlobalTheory.EtC.ConeLocalization

theorem GlobalTheory.EtC.a10 : GlobalTheory.EtC.A10 := by
  intro R _ E F G φ hφ
  haveI := GlobalTheory.EtC.ConeLocalization.cone_kinj R φ
  have hC := GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support R E (mappingCone (resMap R φ)) (GlobalTheory.EtC.ConeLocalization.cone_loc R E φ hφ)
  have ex := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R ((chains R).obj E) (resMap R φ)
  intro n
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((ex m).2.2 x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoactionEqAddOfPrimitiveStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coaction_eq_add_of_primitive : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  first | exact @GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive | exact GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive | (intros; apply GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive <;> assumption)
end

