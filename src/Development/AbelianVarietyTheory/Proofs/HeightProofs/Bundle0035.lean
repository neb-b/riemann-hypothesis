module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsometryAgreeing
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfLift

theorem exists_isometry_agreeing {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La)
    (h : ∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Dw.ModN l.M (s.f l.M a - g a) := by
  have hle : ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤
      (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).comap f := fun f => by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw l
    (LinearEquiv.ofLinear (Submodule.mapQ _ _ g (hle g)) (Submodule.mapQ _ _ g' (hle g'))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).2))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).1)))
  refine ⟨s, h1, fun a ha => ?_⟩
  have key : ∀ x, s.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 (h2 x)
  refine Submodule.smul_induction_on ha (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [map_smul, map_smul, ← smul_sub]
    exact GlobalTheory.LevelIsometry.modN_smul_of_mem_smul Dw l hr (key y)
  · rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact GlobalTheory.SimAlg.modN_add hy hz

theorem add_sub_eq_nsmul {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) :
    x + N • e + N • w - x = N • (e + w) := by
  rw [smul_add]
  abel

theorem exists_unitary_inducing : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V ι → ∀ g g' : Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ∧ g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ∃ u ∈ GfC V, gLat V u = latHat V ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1, (finHom V u).1.mulVec (finVec V (ι a)) - finVec V (ι (g a)) = (l.M : ℕ) • w := by
  intro D H Dw l V ι hι g g' h
  obtain ⟨s, hν, hs⟩ := exists_isometry_agreeing Dw l g g' h
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw ι hι.emb hι.isom s hν
  obtain ⟨b, hb, u, hu, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
  have hb' : finHom V b = 1 := hb
  have hf : finHom V u = finHom V κ := by rw [e, map_mul, hb', one_mul]
  obtain ⟨-, m2, -, m4⟩ := GlobalTheory.Member.latG_move D V
  have hL : latG V 1 = latG V u := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V (hκ.symm.trans (m2 u κ hf).2.symm)
  have hc := m4 1 u hL
  rw [inv_one, one_mul] at hc
  refine ⟨u, hu, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, fun a ha => ?_⟩
  obtain ⟨c, hc'⟩ := hs a ha
  obtain ⟨w, hw, ew⟩ := hκs l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
  have hm : finVec V (ι c) ∈ latGHat V 1 :=
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.emb.2 ▸ LinearMap.mem_range_self ι c)
  refine ⟨finVec V (ι c) + w, add_mem hm hw, ?_⟩
  have h2 : finVec V (ι (s.f l.M a)) = finVec V (ι (g a)) + l.M • finVec V (ι c) := by
    rw [sub_eq_iff_eq_add'.1 hc', map_add (f := _), map_nsmul]
    funext i
    simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
    congr 1
    exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _
  rw [hf, ew, h2]
  exact add_sub_eq_nsmul _ _ _ _

end GlobalTheory.HalfLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSectionMaps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.SecEval

theorem exists_quot_maps {K L C : Type*} [CommRing K] [CommRing L] [CommRing C] [Algebra K L] [Algebra K C]
    (A : Subalgebra K L) (J : Ideal A) (H : Submodule A L) (Λ : L →ₐ[K] C) (hJ : ∀ r ∈ J, Λ (r : L) = 0) :
    ∃ (ψ : (A ⧸ J) →ₐ[K] C) (Ψ : (H ⧸ J • (⊤ : Submodule A H)) →ₗ[K] C),
      (∀ x : A, ψ (Ideal.Quotient.mk J x) = Λ x) ∧ ∀ y : H, Ψ (Submodule.Quotient.mk y) = Λ y := by
  have hH : ∀ z ∈ J • (⊤ : Submodule A H), Λ (z : L) = 0 := by
    intro z hz
    refine Submodule.smul_induction_on (p := fun z : H => Λ (z : L) = 0) hz ?_ ?_
    · intro r hr m _
      rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
      have : Λ (algebraMap A L r) = 0 := hJ r hr
      rw [this, zero_mul]
    · intro x y hx hy
      rw [Submodule.coe_add, map_add (f := _), hx, hy, add_zero]
  let l : H →ₗ[K] C := Λ.toLinearMap ∘ₗ (H.subtype.restrictScalars K)
  refine ⟨Ideal.Quotient.liftₐ J (Λ.comp A.val) hJ,
    (((J • (⊤ : Submodule A H)).restrictScalars K).liftQ l (fun z hz => hH z hz)) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K (J • (⊤ : Submodule A H))).symm.toLinearMap,
    fun x => rfl, fun y => rfl⟩

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem exists_evalRp (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)
    (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C)
    (hχ : ∀ (a : B.KO) (f : X.Forms), χ (a • f) =
      algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) :
    ∃ Θ : Rp X la N →ₐ[Kp X la N] C, ∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F := by
  letI : Algebra (X.Kl la) C := ((algebraMap (Kp X la N) C).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  letI : Algebra B.KO C := ((algebraMap (Kp X la N) C).comp
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X.Kl la) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X.Kl la) (Kp X la N) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X.Forms →ₐ[B.KO] C :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X.Vl la →ₐ[X.Kl la] C :=
    Algebra.TensorProduct.lift (Algebra.ofId (X.Kl la) C) g (fun _ _ => Commute.all _ _)
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId (Kp X la N) C) vl (fun _ _ => Commute.all _ _), fun F => ?_⟩
  rw [emb_apply]
  erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
  erw [map_one, map_one, one_mul, one_mul]
  rfl

theorem exists_section_maps : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL u : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C), (∀ (a : B.KO) (f : X.Forms), χ (a • f) = algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) → (∀ i : Fin (WeightFamilies.dimY D j), ∑ k, algebraMap (Kp X la N) C (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (i.succ, k))) * χ (X.inc wL (w k)) = 0) → IsUnit (∑ k, algebraMap (Kp X la N) C (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (0, k))) * χ (X.inc wL (w k))) → ∃ (Θ : Rp X la N →ₐ[Kp X la N] C) (ψ : OsK X la w →ₐ[Kp X la N] C) (Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C), (∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F) ∧ IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) ∧ (∀ (x : OsK X la w) (a : SectionSheafQuotient X la w u), Ψ (x • a) = ψ x * Ψ a) ∧ (∀ (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))), ψ (toOsK X la w (fr0 X la w k g)) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g) ∧ ∀ f : ↥(Vw X la N u), Ψ (rho0 X la w u f) = Θ f := by
  intro D B P j X la N wL u w C _ _ χ hχ h0 h1
  obtain ⟨Θ, hΘ⟩ := exists_evalRp X la N C χ hχ
  have hsec : ∀ i, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) = ∑ k, algebraMap (Kp X la N) C
      (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) * χ (X.inc wL (w k)) := by
    intro i
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hΘ, Algebra.smul_def]
  have hu : IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := by rw [hsec]; exact h1
  have hu' : IsUnit ((Θ : Rp X la N →+* C) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := hu
  let Λ₀ : Lw X la w →+* C := IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) hu'
  have hΛ₀ : ∀ r, Λ₀ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := fun r => IsLocalization.lift_eq _ r
  let Λ : Lw X la w →ₐ[Kp X la N] C :=
    { Λ₀ with
      commutes' := fun c => by
        show Λ₀ (algebraMap (Kp X la N) (Lw X la w) c) = _
        rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), hΛ₀, AlgHom.commutes] }
  have hΛ : ∀ r, Λ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := hΛ₀
  have hinv : Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) * Λ (w0inv X la w) = 1 := by
    rw [← hΛ, ← map_mul, section_mul_inverse_eq_one, map_one]
  have hfr : ∀ (k : ℕ) (g : Rp X la N),
      Λ (frac X la w k g) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g := by
    intro k g
    rw [frac_apply, map_mul, map_pow, hΛ, mul_assoc, ← mul_pow, mul_comm (Λ _), hinv, one_pow, mul_one]
  have hJ : ∀ r ∈ Jid X la w, Λ (r : Lw X la w) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [coe_sfr, frac_apply, map_mul, hΛ, hsec, h0 i, zero_mul]
    | zero => simp
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]
  obtain ⟨ψ₀, Ψ₀, hψ₀, hΨ₀⟩ := exists_quot_maps (Frac0 X la w) (Jid X la w) (HK X la w u) Λ hJ
  let ψ : OsK X la w →ₐ[Kp X la N] C := ψ₀
  let Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C := Ψ₀
  have hψ : ∀ x, ψ (toOsK X la w x) = Λ x := hψ₀
  have hΨ : ∀ y, Ψ (toA0K X la w u y) = Λ y := hΨ₀
  refine ⟨Θ, ψ, Ψ, hΘ, hu, ?_, ?_, ?_⟩
  · intro x a
    obtain ⟨x, rfl⟩ := toOsK_surjective X la w x
    obtain ⟨y, rfl⟩ := reductionMap_surjective X la w u a
    have e : toOsK X la w x • toA0K X la w u y = toA0K X la w u (x • y) := by
      rw [map_smul]
      exact algebraMap_smul (OsK X la w) x _
    rw [e, hΨ, hΨ, hψ, Submodule.coe_smul, Algebra.smul_def, map_mul]
    rfl
  · intro k g
    rw [hψ, coe_weightZeroFraction, hfr]
  · intro f
    rw [restriction_apply_eq_reduction, hΨ, coe_toHK0, hΛ]

end GlobalTheory.SecEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open IsLocalRing

section
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem mem_maximalIdeal_iff (x : la.adicCompletionIntegers K) :
    x ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      Valued.v (x : la.adicCompletion K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h1 : Valued.v (x : la.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K la).1 x.2
  constructor
  · intro h
    have h2 := lt_of_le_of_ne h1 h
    rcases eq_or_ne (Valued.v (x : la.adicCompletion K)) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
  · intro h h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega

theorem algebraMap_injective :
    Function.Injective (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) := by
  intro a b h
  have h1 := congrArg (fun x : la.adicCompletionIntegers K => (x : la.adicCompletion K)) h
  simp only [Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K (la.adicCompletion K)).injective h1)

theorem map_asIdeal :
    Ideal.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) la.asIdeal =
      maximalIdeal (la.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff, Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO, Formalism.MainNotions.Gaps.LocalGlobalPassage.val_alg,
      HeightOneSpectrum.valuation_of_algebraMap, la.intValuation_le_pow_iff_mem, pow_one]
    exact ha
  · intro x hx
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    obtain ⟨d, hd⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_factor (K := K) la hπ 1 x
      ((mem_maximalIdeal_iff la x).1 hx)
    rw [hd, pow_one]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem exists_sub_mem (x : la.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, x - algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈
      maximalIdeal (la.adicCompletionIntegers K) := by
  obtain ⟨r, hr⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.approx (K := K) la x 1
  exact ⟨r, (mem_maximalIdeal_iff la _).2 hr⟩

end

theorem isLocalization_rename {σ τ O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] (I : Ideal O₁)
    (e : σ ≃ τ) (Q : Ideal (MvPolynomial τ O₁)) [Q.IsPrime] (hQ : Q = Ideal.map MvPolynomial.C I)
    (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime] (hP : P = Ideal.map MvPolynomial.C I)
    [Algebra (MvPolynomial τ O₁) O₂] [IsLocalization.AtPrime O₂ Q] :
    letI : Algebra (MvPolynomial σ O₁) O₂ :=
      ((algebraMap (MvPolynomial τ O₁) O₂).comp
        (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom).toAlgebra
    IsLocalization.AtPrime O₂ P := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv Q.primeCompl O₂
    (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm
  have hmap : Ideal.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom P = Q := by
    rw [hP, hQ, Ideal.map_map]
    congr 1
    ext a
    simp
  have hmem : ∀ x, (MvPolynomial.renameEquiv O₁ e).toRingEquiv x ∈ Q ↔ x ∈ P := by
    intro x
    have hb := Ideal.comap_map_of_bijective (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom
      (MvPolynomial.renameEquiv O₁ e).toRingEquiv.bijective (I := P)
    rw [hmap] at hb
    rw [← hb]
    exact Iff.rfl
  have hM : Q.primeCompl.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      apply hy
      have := (hmem _).2 hx
      rwa [RingEquiv.apply_symm_apply] at this
    · intro hx
      exact ⟨_, fun hy => hx ((hmem x).1 hy), RingEquiv.symm_apply_apply _ _⟩
  rw [hM] at h
  exact h

theorem gaussRing_completion_rename :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (e : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) ∧ (∀ x : Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) ∧ (∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r)) ∧ (∀ a : B.KO, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.C a)) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ p, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X p)) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (e p)) := by
  intro D B P j X la N D' N' e
  letI alg : Algebra (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) :=
    ((algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) e).toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) p =
      algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (MvPolynomial.rename e p) := fun _ => rfl
  haveI hprime := Formalism.DV.GaussP.gaussIdeal_isPrime (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)
  haveI hloc : IsLocalization.AtPrime (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) :=
    isLocalization_rename (maximalIdeal (X.Ol la)) e (gI X la N) rfl
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl
  obtain ⟨-, f, hf, hflat, hloc', hmax, hres⟩ := GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
    (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la)
    (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
  have hinj₂ : Function.Injective (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (ReciprocityTheory.ChartRestriction.G.T0.laT D' N' la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at h1
    have h2 : p = 0 := by
      have h3 := hinj₂ (h1.symm.trans (map_zero _).symm)
      have h4 := MvPolynomial.rename_injective e e.injective (h3.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (h4.trans (map_zero _).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) s).mul_left_eq_zero.mp h
  letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) D' N' la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) D' N' la
  have hg : Function.Injective
      ((@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _).comp f) :=
    (IsFractionRing.injective (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)).comp hfinj
  let φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg
  have hφ : ∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r) := fun r =>
    IsFractionRing.lift_algebraMap (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg r
  have hφp : ∀ p : ReciprocityTheory.ChartRestriction.G.T0.OT B.KO D' N',
      φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _
        (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
          (MvPolynomial.rename e (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    intro p
    rw [← halg, ← hf, ← hφ, ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hloc', hmax, hres, hφ, ?_, ?_⟩
  · have key : (φ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
        (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')).comp MvPolynomial.C)) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h1 := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h1
      simp only [RingHom.comp_apply]
      rw [h1, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change _ = algebraMap (X.Kl la) (Kp X la N)
        (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun key a
  · intro p
    have h1 := hφp (MvPolynomial.X p)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h1
    exact h1

end GlobalTheory.GaussCompletion
end

