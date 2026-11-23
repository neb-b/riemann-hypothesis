module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBdd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceBdd

theorem trace_mem_valuationSubring_of_pow_bounded {K : Type} [Field K] (O : ValuationSubring K) [IsNoetherianRing O]
    (n : ℕ) (y : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ O) : y.trace ∈ O := by
  classical

  let N : Submodule O (Matrix (Fin n) (Fin n) K) :=
    Submodule.span O (Set.range fun p : Fin n × Fin n => a⁻¹ • Matrix.single p.1 p.2 (1 : K))
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hNfg
  have hpow : ∀ k : ℕ, y ^ k ∈ N := by
    intro k
    rw [Matrix.matrix_eq_sum_single (y ^ k)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hc : a * (y ^ k) i j ∈ O := h k i j
    have : Matrix.single i j ((y ^ k) i j) =
        (⟨a * (y ^ k) i j, hc⟩ : O) • (a⁻¹ • Matrix.single i j (1 : K)) := by
      rw [← algebraMap_smul K (⟨a * (y ^ k) i j, hc⟩ : O), smul_smul, Matrix.smul_single, smul_eq_mul]
      congr 1
      change (y ^ k) i j = a * (y ^ k) i j * a⁻¹ * 1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {y}) ≤ N := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    rintro x hx
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hx
    exact hpow k
  have hint : IsIntegral O y :=
    isIntegral_of_submodule_noetherian _ (isNoetherian_of_le hle) y (Algebra.self_mem_adjoin_singleton O y)
  obtain ⟨p, hpm, hp⟩ := hint

  have hpL : aeval (y.map (algebraMap K (AlgebraicClosure K))) (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
    have h1 : aeval y (p.map (algebraMap O K)) = 0 := by
      rw [aeval_map_algebraMap]; exact hp
    have h2 : aeval (y.map (algebraMap K (AlgebraicClosure K)))
          ((p.map (algebraMap O K)).map (algebraMap K (AlgebraicClosure K))) =
        (Algebra.ofId K (AlgebraicClosure K)).mapMatrix (aeval y (p.map (algebraMap O K))) := by
      rw [aeval_map_algebraMap]
      rw [← aeval_algHom_apply]
      rfl
    rw [IsScalarTower.algebraMap_eq O K (AlgebraicClosure K), ← Polynomial.map_map, h2, h1, map_zero]
  have hroot : ∀ μ ∈ (y.map (algebraMap K (AlgebraicClosure K))).charpoly.roots, IsIntegral O μ := by
    intro μ hμ
    have hs : μ ∈ spectrum (AlgebraicClosure K) (y.map (algebraMap K (AlgebraicClosure K))) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
    have hs2 := spectrum.subset_polynomial_aeval (y.map (algebraMap K (AlgebraicClosure K)))
      (p.map (algebraMap O (AlgebraicClosure K))) ⟨μ, hs, rfl⟩
    rw [hpL] at hs2
    have h0 : eval μ (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
      by_contra hc
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Ne.isUnit hc).map _)
    exact ⟨p, hpm, by rwa [eval_map] at h0⟩
  have htr : algebraMap K (AlgebraicClosure K) y.trace = (y.map (algebraMap K (AlgebraicClosure K))).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  have hL : IsIntegral O (algebraMap K (AlgebraicClosure K) y.trace) := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
    exact multiset_sum_mem _ (fun μ hμ => (mem_integralClosure_iff _ _).2 (hroot μ hμ))
  have hK : IsIntegral O y.trace :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).1 hL
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hK
  rw [← hz]
  exact z.2

end GlobalTheory.TraceBdd

theorem GlobalTheory.trace_mem_of_pow_bdd : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (a : w.adicCompletion E), a ≠ 0 →
    (∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ Ov E w) → y.trace ∈ Ov E w := by
  intro E _ _ w n y a ha h
  exact GlobalTheory.TraceBdd.trace_mem_valuationSubring_of_pow_bounded (w.adicCompletionIntegers E) n y a ha h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCount
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem twOrb_congruence_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ w hw K e hBr k t ht htk n Q B u x hsep hF hu γ hγ hM
  obtain ⟨ψ, hψ⟩ := (isModel_iff w e B u x γ).1 hM
  have hψ1 := hψ.1
  have hψ3 := hψ.2.2
  let δ : UL n w := ⟨γ, hγ⟩
  let M : UL n w → Submodule K.O B.A := fun g => pullLat w B ψ g.1
  let τ : UL n w → B.Aˣ := fun g => torusOf w B ψ g.1
  have hcomm : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, h.1 * γ = γ * h.1 := by
    intro h hh
    have := congrArg Subtype.val hh
    simpa using this
  have h1 : ∀ g kk : UL n w, kk ∈ KL n w → M (g * kk) = M g := fun g kk hk =>
    GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL E w K B n ψ g.1 kk.1 (Subgroup.mem_subgroupOf.1 hk)
  have h2 : ∀ g g' : UL n w, M g = M g' → g⁻¹ * g' ∈ KL n w := fun g g' hgg =>
    Subgroup.mem_subgroupOf.2 (by simpa using GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset E w K e hBr B n ψ hψ1 g.1 g'.1 hgg)
  have h3 : ∀ L ∈ B.X x, ∃ g, M g = L := by
    intro L hL
    obtain ⟨hlat, -, hsd⟩ := hL
    obtain ⟨g, hg, hgL⟩ := _root_.GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq E w hw K e hBr B x n ψ hψ1 hψ3 L hlat hsd
    exact ⟨⟨g, hg⟩, hgL⟩
  have hT : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧ ∀ y, ψ ((τ h : B.A) * y) = h.1.val *ᵥ ψ y :=
    fun h hh => _root_.GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute E w hw K e B Q u x n γ ψ hF hψ h.1 h.2 (hcomm h hh)
  have h4 : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧
      ∀ g, M (h * g) = GlobalTheory.UnitLemma.mulLat K.O (τ h : B.A) (M g) :=
    fun h hh => ⟨(hT h hh).1, fun g => _root_.GlobalTheory.KapOrb.pullLat_mul_eq_mulLat E w K B n ψ h.1 g.1 _ (hT h hh).2⟩
  have h5 : ∀ s ∈ B.T, ∃ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h = s := by
    intro s hs
    obtain ⟨h, hU, hc, hspec⟩ := _root_.GlobalTheory.KapOrb.exists_unitary_of_torus E w K e B u x n γ ψ hψ s hs
    refine ⟨⟨h, hU⟩, ?_, torusOf_spec w B ψ h s hspec⟩
    show (⟨h, hU⟩ : UL n w) * δ = δ * (MonoidHom.id (UL n w)) ⟨h, hU⟩
    exact Subtype.ext hc
  have hiff : ∀ g : UL n w, M g ∈ B.X x ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
    intro g
    obtain ⟨hlat, hsd⟩ := _root_.GlobalTheory.KapOrb.SDual.pullLat_selfDual E w hw K e hBr B x n ψ hψ1 hψ3 g.1 g.2
    rw [← _root_.GlobalTheory.KapCong.pullLat_stable_iff_cong E w hw K e hBr k t ht htk B u x n γ ψ hψ hu hγ g.1 g.2]
    exact ⟨fun h => h.2.1, fun h => ⟨hlat, h, hsd⟩⟩
  have h6 : ∀ g : UL n w, avg (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
      ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) = if M g ∈ B.X x then 1 else 0 := by
    intro g
    have hfun : (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
        ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) =
        fun _ => (if g.1⁻¹ * γ * g.1 ∈ congSet w n k then 1 else 0 : ℂ) := by
      funext kk
      rw [Set.indicator_apply]
      have hc : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 =
          (kk.1.1)⁻¹ * (g.1⁻¹ * γ * g.1) * kk.1.1 := by
        simp [δ, mul_assoc]
      have hm : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)) ∈
          ({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)) ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
        show ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 ∈ congSet w n k ↔ _
        rw [hc]
        exact GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff E w n k _ _ (Subgroup.mem_subgroupOf.1 kk.2)
      by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
      · rw [if_pos (hm.2 h), if_pos h]; rfl
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h]
    rw [hfun, GlobalTheory.TwOrbGood.avg_const]
    by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
    · rw [if_pos h, if_pos ((hiff g).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff g).1 h'))]
  have hmul : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ (h * h') = τ h * τ h' := by
    intro h hh h' hh'
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, (hT h hh).2, (hT h' hh').2, Matrix.mulVec_mulVec]
    rfl
  have hinj : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ h = τ h' → h = h' := by
    intro h hh h' hh' heq
    have hv : ∀ v, h.1.val *ᵥ v = h'.1.val *ᵥ v := by
      intro v
      obtain ⟨y, rfl⟩ := ψ.surjective v
      rw [← (hT h hh).2, ← (hT h' hh').2, heq]
    have hm : h.1.val = h'.1.val :=
      Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v)
    exact Subtype.ext (Units.ext hm)
  have hcpt : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ,
      h ∈ cptPart (twCent (MonoidHom.id (UL n w)) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
    fun h hh => _root_.GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits E w hw K e hBr B Q u x n γ hγ ψ hF hψ h hh
  have h7 := _root_.GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat (KL n w) δ B.T M τ h1 h2 h4 h5 hmul hinj hcpt
  exact _root_.GlobalTheory.OrbReindex.twOrb_eq_orbSum (KL n w) δ _ B.T (B.X x) M τ h1 h2 h3 h4 h5 h6 h7

end GlobalTheory.KapOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLe
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem unipFlag_castLE_le_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = 0 := by
      by_contra h0
      obtain ⟨k, hk, -⟩ := (hS ⟨0, by omega⟩).1 (by simp only; omega)
      simp at hk
    subst hs0
    rw [GlobalTheory.StdPar.unip_empty]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨a, ha⟩ := hg.2 (Pi.single j 1) (Subsingleton.elim _ _)
    have h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0 := funext fun _ => by simp [Matrix.mulVec, dotProduct]
    have hv : (fun i => inclR (F := F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one] at ha
    exact (congrFun ha i).trans (Pi.single_apply _ _ _)
  · obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
    have hsm : s = m.val + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk, hle⟩ := (hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)
        have h2 := hmax k hk
        rw [Fin.le_def] at hle h2
        simp only at hle
        omega
      · have := (hS m).2 ⟨m, hmS, le_rfl⟩
        omega
    subst hsm
    have hd' : d = fun i => (S.filter fun k => k.val < i.val).card := by
      funext i
      rw [hd i]
      congr 1
    subst hd'
    exact GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infHom (lam : InfinitePlace E → DomWeight n) : Submodule ℂ (Wsp lam →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {T | ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w)}
  add_mem' ha hb x hx w := by
    simp only [LinearMap.add_apply, ha x hx, hb x hx, map_add (f := _)]
  zero_mem' x _ w := by simp
  smul_mem' c T hT x hx w := by
    simp only [LinearMap.smul_apply, hT x hx, map_smul]

theorem RU_mul (a b : UA E n) (φ : UA E n → ℂ) : RU E n (a * b) φ = RU E n a (RU E n b φ) := by
  rw [map_mul]; rfl

theorem comp_mem_infHom (lam : InfinitePlace E → DomWeight n) {T : Wsp lam →ₗ[ℂ] (UA E n → ℂ)} (hT : T ∈ infHom lam)
    (k : finU (E := E) (n := n)) : RU E n k.1 ∘ₗ T ∈ infHom lam := by
  intro x hx w
  simp only [LinearMap.comp_apply, hT x hx, ← RU_mul, GlobalTheory.DefU.fin_mul_inf k.2 hx]

theorem exists_op (lam : InfinitePlace E → DomWeight n) (A : Module.End ℂ (Wsp lam)) :
    ∃ P : Module.End ℂ (UA E n → ℂ), ∀ T ∈ infHom lam, ∀ w, T (A w) = P (T w) := by
  have hA : A ∈ Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) := by
    rw [_root_.GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top E n lam]; exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨RU E n x.1, fun T hT w => hT x.1 x.2 w⟩
  | zero => exact ⟨0, fun T _ w => by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨P, hP⟩ := hA
    obtain ⟨Q, hQ⟩ := hB
    exact ⟨P + Q, fun T hT w => by simp [hP T hT, hQ T hT]⟩
  | smul c A _ hA =>
    obtain ⟨P, hP⟩ := hA
    exact ⟨c • P, fun T hT w => by simp [hP T hT]⟩

theorem eq_zero_of_sum (lam : InfinitePlace E → DomWeight n) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Wsp lam))
    (T : ι → Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (hT : ∀ j, T j ∈ infHom lam) (h : ∑ j, T j (b j) = 0) (k : ι) :
    T k = 0 := by
  refine b.ext fun m => ?_
  obtain ⟨P, hP⟩ := exists_op lam ((b.coord k).smulRight (b m))
  have := congrArg P h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at this
  rw [LinearMap.zero_apply, ← this]
  rw [Finset.sum_eq_single k]
  · rw [← hP _ (hT k)]; simp
  · intro j _ hj
    rw [← hP _ (hT j)]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hj]
  · simp

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_span_values (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) {φ : UA E n → ℂ} (hφ : φ ∈ π) :
    φ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ} := by
  set Sv := Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ}
  have hle : Sv ≤ π := Submodule.span_le.2 (by rintro _ ⟨T, -, hT, w, rfl⟩; exact hT w)
  have hst : ∀ g, ∀ ψ ∈ Sv, RU E n g ψ ∈ Sv := by
    intro g ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      rw [eq_splitFin_mul_splitInf g, RU_mul, ← hT _ (splitInf E n g).2]
      exact Submodule.subset_span ⟨_, comp_mem_infHom lam hT (splitFin E n g),
        fun w' => hπ.stable _ _ (hTπ w'), _, rfl⟩
    | zero => simp
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨T, hT0, hTπ, hT⟩ := _root_.GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining E n lam π hπ hW
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hT0
  rcases hπ.irred Sv hle hst with h | h
  · have hm : T w ∈ Sv := Submodule.subset_span ⟨T, hT, hTπ, w, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact absurd hm hw
  · rw [h]; exact hφ

theorem mem_range_of_mem (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (lam : InfinitePlace E → DomWeight n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v))
    {φ : UA E n → ℂ} (hφ : φ ∈ π) (hfix : φ ∈ fixed (RF E n) (globLev S K')) :
    φ ∈ LinearMap.range (Phi S lam K') := by
  classical
  let b := Module.finBasis ℂ (Wsp lam)
  have hdec : ∀ ψ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ},
      ∃ T : Fin (Module.finrank ℂ (Wsp lam)) → (Wsp lam →ₗ[ℂ] (UA E n → ℂ)),
        (∀ j, T j ∈ infHom lam) ∧ (∀ j w, T j w ∈ π) ∧ ψ = ∑ j, T j (b j) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      refine ⟨fun j => b.repr w j • T, fun j => Submodule.smul_mem _ _ hT, fun j w' => π.smul_mem _ (hTπ w'), ?_⟩
      calc T w = T (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
        _ = ∑ j, (b.repr w j • T) (b j) := by simp only [map_sum, map_smul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => π.zero_mem, by simp⟩
    | add a c _ _ ha hc =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      obtain ⟨C, hC, hCπ, rfl⟩ := hc
      exact ⟨A + C, fun j => add_mem (hA j) (hC j), fun j w => π.add_mem (hAπ j w) (hCπ j w),
        by simp [Finset.sum_add_distrib]⟩
    | smul c a _ ha =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      exact ⟨c • A, fun j => Submodule.smul_mem _ c (hA j), fun j w => π.smul_mem c (hAπ j w),
        by simp [Finset.smul_sum]⟩
  obtain ⟨T, hT, hTπ, rfl⟩ := hdec φ (mem_span_values lam π hπ hW hφ)
  have hfixT : ∀ k ∈ globLev S K', ∀ j, RU E n k.1 ∘ₗ T j = T j := by
    intro k hk j
    have h1 : RU E n k.1 (∑ j, T j (b j)) = ∑ j, T j (b j) := by
      have := hfix ⟨k, hk⟩
      simpa [RF] using this
    have h2 : ∑ i, (RU E n k.1 ∘ₗ T i - T i) (b i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_sum lam b _ (fun i => sub_mem (comp_mem_infHom lam (hT i) k) (hT i)) h2 j)
  obtain ⟨F, hFa⟩ : ∃ F : Fin (Module.finrank ℂ (Wsp lam)) → finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam),
      ∀ j x w, F j x w = T j w x.1 :=
    ⟨fun j x => LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) x.1 ∘ₗ T j, fun _ _ _ => rfl⟩
  have hphi : ∀ j, phiFun lam (F j) = T j := by
    intro j
    refine LinearMap.ext fun w => funext fun g => ?_
    rw [phiFun_apply, hFa]
    have hg := eq_splitFin_mul_splitInf g
    have hw : wInf lam g = wInf lam (splitInf E n g).1 := by
      conv_lhs => rw [hg]
      rw [map_mul, wInf_fin, one_mul]
    rw [hw, hT j _ (splitInf E n g).2]
    change T j w ((splitFin E n g).1 * (splitInf E n g).1) = T j w g
    rw [← hg]
  have hF : ∀ j, F j ∈ vecM S lam K' := by
    intro j
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · refine LinearMap.ext fun w => ?_
      rw [LinearMap.dualMap_apply, hFa, hFa]
      obtain ⟨r, hr, hrf, hrc⟩ := _root_.GlobalTheory.BCT.RatPt.ratPt E n γ
      set i := splitInf E n r
      have hri : r = (finPt γ).1 * i.1 := by rw [← hrf]; exact eq_splitFin_mul_splitInf r
      have hc : ∀ v : InfinitePlace E, cEmb v.embedding (i.1⁻¹) = GeneralLinearGroup.map v.embedding (γ⁻¹).1 := by
        intro v
        have : i.1⁻¹ = r⁻¹ * (finPt γ).1 := by rw [hri]; group
        rw [this, map_mul, map_inv, hrc v, cEmb_fin, mul_one, Subgroup.coe_inv, map_inv]
      have hwi : wInf lam i.1⁻¹ = wAt lam γ⁻¹ := by
        change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding i.1⁻¹)) = _
        unfold wAt
        simp only [hc]
      have hl := (hπ.aut _ (hTπ j w)).left r hr (i.1⁻¹ * x.1)
      rw [← hwi, hT j _ (inv_mem i.2)]
      change T j w ((finPt γ).1 * x.1) = T j w (x.1 * i.1⁻¹)
      rw [GlobalTheory.DefU.fin_mul_inf x.2 (inv_mem i.2), ← hl, hri]
      group
    · refine LinearMap.ext fun w => ?_
      rw [hFa, hFa]
      change T j w (x.1 * k.1) = T j w x.1
      exact congrFun (LinearMap.congr_fun (hfixT k hk j) w) x.1
  refine ⟨∑ j, ⟨F j, hF j⟩ ⊗ₜ b j, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Phi_tmul, hphi]

theorem forms_le_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  refine iSup_le fun π => iSup_le fun hπ => ?_
  rintro φ ⟨hφ, hfix⟩
  exact mem_range_of_mem S K' lam π hπ.1 hπ.2 hφ hfix

end GlobalTheory.BCT.TrKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem per_om_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ Per F m (om (g, h) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, k, hCk⟩ := GlobalTheory.ThetaLevel.periodic_level F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hper⟩ := hCk g h
  refine ⟨m, hm1, hmle, fun x z hz => ?_⟩
  choose a ha0 haI haz using hz
  have hz' : z = (m : AF F) • a := by
    funext i; simp [haz i]
  rw [hz']
  exact hper x a fun i => ⟨ha0 i, haI i⟩

end GlobalTheory.ArchDecay
end

