module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpec
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem spMap_away_mem_basicOpen {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by
  show algebraMap S (Localization.Away s) s ∉ x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))

theorem exists_basicOpen_cover_affine (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y) :
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  classical
  let T : Set S := {s | ∃ W : Y.Opens, IsAffineOpen W ∧
    ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen s → u.base x ∈ W}
  have hT : Ideal.span T = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (u.base x)) isOpen_univ
    obtain ⟨_, ⟨s, rfl⟩, hxs, hsW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hxW (u ⁻¹ᵁ W).isOpen
    have hsT : s ∈ T := ⟨W, hW, fun y hy => hsW hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, TopologicalSpace.Opens.mem_iSup.mpr ⟨hsT, hxs⟩⟩
  obtain ⟨F, hFT, hF⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  have hW : ∀ t : F, ∃ W : Y.Opens, IsAffineOpen W ∧
      ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen (t : S) → u.base x ∈ W := fun t => hFT t.2
  choose Wf hWa hWs using hW
  refine ⟨F.card, fun i => (F.equivFin.symm i : S), fun i => Wf (F.equivFin.symm i), ?_,
    fun i => hWa _, fun i => ?_⟩
  · have : Set.range (fun i => (F.equivFin.symm i : S)) = (F : Set S) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (F.equivFin.symm i).2
      · intro hy
        exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
    rw [this, hF]
  · rw [eq_top_iff]
    intro x _
    exact hWs _ _ (spMap_away_mem_basicOpen _ x)

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  first | (exact @GlobalTheory.Shin.BlockPar.block_par) | (exact GlobalTheory.Shin.BlockPar.block_par) | (intros; apply GlobalTheory.Shin.BlockPar.block_par  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int : ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  first | (exact @GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (exact GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (intros; apply GlobalTheory.AdeleZ.exists_continuous_adele_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePadicIntDomainEmbedding
section
open IsLocalRing

namespace GlobalTheory.CompletionEmbed

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]

noncomputable def levelMap (hpm : (p : C) ∈ maximalIdeal C) (n : ℕ) :
    ℤ_[p] →+* C ⧸ maximalIdeal C ^ n :=
  have h : ((p ^ n : ℕ) : C ⧸ maximalIdeal C ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal C ^ n)), Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.pow_mem_pow hpm n
  (ZMod.castHom (ringChar.dvd h) (C ⧸ maximalIdeal C ^ n)).comp (PadicInt.toZModPow n)

theorem levelMap_compat (hpm : (p : C) ∈ maximalIdeal C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (levelMap p C hpm n) =
      levelMap p C hpm m := by
  unfold levelMap
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def toCompletion (hpm : (p : C) ∈ maximalIdeal C) :
    ℤ_[p] →+* AdicCompletion (maximalIdeal C) C :=
  AdicCompletion.liftRingHom (maximalIdeal C) (levelMap p C hpm)
    (fun hle => levelMap_compat p C hpm hle)

theorem algebraMap_injective [IsNoetherianRing C] :
    Function.Injective (algebraMap C (AdicCompletion (maximalIdeal C) C)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ ⨅ n : ℕ, maximalIdeal C ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    have := congrArg (AdicCompletion.evalₐ (maximalIdeal C) n) hx
    rw [map_zero] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top] at hmem
  exact hmem

theorem exists_pow_le_span [IsNoetherianRing C] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun Q ⟨hle, hQ⟩ => ?_
  have hQ0 : Q ≠ ⊥ := fun h => hp0 (by
    have := hle (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Ideal.mem_bot).mp this)
  rw [hprime Q hQ hQ0]

theorem finite_quot_span [IsNoetherianRing C] [Finite (ResidueField C)] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    Finite (AdicCompletion (maximalIdeal C) C ⧸
      Ideal.span {(p : AdicCompletion (maximalIdeal C) C)}) := by
  set A := AdicCompletion (maximalIdeal C) C
  have fg : (maximalIdeal C).FG := IsNoetherian.noetherian _
  haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›
  haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by
    have h := Finite.of_injective _
      (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ fg] at h
    exact h
  obtain ⟨N, hN⟩ := exists_pow_le_span p C hp0 hprime
  haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) :=
    Ideal.finite_quotient_pow (fg.map _) N
  have hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)} := by
    rw [← Ideal.map_pow]
    calc _ ≤ (Ideal.span {(p : C)}).map (algebraMap C A) := Ideal.map_mono hN
      _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

end GlobalTheory.CompletionEmbed


open IsLocalRing GlobalTheory.CompletionEmbed in
theorem GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C]
      [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C →
      (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D),
        Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  intro p _ C _ _ _ _ hfin hp0 hpm hprime
  set A := AdicCompletion (maximalIdeal C) C
  haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra
  have hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime
  have hne : Ideal.span {(p : A)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (p : A) := Ideal.span_singleton_eq_top.mp h
    have hu' := hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hpm] at hu'
    exact not_isUnit_zero hu'
  haveI : Module.Finite ℤ_[p] A := by
    refine GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_
    · rw [hJ]; exact hne
    · rw [hJ]; exact Module.Finite.of_finite
  have hnil : ¬ IsNilpotent (p : A) := by
    rintro ⟨n, hn⟩
    have h : algebraMap C A ((p : C) ^ n) = 0 := by rw [map_pow, map_natCast]; exact hn
    have h3 := (injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h
    exact hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  haveI := hQ
  refine ⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_,
    (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hbot : Q.comap (algebraMap C A) = ⊥ := by
      by_contra hb
      have h1 := hprime _ (Ideal.comap_isPrime _ _) hb
      apply hpQ
      have h2 : (p : C) ∈ Q.comap (algebraMap C A) := by
        rw [h1]; exact hpm
      rw [Ideal.mem_comap, map_natCast] at h2
      exact h2
    have hx' : x ∈ Q.comap (algebraMap C A) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    rw [hbot] at hx'
    exact (Ideal.mem_bot).mp hx'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCover
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => _root_.GlobalTheory.affine_inter_finite_basicOpen_cover X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generators_jacobian_det_not_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_of_prime | exact GlobalTheory.exists_generic_jacobian_data_of_prime | (intros; apply GlobalTheory.exists_generic_jacobian_data_of_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNorm
section
open scoped TensorProduct Classical

namespace GlobalTheory.LocalApprox

theorem isUnit_of_isUnit_one_tmul (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (b : E) (hb : IsUnit ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b)) : IsUnit b := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective
  have h1 : Function.Injective (LinearMap.mulLeft ℚ b) := by
    intro x y hxy
    apply hinj
    have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy
    simp only [LinearMap.mulLeft_apply, map_mul] at h
    exact hb.mul_left_cancel h
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 h1 1
  have hw' : b * w = 1 := hw
  exact ⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩

theorem exists_rat_mul_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℚ_[ℓ]ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ r : ℤ_[ℓ]ˣ, (u : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] c * ((r : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hu : 0 < ‖(u : ℚ_[ℓ])‖ := norm_pos_iff.2 u.ne_zero
  obtain ⟨c, hc⟩ := Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu
  have hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖ := by
    have h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c) := by ring
    have hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖ := by rwa [norm_neg]
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  have hc0 : (c : ℚ_[ℓ]) ≠ 0 := norm_pos_iff.1 (hn ▸ hu)
  have h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1 := by rw [norm_div, hn, div_self hu.ne']
  refine ⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩
  rw [PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]

theorem main : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  intro E _ _ _ τ ℓ _ a u z ha hau
  set S := ℚ_[ℓ] ⊗[ℚ] E
  set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ
  set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι
  have hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w := fun w => rfl
  have hτι : ∀ w : E, τℓ (ι w) = ι (τ w) := fun w => by
    show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q) := fun q => by
    rw [ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]
  have hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ])) := fun t => by
    rw [show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w) := fun w hw =>
    hw.map (τℓ.restrictScalars ℤ_[ℓ])
  obtain ⟨c, hc0, r, hur⟩ := exists_rat_mul_unit ℓ u
  obtain ⟨b, s, hs, hb⟩ := GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z
  obtain ⟨ρ, hρ, hρint⟩ := GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs
  set v : S := 1 + (ℓ : S) * s with hv
  have hvint : IsIntegral ℤ_[ℓ] v := by
    refine isIntegral_one.add (IsIntegral.mul ?_ hs)
    rw [show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]
    exact isIntegral_algebraMap
  have hbU : IsUnit b := isUnit_of_isUnit_one_tmul E ℓ b (by
    rw [hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)
  set m : E := algebraMap ℚ E c * (b * τ b) with hm
  have hmU : IsUnit m := ((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))
  obtain ⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1 := ⟨_, hmU.mul_val_inv⟩
  obtain ⟨ai, hai⟩ : ∃ ai : E, a * ai = 1 := ⟨_, ha.mul_val_inv⟩

  set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR
  set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi
  set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC
  set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU
  have hUCR : U = C * R := by rw [hU, hur, map_mul]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.coe_one, map_one]
  have h1 : ι a = U * ((z : S) * τℓ z) := hau
  have h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v)) := by
    rw [hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]
  have h4 : v * ρ = 1 := hρ
  have h5 : τℓ v * τℓ ρ = 1 := by rw [← map_mul, h4, map_one]
  have h3 : ι m * ι mi = 1 := by rw [← map_mul, hmi, map_one]
  have h3' : ι a * ι ai = 1 := by rw [← map_mul, hai, map_one]
  have hx : ι (a * mi) = R * ρ * τℓ ρ := by
    have hK : R * ρ * τℓ ρ * ι m = ι a := by
      rw [h2, h1, hUCR]
      linear_combination (C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5
    rw [map_mul]
    linear_combination (-ι mi) * hK + (R * ρ * τℓ ρ) * h3
  have hy : ι (m * ai) = Ri * v * τℓ v := by
    have hK : Ri * v * τℓ v * ι a = ι m := by
      rw [h2, h1, hUCR]
      linear_combination (C * (z : S) * v * τℓ z * τℓ v) * hRRi
    rw [map_mul]
    linear_combination (-ι ai) * hK + (Ri * v * τℓ v) * h3'
  obtain ⟨d1, hd1, hx1⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by
    rw [← hιapp, hx]
    exact ((hint _).mul hρint).mul (hτint _ hρint))
  obtain ⟨d2, hd2, hy2⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by
    rw [← hιapp, hy]
    exact ((hint _).mul hvint).mul (hτint _ hvint))
  refine ⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩
  · linear_combination (-a) * hmi
  · linear_combination (-m) * hai
  · intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h
    · exact hd1 h
    · exact hd2 h
  · have : ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1
  · have : ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2

end GlobalTheory.LocalApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHomStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom : ∀ (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)), ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  first | (exact @GlobalTheory.HilbAff.exists_hom_secAlg_top) | (exact GlobalTheory.HilbAff.exists_hom_secAlg_top) | (intros; apply GlobalTheory.HilbAff.exists_hom_secAlg_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafComapEqOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  first | (exact @GlobalTheory.IdealGlue.exists_comap_eq) | (exact GlobalTheory.IdealGlue.exists_comap_eq) | (intros; apply GlobalTheory.IdealGlue.exists_comap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable
section
open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

end GlobalTheory.LeviDesc.Krylov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulSubMemJacobsonOfFiniteResidueFielStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) → ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a → ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  first | (exact @GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (exact GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (intros; apply GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField  <;> assumption)
end

