module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineOfPlaceOver
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem map_pow_of_commuting {R S M N : Type} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] (f : M → N) (a : Module.End R M) (b : Module.End S N)
    (hf : ∀ x, f (a x) = b (f x)) (n : ℕ) (x : M) : f ((a ^ n) x) = (b ^ n) (f x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hf]

private theorem aeval_restriction_commute {F L M : Type} [Field F] [Field L] [Algebra F L] [AddCommGroup M] [Module L M]
    [Module F M] [IsScalarTower F L M] (D : Submodule L M) (S : Module.End L D) (T : Module.End F M)
    (hf : ∀ x : D, ((S x : D) : M) = T x) (q : F[X]) (x : D) :
    ((aeval S (q.map (algebraMap F L)) x : D) : M) = aeval T q (x : M) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      algebraMap_smul, map_pow_of_commuting (fun x : D => (x : M)) S T hf]

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

private theorem mem_aux {x : V ⊗[ℚ_[l]] P.R.B} : x ∈ Dcris (P.PD K) ρ ↔ ∀ g, actVB (P.PD K) ρ g x = x := by
  simp [Dcris, sub_eq_zero]

private theorem pullback_fin_relation [FiniteDimensional ↥LL.1 V] (hC : IsCrys (P.PD K) ρ) :
    FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  rcases subsingleton_or_nontrivial V with hs | hn
  · haveI : Subsingleton (V ⊗[ℚ_[l]] P.R.B) := inferInstance
    infer_instance
  · haveI := (P.PD K).finK₀
    apply Module.finite_of_finrank_pos
    rw [hC]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

private theorem frobenius_preserves_crystalline : ∀ x ∈ Dcris (P.PD K) ρ,
    φVB (P.PD K) (LL := ↥LL.1) (V := V) x ∈ Dcris (P.PD K) ρ := by
  intro x hx
  rw [mem_aux] at hx ⊢
  intro g
  have : ∀ y, actVB (P.PD K) ρ g (φVB (P.PD K) (LL := ↥LL.1) (V := V) y) =
      φVB (P.PD K) (LL := ↥LL.1) (V := V) (actVB (P.PD K) ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [actVB, φVB, (P.PD K).φ_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this, hx]

private theorem crystalline_mem_potentially_semistable : ∀ x ∈ Dcris (P.PD K) ρ, crisIncl P ↥LL.1 V x ∈ Dpst P ρ := by
  intro x hx
  exact (mem_Dpst P ρ).mpr ⟨K, fun g _ => by rw [stRep_crisIncl, (mem_aux P ρ).mp hx g]⟩

private noncomputable def crystallineInclusion : ↥(Dcris (P.PD K) ρ) →ₗ[↥LL.1] ↥(Dpst P ρ) :=
  (crisIncl P ↥LL.1 V).restrict (crystalline_mem_potentially_semistable P ρ)

private theorem coe_crystalline_inclusion (x : ↥(Dcris (P.PD K) ρ)) :
    ((crystallineInclusion P ρ x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x := rfl

private noncomputable def frobeniusRestriction : Module.End ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  (φVB (P.PD K) (LL := ↥LL.1) (V := V)).restrict (frobenius_preserves_crystalline P ρ)

private theorem coe_frobenius_restriction_pow (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private theorem coe_frobenius_restriction_pow_base (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private noncomputable def crystallineToWeilDeligne (ι : Om l ≃+* ℂ) : ↥(Dcris (P.PD K) ρ) →+ WDSpace P ι ρ :=
  AddMonoidHom.mk' (fun x => wdMk P ι ρ (crystallineInclusion P ρ x)) fun x y => by rw [map_add (f := _), wdMk_add]

private theorem span_crystalline_weil_deligne_top [FiniteDimensional ↥LL.1 V] (ι : Om l ≃+* ℂ) (hV : IsPst P ρ) (hC : IsCrys (P.PD K) ρ) :
    Submodule.span ℂ (Set.range (crystallineToWeilDeligne P ρ ι)) = ⊤ := by
  rw [eq_top_iff, ← UpperTheory.weil_deligne_span_crystalline P ι ρ hV hC]
  refine Submodule.span_mono ?_
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact ⟨⟨x, hx⟩, congrArg (wdMk P ι ρ) (Subtype.ext hy.symm)⟩

private theorem eval_root_transport (ι : Om l ≃+* ℂ) (b : ℂ) (q : ℚ_[l][X]) (hq : aeval (ι.symm b) q = 0) :
    (q.map (algebraMap ℚ_[l] ↥LL.1)).eval₂ (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) b = 0 := by
  rw [eval₂_map]
  have h1 := congrArg ι.toRingHom hq
  rw [map_zero, aeval_def, hom_eval₂] at h1
  have e1 : (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))).comp (algebraMap ℚ_[l] ↥LL.1) =
      ι.toRingHom.comp (algebraMap ℚ_[l] (Om l)) := by
    rw [IsScalarTower.algebraMap_eq ℚ_[l] ↥LL.1 (Om l)]; rfl
  rw [e1]
  simpa using h1

set_option synthInstance.maxHeartbeats 100000 in
private theorem crystalline_to_weil_deligne_smul (ι : Om l ≃+* ℂ) (a : ↥LL.1) (x : ↥(Dcris (P.PD K) ρ)) :
    crystallineToWeilDeligne P ρ ι (a • x) = (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) a • crystallineToWeilDeligne P ρ ι x :=
  (congrArg (wdMk P ι ρ) ((crystallineInclusion P ρ).map_smul a x)).trans (wdMk_smul P ι ρ a _)

set_option synthInstance.maxHeartbeats 100000 in
private theorem fin_step (n : ℕ) (q : ℚ_[l][X])
    (H : ∃ x : ↥(Dcris (P.PD K) ρ), x ≠ 0 ∧ aeval (frobeniusRestriction P ρ ^ n) (q.map (algebraMap ℚ_[l] ↥LL.1)) x = 0) :
    ∃ x ∈ Dcris (P.PD K) ρ, x ≠ 0 ∧
      aeval ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) q x = 0 := by
  obtain ⟨x, hx0, hx⟩ := H
  refine ⟨x.1, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  exact (aeval_restriction_commute (Dcris (P.PD K) ρ) (frobeniusRestriction P ρ ^ n) _ (coe_frobenius_restriction_pow_base P ρ n) q x).symm.trans
    (congrArg Subtype.val hx)

end SlopeTestRemainingChoices

theorem UpperTheory.crystalline_of_place_over :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), IsPst P ρ → IsCrys (P.PD Bw.Kw) ρ → ∀ σ : ↥(Weil h), deg σ = -1 → ∀ b ∈ (wdPst P ι Bw h hj ρ).eig σ, ∀ q : ℚ_[l][X], aeval (ι.symm b) q = 0 → ∃ x ∈ Dcris (P.PD Bw.Kw) ρ, x ≠ 0 ∧ aeval ((φVB (P.PD Bw.Kw) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) q x = 0 := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ hV hC σ hσ b hb q hq
  haveI := hV.finite
  haveI := pullback_fin_relation P ρ hC
  have hb' : b ∈ (wdRho P ι Bw h hj ρ σ).charpoly.roots := by
    rw [← GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ]
    exact hb
  have hT : ∀ x, wdRho P ι Bw h hj ρ σ (crystallineToWeilDeligne P ρ ι x) = crystallineToWeilDeligne P ρ ι ((frobeniusRestriction P ρ ^ resDeg l w) x) := fun x =>
    (wdRho_mk P ι Bw h hj ρ σ (crystallineInclusion P ρ x)).trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((UpperTheory.local_crystalline_of_induced P Bw h hj ρ σ hσ x.1 (crystallineInclusion P ρ x) x.2 (coe_crystalline_inclusion P ρ x)).trans
        ((coe_crystalline_inclusion P ρ _).trans (congrArg (crisIncl P ↥LL.1 V) (coe_frobenius_restriction_pow P ρ _ x))).symm)))
  exact fin_step P ρ _ q (UpperTheory.exists_eigenvector_of_root (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (crystallineToWeilDeligne P ρ ι)
    (frobeniusRestriction P ρ ^ resDeg l w) (wdRho P ι Bw h hj ρ σ) (crystalline_to_weil_deligne_smul P ρ ι)
    (span_crystalline_weil_deligne_top P ρ ι hV hC) hT (q.map (algebraMap ℚ_[l] ↥LL.1)) b hb' (eval_root_transport ι b q hq))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_exists_torus_congruence_fixed :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))) (γ : (ValueGroupWithZero k)ˣ), γ ≤ 1 → HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    Nontrivial (Jacquet π (unipB k (Fin N))) →
    ∃ y : Jacquet π (unipB k (Fin N)), y ≠ 0 ∧ ∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ hnt
  let f := Equiv.sigmaUnique (Fin N) fun _ : Fin N => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k (Fin N)) 1 := by
    rw [EmptyBlocks.unipRad_eq k f hmono]
  let E : Jacquet π (unipRad k f) ≃ₗ[ℂ] Jacquet π (unipB k (Fin N)) := Submodule.quotEquivOfEq _ _ h3
  have hE : ∀ v : V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support hG hZ k N V π s γ hγ hs hχ f E.toEquiv.nontrivial
  refine ⟨E y, E.map_ne_zero_iff.2 hy0, fun t ht => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hγ' : (γ : ValueGroupWithZero k) ≤ 1 := hγ
  have h1 := hy (EmptyBlocks.torusToLevi k f t) fun a i j => by
    rw [EmptyBlocks.val_torusToLevi, Subsingleton.elim i j, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    exact ht _
  have hv : ∀ i, valuation k (t i : k) = 1 := fun i => by
    have := Valuation.map_one_add_of_lt (valuation k) ((ht i).trans_le hγ')
    rwa [add_sub_cancel] at this
  have hd : deltaHalf k (fun _ : Fin N => Fin 1) (EmptyBlocks.torusToLevi k f t) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
    have := (EmptyBlocks.det_torusToLevi k f t a).trans (Fin.prod_univ_one _)
    exact (congrArg (fun u : kˣ => valuation k (u : k)) this).trans (hv _)
  rw [jac_mk, hd, inv_one, Units.val_one, one_smul, EmptyBlocks.leviEmb_torusToLevi] at h1
  have h2 := congrArg E h1
  rw [hE, hE] at h2
  rw [hE, jacBU_mk]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_character_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))), HasSupport π s → (∀ y ∈ s, y.1 = 1) → Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro hG hZ k _ _ _ _ N V _ _ π s hs h1
  have hV : Nontrivial V := by
    obtain ⟨h, x, hx, hirr, hcu, e0, hsub⟩ := hs
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial).exists_pair_ne
    apply hab
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have : a1 = b1 := Subsingleton.elim _ _
    subst this
    rfl
  let S : ∀ {r : ℕ} {d : Fin r → ℕ}, ((a : Fin r) × Fin (d a) ≃ Fin N) → Finset (Fin N × Fin N) :=
    fun e => Finset.univ.filter (fun pq : Fin N × Fin N => ¬ blk e pq.1 < blk e pq.2)
  have key : ∀ m : ℕ, ∀ (r : ℕ) (d : Fin r → ℕ) (e : (a : Fin r) × Fin (d a) ≃ Fin N),
      (S e).card ≤ m → Nontrivial (Jacquet π (unipRad k e)) →
      Nontrivial (Jacquet π (unipB k (Fin N))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r d e hm hJ
      by_cases hd : ∀ a, d a ≤ 1
      · exact UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one k N V π r d e hd hJ
      push_neg at hd
      obtain ⟨j, hj⟩ := hd
      obtain ⟨t, c, f, hf, hmono, p, q, hpq, hnpq⟩ :=
        UpperTheory.jacquet_finer_parabolic_of_character_support hG hZ k N V π s hs h1 r d e j (by omega) hJ
      have hlt : (S f).card < (S e).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨(p, q), ?_, ?_⟩
          · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hnpq
          · simp [S, hpq]
        · intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact fun h => hx (hmono _ _ h)
      exact ih _ (lt_of_lt_of_le hlt hm) t c f le_rfl hf
  let e1 : (a : Fin 1) × Fin ((fun _ : Fin 1 => N) a) ≃ Fin N :=
    { toFun := fun p => p.2
      invFun := fun i => ⟨0, i⟩
      left_inv := by
        rintro ⟨a, i⟩
        fin_cases a
        rfl
      right_inv := fun i => rfl }
  have hU : ∀ g ∈ unipRad k e1, g = 1 := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    have h0 := congrFun (MonoidHom.mem_ker.mp hp) 0
    ext i j
    have h2 := congrArg (fun u : GL (Fin N) k => (u : Matrix (Fin N) (Fin N) k) i j) h0
    simpa [leviProj, diagBlock, MonoidHom.pi, e1] using h2
  have hker : twKer π (unipRad k e1) 1 = ⊥ := by
    rw [twKer, Submodule.span_eq_bot]
    rintro w ⟨n, v, rfl⟩
    rw [hU n.1 n.2]
    simp
  apply key _ 1 (fun _ => N) e1 le_rfl
  show Nontrivial (V ⧸ twKer π (unipRad k e1) 1)
  rw [hker, Submodule.Quotient.nontrivial_iff]
  exact bot_ne_top
end

