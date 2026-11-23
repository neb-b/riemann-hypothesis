module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLine
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PowImage

lemma idealSumMap_comp_natural {A : Type} [CommRing A] [IsNoetherianRing A] {Z : Scheme.{0}}
    [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (J : Ideal A) :
    idealSumMap F J ≫ g = biproduct.map (fun _ => g) ≫ idealSumMap G J := by
  apply biproduct.hom_ext'
  intro k
  simp only [idealSumMap, biproduct.ι_desc_assoc, biproduct.ι_map_assoc, smulHom_comp,
    biproduct.ι_desc]

lemma idealPowι_comp_cokernel {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (m : ℕ) :
    idealPowι I F m ≫ g ≫ cokernel.π (idealSumMap G (I ^ m)) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage (idealSumMap F (I ^ m)))).1
  have hfac : Abelian.factorThruImage (idealSumMap F (I ^ m)) ≫
      kernel.ι (cokernel.π (idealSumMap F (I ^ m))) = idealSumMap F (I ^ m) :=
    Abelian.image.fac _
  rw [comp_zero, ← Category.assoc, hfac, ← Category.assoc, idealSumMap_comp_natural,
    Category.assoc, cokernel.condition, comp_zero]

theorem adjMap_app_mem_range_idealPowι {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ)
    (hB : B ⊔ powSub I _ (n + 1) = pullSys I φ E S n) (V : X.Opens) (x : Γ(E, V))
    (hx : x ∈ secs (S n) V) :
    (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈
      Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  obtain ⟨y, rfl⟩ := hx
  let f := cokernel.π B.arrow ≫ cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))
  have hle : pullSys I φ E S n ≤ kernelSubobject f := by
    rw [← hB]
    refine sup_le ?_ ?_
    · apply le_kernelSubobject
      rw [← Category.assoc, cokernel.condition, zero_comp]
    · apply le_kernelSubobject
      rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_cokernel, comp_zero]
  have hS : (Scheme.Modules.pullback φ).map (S n).arrow ≫ f = 0 := by
    have h1 := le_sup_left.trans hle
    rw [← imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S n).arrow), Category.assoc,
      ← Subobject.ofLE_arrow h1, Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]
  let k := kernel.lift (cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1))))
    ((Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow)
    (by rw [Category.assoc]; exact hS)
  have hk : k ≫ idealPowι I (cokernel B.arrow) (n + 1) =
      (Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow := kernel.lift_ι _ _ _
  have hadj : (S n).arrow ≫ adjMap φ B =
      (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _ ≫
        (Scheme.Modules.pushforward φ).map (k ≫ idealPowι I (cokernel B.arrow) (n + 1)) := by
    rw [adjMap, Adjunction.homEquiv_unit, hk, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality (S n).arrow
  refine ⟨((Scheme.Modules.pushforward φ).map k).app V
    (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _).app V y), ?_⟩
  have h2 := congrArg (fun g => g.app V y) hadj
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.map_comp] at h2
  rw [h2]
  rfl

end GlobalTheory.CompanionTheory.GE.PowImage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

variable {B : Type} [CommRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N]

theorem exists_eval_smul (r : AdicCompletion I B) (x : AdicCompletion I N) (n : ℕ) :
    ∃ b : B, eval I N n (r • x) = b • eval I N n x := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  exact ⟨b, by show (r • x).val n = b • x.val n; rw [smul_eval, ← hb]; rfl⟩

theorem finite_adicCompletion [Module.Finite B N] :
    Module.Finite (AdicCompletion I B) (AdicCompletion I N) :=
  Module.Finite.of_surjective (ofTensorProduct I N) (ofTensorProduct_surjective_of_finite I N)

theorem span_range_of [Module.Finite B N] :
    Submodule.span (AdicCompletion I B) (Set.range (of I N)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I N x
  induction t with
  | tmul a e =>
    rw [ofTensorProduct_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

variable {I} (T : ℕ → Submodule B N) (hT : ∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n)

noncomputable def toQuot (n : ℕ) : AdicCompletion I N →ₗ[B] N ⧸ T n :=
  Submodule.factor (hT n) ∘ₗ eval I N (n + 1)

theorem toQuot_of (n : ℕ) (e : N) : toQuot T hT n (of I N e) = (T n).mkQ e := by
  simp [toQuot, eval_of, Submodule.factor_mk]

theorem toQuot_mk (n : ℕ) (f : AdicCauchySequence I N) :
    toQuot T hT n (AdicCompletion.mk I N f) = (T n).mkQ (f (n + 1)) := by
  show Submodule.factor (hT n) ((AdicCompletion.mk I N f).val (n + 1)) = _
  rw [mk_apply_coe, Submodule.factor_mk]

noncomputable def Tb (n : ℕ) : Submodule (AdicCompletion I B) (AdicCompletion I N) where
  carrier := {x | toQuot T hT n x = 0}
  add_mem' {x y} hx hy := by simp_all
  zero_mem' := by simp
  smul_mem' r x hx := by
    obtain ⟨b, hb⟩ := exists_eval_smul I r x (n + 1)
    have : toQuot T hT n (r • x) = b • toQuot T hT n x := by
      simp only [toQuot, LinearMap.comp_apply, hb, map_smul]
    simp_all

theorem mem_Tb (n : ℕ) (x : AdicCompletion I N) : x ∈ Tb T hT n ↔ toQuot T hT n x = 0 := Iff.rfl

theorem antitone_of_eq_sup_pow_smul_whole_module (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) : Antitone T :=
  antitone_nat_of_succ_le fun n ↦ (hT' n).symm ▸ le_sup_left

theorem exists_lift (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) (n : ℕ) (e : N)
    (he : e ∈ T n) : ∃ l ∈ ⨅ m, Tb T hT m, eval I N (n + 1) l = eval I N (n + 1) (of I N e) := by
  have step : ∀ j (x : T (n + j)), ∃ y : T (n + j + 1),
      (x : N) - y ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
    intro j x
    have hx : (x : N) ∈ T (n + j + 1) ⊔ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
      rw [← hT']; exact x.2
    obtain ⟨a, ha, c, hc, hxe⟩ := Submodule.mem_sup.1 hx
    exact ⟨⟨a, ha⟩, by rw [← hxe]; simpa using hc⟩
  choose f hf using step
  let u : (j : ℕ) → T (n + j) := fun j ↦ Nat.rec ⟨e, he⟩ (fun j x ↦ f j x) j
  have huj : ∀ j, (u (j + 1)).1 = (f j (u j)).1 := fun j ↦ rfl
  have hu : ∀ j, ((u j).1 - (u (j + 1)).1) ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := fun j ↦ by
    rw [huj]; exact hf j (u j)
  let s : ℕ → N := fun k ↦ (u (k - (n + 1))).1
  have huc : ∀ a b, a = b → (u a).1 = (u b).1 := by rintro a b rfl; rfl
  have hs0 : ∀ k, k ≤ n + 1 → s k = e := fun k hk ↦ huc _ 0 (Nat.sub_eq_zero_of_le hk)
  have hs1 : ∀ j, s (n + 1 + j) = (u j).1 := fun j ↦ huc _ _ (by omega)
  have hcau : ∀ k, s k ≡ s (k + 1) [SMOD (I ^ k • ⊤ : Submodule B N)] := by
    intro k
    rw [SModEq.sub_mem]
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [hs0 k hk.le, hs0 (k + 1) hk, sub_self]; exact zero_mem _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hs1, show n + 1 + j + 1 = n + 1 + (j + 1) by omega, hs1]
      simpa [show n + 1 + j = n + j + 1 by omega] using hu j
  let F : AdicCauchySequence I N := AdicCauchySequence.mk I N s hcau
  have hF : ∀ k, F k = s k := fun k ↦ rfl
  refine ⟨AdicCompletion.mk I N F, Submodule.mem_iInf _ |>.2 fun m ↦ ?_, ?_⟩
  · rw [mem_Tb, toQuot_mk, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [hs0 _ (by omega)]; exact antitone_of_eq_sup_pow_smul_whole_module T hT' hm.le he
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show n + j + 1 = n + 1 + j by omega, hs1]; exact (u j).2
  · show (AdicCompletion.mk I N F).val (n + 1) = _
    rw [mk_apply_coe, eval_of, hF, hs0 _ le_rfl]

end GlobalTheory.CompanionTheory.GE.CompletionTower

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

theorem exists_completion_tower : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N),
    (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) →
    (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type)
      (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M)
      (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧
      Submodule.span R (Set.range μ) = ⊤ ∧
      ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  intro B _ _ I N _ _ _ T hT hT'
  haveI := finite_adicCompletion I (N := N)
  haveI := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let L : Submodule (AdicCompletion I B) (AdicCompletion I N) := ⨅ m, Tb T hT m
  let μ : N →ₗ[B] AdicCompletion I N ⧸ L := (L.mkQ.restrictScalars B) ∘ₗ of I N
  refine ⟨AdicCompletion I B, inferInstance, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    inferInstance, AdicCompletion I N ⧸ L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, μ, IsAdicComplete.le_jacobson_bot _, ?_, ?_⟩
  · have : Set.range μ = L.mkQ '' Set.range (of I N) := by
      ext y; simp [μ]
    rw [this, ← Submodule.map_span, span_range_of, Submodule.map_top, Submodule.range_mkQ]
  · intro n e
    constructor
    · intro he
      obtain ⟨l, hl, hle⟩ := exists_lift T hT hT' n e he
      have hmem : of I N e - l ∈ (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
          map_sub, hle, sub_self]
      have hl0 : L.mkQ l = 0 := (Submodule.Quotient.mk_eq_zero L).2 hl
      have hμ : μ e = (L.mkQ.restrictScalars B) (of I N e - l) := by
        simp only [μ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, hl0, sub_zero]
      have h2 := Submodule.mem_map_of_mem (f := L.mkQ.restrictScalars B) hmem
      rw [Submodule.map_smul''] at h2
      rw [hμ]
      exact Submodule.smul_mono le_rfl le_top h2
    · intro hμ
      have key : (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N ⧸ L)) ≤
          (LinearMap.ker (toQuot T hT n)).map (L.mkQ.restrictScalars B) := by
        rw [Submodule.smul_le]
        intro i hi m _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L m
        refine ⟨i • x, ?_, by simp⟩
        show toQuot T hT n (i • x) = 0
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T n) (toQuot T hT n x)
        rw [← hy, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT n (Submodule.smul_mem_smul hi Submodule.mem_top)
      obtain ⟨x, hx, hxe⟩ := key hμ
      have hd : x - of I N e ∈ L := (Submodule.Quotient.eq L).1 hxe
      have hd' := (Submodule.mem_iInf _).1 hd n
      rw [mem_Tb, map_sub, LinearMap.mem_ker.1 hx, zero_sub, neg_eq_zero, toQuot_of,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd'
      exact hd'

end GlobalTheory.CompanionTheory.GE.CompletionTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLineStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

open Module GlobalTheory.CompanionTheory.DeRhamChar GlobalTheory.CompanionTheory.LTRead in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.de_rham_rank_lubin_tate_line : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K LL : FinExt l), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ LL.1) →
    ∀ (χ : ↥(GK K) →* (↥K.1)ˣ), HasPeriods P K χ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Module.finrank ↥LL.1 ↥(DdR (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ))) =
        Module.finrank ℚ_[l] ↥K.1 * 1 ∧
      ∀ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
        multV (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ)) τ' a =
          if a = (if τ' = τ then (-1 : ℤ) else 0) then 1 else 0 := by
  rintro l _ P AI ⟨T⟩ K LL hsplit χ hP τ
  have := K.2
  have := LL.2
  set ψ : ↥(GK K) →* (↥LL.1)ˣ := (Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ
  have hcomponent : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ',
      (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧
      z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (if τ' = τ then (-1 : ℤ) else 0) ∧
      z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ((if τ' = τ then (-1 : ℤ) else 0) + 1) := by
    intro τ'
    obtain ⟨σ₀, h₀⟩ := exists_lift τ' K.1.val
    obtain ⟨y, hyact, h1, h2⟩ := hP (σ₀.comp τ)
    have hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
        P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y :=
      fun g hg => hyact g.1 g.2 fun x => DFunLike.congr_fun hg (τ x)
    by_cases hτ : τ' = τ
    · have hμ : σ₀.comp τ = K.1.val := AlgHom.ext fun x => by
        rw [AlgHom.comp_apply, ← hτ]
        exact h₀ x
      obtain ⟨m1, m2⟩ := h1 hμ
      rw [ite_eq_left hτ]
      have m2' : y ∉ (P.PD K).Fil (1 + 1) := by
        rw [show (1 + 1 : ℤ) = 2 by norm_num]
        exact m2
      exact component_line P T ψ τ' σ₀ h₀ y hact 1 m1 m2'
    · have hμ : σ₀.comp τ ≠ K.1.val := fun h => hτ (AlgHom.ext fun x =>
        σ₀.toRingHom.injective ((h₀ x).trans (DFunLike.congr_fun h x).symm))
      obtain ⟨m1, m2⟩ := h2 hμ
      rw [ite_eq_right hτ]
      have m2' : y ∉ (P.PD K).Fil (0 + 1) := by
        rw [zero_add]
        exact m2
      have h3 := component_line P T ψ τ' σ₀ h₀ y hact 0 m1 m2'
      rw [neg_zero] at h3
      exact h3
  refine ⟨?_, fun τ' a => ?_⟩
  · have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
      rw [← GlobalTheory.DeRhamSplit.card_emb K LL hsplit, Nat.card_eq_fintype_card]
    have := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K)
      (PositivityTheory.LocInh.tied_field l P AI T).1 (lineRep ψ)).1
    obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) (lineRep ψ) hc 0
    have hone : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) (lineRep ψ) τ') = 1 := by
      intro τ'
      obtain ⟨z, hz, hgen, -, h2⟩ := hcomponent τ'
      have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
      have hspan : DdRE (P.PD K) (lineRep ψ) τ' = ↥LL.1 ∙ z := by
        refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
        obtain ⟨c, rfl⟩ := hgen w hw
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
      rw [hspan]
      exact finrank_span_singleton hz0
    rw [e1, Finset.sum_congr rfl fun τ' _ => hone τ']
    simp [hc]
  · obtain ⟨z, hz, hgen, h1, h2⟩ := hcomponent τ'
    exact multV_of_gen (P.PD K) (lineRep ψ) τ' _ z hz hgen h1 h2 a
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdeles
section
open scoped Pointwise Topology
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.AddSA

variable {F : Type} [Field F] [NumberField F]

theorem exists_approx_finite (w : InfinitePlace F) (x : InfiniteAdeleRing F)
    (y : FiniteAdeleRing (𝓞 F) F) (O : ∀ v : InfinitePlace F, Set v.Completion)
    (hO : ∀ v, O v ∈ 𝓝 (x v)) {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 y) :
    ∃ t : F, (∀ v, v ≠ w → algebraMap F v.Completion t ∈ O v) ∧
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t ∈ U := by
  classical
  have hW : (fun z => y + z) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  have hdF : (d : F) ≠ 0 := by simpa using hd0
  set e : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (d : F)⁻¹ with he
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ¬ (e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F)}.Finite := by
    have h1 := e.2
    have h2 := (e * y).2
    have := h1.and h2
    exact this
  let T₂ : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
  have hOF : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} ∧
        y v ∈ {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} := by
    intro v
    refine ⟨(Valued.isOpen_valuationSubring _).preimage
      (continuous_const.mul (continuous_id.sub continuous_const)), ?_⟩
    show e v * (y v - y v) ∈ v.adicCompletionIntegers F
    simp
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := GlobalTheory.CompanionTheory.PlaneSA.Additive.exists_approx_core (F := F) (Sum.inl w)
    (Finset.univ.erase w) T₂ (fun v hv h => (Finset.mem_erase.1 hv).1 (Sum.inl_injective h))
    (fun v _ h => by cases h) x O (fun v _ => hO v) (fun v => y v)
    (fun v => {z | e v * (z - y v) ∈ v.adicCompletionIntegers F}) (fun v _ => hOF v)
  refine ⟨t, fun v hv => ht₁ v (Finset.mem_erase.2 ⟨hv, Finset.mem_univ v⟩), ?_⟩
  have hmem : e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
    refine GroundTheory.Global.mem_integralFiniteAdeles.2 fun v => ?_
    by_cases hv : v ∈ T₂
    · exact ht₂ v hv
    · have hv' : e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F := by
        simpa [T₂] using hv
      have h3 := ht₃ v hv (by simp)
      have : (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) v =
          e v * algebraMap F (v.adicCompletion F) t - (e * y) v := by
        show e v * (algebraMap F (v.adicCompletion F) t - y v) = e v * _ - e v * y v
        ring
      rw [this]
      exact sub_mem (mul_mem hv'.1 h3) hv'.2
  have h := hd _ hmem
  have hde : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * e = 1 := by
    rw [he, ← map_mul, mul_inv_cancel₀ hdF, map_one]
  have h4 : y + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) *
      (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t := by
    rw [← mul_assoc, hde]; ring
  simpa only [Set.mem_preimage, h4] using h

theorem dense_add_place : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  intro F _ _ w
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
    (show U ∈ 𝓝 ((a.1, a.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from hU.mem_nhds ha)
  have hU₁' : U₁ ∈ Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := by
    have h : 𝓝 a.1 = Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := nhds_pi
    rwa [← h]
  obtain ⟨I, -, O, hO, hIO⟩ := Filter.mem_pi.1 hU₁'
  obtain ⟨t, ht₁, ht₂⟩ := exists_approx_finite w a.1 a.2 O hO hU₂
  let b : NumberField.AdeleRing (𝓞 F) F :=
    ((Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  refine ⟨algebraMap F _ t + b, ?_, Set.add_mem_add ⟨t, rfl⟩ ⟨rfl, fun v hv => ?_⟩⟩
  · apply hsub
    refine ⟨hIO fun v _ => ?_, ?_⟩
    · by_cases hv : v = w
      · subst hv
        have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = a.1 v := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) v
            (a.1 v - algebraMap F v.Completion t) v = a.1 v
          simp
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact mem_of_mem_nhds (hO v)
      · have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = algebraMap F v.Completion t := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
            (a.1 w - algebraMap F w.Completion t) v = _
          simp [Function.update_of_ne hv]
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact ht₁ v hv
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) t + 0 ∈ U₂
      simpa using ht₂
  · show Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) v = 0
    simp [Function.update_of_ne hv]

end GlobalTheory.CompanionTheory.AddSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentative
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeRepCup

open GlobalTheory.CompanionTheory.CupRep

theorem cupList_cocycle {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) :
    ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → CH.d _ m (cupListC A ℓ) = 0
  | 0, _, _ => by
      funext s
      change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom 1 = (0 : A.obj _)
      rw [Fin.sum_univ_two, map_one, map_one]
      simp
  | m + 1, ℓ, h => by
      change CH.d _ (m + 1) ((CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last m))) = 0
      rw [CrystallineSemistableComparison.P.leibniz, cupList_cocycle A _ (fun k => h _), h]
      simp

theorem cupList_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m
  | 0, _, _ => mem_FC.2 fun s => by
      rw [Nat.cast_zero, hF.top 0 le_rfl]
      exact trivial
  | m + 1, ℓ, h => cup_mem hF (r := m) (r' := 1) _ (cupList_mem hF _ fun k => h _) (h _)

theorem exists_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) :
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  intro hF m ℓ hd hl
  have hm : cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m :=
    cupList_mem hF ℓ fun k => mem_FC.2 fun s => by simpa using hl k s
  refine GlobalTheory.CompanionTheory.ConeLocal.rep_exists (cupListC Φ.A ℓ) (mem_FC.1 hm) fun s => ?_
  rw [cupList_cocycle Φ.A ℓ hd]
  exact (Fil ((m : ℤ) + 1)).S _ |>.zero_mem

end GlobalTheory.CompanionTheory.ConeRepCup
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_subobject_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (E : X.Modules), E.IsQuasicoherent → ∀ (n : ℕ) (V : X.Opens), IsAffineOpen V → secs (powSub I E n) V = ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_powSub | exact GlobalTheory.CompanionTheory.GE.secs_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.secs_powSub <;> assumption)
end

