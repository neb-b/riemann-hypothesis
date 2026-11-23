module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.GaloisRepTransportOfCopyAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem multiset_eq_of_esymm (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem isRepOf_of_split (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.HeckeEigenspaceDescentOfEquivariantEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem joint_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

open scoped TensorProduct in
private theorem desc_exists (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ (rd : ↥D.LL0 →+* FractionRing (D.ntw.O i)) (Φ : S.WL j →+ Fm S i j b), (∀ c, rd c = readLL0 S i b c) ∧
      (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = rd c • Φ x) ∧
      (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actG S i j b (In.rho j h1 h2) (In.chi j h1 h2) g (Φ x)) ∧
      (∀ k P x, Φ (In.hL j k P x) = hkF D S i j b (In.hL j) (In.hs j h1 h2) k P (Φ x)) ∧
      Submodule.span (FractionRing (D.ntw.O i)) (Set.range Φ) = ⊤ := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  obtain ⟨Φ, hc, hf, hw⟩ := _root_.GlobalTheory.exists_semilinear_descent_to_baseChange D.LL0 S.kKs S.kKs_spec (S.A j).WK bs hb hKs hLi hLs
    (KT := KB S i b) (readLL0 S i b) (fun s => rfl)
  refine ⟨readLL0 S i b, Φ, fun _ => rfl, hc, fun g x => ?_, fun k P x => ?_, ?_⟩
  · have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
        (S.A j).ρ (S.eG.symm g) x := by
      simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
    have e2 := hc ((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹) ((S.A j).ρ (S.eG.symm g) x)
    rw [← e1, hf ((S.A j).ρ (S.eG.symm g)) (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl), map_inv₀] at e2
    exact e2
  · exact hf (In.hL j k P) _ (fun w => rfl) x
  · refine top_le_iff.1 ?_
    have h := GlobalTheory.HeightCounting.FormsSpan.span_one_tmul (R := S.Ks) (A := KB S i b) (M := ↥(S.A j).WK)
    refine (le_of_eq h.symm).trans (Submodule.span_mono ?_)
    rintro _ ⟨w, rfl⟩
    exact ⟨(w : S.WL j), hw w⟩

open GlobalTheory.HeightCounting.FormsSpan Formalism.MainNotions.IntegralHeckeForms in
private theorem hermFramePairNormalForm_frameSpan_le_of_generators (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (hU : D.nexp.U = Formalism.IndefR.NX.U D.nd)
    (hψ : PsiLaw D S In.θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (rd : ↥D.LL0 →+* FractionRing (D.ntw.O i)) (Ψ : S.WL j →+ D.nexp.Fm i j b) (hrd : ∀ c, rd c = readLL0 S i b c)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Ψ ((c : D.what₂.LL) • x) = rd c • Ψ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Ψ (actL D S j g x) = D.nexp.actG i j b g (Ψ x))
    (hs : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) = ⊤) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j))) := by
  classical
  letI : Fintype (G0g D.nd) := finiteLevelGroupFintype D
  letI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := fintypeU
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  let pr : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
    ∑ u : ↥(Formalism.IndefR.NX.U D.nd), rd (cU D In.θ u) • (D.nexp.actG i j b u).toLinearMap
  have hpr : ∀ w, pr (Ψ w) = Ψ (projL (S := S) In.θ j w) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pr, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hc, ha]
  have hE : ∀ x, eG D.nexp i j b (Ψ x) = Ψ (opL D S j (GlobalTheory.HeightCounting.FormsStep.eL D) x) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [opL_eL, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, eG, MonoidAlgebra.lift_apply,
      Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, D.nexp.eAlg_def, hrd]
    rfl
  have hfix : pr z = z := by
    have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), D.nexp.actG i j b u z =
        rd ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
      intro u
      have hu' : (u : G0g D.nd) ∈ D.nexp.U := by rw [hU]; exact u.2
      have h := (Submodule.mem_iInf _).mp hz ⟨u, hu'⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hψ i b u hu' u.2, ← hrd] at h
      exact h
    simp only [pr, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
    have hcu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
        (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
      intro u
      unfold cU
      rw [map_inv, Units.val_inv_eq_inv_val]
      have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
      field_simp
    simp only [hcu, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (D.ntw.O i)), smul_smul]
    have hne : rd (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
      refine (map_ne_zero rd).mpr fun h => ?_
      have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
      exact Fintype.card_ne_zero (by exact_mod_cast h')
    have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (D.ntw.O i)) *
        rd (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
      rw [map_inv₀, ← map_natCast rd]
      exact mul_inv_cancel₀ hne
    rw [h1, one_smul]
  rw [← hfix]
  have key : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) ≤
      (Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eG D.nexp i j b ∘ₗ pr) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eG D.nexp i j b (pr (Ψ w)) ∈
      Submodule.span (FractionRing (D.ntw.O i)) (Ψ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [hpr, hE]
    exact Submodule.subset_span ⟨_, goodL_of (GlobalTheory.HeightCounting.FormsStep.eIdem_all D) In.θ j w, rfl⟩
  exact key (Submodule.eq_top_iff'.mp hs z)

theorem UpperTheory.heckeEigenspace_descent_of_equivariant_equiv :
    ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S), D.nexp.U = Formalism.IndefR.NX.U D.nd → PsiLaw D S In.θ → (∀ i, In.Sb ⊆ D.ntw.S0 i) → ∀ (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] Fm S i j b), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (g : G0g D.nd) (y : D.nexp.Fm i j b), eF i j b h1 h2 (D.nexp.actG i j b g y) = actG S i j b (In.rho j h1 h2) (In.chi j h1 h2) g (eF i j b h1 h2 y)) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (y : D.nexp.Fm i j b), P ∉ D.ntw.S0 i → IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P y) = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (In.hL j) (In.hs j h1 h2) k P (eF i j b h1 h2 y)) → ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m → ∀ ev : ℕ → PlE D.host → FractionRing (D.ntw.O i), GlobalTheory.EigTie.IsEigSys D.nexp i j b ev → ∃ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ev k P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k * (show FractionRing (D.ntw.O i) from readLL0 S i b (In.eig j σ k P)) := by
  intro D S In hU hψ hSb c eF hact hhk i j b h1 h2 ev hev
  classical
  obtain ⟨y, hyV, hy0, hyE⟩ := hev
  obtain ⟨rd, Φ, hrd, hc, ha, hh, hs⟩ := desc_exists D S In i j b h1 h2
  set e := eF i j b h1 h2 with he
  let Ψ : S.WL j →+ D.nexp.Fm i j b := e.symm.toLinearMap.toAddMonoidHom.comp Φ
  have hΨ : ∀ x, e (Ψ x) = Φ x := fun x => e.apply_symm_apply _
  have hc' : ∀ (c : ↥D.LL0) (x : S.WL j), Ψ ((c : D.what₂.LL) • x) = rd c • Ψ x := fun c x => by
    apply e.injective
    rw [hΨ, hc, map_smul, hΨ]
  have ha' : ∀ (g : G0g D.nd) (x : S.WL j), Ψ (actL D S j g x) = D.nexp.actG i j b g (Ψ x) := fun g x => by
    apply e.injective
    rw [hact i j b h1 h2, hΨ, hΨ, ha]
  have hs' : Submodule.span (FractionRing (D.ntw.O i)) (Set.range Ψ) = ⊤ := by
    have : Set.range Ψ = e.symm.toLinearMap '' Set.range Φ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  have hle := hermFramePairNormalForm_frameSpan_le_of_generators D S In hU hψ i j b rd Ψ hrd hc' ha' hs' hyV
  by_contra hno
  apply hy0
  let sys : D.what₂.FT → ℕ × PlE D.host → FractionRing (D.ntw.O i) := fun σ t =>
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b t.2) ^ t.1 * rd (In.eig j σ t.1 t.2)
  have hfin : {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}.Finite := Set.toFinite _
  refine joint_zero (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => Formalism.MainNotions.IntegralHeckeForms.HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) (hfin.toFinset.image sys) y ?_ (fun t ht => hyE t.1 t.2 ht) (Submodule.span_le.mpr ?_ hle)
  · intro μ hμ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hμ
    rw [Set.Finite.mem_toFinset] at hσ
    by_contra hne
    push_neg at hne
    refine hno ⟨σ, hσ.1, hσ.2, fun k P a1 a2 a3 a4 => ?_⟩
    have := hne (k, P) ⟨a1, a2, a3, a4⟩
    simp only [sys, hrd] at this
    exact this.symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe]
    refine Submodule.iSup_induction (motive := fun y => Ψ y ∈ _) _ (In.span j h1 h2 hx) ?_ ?_ ?_
    · intro σ w hw
      refine Submodule.iSup_induction (motive := fun y => Ψ y ∈ _) _ hw ?_ ?_ ?_
      · intro hσ z hz
        refine Submodule.subset_span ⟨sys σ, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hσ), ?_⟩
        rintro ⟨k, P⟩ ⟨a1, a2, a3, a4⟩
        have hz2 := (Submodule.mem_inf.1 hz).2
        simp only [Submodule.mem_iInf] at hz2
        have h3 := Module.End.mem_eigenspace_iff.1 (hz2 k P ⟨a1, a2, a3, fun h => a4 (hSb i h)⟩)
        apply e.injective
        simp only [sys]
        rw [hhk i j b h1 h2 k P _ a4 a3 a2, map_smul, hΨ, ← hh, h3, hc, mul_smul]
      · rw [map_zero]; exact zero_mem _
      · intro y z hy hz; rw [map_add]; exact add_mem hy hz
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.NonemptyCoefficientRingDataOfIsomorphicCMDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem readMove {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A K L L' : Type} [CommRing A] [CommRing K]
    [CommRing L] [CommRing L'] {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω} {φ : G E Ω →* Aˣ} {rd : A →+* K} {eL : L →+* K}
    {c : L →+* ℂ} {χ : NC.HC E} {w : ℤ} (h : NC.Read pl φ rd eL c χ w) (e : L' ≃+* L) (eL' : L' →+* K) (c' : L' →+* ℂ)
    (h1 : ∀ x, eL (e x) = eL' x) (h2 : ∀ x, c (e x) = c' x) : NC.Read pl φ rd eL' c' χ w := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun P hP => ?_⟩
  obtain ⟨α, hα, x, hx, hσ⟩ := hB P hP
  refine ⟨α, hα, e.symm x, ?_, fun σ hs => ?_⟩
  · rw [← h2, e.apply_symm_apply, hx]
  · rw [← h1, e.apply_symm_apply]; exact hσ σ hs

private theorem plMove {L L' K : Type} [Field L] [Field L'] [CommRing K] (e : L' ≃+* L) (f : L →+* K) (f' : L' →+* K)
    (h1 : ∀ x, f (e x) = f' x) (l : ℕ) (p : K → Prop)
    (h : ∃ w : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∈ w.asIdeal ∧ ∀ x : 𝓞 L, x ∈ w.asIdeal ↔ p (f (x : L))) :
    ∃ w : HeightOneSpectrum (𝓞 L'), (l : 𝓞 L') ∈ w.asIdeal ∧ ∀ x : 𝓞 L', x ∈ w.asIdeal ↔ p (f' (x : L')) := by
  obtain ⟨w, hl, hw⟩ := h
  let g : 𝓞 L' ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (g : 𝓞 L' →+* 𝓞 L), Ideal.comap_isPrime _ _, fun hb => w.ne_bot ?_⟩, ?_, fun x => ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    have : g.symm y ∈ w.asIdeal.comap (g : 𝓞 L' →+* 𝓞 L) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [hb, Ideal.mem_bot] at this
    simpa using this
  · simpa using hl
  · rw [← h1]
    exact hw (g x)

private theorem mid {D : D7} {cf : CharFrame D} {low : Finset ℕ} (B : RingPart D cf low) {L' : Type} [Field L'] (e : L' ≃+* ↥D.LL0)
    (m mb : ∀ i, L' →+* FractionRing (D.ntw.O0 i)) (c : L' →+* ℂ)
    (hm : ∀ i x, D.ntw.emb0 i (e x) = m i x) (hmb : ∀ i x, D.ntw.emb0b i (e x) = mb i x) (hc : ∀ x, embLL0 D (e x) = c x)
    (jL : ∀ i, D.ntw.abelian₂ i → ℕ) (hjL : D.ntw.jL = jL) (s2 : ∀ i, D.ntw.abelian₂ i → ℤ) (hs2 : D.ntw.s2 = s2)
    (lamG : ∀ i, D.ntw.abelian₂ i → (G D.host.E D.nd.Om →* (D.ntw.O i)ˣ)) (hlamG : D.ntw.lamG = lamG)
    (qs : ∀ i, D.ntw.abelian₂ i → HeightOneSpectrum (𝓞 D.host.E) → FractionRing (D.ntw.O i)) (hqs : D.ntw.qs = qs)
    (mu0 : Fin D.R.m → HChar D.host.E) (hmu0 : cf.mu0 = mu0) (eta : HChar D.host.E) (heta : cf.eta = eta)
    (del : HChar D.host.E) (hdel : cf.del = del) (del' : HChar D.host.E) (hdel' : cf.del' = del') :
    (∀ i, ∃ w : HeightOneSpectrum (𝓞 L'), ((D.ntw.l i : ℕ) : 𝓞 L') ∈ w.asIdeal ∧
      ∀ x : 𝓞 L', x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = m i (x : L')) ∧
    (∀ i (x : L') (y z : D.ntw.O0 i), z ≠ 0 →
      (m i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y ↔
        ((B.twF.j0 i).comp e.toRingHom) x * (B.twF.eO0 i z : PadicAlgCl (D.ntw.l i)) = (B.twF.eO0 i y : PadicAlgCl (D.ntw.l i)))) ∧
    (∀ i lam P, P ∉ D.ntw.S0 i →
      B.twF.iCq i (qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(s2 i lam : ℝ) / 2) : ℝ) : ℂ)) ∧
    (∀ s, NC.Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (m s) c (B.chiD.del s) 0) ∧
    (∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → NC.Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
      (if b then m s else mb s) c (B.chiD.firstHeckeCharacter s j) (-(D.R.r : ℤ))) ∧
    (∀ s (b : Bool) (x : L') (y : D.ntw.O0 s),
      algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then m s else mb s) x →
      ((B.chiD.embO s b).comp e.toRingHom) x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)) ∧
    (∀ s lam, NC.Read D.nd.plOm.1 (lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
      ((B.chiD.embO s (D.ntw.sideL s lam)).comp e.toRingHom) c (B.chiD.mu0 (jL s lam) * B.chiD.del s * (B.chiD.chiI s lam)⁻¹) 0) ∧
    (∀ x, B.chiD.etaT.χ x = eta.1 x) ∧
    (∀ (j : Fin D.R.m) x, (B.chiD.mu0 (j.1 + 1)).χ x = (mu0 j).1 x) ∧
    (∀ s x, (B.chiD.del s).χ x = (if D.ntw.l s = D.host.pde then del' else del).1 x) ∧
    (∀ s (x : L'), B.twF.iCq s (((B.chiD.embO s true).comp e.toRingHom) x) = c x) ∧
    (∀ s (x y : L'), c y = starRingEnd ℂ (c x) →
      ((B.chiD.embO s false).comp e.toRingHom) x = ((B.chiD.embO s true).comp e.toRingHom) y) ∧
    (∀ (s : D.ntw.Tw) (w : PlE D.host), w ∉ placesOver D.host.E (D.ntw.l s) → (if D.ntw.l s = D.host.pde then del' else del).UnrAt w →
      ∀ (A : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) A w →
        IsFrob (F := D.host.E) A (normV w) σ →
        ∃ x : L', c x = (((if D.ntw.l s = D.host.pde then del' else del).val w)⁻¹ : ℂˣ).1 ∧
          algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) ((D.ntw.delta s σ : (D.ntw.O0 s)ˣ) : D.ntw.O0 s) = m s x) := by
  subst hjL hs2 hlamG hqs hmu0 heta hdel hdel'
  have hb : ∀ s (b : Bool) x, (if b then D.ntw.emb0 s else D.ntw.emb0b s) (e x) = (if b then m s else mb s) x := by
    intro s b x
    cases b
    · exact hmb s x
    · exact hm s x
  refine ⟨fun i => ?_, fun i x y z hz => ?_, B.tw.qs_pos, fun s => readMove (B.chi.delta s) e _ _ (hm s) hc,
    fun s j b h1 h2 => readMove (B.chi.chi1 s j b h1 h2) e _ _ (hb s b) hc, fun s b x y hy => ?_,
    fun s lam => readMove (B.chi.lamG s lam) e _ _ (fun _ => rfl) hc, B.eta_eq, B.ringSpec_normalisedCharacter_eq, B.del_eq, fun s x => ?_,
    fun s x y hy => ?_, fun s w h1 h2 A σ h3 h4 => ?_⟩
  · exact plMove e (D.ntw.emb0 i) (m i) (hm i) (D.ntw.l i) (fun k => ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = k) (B.tw.pl_emb i)
  · rw [← hm]
    exact B.tw.ringSpec_baseEmbedding_compatible i (e x) y z hz
  · rw [← hb] at hy
    exact B.chi.ringSpec_sidedEmbedding_fixedField s b (e x) y hy
  · rw [← hc]
    exact B.iCq_embO s (e x)
  · refine B.embO_star s (e x) (e y) (D.what₂.embLL.injective ?_)
    rw [← hc, ← hc] at hy
    rw [D.starLL_cx]
    exact hy
  · obtain ⟨x, hx, hx'⟩ := B.deltaRead s w h1 h2 A σ h3 h4
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [← hc, e.apply_symm_apply]
      exact hx
    · rw [← hm, e.apply_symm_apply]
      exact hx'

theorem UpperTheory.nonempty_coefficientRingData_of_isomorphic_CMDatum :
    ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → IsEmpty D'.nd.Loc → ∀ low : Finset ℕ, RingPart D cf low → Nonempty (RingPart D' cf' low) := by
  intro D D' ι e h cf cf' hf hE low B
  have hst : ∀ x y : ↥D'.LL0, (y : D'.what₂.LL) = star (x : D'.what₂.LL) → embLL0 D' y = starRingEnd ℂ (embLL0 D' x) :=
    fun x y hy => (congrArg D'.what₂.embLL hy).trans (D'.starLL_cx _)
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := mid B e ((by with_unfolding_all exact ((overD D r).ntw.emb0 :)))
    ((by with_unfolding_all exact ((overD D r).ntw.emb0b :))) (embLL0 (overD D r))
    (fun i x => eq_of_heq ((by with_unfolding_all exact ((h.cp.emb0 i ((i)) (((HEq.refl i))) x) : _))))
    (fun i x => eq_of_heq ((by with_unfolding_all exact ((h.cp.emb0b i ((i)) (((HEq.refl i))) x) : _)))) h.cp.embLL0_eq
    ((by with_unfolding_all exact ((overD D r).ntw.jL :))) (eq_of_heq ((by with_unfolding_all exact (h.jL :)))) ((by with_unfolding_all exact ((overD D r).ntw.s2 :))) (eq_of_heq ((by with_unfolding_all exact (h.s2 :))))
    ((by with_unfolding_all exact ((overD D r).ntw.lamG :))) (eq_of_heq ((by with_unfolding_all exact (h.lamG :)))) ((by with_unfolding_all exact ((overD D r).ntw.qs :))) (eq_of_heq ((by with_unfolding_all exact (h.qs :))))
    ((by with_unfolding_all exact (cf'.mu0 :))) (eq_of_heq ((by with_unfolding_all exact (hf.mu0 :)))) ((by with_unfolding_all exact (cf'.eta :))) (eq_of_heq ((by with_unfolding_all exact (hf.eta :))))
    ((by with_unfolding_all exact (cf'.del :))) (eq_of_heq ((by with_unfolding_all exact (hf.del :)))) ((by with_unfolding_all exact (cf'.del' :))) (eq_of_heq ((by with_unfolding_all exact (hf.del' :))))
  exact ⟨⟨⟨(by with_unfolding_all exact (B.twF.K0 :)), (by with_unfolding_all exact (B.twF.eO0 :)), (by with_unfolding_all exact ((fun i => (B.twF.j0 i).comp e.toRingHom) :)), (by with_unfolding_all exact (B.twF.Lw :)),
      (by with_unfolding_all exact (B.twF.eO :)), (by with_unfolding_all exact (B.twF.eOk :)), (by with_unfolding_all exact (B.twF.iCq :)), (by with_unfolding_all exact (B.twF.S0x :))⟩,
    ⟨(by with_unfolding_all exact (m1 :)), (by with_unfolding_all exact (B.tw.ringSpec_baseIntegersEquiv_algebraMap :)), (by with_unfolding_all exact (m2 :)), (by with_unfolding_all exact (B.tw.eO_alg :)), (by with_unfolding_all exact (B.tw.eOk_alg :)), (by with_unfolding_all exact (B.tw.mu_g :)),
      (by with_unfolding_all exact (B.tw.hk_split :)), (by with_unfolding_all exact (B.tw.ringSpec_excludedPlaces_eq :)), (by with_unfolding_all exact (B.tw.concreteTwistFrame_extraExcludedPlaces_conj :)), (by with_unfolding_all exact (B.tw.B_range :)), (by with_unfolding_all exact (B.tw.sig_inj :)),
      (by with_unfolding_all exact (m3 :)), (by with_unfolding_all exact (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes :))⟩,
    ⟨(by with_unfolding_all exact (B.chiD.mu0 :)), (by with_unfolding_all exact (B.chiD.etaT :)), (by with_unfolding_all exact (B.chiD.del :)), fun a => hE.elim a, (by with_unfolding_all exact (B.chiD.chiI :)),
      (by with_unfolding_all exact ((fun s b => (B.chiD.embO s b).comp e.toRingHom) :))⟩,
    ⟨fun a => hE.elim a, (by with_unfolding_all exact (B.chi.del_fix :)), (by with_unfolding_all exact (m4 :)), (by with_unfolding_all exact (m5 :)), (by with_unfolding_all exact (m6 :)), (by with_unfolding_all exact (B.chi.etaT_unr :)),
      (by with_unfolding_all exact (B.chi.etaT_inf :)), (by with_unfolding_all exact (m7 :))⟩,
    (by with_unfolding_all exact (m8 :)), (by with_unfolding_all exact (m9 :)), (by with_unfolding_all exact (m10 :)), (by with_unfolding_all exact (m11 :)),
    (by with_unfolding_all exact ((fun s x y hy => m12 s x y (hst x y hy)) :)), (by with_unfolding_all exact (m13 :))⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.SidePlaceExistsOfCopyAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem under_le_one {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (ι : K →+* L)
    (w : HeightOneSpectrum (𝓞 L)) : ∃ v : HeightOneSpectrum (𝓞 K),
    (∀ x : K, v.valuation K x ≤ 1 ↔ w.valuation L (ι x) ≤ 1) ∧
    (∀ x : K, v.valuation K x < 1 ↔ w.valuation L (ι x) < 1) := by
  letI : Algebra K L := ι.toAlgebra
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot] at he
  refine ⟨w.under (𝓞 K), fun x => ?_, fun x => ?_⟩
  · have h := HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w x
    change _ ↔ w.valuation L (algebraMap K L x) ≤ 1
    rw [← h, pow_le_one_iff he]
  · have h := HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w x
    change _ ↔ w.valuation L (algebraMap K L x) < 1
    rw [← h, pow_lt_one_iff he]

private theorem val_nonneg_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg,
      WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]

private theorem val_resChar_lt (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL (D.what₂.places.resChar w : D.what₂.LL) < 1 := by
  have hx : (D.what₂.places.resChar w : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h0 : (D.plEq w).valuation D.what₂.LL (D.what₂.places.resChar w : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hx, WithTop.coe_inj, vAdd] at h
  have hp := D.what₂.places.ramIdx_pos w
  rw [← WithZero.exp_zero, ← WithZero.log_lt_iff_lt_exp h0]
  omega

private theorem prime_eq_of_lt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h1 : w.valuation L (p : L) < 1) (h2 : w.valuation L (q : L) < 1) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : 𝓞 L) (q : 𝓞 L) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  have a1 : (p : 𝓞 L) ∈ w.asIdeal := (w.valuation_lt_one_iff_mem (K := L) _).1 (by simpa using h1)
  have a2 : (q : 𝓞 L) ∈ w.asIdeal := (w.valuation_lt_one_iff_mem (K := L) _).1 (by simpa using h2)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ a1) (w.asIdeal.mul_mem_left _ a2)))

private theorem exists_under {D D' : D7} (ι : D.what₂.LL →+* D'.what₂.LL) (w' : D'.what₂.places.Pl) :
    ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = D'.what₂.places.resChar w' ∧
      ∀ x, 0 ≤ D.what₂.places.val w x ↔ 0 ≤ D'.what₂.places.val w' (ι x) := by
  obtain ⟨v, h1, h2⟩ := under_le_one ι (D'.plEq w')
  obtain ⟨w, rfl⟩ := D.plEq.surjective v
  refine ⟨w, ?_, fun x => ?_⟩
  · have a := (h2 _).1 (val_resChar_lt D w)
    rw [map_natCast] at a
    exact prime_eq_of_lt _ (D.what₂.places.resChar_prime w) (D'.what₂.places.resChar_prime w') a (val_resChar_lt D' w')
  · rw [val_nonneg_iff, val_nonneg_iff, h1]

theorem UpperTheory.sidePlace_exists_of_copyAll :
    ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → (∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D w i true) → ∀ w : D'.what₂.places.Pl, ∃ i, D'.ntw.l i = D'.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D' w i true := by
  intro D D' ι e h H w'
  obtain ⟨w, hr, hv⟩ := exists_under ι w'
  obtain ⟨i, hl, hs⟩ := H w
  have hL := h.cp.LL0
  have hE := h.cp.emb0
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  refine ⟨i, hl.trans hr, fun x => ?_⟩
  have a := hs (e x)
  rw [hv, hL x] at a
  have b : D.ntw.emb0 i (e x) = (overD D r).ntw.emb0 i x := eq_of_heq (hE i i HEq.rfl x)
  rw [if_pos rfl, b] at a
  rw [if_pos rfl]
  exact a
end

