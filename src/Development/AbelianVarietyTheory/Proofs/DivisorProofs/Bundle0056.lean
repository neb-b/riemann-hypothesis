module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorsIrreducibleSubrepDecomposition
section
open Submodule

namespace GlobalTheory.AbsDec

theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (ht : iSupIndep t) :
    ∃ T : ι → V →ₗ[ℂ] V, (∀ i v, T i v ∈ t i) ∧
      (∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (⨆ i, t i)
  have hcompl : ∀ i, IsCompl (t i) ((⨆ (j) (_ : j ≠ i), t j) ⊔ C) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨q, hq, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
      have hcQ : c ∈ ⨆ i, t i := by
        have h1 : q + c ∈ ⨆ i, t i := Submodule.mem_iSup_of_mem i hx
        have h2 : q ∈ ⨆ i, t i :=
          (iSup₂_le fun j _ => le_iSup t j : (⨆ (j) (_ : j ≠ i), t j) ≤ ⨆ i, t i) hq
        simpa using Submodule.sub_mem _ h1 h2
      have hc0 : c = 0 := (Submodule.disjoint_def.1 hC.disjoint) c hcQ hc
      subst hc0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 ((iSupIndep_def.1 ht) i)) q hx hq
    · rw [codisjoint_iff, eq_top_iff, ← hC.sup_eq_top]
      refine sup_le (iSup_le fun j => ?_) (le_sup_of_le_right le_sup_right)
      by_cases h : j = i
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le j h le_rfl))
  refine ⟨fun i => (t i).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ (hcompl i),
    fun i v => ?_, fun i j v hv => ?_⟩
  · simp
  · split_ifs with h
    · subst h
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hcompl i) ⟨v, hv⟩)
    · have hv' : v ∈ (⨆ (k) (_ : k ≠ i), t k) ⊔ C :=
        Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm h) hv))
      have := Submodule.linearProjOfIsCompl_apply_right (hcompl i) ⟨v, hv'⟩
      exact congrArg Subtype.val this

theorem sum_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) {v : V} (hv : v ∈ ⨆ i, t i) :
    ∑ i, T i v = v := by
  refine Submodule.iSup_induction t (motive := fun v => ∑ i, T i v = v) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · simp [hT _ j x hx]
  · simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]

theorem proj_comm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0)
    (hst : ∀ j g, ∀ v ∈ t j, ρ g v ∈ t j) (i : ι) (g : G) {v : V} (hv : v ∈ ⨆ j, t j) :
    T i (ρ g v) = ρ g (T i v) := by
  refine Submodule.iSup_induction t (motive := fun v => T i (ρ g v) = ρ g (T i v)) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · rw [hT i j _ (hst j g x hx), hT i j x hx]
    split_ifs <;> simp
  · simp only [map_add (f := _), hx, hy]

end GlobalTheory.AbsDec

namespace GlobalTheory.AbsDec

theorem fixed_decomposition : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  intro G V _ _ _ ρ K F hF 𝒜 h𝒜 hfd
  classical
  let good : Finset (Submodule ℂ V) → Prop := fun s =>
    (∀ P ∈ s, P ∈ 𝒜 ∧ P ⊓ F ≠ ⊥) ∧ s.SupIndep id
  have bound : ∀ s, good s → s.card ≤ Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := by
    intro s hs
    have hv : ∀ P : s, ∃ v, v ∈ (P : Submodule ℂ V) ⊓ F ∧ v ≠ 0 := fun P =>
      Submodule.exists_mem_ne_zero_of_ne_bot (hs.1 P P.2).2
    choose v hv0 hvne using hv
    have hind : iSupIndep (fun P : s => (P : Submodule ℂ V) ⊓ F) :=
      ((iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2).mono fun P => inf_le_left
    have hli : LinearIndependent ℂ v := hind.linearIndependent _ hv0 hvne
    have hvM : ∀ P : s, v P ∈ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := fun P =>
      (le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (P : Submodule ℂ V) (hs.1 P P.2).1 le_rfl) (hv0 P)
    have hli' : LinearIndependent ℂ
        (fun P : s => (⟨v P, hvM P⟩ : (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    simpa using hli'.fintype_card_le_finrank
  have h0 : ∃ s, good s ∧ s.card = 0 := ⟨∅, ⟨by simp, Finset.supIndep_empty _⟩, rfl⟩
  obtain ⟨s, hs, hsN⟩ := Nat.findGreatest_spec (P := fun n => ∃ s, good s ∧ s.card = n)
    (Nat.zero_le (Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) h0
  have hmax : ∀ s', good s' → s'.card ≤ s.card := by
    intro s' hs'
    rw [hsN]
    by_contra hlt
    push_neg at hlt
    exact Nat.findGreatest_is_greatest hlt (bound s' hs') ⟨s', hs', rfl⟩
  have hQ : ∀ g, ∀ v ∈ ⨆ P : s, (P : Submodule ℂ V), ρ g v ∈ ⨆ P : s, (P : Submodule ℂ V) := by
    intro g v hv
    have : (⨆ P : s, (P : Submodule ℂ V)) ≤ (⨆ P : s, (P : Submodule ℂ V)).comap (ρ g) :=
      iSup_le fun P w hw => Submodule.mem_iSup_of_mem P ((h𝒜 P (hs.1 P P.2).1).2.1 g w hw)
    exact this hv
  have hsup : s.sup id = ⨆ P : s, (P : Submodule ℂ V) := by
    rw [Finset.sup_eq_iSup, iSup_subtype']
    rfl
  have hcover : ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → P ≤ ⨆ Q : s, (Q : Submodule ℂ V) := by
    intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    rcases hirr (P ⊓ ⨆ Q : s, (Q : Submodule ℂ V)) inf_le_left
      (fun g v hv => ⟨hst g v hv.1, hQ g v hv.2⟩) with h | h
    · exfalso
      have hPs : P ∉ s := by
        intro hPs
        have hle : P ≤ P ⊓ ⨆ Q : s, (Q : Submodule ℂ V) :=
          le_inf le_rfl (le_iSup_of_le (⟨P, hPs⟩ : s) le_rfl)
        rw [h] at hle
        exact hne (eq_bot_iff.2 hle)
      have hgood : good (insert P s) := by
        refine ⟨fun R hR => ?_, hs.2.insert ?_⟩
        · rcases Finset.mem_insert.1 hR with rfl | hR
          · exact ⟨hP, hPF⟩
          · exact hs.1 R hR
        · rw [hsup, disjoint_iff]
          exact h
      have := hmax _ hgood
      rw [Finset.card_insert_of_notMem hPs] at this
      omega
    · rw [← h]
      exact inf_le_right
  have hind : iSupIndep (fun P : s => (P : Submodule ℂ V)) :=
    (iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2
  obtain ⟨T, hTmem, hT⟩ := exists_proj (fun P : s => (P : Submodule ℂ V)) hind
  have hst' : ∀ (j : s) g, ∀ v ∈ (j : Submodule ℂ V), ρ g v ∈ (j : Submodule ℂ V) :=
    fun j => (h𝒜 j (hs.1 j j.2).1).2.1
  refine ⟨s, inferInstance, fun P => P, fun i => hs.1 i i.2, hind.mono fun i => inf_le_left,
    ?_, ?_⟩
  · apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (i : Submodule ℂ V) (hs.1 i i.2).1 le_rfl
    · refine iSup₂_le fun P hP => ?_
      by_cases hPF : P ⊓ F = ⊥
      · rw [hPF]
        exact bot_le
      intro φ hφ
      have hφQ := hcover P hP hPF hφ.1
      rw [← sum_proj _ T hT hφQ]
      refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨hTmem i φ, ?_⟩
      refine (hF _).2 fun k hk => ?_
      rw [← proj_comm ρ _ T hT hst' i k hφQ, (hF φ).1 hφ.2 k hk]
  · intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    have hPQ := hcover P hP hPF
    have hex : ∃ i, ∀ v ∈ P, T i v = 0 → v = 0 := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ i, ∀ v ∈ P, T i v = 0 := by
        intro i
        obtain ⟨w, hwP, hw0, hwne⟩ := hcon i
        rcases hirr (P ⊓ LinearMap.ker (T i)) inf_le_left (fun g v hv => ⟨hst g v hv.1,
            LinearMap.mem_ker.2 (by
              rw [proj_comm ρ _ T hT hst' i g (hPQ hv.1), LinearMap.mem_ker.1 hv.2, map_zero])⟩)
          with h | h
        · exact absurd ((Submodule.eq_bot_iff _).1 h w ⟨hwP, hw0⟩) hwne
        · intro v hv
          have hv' : v ∈ P ⊓ LinearMap.ker (T i) := by rw [h]; exact hv
          exact hv'.2
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hvne
      rw [← sum_proj _ T hT (hPQ hv)]
      exact Finset.sum_eq_zero fun i _ => hall i v hv
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, T i, fun v _ => hTmem i v, hi, fun g v hv => proj_comm ρ _ T hT hst' i g (hPQ hv)⟩

end GlobalTheory.AbsDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem flat_quot_smul_top_of_surj_flat :
    ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B]
      (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ →
      Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ →
      RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat →
      Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  intro P R₁ B B₁ _ _ _ _ _ f₁ a₁ c₁ hf hc hcomp hker ha
  set K := RingHom.ker f₁ with hK
  let σ : P ⧸ K ≃+* R₁ := RingHom.quotientKerEquivOfSurjective hf
  have hσ : ((a₁.comp (σ : P ⧸ K →+* R₁))).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective) ha
  letI : Algebra (P ⧸ K) B₁ := (a₁.comp (σ : P ⧸ K →+* R₁)).toAlgebra
  haveI : Module.Flat (P ⧸ K) B₁ := hσ
  letI : Algebra P B₁ := (c₁.comp (algebraMap P B)).toAlgebra
  let g : B →ₗ[P] B₁ :=
    { toFun := c₁
      map_add' := c₁.map_add
      map_smul' := fun p b => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rfl }
  have hg : ∀ b, g b = c₁ b := fun _ => rfl
  have hkerg : LinearMap.ker g = (K • ⊤ : Submodule P B) := by
    ext b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker, LinearMap.mem_ker,
      RingHom.mem_ker, hg]
  have hle : (K • ⊤ : Submodule P B) ≤ LinearMap.ker g := hkerg.ge
  let e₀ := (K • ⊤ : Submodule P B).liftQ g hle
  have he₀ : Function.Bijective e₀ := by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hkerg.le
    · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hc
  let e : (B ⧸ (K • ⊤ : Submodule P B)) ≃ₗ[P ⧸ K] B₁ :=
    LinearEquiv.ofBijective
      { toFun := e₀
        map_add' := e₀.map_add
        map_smul' := fun q x => by
          obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
          have h1 : (Ideal.Quotient.mk K p) • x = p • x := by
            rw [← IsScalarTower.algebraMap_smul (P ⧸ K) p x]
            rfl
          rw [h1, e₀.map_smul, RingHom.id_apply]
          change (c₁.comp (algebraMap P B)) p * e₀ x = a₁ (σ (Ideal.Quotient.mk K p)) * e₀ x
          rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hcomp]
          rfl }
      he₀
  exact Module.Flat.of_linearEquiv e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
section
open scoped TensorProduct

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem formallyEtale_mvPolynomial_eval₂_tensor {k R B : Type} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B)
    (hf : (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  set f := MvPolynomial.eval₂Hom (algebraMap k B) τ with hfdef
  set g := MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i) with hgdef
  letI : Algebra (MvPolynomial (Fin r) k) B := f.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) (R ⊗[k] B) := g.toAlgebra
  letI : Algebra B (R ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (MvPolynomial (Fin r) k) (R ⊗[k] B) :=
    (g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R))).toAlgebra
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) k) B := hf
  have key : g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R)) =
      (algebraMap B (R ⊗[k] B)).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C, f, g,
        MvPolynomial.eval₂Hom_C]
      show (algebraMap k R a) ⊗ₜ[k] (1 : B) = (1 : R) ⊗ₜ[k] algebraMap k B a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X, f, g,
        MvPolynomial.eval₂Hom_X']
      rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) B := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def]
  haveI : IsScalarTower k B (R ⊗[k] B) := IsScalarTower.of_algebraMap_eq fun x =>
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).commutes x).symm
  haveI : IsScalarTower (MvPolynomial (Fin r) k) B (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, key]; rfl
  haveI : IsScalarTower (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI h1 : Algebra.IsPushout k B R (R ⊗[k] B) := inferInstance
  haveI h2 : Algebra.IsPushout (MvPolynomial (Fin r) k) B (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin r) k) R (MvPolynomial (Fin r) R)
      (T := B) (T' := R ⊗[k] B)).1 h1
  haveI : Algebra.IsPushout (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B) :=
    h2.symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    Algebra.FormallyEtale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B))
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfPrincipalMaximalIdealOfKerSmulLe
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem free_of_principal_maximalIdeal_of_ker_smul_le :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      IsLocalRing.maximalIdeal R = Ideal.span {x} →
      ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N →
        (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) →
        Module.Free R N := by
  intro R _ _ _ x hx N _ _ hfin hann
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hx ▸ Ideal.subset_span rfl
  let X : IsLocalRing.maximalIdeal R := ⟨x, hxm⟩
  have hrep : ∀ t : (IsLocalRing.maximalIdeal R) ⊗[R] N, ∃ n : N, t = X ⊗ₜ n := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m n =>
      obtain ⟨r, hr⟩ : ∃ r, r * x = (m : R) := by
        have hm : (m : R) ∈ Ideal.span {x} := hx ▸ m.2
        rwa [Ideal.mem_span_singleton'] at hm
      refine ⟨r • n, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1; ext; simp [X, hr]
    | add a b ha hb =>
      obtain ⟨n1, rfl⟩ := ha; obtain ⟨n2, rfl⟩ := hb
      exact ⟨n1 + n2, by rw [TensorProduct.tmul_add]⟩
  have hspan : ∀ a ∈ Ideal.span {a : R | x * a = 0}, x * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_eq_mul, mul_left_comm, hy, mul_zero]
  have hzero : ∀ n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N),
      (X ⊗ₜ[R] n : (IsLocalRing.maximalIdeal R) ⊗[R] N) = 0 := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro a ha m _
      rw [← TensorProduct.smul_tmul]
      have : a • X = 0 := by ext; simp [X, mul_comm a x, hspan a ha]
      rw [this, TensorProduct.zero_tmul]
    · intro m1 m2 h1 h2
      rw [TensorProduct.tmul_add, h1, h2, add_zero]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, rfl⟩ := hrep t
  have hxn : x • n = 0 := by
    have h2 := congrArg (TensorProduct.lid R N) ht
    simpa [X] using h2
  exact hzero n (hann n hxn)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten
section
namespace GlobalTheory

open Matrix

theorem frobSemilinear_iterate_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  intro p _ S _ _ ι _ _ Q N hN
  set L : (ι → S) → (ι → S) := fun w => Q.mulVec fun k => frobenius S p (w k) with hL
  let F : AddMonoid.End (ι → S) :=
    { toFun := L
      map_zero' := by
        simp only [L, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero Q
      map_add' := by
        intro x y
        simp only [L, Pi.add_apply, map_add (f := _)]
        exact Matrix.mulVec_add Q _ _ }
  have hF : ∀ n, ⇑(F ^ n) = L^[n] := fun n => AddMonoid.End.coe_pow (M := ι → S) F n
  have hsmul : ∀ (a : S) (w : ι → S), L (a • w) = a ^ p • L w := by
    intro a w
    simp only [L]
    rw [← Matrix.mulVec_smul]
    congr 1
    ext k
    simp [frobenius_def, mul_pow]
  have hsmulN : ∀ n (a : S) (w : ι → S), L^[n] (a • w) = a ^ (p ^ n) • L^[n] w := by
    intro n
    induction n with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply, hsmul, ih, ← pow_mul, ← pow_succ', Function.iterate_succ_apply]
  have hdecomp : ∀ w : ι → S, L^[N] w = ∑ j, (w j) ^ (p ^ N) • L^[N] (Pi.single j 1) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, ← hsmulN]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  let J : Ideal S := Ideal.span (Set.range fun ji : ι × ι => L^[N] (Pi.single ji.1 1) ji.2)
  have hJnil : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact (mem_nilradical).2 (hN j i)
  have hstep : ∀ k (w : ι → S), (∀ i, w i ∈ J ^ k) → ∀ i, L^[N] w i ∈ J ^ (k + 1) := by
    intro k w hw i
    rw [hdecomp w, Finset.sum_apply]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, pow_succ]
    exact Ideal.mul_mem_mul
      (Ideal.pow_mem_of_mem _ (hw j) _ (pow_pos (Fact.out : p.Prime).pos _))
      (Ideal.subset_span ⟨(j, i), rfl⟩)
  have hall : ∀ k (z : ι → S), ∀ i, L^[N * k] z i ∈ J ^ k := by
    intro k
    induction k with
    | zero => intro z i; simp
    | succ k ih =>
      intro z i
      rw [show N * (k + 1) = N + N * k by ring, Function.iterate_add_apply]
      exact hstep k _ (ih z) i
  obtain ⟨m, hm⟩ := hJnil
  refine ⟨N * m, fun z => ?_⟩
  funext i
  have h := hall m z i
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
end

