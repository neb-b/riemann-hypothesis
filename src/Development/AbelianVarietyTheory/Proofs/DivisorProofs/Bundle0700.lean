module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W),
      ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    have hMove : ∃ φ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x,
        φ' x = φ x + ∑ a, φ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a :=
      GlobalTheory.SqZeroMove.gen_hom φ
        (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
        (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
        (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn2
    obtain ⟨φ', hφ'⟩ := hMove
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor :
    ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
      {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
      (ρ : Hol W →+* R ⊗[ℂ] Hol W₀),
      (∀ (a : Fin g) (h : Hol W),
        ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h)) →
      ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C,
        (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) →
        Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)
          (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) →
        Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeQcqs
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem contCone_bc_of_compact_separated (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F)
    (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G)
    (hc : IsLimit c) (hG : ∀ i, IsAffineHom (G.obj i).hom) (W : Scheme.{0}) (r : W ⟶ S)
    [CompactSpace W] [W.IsSeparated] : ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hfa : IsAffineHom f := by
    have : IsAffineHom (f ≫ terminal.from W) := isAffineHom_of_isAffine _
    exact IsAffineHom.of_comp f (terminal.from W)
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs @IsAffineHom hfa ?_
  intro Z π hπ
  have : IsAffine Z := isAffine_of_isAffineHom π
  exact GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit R F hF S I G c hc hG Z (π ≫ f ≫ r) inferInstance

theorem contCone_bc_of_qcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S) [CompactSpace W] [QuasiSeparatedSpace W], ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r _ _
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated f := by
    have : IsSeparated (f ≫ terminal.from W) := by
      rw [Subsingleton.elim (f ≫ terminal.from W) (terminal.from V)]; infer_instance
    exact IsSeparated.of_comp f (terminal.from W)
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsMultiplicative :=
    { id_mem := fun X => ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg => by
        obtain ⟨hf1, hf2⟩ := hf
        obtain ⟨hg1, hg2⟩ := hg
        exact ⟨inferInstance, inferInstance⟩ }
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs (@QuasiCompact ⊓ @IsSeparated) ⟨hqc, hsep⟩ ?_
  intro Z π hπ
  obtain ⟨h1, h2⟩ := hπ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace π
  have : Z.IsSeparated := by
    constructor
    rw [Subsingleton.elim (terminal.from Z) (π ≫ terminal.from V)]; infer_instance
  exact contCone_bc_of_compact_separated R F hF S I G c hc hG Z (π ≫ f ≫ r)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLeviDatumPermBlocksMatch
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.BlockMatch

variable {F : Type} [Field F] {r : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eq_zero_of_invariant [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    (hσ : IsCuspDatum b σ) (S : Finset (Fin r)) (hS : ∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) (T : V →ₗ[ℂ] W)
    (hT : ∀ u : blockTri (κ := F) b, (∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → T ∘ₗ σ u = T) : T = 0 := by
  classical
  let c : Fin r → ℕ := fun k => if k ∈ S then 0 else 1
  let U : Subgroup (blockTri (κ := F) b) :=
    (levi F b ⊓ GlobalTheory.FiniteGL.unipRadical F c).subgroupOf (blockTri b)
  have hU : ∀ u : blockTri (κ := F) b, u ∈ U ↔ ∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S := by
    intro u
    simp only [U, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_levi, GlobalTheory.FiniteGL.mem_unipRadical,
      Matrix.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ i j hne
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hne (by rw [h1 i j h, Matrix.one_apply_ne (fun e => h (congrArg b e))])
      · by_contra h
        refine hne (h2 i j ?_)
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [c]
    · intro h
      refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · by_contra h0
        exact hij (h i j (by rwa [Matrix.one_apply_ne (fun e => hij (congrArg b e))])).1
      · by_contra h0
        obtain ⟨-, hi, hj⟩ := h i j h0
        simp [c, hi, hj] at hij
  letI := Fintype.ofFinite U
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  ext v
  have h0 : ∑ u : U, σ u v = 0 := by
    refine hσ.cusp S hS _ fun n hn => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨n, (hU n).2 hn⟩ : U)) _ _ fun u => by simp
  have h1 := congrArg T h0
  have h2 : ∀ u : U, T (σ u v) = T v := fun u => LinearMap.congr_fun (hT u ((hU u).1 u.2)) v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

theorem mem_blockTri_of_ne {b : Fin r → ℕ} {g : GL (Fin r) F}
    (h : ∀ i j, (g : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → b i < b j) :
    g ∈ blockTri (κ := F) b := by
  refine mem_blockTri.2 fun i j hij => ?_
  by_contra h0
  have := h i j (by rwa [Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)])
  omega

theorem blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  intro F _ _ r b b' V V' _ _ _ _ σ σ' hσ hσ' w T hT hint
  have hone : ∀ k l : Fin r, (1 : Matrix (Fin r) (Fin r) F) (w k) (w l) = (1 : Matrix (Fin r) (Fin r) F) k l := by
    intro k l
    simp [Matrix.one_apply]
  have A : ∀ i j, b i = b j → ¬ b' (w i) < b' (w j) := by
    intro i j hij hlt
    refine hT (eq_zero_of_invariant hσ (Finset.univ.filter fun k => b' (w k) ≤ b' (w i))
      ⟨i, j, hij, by simp, by simpa using hlt⟩ T fun u hu => ?_)
    have key : ∀ k l, ((permGL F w * u * (permGL F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b' k < b' l := by
      intro k l
      obtain ⟨k, rfl⟩ := w.surjective k
      obtain ⟨l, rfl⟩ := w.surjective l
      rw [conj_permGL_apply, hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu k l h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have h1 := hint u ⟨_, mem_blockTri_of_ne key⟩ (by simp)
    rw [hσ'.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact h1.symm
  have B : ∀ i j, b' (w i) = b' (w j) → ¬ b i < b j := by
    intro i j hij hlt
    apply hT
    ext v
    refine hσ'.cusp (Finset.univ.filter fun k => b (w.symm k) ≤ b i)
      ⟨w i, w j, hij, by simp, by simpa using hlt⟩ (T v) fun u hu => ?_
    have key : ∀ k l, (((permGL F w)⁻¹ * u * permGL F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b k < b l := by
      intro k l
      rw [← conj_permGL_apply w, ← hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu (w k) (w l) (by simpa [mul_assoc] using h)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at h1 h2
      omega
    have h1 := hint ⟨_, mem_blockTri_of_ne key⟩ u (by simp [mul_assoc])
    rw [hσ.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact LinearMap.congr_fun h1 v
  intro i j
  constructor
  · intro h
    have := A i j h
    have := A j i h.symm
    omega
  · intro h
    have := B i j h
    have := B j i h.symm
    omega

end GlobalTheory.FinGL.BlockMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DcOpCommOfCommute
section
noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.Col

namespace GlobalTheory.HeckeParts

section Grp

variable {G : Type} [Group G] {J Q L : Subgroup G}

def Splits (Q J L : Subgroup G) : Prop :=
  ∀ κ ∈ Q, ∃ k₁ ∈ J, ∃ k₂, k₁ ∈ L ∧ κ = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

def RInv (J : Subgroup G) (F : G → ℂ) : Prop := ∀ k ∈ J, ∀ h, F (h * k) = F h

theorem Splits.self (h : Splits Q J L) (hJ : J ≤ Q) :
    ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l := by
  intro k hk
  obtain ⟨k₁, h₁, k₂, hL, e, hc⟩ := h k (hJ hk)
  refine ⟨k₁, h₁, k₂, ?_, hL, e, hc⟩
  have : k₂ = k₁⁻¹ * k := by rw [e]; group
  rw [this]
  exact J.mul_mem (J.inv_mem h₁) hk

theorem RInv.one {F : G → ℂ} (h : RInv J F) (k : J) (g : G) : F (g * k) = (((1 : J →* ℂˣ) k : ℂˣ) : ℂ) • F g := by
  simp [h k k.2 g]

theorem isDC_of_splits (hs : Splits Q J L) (hJ : J ≤ Q) {x : G} (hx : x ∈ L) {A : Finset G} (hA : ∀ a ∈ A, a ∈ L)
    {K : Set G} (hK : ∀ g, g ∈ K ↔ g ∈ J ∧ g ∈ L) (h1 : ∀ γ ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * x * k₂)
    (h2 : ∀ y, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * y ∈ K) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h1 a ha
    exact ⟨⟨k₁, ((hK _).1 h₁).1⟩, ⟨k₂, ((hK _).1 h₂).1⟩, e⟩
  · rintro g ⟨k, k', rfl⟩
    obtain ⟨k₁, h₁, k₂, h₂, hL, e, hc⟩ := hs.self hJ k k.2
    have key : ∀ a : G, a⁻¹ * ((k : G) * x * k') = a⁻¹ * (k₁ * x * 1) * (k₂ * k') := by
      intro a
      rw [e, mul_assoc k₁ k₂ x, (hc x hx).eq]; group
    have hm : k₂ * (k' : G) ∈ J := J.mul_mem h₂ k'.2
    refine (existsUnique_congr fun a => and_congr_right fun ha => ?_).1
      (h2 _ ⟨k₁, (hK _).2 ⟨h₁, hL⟩, 1, (hK _).2 ⟨J.one_mem, L.one_mem⟩, rfl⟩)
    rw [key, J.mul_mem_cancel_right hm, hK]
    exact and_iff_left (L.mul_mem (L.inv_mem (hA a ha)) (L.mul_mem (L.mul_mem hL hx) L.one_mem))

theorem dcOp_eq_rInv {x x' : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) {F : G → ℂ} (hF : RInv J F) :
    dcOp A F = dcOp A' F ∧ RInv J (dcOp A F) := by
  have := GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx hF.one
  exact ⟨this.1, fun k hk h => by simpa using this.2 ⟨k, hk⟩ h⟩

theorem dcOp_rInv {x : G} {A : Finset G} (hA : IsDC J x A) {F : G → ℂ} (hF : RInv J F) : RInv J (dcOp A F) :=
  (dcOp_eq_rInv hA hA ⟨1, 1, by simp⟩ hF).2

theorem dcOp_translate (hs : Splits Q J L) {x : G} {A : Finset G} (hA : IsDC J x A) (hL : ∀ a ∈ A, a ∈ L)
    {F : G → ℂ} (hF : RInv J F) {κ : G} (hκ : κ ∈ Q) (h : G) :
    dcOp A F (h * κ) = dcOp A (fun g => F (g * κ)) h := by
  obtain ⟨k₁, h₁, k₂, hl, rfl, hc⟩ := hs κ hκ
  rw [← (hc k₁ hl).eq, ← mul_assoc, dcOp_rInv hA hF k₁ h₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  show F (h * k₂ * a) = F (h * a * (k₂ * k₁))
  rw [← mul_assoc, hF k₁ h₁, mul_assoc, (hc a (hL a ha)).eq, mul_assoc]

theorem dcOp_comm_of_commute {A B : Finset G} (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (F : G → ℂ) :
    dcOp A (dcOp B F) = dcOp B (dcOp A F) := by
  funext g
  simp only [dcOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  rw [mul_assoc, (h a ha b hb).eq, mul_assoc]

end Grp

section Normal

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end Normal

end GlobalTheory.HeckeParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfShearAutomorphismLiftNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

theorem eq_of_fst_snd_left {C : Type*} [Category C] [Limits.HasPullbacks C] {B : C} {Y : Over B} {T : C}
    {a b : T ⟶ (Y ⊗ Y).left} (h₁ : a ≫ (fst Y Y).left = b ≫ (fst Y Y).left)
    (h₂ : a ≫ (snd Y Y).left = b ≫ (snd Y Y).left) : a = b := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact Limits.pullback.hom_ext h₁ h₂

theorem eq_of_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i → IsIso (lift (fst X X) m) →
    ∀ (P : Over (Sp R)) (P₀ : Over (Sp R₀)) (k : P₀.left ⟶ P.left), IsPullback k P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f f' : P ⟶ X), k ≫ f.left = k ≫ f'.left → ε ≫ f.left = ε ≫ f'.left → f = f' := by
  intro R R₀ _ _ π hπ hnil A₀ _ X i hi l hl1 hl2 m hm hσ P P₀ k hk hsm hpr hgc ε hε f f' hk' hε'
  have hσl : IsIso (lift (fst X X) m).left := Functor.map_isIso (Over.forget (Sp R)) (lift (fst X X) m)

  have hsq : (k ≫ f.left) ≫ X.hom = P₀.hom ≫ spMap π := by
    rw [Category.assoc, Over.w f]; exact hk.w
  let f₀ : P₀ ⟶ A₀ := Over.homMk (hi.lift (k ≫ f.left) P₀.hom hsq) (hi.lift_snd _ _ _)
  have hf₀i : f₀.left ≫ i = k ≫ f.left := hi.lift_fst _ _ _

  have hlσ : l ≫ (lift (fst X X) m).left = (lift (fst A₀ A₀) μ).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hm, hl2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have hred : k ≫ (lift f f).left = (lift f₀ f₀).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst, hf₀i]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hl2, ← Category.assoc, ← Over.comp_left, lift_snd, hf₀i]
  let h₀ : P₀ ⟶ A₀ ⊗ A₀ := lift f₀ (toUnit P₀ ≫ η)
  have hh₀ : h₀ ≫ lift (fst A₀ A₀) μ = lift f₀ f₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [h₀]
    · simp only [h₀, Category.assoc, lift_snd]
      exact lift_comp_one_right _ _
  obtain ⟨gu, hgu_def⟩ : ∃ g, g = lift f f' ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  obtain ⟨gv, hgv_def⟩ : ∃ g, g = lift f f ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  have eu : gu.left ≫ (lift (fst X X) m).left = (lift f f').left := by
    rw [← Over.comp_left, hgu_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ev : gv.left ≫ (lift (fst X X) m).left = (lift f f).left := by
    rw [← Over.comp_left, hgv_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hgv : k ≫ gv.left = h₀.left ≫ l := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, ev, hred, Category.assoc, hlσ,
      ← Category.assoc, ← Over.comp_left, hh₀]
  have hpair_k : k ≫ (lift f f').left = k ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hk'.symm
  have hpair_ε : ε ≫ (lift f f').left = ε ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hε'.symm
  have hgu_k : k ≫ gu.left = k ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_k]
  have hgu_ε : ε ≫ gu.left = ε ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_ε]

  have e2 : (h₀ ≫ snd A₀ A₀).left = P₀.hom ≫ (η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left := by
    simp only [h₀, lift_snd, Over.comp_left, Over.toUnit_left]
  have hv₀ : k ≫ (gv ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    calc k ≫ (gv ≫ snd X X).left = (k ≫ gv.left) ≫ (snd X X).left := by
          rw [Over.comp_left, Category.assoc]
      _ = h₀.left ≫ (l ≫ (snd X X).left) := by rw [hgv, Category.assoc]
      _ = (h₀ ≫ snd A₀ A₀).left ≫ i := by rw [hl2, Over.comp_left, Category.assoc]
      _ = _ := by rw [e2, Category.assoc]
  have hu₀ : k ≫ (gu ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    rw [Over.comp_left, ← Category.assoc, hgu_k, Category.assoc, ← Over.comp_left]; exact hv₀
  have cu := _root_.GlobalTheory.Rigidity.eq_comp_section R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hu₀
  have cv := _root_.GlobalTheory.Rigidity.eq_comp_section R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hv₀
  have huv : gu ≫ snd X X = gv ≫ snd X X := by
    apply Over.OverMorphism.ext
    rw [cu, cv, Over.comp_left, Over.comp_left, ← Category.assoc ε gu.left, hgu_ε, Category.assoc]
  have hinvfst : inv (lift (fst X X) m) ≫ fst X X = fst X X := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hg : gu = gv := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hgu_def, hgv_def, Category.assoc, Category.assoc, hinvfst, lift_fst, lift_fst]
    · exact huv
  rw [hgu_def, hgv_def] at hg
  have hff : lift f f' = lift f f := (cancel_mono (inv (lift (fst X X) m))).1 hg
  have := congrArg (· ≫ snd X X) hff
  simp only [lift_snd] at this
  exact this.symm

end GlobalTheory.ShearLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem IsCuspDatum.exists_blockDiag_act_eq (F : Type) [Field F] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ)
    (p : blockTri (κ := F) b) :
    ∃ m : blockTri (κ := F) b, σ m = σ p ∧ ∀ i k : Fin r, ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := by
  refine ⟨Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p), ?_,
    fun i k => GlobalTheory.Parabolic.leviProj_apply b p i k⟩
  set m := Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p) with hm
  have h1 : GlobalTheory.Parabolic.leviProj b (m⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hm, GlobalTheory.Parabolic.leviProj_inclusion, inv_mul_cancel]
  have h2 : σ (m⁻¹ * p) = 1 := by
    refine hσ.infl _ fun i j hij => ?_
    have e := GlobalTheory.Parabolic.leviProj_apply b (m⁻¹ * p) i j
    rw [h1, if_pos hij] at e
    rw [← e]
    simp
  calc σ m = σ m * σ (m⁻¹ * p) := by rw [h2, mul_one]
    _ = σ p := by rw [← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinGL
end

