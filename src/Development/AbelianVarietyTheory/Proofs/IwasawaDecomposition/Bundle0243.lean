module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphism
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorus
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isOpen_setOf_valuation_lt_of_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans_lt (max_lt hy hx)

theorem isCompact_boundedTorus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  intro k _ _ _ _ m R1 R2
  have hS : IsCompact {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)} := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : (Units.val '' {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)})
        = {y : k | valuation k y ≤ valuation k (R1 : k)} ∩ {y : k | valuation k (R2 : k) ≤ valuation k y} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2, hx.1⟩
      · rintro ⟨h1, h2⟩
        have hy : y ≠ 0 := by
          rintro rfl
          simp at h2
        exact ⟨Units.mk0 y hy, ⟨h2, h1⟩, rfl⟩
    rw [himg]
    refine (IsNonarchimedeanLocalField.isCompact_closedBall k _).inter_right ?_
    have hne : valuation k (R2 : k) ≠ 0 := by simp
    have ho := isOpen_setOf_valuation_lt_of_ne_zero (valuation k (R2 : k)) hne
    have hc : {y : k | valuation k (R2 : k) ≤ valuation k y} = {y : k | valuation k y < valuation k (R2 : k)}ᶜ := by
      ext y; simp
    rw [hc]
    exact ho.isClosed_compl
  have : {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)}
      = Set.pi Set.univ (fun _ => {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}) := by
    ext t; simp
  rw [this]
  exact isCompact_univ_pi fun _ => hS

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ}

theorem mat_chain {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (ψ : K₁ →+* K₂) (ψ' : K₂ →+* K₃)
    (A'' : Mat m K₃) (A' : Mat m K₂) (A : Mat m K₁) (hA' : ∀ τ, (A' τ).det ≠ 0) :
    A'' * (A'.map ψ')⁻¹ * (A' * (A.map ψ)⁻¹).map ψ' = A'' * (A.map (ψ'.comp ψ))⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc (A'.map ψ')⁻¹,
    Mat.inv_mul (fun τ => by rw [Mat.det_map]; exact (map_ne_zero ψ').2 (hA' τ)), one_mul]
  congr 2

def valAt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) : (M.O (q (IsLocalRing.closedPoint K))).toSubring →+* K :=
  RatModel.valHom q _ (RatModel.range_eq_singleton q (IsLocalRing.closedPoint K))

theorem valAt_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) (x : (M.O (q (IsLocalRing.closedPoint K))).toSubring) : M.val q x = valAt M q x := rfl

end GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {Ω Ω' Ω'' : Type} [Field Ω] [Algebra F Ω] [Field Ω']
  [Algebra F Ω'] [Field Ω''] [Algebra F Ω'']

theorem val_chain {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} (hf' : M'.IsHom M'' φ' f') {K : Type} [Field K] (q : Sp K ⟶ M''.Z)
    {k k' : ι → ℕ} {A'' : Mat m Ω''} {A' : Mat m Ω'} {A : Mat m Ω} (hA' : ∀ τ, (A' τ).det ≠ 0)
    (h2 : Par k' (M''.O (q (IsLocalRing.closedPoint K))).toSubring (A'' * (A'.map φ')⁻¹))
    (h1 : Par k (M'.O (f' (q (IsLocalRing.closedPoint K)))).toSubring (A' * (A.map φ)⁻¹)) :
    (A'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
      (A'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val (q ≫ f')) := by
  have h1' : Par k (M''.O (q (IsLocalRing.closedPoint K))).toSubring ((A' * (A.map φ)⁻¹).map φ') :=
    h1.map (φ' : Ω' →+* Ω'') fun x hx => hf'.map_mem_O hx
  have e := mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A hA'
  have e2 : (A'' * (A.map (φ'.comp φ))⁻¹) = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' := e.symm
  rw [e2, Par.map_mul_of h2 h1' (M''.val q) (valAt M'' q) (valAt_apply M'' q)]
  congr 1
  funext τ
  ext i j
  show M''.val q (φ' ((A' * (A.map φ)⁻¹) τ i j)) = M'.val (q ≫ f') ((A' * (A.map φ)⁻¹) τ i j)
  exact (hf'.val_comp q (IsLocalRing.closedPoint K) ((h1 τ).1 i j)).symm

theorem Refines.comp {M : RatModel F Ω} {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} {k k' k'' : ι → ℕ} {S : Fr M m k}
    {S' : Fr M' m k'} {S'' : Fr M'' m k''} (h1 : Refines S S' φ f) (h2 : Refines S' S'' φ' f') :
    Refines S S'' (φ'.comp φ) (f' ≫ f) := {
  le := le_trans h1.le h2.le
  hom := h1.hom.comp h2.hom
  sub z'' A'' hA'' A hA := by
    obtain ⟨A', hA'⟩ := S'.nonempty (f' z'')
    have e : A'' * (A.map (φ'.comp φ))⁻¹ = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' :=
      (mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A (Fr.det_ne hA')).symm
    rw [e]
    exact ((h2.sub z'' A'' hA'' A' hA').mono h1.le le_rfl).mul
      ((h1.sub (f' z'') A' hA' A hA).map (φ' : Ω' →+* Ω'') fun x hx => h2.hom.map_mem_O hx)
  rad z'' g hg := h2.rad z'' (φ g) (h1.rad (f' z'') g hg)
  lifts K _ x A hA h hh := by
    obtain ⟨p', ⟨hp'x, A', hA', hP'⟩, hu1⟩ := h1.lifts K x A hA h hh
    obtain ⟨p'', ⟨hp'', A'', hA'', hP''⟩, hu2⟩ :=
      h2.lifts K p' A' hA' (h * ((A' * (A.map φ)⁻¹).map (M'.val p'))⁻¹) hP'
    have hAx : A ∈ S.S (f (p' (IsLocalRing.closedPoint K))) := by
      have h0 := hA; rw [← hp'x] at h0; exact h0
    have fac : ∀ q : Sp K ⟶ M''.Z, q ≫ f' = p' → ∀ B'' ∈ S''.S (q (IsLocalRing.closedPoint K)),
        (B'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
          (B'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val p') := by
      intro q hq B'' hB''
      have hq' : p' (IsLocalRing.closedPoint K) = f' (q (IsLocalRing.closedPoint K)) := by
        rw [← hq]; rfl
      have hA'q : A' ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := by rw [← hq']; exact hA'
      have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by rw [← hq']; exact hAx
      rw [val_chain h2.hom q (Fr.det_ne hA') (h2.sub _ B'' hB'' A' hA'q) (h1.sub _ A' hA'q A hAq), hq]
    refine ⟨p'', ⟨by rw [← Category.assoc, hp'', hp'x], A'', hA'', ?_⟩, ?_⟩
    · rw [fac p'' hp'' A'' hA'', Mat.mul_inv_rev, ← mul_assoc]
      exact hP''
    · rintro q ⟨hqx, B'', hB'', hPq⟩
      have hq1 : q ≫ f' = p' := by
        refine hu1 (q ≫ f') ⟨by rw [Category.assoc, hqx], ?_⟩
        obtain ⟨A₁, hA₁⟩ := S'.nonempty ((q ≫ f') (IsLocalRing.closedPoint K))
        refine ⟨A₁, hA₁, ?_⟩
        have hA₁' : A₁ ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := hA₁
        have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by
          have h0 := hA; rw [← hqx] at h0; exact h0
        have h2s := h2.sub _ B'' hB'' A₁ hA₁'
        rw [val_chain h2.hom q (Fr.det_ne hA₁') h2s (h1.sub _ A₁ hA₁' A hAq)] at hPq
        have hG : Par k' ⊤ ((B'' * (A₁.map φ')⁻¹).map (M''.val q)) :=
          h2s.map_of _ (valAt M'' q) (valAt_apply M'' q)
        have e : h * ((A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ =
            h * ((B'' * (A₁.map φ')⁻¹).map (M''.val q) * (A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ *
              (B'' * (A₁.map φ')⁻¹).map (M''.val q) := by
          rw [Mat.mul_inv_rev, mul_assoc, mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
        rw [e]
        exact (hPq.mono h2.le le_rfl).mul hG
      refine hu2 q ⟨hq1, B'', hB'', ?_⟩
      rw [fac q hq1 B'' hB'', Mat.mul_inv_rev, ← mul_assoc] at hPq
      exact hPq }

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.refines_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.comp h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermitianJmBracket
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocUniqueOfIsSplitAt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.AU

theorem isLoc_unique_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin n) (w.adicCompletion E))),
    IsSplitAt w → π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ n π w σ σ' hw h h'
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ
  obtain ⟨σ', rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ'
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  have key : ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), U.IsLocComp w τ →
      ∃ f : τ.ρ.IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict U.V hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key σ h
  obtain ⟨f', hf'⟩ := key σ' h'
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact Quotient.sound ((_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ U.rep s σ.ρ σ'.ρ U.isIrreducible_rep σ.irred σ'.irred hcomm f hf).2 f' hf')

end GlobalTheory.DefU.AU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyA
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem algebraMap_mem_span_of_mem_span {K L A M : Type} [Field K] [Field L] [Algebra K L]
    [Field A] [CommRing M] [Algebra L M] [Algebra A M] (g : K →+* A)
    (hg : ∀ c : K, algebraMap A M (g c) = algebraMap L M (algebraMap K L c))
    {ι : Type} (s : ι → L) (x : L) (hx : x ∈ Submodule.span K (Set.range s)) :
    algebraMap L M x ∈ Submodule.span A (Set.range fun i => algebraMap L M (s i)) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Algebra.smul_def, map_mul, ← hg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

theorem linearIndependent_completion_of_irreducible_minpoly :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  intro K L _ _ _ _ _ v v' f hf hirr
  letI := f.toAlgebra
  intro n b
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hcomp : f.comp (algebraMap K (v.adicCompletion K)) =
      (algebraMap L (v'.adicCompletion L)).comp (algebraMap K L) := RingHom.ext hf
  have hroot : Polynomial.aeval (algebraMap L (v'.adicCompletion L) α)
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (f.comp (algebraMap K (v.adicCompletion K))) _ _ = 0
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmin : (minpoly K α).map (algebraMap K (v.adicCompletion K)) =
      minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α) :=
    minpoly.eq_of_irreducible_of_monic (hirr α) hroot ((minpoly.monic hint).map _)
  have hdeg : (minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree
      = n := by
    rw [← hmin, (minpoly.monic hint).natDegree_map, ← IntermediateField.adjoin.finrank hint, hα,
      IntermediateField.finrank_top', Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hpow := linearIndependent_pow (K := v.adicCompletion K)
    (algebraMap L (v'.adicCompletion L) α)
  have hle : Submodule.span (v.adicCompletion K) (Set.range fun i : Fin (minpoly
      (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree =>
        (algebraMap L (v'.adicCompletion L) α) ^ (i : ℕ)) ≤
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := algebraMap_mem_span_of_mem_span (M := v'.adicCompletion L)
      (algebraMap K (v.adicCompletion K)) hf b (α ^ (i : ℕ)) (by rw [b.span_eq]; trivial)
    simpa using this
  have h1 := finrank_span_eq_card hpow
  have h2 := finrank_range_le_card (R := v.adicCompletion K)
    (fun i => algebraMap L (v'.adicCompletion L) (b i))
  haveI : Module.Finite (v.adicCompletion K) (Submodule.span (v.adicCompletion K)
      (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have h3 := Submodule.finrank_mono hle
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin] at h1 h2 ⊢
  rw [Set.finrank] at h2 ⊢
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecomposition
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise

namespace GlobalTheory.LocEmbDec

theorem exists_dec_of_isLocEmb : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  intro K Ω _ _ _ _ _ A v ι ι₂ hι hι₂
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set e : Ω ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι with he
  haveI : Normal K ι.fieldRange := Normal.of_algEquiv e
  have hr : (ι₂.comp e.symm.toAlgHom).fieldRange = ι.fieldRange :=
    AlgHom.fieldRange_of_normal _
  have hmem : ∀ z, ι₂ z ∈ ι.fieldRange := fun z => by
    rw [← hr]; exact ⟨e z, by simp⟩
  let f : Ω →ₐ[K] ι.fieldRange := ι₂.codRestrict ι.fieldRange.toSubalgebra hmem
  let σ0 : Ω →ₐ[K] Ω := e.symm.toAlgHom.comp f
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ0 (Algebra.IsAlgebraic.algHom_bijective σ0)
  have key : ∀ z, ι (σ z) = ι₂ z := fun z => by
    have h1 : ((e (σ z) : ι.fieldRange) : Kbar v) = ι (σ z) := rfl
    rw [← h1]
    change ((e (e.symm (f z)) : ι.fieldRange) : Kbar v) = ι₂ z
    rw [AlgEquiv.apply_symm_apply]; rfl
  refine ⟨σ, ?_, fun z => (key z).symm⟩
  show σ • A = A
  have hA : ∀ x, σ x ∈ A ↔ x ∈ A := fun x => by rw [hι, key, ← hι₂]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hA]
  show σ (σ⁻¹ y) ∈ A ↔ y ∈ A
  rw [← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

end GlobalTheory.LocEmbDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOver
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LyingOver

theorem valuation_pow_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  intro K L Ω _ _ _ _ _ _ _ _ _ A v v' hv hv'
  have hcomap : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hv x, ← hv' (algebraMap (𝓞 K) (𝓞 L) x)]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨hcomap.symm⟩
  refine ⟨v.asIdeal.ramificationIdx' v'.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v'.asIdeal v.ne_bot), ?_⟩
  intro x
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal v'.asIdeal v.ne_bot]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v v' x).symm

end GlobalTheory.LyingOver
end

