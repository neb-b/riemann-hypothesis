module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.CovolTransport

section General

theorem isometry_iff {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (J g : Matrix (Fin M) (Fin M) A) :
    (∀ u w : Fin M → A, ∑ a, ∑ b, (g *ᵥ u) a * J b a * s ((g *ᵥ w) b) = ∑ a, ∑ b, u a * J b a * s (w b)) ↔
      Formalism.UG.cT s g * J * g = J := by
  have h1 : ∀ (K : Matrix (Fin M) (Fin M) A) (u w : Fin M → A),
      ∑ a, ∑ b, u a * K b a * s (w b) = (s ∘ w) ⬝ᵥ (K *ᵥ u) := by
    intro K u w
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∀ u w : Fin M → A, (s ∘ (g *ᵥ w)) ⬝ᵥ (J *ᵥ (g *ᵥ u)) =
      (s ∘ w) ⬝ᵥ ((Formalism.UG.cT s g * J * g) *ᵥ u) := by
    intro u w
    have e : s ∘ (g *ᵥ w) = g.map s *ᵥ (s ∘ w) := by
      funext a; exact RingHom.map_mulVec s g w a
    rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    rfl
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single b 1) (Pi.single a 1)
    have e : s ∘ (Pi.single a 1 : Fin M → A) = Pi.single a 1 := by
      funext k
      by_cases hk : k = a <;> simp [Pi.single_apply, hk]
    rw [e] at this
    simpa using this
  · intro h u w
    rw [h]

variable {S : Type} [CommRing S] {I : Type} {M : ℕ} {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) :
    (Formalism.UG.cT s X).map t = Formalism.UG.cT (starRingEnd ℂ) (X.map t) := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (H : Subgroup (I → GL (Fin M) ℂ))
    (hH : ∀ g, g ∈ H ↔ ∀ i, g i ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map (θ i))) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* H, ∀ h i, (((f h : I → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
      ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  let fw : Formalism.UG.UJ s J → H := fun h => ⟨fun i => Formalism.UG.bc (θ i) h.1, (hH _).2 fun i => by
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    exact h2⟩
  have hfw : ∀ h i, ((fw h).1 i).1 = h.1.1.map (θ i) := fun _ _ => rfl
  let L : H → Matrix (Fin M) (Fin M) S :=
    fun g => Matrix.of fun a b => e.symm fun i => (g.1 i).1 a b
  have hL : ∀ g i, (L g).map (θ i) = (g.1 i).1 := fun g i => by
    ext a b
    simp [L, ← he]
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL]
    rfl
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, hone]
    rfl
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact (hH _).1 g.2 i
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : H => (g.1 i).1 :=
      Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact this.matrix_elem a b
  let bw : H → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => rfl⟩
  · exact Subtype.ext (Units.ext (ext_map he fun i => hL (fw h) i))
  · exact Subtype.ext (funext fun i => Units.ext (hL g i))
  · exact Subtype.ext (funext fun i => map_mul (Formalism.UG.bc (θ i)) h.1 h'.1)
  · refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (hθ i)
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (hθ i)
  · exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _

end General

theorem isCMFam_val {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    IsCMFam (fun τ : Ψ => τ.1) := by
  constructor
  · intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ j.2) ((hΨ _).1 i.2)
  · intro w
    by_cases h : w.embedding ∈ Ψ
    · exact ⟨⟨_, h⟩, w.mk_embedding⟩
    · have h' : ComplexEmbedding.conjugate w.embedding ∈ Ψ := by
        by_contra hn
        exact h ((hΨ _).2 hn)
      exact ⟨⟨_, h'⟩, (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩

theorem finite_covolume_real_points : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  intro hyp F E _ _ _ _ _ σ hcm M J hJ L hL hsp ν hν
  haveI := hcm.1
  haveI := hcm.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [ReciprocityTheory.ChartRestriction.G.FD.emb_cc, hcm.2.2.2]
    rfl
  obtain ⟨Ψ, hΨ, hcov⟩ := hyp E M Jᵀ L (fun a b => by rw [hcc]; exact hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) hL hsp
  choose θ hθ using fun τ : Ψ => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hcm τ.1).exists
  obtain ⟨e, he, hc, hc', hs⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ Ψ _ θ hcm (isCMFam_val Ψ hΨ) hθ
  have hincl : ∀ (X : Matrix (Fin M) (Fin M) E) (τ : Ψ),
      (X.map (inclR (F := F) (Ainf F))).map (θ τ) = X.map τ.1 := fun X τ => by
    ext a b
    exact (hθ τ).1 (X a b)
  let H : Subgroup (Ψ → GL (Fin M) ℂ) :=
    Subgroup.pi Set.univ fun τ => Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1)
  obtain ⟨f, hf⟩ : ∃ f : HA (Ainf F) σ J ≃ₜ* H, ∀ h i,
      (((f h : Ψ → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
        (HA.mat (Ainf F) σ J h : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) :=
    exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs]) (JR (Ainf F) J) H
      fun g => by
        simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const, JR, hincl]
  borelize ↥H
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Ainf F) σ J) :=
    f.toHomeomorph.isInducing.topologicalGroup f
  haveI : (ν.map f).IsHaarMeasure := f.isHaarMeasure_map ν
  obtain ⟨Ω, hΩm, hΩf, hΩ⟩ := hcov H (fun g => by
    simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const]
    exact forall_congr' fun τ => (isometry_iff (starRingEnd ℂ) (J.map τ.1) (g τ).1).symm) (ν.map f)
  have hfm : Measurable f := f.continuous.measurable
  refine ⟨f ⁻¹' Ω, hfm hΩm, by rwa [Measure.map_apply hfm hΩm] at hΩf, fun g => ?_⟩
  obtain ⟨γ, hγ, w, hw, hgw⟩ := hΩ (f g)
  refine ⟨γ, (isometry_iff (σ : E →+* E) J γ.1).1 fun u v => ?_, hγ.2, f.symm w, by simpa using hw, ?_⟩
  · have := hγ.1 u v
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, hcc, Matrix.transpose_apply] at this
    exact this
  · refine Units.ext (ext_map he fun τ => ?_)
    rw [Units.val_mul, Matrix.map_mul, ← hf, ← hf, f.apply_symm_apply, hgw, ← hincl]
    rfl

end GlobalTheory.Mem.CovolTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdealMapEqTransfer
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published
open scoped Pointwise

namespace GlobalTheory.FrobTransfer

theorem pow_smul_sub_mem {G S : Type} [Group G] [CommRing S] [MulSemiringAction G S] {P : Ideal S} {σ : G} {q : ℕ}
    (h : ∀ x, σ • x - x ^ q ∈ P) (n : ℕ) (x : S) : σ ^ n • x - x ^ q ^ n ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h (σ ^ n • x)
    rw [← Ideal.Quotient.eq] at h1 ih ⊢
    rw [pow_succ', mul_smul, h1, map_pow, ih, ← map_pow, ← pow_mul, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem orderOf_eq_inertiaDeg {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)} [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L} (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    orderOf σ = P.inertiaDeg (𝓞 K) := by
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : P.IsMaximal := hP.isMaximal hne
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (𝓞 L ⧸ P)
  have hc : Fintype.card (𝓞 L ⧸ P) = Ideal.absNorm 𝔭.asIdeal ^ P.inertiaDeg (𝓞 K) := by
    rw [Ideal.absNorm_pow_inertiaDeg, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hq : 1 < Ideal.absNorm 𝔭.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hf := Ideal.inertiaDeg_pos P (𝓞 K)
  apply le_antisymm
  · refine orderOf_le_of_pow_eq_one hf (hu _ ⟨P, hP, hPo, fun x => ?_⟩)
    have h1 := pow_smul_sub_mem h (P.inertiaDeg (𝓞 K)) x
    rw [← Ideal.Quotient.eq] at h1 ⊢
    rw [h1, map_pow, ← hc, FiniteField.pow_card]
  · have ho : 0 < orderOf σ := orderOf_pos σ
    have hlt : 1 < Ideal.absNorm 𝔭.asIdeal ^ orderOf σ := Nat.one_lt_pow ho.ne' hq
    have h2 := (FiniteField.forall_pow_eq_one_iff (𝓞 L ⧸ P) (Ideal.absNorm 𝔭.asIdeal ^ orderOf σ - 1)).1 fun u => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ P)
      have h1 := pow_smul_sub_mem h (orderOf σ) x
      rw [pow_orderOf_eq_one, one_smul, ← Ideal.Quotient.eq, map_pow, hx] at h1
      have h3 : u ^ Ideal.absNorm 𝔭.asIdeal ^ orderOf σ = u := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h1])
      rw [pow_sub u hlt.le, h3, pow_one, mul_inv_cancel]
    have h4 := Nat.le_of_dvd (by omega) h2
    rw [hc] at h4
    exact (Nat.pow_le_pow_iff_right hq).1 (by omega)


omit [NumberField K] [NumberField L] in
theorem card_inertia {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] : Nat.card (P.inertia (L ≃ₐ[K] L)) = 1 := by
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu τ ⟨P, hP, hPo, hτ⟩
  rw [h1, Subgroup.card_bot]

theorem stabilizer_eq [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)}
    [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) P := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have hF : IsArithFrobAt (𝓞 K) σ P := by
    unfold IsArithFrobAt AlgHom.IsArithFrobAt
    rw [← hPo.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hF.mem_stabilizer) ?_
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, one_mul,
    Nat.card_zpowers, orderOf_eq_inertiaDeg hu h]

theorem map_eq_prod [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) :
    𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) = ∏ P : 𝔭.asIdeal.primesOver (𝓞 L), P.1 := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow 𝔭.ne_bot, ← Finset.prod_set_coe]
  refine Finset.prod_congr rfl fun ⟨P, hP, hPo⟩ _ => ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, pow_one]

theorem heckeIdeal_prod {ι : Type} (χ : (L ≃ₐ[K] L) →* ℂˣ) (s : Finset ι) (f : ι → Ideal (𝓞 K))
    (hf : ∀ i, f i ≠ 0) : heckeIdeal L χ (∏ i ∈ s, f i) = ∏ i ∈ s, heckeIdeal L χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.NT.Model.heckeIdeal_top L χ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      GlobalTheory.NT.Model.heckeIdeal_mul L χ (hf a) (Finset.prod_ne_zero_iff.2 fun i _ => hf i), ih]

variable {N : Type} [Field N] [NumberField N] [Algebra L N] [Algebra K N] [IsScalarTower K L N]

omit [NumberField K] [NumberField L] [NumberField N] in
theorem algebraMap_restrict_smul [Normal K L] (g : N ≃ₐ[K] N) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 N) (AlgEquiv.restrictNormalHom L g • x) = g • algebraMap (𝓞 L) (𝓞 N) x :=
  RingOfIntegers.ext (g.restrictNormal_commutes L x)

omit [NumberField K] [NumberField L] [NumberField N] in
theorem under_inv_smul [Normal K L] (g : N ≃ₐ[K] N) (Q : Ideal (𝓞 N)) :
    (g⁻¹ • Q).under (𝓞 L) = (AlgEquiv.restrictNormalHom L g)⁻¹ • Q.under (𝓞 L) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_under,
    algebraMap_restrict_smul]


omit [NumberField K] [NumberField L] [NumberField N] in
theorem exists_restrictScalars [Normal K L] (g : N ≃ₐ[K] N) (hg : AlgEquiv.restrictNormalHom L g = 1) :
    ∃ τ : N ≃ₐ[L] N, τ.restrictScalars K = g := by
  refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => ?_, rfl⟩
  have := g.restrictNormal_commutes L x
  rw [show g.restrictNormal L = 1 from hg] at this
  exact this.symm


omit [NumberField K] [NumberField L] [NumberField N] in
theorem unramIn_top {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn N 𝔭) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] : UnramIn N P := by
  rintro τ ⟨Q, hQ, hQo, hτ⟩
  have := hu (τ.restrictScalars K) ⟨Q, hQ, Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal, hτ⟩
  exact AlgEquiv.ext fun x => DFunLike.congr_fun this x


omit [NumberField K] [NumberField L] [NumberField N] in
theorem minimalPeriod_eq [Normal K L] (σ : N ≃ₐ[K] N)
    (c : (N ≃ₐ[K] N) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker) :
    Function.minimalPeriod (σ • ·) c = orderOf (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  refine Nat.dvd_right_iff_eq.1 fun n => ?_
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, orderOf_dvd_iff_pow_eq_one, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, MonoidHom.mem_ker, smul_eq_mul, map_mul, map_inv, map_mul, inv_mul_eq_one, mul_eq_right,
    map_pow]

theorem heckeIdeal_under [IsGalois K L] [IsGalois K N] [IsGalois L N] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn N 𝔭) {Q : Ideal (𝓞 N)} [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : N ≃ₐ[K] N}
    (h : ∀ x : 𝓞 N, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) (χ : (N ≃ₐ[L] N) →* ℂˣ) (t : N ≃ₐ[K] N)
    (τ : N ≃ₐ[L] N) (hτ : τ.restrictScalars K = t⁻¹ * σ ^ (Q.under (𝓞 L)).inertiaDeg (𝓞 K) * t) :
    heckeIdeal N χ ((t⁻¹ • Q).under (𝓞 L)) = (χ τ : ℂˣ) := by
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨(t⁻¹ • Q).under (𝓞 L), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have : P.asIdeal.LiesOver 𝔭.asIdeal := inferInstanceAs (((t⁻¹ • Q).under (𝓞 L)).LiesOver 𝔭.asIdeal)
  have := P.isPrime
  change heckeIdeal N χ P.asIdeal = _
  rw [GlobalTheory.NT.Model.heckeIdeal_prime]
  refine heckeVal_of_unramIn N χ (unramIn_top hu P) ⟨t⁻¹ • Q, inferInstance, ⟨rfl⟩, fun x => ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal,
    ← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal (Q.under (𝓞 L)) (L ≃ₐ[K] L), Ideal.mem_inv_pointwise_smul_iff,
    show τ • x = τ.restrictScalars K • x from rfl, hτ, smul_sub, smul_pow', ← mul_smul, mul_assoc,
    mul_inv_cancel_left, mul_smul]
  exact pow_smul_sub_mem h _ _

theorem heckeIdeal_map_eq_transfer : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N] [IsAbelianGalois L N] (𝔭 : HeightOneSpectrum (𝓞 K)), GlobalTheory.NT.UnramIn N 𝔭 → ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ (χ : (N ≃ₐ[L] N) →* ℂˣ) (φ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker →* ℂˣ), (∀ (τ : N ≃ₐ[L] N) (h : τ.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker), φ ⟨τ.restrictScalars K, h⟩ = χ τ) → GlobalTheory.NT.heckeIdeal N χ (𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) = ((MonoidHom.transfer φ σ : ℂˣ) : ℂ) := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔭 hu σ ⟨Q, hQ, hQo, h⟩ χ φ hφ
  classical
  have huL : UnramIn L 𝔭 := GlobalTheory.RayMaximal.unramIn_of_tower hu
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L
  have hL : ∀ x : 𝓞 L, r σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_under, map_sub, map_pow, algebraMap_restrict_smul]
    exact h _
  have hst := stabilizer_eq huL hL
  have hord := orderOf_eq_inertiaDeg huL hL
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)))
  let e : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)) → 𝔭.asIdeal.primesOver (𝓞 L) :=
    fun q => ⟨(q.out.out⁻¹ • Q).under (𝓞 L), inferInstance, inferInstance⟩
  have key : ∀ s t : N ≃ₐ[K] N, (s⁻¹ • Q).under (𝓞 L) = (t⁻¹ • Q).under (𝓞 L) ↔
      MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker) (s : (N ≃ₐ[K] N) ⧸ r.ker) t := fun s t => by
    rw [under_inv_smul, under_inv_smul, inv_smul_eq_iff, ← mul_smul, eq_comm, ← MulAction.mem_stabilizer_iff, ← hst,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨σ ^ k, k, rfl⟩, ?_⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, hk, inv_mul_cancel_right,
        inv_mul_cancel]
    · rintro ⟨⟨_, k, rfl⟩, hk⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s at hk
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, inv_mul_eq_one] at hk
      exact ⟨k, by rw [← hk, mul_inv_cancel_right]⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      have := (key _ _).1 (congrArg Subtype.val hq)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact Quotient.out_equiv_out.1 this
    · rintro ⟨P, hP, hPo⟩
      obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal (Q.under (𝓞 L)) P (L ≃ₐ[K] L)
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) N γ⁻¹
      refine ⟨Quotient.mk _ (g : (N ≃ₐ[K] N) ⧸ r.ker), Subtype.ext ?_⟩
      refine ((key _ g).2 ?_).trans (by rw [under_inv_smul, hg, inv_inv, hγ])
      rw [QuotientGroup.out_eq']
      exact Quotient.mk_out _
  rw [map_eq_prod huL, heckeIdeal_prod χ _ _ fun P => ?_, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Units.coe_prod]
  · refine (Fintype.prod_bijective e he _ _ fun q => ?_).symm
    obtain ⟨τ, hτ⟩ := exists_restrictScalars (L := L) _ (QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)
    rw [heckeIdeal_under hu h χ q.out.out τ (by rw [hτ, minimalPeriod_eq, hord]),
      ← hφ τ (hτ ▸ QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)]
    exact congrArg (fun x => ((φ x : ℂˣ) : ℂ)) (Subtype.ext hτ.symm)
  · have := P.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _

end GlobalTheory.FrobTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEq
section
noncomputable section

namespace GlobalTheory.GaugeEx.OrbitQuadric

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] (s : A →+* A)
    (G g : Matrix (Fin M) (Fin M) A) (hg : Formalism.UG.cT s g * G * g = G) (x y : Fin M → A) :
    Formalism.UG.hform s G (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s G x y := by
  have hc : Formalism.UG.cT s g = (g.map s)ᵀ := by
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; simp)
  rw [hc] at hg
  have hs : (fun i => s ((g *ᵥ x) i)) = (g.map s) *ᵥ (fun i => s (x i)) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [hform_eq_dot, hform_eq_dot, hs, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose (g.map s) (fun i => s (x i)),
    ← Matrix.dotProduct_mulVec (fun i => s (x i)) (g.map s)ᵀ ((G * g) *ᵥ y),
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : HA.mat R σ J k ∈ HR R σ J := (k : HR R σ J).2
  unfold HR Formalism.UG.UJ at hk
  have hk' : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J := hk
  unfold hR
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (sigR R σ) (JR R J) _ hk' x y

theorem hR_rat (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = (1 : R) ⊗ₜ[F] hE σ J x z := by
  unfold hR hE JR
  rw [hform_eq_dot, hform_eq_dot]
  show _ = inclR R _
  rw [RingHom.map_dotProduct]
  congr 1
  all_goals funext i
  all_goals first
    | exact (RingHom.map_mulVec (inclR R) J z i).symm
    | simp [sigR, inclR]

end Form

theorem qR_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  intro F E _ _ _ _ _ σ hcm R _ _ M J x a hx g
  have hfin : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hact : (g • ratTup (F := F) R x) 0 = (HA.mat R σ J g).1 *ᵥ (fun i => inclR R (x 0 i)) := rfl
  rw [hact]
  unfold qR
  rw [hR_act R σ J g, hR_rat R σ J (x 0) (x 0), hx]
  have h2 : (1 : R) ⊗ₜ[F] algebraMap F E a = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]
    exact (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).commutes a
  rw [h2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasis F E)) (algebraMap F R a),
    Fintype.card_fin, hcm.2.2.1, nsmul_eq_mul, ← mul_assoc]
  have h3 : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [h3, one_mul]

end GlobalTheory.GaugeEx.OrbitQuadric
end
end

