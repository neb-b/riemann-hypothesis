module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicFlagLeviOfKeepsWeights
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut

theorem exists_blockTriangular_of_keeps_weights {A ι : Type} [CommRing A] [Fintype ι] {n r : ℕ}
    {ε : ι → Matrix (Fin n) (Fin n) A} {w : ι → ℤ} (h1 : ∑ a, ε a = 1) {C : Matrix (Fin n) (Fin r) A}
    {L : Matrix (Fin r) (Fin n) A} (hL : L * C = 1) (e : Fin r → ι) (he : ∀ j, ε (e j) = C * single j j (1 : A) * L)
    {d : Fin r → ℕ} (hw : ∀ a j, w a = w (e j) → ∃ i, a = e i) (hd : ∀ i j, d j < d i → w (e i) ≠ w (e j))
    {z : Matrix (Fin n) (Fin n) A} (hz : ∀ a b, w a ≠ w b → ε a * z * ε b = 0) :
    ∃ B : Matrix (Fin r) (Fin r) A, B.BlockTriangular d ∧ z * C = C * B := by
  refine ⟨L * z * C, fun i j hij => ?_, ?_⟩
  · have := hz _ _ (hd i j hij)
    rw [he, he] at this
    exact (sandwich_eq_zero hL z j i).1 this
  · have h2 : (1 - C * L) * C = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 : ∀ j, (1 - C * L) * (z * ε (e j)) = 0 := fun j => by
      rw [← Matrix.one_mul (z * ε (e j)), ← h1, Finset.sum_mul, h1, Finset.mul_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases h : w a = w (e j)
      · obtain ⟨i, rfl⟩ := hw a j h
        rw [← Matrix.mul_assoc, he i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
        simp
      · rw [← Matrix.mul_assoc (ε a), hz _ _ h, Matrix.mul_zero]
    have h4 : ∑ j, ε (e j) = C * L := by
      simp only [he]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    have h5 : (1 - C * L) * (z * (C * L)) = 0 := by
      conv_lhs => rw [← h4, Finset.mul_sum, Finset.mul_sum, h4]
      exact Finset.sum_eq_zero fun j _ => h3 j
    have h6 := congrArg (· * C) h5
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.zero_mul] at h6
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h6
    rw [h6]
    simp only [Matrix.mul_assoc]

theorem mem_leviFlag_of_keeps_weights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ g : GAd σ J, (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g⁻¹).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → g ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y d M hd _ _ xy g hg hg'
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  set φ := inclR (F := F) (E := E) (AF F)
  have m1 : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → L.map φ * C.map φ = 1 :=
    fun h => by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ∑ a, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) a = 1 := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _
  have cs : ∀ j : Fin r, Formalism.UG.cT (σ : E →+* E) (single j j (1 : E)) = single j j (1 : E) := fun j => by
    rw [Formalism.UG.cT, Matrix.map_single, transpose_single, map_one]
  have eY : ∀ j, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) (some (.inr j)) =
      Y.map φ * single j j (1 : AF F ⊗[F] E) * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun j => by
    rw [← idemA_eq]
    change adjA σ J (idemA X _ j) = _
    rw [idemA, idemA, adjA_map, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, cs]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
  have kX : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * X.map φ = X.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 yx) (fun j => some (.inl j))
      (fun j => idemA_eq _ _ j)
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · exact ⟨i, rfl⟩
        · have := hd j; have := hd i; simp [wt] at h; omega)
      (fun i j h => by simp [wt]; omega) hz
  have kY : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * Y.map φ = Y.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 xy) (fun j => some (.inr j)) eY
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · have := hd j; have := hd i; simp [wt] at h; omega
        · exact ⟨i, rfl⟩)
      (fun i j h => by simp [wt]; omega) hz
  exact ⟨⟨kX hg, kX hg'⟩, kY hg, kY hg'⟩

end GlobalTheory.UAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.StairConj

theorem mem_mul_inv_iff {E : Type} [Field E] [NumberField E] (c : E → E) (hc : ∀ x, c (c x) = x)
    (hm : ∀ x y, c (x * y) = c x * c y) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : B ≠ 0) (hB' : B' ≠ 0)
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hBB : ∀ x, x ∈ B' ↔ c x ∈ B) (x : E) :
    x ∈ A' * B'⁻¹ ↔ c x ∈ A * B⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB,
    FractionalIdeal.mem_div_iff_of_ne_zero hB']
  constructor
  · intro h y hy
    have h1 := (hA _).1 (h (c y) ((hBB _).2 (by rwa [hc])))
    rwa [hm, hc] at h1
  · intro h y hy
    rw [hA, hm]
    exact h _ ((hBB _).1 hy)

theorem mem_coe_iff (D : D7) (I : Ideal (𝓞 D.host.E)) (x : D.host.E) :
    x ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔
      D.host.conj x ∈ ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.host.conj • z, Ideal.smul_mem_pointwise_smul _ _ _ hz, rfl⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨D.host.conj⁻¹ • z, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz, ?_⟩
    rw [Formalism.L2.Pj.algebraMap_gal_smul, Formalism.L2.Pj.conj_inv_apply, h, Formalism.L2.Pj.conj_conj]

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero (Formalism.L2.Pj.bB_ne D).1)
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  intro h
  exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)

theorem conj_AA_and_stA : ∀ (D : D7), (D.host.AA ≠ 0 ∧ ∀ x, x ∈ D.host.AAbar ↔ star x ∈ D.host.AA) ∧ ∀ (T : Type) (L : LevCh D T) (P : Places L) (sc : Consts), P.stA sc ≠ 0 ∧ ∀ x, x ∈ P.stAbar sc ↔ star x ∈ P.stA sc := by
  intro D
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hA : ∀ x, x ∈ D.host.AAbar ↔ D.host.conj x ∈ D.host.AA := fun x =>
    ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  refine ⟨⟨AA_ne_zero D, fun x => by rw [hs]; exact hA x⟩, fun T L P sc => ?_⟩
  have h1 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have h2 : ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    apply h1
    rw [FractionalIdeal.eq_zero_iff] at h ⊢
    intro x hx
    have := h _ ((mem_coe_iff D _ x).1 hx)
    exact (map_eq_zero _).1 this
  refine ⟨mul_ne_zero (AA_ne_zero D) (inv_ne_zero h2), fun x => ?_⟩
  rw [hs]
  exact mem_mul_inv_iff D.host.conj (Formalism.L2.Pj.conj_conj D) (map_mul _) h2 h1 hA (mem_coe_iff D _) x

end GlobalTheory.ChiGrid.StairConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntry
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem mem_range_section_of_not_unitAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b z
  obtain ⟨k, _, w, rfl⟩ : ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ W.Z), w (IsLocalRing.closedPoint k) = z :=
    ⟨W.Z.residueField z, inferInstance, W.Z.fromSpecResidueField z, Scheme.fromSpecResidueField_apply _ _⟩
  intro A₁ hA₁ A₂ hA₂ hlow hnu
  have hbase : W.p₁ ≫ f = W.p₂ ≫ f := _root_.GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom F X Y φ f hf.hom W hα
  obtain ⟨ev, hev, hq⟩ := _root_.GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint F Y W.Z k w
  refine W.diag k w ?_
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hff : f (W.p₂ (w (IsLocalRing.closedPoint k))) = f (W.p₁ (w (IsLocalRing.closedPoint k))) := by
    rw [← Scheme.Hom.comp_apply W.p₂ f, ← hbase, Scheme.Hom.comp_apply]
  have hM₁ := hf.sub _ A₁ hA₁ A hA
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun y => A ∈ E.S y) hff).mpr hA)
  let v : W.Z.functionField → k := fun x =>
    if h : x ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range then ev ⟨x, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v x = ev x := fun x => dif_pos x.2
  have hN₁ := hM₁.map W.α₁ fun x hx => (hq W.p₁ x (mem_O_ratOf.1 hx)).1
  have hN₂ := hM₂.map W.α₂ fun x hx => (hq W.p₂ x (mem_O_ratOf.1 hx)).1
  have e₁ : ((A₁ * (A.map φ)⁻¹).map W.α₁).map v = (A₁ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₁)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₁ _ (mem_O_ratOf.1 ((hM₁ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have e₂ : ((A₂ * (A.map φ)⁻¹).map W.α₂).map v = (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₂)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₂ _ (mem_O_ratOf.1 ((hM₂ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have hC : (A.map φ).map W.α₁ = (A.map φ).map W.α₂ := by
    funext σ
    ext i j
    exact hα _
  have hCd : ∀ σ, (((A.map φ).map W.α₂)⁻¹ σ).det ≠ 0 := fun σ => by
    have h := hN₂.det_ne σ
    rw [Mat.map_mul, Mat.map_inv, Pi.mul_apply, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  have hg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      (A₁ * (A.map φ)⁻¹).map W.α₁ * ((A₂ * (A.map φ)⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hC, Mat.mul_inv_rev, mul_assoc, ← mul_assoc _ _ (A₂.map W.α₂)⁻¹,
      Mat.mul_inv hCd, one_mul]
  have hG := hN₁.mul hN₂.inv
  rw [hg] at hlow hnu
  generalize hN1 : (A₁ * (A.map φ)⁻¹).map W.α₁ = N₁ at *
  generalize hN2 : (A₂ * (A.map φ)⁻¹).map W.α₂ = N₂ at *
  have hb₁ := hN₁.map_of v ev hv
  have hb₂ := hN₂.map_of v ev hv
  have hbG := hG.map_of v ev hv
  have hmul : (N₁ * N₂⁻¹).map v * N₂.map v = N₁.map v := by
    rw [← hG.map_mul_of hN₂ v ev hv, mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one]
  have hv0 : v 0 = 0 := (hv 0).trans (map_zero ev)
  have hlowv : Par m ⊤ ((N₁ * N₂⁻¹).map v) := fun σ => by
    refine ⟨(hbG σ).1, (hbG σ).2.1, (hbG σ).2.2.1, fun i j _ hij => ?_⟩
    show v ((N₁ * N₂⁻¹) σ i j) = 0
    by_cases hc : (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩
    · obtain ⟨h1, h2⟩ := hc
      cases h1
      have h3 : j = b := eq_of_heq (Sigma.mk.inj h2).2
      subst h3
      by_contra h0
      exact hnu ((hev ⟨_, (hG τ).1 a j⟩).1 fun h => h0 ((hv ⟨_, (hG τ).1 a j⟩).trans h))
    · rw [hlow.2.2 σ i j hij hc, hv0]
  have hA' : A ∈ E.S ((w ≫ W.p₁ ≫ f) (IsLocalRing.closedPoint k)) :=
    (congrArg (fun y => A ∈ E.S y) ((Scheme.Hom.comp_apply w (W.p₁ ≫ f) _).trans
      (Scheme.Hom.comp_apply W.p₁ f _))).mpr hA
  refine (hf.lifts k (w ≫ W.p₁ ≫ f) A hA' (N₁.map v) hb₁).unique ⟨Category.assoc _ _ _, A₁, ?_, ?_⟩
    ⟨(Category.assoc _ _ _).trans (congrArg (w ≫ ·) hbase.symm), A₂, ?_, ?_⟩
  · exact (congrArg (fun y => A₁ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₁ _)).mpr hA₁
  · have : Par m ⊤ (N₁.map v * (N₁.map v)⁻¹) := by rw [Mat.mul_inv hb₁.det_ne]; exact Par.one
    exact e₁ ▸ this
  · exact (congrArg (fun y => A₂ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₂ _)).mpr hA₂
  · have : Par m ⊤ (N₁.map v * (N₂.map v)⁻¹) := by
      rw [← hmul, mul_assoc, Mat.mul_inv hb₂.det_ne, mul_one]; exact hlowv
    exact e₂ ▸ this

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
section
noncomputable section

open MeasureTheory Formalism.UG

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cornerU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : L :=
  ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev

def depthU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : ℕ :=
  (-ordL (cornerU k u)).toNat

def shellU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℤ) : Set (cellU y) :=
  {u | Valued.v (cornerU k (u : GU σ n)) ≤ WithZero.exp j}

theorem mem_shellU_iff_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℕ) (u : cellU y) :
    u ∈ shellU k y j ↔ depthU k (u : GU σ n) ≤ j := by
  unfold shellU depthU
  simp only [Set.mem_setOf_eq]
  by_cases h0 : cornerU k (u : GU σ n) = 0
  · rw [h0]; simp [ordL]
  · rw [GlobalTheory.BorelUMod.v_eq_exp h0, WithZero.exp_le_exp]
    omega

theorem mem_shellU_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (u : cellU y) :
    u ∈ shellU k y (depthU k (u : GU σ n)) :=
  (mem_shellU_iff_depth k y _ u).2 le_rfl

theorem shellU_mono {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) {j j' : ℤ} (h : j ≤ j') :
    shellU k y j ⊆ shellU k y j' :=
  fun _ hu => le_trans hu (WithZero.exp_le_exp.2 h)

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIff
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCellRankOne

variable {L : Type} [Field L] {n : ℕ}

theorem conj_apply {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((y⁻¹ : GL (Fin n) L) * M * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * M (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro h; apply hb; rw [h]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem diag_mul_eq_one {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) *
        (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h := conj_apply hy 1 i i
  rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq,
    Matrix.one_apply_eq, mul_one] at h
  exact h.symm

theorem swap_lt {a b p q : Fin n} (hab : b.val = a.val + 1) (hpq : p < q) (hne : ¬ (p = a ∧ q = b)) :
    Equiv.swap a b p < Equiv.swap a b q := by
  rw [Fin.lt_def] at hpq ⊢
  have ha : ∀ x : Fin n, x = a ↔ x.val = a.val := fun x => Fin.ext_iff
  have hb : ∀ x : Fin n, x = b ↔ x.val = b.val := fun x => Fin.ext_iff
  simp only [Equiv.swap_apply_def]
  rw [ha, hb] at hne
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [ha, hb] at * <;> omega

theorem mem_cell_swap {a b : Fin n} (hab : b.val = a.val + 1) {y : GL (Fin n) L}
    (hy : IsWeylRep (Equiv.swap a b) y) (u : GL (Fin n) L) :
    u ∈ cell y ↔ ∀ i j, ¬ (i = a ∧ j = b) →
      (u : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  set s := Equiv.swap a b with hs
  have hd := diag_mul_eq_one hy
  have hne1 : ∀ i, ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) ≠ 0 :=
    fun i h => by have := hd i; rw [h, zero_mul] at this; exact zero_ne_one this
  have hne2 : ∀ i, (y : Matrix (Fin n) (Fin n) L) (s i) i ≠ 0 :=
    fun i h => by have := hd i; rw [h, mul_zero] at this; exact zero_ne_one this
  have hconj : ∀ i j, ((y⁻¹ * u * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (u : Matrix (Fin n) (Fin n) L) (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
    intro i j; rw [Units.val_mul, Units.val_mul]; exact conj_apply hy _ i j
  have hss : ∀ x, s (s x) = x := fun x => Equiv.swap_apply_self a b x
  have hlt : a < b := by rw [Fin.lt_def]; omega
  rw [mem_cell, mem_unipB, mem_unipBLower]
  constructor
  · rintro ⟨⟨hup, hdiag⟩, hlow, -⟩ i j hij
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.one_apply_ne h.ne]
      have h2 := hlow (s i) (s j) (swap_lt hab h hij)
      rw [hconj] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (hne1 _)
        · rwa [hss, hss] at h4
      · exact absurd h3 (hne2 _)
    · rw [Matrix.one_apply_eq]; exact hdiag i
    · rw [Matrix.one_apply_ne h.ne']; exact hup i j h
  · intro h
    have hdiag : ∀ i, (u : Matrix (Fin n) (Fin n) L) i i = 1 := fun i => by
      rw [h i i (fun hh => by rw [← hh.1, ← hh.2] at hlt; exact lt_irrefl _ hlt), Matrix.one_apply_eq]
    refine ⟨⟨fun i j hji => ?_, hdiag⟩, fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (fun hh => by rw [hh.1, hh.2] at hji; exact lt_asymm hji hlt), Matrix.one_apply_ne hji.ne']
    · rw [hconj, h (s i) (s j), Matrix.one_apply_ne, mul_zero, zero_mul]
      · intro he; exact hij.ne (s.injective he)
      · rintro ⟨h1, h2⟩
        have e1 : i = b := by rw [← hss i, h1]; exact Equiv.swap_apply_left a b
        have e2 : j = a := by rw [← hss j, h2]; exact Equiv.swap_apply_right a b
        rw [e1, e2] at hij; exact lt_asymm hij hlt
    · rw [hconj, hdiag, mul_one]; exact hd i

end WeylCellRankOne

open WeylCellRankOne in
theorem cellU_rankOne_shape : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  intro L _ _ σ n k hk he y hy u
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  rw [hs] at hy
  have hab : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, rfl⟩ := he
    have hk2 := k.isLt
    simp only [Fin.val_rev, lo, Fin.coe_castLE]
    omega
  rw [cellU, Subgroup.mem_subgroupOf]
  exact mem_cell_swap hab hy (u : GL (Fin n) L)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem ord_eq_zero_iff (E : Place c) {f : K} (hf : f ≠ 0) :
    E.ord f = 0 ↔ f ∈ E.ring ∧ f⁻¹ ∈ E.ring := by
  rw [← E.ord_nonneg_iff hf, ← E.ord_nonneg_iff (inv_ne_zero hf), E.ord_inv]
  omega

end GlobalTheory.FieldPair.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArithStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds : ∀ (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ), (∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤ C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1))) → (∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤ C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) → ((d : ℤ) + 1) * b < a → ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  first | exact @GlobalTheory.morse_inequality_arith | exact GlobalTheory.morse_inequality_arith | (intros; apply GlobalTheory.morse_inequality_arith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefNumericsOfRiemannRoch
section
set_option autoImplicit false

namespace GlobalTheory.Published

theorem nefNumerics_of_product_of_riemannRoch
    (h₁ : NefProductNonneg) (h₂ : NefRiemannRoch) : NefNumerics :=
  ⟨h₁, h₂.nefBigIff, h₂⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBoundStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_le_of_weighted_entry_bound : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) → ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_det_le_of_weighted | exact GlobalTheory.GoodTop.norm_det_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_det_le_of_weighted <;> assumption)
end

