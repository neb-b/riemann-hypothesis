module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformRegularityBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

namespace GlobalTheory.TorsionCut

theorem appLE_resG {X X' : Scheme.{0}} (φ : X' ⟶ X) {U V : X.Opens} {U' V' : X'.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (a : U' ≤ φ ⁻¹ᵁ U) (b : V' ≤ φ ⁻¹ᵁ V) (f : Γ(X, U)) :
    (φ.appLE V V' b).hom (resG X h f) = resG X' h' ((φ.appLE U U' a).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_surjective {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] {U : X.Opens} {U' : X'.Opens}
    (h : U' = φ ⁻¹ᵁ U) : Function.Surjective (φ.appLE U U' h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (φ.app U)).2

theorem vamp_pull {K σ : Type} [Field K] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] (p : X ⟶ Sp K) (M : LB X)
    (th : σ → M.Sec) (h : VAmp p M th) : VAmp (φ ≫ p) (M.pull φ) fun i => secPull (th i) φ := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [nonzeroLocus_secPull]
    rw [← Scheme.Hom.preimage_iSup, h.1]; rfl
  · rw [nonzeroLocus_secPull]
    exact (h.2 i).1.preimage φ
  · obtain ⟨r, hr, hs⟩ := (h.2 i).2
    have hD := nonzeroLocus_secPull (th i) φ
    refine ⟨fun j => (φ.appLE _ _ hD.le).hom (r j), fun j k => ?_, fun f => ?_⟩
    · have hk : (M.pull φ).U k ≤ φ ⁻¹ᵁ M.U (k PUnit.unit) := LB.wchart_le M (fun _ : PUnit => φ) k PUnit.unit
      have e := congrArg (φ.appLE (Out.nonzeroLocus (th i) ⊓ M.U (k PUnit.unit))
        (Out.nonzeroLocus (secPull (th i) φ) ⊓ (M.pull φ).U k) (inf_le_inf hD.le hk)).hom (hr j (k PUnit.unit))
      rw [map_mul] at e
      exact (appLE_resG φ _ inf_le_right hk _ _).symm.trans (e.trans (congrArg₂ (· * ·)
        (appLE_resG φ _ inf_le_left hD.le _ _) (appLE_resG φ _ inf_le_right hk _ _)))
    · obtain ⟨f, rfl⟩ := appLE_surjective φ hD f
      obtain ⟨F, rfl⟩ := hs f
      refine ⟨F, ?_⟩
      rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
      rfl

theorem vamp_of_comp {K σ σ₀ : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (M : LB X) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (hr : Function.Surjective r) (h : VAmp p M (th ∘ r)) : VAmp p M th := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  refine ⟨?_, fun i => ?_⟩
  · rw [← h.1]; exact (hr.iSup_comp fun i => Out.nonzeroLocus (th i)).symm
  · obtain ⟨i, rfl⟩ := hr i
    obtain ⟨ha, ρ, h₁, h₂⟩ := h.2 i
    refine ⟨ha, ρ ∘ s, fun j k => ?_, fun f => ?_⟩
    · have := h₁ (s j) k
      simp only [Function.comp_apply, hs j] at this
      exact this
    · obtain ⟨F, rfl⟩ := h₂ f
      refine ⟨MvPolynomial.rename r F, ?_⟩
      rw [MvPolynomial.eval₂_rename]
      congr 1
      funext a
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
      have hy' : y ∈ Out.nonzeroLocus (th (r i)) ⊓ M.U k := ⟨hy, hk⟩
      have e₁ := congrArg (gs (𝟙 X) y _) (h₁ a k)
      have e₂ := congrArg (gs (𝟙 X) y _) (h₁ (s (r a)) k)
      simp only [Function.comp_apply, hs (r a)] at e₁ e₂ ⊢
      rw [gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e₁ e₂
      exact ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel (e₁.symm.trans e₂)

theorem secCoord_comp {σ σ₀ : Type} {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (s : σ₀ → σ) (hs : ∀ a, r (s a) = a) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : σ → R)
    (h : SecCoord M (th ∘ r) x v) : SecCoord M th x (v ∘ s) ∧ v ∘ s ∘ r = v := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨⟨τ, hτ, fun i j hj => ?_⟩, funext fun a => ?_⟩
  · have := h (s i) j hj
    simp only [Function.comp_apply, hs i] at this
    exact this
  · apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
    refine (Sp R).IsSheaf.section_ext fun y _ => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hj := LB.wchart_le M (fun _ : PUnit => x) (fun _ => k) PUnit.unit
    refine ⟨(M.pull x).U fun _ => k, le_top, mem_pull.2 hk, ?_⟩
    have h₁ := h a (fun _ => k) hj
    have h₂ := h (s (r a)) (fun _ => k) hj
    simp only [Function.comp_apply, hs] at h₁ h₂
    exact (Units.mul_left_inj (τ.s fun _ => k)).1 (h₂.symm.trans h₁)

theorem idealOf_comp {K σ σ₀ : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {M : LB X} (hM : M.IsLB)
    (th : σ₀ → M.Sec) (r : σ → σ₀) (hr : Function.Surjective r) :
    idealOf p M (th ∘ r) (𝟙 X) = (idealOf p M th (𝟙 X)).comap (MvPolynomial.rename r) := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  ext F
  simp only [idealOf, Ideal.mem_comap, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_rename]
  refine ⟨fun H R _ β y v hv => H R _ β y _ ⟨hv.1, ?_⟩, fun H R _ β y v hv => ?_⟩
  · obtain ⟨τ, hτ, h⟩ := hv.2
    exact ⟨τ, hτ, fun i => h (r i)⟩
  · obtain ⟨h₁, h₂⟩ := secCoord_comp hM th r s hs _ v hv.2
    have := H R _ β y _ ⟨hv.1, h₁⟩
    rwa [Function.comp_assoc, h₂] at this

theorem isDominant_one {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0) :
    IsDominant (1 : Out.baseOver (Sp K) ⟶ P.A).left := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  exact ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩

theorem sec_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {Y : Scheme.{0}} (e : Y ≅ P.A.left) (M : LB Y) {σ : Type} [Finite σ] (th : σ → M.Sec) {C d k δ : ℕ}
    (hM : M.IsLB) (hs : SymB (A := P.A) (M.pull e.inv)) (hv : VAmp (e.hom ≫ P.A.hom) M th) (hδ : δ ≤ C ^ P.g)
    (h0 : ∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ P.g)) (hk : C ^ P.g * P.g.factorial * d < k)
    (hK : (k : K) ≠ 0) (τ : (lbPow M d).Sec)
    (hτ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ (x.left ≫ e.inv) ⁻¹ᵁ Out.nonzeroLocus τ) (j) :
    τ.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsReduced Y := isReduced_of_isOpenImmersion e.hom
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z : P.A.left, z ∈ e.inv ⁻¹ᵁ Out.nonzeroLocus τ := by
    have hb : (Y.basicOpen (τ.f j) : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
    obtain ⟨y, hy⟩ := hb
    obtain ⟨z, rfl⟩ := e.inv.homeomorph.surjective y
    exact ⟨z, basicOpen_le_nonzeroLocus τ j hy⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨y, hy⟩ := (isDominant_one P hg).denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) ⟨z, hz⟩
    refine hτ 1 (one_pow _) fun y' _ => ?_
    have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hy
  have hk1 : 1 ≤ k := by omega
  have hcard : Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ k = 1} = k ^ (2 * P.g) :=
    (h.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hK
  have hM' : (M.pull e.inv).IsLB := LB.isLB_linComb hM _ _
  have hv' := vamp_pull e.inv _ M th hv
  rw [e.inv_hom_id_assoc] at hv'
  have H := GlobalTheory.card_zeros_on_torsion_le_of_symmetric_veryAmple h h₂ K P (M.pull e.inv) σ _ C d k hM' hs hv' (fun n hn => ⟨δ * n ^ P.g,
    by rw [mul_pow]; exact Nat.mul_le_mul_right _ hδ, by
      have hn' : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
      have a := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ hn').2.2.2.2.2 _ e.symm _).1 (h0 n hn)
      rw [Iso.symm_hom, e.inv_hom_id_assoc] at a
      exact ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (LB.isLB_linComb hn' _ _)).2.1 _ (LB.isLB_linComb hM' _ _)
        ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y (e.hom ≫ P.A.hom) M hM).2.2.2.2.1 _ e.inv n).symm).1 _ a⟩) hg hK (secPowPull τ e.inv) (by
      rw [← nonzeroLocus_secPowPull] at hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨i, fun e => by rw [e, Scheme.basicOpen_zero] at hi; exact hi⟩)
  rw [nonzeroLocus_secPowPull, Nat.card_congr (Equiv.subtypeEquivRight (q := fun b => b ^ k = 1)
    fun x => ⟨fun a => a.1, fun a => ⟨a, hτ x a⟩⟩), hcard,
    show k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) by rw [← pow_add]; congr 1; omega] at H
  have := Nat.le_of_mul_le_mul_right H (by positivity)
  nlinarith

end GlobalTheory.TorsionCut

namespace GlobalTheory


open TorsionCut in
theorem cutBy_idealOf_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  intro h h₂ g C σ₀ _ _
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule σ₀
  choose d₀ hd₀ using fun δ : ℕ =>
    exists_uniform_regularity_bound σ₀ (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g)
  let d := (Finset.range (C ^ g + 1)).sup d₀ + 1
  refine ⟨d, C ^ g * g.factorial * d + 1, fun δ hδ σ _ r hr => ?_⟩
  have hd : d₀ δ ≤ d := (Finset.le_sup (f := d₀) (Finset.mem_range.2 (Nat.lt_succ_of_le hδ))).trans (Nat.le_succ _)
  obtain ⟨Q, hQ⟩ := regularity_comap_rename_of_surjective σ σ₀ r (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g) hr
  refine ⟨Q, fun K _ _ P hg Y e M th k Hh y p hM hs hv hth h0 hk hK hy hp => ?_⟩
  subst hg
  obtain ⟨th₀, rfl⟩ : ∃ th₀ : σ₀ → M.Sec, th = th₀ ∘ r := by
    obtain ⟨s, hs⟩ := hr.hasRightInverse
    refine ⟨th ∘ s, funext fun a => ?_⟩
    have := funext (hth a (s (r a)) (hs _).symm)
    change th a = th (s (r a))
    generalize th a = u at this
    generalize th (s (r a)) = v at this
    cases u; cases v; cases this; rfl
  have hv₀ := vamp_of_comp _ M th₀ r hr hv
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ₀ Y _ M th₀ hM hv₀
  obtain ⟨_, a₃⟩ := GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf K σ₀ Y _ M th₀ hM hv₀
  have hreg := hd₀ δ K _ a₁ a₂ (by
    filter_upwards [a₃, Filter.eventually_ge_atTop 1] with n ⟨m, hm, _, hm'⟩ hn
    obtain rfl := (GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ (LB.isLB_linComb hM _ _)).1 _ _ hm (h0 n hn)
    have := congrArg (Nat.cast : ℕ → ℚ) hm'
    rw [hQ₀] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast at this
    rw [← this, dimDeg]
    ring)
  have hyp : ∀ i, ((y i).left ≫ e.inv) ≫ e.hom ≫ P.A.hom = 𝟙 _ := fun i => by
    rw [Category.assoc, e.inv_hom_id_assoc]; exact Over.w _
  refine cutBy_of_regular_of_zeroEstimate K σ Hh _ Q d d p le_rfl (fun n hn => ?_) (fun F hF i => ?_)
    fun F hF hz => ?_
  · obtain ⟨b₁, b₂⟩ := hQ K _ _ d (idealOf_comp (e.hom ≫ P.A.hom) hM th₀ r hr) (Nat.le_add_left _ _) n hn
    refine ⟨b₁ (hreg n (hd.trans hn)).1, b₂ fun F hF hFn => ?_⟩
    have h := homogeneousComponent_mul_mem_span_degree _ hd hn ((hreg n (hd.trans hn)).2 F hF hFn) 1
    rwa [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hFn, if_pos rfl] at h
  · simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom] at hF
    exact hF K _ (RingHom.id K) ((y i).left ≫ e.inv) (p i)
      ⟨(hyp i).trans (Spec.map_id _).symm, by rw [Category.comp_id]; exact hp i⟩
  · obtain ⟨τ, -, c₁, c₂⟩ := (GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ Y _ M _ hM hv).2.2 d F hF
    refine c₁.1 (sec_eq_zero h h₂ P e M _ hM hs hv hδ h0 hk hK τ fun x hx => ?_)
    obtain ⟨i, rfl⟩ := hy x hx
    exact (c₂ _ _ (hyp i) (hp i)).1 (hz i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFamily

theorem exists_isSharp_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  intro laws _ cube h g W J a bas hW hbas hunit k o _ b em S _ _ s t₀ hk hd₀
  obtain ⟨t, hd, back⟩ := GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices h g W J a bas k o b em S s t₀ hunit hd₀
  obtain ⟨rmul, radd, rone, rpt⟩ := GlobalTheory.T.dense_fromSet_sharpClass h g W _ _ bas k o b em S s t hd
  obtain ⟨adj, diag⟩ := GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers laws.globalFns cube h g W _ _ bas k o b em S s t hd
  letI := t.ab.comm
  let ρ : Matrix (Fin 8) (Fin 8) ℤ → (t.A ⟶ t.A) := fun m => t.act (Sum.inr m)
  obtain ⟨A, _, pr, hA, hpr, hprod, hρ⟩ := _root_.GlobalTheory.MatrixPower.abelianScheme_matrix_power S t.A ρ t.ab (fun m => t.hom _)
    (fun m m' => rmul (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl) (fun m m' => radd (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl)
    (rone (Sum.inr 1) rfl)
  letI := hA.comm
  obtain ⟨P, hP, r₁, r₂, hsym, hbi, hiso⟩ := GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower W S t.A A pr t.L ρ hW hpr hprod t.isLB
    (cube S t.pol t.L t.isLB) hρ (fun m m' e => adj (Sum.inr m) (Sum.inr m') e) (fun m e => diag (Sum.inr m) e)
  let pt : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := fun i => Over.homMk (t.pt i).left (Over.w (t.pt i))
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A) := fun x =>
    (∏ i, pt i ^ bas.symm (Pi.single 0 x) i) ≫ pr 0
  have hadd : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    have := hpr 0
    simp only [lev, Pi.single_add, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib, MonObj.mul_comp]
  have hpt : ∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left := fun i u => by
    have e₁ : ρ (Matrix.single 0 u 1) ≫ pr 0 = pr u := by
      rw [hρ, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.single_apply, eq_comm]
    have e₂ := rpt (Sum.inr (Matrix.single 0 u 1)) i
    have e₃ : (fun u' => ∑ v, (Sum.elim a id (Sum.inr (Matrix.single 0 u 1)) : Matrix (Fin 8) (Fin 8) ℤ) u' v •
        bas (Pi.single i 1) v) = Pi.single 0 (bas (Pi.single i 1) u) := by
      funext u'
      by_cases hu : u' = 0
      · subst hu
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hu, Ne.symm hu]
    rw [e₃, List.prod_ofFn] at e₂
    rw [← e₁, ← Category.assoc, e₂]
    rfl
  obtain ⟨htor, hgeo⟩ := _root_.GlobalTheory.ZM.level_on_factor_of_eighth_power h g _ bas k o b S s t A pr lev hk.pos hpr hprod hadd hpt
  refine ⟨{ A := A, ab := hA, P := P, isLB := hP, rig₁ := r₁, rig₂ := r₂, symm := hsym, lev := lev, lev_add := hadd,
            lev_tors := htor, geom := fun K _ _ p β z hp hz => ⟨(hgeo K p).1, (hgeo K p).2, fun x y => ?_⟩ },
    ⟨GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form W S t.A A pr t.L P hW t.ab hA hpr hprod t.isLB hP hbi hiso t.ample,
      GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower W S t.A A pr t.L P hpr hprod t.isLB hP hsym hbi hiso t.ktriv⟩,
    back _ ⟨pr, hpr, hprod, hiso, fun j u => ?_, hpt⟩⟩
  · have e : unitOn (z ^ (2 * omegaStd x y)) = unitOn z ^ (2 * omegaStd x y) := map_zpow (Units.map _) _ _
    rw [e]
    exact GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form laws.globalFns h k W S t.A A pr t.L P K p (fun x => toUnit _ ≫ lev x) (unitOn z) hW t.ab hA
      hpr hprod t.isLB hP hsym hbi hiso (fun x y => by rw [hadd, MonObj.comp_mul])
      (fun x => by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
      (_root_.GlobalTheory.weilIs_sharp_levelPoints laws h g W _ bas k o b S s t A pr lev hbas hpr hprod hadd hpt K p β z hp hz) x y
  · rw [rmul (Sum.inr (Sum.elim a id j)) (Sum.inr 1) j (_root_.mul_one _).symm, rone (Sum.inr 1) rfl, Category.id_comp]
    exact hρ _ u

end GlobalTheory.SharpFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.EmbField

theorem exists_section_spMap {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, spMap ψ ≫ spMap φ = 𝟙 _ := by
  obtain ⟨a, -⟩ := hp
  have hsurj : Surjective (spMap φ) := ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, hsurj⟩
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have hinv : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := by
    simp [spMap]
  rw [hinv, IsIso.inv_hom_id]

private theorem projRep_map_of_secCoord_iff {A B σ : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (φ : B →+* A) (hψ : spMap ψ ≫ spMap φ = 𝟙 (Sp B))
    {Z Z' : Scheme.{0}} {s : Z ⟶ Sp A} {s' : Z' ⟶ Sp B} (jz : Z' ⟶ Z) [IsIso jz]
    (hjz : jz ≫ s = s' ≫ spMap ψ) {M : LB Z} {M' : LB Z'} {th : σ → M.Sec} {th' : σ → M'.Sec}
    (hM' : M'.IsLB)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z') (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ jz) w)
    {I : Ideal (MvPolynomial σ A)} (h : ProjRep I s M th) :
    ProjRep (I.map (MvPolynomial.map ψ)) s' M' th' := by
  obtain ⟨-, hpt, hex⟩ := h
  have hs' : s' = jz ≫ s ≫ spMap φ := by
    rw [reassoc_of% hjz, hψ, Category.comp_id]
  have hcomp : ∀ (T : Type) [CommRing T] (β : B →+* T), spMap β ≫ spMap ψ = spMap (β.comp ψ) := by
    intro T _ β
    exact (spMap_comp β ψ).symm
  have hker : ∀ (T : Type) [CommRing T] (β : B →+* T) (v : σ → T),
      (∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0) →
        ∀ F ∈ I.map (MvPolynomial.map ψ), MvPolynomial.eval₂ β v F = 0 := by
    intro T _ β v hv F hF
    have hle : I.map (MvPolynomial.map ψ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      refine Ideal.map_le_iff_le_comap.2 fun G hG => ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact hv G hG
    simpa [RingHom.mem_ker] using hle hF
  refine ⟨hM', fun T _ β x v hx hc => ?_, fun T _ β v hv hI => ?_⟩
  · have hx' : (x ≫ jz) ≫ s = spMap (β.comp ψ) := by
      rw [Category.assoc, hjz, ← Category.assoc, hx, hcomp]
    obtain ⟨hspan, hzero⟩ := hpt T (β.comp ψ) (x ≫ jz) v hx' ((e T x v).1 hc)
    exact ⟨hspan, hker T β v hzero⟩
  · have hI' : ∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0 := by
      intro F hF
      rw [← MvPolynomial.eval₂_map]
      exact hI _ (Ideal.mem_map_of_mem _ hF)
    obtain ⟨x₀, ⟨hx₀, hc₀⟩, hu⟩ := hex T (β.comp ψ) v hv hI'
    refine ⟨x₀ ≫ inv jz, ⟨?_, ?_⟩, fun y hy => ?_⟩
    · simp only [hs', Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc, hx₀, ← hcomp, Category.assoc, hψ, Category.comp_id]
    · exact (e T _ v).2 (by rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    · have hyx : y ≫ jz = x₀ :=
        hu _ ⟨by rw [Category.assoc, hjz, ← Category.assoc, hy.1, hcomp], (e T y v).1 hy.2⟩
      rw [← hyx, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem exists_emb_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  intro hL hL2 o _ g N' J b K _ s t m w hm h2 hth
  have hLB : (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB := by
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.isLB _ _
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ :=
    _root_.GlobalTheory.ZM.EmbedLocal.exists_emb_projRep hL hL2 o g N' J b (Sp K) s t m K (𝟙 _) w hm h2 hth (default : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_section_spMap φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by simpa using hψ)
  have hA1 : IsAffine (Over.mk (spMap φ ≫ 𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of R')) from inferInstance
  have hA2 : IsAffine (Over.mk (𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of K)) from inferInstance
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.emb_baseChange hL2 o g N' J b (Sp K) s t m _ _ h σ hA1 hA2 hE
  refine ⟨σ', hE', ?_⟩
  have : IsIso (spMap φ) := by
    obtain ⟨a, -⟩ := hp
    exact (isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨hφ, ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩⟩
  have : IsIso (spMap ψ ≫ spMap φ) := by rw [hψ]; infer_instance
  have : IsIso (spMap ψ) := IsIso.of_isIso_comp_right (spMap ψ) (spMap φ)
  have : IsIso ((Over.forget (Sp K)).map h) := show IsIso (spMap ψ) from inferInstance
  have : IsIso h := isIso_of_reflects_iso h (Over.forget (Sp K))
  have : IsIso (h ▷ t.A).left := show IsIso ((Over.forget (Sp K)).map (h ▷ t.A)) from inferInstance
  have hsq := (GlobalTheory.EmbPull.isPullback_whisker t.A h).w
  have hP' := projRep_map_of_secCoord_iff ψ φ hψ (h ▷ t.A).left hsq hLB hc hP
  exact ideals_homogeneous.2.2 K _ _ _ _ _ _ hP'

end GlobalTheory.ZM.EmbField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstantsPolarisedLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem exists_holomorphic_thetaConstants_of_family : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (d : ℕ) (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), Odd N' → Function.Bijective EF → IsOpen B → (∀ x, DifferentiableOn ℂ (fun bb => Q bb x) B) → (∀ bb ∈ B, (Function.Injective (Q bb) ∧ DiscreteTopology ((Q bb)).range ∧ Submodule.span ℝ (Set.range (Q bb)) = ⊤ ∧ ((Hm bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm bb) z z).re) ∧ ∀ x y, (hermForm (Hm bb) ((Q bb) x) ((Q bb) y)).im = EF x y) ∧ ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q bb x) = Q bb (ac w x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) ∧ ∀ bb ∈ B, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q bb) x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q bb) (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q bb) x) = (Q bb) (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.HasTh (𝟙 _) (θ bb) := by
  intro hL hL2 _ hU o _ g N' J b em w w' La _ EF lam ac d B Q Hm hN hE hB hQ hpol hsum hadj
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨0, fun _ => differentiableOn_empty, fun _ h => absurd h (Set.notMem_empty _)⟩
  obtain ⟨hp₀, F₀, hF₀⟩ := hpol b₀ hb₀
  obtain ⟨hfree, hfin, -, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g (Q b₀) (Hm b₀) hp₀
  have hadd : ∀ x y, ac w (x + y) = ac w x + ac w y := fun x y => hp₀.1 (by
    rw [map_add (f := _), ← hF₀, ← hF₀, ← hF₀, map_add (f := _), map_add (f := _)])
  let W : La →ₗ[ℤ] La := (AddMonoidHom.mk' (ac w) hadd).toIntLinearMap
  have hW : ∀ x, W x = ac w x := fun _ => rfl
  have hW' : ∀ x, (LinearMap.id - W : La →ₗ[ℤ] La) x = ac w' x := fun x => by
    rw [LinearMap.sub_apply, LinearMap.id_apply, hW, sub_eq_iff_eq_add', hsum]
  have hsemi := neg_one_zpow_form_apply_semicharacter La EF W (LinearMap.id - W) halt
    (add_sub_cancel _ _) (fun x y => by rw [hW, hW', hadj])
  simp only [hW] at hsemi
  obtain ⟨θ, hθ, hhol⟩ := HolTheta.exists_theta_holomorphic La EF
    (fun x => (-1 : ℂ) ^ EF x (ac w x)) g d N' B Q Hm hN.pos hE
    (fun x => by
      rcases Int.even_or_odd (EF x (ac w x)) with h | h
      · exact Or.inl h.neg_one_zpow
      · exact Or.inr h.neg_one_zpow)
    hsemi hB hQ (fun bb hb => (hpol bb hb).1)
  let x : Ix g (N' ^ 2) → La := fun a => ∑ i, ((a i).val : ℤ) • lam i
  refine ⟨fun z a => (-1 : ℂ) ^ EF (x a) (ac w (x a)) *
      (Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm (Hm z) (Q z (x a)) (Q z (x a))) *
        θ z ((N' : ℂ)⁻¹ • Q z (x a))), fun a => (hhol (x a)).const_mul _, ?_⟩
  rintro bb hb t ⟨u, χ', hAH, hΛ, hχ, hpt, -⟩
  obtain ⟨hne, hdiff, hfe⟩ := hθ bb hb
  let lam' : Fin (2 * g) → u.Λ := fun i => ⟨Q bb (lam i), (hΛ _).2 ⟨_, rfl⟩⟩
  have hth : u.IsThetaFn (Hm bb) χ' 1 (θ bb) := by
    refine ⟨hdiff, fun l z => ?_⟩
    obtain ⟨y, hy⟩ := (hΛ l).1 l.2
    rw [pow_one, hχ y l hy.symm, ← hy, hfe]
  have key := _root_.GlobalTheory.ThetaClassical.hasTh_classical hL hL2 hU o g N' J b em t u (Hm bb) χ' (θ bb) lam' hN hAH hth hne
    (fun i => by rw [hpt i, Nat.cast_pow])
  have hx : ∀ a : Ix g (N' ^ 2),
      ∑ i, ((a i).val : ℂ) • (lam' i : Fin g → ℂ) = Q bb (x a) := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, lam', map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hx' : ∀ a : Ix g (N' ^ 2),
      χ' (∑ i, ((a i).val : ℤ) • lam' i) = (-1) ^ EF (x a) (ac w (x a)) := fun a => by
    refine hχ _ _ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, lam', map_sum, map_zsmul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  simp only [hx, hx'] at key
  convert key using 2 with a
  exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory
end

