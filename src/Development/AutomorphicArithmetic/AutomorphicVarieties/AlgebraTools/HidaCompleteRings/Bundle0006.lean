module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmLocal
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M], OrdAdm (M := M) (IsLocalRing.maximalIdeal R) ∧ (Finite (IsLocalRing.ResidueField R) → ∀ k : ℕ, Finite (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M))) := by
  intro R _ M _ _ _ _ _ _
  haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  have hOrd : OrdAdm (M := M) (IsLocalRing.maximalIdeal R) := by
    refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin (IsLocalRing.maximalIdeal R), fun k => ?_⟩
    have hMax {I : Ideal R} [IsArtinianRing (R ⧸ I)] (P : Ideal R) [P.IsPrime]
        (h : I ≤ P) : P.IsMaximal := by
      have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
      have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (K := P.map (Ideal.Quotient.mk I))
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 h] at h3
    have hArtPow (k : ℕ) : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
      rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
      intro p hp
      have h0 : IsLocalRing.maximalIdeal R ^ k ≤ p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)) := by
        intro x hx
        simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have h1 : (p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))).IsMaximal :=
        hMax _ (Ideal.IsPrime.le_of_pow_le h0)
      have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
        Ideal.Quotient.mk_surjective p
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
          Ideal.Quotient.mk_surjective h1 with h | h
      · exact absurd (h2 ▸ h) hp.ne_top
      · exact h2 ▸ h
    haveI := hArtPow k
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    refine ⟨inferInstance, ?_⟩
    haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k)
        (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact isArtinian_of_surjective_algebraMap (R := R ⧸ IsLocalRing.maximalIdeal R ^ k)
      Ideal.Quotient.mk_surjective
  refine ⟨hOrd, fun hfin k => ?_⟩
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    infer_instance
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocFree
section
open IsLocalRing UpperTheory.V.Hi

private theorem pres_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) (n : ℕ) : ∀ y ∈ N, (T ^ n) y ∈ N := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih => intro y hy; rw [pow_succ', mul_apply_eq_comp]; exact h _ (ih y hy)

private theorem pres_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (I : Ideal A) (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) : ∀ y ∈ I • N, T y ∈ I • N := by
  intro y hy
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr (h n hn)
  · rw [map_add]; exact add_mem hx hy

private theorem pres_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (c : A) (h : ∀ y ∈ N, T y ∈ N) :
    ∀ y ∈ N, (T - algebraMap A (Module.End A M) c) y ∈ N := by
  intro y hy
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
  exact sub_mem (h y hy) (N.smul_mem c hy)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locFree :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → CommOn (locPart Y op a) op ∧ locPart (locPart Y op a) op a = locPart Y op a ∧ Module.Finite A (locPart Y op a) ∧ (∃ Z : Submodule A M, Disjoint (locPart Y op a) Z ∧ locPart Y op a ⊔ Z = Y ∧ ∀ i, ∀ z ∈ Z, op i z ∈ Z) ∧ (Module.Projective A Y → Module.Free A (locPart Y op a)) := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨e, -, he, hmem, hcomm⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A M ι Y op a h
  have hLY : locPart Y op a ≤ Y := inf_le_left
  have hee : ∀ y : Y, e (e y) = e y := fun y => by
    rw [← mul_apply_eq_comp, he.eq]
  have heL : ∀ y : Y, (e y : M) ∈ locPart Y op a := fun y => (hmem _).2 (hee y)
  have hc : ∀ j (y : Y), e ⟨op j y, h.1 j y y.2⟩ = ⟨op j (e y), h.1 j _ (e y).2⟩ := by
    intro j y
    have := hcomm ((op j).restrict (h.1 j)) (fun i t ht => by
      ext z
      have h1 : ∀ w : Y, (t w : M) = op i w := ht
      simp only [mul_apply_eq_comp, h1, LinearMap.coe_restrict_apply]
      exact h.2 j i z z.2)
    exact (LinearMap.congr_fun this y).symm
  have hst : ∀ i, ∀ y ∈ locPart Y op a, op i y ∈ locPart Y op a := by
    intro i y hy
    have h1 := (hmem ⟨y, hLY hy⟩).1 hy
    refine (hmem ⟨op i y, h.1 i y (hLY hy)⟩).2 ?_
    have h2 := hc i ⟨y, hLY hy⟩
    rw [h2]
    simp only [h1]
  let E : Y →ₗ[A] locPart Y op a := LinearMap.codRestrict _ (Y.subtype ∘ₗ e) heL
  have hE : E ∘ₗ Submodule.inclusion hLY = LinearMap.id := by
    ext x
    exact congrArg (fun w : Y => (w : M)) ((hmem ⟨x, hLY x.2⟩).1 x.2)
  have hfin : Module.Finite A (locPart Y op a) :=
    Module.Finite.of_surjective E fun x => ⟨_, LinearMap.congr_fun hE x⟩
  have hkey : ∀ (I : Ideal A), ∀ w ∈ locPart Y op a, w ∈ I • Y → w ∈ I • locPart Y op a := by
    intro I w hw hw'
    have h0 : ∀ y ∈ I • (⊤ : Submodule A Y), (e y : M) ∈ I • locPart Y op a := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun x y hx hy => ?_)
      · rw [map_smul]; exact Submodule.smul_mem_smul hr (heL n)
      · rw [map_add]; exact add_mem hx hy
    have h1 := h0 ⟨w, hLY hw⟩ ((Submodule.mem_smul_top_iff I Y _).2 hw')
    rwa [(hmem ⟨w, hLY hw⟩).1 hw] at h1
  refine ⟨⟨hst, fun i j y hy => h.2 i j y (hLY hy)⟩, ?_, hfin, ?_, fun hP => ?_⟩
  · refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
    have hx2 := hx.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx2 ⊢
    intro i k
    have hmono : Monotone fun n : ℕ =>
        (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n) := by
      refine monotone_nat_of_le_succ fun n y hy => ?_
      rw [Submodule.mem_comap] at hy ⊢
      rw [pow_succ', mul_apply_eq_comp]
      exact pres_smul Y _ _ (pres_sub Y _ _ (h.1 i)) _ hy
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (hx2 i k)
    refine Submodule.mem_iSup_of_mem n ?_
    exact hkey _ _ (pres_pow _ _ (pres_sub _ _ _ (hst i)) n x hx) hn
  · refine ⟨(LinearMap.ker e).map Y.subtype, ?_, ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨y, hy, rfl⟩
      have h1 := (hmem y).1 hx
      have h2 : e y = 0 := hy
      rw [← h1, h2, map_zero]
    · refine le_antisymm (sup_le hLY (Submodule.map_subtype_le _ _)) fun x hx => ?_
      have : x = (e ⟨x, hx⟩ : M) + Y.subtype (⟨x, hx⟩ - e ⟨x, hx⟩) := by simp
      rw [this]
      refine Submodule.add_mem_sup (heL _) ⟨_, ?_, rfl⟩
      change e _ = 0
      rw [map_sub, hee, sub_self]
    · rintro i x ⟨y, hy, rfl⟩
      have h2 : e y = 0 := hy
      refine ⟨⟨op i y, h.1 i y y.2⟩, ?_, rfl⟩
      change e _ = 0
      rw [hc]
      simp [h2]
  · have : Module.Projective A (locPart Y op a) := Module.Projective.of_split _ _ hE
    exact Module.free_of_flat_of_isLocalRing
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepScalar
section
open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repScalar :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type} [AddCommGroup N] [Module k N] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (σ : Representation k G N), IsSmooth σ → ∀ (Y : Submodule k V), Y ≤ copies ρ Y σ → ∀ (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → (Y ⊓ eig ρ K χ ≠ ⊥ → eig σ K χ ≠ ⊥) ∧ ∀ (A : Module.End k V) (A' : Module.End k N) (a : k), (∀ f : Into ρ Y σ, ∀ n ∈ eig σ K χ, A (f.1 n) = f.1 (A' n)) → (∀ n ∈ eig σ K χ, A' n = a • n) → ∀ v ∈ Y ⊓ eig ρ K χ, A v = a • v := by
  intro k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y hY K χ hK hχ
  have key : Y ⊓ eig ρ K χ ≤ ⨆ f : Into ρ Y σ, Submodule.map (f : N →ₗ[k] V) (eig σ K χ) := by
    rw [← repEigSum ρ σ hσ Y K χ hK hχ]
    exact inf_le_inf_right _ hY
  refine ⟨fun hne hσ0 => hne ?_, ?_⟩
  · apply le_bot_iff.mp
    refine key.trans ?_
    simp [hσ0]
  · intro A A' a hA hA' v hv
    refine Submodule.iSup_induction (fun f : Into ρ Y σ => Submodule.map (f : N →ₗ[k] V) (eig σ K χ))
      (motive := fun x => A x = a • x) (key hv) ?_ ?_ ?_
    · intro f w hw
      obtain ⟨n, hn, rfl⟩ := hw
      have h1 := hA f n hn
      rw [hA' n hn, map_smul] at h1
      exact h1
    · simp
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, smul_add]
end

