module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLatOm
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem dual_of_lattice {A F W : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    [AddCommGroup W] [Module F W] [Module A W] [IsScalarTower A F W] (P : Submodule A W)
    [Module.Finite A P] [Module.Projective A P] (hP : Submodule.span F (P : Set W) = ⊤) :
    ∃ (n : ℕ) (v : Fin n → W) (φ : Fin n → W →ₗ[F] F), (∀ k, v k ∈ P) ∧
      (∀ k, ∀ p ∈ P, φ k p ∈ (algebraMap A F).range) ∧ ∀ w, w = ∑ k, φ k w • v k := by
  classical
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let S := nonZeroDivisors A
  have hsurj : ∀ w : W, ∃ (s : S) (p : P), (s : A) • w = (p : W) := by
    intro w
    have hw : w ∈ Submodule.span F (P : Set W) := hP ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem z hz => exact ⟨1, ⟨z, hz⟩, by simp⟩
    | zero => exact ⟨1, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨t, q, h'⟩ := hb
      refine ⟨s * t, (t : A) • p + (s : A) • q, ?_⟩
      simp only [Submonoid.coe_mul, smul_add, Submodule.coe_add, Submodule.coe_smul, ← h, ← h', smul_smul]
      rw [mul_comm (t : A) (s : A)]
    | smul c a _ ha =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S c
      refine ⟨s * t, b • p, ?_⟩
      have ht : algebraMap A F (t : A) * IsLocalization.mk' F b t = algebraMap A F b := IsLocalization.mk'_spec' F b t
      rw [Submodule.coe_smul, ← h, Submonoid.coe_mul, mul_comm, mul_smul, smul_comm (s : A), ← algebraMap_smul F (t : A),
        smul_smul, ht, algebraMap_smul, smul_comm]
  have hloc : IsLocalizedModule S P.subtype := by
    refine ⟨fun s => ?_, fun w => ?_, fun {p q} h => ⟨1, ?_⟩⟩
    · have hs : algebraMap A F (s : A) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b h
        simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul F (s : A) a, ← algebraMap_smul F (s : A) b] at h
        exact smul_right_injective W hs h
      · intro b
        refine ⟨(algebraMap A F (s : A))⁻¹ • b, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul F (s : A), smul_smul, mul_inv_cancel₀ hs, one_smul]
    · obtain ⟨s, p, h⟩ := hsurj w
      exact ⟨(p, s), h⟩
    · have : p = q := Subtype.ext h
      simp [this]
  let ψ : Fin n → P →ₗ[A] F := fun k => Algebra.linearMap A F ∘ₗ LinearMap.proj k ∘ₗ g
  have hunit : ∀ s : S, IsUnit (algebraMap A (Module.End A F) (s : A)) := fun s =>
    IsLocalizedModule.map_units (S := S) (f := Algebra.linearMap A F) s
  let Ψ : Fin n → W →ₗ[A] F := fun k => IsLocalizedModule.lift S P.subtype (ψ k) hunit
  have hΨ : ∀ k (p : P), Ψ k (p : W) = ψ k p := fun k p =>
    IsLocalizedModule.lift_apply S P.subtype (ψ k) hunit p
  let φ : Fin n → W →ₗ[F] F := fun k => (Ψ k).extendScalarsOfIsLocalization S F
  have hφ : ∀ k (p : P), φ k (p : W) = algebraMap A F (g p k) := fun k p => hΨ k p
  have hid : ∀ p : P, (p : W) = ∑ k, φ k (p : W) • ((f (Pi.single k 1) : P) : W) := by
    intro p
    have h1 : f (g p) = p := congrArg (fun u => u p) hfg
    have h2 : g p = ∑ k, g p k • (Pi.single k (1 : A) : Fin n → A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hφ, algebraMap_smul]
  refine ⟨n, fun k => (f (Pi.single k 1) : P), φ, fun k => (f (Pi.single k 1)).2, ?_, ?_⟩
  · rintro k p hp
    exact ⟨g ⟨p, hp⟩ k, (hφ k ⟨p, hp⟩).symm⟩
  · have : (LinearMap.id : W →ₗ[F] W) = ∑ k, (φ k).smulRight ((f (Pi.single k 1) : P) : W) := by
      refine LinearMap.ext_on hP ?_
      intro p hp
      simpa using hid ⟨p, hp⟩
    intro w
    simpa using congrArg (fun u => u w) this

private theorem lat_of_isBundle {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (hx : IsPd ℂ x)
    {W V : Type} [AddCommGroup W] [Module F W] [Module ℂ W] [IsScalarTower ℂ F W]
    [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V] (e : W →ₗ[F] V)
    (he : Function.Injective e) (L : Finset (Fin (d + 1)) → Submodule ℂ W) (hL : IsBundle ℂ x L)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (M : Submodule ℂ V)
    (hM : ∀ m ∈ M, ∃ w, e w = m) (hML : ∀ w, w ∈ L I ↔ e w ∈ M) :
    Lat (rA ℂ x I) M ∧ ∀ w, e w ∈ Submodule.span F (M : Set V) := by
  classical
  haveI : IsFractionRing (rA ℂ x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x hx {i} (Finset.singleton_nonempty i)).1
  obtain ⟨s, hs, hsF⟩ := hL.fg i
  let P : Submodule (rA ℂ x {i}) W := Submodule.span (rA ℂ x {i}) (L {i} : Set W)
  have hPs : P = Submodule.span (rA ℂ x {i}) (s : Set W) := by
    change Submodule.span (rA ℂ x {i}) (L {i} : Set W) = _
    rw [hs]
    exact Submodule.span_eq _
  haveI : Module.Finite (rA ℂ x {i}) P := Module.Finite.iff_fg.2 ⟨s, hPs.symm⟩
  haveI : Module.Projective (rA ℂ x {i}) P := hL.proj i
  have hP : Submodule.span F (P : Set W) = ⊤ := by
    rw [eq_top_iff, ← hsF]
    refine Submodule.span_mono fun z hz => ?_
    rw [hPs]
    exact Submodule.subset_span hz
  obtain ⟨n, v, φ, hv, hφ, hid⟩ := dual_of_lattice P hP
  obtain ⟨r, hr⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 he)
  have hre : ∀ w, r (e w) = w := fun w => LinearMap.congr_fun hr w
  have hLI := hL.loc I i hi
  have hLii := hL.loc {i} i (Finset.mem_singleton_self i)
  have hPL : ∀ p ∈ P, p ∈ L {i} := fun p hp => by
    rw [hLii]
    exact hp
  have hLsub : ∀ w ∈ L {i}, w ∈ L I := fun w hw => by
    rw [hLI]
    exact Submodule.subset_span hw
  have hmono : rA ℂ x {i} ≤ rA ℂ x I := Algebra.adjoin_mono fun y ⟨a, ha, h⟩ =>
    ⟨a, by rw [Finset.mem_singleton.1 ha]; exact hi, h⟩
  have hsm : ∀ c ∈ rA ℂ x I, ∀ w ∈ L I, c • w ∈ L I := fun c hc w hw => by
    rw [hLI] at hw ⊢
    exact Submodule.smul_mem (Submodule.span (rA ℂ x I) (L {i} : Set W)) (⟨c, hc⟩ : rA ℂ x I) hw
  have hval : ∀ k, ∀ w ∈ L I, φ k w ∈ rA ℂ x I := by
    intro k w hw
    rw [hLI] at hw
    have hw' : w ∈ Submodule.span (rA ℂ x I) (L {i} : Set W) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy⟩ := hφ k z (Submodule.subset_span hz)
      rw [← hy]
      exact hmono y.2
    | zero => simpa using (rA ℂ x I).zero_mem
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact (rA ℂ x I).add_mem ha hb
    | smul c a _ ha =>
      have : φ k (c • a) = (c : F) * φ k a := by
        rw [show c • a = (c : F) • a from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact (rA ℂ x I).mul_mem c.2 ha
  refine ⟨⟨fun c hc m hm => ?_, n, fun k => e (v k), fun k => φ k ∘ₗ r, fun k => ?_, fun k m hm => ?_, fun m hm => ?_⟩, fun w => ?_⟩
  · obtain ⟨w, rfl⟩ := hM m hm
    rw [← map_smul]
    exact (hML _).1 (hsm c hc w ((hML w).2 hm))
  · exact (hML _).1 (hLsub _ (hPL _ (hv k)))
  · obtain ⟨w, rfl⟩ := hM m hm
    simpa [hre] using hval k w ((hML w).2 hm)
  · obtain ⟨w, rfl⟩ := hM m hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, hre, ← map_smul, ← map_sum]
    exact congrArg e (hid w)
  · have hw : w ∈ Submodule.span F (s : Set W) := hsF ▸ Submodule.mem_top
    have hsL : ∀ z ∈ s, e z ∈ M := fun z hz => (hML z).1 (hLsub z (hPL z (by rw [hPs]; exact Submodule.subset_span hz)))
    have hmap : (Submodule.span F (s : Set W)).map e ≤ Submodule.span F (M : Set V) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hsL z hz
    exact hmap ⟨w, hw, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.latOm_of :
    LatOm := by
  intro F K _ _ _ _ _ _ d x hc a I hI
  obtain ⟨i, hi⟩ := hI
  have hB := GlobalTheory.T.regularForms_isBundle_projectiveCover ℂ F K d (xv x) hc a (⋀[K]^a Ω[K⁄ℂ]) (⋀[K]^a Ω[K⁄ℂ]).subtype
    Subtype.val_injective (Submodule.range_subtype _)
  have hle : omB ℂ K (rB ℂ K (xv x) I) a ≤ (⋀[K]^a Ω[K⁄ℂ]).restrictScalars ℂ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, v, -, rfl⟩
    refine (⋀[K]^a Ω[K⁄ℂ]).smul_mem b ?_
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact Submodule.subset_span ⟨_, rfl⟩
  have key := lat_of_isBundle hc.pd (((⋀[K]^a Ω[K⁄ℂ]).subtype).restrictScalars F) Subtype.val_injective _ hB I i hi
    (omB ℂ K (rB ℂ K (xv x) I) a) (fun m hm => ⟨⟨m, hle hm⟩, rfl⟩) (fun w => Iff.rfl)
  exact ⟨key.1, fun w hw => key.2 ⟨w, hw⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPTheta
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

private lemma lat_mem (hA : LatA) {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)
    (hpd : IsPd ℂ (xv x)) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) :
    (∏ m ∈ Iᶜ, ((x m : F) / x i)) ∈ omA ℂ (xv x) I := by
  rw [(hA F d x hpd I i hi).2.1]
  have hne : (∏ m ∈ Iᶜ, ((x m : F) / x i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => div_ne_zero (x m).ne_zero (x i).ne_zero
  have e : (∏ m ∈ Iᶜ, ((x m : F) / x i)) / omG x i = ∏ m ∈ I, ((x i : F) / x m) := by
    unfold omG
    rw [← Finset.prod_mul_prod_compl I (fun l => (x l : F) / x i), div_mul_cancel_right₀ hne,
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun m _ => inv_div _ _
  rw [e]
  exact Subalgebra.prod_mem _ fun m hm => Algebra.subset_adjoin ⟨m, hm, i, rfl⟩

private lemma prod_split {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (I : Finset (Fin (d + 1)))
    (i : Fin (d + 1)) : ∏ m ∈ Iᶜ, (x m : F) = (∏ m ∈ Iᶜ, ((x m : F) / x i)) * (x i : F) ^ Iᶜ.card := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (div_mul_cancel₀ _ (x i).ne_zero).symm

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
  {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ)

private lemma act_tmul (f g : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (g ⊗ₜ w) = (f * g) ⊗ₜ (k • w) := by
  simp [sysP, Module.endTensorEndAlgHom_apply]

private lemma mulP_one (w : DR ℂ K) : mulP F K ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [mulP]

private lemma X_val (i : Fin (d + 1)) : (((sysP K x a).X i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) = (x i : F) ⊗ₜ 1 := rfl

private lemma Y_val (i : Fin (d + 1)) : (((sysP K x a).Y i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
    1 ⊗ₜ algebraMap F K (x i) := rfl

end

theorem UpperTheory.Gal.productCup_of_system.pTheta_of :
    MJ → ThMu → ThMuLat → KapInd → LatA → ActsLin → GoodZ → SysBasic → SysOk → PTheta := by
  intro hMJ hTh hLat hKap hLA hAL hG hSB _ F K _ _ _ _ _ _ d x hc a p β hβ
  have hU := wdUni_of
  have hl : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), lft (uni b L) = b :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.1
  have hr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), rgt (uni b L) = L :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1
  have hcard : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B),
      (uni b L).card = b.card + L.card :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1
  have hlr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (s : Finset (A ⊕ₗ B)), uni (lft s) (rgt s) = s :=
    fun {A B} _ _ s => (hU A B ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s
  have hGood : (sysP K x a).Good := (hG F K d x hc a).2.1
  have hβC : ∀ J, β J ∈ (if J.Nonempty ∧ (J.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) J) a else ⊥) :=
    fun J => hβ.1 J (Set.mem_univ J)
  set b : Finset (Fin (d + 1)) → F ⊗[ℂ] DR ℂ K := fun J => (1 : F) ⊗ₜ[ℂ] β J with hbdef
  have hb0 : ∀ J, ¬ (J.Nonempty ∧ J.card = p + 1) → b J = 0 := by
    intro J hJ
    have h := hβC J
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hJ ⟨h1, by exact_mod_cast h2⟩)] at h
    simp only [hbdef, (Submodule.mem_bot ℂ).1 h, TensorProduct.tmul_zero]
  have hb1 : deltaL ℂ _ _ b = 0 := by
    funext t
    have h0 : deltaL ℂ _ _ β t = 0 := congrFun hβ.2 t
    change ∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i) = 0
    have h1 : ∑ i ∈ t, GlobalTheory.cubeSign t i • β (t.erase i) = 0 := h0
    have h2 := congrArg (TensorProduct.mk ℂ F (DR ℂ K) 1) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by simp only [hbdef, Units.smul_def, map_zsmul, TensorProduct.mk_apply]
  have hb2 : ∀ J, J.card ≠ p + 1 → b J = 0 := fun J hJ => hb0 J fun h => hJ h.2
  have hθ0 : ∀ (I : Finset (Fin (d + 1))) (L : Finset (Mi d)), I.card + L.card ≠ d + 1 →
      detC (sysP K x a).rowMu (uni I L) = 0 := by
    intro I L h
    unfold detC
    rw [dite_eq_right (by rw [hcard]; exact h)]
  have hθe : ∀ L : Finset (Mi d), detC (sysP K x a).rowMu (uni ∅ L) = 0 :=
    (hTh d _ _ (sysP K x a)).2.1
  have hval : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) =
        ((-1 : ℤ) ^ ((p + 1) * L.card)) • (sysP K x a).act (detC (sysP K x a).rowMu (uni I L)) (b J) := by
    intro I J L
    simp only [Sys.mj, hl, hr]
  have hzero : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (I = ∅ ∨ ¬ (J.Nonempty ∧ J.card = p + 1) ∨ I.card + L.card ≠ d + 1) →
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
    intro I J L h
    rw [hval]
    rcases h with rfl | h | h
    · rw [hθe]; simp
    · rw [hb0 J h]; simp
    · rw [hθ0 I L h]; simp
  refine ⟨(sysP K x a).mj p (detC (sysP K x a).rowMu) b, ?_, ?_, ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [(hSB d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu _).2.1]
      intro I J
      split_ifs with hIJ
      · obtain ⟨hI, hJ⟩ := hIJ
        intro L _
        change (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) ∈ _
        dsimp only
        rw [SetLike.mem_coe]
        split_ifs with hL
        · by_cases hJc : J.card = p + 1
          · have hIL : I.card + L.card = d + 1 := by push_cast [hJc] at hL; omega
            have hi := pk_mem hI
            have hj := pk_mem hJ
            obtain ⟨s, hs, hdet⟩ := (hLat d _ _ (sysP K x a) hGood).2 I J L hI (pk J) hj
            have hbJ : β J ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
              have h := hβC J
              rwa [if_pos ⟨hJ, by exact_mod_cast hJc⟩] at h
            have hcompl : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            have hfm := lat_mem hLA x hc.pd I (pk I) hi
            have hsplit := prod_split x I (pk I)
            generalize (∏ m ∈ Iᶜ, ((x m : F) / x (pk I))) = f at hfm hsplit
            have hm : f ⊗ₜ[ℂ] β J ∈ (sysP K x a).M I J := Submodule.apply_mem_map₂ _ hfm hbJ
            have hm' := hGood.stab I J hI hJ s hs _ hm
            have hXprod : ∏ m ∈ Iᶜ, (((sysP K x a).X m : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
                (f ⊗ₜ (1 : K)) * (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have e := congrArg (Algebra.TensorProduct.includeLeftRingHom : F →+* F ⊗[ℂ] K) hsplit
              rw [map_prod, map_mul, map_pow, hcompl] at e
              exact e
            have hU' : (((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ)) : F ⊗[ℂ] K) =
                (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card *
                  (((sysP K x a).Y (pk J) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have : ∀ l : Mi d, (sysP K x a).u n11 (pk I) (pk J) l = (sysP K x a).X (pk I) * (sysP K x a).Y (pk J) := by
                intro l; simp [Sys.u, n11]
              simp only [this, Finset.prod_const, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
            have hact : (sysP K x a).act (f ⊗ₜ (1 : K)) (b J) = f ⊗ₜ[ℂ] β J := by
              simp [hbdef, act_tmul]
            rw [hval]
            apply zsmul_mem
            refine ⟨(sysP K x a).act s (f ⊗ₜ[ℂ] β J), hm', ?_⟩
            rw [hdet, hXprod, hU', ← hact, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2
            ring
          · rw [hzero I J L (Or.inr (Or.inl fun h => hJc h.2))]
            exact Submodule.zero_mem _
        · have : (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
            refine hzero I J L ?_
            by_cases hJc : J.card = p + 1
            · refine Or.inr (Or.inr fun h => hL ?_)
              push_cast [hJc]; omega
            · exact Or.inr (Or.inl fun h => hJc h.2)
          rw [this]
          exact Submodule.zero_mem _
      · funext L
        refine hzero I J L ?_
        by_cases hI : I.Nonempty
        · exact Or.inr (Or.inl fun h => hIJ ⟨hI, h.1⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 hI)
    · exact hMJ d _ _ (sysP K x a) (Mi d) (sysP K x a).mu p _ b (hTh d _ _ (sysP K x a)).1 hb1 hb2
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    refine hzero I J L ?_
    by_cases hI : I = ∅
    · exact Or.inl hI
    · refine Or.inr (Or.inr fun h => hI ?_)
      exact Finset.card_eq_zero.1 (by omega)
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    have hedge : edge2 β (uni I J) = if I.card = 1 then β J else 0 := by simp only [edge2, hl, hr]
    rw [hedge]
    by_cases hI : I.card = 1
    · rw [if_pos hI]
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hI
      obtain ⟨τ, hτ⟩ := hc.exists_isTop
      have h5 := (hAL F K d x hc τ hτ a).2.2.2.2.1
      have hk := hKap F K d x hc _ _ (sysP K x a)
        (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K))
        (fun m => by rw [X_val]; simp) (fun m => by rw [Y_val]; simp) i L hL
      rw [hval, hL, map_zsmul, h5, hk, hbdef]
      simp only [mulP_one]
      rw [smul_comm]
    · rw [if_neg hI, hzero I J L (Or.inr (Or.inr (by omega)))]
      simp
  · intro J
    rw [hval, (hTh d _ _ (sysP K x a)).2.2.1]
    simp [hbdef]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PowMulMem
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → Fˣ}

private lemma ratio_mem (i j : Fin (d + 1)) :
    algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := by
  have hm : ((x j : F) / x i) ∈ rA ℂ (xv x) {i} :=
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := rA ℂ (xv x) {i}) (x := ⟨_, hm⟩)

private lemma pow_mul_mem (h : IsFinCover ℂ K (xv x)) (i i' : Fin (d + 1)) (b : K)
    (hb : b ∈ rB ℂ K (xv x) {i}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} := by
  by_cases hne : i = i'
  · subst hne
    refine ⟨0, fun N _ => ?_⟩
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i i) N) hb
  have hb' : b ∈ rB ℂ K (xv x) {i, i'} :=
    (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i} i (by simp)).1 {i, i'} (by simp) hb
  obtain ⟨N0, hN0⟩ :=
    ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i, i'} i' (by simp)).2 b).mp hb'
  rw [Finset.prod_pair hne, div_self (Units.ne_zero (x i')), mul_one] at hN0
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have e : algebraMap F K ((x i : F) / x i') ^ (N0 + k) * b =
      algebraMap F K ((x i : F) / x i') ^ k * (b * algebraMap F K ((x i : F) / x i') ^ N0) := by
    ring
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i' i) k) hN0

private lemma gens (h : IsFinCover ℂ K (xv x)) (i : Fin (d + 1)) :
    ∃ G : Finset K, Algebra.adjoin ℂ (G : Set K) = rB ℂ K (xv x) {i} := by
  haveI := h.smooth i
  exact (Subalgebra.fg_iff_finiteType _).mpr inferInstance

private lemma tensor_id (a a' a'' b : K) (ha' : a' ≠ 0) (ha'' : a'' ≠ 0) (N : ℕ) :
    (((a ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a ^ N))) * (b ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] b) =
      ((((a / a') ^ N * b) ⊗ₜ[ℂ] ((a / a'') ^ N)) - (((a / a') ^ N) ⊗ₜ[ℂ] ((a / a'') ^ N * b))) *
        (((a' ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a'' ^ N))) := by
  have e1 : (a / a') ^ N * a' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha']
  have e2 : (a / a'') ^ N * a'' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha'']
  have e3 : (a / a') ^ N * b * a' ^ N = a ^ N * b := by rw [mul_right_comm, e1]
  have e4 : (a / a'') ^ N * b * a'' ^ N = a ^ N * b := by rw [mul_right_comm, e2]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, sub_mul, mul_sub, mul_one, one_mul, e1, e2, e3, e4]
  done

private lemma coe_XY (i j : Fin (d + 1)) (N : ℕ) :
    (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y j ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      (((algebraMap F K (x i)) ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] ((algebraMap F K (x j)) ^ N)) := by
  simp [sysZ, Units.val_pow_eq_pow_val, Algebra.TensorProduct.tmul_pow]

end

theorem UpperTheory.Gal.productCup_of_system.zFam_of :
    ZFam := by
  classical
  intro F K _ _ _ _ _ _ d x h
  choose G hG using fun i => gens (x := x) h i
  have hGm : ∀ i, ∀ b ∈ G i, b ∈ rB ℂ K (xv x) {i} := fun i b hb =>
    hG i ▸ Algebra.subset_adjoin hb
  have hP : ∀ i b, b ∈ G i → ∀ i', ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} :=
    fun i b hb i' => pow_mul_mem h i i' b (hGm i b hb)
  choose! Nb hNb using hP
  let Nq : Fin (d + 1) × K → ℕ := fun q => Finset.univ.sup (fun i' => Nb q.1 q.2 i')
  let P : Finset (Fin (d + 1) × K) :=
    Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))
  have hPm : ∀ q ∈ P, q.2 ∈ G q.1 := by
    intro q hq
    simp only [P, Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨i, _, b, hb, rfl⟩ := hq
    exact hb
  let e := P.equivFin.symm
  let zz : Fin (d + 1) × K → K ⊗[ℂ] K := fun q =>
    (((sysZ K x 0).X q.1 ^ Nq q * (sysZ K x 0).Y q.1 ^ Nq q : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) *
      (q.2 ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] q.2)
  refine ⟨P.card, fun l => (Nq (e l).1, Nq (e l).1), fun l => zz (e l).1, ⟨?_, ?_, ?_⟩⟩
  · intro i' j' l
    show zz (e l).1 * ↑((sysZ K x 0).X i' ^ Nq (e l).1 * (sysZ K x 0).Y j' ^ Nq (e l).1)⁻¹ ∈ _
    have hb := hPm _ (e l).2
    generalize (e l).1 = q at hb ⊢
    obtain ⟨i, b⟩ := q
    dsimp only [zz] at hb ⊢
    have hN1 : Nb i b i' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ i')
    have hN2 : Nb i b j' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ j')
    have hA := hNb i b hb i' _ hN1
    have hD := hNb i b hb j' _ hN2
    have hB := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) j' i) (Nq (i, b))
    have hC := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) i' i) (Nq (i, b))
    rw [coe_XY, tensor_id (algebraMap F K (x i)) (algebraMap F K (x i')) (algebraMap F K (x j')) b
      (by simp) (by simp) _, ← coe_XY i' j' _, Units.mul_inv_cancel_right]
    simp only [map_div₀] at hA hB hC hD
    exact Subalgebra.sub_mem _ ((AlgHom.mem_range _).mpr ⟨⟨_, hA⟩ ⊗ₜ ⟨_, hB⟩, by simp⟩)
      ((AlgHom.mem_range _).mpr ⟨⟨_, hC⟩ ⊗ₜ ⟨_, hD⟩, by simp⟩)
  · intro l
    simp [zz, Algebra.TensorProduct.lmul'_apply_tmul]
  · intro i
    apply le_antisymm
    · exact Algebra.adjoin_le (fun b hb => hb.1)
    · refine (hG i).symm.le.trans (Algebra.adjoin_mono ?_)
      intro b hb
      have hq : (i, b) ∈ P := by
        simp only [P, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨i, Finset.mem_univ _, b, hb, rfl⟩
      refine ⟨hGm i b hb, e.symm ⟨(i, b), hq⟩, Nq (i, b), ?_, ?_⟩ <;> simp [e, zz]
end

