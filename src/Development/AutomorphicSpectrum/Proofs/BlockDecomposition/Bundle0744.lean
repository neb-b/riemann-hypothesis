module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.FibreRed

open GlobalTheory.SmallExtLift

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}}
    {s : X ⟶ Sp R} {ι : Y ⟶ X} {f : Y ⟶ Sp (IsLocalRing.ResidueField R)}
    (w : ι ≫ s = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (U : X.Opens)
    {z : Γ(X, U)} (hz : z ∈ ext s (IsLocalRing.maximalIdeal R) U) : (ι.app U).hom z = 0 := by
  have key : Ideal.map (GlobalTheory.SmallExtLift.cst s U) (IsLocalRing.maximalIdeal R) ≤
      RingHom.ker (ι.app U).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst w U r,
      (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
  exact key hz

private theorem app_rs_eq_rs_app {X Y : Scheme.{0}} (φ : Y ⟶ X) {U W : X.Opens} (h : W ≤ U)
    (h' : φ ⁻¹ᵁ W ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.app W).hom (rs X h x) = rs Y h' ((φ.app U).hom x) := by
  have := congrArg (fun q => q.hom x) (φ.naturality (homOfLE h).op)
  exact this

theorem dep_fibre : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  intro hD R _ _ X s hs n r hnr hfib A V hV hVa b hb
  let g := spMap (algebraMap R (IsLocalRing.ResidueField R))
  let φ := pullback.fst s g
  let s' := pullback.snd s g
  have hpb : IsPullback φ s' s g := IsPullback.of_hasPullback _ _
  have hpb' : IsPullback φ s' s (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := hpb
  have hw : φ ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := hpb.w
  have hsurj : Function.Surjective (IsLocalRing.residue R) := Ideal.Quotient.mk_surjective
  obtain ⟨hfin, hrank⟩ := hfib _ s' φ hpb
  have hSp : ∀ (T : Type) [CommRing T], (Sp T).IsSeparated := fun T _ => by unfold Sp; infer_instance
  haveI hXsep : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  haveI hsep : (pullback s g).IsSeparated := ⟨by rw [← terminal.comp_from s']; infer_instance⟩
  haveI hg : IsAffineHom g := by
    show IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
    infer_instance
  haveI haff : IsAffineHom φ := MorphismProperty.pullback_fst (P := @IsAffineHom) s g hg
  let V' : A → (pullback s g).Opens := fun a => φ ⁻¹ᵁ V a
  have hV' : ⨆ a, V' a = ⊤ := by
    have h1 : ⨆ a, V' a = φ ⁻¹ᵁ (⨆ a, V a) := (TopologicalSpace.Opens.map_iSup φ.base V).symm
    rw [h1, hV]
    rfl
  have hV'a : ∀ a, IsAffineOpen (V' a) := fun a => (hVa a).preimage φ
  let α : Fin r → ∀ a c, Γ(pullback s g, V' a ⊓ V' c) := fun i a c => (φ.app (V a ⊓ V c)).hom (b i a c)
  have hα : ∀ i a c d, rs _ (le₁₂ V' a c d) (α i a c) + rs _ (le₂₃ V' a c d) (α i c d) =
      rs _ (le₁₃ V' a c d) (α i a d) := by
    intro i a c d
    have h0 := app_eq_zero_of_mem_ext hw (V a ⊓ V c ⊓ V d) (hb i a c d)
    rw [map_sub, map_add (f := _), app_rs_eq_rs_app φ (le₁₂ V a c d) (le₁₂ V' a c d),
      app_rs_eq_rs_app φ (le₂₃ V a c d) (le₂₃ V' a c d), app_rs_eq_rs_app φ (le₁₃ V a c d) (le₁₃ V' a c d)] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨c, ψ, hc0, hcψ⟩ := hD (IsLocalRing.ResidueField R) (pullback s g) s' hsep n r hfin hrank hnr A V'
    hV' hV'a α hα
  choose e he using fun i => hsurj (c i)
  choose β hβ using fun a => app_surj hsurj hpb' (hVa a) (ψ a)
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hc0
  have hlu : IsUnit (e l) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [he l]; exact hl)
  refine ⟨e, β, ⟨l, hlu⟩, fun a c' => ?_⟩
  show _ ∈ Ideal.map (cst s (V a ⊓ V c')) (IsLocalRing.maximalIdeal R)
  rw [← IsLocalRing.ker_residue]
  apply mem_of_app_eq_zero hsurj hpb' ((hVa a).inf (hVa c'))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_sub, app_rs_eq_rs_app φ inf_le_left (inf_le_left : V' a ⊓ V' c' ≤ V' a),
    app_rs_eq_rs_app φ inf_le_right (inf_le_right : V' a ⊓ V' c' ≤ V' c'), hβ, hβ]
  simp only [map_mul, app_cst hw, he]
  exact sub_eq_zero.mpr (hcψ a c')

end GlobalTheory.CompanionTheory.FewEq.FibreRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem form_mem_of_mem_smul_top {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (J : Ideal A) (φ : N →ₗ[A] A) {n : N} (h : n ∈ J • (⊤ : Submodule A N)) : φ n ∈ J := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro r hr n _
    rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add (f := _)]
    exact J.add_mem hx hy

theorem exists_step_of_sup_span {A : Type} [CommRing A] (K I : Ideal A) (S : Finset A)
    (hS : K ⊔ Ideal.span (S : Set A) = I) (hne : K ≠ I) :
    ∃ (J : Ideal A) (t : A), K ≤ J ∧ J ≠ I ∧ J ⊔ Ideal.span {t} = I := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact absurd (by simpa using hS) hne
  | insert a S' _ ih =>
    by_cases h : K ⊔ Ideal.span (S' : Set A) = I
    · exact ih h
    · refine ⟨K ⊔ Ideal.span (S' : Set A), a, le_sup_left, h, ?_⟩
      rw [← hS, Finset.coe_insert, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {a})]

theorem eq_zero_of_lift_of_mem_maximalIdeal_smul (A Q N : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N) (hL : Lift b)
    (hb : ∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) : b = 0 := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A Q).FG)
  let v := Module.finBasis A N
  let g : Fin (Module.finrank A N) × S → A := fun p ↦ v.coord p.1 (b p.2)
  let I : Ideal A := Ideal.span (Set.range g)
  have hIfg : I.FG := ⟨(Set.finite_range g).toFinset, by simp [I]⟩

  have hcoord : ∀ q i, v.coord i (b q) ∈ I := by
    intro q
    have hq : q ∈ Submodule.span A (S : Set Q) := by rw [hS]; trivial
    induction hq using Submodule.span_induction with
    | mem x hx =>
      intro i
      exact Ideal.subset_span ⟨(i, ⟨x, hx⟩), rfl⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      rw [map_add (f := _), map_add (f := _)]
      exact I.add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      rw [map_smul, map_smul, smul_eq_mul]
      exact I.mul_mem_left _ (hx i)

  have hval : ∀ q, b q ∈ I • (⊤ : Submodule A N) := by
    intro q
    rw [← v.sum_repr (b q)]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hcoord q i) trivial
  have hIm : I ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hb p.2)
  have hI : I = ⊥ := by
    by_contra hI
    set m := IsLocalRing.maximalIdeal A with hm
    have hjac : m ≤ Ideal.jacobson (⊥ : Ideal A) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hne : m * I ≠ I := by
      intro h
      exact hI (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m I hIfg
        (by rw [smul_eq_mul, h]) hjac)
    obtain ⟨T, hT⟩ := hIfg
    have hsup : m * I ⊔ Ideal.span (T : Set A) = I := by
      have hT' : Ideal.span (T : Set A) = I := hT
      rw [hT']
      exact sup_eq_right.2 (Ideal.mul_le_right : m * I ≤ I)
    obtain ⟨J, t, hKJ, hJI, hJt⟩ := exists_step_of_sup_span (m * I) I T hsup hne
    have hJle : J ≤ I := hJt ▸ le_sup_left
    have htI : t ∈ I := by
      rw [← hJt]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)
    have hJtop : J ≠ ⊤ := fun h ↦ by
      have : (1 : A) ∈ m := hIm (hJle (h ▸ Submodule.mem_top))
      exact (Ideal.ne_top_iff_one m).1 (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
    have hxt : ∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J :=
      fun x hx ↦ hKJ (Ideal.mul_mem_mul hx htI)

    have hstep : ∀ y ∈ I • (⊤ : Submodule A Q), b y ∈ J • (⊤ : Submodule A N) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr q _
        rw [map_smul]
        have h1 : r • b q ∈ I • m • (⊤ : Submodule A N) :=
          Submodule.smul_mem_smul hr (hb q)
        have h2 : I • m • (⊤ : Submodule A N) ≤ J • (⊤ : Submodule A N) := by
          rw [← Submodule.mul_smul, mul_comm]
          exact Submodule.smul_mono_left hKJ
        exact h2 h1
      · intro x y hx hy
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
    have hzJ : ∀ z, b z ∈ J • (⊤ : Submodule A N) := by
      intro z
      obtain ⟨x, hx, hxz⟩ := hL J t hJtop hxt z (by rw [hJt]; exact hval z)
      rw [hJt] at hxz
      have h := Submodule.sub_mem _ hx (hstep _ hxz)
      rwa [← map_sub, sub_sub_cancel] at h
    apply hJI
    refine le_antisymm hJle (Ideal.span_le.2 ?_)
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hzJ p.2)
  ext q
  apply v.repr.injective
  ext i
  have := hcoord q i
  rw [hI, Ideal.mem_bot] at this
  simpa using this

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverse
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem projective_of_genInverse_of_exact {S P Q T : Type} [CommRing S]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q] [Module.Projective S Q]
    [AddCommGroup T] [Module S T] (f : P →ₗ[S] Q) (g : Q →ₗ[S] T) (s : Q →ₗ[S] P)
    (hs : f ∘ₗ s ∘ₗ f = f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective S T := by
  have hker : LinearMap.ker g ≤ LinearMap.ker (LinearMap.id - f ∘ₗ s) := by
    intro q hq
    obtain ⟨p, rfl⟩ := (hex q).1 hq
    have hp : f (s (f p)) = f p := LinearMap.congr_fun hs p
    simp [LinearMap.mem_ker, hp]
  let t : T →ₗ[S] Q := (LinearMap.ker g).liftQ (LinearMap.id - f ∘ₗ s) hker ∘ₗ
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine Module.Projective.of_split t g ?_
  ext x
  obtain ⟨q, rfl⟩ := hg x
  have h1 : (g.quotKerEquivOfSurjective hg).symm (g q) = Submodule.Quotient.mk q := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, hex.apply_apply_eq_zero, sub_zero]

theorem exists_genInverse_of_forall_maximal (R A B : Type) [CommRing R] [AddCommGroup A]
    [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B]
    [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (h : ∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) :
    ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  haveI : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  haveI : Module.FinitePresentation R (B ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (LinearMap.range f).mkQ_surjective
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f)
  haveI : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl _ _).2 (TensorProduct.isBaseChange R _ _)
  haveI : Module.Projective R (B ⧸ LinearMap.range f) := by
    refine Module.projective_of_localization_maximal' (fun P _ => Localization.AtPrime P)
      (fun P _ => Localization.AtPrime P ⊗[R] (B ⧸ LinearMap.range f))
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) ?_
    intro m hm
    obtain ⟨s, hs⟩ := h m
    refine GlobalTheory.CompanionTheory.PerfVB.projective_of_genInverse_of_exact (f.baseChange (Localization.AtPrime m))
      ((LinearMap.range f).mkQ.baseChange (Localization.AtPrime m)) s hs ?_ ?_
    · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact _ (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective
    · rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective _ (LinearMap.range f).mkQ_surjective
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (LinearMap.range f).mkQ_surjective
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ : B →ₗ[R] B) b ∈
      LinearMap.range f := by
    intro b
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    have hb : (LinearMap.range f).mkQ (t ((LinearMap.range f).mkQ b)) =
        (LinearMap.range f).mkQ b := LinearMap.congr_fun ht ((LinearMap.range f).mkQ b)
    change (LinearMap.range f).mkQ (b - t ((LinearMap.range f).mkQ b)) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict (LinearMap.range f) (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ) hmem)
    f.surjective_rangeRestrict
  refine ⟨s, ?_⟩
  ext a
  have h2 : (LinearMap.range f).mkQ (f a) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f a
  have h1 : f (s (f a)) = f a - t ((LinearMap.range f).mkQ (f a)) :=
    congrArg Subtype.val (LinearMap.congr_fun hs (f a))
  rw [h2, map_zero, sub_zero] at h1
  simpa only [LinearMap.comp_apply] using h1

end GlobalTheory.CompanionTheory.PerfVB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_coeffs_of_mem_mul_span {S : Type} [CommRing S] {r : ℕ} (J : Ideal S)
    (u : Fin r → S) {w : S} (hw : w ∈ J * Ideal.span (Set.range u)) :
    ∃ a : Fin r → S, (∀ i, a i ∈ J) ∧ ∑ i, u i * a i = w := by
  have hw' : w ∈ J • Submodule.span S (Set.range u) := hw
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J u w).1 hw'
  refine ⟨a, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype _ _ (fun i => zero_smul S (u i))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mem_map_maximalIdeal_of_flat {R : Type} [CommRing R] [IsLocalRing R] {S : Type}
    [CommRing S] [Algebra R S] [Module.Flat R S] {r : ℕ} (t : Fin r → R)
    (hmin : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (y a : Fin r → S) (h : ∑ i, algebraMap R S (t i) * y i = ∑ i, algebraMap R S (t i) * a i)
    (i : Fin r) : y i - a i ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  have hrel : ∑ j, t j • (y j - a j) = 0 := by
    simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, h, sub_self]
  obtain ⟨k, d, w, hw, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S)
    (f := t) (x := fun j => y j - a j) hrel
  have hwi : y i - a i = ∑ j, d i j • w j := hw i
  rw [hwi]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  refine hmin (fun i => d i j) ?_ i
  rw [← hd j]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem minimal_generators_flat_independent :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  intro R _ _ S _ c hc r t I hI hmin y hy i
  have hmap : (IsLocalRing.maximalIdeal R * I).map c
      = (IsLocalRing.maximalIdeal R).map c * Ideal.span (Set.range fun j => c (t j)) := by
    rw [Ideal.map_mul, ← hI, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hy
  obtain ⟨a, ha, hsum⟩ := exists_coeffs_of_mem_mul_span _ _ hy
  have hmin0 : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R :=
    fun x hx => hmin x (by rw [hx]; exact Ideal.zero_mem _)
  have h3 : y i - a i ∈ (IsLocalRing.maximalIdeal R).map c := by
    letI := c.toAlgebra
    haveI : Module.Flat R S := hc
    exact mem_map_maximalIdeal_of_flat t hmin0 y a hsum.symm i
  have h4 := Ideal.add_mem _ h3 (ha i)
  rwa [sub_add_cancel] at h4

end GlobalTheory.CompanionTheory.FewEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsLocalIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_fin_span_eq_of_unit_coeff {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (t : Fin (n + 1) → R)
    (ht : Ideal.span (Set.range t) = I) (x : Fin (n + 1) → R)
    (hx : ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I) (l : Fin (n + 1))
    (hu : IsUnit (x l)) : ∃ s : Fin n → R, Ideal.span (Set.range s) = I := by
  refine ⟨fun j => t (l.succAbove j), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← ht]
    exact Ideal.subset_span ⟨_, rfl⟩
  set N : Ideal R := Ideal.span (Set.range fun j => t (l.succAbove j)) with hN
  have hmem : ∀ j, t (l.succAbove j) ∈ N := fun j => Ideal.subset_span ⟨j, rfl⟩
  have htl : t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
    obtain ⟨u, hu⟩ := hu
    have hsum : x l * t l = ∑ i, x i * t i - ∑ j, x (l.succAbove j) * t (l.succAbove j) := by
      rw [Fin.sum_univ_succAbove _ l]
      ring
    have h1 : x l * t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
      rw [hsum]
      refine Ideal.sub_mem _ (Ideal.mem_sup_right (by simpa [smul_eq_mul] using hx)) ?_
      exact Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j))
    have h2 : t l = (↑u⁻¹ : R) * (x l * t l) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  have hle : I ≤ N ⊔ IsLocalRing.maximalIdeal R • I := by
    conv_lhs => rw [← ht]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l i with h | ⟨j, h⟩
    · rw [h]; exact htl
    · rw [h]; exact Ideal.mem_sup_left (hmem j)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle

theorem exists_minimal_generators : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ (r : ℕ) (t : Fin r → R), Ideal.span (Set.range t) = I ∧
      ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
  intro R _ _ _ I
  classical
  have hex : ∃ r : ℕ, ∃ t : Fin r → R, Ideal.span (Set.range t) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  refine ⟨_, t, ht, fun x hx l => ?_⟩
  by_contra hl
  have hu : IsUnit (x l) := by
    by_contra h
    exact hl ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hmin : ∀ m : ℕ, (∃ s : Fin m → R, Ideal.span (Set.range s) = I) → Nat.find hex ≤ m :=
    fun m h => Nat.find_min' hex h
  generalize Nat.find hex = r at t ht x hx l hu hmin
  cases r with
  | zero => exact l.elim0
  | succ n =>
    have := hmin n (exists_fin_span_eq_of_unit_coeff I t ht x hx l hu)
    omega

end GlobalTheory.CompanionTheory.FewEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTrivialityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_locus_represents_triviality : ∀ {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left), N.IsLB → ∀ (i : Z ⟶ Y), PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i → ∀ (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left), Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  first | exact @GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | exact GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | (intros; apply GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff <;> assumption)
end

