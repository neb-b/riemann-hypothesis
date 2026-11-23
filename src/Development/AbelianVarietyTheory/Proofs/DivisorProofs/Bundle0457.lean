module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_upwardFamily_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Van1 (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t₀ Sg hSg hcovT
  classical
  intro y hy

  let Q : C' → Prop := fun t ↦ ∃ a : t₀ ⟶ t, Sg t a
  have hQ : ∀ t t', Q t → (t ⟶ t') → Q t' := fun t t' ⟨a, ha⟩ b ↦ ⟨a ≫ b, hSg t t' a b ha⟩

  let yb : ∀ t t' : C', F.obj (G.obj t') := fun t t' ↦
    if h : Q t ∧ Nonempty (t ⟶ t') then y t t' h.1.choose h.2.some else 0
  have hyb : ∀ t t' (u : t₀ ⟶ t) (a : t ⟶ t'), Sg t u → y t t' u a = yb t t' := by
    intro t t' u a hu
    have h : Q t ∧ Nonempty (t ⟶ t') := ⟨⟨u, hu⟩, ⟨a⟩⟩
    simp only [yb, dif_pos h]
    exact congrArg₂ (y t t') (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hyc : ∀ t t' t'', Q t → ∀ (a : t ⟶ t') (b : t' ⟶ t''),
      yb t t'' = mp F (G.map b) (yb t t') + yb t' t'' := by
    rintro t t' t'' ⟨u, hu⟩ a b
    rw [← hyb t t'' u (a ≫ b) hu, ← hyb t t' u a hu, ← hyb t' t'' (u ≫ a) b (hSg t t' u a hu)]
    exact hy t t' t'' u a b hu

  obtain ⟨n, b, hb, hcT⟩ := hcovT
  have hpt : ∀ i : Fin n, ∃ p : C', Q p ∧ ∀ S (u : G.obj t₀ ⟶ S),
      IsUnit (mp F u (b i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H (G.obj t₀) (b i)
    obtain ⟨p, a, ha, ⟨w⟩⟩ := hcT i T' l hl
    exact ⟨p, ⟨a, ha⟩, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p hpQ hp using hpt

  have hc0 : ∀ i j : Fin n, ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj (p i) ⟶ S) →
      Nonempty (G.obj (p j) ⟶ S) → ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (p i ⟶ t) →
        Nonempty (p j ⟶ t) → mp F ψ (x S) = mp F w (yb (p j) t - yb (p i) t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj (p i) ⟶ S) → Nonempty (G.obj (p j) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i j
    refine exists_glue_points F G H hdir (p i) (p j) _ fun t t' a ⟨ai⟩ ⟨aj⟩ ↦ ?_
    rw [map_sub, hyc (p j) t t' (hpQ j) aj a, hyc (p i) t t' (hpQ i) ai a]
    ring
  choose c hc hc' using hc0
  have hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j)))
      (fun S (_ : G.obj t₀ ⟶ S) ↦ c i j S) := fun i j S S' u ψ h ↦
    hc' i j S S' ψ (hp i S u h.1) (hp j S u h.2)
  have hcc : ∀ i j k S (u : G.obj t₀ ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c j k S - c i k S + c i j S = 0 := by
    intro i j k S u hi hj hk
    refine eq_zero_of_local₃ F G H hdir (hp i S u hi) (hp j S u hj) (hp k S u hk) _
      fun t S' ψ ai aj ak ⟨w⟩ ↦ ?_
    rw [map_add (f := _), map_sub, hc j k S (hp j S u hj) (hp k S u hk) t S' ψ w aj ak,
      hc i k S (hp i S u hi) (hp k S u hk) t S' ψ w ai ak,
      hc i j S (hp i S u hi) (hp j S u hj) t S' ψ w ai aj]
    simp only [map_sub]
    ring
  obtain ⟨e, he, he'⟩ := Desc.cech1 H hb (fun i j S (_ : G.obj t₀ ⟶ S) ↦ c i j S) hs hcc
  have he'' : ∀ i j S (u : G.obj t₀ ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      c i j S = e j S u - e i S u := he'

  have hX0 : ∀ i (t : C') (_ : Q t), ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t ⟶ S) →
      Nonempty (G.obj (p i) ⟶ S) → ∀ t' S' (ψ : S ⟶ S') (w : G.obj t' ⟶ S'), Nonempty (t ⟶ t') →
        Nonempty (p i ⟶ t') → mp F ψ (x S) = mp F w (yb (p i) t' - yb t t')) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t ⟶ S) → Nonempty (G.obj (p i) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i t ht
    refine exists_glue_points F G H hdir t (p i) _ fun t' t'' a ⟨a0⟩ ⟨ai⟩ ↦ ?_
    rw [map_sub, hyc (p i) t' t'' (hpQ i) ai a, hyc t t' t'' ht a0 a]
    ring
  choose X hX hX' using hX0

  have indep : ∀ t (ht : Q t) (u : G.obj t₀ ⟶ G.obj t) S (ψ : G.obj t ⟶ S) i j,
      IsUnit (mp F (u ≫ ψ) (b i)) → IsUnit (mp F (u ≫ ψ) (b j)) →
      X i t ht S - e i S (u ≫ ψ) = X j t ht S - e j S (u ≫ ψ) := by
    intro t ht u S ψ i j hi hj
    have key : X i t ht S - X j t ht S + c i j S = 0 :=
      eq_zero_of_local₃ F G H hdir ⟨ψ⟩ (hp i S _ hi) (hp j S _ hj) _ fun t' S' χ a0 ai aj ⟨w⟩ ↦ by
        rw [map_add (f := _), map_sub, hX i t ht S ⟨ψ⟩ (hp i S _ hi) t' S' χ w a0 ai,
          hX j t ht S ⟨ψ⟩ (hp j S _ hj) t' S' χ w a0 aj,
          hc i j S (hp i S _ hi) (hp j S _ hj) t' S' χ w ai aj]
        simp only [map_sub]
        ring
    linear_combination key - he'' i j S (u ≫ ψ) hi hj

  have hg0 : ∀ t (ht : Q t) (u : G.obj t₀ ⟶ G.obj t), ∃ x : F.obj (G.obj t), ∀ S (ψ : G.obj t ⟶ S) i,
      IsUnit (mp F (u ≫ ψ) (b i)) → mp F ψ x = X i t ht S - e i S (u ≫ ψ) := by
    intro t ht u
    let σ : ∀ S, (G.obj t ⟶ S) → F.obj S := fun S ψ ↦
      if h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) then X h.choose t ht S - e h.choose S (u ≫ ψ) else 0
    have hσ : ∀ S ψ i, IsUnit (mp F (u ≫ ψ) (b i)) → σ S ψ = X i t ht S - e i S (u ≫ ψ) := by
      intro S ψ i hi
      have h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := ⟨i, hi⟩
      simp only [σ, dif_pos h]
      exact indep t ht u S ψ _ i h.choose_spec hi
    obtain ⟨x, hx⟩ := glue_std H (span_map_eq_top F u hb) σ fun S S' ψ χ ⟨i, hi⟩ ↦ by
      have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
      have hi'' : IsUnit (mp F (u ≫ ψ ≫ χ) (b i)) := by
        rw [← Category.assoc, mp_comp]; exact hi'.map _
      rw [hσ S' (ψ ≫ χ) i hi'', hσ S ψ i hi', map_sub, ← hX' i t ht S S' χ ⟨ψ⟩ (hp i S _ hi'),
        ← he i S S' (u ≫ ψ) χ hi', Category.assoc]
    exact ⟨x, fun S ψ i hi ↦ by
      rw [hx S ψ ⟨i, by rw [mp_comp] at hi; exact hi⟩, hσ S ψ i hi]⟩
  choose g hg using hg0
  refine ⟨fun t' a ↦ if h : Sg t' a then g t' ⟨a, h⟩ (G.map a) else 0, fun t t' u a hu ↦ ?_⟩
  have hu' : Sg t' (u ≫ a) := hSg t t' u a hu
  have ht : Q t := ⟨u, hu⟩
  have ht' : Q t' := ⟨u ≫ a, hu'⟩
  dsimp only
  rw [dif_pos hu', dif_pos hu, G.map_comp]
  change g t' ht' (G.map u ≫ G.map a) - mp F (G.map a) (g t ht (G.map u)) = y t t' u a
  rw [hyb t t' u a hu]
  refine sub_eq_zero.1 (sep_std H (span_map_eq_top F (G.map u ≫ G.map a) hb) _ fun S χ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F ((G.map u ≫ G.map a) ≫ χ) (b i)) := by rw [mp_comp]; exact hi
  have hi'' : IsUnit (mp F (G.map u ≫ G.map a ≫ χ) (b i)) := by rw [← Category.assoc]; exact hi'
  rw [map_sub, map_sub, hg t' ht' (G.map u ≫ G.map a) S χ i hi', ← mp_comp,
    hg t ht (G.map u) S (G.map a ≫ χ) i hi'', Category.assoc]
  have key : X i t' ht' S - X i t ht S - mp F χ (yb t t') = 0 :=
    eq_zero_of_local F G H hdir ⟨χ⟩ (hp i S _ hi') _ fun t'' S' ψ ⟨a'⟩ ai ⟨w⟩ ↦ by
      rw [map_sub, map_sub, hX i t' ht' S ⟨χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a'⟩ ai,
        hX i t ht S ⟨G.map a ≫ χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a ≫ a'⟩ ai, ← mp_comp,
        (Subsingleton.elim _ _ : χ ≫ ψ = G.map a' ≫ w), mp_comp, hyc t t' t'' ht a a']
      simp only [map_sub, map_add (f := _)]
      ring
  linear_combination key

end GlobalTheory.CatCoh.Desc.Basis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem secMap_secRes_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem secRes_secRes {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom x) = (F.obj.map (k ≫ g).op).hom x
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]

theorem classes_die_on_etale_cover : A5 := by
  intro R _ X F n hn x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hsch := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by omega) rfl
  have hres := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X
  set z := ev α.1 0 n (by simp) X (𝟙 X) with hz
  have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := (hsch.2 α).1
  have hloc := hres.2.2.1 (n - 1) n (n + 1) hn (by omega) z rfl hdz
  rw [loc_iff_etale_affine_points] at hloc
  swap
  · rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [secMap_secRes_comm, hy, secRes_secRes]
  choose V g _ hg hmem y hy using hloc
  let f : (∐ V) ⟶ X := Sigma.desc g
  have hιf : ∀ i, Sigma.ι V i ≫ f = g i := fun i => Sigma.ι_desc g i
  refine ⟨∐ V, f, ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hg
  · refine ⟨fun p => ?_⟩
    obtain ⟨q, hq⟩ := hmem p
    refine ⟨Sigma.ι V p q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιf, hq]
  · obtain ⟨a, ha⟩ := (sec_sigma_bijective R ((res R F).X (n - 1)) V).2 y
    have hda : Sec.map ((res R F).d (n - 1) n) a = Sec.res f z := by
      apply (sec_sigma_bijective R ((res R F).X n) V).1
      funext i
      have hai : Sec.res (Sigma.ι V i) a = y i := congrFun ha i
      change Sec.res (Sigma.ι V i) (Sec.map _ a) = Sec.res (Sigma.ι V i) (Sec.res f z)
      rw [← secMap_secRes_comm, hai, hy, secRes_secRes, hιf]
    have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (∐ V) (res R F) (n - 1) n (n + 1) (by omega) rfl
    have hev := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := n)
    let α' : Cocycle ((chains R).obj (sch.obj (∐ V))) (res R F) n :=
      zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)
    change CohomologyClass.mk α' = 0
    rw [(hY.2 α').2]
    refine ⟨a, ?_⟩
    rw [hda]
    have h1 := (hev.2.2.2.1 (sch.map f) α.1 0 n (by simp) (∐ V) (𝟙 (∐ V)))
    have h2 := (hev.2.1 α.1 0 n (by simp) (∐ V) X f (𝟙 X))
    change _ = ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ (∐ V) (𝟙 (∐ V))
    rw [h1, hz, h2]
    rfl

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

lemma isIso_mapCechNerve_app_of_mono {A B C : PSh} (π : A ⟶ B) (ι : B ⟶ C) [Mono ι] (φ : A ⟶ C)
    (h : π ≫ ι = φ) (n : SimplexCategoryᵒᵖ) :
    IsIso ((Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp [h]) : Arrow.mk π ⟶ Arrow.mk φ)).app n) := by
  subst h
  have e : (Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp) : Arrow.mk π ⟶ Arrow.mk (π ≫ ι))).app n =
      WidePullback.lift (WidePullback.base (fun _ : Fin (n.unop.len + 1) => π) ≫ ι)
        (fun i => WidePullback.π (fun _ : Fin (n.unop.len + 1) => π) i)
        (fun j => by
          show _ ≫ (π ≫ ι) = _
          rw [← Category.assoc, WidePullback.π_arrow]) := by
    apply WidePullback.hom_ext
    · intro j
      erw [WidePullback.lift_π]
    · erw [WidePullback.lift_base]
  rw [e]
  refine ⟨WidePullback.lift (WidePullback.π _ 0 ≫ π) (fun i => WidePullback.π _ i) ?_, ?_, ?_⟩
  · intro i
    rw [← cancel_mono ι]
    simp only [Category.assoc]
    exact (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) i).trans
      (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0).symm
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_π]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π) 0
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_base]
      rw [Category.assoc]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_locSurj (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q)
    (hφ : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) :
    QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
      (Arrow.mk φ).augmentedCechNerve.hom)) := by
  let aφ : (Arrow.mk φ).cechNerve ⟶ disc.obj Q := (Arrow.mk φ).augmentedCechNerve.hom
  change QuasiIso ((chains R).map aφ)
  have hπι : Subfunctor.toRange φ ≫ (Subfunctor.range φ).ι = φ := Subfunctor.toRange_ι φ
  set π := Subfunctor.toRange φ with hπ
  set ι := (Subfunctor.range φ).ι with hι
  let F : Arrow.mk π ⟶ Arrow.mk φ := Arrow.homMk (𝟙 P) ι (by simp [hπι])
  let aπ : (Arrow.mk π).cechNerve ⟶ disc.obj _ := (Arrow.mk π).augmentedCechNerve.hom
  have sq : Arrow.mapCechNerve F ≫ aφ = aπ ≫ disc.map ι := by
    ext n : 1
    erw [NatTrans.comp_app, NatTrans.comp_app]
    erw [Arrow.augmentedCechNerve_hom_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
    rfl
  have hsurj : ∀ U, Function.Surjective (π.app U) := fun U =>
    (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 (inferInstance : Epi π) U)
  have h1 : QuasiIso ((chains R).map aπ) := GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R π hsurj
  have hιfree : IsIso ((free R).map ι) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R ι).2.2 ?_ ?_
    · intro U y
      exact GlobalTheory.EtC.loc_calculus.2.1 U _ _ (hφ U y) fun V g ⟨x, hx⟩ => ⟨π.app (op V) x, hx⟩
    · intro U x x' hxx
      have : x = x' := Subtype.ext hxx
      subst this
      exact GlobalTheory.EtC.loc_calculus.1 U _ fun _ _ => rfl
  have h2 : IsIso ((chains R).map (disc.map ι)) :=
    isIso_chains_map_of_isIso_free R _ fun n => hιfree
  have h3 : IsIso ((chains R).map (Arrow.mapCechNerve F)) :=
    isIso_chains_map_of_isIso_free R _ fun n => by
      have := isIso_mapCechNerve_app_of_mono π ι φ hπι n
      exact Functor.map_isIso _ _
  have key : (chains R).map (Arrow.mapCechNerve F) ≫ (chains R).map aφ =
      (chains R).map aπ ≫ (chains R).map (disc.map ι) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq]
  rw [← quasiIso_iff_comp_left ((chains R).map (Arrow.mapCechNerve F)), key]
  haveI := h1
  haveI := h2
  have h2' : QuasiIso ((chains R).map (disc.map ι)) := inferInstance
  exact quasiIso_comp ((chains R).map aπ) ((chains R).map (disc.map ι)) (hφ := h1) (hφ' := h2')

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ExtQis

theorem quasiIso_of_mappingCone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone (Q : ℕ) [NeZero Q] (F : Shv (ZMod Q)) (hF : FlatS F) (n : ℤ) :
    FlatS ((mappingCone (resAug F)).X n) := by
  obtain ⟨hiso, hzero⟩ := _root_.GlobalTheory.EtC.flatS_iso_and_zero (ZMod Q)
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resAug F) n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ ?_)
  · by_cases h : n + 1 = 0
    · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
    · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · haveI : Injective ((res (ZMod Q) F).X n) :=
      (inferInstance : Injective ((injectiveResolution F).cochainComplex.X n))
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf Q _).2

theorem quasiIso_extAug : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ),
    QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  intro Q q _ hq i
  have hq' : QuasiIso (resAug (tw Q i)) := (inferInstance : QuasiIso (injectiveResolution (tw Q i)).ι')
  have hK : (mappingCone (resAug (tw Q i))).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  haveI : (res (ZMod Q) (tw Q i)).IsStrictlyGE 0 :=
    (inferInstance : (injectiveResolution (tw Q i)).cochainComplex.IsStrictlyGE 0)
  haveI : (mappingCone (resAug (tw Q i))).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  have hE := _root_.GlobalTheory.EtC.flatExtAcyc.main Q q hq (mappingCone (resAug (tw Q i))) (-1)
    (flatS_cone Q (tw Q i) (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q i)) hK
  have hC : (mappingCone (((extSh (ZMod.castHom hq (ZMod q))).mapHomologicalComplex _).map
      (resAug (tw Q i)))).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso (resAug (tw Q i))
      (extSh (ZMod.castHom hq (ZMod q))))
  have h1 := quasiIso_of_mappingCone_acyclic _ hC
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)) := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end GlobalTheory.EtC.ExtQis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
section
namespace GlobalTheory.IntFiniteTypeDim

theorem exists_natPrime_mem_of_isMaximal (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  letI := Ideal.Quotient.field m
  have hfin : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  rcases CharP.char_is_prime_or_zero (A ⧸ m) p with h | h
  · refine ⟨p, h, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · subst h
    haveI : CharZero (A ⧸ m) := CharP.charP_to_charZero _
    exfalso
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) :=
      RingHom.injective_int _
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (A ⧸ m)))

theorem ringKrullDim_quotient_le_of_minimalPrimes {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := s.head.1.asIdeal) s.head.2
  refine le_trans ?_ (h P hP)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) P) :=
    ⟨s.length, fun i => ⟨(s i).1, hle.trans (show s.head.1 ≤ (s i).1 from s.head_le i)⟩,
      fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

theorem ringKrullDim_eq_trdeg_add_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by
  intro A _ _ _ hinj
  haveI : CharZero A := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ℤ) (S := A))
  have hrhs : ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) =
      (d : WithBot ℕ∞) + 1 := by
    rw [hd, Cardinal.toENat_nat]; rfl
  rw [hrhs]
  apply le_antisymm
  · refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm => ?_
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    refine (Ideal.height_le_ringKrullDim_quotient_add_one hlm).trans ?_
    gcongr
    refine ringKrullDim_quotient_le_of_minimalPrimes _ _ fun q hq => ?_
    haveI := hq.1.1
    exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd).le
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {(l : A)}) (J := m)
      ((Ideal.span_singleton_le_iff_mem _).mpr hlm)
    haveI := hq.1.1
    rw [← ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd]
    have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      (r := (l : A)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hl.ne_zero))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hlq)

end GlobalTheory.IntFiniteTypeDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  first | (exact @GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (exact GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (intros; apply GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.tw_mul_locSurj) | (exact GlobalTheory.EtC.tw_mul_locSurj) | (intros; apply GlobalTheory.EtC.tw_mul_locSurj  <;> assumption)
end

