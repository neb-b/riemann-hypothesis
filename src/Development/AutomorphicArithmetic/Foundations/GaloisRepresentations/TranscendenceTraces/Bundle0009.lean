module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtDegConst
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtDegConst_of :
    PtEx → WtDegConst := by
  intro _ Z S p _ _ w hw
  obtain ⟨ψ, hψ, hsum⟩ := hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)
  have hψ' : IsLocallyConstant (fun s : S => ψ s) := hψ
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨ψ s₀, ?_⟩
    funext Ω _ _ x
    have h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1 := hsum Ω x
    simp only [Category.comp_id, mul_one] at h
    show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀
    have hc : ψ (pt x) = ψ s₀ := hψ'.apply_eq_of_preconnectedSpace (pt x) s₀
    rw [← hc]
    exact h.symm
  · refine ⟨0, ?_⟩
    funext Ω _ _ x
    exact (hS ⟨pt x⟩).elim
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtExt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fsum_single {α : Type*} (s : Set α) (f : α → ℤ) (a : α) (ha : a ∈ s)
    (h : ∀ x ∈ s, f x ≠ 0 → x = a) : ∑ᶠ x ∈ s, f x = f a := by
  classical
  rw [finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), f x) a]
  · simp [ha]
  · intro x hx
    by_cases hs : x ∈ s
    · have h0 : f x = 0 := by
        by_contra h0
        exact hx (h x hs h0)
      simp [h0]
    · simp [hs]

private theorem discrete_of_chart (hChart : Chart) {V : Scheme.{0}} (Ω : Type) [Field Ω] (r : V ⟶ gp Ω) [IsFinite r] :
    DiscreteTopology V := by
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hChart r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : DiscreteTopology (Spec (CommRingCat.of B)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum B))
  exact (Scheme.homeoOfIso (asIso v)).symm.isEmbedding.discreteTopology

theorem UpperTheory.Gal.TranscendenceTraces.wtExt_of :
    PtOne → Chart → WtExt := by
  intro hOne hChart Z S p _ w hw Ω L _ _ _ _ z a
  classical
  haveI hr : IsFinite (pullback.snd p (z ≫ p)) := Sq.finite (Sq.of p (z ≫ p))
  haveI := discrete_of_chart hChart Ω (pullback.snd p (z ≫ p))
  let z0 : gp Ω ⟶ pullback p (z ≫ p) := pullback.lift z (𝟙 _) (by simp)
  have hf : z0 ≫ pullback.fst p (z ≫ p) = z := pullback.lift_fst _ _ _
  have hs : z0 ≫ pullback.snd p (z ≫ p) = 𝟙 _ := pullback.lift_snd _ _ _
  let φ : (pullback p (z ≫ p) : Scheme.{0}) → ℤ := fun y => if y = pt z0 then 1 else 0
  obtain ⟨ψ, -, hψ⟩ := hw (Sq.of p (z ≫ p)) φ (IsLocallyConstant.of_discrete φ)
  have h1 : ψ (pt (𝟙 (gp Ω))) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ Ω (𝟙 _)
  have h2 : ψ (pt a) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ L a
  have hpt : pt (a ≫ z0) = pt z0 := by rw [pt_comp, pt_eq]
  have hφ : φ (pt z0) = 1 := if_pos rfl
  have hne : ∀ y : (pullback p (z ≫ p) : Scheme.{0}), φ y ≠ 0 → y = pt z0 := by
    intro y hy
    by_contra h
    exact hy (if_neg h)
  have e1 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w Ω z := by
    rw [fsum_single _ _ z0 hs, hf, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) Ω (𝟙 _) y z0 hy hs (hne _ (right_ne_zero_of_mul h0))
  have hs' : (a ≫ z0) ≫ pullback.snd p (z ≫ p) = a := by
    rw [Category.assoc, hs, Category.comp_id]
  have e2 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w L (a ≫ z) := by
    rw [fsum_single _ _ (a ≫ z0) hs', Category.assoc, hf, hpt, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) L a y (a ≫ z0) hy hs'
      ((hne _ (right_ne_zero_of_mul h0)).trans hpt.symm)
  have hU : pt a = pt (𝟙 (gp Ω)) := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  rw [← e2, ← e1, ← h2, ← h1]
  exact congrArg ψ hU
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtFlat_of :
    WtClopen → MultSum → MultBC → MultOpen → WtFlat := by
  intro hC hS hB hO Z S p _ _ _
  refine hC p (mult p) fun A W hW => ?_
  have : IsFinite A.r := A.finite
  have : Flat A.r := MorphismProperty.of_isPullback A.pb ‹_›
  have : LocallyOfFinitePresentation A.r := MorphismProperty.of_isPullback A.pb ‹_›
  let O : A.V.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)
  have hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι := hO O.ι A.r
  have hm' : mult A.r = (mult p).comap A.v := hB A.v A.r p A.u A.pb
  refine ⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩
  · exact (Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _
  · intro Ω _ _ x
    have h1 := hS (O.ι ≫ A.r) Ω x
    refine h1.symm.trans ?_
    change ∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _
    refine finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · change (z ≫ O.ι) ≫ A.r = x
        rw [Category.assoc]; exact hz
      · change pt (z ≫ O.ι) ∈ W
        rw [pt_comp]; exact (pt z).2
    · intro z _ z' _ e
      exact (cancel_mono O.ι).1 e
    · rintro z ⟨hz, hzW⟩
      have hr : Set.range z ⊆ Set.range O.ι := by
        rw [O.range_ι]
        rintro _ ⟨t, rfl⟩
        rw [pt_eq]; exact hzW
      refine ⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
      change _ ≫ O.ι ≫ A.r = x
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hz
    · intro z _
      rw [hm, hm']
      simp [Wt.comap]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLin
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLin_of :
    FibFin → WtLin := by
  intro hF
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' h1 h2
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    obtain ⟨ψ2, hψ2, e2⟩ := h2 A φ hφ
    refine ⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩
    intro Ω _ _ x
    haveI := A.finite
    have hfin := hF A.r Ω x
    rw [Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = (w Ω _ + w' Ω _) * _
    ring
  · intro Z S p _ d w h1
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    refine ⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩
    intro Ω _ _ x
    rw [Function.comp_apply, e1, mul_finsum_mem]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = d * w Ω _ * _
    ring
  · intro Z S p _ d
    unfold IsWt
    intro A φ hφ
    haveI : IsIso A.r := by
      rw [← A.pb.isoPullback_hom_snd]
      infer_instance
    refine ⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩
    intro Ω _ _ x
    have hs : fib A.r x = {x ≫ inv A.r} := by
      ext z
      show z ≫ A.r = x ↔ z = x ≫ inv A.r
      constructor
      · rintro rfl
        simp
      · rintro rfl
        simp
    rw [hs, finsum_mem_singleton, pt_comp]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLocal
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLocal_of :
    WtCrit → WtLocal := by
  intro hcrit Z S p w hloc
  apply hcrit p w
  intro B φ hφ b
  obtain ⟨A, hAo, ⟨a, ha⟩, hA⟩ := hloc (B.u b)
  obtain ⟨W, f1, f2, hW, hf1, c0, hc0⟩ : ∃ (W : Scheme) (f1 : W ⟶ B.U) (f2 : W ⟶ A.U),
      IsPullback f1 f2 B.u A.u ∧ IsOpenImmersion f1 ∧ ∃ c0, f1 c0 = b := by
    obtain ⟨c0, hc0, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := B.u) (g := A.u) b a ha.symm
    exact ⟨_, _, _, IsPullback.of_hasPullback B.u A.u, inferInstance, c0, hc0⟩
  obtain ⟨V', q1, q2, hq⟩ : ∃ (V' : Scheme) (q1 : V' ⟶ A.V) (q2 : V' ⟶ W),
      IsPullback q1 q2 A.r f2 :=
    ⟨_, _, _, IsPullback.of_hasPullback A.r f2⟩
  have hcomm : (q1 ≫ A.v) ≫ p = (q2 ≫ f1) ≫ B.u := by
    simp only [Category.assoc]
    rw [A.pb.w, ← Category.assoc, hq.w, Category.assoc, hW.w]
  obtain ⟨g, hg1, hg2⟩ : ∃ g : V' ⟶ B.V, g ≫ B.v = q1 ≫ A.v ∧ g ≫ B.r = q2 ≫ f1 :=
    ⟨B.pb.lift _ _ hcomm, B.pb.lift_fst _ _ _, B.pb.lift_snd _ _ _⟩
  have hsq : IsPullback g q2 B.r f1 := by
    refine IsPullback.of_right ?_ hg2 B.pb
    rw [hg1, hW.w]
    exact hq.paste_horiz A.pb
  obtain ⟨ψ, hψ, hψs⟩ :=
    hA ⟨W, V', f2, q1, q2, hq⟩ (fun y => φ (g y)) (hφ.comp_continuous g.continuous)
  refine ⟨f1 '' {y | ψ y = ψ c0}, ψ c0, f1.isOpenEmbedding.isOpenMap _ (hψ.isOpen_fiber _),
    ⟨c0, rfl, hc0⟩, ?_⟩
  rintro Ω _ _ x ⟨y, hy, hyx⟩
  have hr : Set.range x ⊆ Set.range f1 := by
    rintro _ ⟨t, rfl⟩
    exact ⟨y, hyx.trans (pt_eq x t).symm⟩
  have hx' : IsOpenImmersion.lift f1 x hr ≫ f1 = x := IsOpenImmersion.lift_fac _ _ _
  have hpt : pt (IsOpenImmersion.lift f1 x hr) = y := by
    apply f1.isOpenEmbedding.injective
    rw [← pt_comp, hx', hyx]
  have hs := hψs Ω (IsOpenImmersion.lift f1 x hr)
  rw [hpt, show ψ y = ψ c0 from hy] at hs
  rw [hs]
  symm
  have hb := fib_bijOn hsq (IsOpenImmersion.lift f1 x hr)
  rw [hx'] at hb
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ g) hb ?_
  intro z _
  simp only [Wt.comap, pt_comp, Category.assoc, hg1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtNormal
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dite_eq_left h]
  exact h.choose_spec
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtPush
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem sum_up {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∑ᶠ a ∈ s, (ULift.up.{1} (f a)) = ULift.up.{1} (∑ᶠ a ∈ s, f a) :=
  ((AddEquiv.ulift (α := ℤ)).symm.map_finsum_mem f hs).symm

theorem UpperTheory.Gal.TranscendenceTraces.wtPush_of :
    SumComp → FibFin → WtPush := by
  intro hS hF Z Z' S h p _ _ w hw A φ hφ
  let B : Sq (h ≫ p) :=
    ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
      IsPullback.paste_vert (IsPullback.of_hasPullback h A.v) A.pb⟩
  haveI : IsFinite A.r := Sq.finite A
  have hφ' : IsLocallyConstant (φ ∘ (pullback.snd h A.v)) :=
    hφ.comp_continuous (Scheme.Hom.continuous _)
  obtain ⟨ψ, hψ, hψeq⟩ := hw B (φ ∘ (pullback.snd h A.v)) hφ'
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [hψeq Ω x]
  apply (ULift.up_injective : Function.Injective (ULift.up.{1, 0} : ℤ → ULift.{1} ℤ))
  have step1 : ∀ q : gp Ω ⟶ pullback h A.v,
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)
        = w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v)) := by
    intro q
    simp only [Function.comp_apply, pt_comp]
    rfl
  change ULift.up (∑ᶠ (q : gp Ω ⟶ pullback h A.v) (_ : q ∈ fib (pullback.snd h A.v ≫ A.r) x),
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)) = _
  simp only [step1]
  rw [← sum_up (hF _ Ω x)]
  rw [hS (pullback.snd h A.v) A.r Ω x (ULift.{1} ℤ)
    (fun q => ULift.up (w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v))))]
  rw [← sum_up (hF A.r Ω x)]
  apply finsum_mem_congr rfl
  intro y hy
  rw [sum_up (hF _ Ω y)]
  congr 1
  unfold Wt.push
  rw [finsum_mem_mul]
  apply finsum_mem_eq_of_bijOn (fun q => q ≫ pullback.fst h A.v)
    (fib_bijOn (IsPullback.of_hasPullback h A.v) y)
  intro q hq
  simp only [fib, Set.mem_setOf_eq] at hq
  rw [hq]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtUnique
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtUnique_of :
    WtVanish → WtLin → WtUnique := by
  intro hV hL Z S p _ w w' hw hw' D hD hagree
  have hdiff : IsWt p (w.add (Wt.smul (-1) w')) := hL.1 p w _ hw (hL.2.1 p (-1) w' hw')
  have h0 := hV p _ hdiff D hD (by
    intro Ω _ _ z hz
    show w Ω z + (-1) * w' Ω z = 0
    rw [hagree Ω z hz]
    ring)
  funext Ω _ _ z
  have h := congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z
  change w Ω z + (-1) * w' Ω z = 0 at h
  linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtVanish
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtVanish_of :
    Isolate → WtPt → PtEx → PtLift → FibFin → WtVanish := by
  intro hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero
  funext Ω _ _ z
  show w Ω z = 0
  obtain ⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩ := hIso p (pt z)
  haveI : IsFinite A.r := A.finite
  classical
  let φ : A.V → ℤ := fun y => if y ∈ W then 1 else 0
  have hφ : IsLocallyConstant φ := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
    intro n
    by_cases h1 : n = 1
    · subst h1
      convert hW.isOpen using 1
      ext y
      by_cases hy : y ∈ W <;> simp [φ, hy]
    · by_cases h0 : n = 0
      · subst h0
        convert hW.compl.isOpen using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy]
      · convert isOpen_empty using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega
  obtain ⟨ψ, hψ, hψeq⟩ := hw A φ hφ
  have hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    rw [← hx1, hψeq Ω1 x1, mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro z' hz'
    have hz'' : z' ≫ A.r = x1 := hz'
    by_cases hW' : pt z' ∈ W
    · have hr : A.r (pt z') = A.r v := by
        rw [← pt_comp, hz'']
        exact hx1
      have hv : pt z' = v := huniq _ hW' hr
      have hwz : w Ω1 (z' ≫ A.v) = w Ω z :=
        hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])
      simp [φ, hW', hwz]
    · simp [φ, hW']
  have hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    obtain ⟨z1, hz1, hpz1⟩ := hLift A.r Ω1 x1 v hx1.symm
    have hf := hFin A.r Ω1 x1
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have hmem : z1 ∈ hf.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hz1
    calc (0:ℤ) < φ (pt z1) := by simp [φ, hpz1, hvW]
      _ ≤ _ := Finset.single_le_sum (f := fun z' => φ (pt z'))
          (fun i _ => by by_cases hi : pt i ∈ W <;> simp [φ, hi]) hmem
  obtain ⟨Ω0, _, _, x0, hx0⟩ := hEx A.U (A.r v)
  have hO : IsOpen (ψ ⁻¹' {ψ (A.r v)}) := hψ.isOpen_fiber _
  have hopen := A.u.isOpenMap _ hO
  obtain ⟨y, ⟨u1, hu1, rfl⟩, hyD⟩ :=
    hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩
  obtain ⟨Ω2, _, _, x2, hx2⟩ := hEx A.U u1
  have hψ1 : ψ u1 = 0 := by
    rw [← hx2, hψeq Ω2 x2]
    apply finsum_mem_of_eqOn_zero
    intro z' hz'
    have hz'' : z' ≫ A.r = x2 := hz'
    have hw0 : w Ω2 (z' ≫ A.v) = 0 := by
      apply hzero Ω2
      have hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u := by
        rw [Category.assoc, A.pb.w, ← Category.assoc, hz'']
      rw [hc, pt_comp, hx2]
      exact hyD
    simp [hw0]
  have hu1' : ψ u1 = ψ (A.r v) := hu1
  have h1 := hsum Ω0 x0 hx0
  have h2 := hpos Ω0 x0 hx0
  rw [← hu1', hψ1] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h h2.ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PtExOf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptEx_of :
    PtEx := by
  intro X s
  let Ω : Type := AlgebraicClosure (X.residueField s)
  let y : gp Ω ⟶ Spec (X.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))
  refine ⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩
  rw [pt_comp]
  exact Scheme.fromSpecResidueField_apply s (pt y)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrBCOf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBC_of :
    TrChar → FamBC → WtBC → RpBasic → RpOp → TrBC := by
  intro hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWbc v p' p g w hpb hw
  have hq' : IsUnit ((q : ℕ) : Γ(S', ⊤)) := by
    have := hq.map g.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hs, _⟩ := hChar q i p w hw hq
  obtain ⟨τ', hτ', hτeq⟩ := hFam q i v p' p g w hpb (trFam p w q i) hs
  rw [(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ Z n).1 x
  have h1 := hOp _ _ (trFam p w q i) n x a ha
  have h2 := (hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1
  have h3 := (hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha
  have h4 := hOp _ _ τ' n _ _ h3
  have h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x))
      (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a)) := by
    have e := hτeq n a
    exact e ▸ h4
  exact ((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl
end

