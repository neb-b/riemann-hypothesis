module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0030
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactCOfOfExactBase
section
open CategoryTheory UpperTheory.V UpperTheory.V.Af.BA

private theorem hom_sum_apply {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, c i • f i).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom, Rep.smul_hom]
    simp [ih]

private theorem d_coeff {Γ I : Type} [Group Γ] [MulAction Γ I] (K : Cx Γ I) (p : ℕ)
    (x : K.Tup (p + 1)) (y : K.Tup p) :
    ((K.d p).hom.toLinearMap (Finsupp.single x 1) : K.Tup p →₀ ℂ) y =
      ((KH.faceD (fun (i : Fin (p + 2)) => K.re i.succAbove) (Finsupp.single x 1) y : ℤ) : ℂ) := by
  classical
  show (Rep.Hom.hom (K.d p)) (Finsupp.single x 1) y = _
  simp only [Cx.d]
  rw [hom_sum_apply]
  simp [KH.faceD_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Cx.reC_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem UpperTheory.exactCOf_of_exactBase :
    UpperTheory.V.Af.BA.ExactBase → UpperTheory.V.Af.BA.ExactCOf := by
  intro hB Γ I _ _ K hZ
  classical
  obtain ⟨hs, he0, -⟩ := hZ 0
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs 1
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    obtain ⟨t, -⟩ := Finsupp.support_nonempty_iff.2 hv0
    intro c
    exact ⟨Finsupp.single t c, by rw [augC_single]⟩
  · have key := hB (K.Tup 1) (K.Tup 0) Unit _
      ((Finsupp.lsingle ()) ∘ₗ KH.aug (K.Tup 0)) _
      ((Finsupp.lsingle ()) ∘ₗ (Rep.Hom.hom (augC Γ (K.Tup 0))).toLinearMap) (d_coeff K 0) ?_ ?_
    · intro y
      have hy := key y
      simpa [Finsupp.single_eq_zero] using hy
    · intro y z
      simp [KH.aug_single]
      exact augC_single y 1
    · intro y
      have hy := he0 y
      simpa [Finsupp.single_eq_zero] using hy
  · intro p
    exact hB _ _ _ _ _ _ _ (d_coeff K (p + 1)) (d_coeff K p) ((hZ (p + 1)).2.2 p (Nat.lt_succ_self p))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem grp1 {G : Type*} [Group G] (g a b u : G) (h : a * u = u * a) :
    g * u * (a * b) = g * (a * b) * (b⁻¹ * u * b) := by
  rw [mul_assoc g u, ← mul_assoc u, ← h]
  group

private theorem grp2 {G : Type*} [Group G] (g a b u : G) (h : u * a * b = b * (u * a)) :
    g * u * (a * b) = g * b * (u * a) := by
  rw [mul_assoc g b, ← h]
  group

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem id1 (g k : AdelicGLn.AdelicGL K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    g * finEmb K n u * k = g * k * finEmb K n ((finPart k)⁻¹ * u * finPart k) := by
  have h := grp1 g _ (finEmb K n (finPart k)) _ (infEmb_mul_finEmb_comm (archPart k) u)
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul, map_mul, map_inv]
  exact h

private theorem id2 (g k : AdelicGLn.AdelicGL K n) (u : archGroup K n) :
    g * infEmb K n u * k = g * finEmb K n (finPart k) * infEmb K n (u * archPart k) := by
  have h0 := infEmb_mul_finEmb_comm (u * archPart k) (finPart k)
  rw [map_mul] at h0
  have h := grp2 g _ _ _ h0
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul]
  exact h

private theorem hmul (a b : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) : rt a (rt b φ) = rt (a * b) φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, rt_apply, rt_apply, mul_assoc])

private theorem hone (φ : archSmooth K n) : rt (1 : AdelicGLn.AdelicGL K n) φ = φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, mul_one])

private noncomputable def sat (S : Submodule ℂ (archSmooth K n)) : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {ψ | ∃ k ∈ Reduction.maxCompact (K := K) (n := n), ∃ φ ∈ S, ψ = rt k φ}

private theorem ind (S : Submodule ℂ (archSmooth K n)) (P : archSmooth K n → Prop) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (c : ℂ) x, P x → P (c • x))
    (hg : ∀ k ∈ Reduction.maxCompact (K := K) (n := n), ∀ φ ∈ S, P (rt k φ)) : ∀ ψ ∈ sat S, P ψ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, φ, hφ, rfl⟩ := hx
    exact hg k hk φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul c x _ hx => exact hs c x hx
end

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {S : Submodule ℂ (archSmooth K n)}

private theorem sat_left (hS : Bdd S) : ∀ φ ∈ sat S, IsLeftInvariant φ.1 := by
  refine ind S (fun φ => IsLeftInvariant φ.1) isLeftInvariant_zero
      (fun x y hx hy γ g => congrArg₂ (· + ·) (hx γ g) (hy γ g))
      (fun c x hx γ g => congrArg (c • ·) (hx γ g)) ?_
  intro k _ φ hφ γ g
  rw [rt_apply, rt_apply, mul_assoc]
  exact hS.left φ hφ γ _

private theorem sat_growth (hS : Bdd S) : Growth (sat S) := by
  refine ind S (fun φ => HasModerateGrowth φ.1) hasModerateGrowth_zero
      (fun x y hx hy => hx.add hy) (fun c x hx => hx.smul c) ?_
  intro k _ φ hφ
  have h := (hS.growth φ hφ).translate k
  have e : (rt k φ).1 = rightTranslate k φ.1 := funext fun x => rt_apply k φ x
  rw [e]
  exact h

private theorem sat_level (hS : Bdd S) : Level (sat S) := by
  obtain ⟨L, hL, hinv⟩ := hS.level
  obtain ⟨L', hL', hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  refine ⟨L', hL', ?_⟩
  refine ind S (fun φ => ∀ u ∈ L', ∀ g, φ.1 (g * finEmb K n u) = φ.1 g) (fun _ _ _ => rfl)
      (fun x y hx hy u hu g => congrArg₂ (· + ·) (hx u hu g) (hy u hu g))
      (fun c x hx u hu g => congrArg (c • ·) (hx u hu g)) ?_
  intro k hk φ hφ u hu g
  rw [rt_apply, rt_apply, id1]
  exact hinv φ hφ _ (hle (hconj _ (finPart_mem_integralFiniteGL hk) u hu)) (g * k)

private theorem sat_types (hS : Bdd S) : Types (sat S) := by
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, ?_⟩
  refine ind S (fun φ => ∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k.1)) ∈ V) (fun _ => V.zero_mem)
      (fun x y hx hy g => V.add_mem (hx g) (hy g))
      (fun c x hx g => V.smul_mem c (hx g)) ?_
  intro k hk φ hφ g
  have h := hst _ (hmem φ hφ (g * finEmb K n (finPart k))) ⟨archPart k, archPart_mem_archCompact hk⟩
  have e : (fun k' : archCompact K n => (rt k φ).1 (g * infEmb K n k'.1)) =
      fun k' : archCompact K n => φ.1 (g * finEmb K n (finPart k) * infEmb K n (k'.1 * archPart k)) :=
    funext fun k' => by rw [rt_apply, id2]
  rw [e]
  exact h

private theorem sat_centre (hS : Bdd S) : Centre (sat S) := by
  intro z hz
  obtain ⟨p, hp, h⟩ := hS.centre z hz
  refine ⟨p, hp, ?_⟩
  refine ind S (fun φ => Polynomial.aeval (uAction z) p φ ∈ (⊥ : Submodule ℂ (archSmooth K n)))
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k _ φ hφ
  have hc : Commute (rt (K := K) (n := n) k) (Polynomial.aeval (uAction z) p) :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      (by rintro _ rfl; exact (UpperTheory.centerU_action_commute_rightTranslation K n z hz k).symm)
  have e := LinearMap.congr_fun hc.eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  rw [← e, (Submodule.mem_bot ℂ).1 (h φ hφ), map_zero]
  exact Submodule.zero_mem _

private theorem sat_sat : Sat (sat S) := by
  intro k hk
  refine ind S (fun φ => rt k φ ∈ sat S)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k' hk' φ hφ
  exact Submodule.subset_span ⟨k * k', mul_mem hk hk', φ, hφ, hmul _ _ _⟩
end

theorem UpperTheory.exists_automorphic_saturation_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∃ S' : Submodule ℂ (archSmooth K n), S ≤ S' ∧ Bdd S' ∧ Sat S' := by
  intro K _ _ n S hS
  exact ⟨sat S, fun φ hφ => Submodule.subset_span ⟨1, one_mem _, φ, hφ, (hone φ).symm⟩,
    ⟨sat_left hS, sat_growth hS, sat_level hS, sat_types hS, sat_centre hS⟩, sat_sat⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMExtension
section
open NumberField QuadraticAlgebra

private theorem real_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ψ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (ψ x) = ψ x := by
  have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk ψ)))
  have := RingHom.congr_fun hr x
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  exact this

private theorem sq_neg_one {z : ℂ} (h : z * z = -1) : starRingEnd ℂ z = -z := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
    Complex.one_im] at h1 h2
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre]

theorem UpperTheory.exists_CM_extension :
    UpperTheory.V.Af.BA.ExCM := by
  intro F _ _ _
  let ψ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  haveI hfact : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) := by
    refine ⟨fun r hr => ?_⟩
    have h2 : ψ r * ψ r = -1 := by
      rw [← map_mul, ← pow_two, hr]
      simp
    have h3 := real_val ψ r
    rw [sq_neg_one h2] at h3
    have h4 : ψ r = 0 := by
      have : (2 : ℂ) * ψ r = 0 := by linear_combination -h3
      simpa using this
    rw [h4] at h2
    norm_num at h2
  haveI hNF : NumberField (QuadraticAlgebra F (-1) 0) :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F (QuadraticAlgebra F (-1) 0) }
  have hωω : (ω : QuadraticAlgebra F (-1) 0) * ω = -1 := by
    rw [omega_mul_omega_eq_mk]
    ext <;> simp
  have hφω : ∀ φ : QuadraticAlgebra F (-1) 0 →+* ℂ, starRingEnd ℂ (φ ω) = - φ ω := by
    intro φ
    apply sq_neg_one
    rw [← map_mul, hωω, map_neg, map_one]
  have hTC : IsTotallyComplex (QuadraticAlgebra F (-1) 0) := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)
    have h1 := RingHom.congr_fun hr ω
    rw [ComplexEmbedding.conjugate_coe_eq, hφω] at h1
    have h0 : v.embedding ω = 0 := by
      have : (2 : ℂ) * v.embedding ω = 0 := by linear_combination -h1
      simpa using this
    have h5 : v.embedding ω * v.embedding ω = -1 := by
      rw [← map_mul, hωω, map_neg, map_one]
    rw [h0] at h5
    norm_num at h5
  refine ⟨QuadraticAlgebra F (-1) 0, inferInstance, hNF, hTC, algebraMap F (QuadraticAlgebra F (-1) 0),
    starRingEnd (QuadraticAlgebra F (-1) 0), ?_, ?_⟩
  · intro φ x
    have hx : x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re +
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      ext <;> simp
    have hsx : starRingEnd (QuadraticAlgebra F (-1) 0) x = algebraMap F (QuadraticAlgebra F (-1) 0) x.re -
        algebraMap F (QuadraticAlgebra F (-1) 0) x.im * ω := by
      show star x = _
      ext <;> simp
    have hreal : ∀ y : F, starRingEnd ℂ (φ (algebraMap F (QuadraticAlgebra F (-1) 0) y)) =
        φ (algebraMap F (QuadraticAlgebra F (-1) 0) y) :=
      fun y => real_val (φ.comp (algebraMap F (QuadraticAlgebra F (-1) 0))) y
    rw [hsx]
    conv_rhs => rw [hx]
    simp only [map_add (f := _), map_sub, map_mul, hreal, hφω]
    ring
  · intro x
    rw [RingHom.mem_range]
    constructor
    · intro hx
      have him := congrArg QuadraticAlgebra.im hx
      change (star x).im = x.im at him
      rw [im_star] at him
      have h0 : x.im = 0 := by
        have : (2 : F) * x.im = 0 := by linear_combination -him
        simpa using this
      refine ⟨x.re, ?_⟩
      ext <;> simp [h0]
    · rintro ⟨y, rfl⟩
      show star (algebraMap F (QuadraticAlgebra F (-1) 0) y) = _
      ext <;> simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExtVanishingOfResolutionEndo
section
open CategoryTheory Limits in
private theorem homologyMap_zero_of_f {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (Ψ : K ⟶ L) (q : ι) (h : Ψ.f q = 0) :
    HomologicalComplex.homologyMap Ψ q = 0 := by
  have h1 : HomologicalComplex.cyclesMap Ψ q = 0 := by
    rw [← cancel_mono (L.iCycles q), zero_comp, HomologicalComplex.cyclesMap_i, h, comp_zero]
  rw [← cancel_epi (K.homologyπ q), comp_zero, HomologicalComplex.homologyπ_naturality, h1, zero_comp]

open CategoryTheory Limits in
private theorem isZero_yoneda {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
    [Linear R C] {X : C} (Y : C) (P : ProjectiveResolution X) (e : P.complex ⟶ P.complex)
    (he : e ≫ P.π = P.π) (q : ℕ) (hq : e.f q = 0) :
    IsZero ((P.complex.linearYonedaObj R Y).homology q) := by
  let F := ((linearYoneda R C).obj Y).rightOp
  have h1 : Homotopy e (𝟙 P.complex) :=
    ProjectiveResolution.liftHomotopy (𝟙 X) e (𝟙 _) (by simpa using he) (by simp)
  have h2 := (F.mapHomotopy h1).unop
  have h3 := h2.homologyMap_eq q
  have hz : ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map e).op).f q = 0 := by
    show (F.map (e.f q)).unop = 0
    rw [hq, F.map_zero]
    rfl
  rw [homologyMap_zero_of_f _ q hz] at h3
  simp only [CategoryTheory.Functor.map_id, op_id, HomologicalComplex.homologyMap_id] at h3
  rw [IsZero.iff_id_eq_zero]
  exact h3.symm

open CategoryTheory Limits in
theorem UpperTheory.ext_vanishing_of_resolution_endo :
    UpperTheory.V.Af.BA.VanishOf := by
  intro Γ _ P e he q hq A
  have h2 : IsZero (groupCohomology A q) :=
    (isZero_yoneda (R := ℂ) A P e he q hq).of_iso (groupCohomologyIso A q P)
  haveI := ModuleCat.subsingleton_of_isZero h2
  exact rank_subsingleton' ℂ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedOrbitsFiniteRepresentatives
section
private theorem fixOrb_reps {Z T : Type} (f : Z → T) (W : Set Z) (h : (f '' W).Finite) :
    ∃ B : Set Z, B ⊆ W ∧ B.Finite ∧ ∀ z ∈ W, ∃ z' ∈ B, f z' = f z := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · exact ⟨∅, by simp, Set.finite_empty, by simp [hW]⟩
  · haveI : Nonempty Z := ⟨w⟩
    refine ⟨Function.invFunOn f W '' (f '' W), ?_, h.image _, ?_⟩
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Function.invFunOn_mem ⟨z, hz, rfl⟩
    · intro z hz
      exact ⟨Function.invFunOn f W (f z), ⟨f z, ⟨z, hz, rfl⟩, rfl⟩,
        Function.invFunOn_eq ⟨z, hz, rfl⟩⟩

theorem UpperTheory.fixedOrbits_finite_representatives :
    UpperTheory.V.Af.BA.FixOrb := by
  classical
  intro G Z _ _ σ s hs W hfix hstab ⟨R, hR, hRW⟩
  have himg : ((fun z => MulAction.orbit G z) '' W).Finite := by
    refine (hR.image (fun z => MulAction.orbit G z)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := hRW z hz
    exact ⟨g • z, hg, MulAction.orbit_smul g z⟩
  obtain ⟨B1, hB1W, hB1, hB1r⟩ := fixOrb_reps _ W himg
  have hb : ∀ z ∈ W, ∃ b ∈ B1, ∃ h : G, h • b = z := by
    intro z hz
    obtain ⟨b, hbB, hbo⟩ := hB1r z hz
    have hbo' : MulAction.orbit G b = MulAction.orbit G z := hbo
    have hm : z ∈ MulAction.orbit G b := by
      rw [hbo']
      exact MulAction.mem_orbit_self z
    obtain ⟨h, hh⟩ := hm
    exact ⟨b, hbB, h, hh⟩
  let bb : Z → Z := fun z => if hz : z ∈ W then (hb z hz).choose else z
  let hh : Z → G := fun z => if hz : z ∈ W then (hb z hz).choose_spec.2.choose else 1
  have bbB : ∀ z ∈ W, bb z ∈ B1 := fun z hz => by
    simp only [bb, dif_pos hz]
    exact (hb z hz).choose_spec.1
  have hhb : ∀ z ∈ W, hh z • bb z = z := fun z hz => by
    simp only [bb, hh, dif_pos hz]
    exact (hb z hz).choose_spec.2.choose_spec
  have hcoc : ∀ z ∈ W, (hh z)⁻¹ * σ (hh z) ∈ MulAction.stabilizer G (bb z) := by
    intro z hz
    have hbW : bb z ∈ W := hB1W (bbB z hz)
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    calc σ (hh z) • bb z = σ (hh z) • s (bb z) := by rw [hfix _ hbW]
      _ = s (hh z • bb z) := (hs _ _).symm
      _ = hh z • bb z := by rw [hhb z hz, hfix z hz]
  let key : Z → Z × G := fun z => (bb z, (hh z)⁻¹ * σ (hh z))
  have hkey : (key '' W).Finite := by
    refine (hB1.prod (hB1.biUnion (fun b hbB =>
      (haveI := hstab b (hB1W hbB); Set.toFinite (MulAction.stabilizer G b : Set G))))).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨bbB z hz, Set.mem_biUnion (bbB z hz) (hcoc z hz)⟩
  obtain ⟨B, hBW, hB, hBr⟩ := fixOrb_reps key W hkey
  refine ⟨B, hB, fun z hz => ?_⟩
  obtain ⟨z', hz'B, hk⟩ := hBr z hz
  have hz'W := hBW hz'B
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨hh z' * (hh z)⁻¹, ?_, ?_⟩
  · have : σ (hh z') = hh z' * ((hh z)⁻¹ * σ (hh z)) := by
      rw [← h2, mul_inv_cancel_left]
    rw [map_mul, map_inv, this]
    group
  · rw [mul_smul, inv_smul_eq_iff.mpr (hhb z hz).symm, ← h1, hhb z' hz'W]
    exact hz'B
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
section
theorem UpperTheory.galois_rep_values_in_finite_extension :
    UpperTheory.V.Af.Wd.FinVal := by
  intro F Ω C _ _ _ _ M hM χ hχ
  classical
  have hpos : 0 < M := by omega
  have hR : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hpos] using hζ
  haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype
  let π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1}) := fun s ζ =>
    ⟨s ζ, by
      show (s ζ) ^ M = 1
      rw [← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩
  have hfac : ∀ s t, π s = π t → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      refine hχ _ (fun ζ hζ => ?_)
      have h := congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst
      simp only [π] at h
      rw [AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  refine (Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ImaginaryGenerator
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.imaginary_generator :
    UpperTheory.V.Af.Cr.ImagGen := by
  intro K _ _ _ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  obtain ⟨d, e, -, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq ℚ K
  have hy : e 1 ^ 2 = (d : K) := by rw [sq, h1]; simp
  have hx : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * e 1 := fun x => by
    refine ⟨e.repr x 0, e.repr x 1, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨d, e 1, ?_, hy, hx⟩
  by_contra hd
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast not_lt.1 hd
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  have hφ : φ (e 1) ^ 2 = ((Real.sqrt d : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hy, ← Complex.ofReal_pow, Real.sq_sqrt hd0]
    simp
  have hc : (starRingEnd ℂ) (φ (e 1)) = φ (e 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hφ with h2 | h2 <;> simp [h2]
  rw [ComplexEmbedding.isReal_iff]
  ext1 x
  obtain ⟨a, b, rfl⟩ := hx x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp [hc]
end

