module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTypeOfLbl
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

private noncomputable def chRep {H : Type} [Group H] (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

private theorem chRep_apply {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) (z : ℂ) :
    chRep χ g z = ((χ g : ℂˣ) : ℂ) • z := rfl

private theorem trace_chRep {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) :
    LinearMap.trace ℂ ℂ (chRep χ g) = ((χ g : ℂˣ) : ℂ) := by
  show LinearMap.trace ℂ ℂ (((χ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl (fun g => LinearMap.trace ℂ W (ρ g)) := by
  intro x y
  simp only [map_mul]
  rw [LinearMap.trace_mul_cycle, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem trace_zero {W : Type} [AddCommGroup W] [Module ℂ W] (h : ¬ FiniteDimensional ℂ W) :
    LinearMap.trace ℂ W = 0 := by
  ext f
  have hn : ¬ ∃ s : Finset W, Nonempty (Module.Basis s ℂ W) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp only [LinearMap.trace, dif_neg hn]

private theorem ofFn_comp_get {β : Type} (M : List (ℕ × ℕ)) (f : ℕ × ℕ → β) :
    List.ofFn (fun a : Fin M.length => f (M.get a)) = M.map f := by
  rw [List.ofFn_comp', List.ofFn_get]

private theorem sum_fst (M : List (ℕ × ℕ)) : ∑ a : Fin M.length, (M.get a).1 = deg M := by
  unfold GlobalTheory.Shin.deg
  rw [← List.sum_ofFn]
  congr 1
  have := List.ofFn_comp' M.get Prod.fst
  simpa [List.ofFn_get] using this

end UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

open UpperTheory.Gal.InertialTypesAlt.TypesOfLabels in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.typeOfLbl :
    MeetsIff → FrobL → JDEq → TypeOfLbl := by
  intro hMI hFL hJD k _ _ _ _ θ N V _ _ π b hb hL
  obtain ⟨_, _, hN, hmeet⟩ := hb
  have hd : ∑ a : Fin (b.D ++ b.L).length, ((b.D ++ b.L).get a).1 = N := by
    rw [sum_fst, hN]
    simp [Lbl.rk, GlobalTheory.Shin.deg, List.map_append, List.sum_append]
  let ω : Fin (b.D ++ b.L).length → 𝓀[k]ˣ →* ℂˣ := fun a =>
    (powMonoidHom ((b.D ++ b.L).get a).2).comp
      ((Units.map (θ : AlgebraicClosure 𝓀[k] →* ℂ)).comp
        (Units.map (algebraMap 𝓀[k] (AlgebraicClosure 𝓀[k])).toMonoidHom))
  refine ⟨(b.D ++ b.L).length, fun a => ((b.D ++ b.L).get a).1,
    fun a => ((b.D ++ b.L).get a).2, hd, ω, ?_, ?_, ?_⟩
  · rw [show (fun a : Fin (b.D ++ b.L).length => (((b.D ++ b.L).get a).1, ((b.D ++ b.L).get a).2))
        = (b.D ++ b.L).get from funext fun a => rfl, List.ofFn_get]
  · intro a u
    simp [ω]
  have hJ : JD θ b.D b.L N = hcL (List.ofFn fun i : Fin (b.D ++ b.L).length =>
      (⟨((b.D ++ b.L).get i).1, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJD 𝓀[k] θ).1, ofFn_comp_get (b.D ++ b.L)
      (fun p => (⟨p.1, detc θ p.1 p.2⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))), List.map_append]
    congr 2
    apply List.map_congr_left
    rintro ⟨p1, p2⟩ hp
    have h1 : p1 = 1 := hL _ hp
    subst h1
    rw [(hJD 𝓀[k] θ).2.1]
  obtain ⟨c0, hc0, hF⟩ := hFL 𝓀[k] (b.D ++ b.L).length (fun a => ((b.D ++ b.L).get a).1) N hd
  have hsum := hF (fun i => detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2)
    (fun g => LinearMap.trace ℂ _ (levelZero π g)) (isCl_trace _)
  have hne : ∑ᶠ p : parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd),
      star (∏ i, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2
        (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd) p i)) *
        LinearMap.trace ℂ _ (levelZero π (p : GL (Fin N) 𝓀[k])) ≠ 0 := by
    intro h0
    unfold Meets at hmeet
    rw [hJ, hsum, h0, mul_zero] at hmeet
    exact hmeet rfl
  have hfd : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    by_contra hfd
    apply hne
    simp [trace_zero hfd]
  let χ := (UpperTheory.Gal.TypesAndIwahori.leviChar (fun a : Fin (b.D ++ b.L).length => Fin ((b.D ++ b.L).get a).1) ω).comp
    (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd))
  have hm : Meets ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd)).subtype)
      (fun g => LinearMap.trace ℂ ℂ (chRep χ g)) := by
    unfold Meets
    convert hne using 3 with p
    simp only [trace_chRep]
    simp [χ, ω, UpperTheory.Gal.TypesAndIwahori.leviChar_apply, detc]
  obtain ⟨f, hf0, hf⟩ := ((hMI _ _ ℂ _ _).2).1 hm
  have hf1 : f 1 ≠ 0 := fun h => hf0 (LinearMap.ext_ring (by simpa using h))
  refine ⟨(f 1 : V), by simpa using hf1, ?_⟩
  intro g
  obtain ⟨hK, hP⟩ := mem_levelPre.1 g.2
  have h2 := congrArg Subtype.val (hf ⟨redK k (Fin N) ⟨(g : GL (Fin N) k), hK⟩, hP⟩ 1)
  rw [chRep_apply, map_smul] at h2
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, levelZero_apply,
    Submodule.coe_smul] at h2
  rw [← h2]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnrOfIne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unrOfIne :
    UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI
  have hunder : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    ext x
    show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal
    rw [← hw, ← hv]
    have hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K) := by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      rfl
    rw [hx]
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩
  have hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap M Ω).injective
    show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hI t ht x
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← (UpperTheory.V.CF.ineCard).1 K M w, hinert]
    simp
  refine ⟨hunder, ?_, ?_⟩
  · rintro ⟨w', hw'⟩
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]
    exact he
  · intro x hx hmem
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    have hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
      exact he
    have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal :=
      Ideal.map_le_iff_le_comap.2 hcomap.ge
    have hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2 :=
      fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1
    by_cases hxv : x ∈ v.asIdeal
    · obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x} :=
        Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)
      have hJv : ¬ J ≤ v.asIdeal := by
        intro h
        apply hx
        rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
        exact Ideal.mul_mono_right h
      have hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal := by
        intro h
        rw [Ideal.map_le_iff_le_comap, hcomap] at h
        exact hJv h
      have hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤ := by
        by_contra hne
        exact hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))
      have hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤ := by
        have hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal :=
          Ideal.isCoprime_iff_sup_eq.2 hsup
        exact Ideal.isCoprime_iff_sup_eq.1 hc.pow_right
      apply hnot
      have hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
        exact hmem
      have hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2 :=
        Ideal.mul_le_right
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal
          = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal *
              (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2) := by rw [hsup2, Ideal.mul_top]
        _ = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ⊔
              Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 := by
            rw [Ideal.mul_sup, hJ, Ideal.map_mul]
        _ ≤ w.asIdeal ^ 2 := sup_le hx2 hr
    · apply hxv
      rw [← hcomap, Ideal.mem_comap]
      exact Ideal.pow_le_self two_ne_zero hmem
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SumFstMap
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons' {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b n : ℕ) (h : (Y.map Sigma.fst).sum = b) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h; rfl

private theorem sum_fst_map {F : Type} [Field F] (f : ℕ × ℕ → (Σ m : ℕ, GL (Fin m) F → ℂ))
    (hf : ∀ p, (f p).1 = p.1) (L : List (ℕ × ℕ)) :
    ((L.map f).map Sigma.fst).sum = deg L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih, hf]
    rfl

private theorem J_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) :
    ∀ n, J θ L n = hcL (L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction L with
  | nil => intro n; rfl
  | cons p L ih =>
    intro n
    rw [J_cons, List.map_cons, hcL_cons' _ _ (deg L) n (sum_fst_map _ (fun _ => rfl) L), ih]

private theorem JD_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) :
    ∀ n, JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction D with
  | nil => intro n; simpa [JD_nil] using J_eq θ L n
  | cons p D ih =>
    intro n
    have hs : (((D.map (fun p : ℕ × ℕ => (⟨p.1, detc θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))) ++
        L.map (fun p : ℕ × ℕ => (⟨p.1, cusp θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).map Sigma.fst).sum =
        deg D + deg L := by
      rw [List.map_append, List.sum_append, sum_fst_map _ (fun _ => rfl) D, sum_fst_map _ (fun _ => rfl) L]
    rw [JD_cons, List.map_cons, List.cons_append, hcL_cons' _ _ (deg D + deg L) n hs, ih]

private theorem cusp_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    cusp θ 1 k = detc θ 1 k := by
  haveI : Fintype F := Fintype.ofFinite F
  funext x
  have hcp : Matrix.charpoly (x : Matrix (Fin 1) (Fin 1) F) = X - C ((x : Matrix (Fin 1) (Fin 1) F) 0 0) := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  have hval := _root_.GlobalTheory.CuspGL.psi_of_irreducible_charpoly F (Fin 1 → F) _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1
    (Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F))
    (by rw [Matrix.charpoly_toLin', hcp]; exact irreducible_X_sub_C _)
  rw [Matrix.charpoly_toLin', hcp] at hval
  simp only [cusp, psiG, detc, Nat.sub_self, pow_zero, one_mul]
  rw [hval, Matrix.det_fin_one]
  simp [GlobalTheory.CuspGL.rootSum]

theorem UpperTheory.Gal.InertialTypesAlt.jdEq :
    JDEq := by
  intro F _ _ θ
  refine ⟨fun D L n => JD_eq θ D L n, cusp_one θ, ?_⟩
  intro D L n
  cases D with
  | nil =>
    cases L with
    | nil => intro x y; rfl
    | cons p L => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
  | cons p D => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
end

