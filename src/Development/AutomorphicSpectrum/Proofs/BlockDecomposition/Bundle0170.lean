module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0163
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.HT CrystallineSemistableComparison.Pb GlobalTheory.LogCris

namespace GlobalTheory.CompanionTheory.HodgePull

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem thick_ext {T T' : Thick (smFun X q)} (hB : T.B = T'.B) (hr : HEq T.ring T'.ring) (hi : HEq T.i T'.i)
    (hJ : HEq T.J T'.J) (hδ : HEq T.δ T'.δ) (hy : HEq T.y T'.y) : T = T' := by
  have hs : T.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  have hs' : T'.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'
  cases T with
  | @mk B ring i J δ adm compat α y inα w x v s hx hs0 hv =>
  cases T' with
  | @mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv' =>
  dsimp only at hB hr hi hJ hδ hy hs hs'
  subst hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hy
  obtain rfl : x = x' := funext fun j => Empty.elim j
  obtain rfl : v = v' := funext fun j => Empty.elim j
  obtain rfl : s = s' := hs.trans hs'.symm
  rfl

theorem hom_heq {T₁ T₂ T₁' T₂' : Thick (smFun X q)} (h : T₁ = T₂) (h' : T₁' = T₂') (f : T₁ ⟶ T₁') (g : T₂ ⟶ T₂')
    (hφ : HEq f.φ g.φ) : HEq f g := by
  subst h h'
  exact heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))

theorem obj_id (T : Thick (smFun X q)) : (smMor (𝟙 X) (Category.id_comp q)).obj T = T :=
  thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))

theorem functor_id : (smMor (𝟙 X) (Category.id_comp q)).functor = 𝟭 _ :=
  Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl

abbrev idMor (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ) : CH.Mor (grT (smFun X q) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS (𝟙 X) (Category.id_comp q)).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ))
    (b' := thFil _ ((a : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx

theorem τ_id (a : ℕ) (T : Thick (smFun X q)) (y : (grT (smFun X q) a).obj T) :
    (idMor q a).τ T y = y := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem pullC_id (a n : ℕ) (z : CH.Cn (grT (smFun X q) a) n) : (idMor q a).pullC n z = z := by
  funext s
  have h : s ⋙ (idMor q a).G = s := by
    change s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s
    rw [functor_id]
    exact Functor.comp_id s
  exact (τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))

theorem pullH_id : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    pullH (𝟙 X) (Category.id_comp q) a n x = x := by
  intro K _ X q a n x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))

end GlobalTheory.CompanionTheory.HodgePull

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXi
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

namespace GradedFiltration

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem dividedXi_mem_filtration {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.dxi0 r ∈ A.Fil0 r :=
  Ideal.subset_span ⟨r, le_rfl, rfl⟩

theorem mem_filtration_of_prime_pow_mul {l : ℕ} [Fact l.Prime] (A : PAlg l) (r n : ℕ) (z : A.Acr0)
    (h : (l : A.Acr0) ^ n * z ∈ A.Fil0 r) : z ∈ A.Fil0 r := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply _root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated A r
    rwa [pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc] at h

theorem mkAcr_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

end GradedFiltration


open GradedFiltration in
theorem graded_mod_pow : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ),
    (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  intro l _ A n r
  have hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n) := (_root_.GlobalTheory.CompanionTheory.FilMul.main A).2.2.2.2.1 n
  have hsurj := mkAcr_surjective A n
  have hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w) := fun _ => rfl
  have hdx : A.dxi n r = A.mkAcr n (A.dxi0 r) := rfl
  refine ⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨w, hw⟩ := (_root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces A r).1 z0 hz0
    refine ⟨w, ?_⟩
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hF, hto, hdx, ← map_mul (A.mkAcr n), ← map_sub (A.mkAcr n)]
    exact Ideal.mem_map_of_mem _ hw
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul] at h
    obtain ⟨z', hz', e⟩ := h
    have hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n} := by
      apply Ideal.Quotient.eq.1
      exact e.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hd
    have hzr : z ∈ A.Fil0 r := by
      apply mem_filtration_of_prime_pow_mul A r n
      rw [← hz]
      exact sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')
    obtain ⟨w', hw'⟩ := (_root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces A r).1 z hzr
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      rw [← (_root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces A r).2.1]
      have : algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r =
          z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hz
      rw [this]
      exact add_mem hz' (Ideal.mul_mem_left _ _ hw')
    have : A.th w = (l : A.U) ^ n * A.th w' := by
      have h0 : A.th (w - (l : A.W) ^ n * w') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxi
      rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at h0
      exact h0
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h
    obtain ⟨w', rfl⟩ : ∃ w', A.th w' = u := Ideal.Quotient.mk_surjective u
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      apply Ideal.Quotient.eq_zero_iff_mem.1
      change A.th (w - (l : A.W) ^ n * w') = 0
      rw [map_sub, map_mul, map_pow, map_natCast, hu, sub_self]
    have h1 := (_root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces A r).2.1 _ |>.2 hxi
    have h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1) := by
      rw [hF, hto, hdx, ← map_mul]
      exact Ideal.mem_map_of_mem _ h1
    have h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w := by
      rw [map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]
    rwa [h3] at h2

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLift

theorem exists_injectiveSequence_lift {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') :
    ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  have hS := injectiveSequence_shortExact G
  have : Mono (injectiveSequence G).f := hS.mono_f
  have : Injective ((push f).obj (injectiveSequence G').X₂) := injective_push f _
  let τ₂ : (injectiveSequence G).X₂ ⟶ (push f).obj (injectiveSequence G').X₂ :=
    Injective.factorThru (φ ≫ (push f).map (injectiveSequence G').f) (injectiveSequence G).f
  have h₁ : (injectiveSequence G).f ≫ τ₂ = φ ≫ (push f).map (injectiveSequence G').f :=
    Injective.comp_factorThru _ _
  have h₀ : (injectiveSequence G).f ≫ τ₂ ≫ (push f).map (injectiveSequence G').g = 0 := by
    rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, (injectiveSequence G').zero,
      Functor.map_zero, comp_zero]
  let τ₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ h₀)
  have h₃ : (injectiveSequence G).g ≫ τ₃ = τ₂ ≫ (push f).map (injectiveSequence G').g :=
    Cofork.IsColimit.π_desc hS.gIsCokernel
  exact ⟨{ τ₁ := φ, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₁.symm, comm₂₃ := h₃.symm }, rfl⟩

end GlobalTheory.CompanionTheory.CechLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis.PullO

theorem restrict_pull1_bijective_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (CoefMap.restrict (OAff s') G).pull1 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

section Triple

variable {R'' : Type} [CommRing R''] {X X' X'' : Scheme.{0}}
variable (ψ : X'' ⟶ X') (φ : X' ⟶ X)

theorem triple_restriction_pair_restriction (s'' : X'' ⟶ Sp R'') (c : HO1 s'') :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ c
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem triple_restriction_injective (s'' : X'' ⟶ Sp R'') : Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [triple_restriction_pair_restriction, triple_restriction_pair_restriction] at hxy
  rw [(restrict_pull1_bijective_of_basis s'' (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))
    (triple_cover_affine ψ φ s'') (exists_triple_below_two ψ φ s'')).1 hxy]

end Triple

section Comp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem tri_pull_pull (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  erw [GlobalTheory.CatCoh.mp_id]
  show (CommRingCat.Hom.hom (Scheme.Hom.appLE φ _ _ _ ≫ Scheme.Hom.appLE ψ _ _ _)) b =
    CommRingCat.Hom.hom (Scheme.Hom.appLE (ψ ≫ φ) _ _ _) b
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (Scheme.Hom.appLE_comp_appLE ψ φ _ _ _ _ _)

theorem tri_res_pull (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HO1 s') :
    (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem tri_res_res (a : HO1 s'') :
    (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (b : HO1 s') (c : HO1 s'') :
    IsPullO h a b → IsPullO h' b c → IsPullO h'' a c := by
  intro hab hbc
  apply triple_restriction_injective ψ φ s''
  unfold IsPullO at hab hbc
  rw [tri_pull_pull h h' h'' a, hab, tri_res_pull h' b, hbc, tri_res_res (φ := φ) c]

end Comp

theorem isPullO_wOver_comp : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  intro R _ X Y Z f g a b c hab hbc
  exact isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) a b c hab hbc

end GlobalTheory.CompanionTheory.Axis.PullO
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecomposition
section
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem exists_proj_sup {E : Type*} [AddCommGroup E] [Module ℝ E] (𝔨 𝔟 : Submodule ℝ E) :
    ∃ p q : E →ₗ[ℝ] E, (∀ Z, p Z ∈ 𝔨) ∧ (∀ Z, q Z ∈ 𝔟) ∧
      ∀ Z, Z - p Z - q Z ∈ 𝔨 ⊔ 𝔟 → Z - p Z - q Z = 0 := by
  let f : (𝔨 × 𝔟) →ₗ[ℝ] E := 𝔨.subtype.coprod 𝔟.subtype
  have hr : LinearMap.range f = 𝔨 ⊔ 𝔟 := by
    simp [f, LinearMap.range_coprod]
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨P, hP⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (by simp)
  have hsum : ∀ Z, ((s (P Z)).1 : E) + ((s (P Z)).2 : E) = (P Z : E) := by
    intro Z
    have h2 := LinearMap.congr_fun hs (P Z)
    have h3 := congrArg Subtype.val h2
    simpa [f] using h3
  refine ⟨𝔨.subtype ∘ₗ LinearMap.fst ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P, 𝔟.subtype ∘ₗ LinearMap.snd ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P,
    fun Z => (s (P Z)).1.2, fun Z => (s (P Z)).2.2, fun Z hZ => ?_⟩
  have hid : ∀ W (hW : W ∈ LinearMap.range f), P W = ⟨W, hW⟩ := fun W hW =>
    LinearMap.congr_fun hP ⟨W, hW⟩
  have hval : Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = Z - (P Z : E) := by
    rw [sub_sub, hsum]
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = 0
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) ∈ 𝔨 ⊔ 𝔟 at hZ
  rw [hval] at hZ ⊢
  rw [← hr] at hZ
  have h1 := hid _ hZ
  have h2 : P (Z - (P Z : E)) = P Z - P (P Z : E) := map_sub _ _ _
  have h3 : P (P Z : E) = P Z := hid _ (P Z).2
  rw [h3, sub_self] at h2
  have h4 := congrArg Subtype.val (h1.symm.trans h2)
  simpa using h4

theorem eventually_exp_mul_exp {G : Set A} (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {𝔤 𝔨 𝔟 : Submodule ℝ A} (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {V : Set A} (hV : V ∈ 𝓝 (0 : A)) (hVG : ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨p₀, q₀, hpk, hqb, hr0⟩ := exists_proj_sup 𝔨 𝔟
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap p₀
  let q : A →L[ℝ] A := LinearMap.toContinuousLinearMap q₀
  let r : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p - q
  have hr : ∀ Z, r Z = Z - p Z - q Z := fun Z => rfl
  let Φ : A → A := fun Z =>
    NormedSpace.exp (p Z) * NormedSpace.exp (q Z) * NormedSpace.exp (r Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEl : ∀ l : A →L[ℝ] A, HasStrictFDerivAt (fun Z => NormedSpace.exp (l Z)) l (0 : A) := by
    intro l
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (l 0) := by
      simpa using hE
    exact (h2.comp (0 : A) l.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := ((hEl p).mul' (hEl q)).mul' (hEl r)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hr]
    abel
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : r ⁻¹' V ∈ 𝓝 (0 : A) := by
    refine r.continuous.continuousAt.preimage_mem_nhds ?_
    simpa using hV
  have himg : Φ '' (r ⁻¹' V) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  have hneg : ∀ X ∈ 𝔤, NormedSpace.exp (-X) ∈ G := by
    intro X hX
    simpa using (h𝔤 X).1 hX (-1)
  have hcancel : ∀ X : A, NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    intro X
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  filter_upwards [himg]
  rintro g ⟨Z, hZ, rfl⟩ hgG
  have hpg : p Z ∈ 𝔤 := hk (hpk Z)
  have hqg : q Z ∈ 𝔤 := hb (hqb Z)
  have hrG : NormedSpace.exp (r Z) ∈ G := by
    have h2 := hmul _ (hneg _ hqg) _ (hmul _ (hneg _ hpg) _ hgG)
    have h3 : NormedSpace.exp (-(q Z)) * (NormedSpace.exp (-(p Z)) * Φ Z) = NormedSpace.exp (r Z) := by
      simp only [Φ]
      rw [← mul_assoc (NormedSpace.exp (-(p Z))), ← mul_assoc (NormedSpace.exp (-(p Z))), hcancel,
        one_mul, ← mul_assoc, hcancel, one_mul]
    rwa [h3] at h2
  have hr𝔤 : r Z ∈ 𝔨 ⊔ 𝔟 := hg (hVG _ hZ hrG)
  have hrz : r Z = 0 := hr0 Z hr𝔤
  refine ⟨p Z, hpk Z, q Z, hqb Z, ?_⟩
  simp [Φ, hrz]

end Banach

theorem eventually_exp_mul_exp_of_isLinRed {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hG : GlobalTheory.LinRed.IsLinRed G) (𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (hV : ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  obtain ⟨V, hV, hVG⟩ := hV
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedRing
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedSpace
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { (inferInstance : Algebra ℝ (Matrix (Fin n) (Fin n) ℂ)) with
      norm_smul_le := fun t X => by
        have : t • X = (t : ℂ) • X := by ext a b; simp
        rw [this, norm_smul]
        simp }
  exact eventually_exp_mul_exp hG.mul_mem h𝔤 hV hVG hk hb hg

end GlobalTheory.CompanionTheory.ClosedSubgroup
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechDelta

theorem terminalEquiv_δ {X : TopCat.{0}} {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ)
    (y : Sheaf.H'.{0} S.X₃ n (⊤ : Opens X)) :
    GlobalTheory.SiteCoh.terminalEquiv S.X₁ (n + 1) isTerminalTop (GlobalTheory.SheafLES.δ hS n ⊤ y) =
      H.δ hS n (n + 1) rfl (GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y) := by
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (GlobalTheory.SiteCoh.freeSheafIsoConst isTerminalTop).inv) y hS.extClass (zero_add n) rfl (by omega)).symm

theorem hPull_δ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n) :
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  obtain ⟨y, rfl⟩ : ∃ y, GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  rw [← terminalEquiv_δ hS n y]
  dsimp only [hPull, GlobalTheory.SheafPull.pull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  erw [GlobalTheory.SheafPull.sitePull_δ (TopologicalSpace.Opens.map f) hS hS' α n]
  exact terminalEquiv_δ hS' n _

end GlobalTheory.CompanionTheory.CechDelta
end

