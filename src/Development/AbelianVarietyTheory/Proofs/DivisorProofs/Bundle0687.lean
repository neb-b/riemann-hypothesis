module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalBoundOfPeriodClass
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_bound_glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  intro I _ g Λ _ F B _ X s σ K hK r f per hc
  have hc' : GlobalTheory.CatCoh.H1.mk K.Oc (r.coef.pullbackOneCocycle f.1) = GlobalTheory.CatCoh.H1.mk K.Oc (K.perZ per) := hc
  obtain ⟨q, hq⟩ := GlobalTheory.CatCoh.H1.mk_eq_mk.1 hc'
  have key : ∀ (l : Λ) (k k' : K.K) (h : K.le l k' k),
      Charts.sh h (q (K.triv k)) = q (K.triv k') + K.cst k' (per l) := by
    intro l k k' h
    have e := congrFun (congrFun (congrFun hq (K.triv k)) (K.triv k')) (Charts.ptHom (K.triv k') h)
    have h0 : (r.coef.pullbackOneCocycle f.1).1 _ _ (Charts.ptHom (K.triv k') h) = 0 :=
      f.2 (r.functor.map (Charts.ptHom (K.triv k') h)) rfl rfl
    rw [GlobalTheory.CatCoh.amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0, zero_sub] at e
    change q (K.triv k') - Charts.sh h (q (K.triv k)) = -K.cst k' (per l) at e
    linear_combination -e
  obtain ⟨G, hGa, hG, hsh, -⟩ := Charts.glue K hK (fun k ↦ q (K.triv k))
    (fun k k' h ↦ by rw [key 0 k k' h, map_zero, map_zero, add_zero])
  exact ⟨q, G, hq, hGa, hG, fun l p hp ↦ hsh l (per l) (fun k k' h ↦ key l k k' h) p hp⟩

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHom
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem perCl_add' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (p q r : Λ →+ Hol F.V) (h : ∀ l, r l = p l + q l) : K.perCl r = K.perCl p + K.perCl q := by
  unfold Charts.perCl
  rw [← map_add (f := _)]
  congr 1
  refine Subtype.ext ?_
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = algebraMap (Hol F.V) T'.C (p f.deg) + algebraMap (Hol F.V) T'.C (q f.deg)
  rw [h]
  exact (algebraMap (Hol F.V) T'.C).map_add _ _

theorem perCl_smul' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (a : Hol F.V) (p r : Λ →+ Hol F.V) (h : ∀ l, r l = a * p l) : K.perCl r = a • K.perCl p := by
  refine Eq.trans ?_ ((H1.mk K.Oc).map_smul a (K.perZ p))
  refine congrArg (H1.mk K.Oc) (Subtype.ext ?_)
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = a • algebraMap (Hol F.V) T'.C (p f.deg)
  rw [h, map_mul, Algebra.smul_def]

attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain in
theorem hol_point (f : Hol (⊤ : Opens (Empty → ℂ))) : algebraMap ℂ _ (f.fn 0) = f :=
  Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Subsingleton.elim p 0]

theorem pHom_of (hE : PExist) (hU : PUniq) : PHom := by
  intro A _ g hA L u
  have : IsProper A.hom := hA.proper
  have : IsSeparated (A.hom ≫ 𝟙 _) := inferInstance
  have hB : (fibUnif u).Based := by
    let f : Sp ℂ ⟶ A.left := (u.ex 0).left
    have hs : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := (A.left.isBasis_affineOpens).exists_subset_of_mem_open
      (Set.mem_univ (f pt)) isOpen_univ
    refine ⟨U, hU, fun z _ q _ ↦ ?_⟩
    rw [Subsingleton.elim q pt]
    exact hx
  choose per hper using fun c : primDR A ↦ hE _ _ _ _ _ _ _ _ (fibUnif u) hB c.1
  have hadd : ∀ c c' : primDR A, per (c + c') = per c + per c' := fun c c' ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (c + c')) fun K r hr ↦ by
      rw [perCl_add' K (per c) (per c') _ fun _ ↦ rfl, ← hper c K r hr, ← hper c' K r hr, ← map_add (f := _)]
      rfl
  have hsmul : ∀ (a : ℂ) (c : primDR A), per (a • c) =
      (AddMonoidHom.mulLeft (algebraMap ℂ (Hol (fibFam u).V) a)).comp (per c) := fun a c ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (a • c)) fun K r hr ↦ by
      rw [perCl_smul' K (algebraMap ℂ (Hol (fibFam u).V) a) (per c) _ fun _ ↦ rfl, ← hper c K r hr, ← map_smulₛₗ]
      rfl
  let ev : Hol (fibFam u).V →ₐ[ℂ] ℂ := Hol.ev 0 trivial
  refine ⟨{ toFun x :=
              { toFun c := ev (per c x)
                map_add' c c' := by rw [hadd, AddMonoidHom.add_apply, map_add (f := _)]
                map_smul' a c := by
                  rw [hsmul]
                  change ev (algebraMap ℂ _ a * per c x) = a * _
                  rw [map_mul, AlgHom.commutes]; rfl }
            map_zero' := LinearMap.ext fun c ↦ by
              change ev (per c 0) = 0
              rw [map_zero, map_zero]
            map_add' x y := LinearMap.ext fun c ↦ by
              change ev (per c (x + y)) = ev (per c x) + ev (per c y)
              rw [map_add (f := _), map_add (f := _)] }, fun c ↦ ?_⟩
  convert hper c using 1
  refine AddMonoidHom.ext fun x ↦ ?_
  change algebraMap ℂ (Hol (fibFam u).V) (ev (per c x)) = per c x
  exact (congrArg _ (Hol.ev_apply (W := (fibFam u).V) 0 trivial (per c x))).trans (hol_point _)

theorem pHom : PHom := pHom_of _root_.GlobalTheory.AnPer.periods_exist _root_.GlobalTheory.AnPer.period_unique

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianScheme
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.SqLift

theorem exists_intermediate_grpPullback : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  intro R R₁ R₀ _ _ _ ρ π₁ g A₀ _ A _ i h hA hg
  have e : spMap (π₁.comp ρ) = spMap π₁ ≫ spMap ρ := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := isGrpPullback_pullback A (spMap ρ)
  have hw : i ≫ A.hom = (A₀.hom ≫ spMap π₁) ≫ spMap ρ := by
    rw [h.1.w, e, Category.assoc]
  let i₁ : A₀.left ⟶ ((Over.pullback (spMap ρ)).obj A).left := h₂.1.lift i (A₀.hom ≫ spMap π₁) hw
  have c₁ : i₁ ≫ Limits.pullback.fst A.hom (spMap ρ) = i := h₂.1.lift_fst _ _ _
  have c₂ : i₁ ≫ ((Over.pullback (spMap ρ)).obj A).hom = A₀.hom ≫ spMap π₁ := h₂.1.lift_snd _ _ _
  have h₁ : IsGrpPullback A₀ ((Over.pullback (spMap ρ)).obj A) (spMap π₁) i₁ :=
    h₂.cancel (h.congr e c₁.symm) c₂
  refine ⟨(Over.pullback (spMap ρ)).obj A, Functor.grpObjObj, i₁, Limits.pullback.fst A.hom (spMap ρ), h₁, h₂, c₁,
    isAbelianScheme_pullback_obj (spMap ρ) A hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStepNilExp
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def prods (κ : DividedPowers I) (m : ℕ) : Set R :=
  {x | ∃ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ κ.dpow p.1 p.2).prod}

theorem prod_mem (κ : DividedPowers I) : ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) →
    1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod ∈ I := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro hl hs
    have hp : p.2 ∈ I := hl p (by simp)
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h] at hs
      exact I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))
    · exact I.mul_mem_right _ (κ.dpow_mem (by omega) hp)

theorem dpow_prod_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N + 1 ≤ (l.map Prod.fst).sum →
      ∀ n, 2 ≤ n → κ.dpow n (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p l ih =>
    intro hl hs n hn
    have hp : p.2 ∈ I := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ I := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, κ.dpow_zero hp, _root_.one_mul]
      exact ih hl' (by omega) n hn
    · set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod
      have hm : κ.dpow p.1 p.2 ∈ I := κ.dpow_mem (by omega) hp
      have hz : P * κ.dpow (n * p.1) p.2 = 0 := by
        have := hN ((n * p.1, p.2) :: l) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hl' q hq) (by
          have : 2 * p.1 ≤ n * p.1 := Nat.mul_le_mul_right _ hn
          simp only [List.map_cons, List.sum_cons]
          omega)
        simpa [List.map_cons, List.prod_cons, mul_comm] using this
      rw [mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]

end GlobalTheory.SqLift.DPStep

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def idl (κ : DividedPowers I) (m : ℕ) : Ideal R := Ideal.span (prods κ m)

theorem idl_le (κ : DividedPowers I) (N : ℕ) : idl κ (N + 1) ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact prod_mem κ l hl (by omega)

theorem mul_idl_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) {a : R} (ha : a ∈ I) :
    ∀ b ∈ idl κ (N + 1), a * b = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    have := hN ((1, a) :: l) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)
    simpa [κ.dpow_one ha] using this
  | zero => exact mul_zero a
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

theorem idl_sq (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) : idl κ (N + 1) ^ 2 = 0 := by
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  rw [Ideal.mem_bot]
  exact mul_idl_eq_zero κ hN (idl_le κ N ha) b hb

theorem dpow_idl (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ x ∈ idl κ (N + 1), ∀ n, 2 ≤ n → κ.dpow n x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    exact dpow_prod_eq_zero κ hN l hl hs
  | zero => intro n hn; exact κ.dpow_eval_zero (by omega)
  | add x y hxm hym hx hy =>
    intro n hn
    have hxI := idl_le κ N hxm
    have hyI := idl_le κ N hym
    rw [κ.dpow_add hxI hyI]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : 2 ≤ k.1
    · rw [hx _ h1, MulZeroClass.zero_mul]
    by_cases h2 : 2 ≤ k.2
    · rw [hy _ h2, mul_zero]
    obtain ⟨a, b⟩ := k
    simp only at h1 h2 hk
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [κ.dpow_one hxI, κ.dpow_one hyI]
    exact mul_idl_eq_zero κ hN hxI y hym
  | smul r x hxm hx =>
    intro n hn
    rw [smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]

theorem isSubDPIdeal (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    IsSubDPIdeal κ (idl κ (N + 1) ⊓ I) := by
  refine DividedPowers.IsSubDPIdeal.mk inf_le_right ?_
  intro n hn j hj
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [κ.dpow_one hj.2]
    exact hj
  · rw [dpow_idl κ hN j hj.1 n h]
    exact Ideal.zero_mem _

end GlobalTheory.SqLift.DPStep


open GlobalTheory.SqLift.DPStep in
theorem GlobalTheory.SqLift.exists_isStep_nilExp :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ N : ℕ, NilExp κ (N + 2) →
    ∃ (R₁ : Type) (_ : CommRing R₁) (J : Ideal R) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀),
      IsStep κ π hJ ρ κ₁ π₁ ∧ NilExp κ₁ (N + 1) := by
  intro R R₀ _ _ I κ π hπ hker N hN
  set J := idl κ (N + 1)
  have hJI : J ≤ I := idl_le κ N
  have hsub := isSubDPIdeal κ hN
  have hz : ∀ a ∈ J, π a = 0 := fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha
  let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π hz
  have hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1) := by
    intro l hl hs
    have key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) →
        ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧
          (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod =
            Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpow p.1 p.2).prod := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
      | cons p l ih =>
        intro hl
        obtain ⟨l', hl', he, hp⟩ := ih fun q hq ↦ hl q (by simp [hq])
        obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
          (hl p (by simp))
        refine ⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ha
          · exact hl' q hq
        · simp only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]
          rw [DividedPowers.Quotient.dpow_apply κ hsub ha]
    obtain ⟨l', hl', he, hp⟩ := key l hl
    rw [hp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩
  refine ⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J),
    DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩
  refine
    { nil := ⟨N + 2, hN⟩
      nil₁ := ⟨N + 1, hnil1⟩
      surj := Ideal.Quotient.mk_surjective
      surj₁ := ?_
      comp := Ideal.Quotient.lift_comp_mk J π hz
      ker := hker
      kerJ := Ideal.mk_ker
      ker₁ := ?_
      dp := DividedPowers.Quotient.isDPMorphism κ hsub
      dpJ := ?_ }
  · intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩
  · ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]
  · refine (isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]
    · rw [RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_boundary_etale_cohomology : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  first | (exact @GlobalTheory.kummer_boundary) | (exact GlobalTheory.kummer_boundary) | (intros; apply GlobalTheory.kummer_boundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem PDPoly.liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    Q.liftAlg c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem PDPoly.exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  intro B _ Q
  refine ⟨fun C _ f c h0 hm ↦ ?_, ?_⟩
  · letI := f.toAlgebra
    exact ⟨(Q.liftAlg c h0 hm).toRingHom, fun b ↦ (Q.liftAlg c h0 hm).commutes b,
      fun n ↦ Q.liftAlg_e c h0 hm n⟩
  · let d : ℕ → B := fun n ↦ if n = 0 then 1 else 0
    have h0 : d 0 = 1 := by simp [d]
    have hm : ∀ m n, d m * d n = ((m + n).choose m : B) * d (m + n) := by
      intro m n
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [d, hm, hn]
    let ε := Q.liftAlg d h0 hm
    have hε : ∀ n, ε (Q.e n) = d n := Q.liftAlg_e d h0 hm
    have hmem : ∀ p, p - algebraMap B Q.P (ε p) ∈ Q.aug := by
      intro p
      have hp : p ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [hε]
        rcases n with _ | n
        · simp [d, Q.e_zero]
        · simpa [d] using Q.e_succ_mem_aug n
      | zero => simp
      | add x y _ _ hx hy =>
        have : x + y - algebraMap B Q.P (ε (x + y)) =
            (x - algebraMap B Q.P (ε x)) + (y - algebraMap B Q.P (ε y)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this]; exact add_mem hx hy
      | smul b x _ hx =>
        have : b • x - algebraMap B Q.P (ε (b • x)) = algebraMap B Q.P b * (x - algebraMap B Q.P (ε x)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [this]; exact Q.aug.mul_mem_left _ hx
    refine ⟨ε, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
    · have hle : Q.aug ≤ RingHom.ker ε := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        simp [RingHom.mem_ker, hε, d]
      exact RingHom.mem_ker.1 (hle hp)
    · have := hmem p
      rwa [hp, map_zero, sub_zero] at this

end GlobalTheory.PDA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morita_lattice_quotient_torsion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  first | (exact @GlobalTheory.EtLevMorita.exists_lev) | (exact GlobalTheory.EtLevMorita.exists_lev) | (intros; apply GlobalTheory.EtLevMorita.exists_lev <;> assumption)
end

