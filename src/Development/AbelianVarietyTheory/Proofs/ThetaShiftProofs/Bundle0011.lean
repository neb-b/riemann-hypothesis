module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisOfIsExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem exists_basis_of_isExtension {K L : Type} [Field K] [Field L] [Algebra K L] {V W : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] {g : V →ₛₗ[algebraMap K L] W} (hg : IsExtension g) {I : Type}
    (v : Module.Basis I K V) : ∃ B : Module.Basis I L W, ∀ i, B i = g (v i) := by
  refine ⟨Module.Basis.mk (linearIndependent_of_isExtension hg v.linearIndependent) ?_,
    fun i => Module.Basis.mk_apply _ _ i⟩
  rw [← hg.span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (Set.range v) := v.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_basis_of_components {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M] {C : Type}
    [Finite C] {W : C → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module L (W x)] (p : ∀ x, M →ₗ[L] W x)
    (inj : ∀ m, (∀ x, p x m = 0) → m = 0) {Idx : C → Type} (bs : ∀ x, Module.Basis (Idx x) L (W x))
    (v : ∀ x, Idx x → M) (h₁ : ∀ x i, p x (v x i) = bs x i) (h₂ : ∀ x y i, y ≠ x → p y (v x i) = 0) :
    ∃ B : Module.Basis (Σ x, Idx x) L M, ∀ x i, B ⟨x, i⟩ = v x i := by
  classical
  have := Fintype.ofFinite C
  have key : ∀ x i, LinearMap.pi p (v x i) = Pi.basis bs ⟨x, i⟩ := fun x i => by
    rw [Pi.basis_apply]
    funext y
    by_cases h : y = x
    · subst h
      rw [LinearMap.pi_apply, h₁, Pi.single_eq_same]
    · rw [LinearMap.pi_apply, h₂ x y i h, Pi.single_eq_of_ne h]
  have hb : Function.Bijective (LinearMap.pi p) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => inj m fun x => congrFun hm x, ?_⟩
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basis bs).span_eq, Submodule.span_le]
    rintro _ ⟨⟨x, i⟩, rfl⟩
    exact ⟨v x i, key x i⟩
  refine ⟨(Pi.basis bs).map (LinearEquiv.ofBijective _ hb).symm, fun x i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.symm_apply_eq]
  exact (key x i).symm

theorem finite_of_reps {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {j : ℕ} (hj : 1 ≤ j) {C : Type}
    (rep : C → X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α) : Finite C := by
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X (show j ≠ 0 by omega)
  refine Finite.of_injective
    (fun x => (QuotientAddGroup.mk (rep x) : X ⧸ (nsmulAddMonoidHom j : X →+ X).range)) fun x y h => ?_
  obtain ⟨mu, hmu⟩ := QuotientAddGroup.eq.1 h
  refine (hrep (rep y)).unique ⟨mu, ?_⟩ ⟨0, by rw [smul_zero, add_zero]⟩
  rw [show j • mu = -rep x + rep y from hmu, add_neg_cancel_left]

theorem exists_basis_constFam {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) :
    ∃ B : Module.Basis (Σ x, Idx x) F (Fam P.toPre F j),
      ∀ x i, B ⟨x, i⟩ = constFam hW F hG hj (rep x) (bas x i) := by
  let _ : Algebra k F := (constF k F).toAlgebra
  have := finite_of_reps hj rep hrep
  choose bs hbs using fun x => exists_basis_of_isExtension (isExtension_pullF hW F j (rep x)) (bas x)
  refine exists_basis_of_components (fun x => famComp P.toPre F j (e (rep x))) (fun m hm => ?_) bs _
    (fun x i => (constFam_self hW F hG hj _ _).trans (hbs x i).symm) (fun x y i h => ?_)
  · refine fam_ext fun χ i => ?_
    obtain ⟨x, ⟨mu, hmu⟩, -⟩ := hrep (e.symm χ)
    have hχ : ∃ nu, e (rep x) + j • nu = χ :=
      ⟨e mu, by rw [← map_nsmul, ← map_add (f := _), hmu, LinearEquiv.apply_symm_apply]⟩
    exact congrArg (fun q => LB.Sec.f q i) (FamFree.eq_of_eq_add_nsmul hG m 0 hχ (hm x))
  · refine constFam_off hW F hG hj _ _ _ fun mu hmu => h ?_
    refine (hrep (rep y)).unique ⟨0, by rw [smul_zero, add_zero]⟩ ⟨e.symm mu, e.injective ?_⟩
    rw [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, hmu]

end GlobalTheory.ConstFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem pullOver_injective_of_dominant {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' : Scheme.{0}}
    {π : Y ⟶ Spec (CommRingCat.of R)} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ)
    {π' : Y' ⟶ Spec (CommRingCat.of R')} {g : R →+* R'} {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom g)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p] : Function.Injective (pullOver L ε hp hφ) := by
  intro s t h
  refine SecOver.ext _ _ fun i => p.app_injective _ (fn_ext fun y hy => ?_)
  have e := congrArg (fun q : SecOver π' (LB.LinComb L φ' ε) => gs (𝟙 _) y _ (LB.Sec.f q i)) h
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L φ' i := (wchart_eq hφ i).ge hy
  exact (gs_pull _ _ y _ hy _).trans ((gs_pullFn _ _ _ _ y hy').symm.trans (e.trans
    ((gs_pullFn _ _ _ _ y hy').trans (gs_pull _ _ y _ hy _).symm)))

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {j n : ℕ}

theorem expandsAt_smul (a : R)
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (a • σ : SecOver G.hom _) (a • f : ∀ χ, SecBMod D.toPre j χ) :=
  expandsAt_secIsMul R I D A G U n j a σ _ f _ (fun _ => rfl) (fun _ _ => rfl) h

theorem expandsAt_zero
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (0 : SecOver G.hom _) (0 : ∀ χ, SecBMod D.toPre j χ) := by
  have e₁ : (0 : R) • σ = 0 := zero_smul R σ
  have e₂ : (0 : R) • f = 0 := zero_smul R f
  exact e₁ ▸ e₂ ▸ expandsAt_smul U (0 : R) h

theorem expandsAt_add
    {σ τ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f g : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) (h' : U.ExpandsAt n j τ g) :
    U.ExpandsAt n j (σ + τ : SecOver G.hom _) (f + g : ∀ χ, SecBMod D.toPre j χ) := by
  refine expandsAt_sub R I D A G U n j σ ((-1 : R) • τ : SecOver G.hom _) _ f
    ((-1 : R) • g : ∀ χ, SecBMod D.toPre j χ) _ (fun i => ?_) (fun α i => ?_) h (expandsAt_smul U (-1) h')
  · show chartLin G.hom _ i (σ + τ) = chartLin G.hom _ i σ - chartLin G.hom _ i ((-1 : R) • τ)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]
  · show chartLin D.toPre.P.A.hom _ i (f α + g α) =
      chartLin D.toPre.P.A.hom _ i (f α) - chartLin D.toPre.P.A.hom _ i ((-1 : R) • g α)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]

end

theorem exists_smul_mem_span_of_expandsAt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) {j : ℕ} (hj : 1 ≤ j) {Idx : Type} (Φ : Idx → Fam D.toPre (FractionRing R) j)
    (hΦ : Submodule.span (FractionRing R) (Set.range Φ) = ⊤) (r : Idx → R) (hr : ∀ i, r i ≠ 0)
    (σ : Idx → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (f : Idx → ∀ χ, SecBMod D.toPre j χ)
    (hf : ∀ i χ, resF D.toPre (FractionRing R) j χ (f i χ) =
      toF (R := R) (FractionRing R) (r i) • famComp D.toPre (FractionRing R) j χ (Φ i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ t • s ∈ Submodule.span R (Set.range σ) := by
  have hsm := U.smooth
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have : IsDominant (jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hp : pullback.fst G.hom (jK R) ≫ G.hom =
      pullback.snd G.hom (jK R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (jK R)) k =
      pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  have hρ := pullOver_injective_of_dominant U.LG.L (fun _ : Fin 1 => (j : ℤ)) hp hφ
  set ρ := pullOver U.LG.L (fun _ : Fin 1 => (j : ℤ)) hp hφ with hρdef
  have hS := fun s₁ s₂ c => secScal_iff hp hφ (ε := fun _ : Fin 1 => (j : ℤ)) U.LG.isLB s₁ s₂
    (pullback.snd G.hom (jK R) ≫ jK R) (algebraMap R (FractionRing R)) rfl c
  have toF_eq : ∀ x : R, toF (R := R) (FractionRing R) x = algebraMap R (FractionRing R) x := fun _ => rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := (U.expand j hj).1 (ρ s)
  obtain ⟨-, -, σ₀, f₀, -, -, h₀⟩ := id hΦ₀
  have key : ∀ Ψ ∈ Submodule.span (FractionRing R) (Set.range Φ), ∃ t : R, t ≠ 0 ∧
      ∃ σ' ∈ Submodule.span R (Set.range σ), ∃ f' : ∀ χ, SecBMod D.toPre j χ,
        (∀ χ, resF D.toPre (FractionRing R) j χ (f' χ) =
          toF (R := R) (FractionRing R) t • famComp D.toPre (FractionRing R) j χ Ψ) ∧
        ∀ n, U.toUnifPre.ExpandsAt n j σ' f' := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨r i, hr i, σ i, Submodule.subset_span ⟨i, rfl⟩, f i, hf i, hE i⟩
    | zero =>
      refine ⟨1, one_ne_zero, 0, zero_mem _, 0, fun χ => by simp, fun n => ?_⟩
      exact expandsAt_zero U.toUnifPre (σ := σ₀) (f := f₀) (h₀ n)
    | add x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, σ₁, m₁, f₁, e₁, E₁⟩ := hx
      obtain ⟨t₂, ht₂, σ₂, m₂, f₂, e₂, E₂⟩ := hy
      refine ⟨t₁ * t₂, mul_ne_zero ht₁ ht₂, t₂ • σ₁ + t₁ • σ₂,
        add_mem (Submodule.smul_mem _ _ m₁) (Submodule.smul_mem _ _ m₂), t₂ • f₁ + t₁ • f₂, fun χ => ?_,
        fun n => expandsAt_add _ (expandsAt_smul _ _ (E₁ n)) (expandsAt_smul _ _ (E₂ n))⟩
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, map_add (f := _), map_smulₛₗ, map_smulₛₗ, e₁, e₂, map_add (f := _), map_mul,
        smul_add, smul_smul, smul_smul, mul_comm]
    | smul a x _ hx =>
      obtain ⟨t, ht, σ₁, m₁, f₁, e₁, E₁⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
      have hv' : algebraMap R (FractionRing R) v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero _).symm))
      refine ⟨t * v, mul_ne_zero ht hv0, u • σ₁, Submodule.smul_mem _ _ m₁, u • f₁, fun χ => ?_,
        fun n => expandsAt_smul _ _ (E₁ n)⟩
      rw [Pi.smul_apply, map_smulₛₗ, e₁, map_smul, smul_smul, smul_smul, map_mul, toF_eq, toF_eq, toF_eq]
      congr 1
      field_simp
  obtain ⟨t, ht, σ', m, f', e, E⟩ := key Φ₀ (hΦ ▸ Submodule.mem_top)
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := fun h => ht (hinj (h.trans (map_zero _).symm))
  have hX : U.toUnifPre.Expands j ((algebraMap R (FractionRing R) t)⁻¹ • ρ σ' : SecOver _ _) Φ₀ :=
    ⟨t, ht, σ', f', (hS _ _ _).2 (by rw [smul_inv_smul₀ ht']),
      fun χ => (secScal_iff_resF D.toPre (FractionRing R) _ _ _).2 (e χ), E⟩
  have hu : ((algebraMap R (FractionRing R) t)⁻¹ • ρ σ' : SecOver _ _) = ρ s :=
    ((U.expand j hj).2 Φ₀).unique hX hΦ₀
  refine ⟨t, ht, ?_⟩
  have : t • s = σ' := hρ (by rw [map_smulₛₗ, ← hu, smul_inv_smul₀ ht'])
  rwa [this]

end GlobalTheory.ConstFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegerRingSmulMemSubmodule
section
namespace GlobalTheory.SubmoduleScalarClosure

open NumberField

theorem int_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (m : ℤ) :
    (m : E) • x ∈ L := by
  have h := L.smul_mem (m : 𝓞 E) hx
  rwa [← algebraMap_smul E (m : 𝓞 E) x, map_intCast] at h

theorem integer_ring_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (a : 𝓞 E) :
    (a : E) • x ∈ L := by
  have h := L.smul_mem a hx
  rwa [← algebraMap_smul E a x] at h

theorem main {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by

  let S : Submodule E (Fin r → E) :=
    { carrier := {w | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • w ∈ X.Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩
        refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
        have h := X.Λ.add_mem (int_smul_mem_submodule X.Λ ha k) (int_smul_mem_submodule X.Λ hb n)
        convert h using 1
        rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (k : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨n, hn, hw⟩

        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
        refine ⟨d * n, mul_ne_zero hd hn, ?_⟩
        have h := integer_ring_smul_mem_submodule X.Λ hw ⟨d • c, hint⟩
        convert h using 1
        show _ = (d • c) • ((n : E) • w)
        rw [smul_smul, smul_smul, zsmul_eq_mul]
        congr 1
        push_cast
        ring }
  have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ S :=
    Submodule.span_le.mpr fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [X.Λ_span] at hle
  obtain ⟨n, hn, h⟩ := hle (Submodule.mem_top : v ∈ ⊤)
  exact ⟨n, hn, h⟩

end GlobalTheory.SubmoduleScalarClosure
end

