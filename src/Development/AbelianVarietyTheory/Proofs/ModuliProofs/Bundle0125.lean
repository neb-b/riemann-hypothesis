module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem surjectiveOnStalks_of_dedekind_overring {O O' F : Type} [CommRing O] [IsDedekindDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] [CommRing O'] (β' : O' →+* F) (b : O →+* O') (hβ' : Function.Injective β')
    (h : ∀ x, β' (b x) = algebraMap O F x) : b.SurjectiveOnStalks := by
  intro P' hP'
  rw [RingHom.surjective_localRingHom_iff]
  intro s
  obtain ⟨x, y, hy, hs⟩ := IsFractionRing.div_surjective (A := O) (β' s)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap O F y ≠ 0 := fun e => hy0 (IsFractionRing.injective O F (by rw [e, map_zero]))
  have h1 : (1 : O') ∉ P' := P'.primeCompl.one_mem
  have key : ∀ u v : O, v * x = u * y → b v * s = b u := by
    intro u v e
    apply hβ'
    have e' := congrArg (algebraMap O F) e
    rw [map_mul, map_mul] at e'
    rw [map_mul, h, h, ← hs, ← mul_div_assoc, e', mul_div_assoc, div_self hyF, _root_.mul_one]
  by_cases hP : P'.comap b = ⊥
  · refine ⟨x, y, 1, h1, fun hm => hy0 ?_, by rw [_root_.one_mul, _root_.one_mul]; exact key x y (mul_comm _ _)⟩
    have : y ∈ P'.comap b := hm
    rwa [hP, Ideal.mem_bot] at this
  · have hd := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP
      (Localization.AtPrime (P'.comap b))
    have inj : Function.Injective (algebraMap O (Localization.AtPrime (P'.comap b))) :=
      IsLocalization.injective _ (P'.comap b).primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap O (Localization.AtPrime (P'.comap b)) x) (algebraMap O _ y)
    obtain ⟨u, v, rfl⟩ := IsLocalization.exists_mk'_eq (P'.comap b).primeCompl c
    have hv : b v ∉ P' := v.2
    rcases hc with hc | hc
    · have e : u * x = v * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      have e' := key _ _ e
      refine ⟨v, u, 1, h1, fun hm => hv ?_, by rw [_root_.one_mul, _root_.one_mul]; exact e'⟩
      rw [← e']
      exact P'.mul_mem_right _ hm
    · have e : v * x = u * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      exact ⟨u, v, 1, h1, hv, by rw [_root_.one_mul, _root_.one_mul]; exact key _ _ e⟩

theorem flat_of_dedekind_of_injective {O O' : Type} [CommRing O] [IsDedekindDomain O] [CommRing O'] [IsDomain O']
    (b : O →+* O') (hb : Function.Injective b) : b.Flat := by
  algebraize [b]
  refine IsDedekindDomain.flat_iff_torsion_eq_bot.2 ?_
  rw [eq_bot_iff]
  rintro x ⟨a, ha⟩
  have ha' : b a * x = 0 := by
    rw [Submonoid.smul_def, Algebra.smul_def] at ha
    exact ha
  rcases mul_eq_zero.1 ha' with e | e
  · exact absurd (hb (by rw [e, map_zero])) (nonZeroDivisors.ne_zero a.2)
  · exact e

theorem isNormalScheme_of_flat_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [SurjectiveOnStalks f]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks f y
  obtain ⟨h₁, h₂⟩ := hX (f y)
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem Models.Cpt.exists_above_isIso_of_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  intro E _ _ _ H U F O _ _ c t β O' _ β' b C ν hν hβ hβ' hb
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, -⟩, -, hF'⟩ := hβ'
  have inj' : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  have hbx : ∀ x, β' (b x) = β x := fun x => congrArg (fun f : O →+* F => f x) hb
  have inj : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O F
  have injb : Function.Injective b := fun x y e => inj (by rw [← hbx, ← hbx, e])
  have hS : SurjectiveOnStalks (spMap b) := by
    letI := β.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2
      (surjectiveOnStalks_of_dedekind_overring β' b inj' hbx)
  have hFl : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact flat_of_dedekind_of_injective b injb
  have hS' : SurjectiveOnStalks (pullback.fst C.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip hS
  have hsp : spMap β' ≫ spMap b = spMap β := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hp : IsPullback (pullback.fst (pullback.snd C.s (spMap b)) (spMap β') ≫ pullback.fst C.s (spMap b))
      (pullback.snd (pullback.snd C.s (spMap b)) (spMap β')) C.s (spMap β) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hj : ((C.jQ ≫ hp.isoPullback.inv) ≫ pullback.fst (pullback.snd C.s (spMap b)) (spMap β')) ≫
      pullback.fst C.s (spMap b) = C.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, hp.isoPullback_inv_fst]
  obtain ⟨t', ⟨mu⟩⟩ : ∃ t' : SAB H (pullback C.s (spMap b)), Nonempty (SABMap t' C.t (pullback.fst C.s (spMap b))) := by
    obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b)) C.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t t' ((C.jQ ≫ hp.isoPullback.inv) ≫
      pullback.fst (pullback.snd C.s (spMap b)) (spMap β')), C.m.φ = m'.φ ≫ mu.φ := by
    have aux : ∀ (g : U ⟶ pullback C.s (spMap b)) (e : U ⟶ C.X) (n : SABMap t C.t e),
        g ≫ pullback.fst C.s (spMap b) = e → ∃ m' : SABMap t t' g, n.φ = m'.φ ≫ mu.φ := by
      rintro g e n rfl
      exact ObjMaps.exists_sab_cancel mu n
    exact aux _ _ C.m hj
  have := C.flat
  have := C.jQ_open
  have hr : Set.range (C.jQ ≫ hp.isoPullback.inv) = hp.isoPullback.hom ⁻¹' Set.range C.jQ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  have hiso : IsIso (pullback.lift (pullback.fst C.s (spMap b)) (pullback.snd C.s (spMap b)) pullback.condition) := by
    rw [pullback.lift_fst_snd]
    infer_instance
  refine ⟨⟨pullback C.s (spMap b), pullback.snd _ _,
    isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst C.s (spMap b)) C.normal,
    ProjSpace.isProjOver_pullback_snd b C.proj, inferInstance, C.jQ ≫ hp.isoPullback.inv, ?_, inferInstance, ?_, t', m', ?_⟩,
    ⟨pullback.fst _ _, pullback.condition, inferInstance, mu, ?_, ?_⟩, hiso⟩
  · rw [Category.assoc, hp.isoPullback_inv_snd, C.jQ_over]
  · rw [hr]
    exact C.jQ_dense.preimage hp.isoPullback.hom.isOpenEmbedding.isOpenMap
  · rw [hr, ← C.ab_gen]
    ext x
    simp only [Set.mem_preimage]
    rw [← abLocus_pullback abLocusOne C.t.semi mu.cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hp.isoPullback_hom_fst]
  · exact hj.trans (Category.id_comp _).symm
  · refine hm'.symm.trans ?_
    rw [hν, Category.id_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PeriodPoint

theorem exists_point_of_period : ThetaUnifAV → Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M
    : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin
    g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef
    : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
    ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef
    a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u
    : HolUnif P.A P.L g) (χ
    : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (P
    P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g →
    ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp
    k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
    : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫
    a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A]
    P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L)) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act
    : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B
    M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd
    B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_
    : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B
    ≫ act.act (H.bar a)] PP.L)) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P
    : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M
    : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x
    : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂
    P.A (M.pull ψ.left)) → Out.KTriv B M) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B
    : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n
    : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B
    M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat
    ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B
    M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M') → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin
    g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z +
    w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro _ laws cube tor hom adjW prim princ amp rep E _ _ _ H D l Xo σ g ty hpq hσ hty D' t P
    ⟨hp, hq, f, ν, htow, hiso, hsim, hζ, ht⟩ hP
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    exists_triple laws cube tor hom adjW prim princ amp D' ty P hP
  let Q : Out.PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hmul : ∀ (n : ℕ) a, 0 < n → u.ex ((n : ℂ)⁻¹ • P (n • a)) = 1 := fun n a hn => by
    rw [hker, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    exact ⟨a, rfl⟩
  have hadd : ∀ (n : ℕ) a b, u.ex ((n : ℂ)⁻¹ • P (f n (a + b))) =
      u.ex ((n : ℂ)⁻¹ • P (f n a)) * u.ex ((n : ℂ)⁻¹ • P (f n b)) := fun n a b => by
    rw [map_add (f := _), map_add (f := _), smul_add, u.ex_add]
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨κ, hκ₁, hκ₂, hκ₃⟩ := exists_halfLevel (D := D) l (fun a => u.ex ((l.M : ℂ)⁻¹ • P (f l.M a))) (hadd l.M)
    fun b => by rw [map_nsmul, hmul _ _ hM]
  let b : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o : Obj D l b (𝟙 (Sp ℂ)) :=
    { t := T, proper := hA.proper, ample := hamp, ktriv := hK
      eta := κ, eta_add := hκ₁, eta_ker := hκ₂
      etaA := fun a => u.ex ((l.A : ℂ)⁻¹ • P (f l.A a))
      etaA_add := hadd l.A
      etaA_ker := fun a => by rw [map_nsmul, hmul _ _ l.A_pos]
      geom := fun k _ _ x β hx => by
        obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
        refine ⟨?_, ?_⟩
        · rw [show b.ρ = H.rt0 from hσ]
          exact detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
            (fun i a => heig _ _ (T.act.hom a) (hact a) i) β
        · obtain ⟨I, hI₁, hI₂⟩ := exists_tateIso_of_periods laws E H D D' g ty P Q T.act u.ex f ν hpq hP u.ex_add
            u.ex_onto hker hact hW htow hiso hsim k β
          exact ⟨I, (hI₁ _).trans (congrArg β hζ.symm), fun a => (hI₂ _ a).symm,
            fun a ha => by rw [hκ₃ a ha]; exact (hI₂ _ a).symm⟩ }
  obtain ⟨y, ⟨hy, ⟨m⟩⟩, -⟩ := rep E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o inferInstance rfl rfl
  obtain ⟨e, he, hhol, he₁, he₂, he₃⟩ := exists_fibre_unif T Xo.univ.t y m.toSABMap u ht₁ ht₂
  have hlev : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, u.ex ((n : ℂ)⁻¹ • P (t a)) = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
    rintro n hn ⟨r, hr⟩ a
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left ((Nat.lcm_pos hM l.A_pos).trans_eq hr)
    obtain ⟨c, hc⟩ := htow n r hn hr0 a
    rw [ht, hr, hc, map_add (f := _), smul_add, u.ex_add, hmul _ _ hn, _root_.mul_one]
  refine ⟨y, e, hy.trans (Category.id_comp _), hP, hhol, fun z => (he₁ z).trans (hker z),
    fun a z => he₂ a z _ (hact a z), fun k a a₂ c hk hc => he₃ k _ _ _ (hW k a a₂ c hk hc),
    fun a ha => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · rw [he, hlev _ hM (Nat.dvd_lcm_left _ _), ← hκ₃ a ha]
    exact (m.eta a).symm
  · rw [he, hlev _ l.A_pos (Nat.dvd_lcm_right _ _)]
    exact (m.etaA a).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecLbPowDivNeZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowDominates

open LBGerm GlobalTheory.AbLaw GlobalTheory.TwistGen ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def chartPullTw (L N : LB X) (t : ℕ) : ChartPull (LB.div (lbPow L t) N) (tw (pw N (-1)) L (t : ℤ)) (𝟙 X) where
  idx p := (p.2, p.1 PUnit.unit)
  le _ _ hy := ⟨hy.2, mem_powChart.1 hy.1⟩
  g y p q hp hq := by
    refine (gm_div N (lbPow L t) (𝟙 X) y p q ⟨hp, hq⟩).trans (Eq.symm (Units.ext ?_))
    refine (gm_tw_g (pw N (-1)) L t y (p.2, p.1 PUnit.unit) (q.2, q.1 PUnit.unit)
      ⟨hp.2, mem_powChart.1 hp.1⟩ ⟨hq.2, mem_powChart.1 hq.1⟩).trans ?_
    rw [gm_lbPow_g t (𝟙 X) y p.1 q.1 hp.1 hq.1, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.mul_comm]
    refine congrArg Units.val (congrArg₂ (· * ·) rfl ?_)
    exact (map_zpow _ _ _).trans (zpow_neg_one _)

theorem exists_sec_div [CompactSpace X] [QuasiSeparatedSpace X] {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) {n : ℕ}
    (s : (lbPow L n).Sec) (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (t : ℕ) (u : (LB.div (lbPow L t) N).Sec), y ∈ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hN y
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := N.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hL s a
  obtain ⟨e, u, hu⟩ := exists_sec_of_le_chart (M := pw N (-1)) (isLB_pw hN (-1)) hL (n * m) (powSecFn σ)
    (fun z j j' hj hj' => by
      have hz : z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨n * m * e, chartSec (chartPullTw L N _) u, ?_⟩
  rw [nonzeroLocus_chartSec_id (chartPullTw L N _) u fun z j hj =>
    ⟨((fun _ => j.2 : PUnit → L.ι), j.1),
      (⟨mem_powChart.2 hj.2, hj.1⟩ : z ∈ powChart L (fun _ => j.2) ⊓ N.U j.1)⟩]
  exact hu hya

theorem exists_f_ne_zero {M : LB X} (u : M.Sec) {y : X} (hy : y ∈ nonzeroLocus u) : ∃ j, u.f j ≠ 0 := by
  have hy' : y ∈ ⨆ k, X.basicOpen (u.f k) := hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  refine ⟨k, fun h0 => ?_⟩
  rw [h0, Scheme.basicOpen_zero] at hk
  exact absurd hk (by simp)

end GlobalTheory.PowDominates

namespace GlobalTheory

open PowDominates

theorem exists_sec_lbPow_div_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  intro h K _ _ P N hN
  obtain ⟨m, s, hc, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨_, _⟩ := TwistGen.compact_quasiSeparated (isLB_lbPow P.isLB 4) s hc fun i => (hs i).1
  obtain ⟨y⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hc]; trivial)
  obtain ⟨t, u, hu⟩ := exists_sec_div P.isLB hN (s i) (hs i).1 y hi
  exact ⟨t, u, exists_f_ne_zero u hu⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDivSec

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def invLB (L : LB X) : LB X := ⟨L.1, L.U, fun i j => (L.g i j)⁻¹⟩

theorem isLB_invLB {L : LB X} (hL : L.IsLB) : (invLB L).IsLB := {
  cover := hL.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hL.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hL.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h }

theorem exists_sec_div (L M : LB X) (n t : ℕ) (u : LB.Sec (tw (invLB L) (lbPow M n) (t : ℤ))) :
    ∃ s : (LB.div (lbPow M (n * t)) L).Sec, nonzeroLocus u ≤ nonzeroLocus s := by
  have le : ∀ p : (PUnit → M.ι) × L.ι, powChart M p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ powChart M p.1 :=
    fun p y hy => ⟨hy.2, hy.1⟩
  let F : ∀ p : (PUnit → M.ι) × L.ι, Γ(X, powChart M p.1 ⊓ L.U p.2) := fun p =>
    resG X (le p) (show Γ(X, L.U p.2 ⊓ powChart M p.1) from u.f (p.2, p.1))
  have hF : ∀ (y : X) (p : (PUnit → M.ι) × L.ι), y ∈ powChart M p.1 ⊓ L.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f (p.2, p.1)) := fun y p hy => gs_res (𝟙 X) y (le p) hy _
  refine ⟨secOfGerm (M := LB.div (lbPow M (n * t)) L) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · have e₁ := gs_compat u (𝟙 X) y (j := (p.2, p.1)) (j' := (q.2, q.1)) (le p hp) (le q hq)
    have e₂ := TwistGen.gm_tw_g (invLB L) (lbPow M n) t y (p.2, p.1) (q.2, q.1) (le p hp) (le q hq)
    have e₃ := gm_lbPow_g (L := M) n (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₄ := gm_lbPow_g (L := M) (n * t) (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₅ := gm_div L (lbPow M (n * t)) (𝟙 X) y p q ⟨hp, hq⟩
    have e₆ : gm (𝟙 X) y ((invLB L).U p.2 ⊓ (invLB L).U q.2) ((invLB L).g p.2 q.2) =
        (gm (𝟙 X) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := map_inv _ _
    rw [e₄] at e₅
    dsimp only at e₂
    rw [e₃, e₆] at e₂
    refine (hF y p hp).trans (e₁.trans (congrArg₂ (· * ·) (e₂.trans ?_) (hF y q hq).symm))
    refine Eq.trans ?_ (congrArg Units.val e₅).symm
    rw [Units.val_mul, pow_mul, _root_.mul_comm]
    simp only [Units.val_pow_eq_pow_val]
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hp' : y ∈ powChart M p.2 ⊓ L.U p.1 := ⟨hp.2, hp.1⟩
    refine (mem_nonzeroLocus_iff_isUnit (M := LB.div (lbPow M (n * t)) L) _ (k := (p.2, p.1)) hp').2 ?_
    exact (congrArg IsUnit (hF y (p.2, p.1) hp')).mpr ((mem_nonzeroLocus_iff_isUnit u hp).1 hy)

theorem exists_sec_div_mem {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M) (x : X) :
    ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ x ∈ nonzeroLocus s := by
  have := hM.compactSpace
  have := hM.quasiSeparatedSpace
  obtain ⟨n, hn, σ, hx, ha⟩ := hM.exists_affine x
  obtain ⟨V, N, hV, h⟩ := TwistGen.exists_nhds (isLB_invLB hL) (isLB_lbPow hM.isLB n) σ ha x hx
  obtain ⟨u, hu⟩ := h 1
  obtain ⟨s, hs⟩ := exists_sec_div L M n (N + 1) u
  exact ⟨_, s, Nat.mul_pos hn (Nat.succ_pos N), hs (hu hV)⟩

theorem exists_sec_pow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  intro K _ A L M _ ⟨x⟩ hL hM hA
  obtain ⟨a, s, ha, hx⟩ := exists_sec_div_mem hL (isAmpleLB_of_relAmple_of_isAffine A hM hA) x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨a, s, ha, j, fun h => ?_⟩
  rw [h, Scheme.basicOpen_zero] at hj
  exact hj

end GlobalTheory.AmpleDivSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionConstantFamilyDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem torsion_section_const : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  intro _ P₀ A' _ ρ j hc k y y₀ hk hy hy₀ hyj
  letI := P₀.isAb.comm
  have hu : IsUnit ((k : ℕ) : Γ(Sp ℂ, ⊤)) := by
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    refine (MulEquiv.isUnit_map e.toMulEquiv).mp ?_
    have he : e.toMulEquiv (k : Γ(Sp ℂ, ⊤)) = (k : ℂ) := map_natCast e k
    rw [he]
    exact (Nat.cast_ne_zero.mpr hk).isUnit
  exact GlobalTheory.ConstTheta.torsion_const hc.1 hc.2.2 hu y y₀ hy hy₀ hyj.symm

end GlobalTheory.KS
end

