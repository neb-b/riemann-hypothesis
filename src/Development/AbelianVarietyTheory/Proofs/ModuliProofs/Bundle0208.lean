module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHermFormCurve
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.ExCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem weilIs_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (s' : Sp ℂ ⟶ S') (s : Sp ℂ ⟶ S) (hs : s = s' ≫ f) (k : ℤ) (x y : Over.mk s' ⟶ t'.G) (x₀ y₀ : Over.mk s ⟶ t.G)
    (c : ℂˣ) (hx : x₀.left = x.left ≫ m.φ) (hy : y₀.left = y.left ≫ m.φ) :
    Out.WeilIs t'.G t'.PP.L k x y (unitOn c) ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ (unitOn c) := by
  subst hs
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk s') k x y x₀ y₀ _ hx hy

theorem exists_isExp_of_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ₀ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {R K : Type} [CommRing R] [Field K] (f : R →+* K) (σ : K →+* ℂ)
    (B : PAT H (Sp R)) {y : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t y) (n : SABMap t B.t (spMap f))
    (hy : spMap σ ≫ y = FU.u i Pe) :
    ∃ eB : (Fin g → ℂ) → (Over.mk (spMap (σ.comp f)) ⟶ B.t.G), IsExp B (σ.comp f) (FU.Di i) ty Pe eB ∧
      ∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ t.G.hom = spMap σ ∧ x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left := by
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap σ)) (FU.u i Pe) hy.symm
  obtain ⟨q, hq⟩ := LiePull.exists_pushEquiv n.cart (Over.mk (spMap σ)) (spMap (σ.comp f)) (spMap_comp f σ).symm
  have hp' : ∀ z, (p.symm (FU.ex i Pe z)).left ≫ m.φ = (FU.ex i Pe z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => q (p.symm (FU.ex i Pe z)), ⟨hP, ?_, fun z w => ?_,
    q.surjective.comp (p.symm.surjective.comp (FU.ex_onto i Pe hP)), fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩, fun z => ⟨(p.symm (FU.ex i Pe z)).left, Over.w _, (hq _).symm, hp' z⟩⟩
  · have hpb := (IsPullback.of_hasPullback t.G.hom (spMap σ)).paste_horiz m.cart.1
    let c : (Fin g → ℂ) → (Sp ℂ ⟶ pullback t.G.hom (spMap σ)) := fun z =>
      pullback.lift (p.symm (FU.ex i Pe z)).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)
    have hc := ThetaPoint.isHolTo_fibre hpb c (fun z => pullback.lift_snd _ _ _) (by
      have e : (fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ m.cm.F) = fun z => (FU.ex i Pe z).left :=
        funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hp' z
      rw [e]
      exact ExpUniqFamily.isHolTo_ex FU i Pe hP)
    have e : (fun z => (q (p.symm (FU.ex i Pe z))).left) = fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ n.φ :=
      funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hq _
    rw [e]
    exact isHolTo_comp_hom hc _
  · beta_reduce
    rw [FU.ex_add i Pe hP, map_mul, map_mul]
  · exact (map_eq_one_iff q q.injective).trans ((map_eq_one_iff _ p.symm.injective).trans (FU.ex_ker i Pe hP z))
  · have e : p.symm (FU.ex i Pe z ≫ Xo.univ.t.act.act a) = p.symm (FU.ex i Pe z) ≫ t.act.act a := by
      rw [p.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
      exact congrArg (· ≫ _) (hp' z).symm
    apply Over.OverMorphism.ext
    beta_reduce
    rw [FU.ex_lin i Pe hP, e, Over.comp_left, hq, hq, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (n.act a)
  · exact (weilIs_iff n _ _ (spMap_comp f σ).symm k _ _ _ _ c (hq _) (hq _)).1
      ((weilIs_iff m _ _ hy.symm k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (FU.ex_weil i Pe hP k a b c hk hc))

section Comparison₂

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end Comparison₂

section CMStatement

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end CMStatement

section Tensor

end Tensor

section TensorStatement

variable {M : Type} [Field M] [NumberField M] {ω : 𝓞 M}

end TensorStatement

end GlobalTheory.CM.ExCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type}
    (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

theorem TObj.HasTh.unit_smul {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (H : t.HasTh x v) {c : R} (hc : IsUnit c) :
    t.HasTh x (c • v) := by
  have h := isThetaPt_unit_mul t.pol N' (T := Over.mk x) _ _ _
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) H
  unfold TObj.HasTh
  convert h using 2 with a
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem tmap_of_hasTh_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, H⟩ := _root_.GlobalTheory.ZM.exists_tObj_of_veryDense hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b em t t' v c hc hs hs' hv hv' => ?_⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  have hv'' : t'.HasTh (𝟙 _) v := by
    have h := hv'.unit_smul (IsUnit.mk0 c⁻¹ (inv_ne_zero hc))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have key : ∀ s : Sp ℂ ⟶ Sp o, s = spMap (RingHom.id ℂ) ≫ spMap em →
      ∀ t t' : TObj g ((n ^ j) ^ 2) J b s, t.Shape Mat κ → t'.Shape Mat κ →
        t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
    intro s hs t t' h1 h1' h2 h2'
    subst hs
    have hvd : VeryDense (objPrimes b Mat κ em v) := by
      intro q f hq hf
      have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
      subst hq0
      refine ⟨⊥, ⟨ℂ, inferInstance, inferInstance, RingHom.id ℂ, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
      exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id ℂ).injective
    obtain ⟨t₀, -, h₀⟩ := H j hj o b ℂ em v hvd
    have m := h₀ ℂ (RingHom.id ℂ) t h1 h2
    have m' := h₀ ℂ (RingHom.id ℂ) t' h1' h2'
    refine ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
    rwa [Category.id_comp]
  exact key _ (by rw [hid, Category.id_comp]) t t' hs hs' hv hv''

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam GlobalTheory.AbLaw GlobalTheory.Biadditive

namespace GlobalTheory.IsogenyBitriv

theorem triv_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {G : Type} [Monoid G] (F : G → (Y ⟶ X))
    (h₁ : Triv (L.pull (F 1)))
    (hm : ∀ x x', Triv (LB.LinComb L (K := Fin 3) ![F (x * x'), F x, F x'] ![1, -1, -1])) (x : G) (n : ℕ) :
    Triv (LB.LinComb L (K := Fin 2) ![F (x ^ n), F x] ![1, -(n : ℤ)]) := by
  induction n with
  | zero =>
    refine triv_of_formal hL h₁ fun U _ k => ?_
    simp [Fin.prod_univ_two]
  | succ n ih =>
    refine triv_of_formal hL (triv_mul (hm (x ^ n) x) ih) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_sum_type, pow_succ, zpow_add, mul_comm,
      mul_left_comm, _root_.mul_assoc]
    exact Additive.ofMul.injective (by simp only [ofMul_mul, ofMul_inv]; abel)

theorem triv_of_triv_pull_isogeny :
    ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro S _ A B _ _ _ _ ψ M N n hA hB hM hamp hN hψ hfin het hsurj _ hn hker h₁ h₂ h₃
  have hG : Out.GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨mA, -, -, sA⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have := hA.proper
  have := hB.smooth
  obtain ⟨ψ', hψ', e, -⟩ := GlobalTheory.HkFactor.exists_unique_factor S A B A ψ ((𝟙 A) ^ n) hA hB inferInstance hψ
    hfin het hsurj mA (fun k _ _ t x hx => by rw [MonObj.comp_pow, Category.comp_id]; exact hker k t x hx)
  have e' : ψ' ≫ ψ = (𝟙 B) ^ n := by
    have : Epi ψ.left := Flat.epi_of_flat_of_surjective ψ.left
    have : Epi ψ := Over.epi_of_epi_left ψ
    rw [← cancel_epi ψ, ← Category.assoc, e, MonObj.pow_comp, MonObj.comp_pow, Category.comp_id,
      Category.id_comp]
  have a₁ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift 1 y).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift y 1).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have key : ∀ {T : Over S} (a : T ⟶ A) (y : T ⟶ B), Triv (N.pull (lift ((a ≫ ψ) ^ n) y).left) := by
    intro T a y
    have bi := biadditive_of_triv_axes hG S B M hB hM hamp N hN h₁ h₂ T
    have p₁ := triv_pow hN (fun x : T ⟶ B => (lift x y).left) (a₁ y) (fun x x' => (bi x x' y).1) (a ≫ ψ) n
    have p₂ := triv_pow hN (fun x : T ⟶ B => (lift (a ≫ ψ) x).left) (a₂ _)
      (fun x x' => (bi x x' (a ≫ ψ)).2) y n
    have p₃ : Triv (N.pull (lift (a ≫ ψ) (y ^ n)).left) := by
      have := triv_pull_comp h₃ (lift a (y ≫ ψ')).left
      rwa [← Over.comp_left, lift_map, Category.assoc, e', MonObj.comp_pow, Category.comp_id] at this
    refine triv_of_formal hN (triv_mul (triv_mul p₁ (triv_inv p₂)) p₃) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fintype.prod_sum_type, _root_.mul_assoc]
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have hp : IsPullback (snd B B).left (fst B B).left B.hom B.hom :=
    (IsPullback.of_hasPullback B.hom B.hom).flip
  refine GlobalTheory.seesaw_reduced_of_dense hG S B M hB hM hamp B.left (B ⊗ B).left B.hom (snd B B).left
    (fst B B).left N hp hN ?_ (lift (𝟙 B) (1 : B ⟶ B)).left ?_ h₂
  · intro p
    refine subset_closure ?_
    have : Surjective ((𝟙 A ^ n) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
    obtain ⟨a, ha⟩ := ((𝟙 A ^ n) ≫ ψ).left.surjective p
    have hr : Set.range (A.left.fromSpecResidueField a) = {a} := Scheme.range_fromSpecResidueField _
    obtain ⟨z, hz⟩ := hr.ge rfl
    let j := A.left.fromSpecResidueField a
    let g := j ≫ ((𝟙 A ^ n) ≫ ψ).left
    refine ⟨A.left.residueField a, inferInstance, g, _, _, _, ⟨z, ?_⟩,
      IsPullback.of_hasPullback (fst B B).left g, ?_⟩
    · exact (congrArg (fun w => ((𝟙 A ^ n) ≫ ψ).left w) hz).trans ha
    · let ρ := pullback.fst (fst B B).left g
      let T : Over S := Over.mk (ρ ≫ (B ⊗ B).hom)
      let r : T ⟶ B ⊗ B := Over.homMk ρ rfl
      let b : T ⟶ A := Over.homMk (pullback.snd (fst B B).left g ≫ j) (by
        have c := congrArg (· ≫ B.hom) (pullback.condition (f := (fst B B).left) (g := g))
        simp only [g, Category.assoc, Over.w] at c
        exact (Category.assoc _ _ _).trans c.symm)
      have hr : r ≫ fst B B = (b ≫ ψ) ^ n := by
        have : (b ≫ ψ) ^ n = b ≫ (𝟙 A ^ n) ≫ ψ := by
          rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
        rw [this]
        apply Over.OverMorphism.ext
        exact pullback.condition.trans (Category.assoc _ _ _).symm
      have := key b (r ≫ snd B B)
      rw [← hr, lift_comp_fst_snd] at this
      exact this
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory.IsogenyBitriv
end

