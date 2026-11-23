module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelOfPowEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem pow_eq_one_iff_of_isGrpPullback {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a' : X ⟶ S'} {a : X ⟶ S} (e : a = a' ≫ f)
    (x' : Over.mk a' ⟶ G') (x : Over.mk a ⟶ G) (hx : x.left = x'.left ≫ φ) (m : ℕ) :
    x' ^ m = 1 ↔ x ^ m = 1 := by
  subst e
  have hx' : x = pushHom h (Over.mk a') x' := Over.OverMorphism.ext hx
  have inj : Function.Injective (pushHom h (Over.mk a')) := fun y y' hy => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hy
    · rw [Over.w y, Over.w y']
  have : x ^ m = pushHom h (Over.mk a') (x' ^ m) := by rw [map_pow]; exact congrArg (· ^ m) hx'
  rw [this]
  exact (map_eq_one_iff _ inj).symm

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_label_of_pow_eq_one : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N →
    ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm h hh
  have := u.U.gen_hom
  have hw : h.left ≫ u.G.hom = 𝟙 _ := Over.w h
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (jK u.V ≫ h.left) (𝟙 _) (by rw [Category.assoc, hw]; simp)
  have hx₁ : x ≫ pullback.fst _ _ = jK u.V ≫ h.left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  let i : Sp (PadicAlgCl p) ⟶ Sp (FractionRing u.V) := spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))
  have : Epi i := epi_spMap_of_field _
  have hy : spMap y₀ = i ≫ spMap u.yK :=
    (congrArg spMap u.fac).symm.trans (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom _))
  have hψ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  let x' : Over.mk i ⟶ (Over.pullback (jK u.V)).obj u.G :=
    Over.homMk (i ≫ x) (by
      show (i ≫ x) ≫ pullback.snd _ _ = i
      rw [Category.assoc, hx₂, Category.comp_id])
  let t : Over.mk (i ≫ jK u.V) ⟶ baseOver (Sp u.V) := Over.homMk (i ≫ jK u.V) (by simp)
  have h₀ : (t ≫ h) ^ m = 1 := by
    have := (map_pow (preHom (G := u.G) t) h m).symm.trans ((congrArg _ hh).trans (map_one _))
    exact this
  have h₁ : x' ^ m = 1 :=
    (pow_eq_one_iff_of_isGrpPullback (isGrpPullback_pullback u.G (jK u.V)) rfl x' (t ≫ h) (by
      show (i ≫ jK u.V) ≫ h.left = (i ≫ x) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, hx₁]) m).2 h₀
  let z : Over.mk (spMap y₀) ⟶ ρ.P.A := Over.homMk (x'.left ≫ u.U.gen.hom.left ≫ u.φ) (by
    show (x'.left ≫ u.U.gen.hom.left ≫ u.φ) ≫ ρ.P.A.hom = spMap y₀
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w x', hy]; rfl)
  have h₂ : z ^ m = 1 := (pow_eq_one_iff_of_isGrpPullback hψ hy x' z rfl m).1 h₁
  have h₃ : z ^ (S.r * S.N) = 1 := by
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, h₂, one_pow]
  obtain ⟨b, hb, -⟩ := ρ.pt_bij (PadicAlgCl p) (spMap y₀) z h₃
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  refine ⟨b, ?_, x, hx₁, hx₂, ?_⟩
  · refine (ρ.pt_bij (PadicAlgCl p) (spMap y₀) 1 (one_pow _)).unique ?_ ?_
    · rw [hp, ← h₂, ← hb]
      exact map_pow (preHom (G := ρ.P.A) _) _ m
    · rw [h0]
      exact map_one (preHom (G := ρ.P.A) _)
  · have e : spMap y₀ ≫ (ρ.pt b).left = (i ≫ x) ≫ u.U.gen.hom.left ≫ u.φ := congrArg (fun w => w.left) hb
    rw [← cancel_epi i, ← Category.assoc i (spMap u.yK), ← hy, e, Category.assoc]

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ThetaReal.exists_monomial_matrices : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ b u s₀ hker hmul hcomm hfix hspan
  subst hN
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩

  let rep : (Fin g ⊕ Fin g → Fin m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j k => ((j k : ℕ) : ZMod (r * m ^ 2))
  let cls : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → Fin m) :=
    fun a k => ⟨(a k).val % m, Nat.mod_lt _ hm⟩
  haveI : NeZero (r * m ^ 2) := ⟨(Nat.mul_pos (by omega) (pow_pos (by omega) 2)).ne'⟩
  have hzero : ((r : ZMod (r * m ^ 2)) * (m : ZMod (r * m ^ 2)) ^ 2) = 0 := by
    exact_mod_cast ZMod.natCast_self (r * m ^ 2)
  have hcls : ∀ a, (r * m) • (a - rep (cls a)) = 0 := fun a => by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, nsmul_eq_mul, rep, cls]
    have hx : a k - (((a k).val % m : ℕ) : ZMod (r * m ^ 2)) = (((m * ((a k).val / m) : ℕ) : ZMod (r * m ^ 2))) := by
      rw [sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    rw [hx]
    push_cast
    linear_combination (((a k).val / m : ℕ) : ZMod (r * m ^ 2)) * hzero
  have hrep : ∀ j, cls (rep j) = j := fun j => by
    funext k
    apply Fin.ext
    have hlt : (j k : ℕ) < r * m ^ 2 :=
      lt_of_lt_of_le (j k).isLt (by nlinarith)
    simp only [rep, cls, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt (j k).isLt]
  have hrep0 : rep (cls 0) = 0 := by
    funext k
    simp [rep, cls]
  let s : (Fin g ⊕ Fin g → Fin m) → M := fun j => u (rep j) s₀
  have hA : ∀ a, ∃ c : ℕ, u a s₀ = f (ζ ^ c) • s (cls a) := fun a => by
    obtain ⟨e, he⟩ := hmul (rep (cls a)) (a - rep (cls a))
    have h1 := he s₀
    rw [hfix _ (hcls a), add_sub_cancel] at h1
    refine ⟨e * q, ?_⟩
    show u a s₀ = f (ζ ^ (e * q)) • u (rep (cls a)) s₀
    rw [h1, smul_smul, ← map_mul, ← pow_add]
    have : e * q + e = e * (q + 1) := by ring
    rw [this, pow_mul', hζ, one_pow, map_one, one_smul]
  have hB : ∀ a j, ∃ c : ℕ, u a (s j) = f (ζ ^ c) • s (cls (a + rep j)) := fun a j => by
    obtain ⟨e, he⟩ := hmul a (rep j)
    obtain ⟨c, hc⟩ := hA (a + rep j)
    refine ⟨e + c, ?_⟩
    show u a (u (rep j) s₀) = _
    rw [he, hc, smul_smul, ← map_mul, ← pow_add]
  have hcard : Fintype.card (Fin g ⊕ Fin g → Fin m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspan' : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hA a
    show u a s₀ ∈ Submodule.span A (Set.range s)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cls a, rfl⟩)
  let sB : Module.Basis (Fin g ⊕ Fin g → Fin m) A M := basisOfTopLeSpanOfCardEqFinrank s hspan'
    (by rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hsB : ⇑sB = s := coe_basisOfTopLeSpanOfCardEqFinrank s hspan' _
  choose c hc using hB
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o :=
    fun a => Matrix.of fun l i => if l = cls (a + rep i) then ζ ^ c a i else 0
  have hsum : ∀ a i, u a (sB i) = ∑ l, f (ρ a l i) • sB l := fun a i => by
    rw [hsB, hc a i]
    simp [ρ, apply_ite f, ite_smul]
  have hmat : ∀ a, LinearMap.toMatrix sB sB (u a) = (ρ a).map f := fun a => by
    ext l i
    rw [LinearMap.toMatrix_apply, hsum a i, Module.Basis.repr_sum_self, Matrix.map_apply]
  have hinj : Function.Injective (fun P : Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o => P.map f) :=
    Matrix.map_injective hf
  refine ⟨Fin g ⊕ Fin g → Fin m, inferInstance, ρ, sB, cls 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsB]
    show u (rep (cls 0)) s₀ = s₀
    rw [hrep0]
    exact hker 0 (smul_zero r) s₀
  · intro a ha
    have hid : u a = LinearMap.id := LinearMap.ext (hker a ha)
    apply hinj
    dsimp only
    rw [← hmat, hid, LinearMap.toMatrix_id]
    convert (Matrix.map_one f (map_zero f) (map_one f)).symm
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (funext x y; exact Subsingleton.elim _ _)
  · intro a a'
    obtain ⟨e, he⟩ := hmul a a'
    refine ⟨e, hinj ?_⟩
    have hcomp : u a ∘ₗ u a' = f (ζ ^ e) • u (a + a') := LinearMap.ext he
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, map_smul, hmat]
    ext l i
    simp [Matrix.map_apply, Matrix.smul_apply]
  · intro a a' ha
    apply hinj
    have hcomp : u a ∘ₗ u a' = u (a + a') := LinearMap.ext (hcomm a a' ha)
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, hmat]
  · exact hsum
  · intro i
    refine ⟨rep i, c (rep i) (cls 0), fun l => ?_⟩
    simp only [ρ, Matrix.of_apply]
    rw [hrep0, add_zero, hrep]
    split_ifs <;> rfl

end GlobalTheory.ThetaReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.ThetaReal.NormMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  have v : ∀ (y : T.left) (i : Fin 1 → L.ι), y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k :=
    fun y i hi => (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res (𝟙 T.left) y (rigT_le A L i) hi _).trans
      (gm_pull (𝟙 T.left) T.hom y _ (rigT_le A L i hi) (ρ.s fun _ => i 0))))
  refine SymLiftOdd.isGen_of_gm fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hi) (rigT_le A L (T := T) j hj)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  rw [v y i hi, v y j hj, trF, Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd]; rfl

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left)
        (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b)) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + -b + (a + b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left))
      (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b))) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigT_isGen hρ a) (rigT_isGen hρ b))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end GlobalTheory.ThetaReal.NormMul

namespace GlobalTheory.ThetaReal

theorem exists_normalised_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  intro hLaw S _ P rig hrig m N hN T
  subst hN
  have H := hLaw.mulPull _ P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α₁, hα₁, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left]) α₀ hα₀ (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  exact NormMul.exists_normalised P.isLB hrig m _ _ α₁ hα₁

end GlobalTheory.ThetaReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimScale

open TopologicalSpace GlobalTheory.HolHom

theorem chart_one_le {X : Scheme.{0}} (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun _ hy => Set.mem_iInter.1 hy 0

theorem exists_section_firstPower_restrict {X : Scheme.{0}} {L : LB X} (s : L.Sec) : ∃ t : H0 L 1, ∀ j,
    t.f j = (X.presheaf.map (homOfLE (chart_one_le L j)).op).hom (s.f (j 0)) := by
  have le := chart_one_le L
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (s.f (j 0)),
    fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun _ => rfl⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((SecPullIso.gs_sec_trans s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  simp only [valR_eq _ _ h, map_mul]

theorem valR_const {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (p : X ⟶ Sp A) (h : x ≫ p = 𝟙 _) (a : A) :
    valR x ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
  refine (valR_comp x p ⊤ _).symm.trans ?_
  rw [h, valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

theorem exists_primitive_scaling : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  intro V _ _ _ G _ hG M hM Y L hL ψ w hw θ hθ
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull ψ L (M.pull (pullback.fst G.hom (jK V))) w hL (LB.isLB_linComb hM _ _) hw θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hM r (by
    obtain ⟨x, hx⟩ := hθ
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    obtain ⟨a, ha⟩ := exists_chart (L := M.pull (pullback.fst G.hom (jK V))) (LB.isLB_linComb hM _ _) x
    have hk' := Y.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff ψ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
  obtain ⟨ϑ, hϑ⟩ := exists_section_firstPower_restrict σ
  refine ⟨ϑ, _, h0, ⟨x₀, Opens.mem_iSup.2 ⟨fun _ => b, ?_⟩, hx₀⟩, fun x hx i k hi hk => ?_⟩
  · refine (congrArg G.left.basicOpen (hϑ fun _ => b)).ge ?_
    exact (Scheme.basicOpen_res _ _ _).ge ⟨Set.mem_iInter.2 fun _ => G.left.basicOpen_le _ hb, hb⟩
  · have hi₁ : ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) :=
      fun z hz => Set.mem_iInter.2 fun _ => hi hz
    have hi₂ : ⊤ ≤ x ⁻¹ᵁ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) := fun z hz => mem_pull.2 (hi hz)
    have hW : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
      fun z hz => ⟨mem_pull.2 (hk hz), hi₂ hz⟩
    have l₁ : (L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) ≤ ψ ⁻¹ᵁ L.U k :=
      fun y hy => mem_pull.1 hy.1
    have e₁ : valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) =
        algebraMap V (FractionRing V) ϖ ^ n * valR x _ (r.f fun _ => i) := by
      refine (congrArg (valR _ _) (hϑ fun _ => i)).trans ?_
      refine (valR_res _ _ _ hi₁).trans ((valR_appLE x _ _ _ _ _ hi₂).symm.trans
        ((congrArg (valR x _) (hσ fun _ => i)).trans ((valR_mul' x _ hi₂ _ _).trans (congrArg (· * _) ?_))))
      exact (valR_res x le_top _ hi₂).trans (valR_const x _ hx _)
    have e₂ : (ψ.appLE _ _ l₁).hom (θ.f k) = (show Γ(pullback G.hom (jK V), (L.pull ψ).U (fun _ => k) ⊓
        (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i))ˣ from w.s (fun _ => k, fun _ => i)).val *
          ((pullback G.hom (jK V)).presheaf.map (homOfLE inf_le_right).op).hom (r.f fun _ => i) :=
      fn_ext fun y hy => by
        refine (gs_appLE _ _ _ _ (𝟙 _) y hy _).trans ?_
        rw [Category.id_comp, hr y k _ (l₁ hy) hy.2]
        exact ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          (gs_res (𝟙 _) y _ hy _))).symm
    have e₃ := (valR_appLE x ψ _ _ l₁ _ hW).symm.trans ((congrArg (valR x _) e₂).trans
      ((valR_mul' x _ hW _ _).trans (congrArg (_ * ·) (valR_res x _ _ hW))))
    rw [e₁, e₃]
    exact mul_left_comm _ _ _

end GlobalTheory.PrimScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrum
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiTop

theorem exists_setPsi_psiOn_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  intro R _ _ _ D
  have H : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (Y := Spec (CommRingCat.of R))
      (fun _ => (D.c χ).left) (fun _ => -1)), t.IsGen := fun χ =>
    DVR.exists_gen_of_local D.P.L D.P.isLB _ _
  choose t ht using H
  refine ⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (jK R), fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _,
    ⟨⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
      fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine Eq.trans ?_ (val_pull hJ (t χ) _ _).symm
  rw [Category.assoc, Category.assoc, morphismRestrict_ι]

end GlobalTheory.PsiTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCharts_torus_extension_over_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom :=
  GlobalTheory.SplitChartsField.main
end

