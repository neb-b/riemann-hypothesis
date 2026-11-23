module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalProperties
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  have hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
    IsFractionRing.injective _ _
  have hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧
      WittVector.constantCoeff w = coeff α (u' i) := hu
  choose U hU using hu1
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply hinj
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
        WittVector.constantCoeff w = coeff α f' := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w) := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

def QHyp {S : Scheme.{0}} (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left)

def formLB {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) {G : Over S} {r : ℕ} (pr : Fin r → (G ⟶ A))
    (W : Matrix (Fin r) (Fin r) ℤ) : LB G.left :=
  LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

def diagPow {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) (d : ℤ) : LB A.left :=
  LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => d)

def sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  pullback.lift ((fst G' G').left ≫ φ) ((snd G' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w (fst G' G'), Over.w (snd G' G')])

theorem isSquare_sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : IsSquare φ (sqMap f φ w) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {φ' : G''.left ⟶ G'.left} {φ₂' : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare φ' φ₂') (h : IsSquare φ φ₂) : IsSquare (φ' ≫ φ) (φ₂' ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
   by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isMonHom_prodPow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (c : Fin r → ℤ) : IsMonHom (∏ k, f k ^ c k) :=
  Finset.prod_induction _ (fun x => IsMonHom x) (fun a b ha hb => by
    haveI := ha; haveI := hb; exact GlobalTheory.Serre.isMonHom_mul a b) GlobalTheory.Serre.isMonHom_one fun k _ => by
    haveI := hf k; exact GlobalTheory.Serre.isMonHom_zpow _ _

theorem powext {S : Scheme.{0}} (A : Over S) (r : ℕ) {X : Scheme.{0}} (a b : X ⟶ (Out.powObj A r).left)
    (h0 : a ≫ (Out.powObj A r).hom = b ≫ (Out.powObj A r).hom)
    (h : ∀ k, a ≫ (Out.powPr A k).left = b ≫ (Out.powPr A k).left) : a = b := by
  have := (Out.powIsLimit A r).hom_ext (W := Over.mk (b ≫ (Out.powObj A r).hom)) (f := Over.homMk a h0)
    (f' := Over.homMk b rfl) (fun ⟨k⟩ => Over.OverMorphism.ext (by simpa using h k))
  exact congrArg (fun m => m.left) this

end GlobalTheory.ActFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_sectionComponents_of_family (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  classical
  have hfe : ∀ t : S, f (e t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  refine _root_.GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces X _ (_root_.GlobalTheory.stableUnderGeneralization_sectionComponents X S f e hf he) ?_
  intro x hx
  obtain ⟨U, V₀, V, I, hV, hs, hU, hI, hirr⟩ := _root_.GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible X S f e hf he (f x)
  refine ⟨⟨O U, hO U⟩ ⊓ f ⁻¹ᵁ (V₀ ⊓ e ⁻¹ᵁ U), f ⁻¹ᵁ V, I.image (fun c => f.app V c), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hV hy.2.1
  · exact ⟨h1 U x hU hx, hs, hU⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    rw [← Scheme.preimage_basicOpen]
    exact hI d hd
  · intro y hy hJ
    have hpre := hirr (f y) hy.2.1 (fun c hc => by
      have := hJ _ (Finset.mem_image_of_mem _ hc)
      rw [← Scheme.preimage_basicOpen] at this
      exact this)
    refine h2 U y ?_ hy.1
    intro z hz hzy
    have hsub := hpre.isPreconnected.subset_connectedComponentIn
      (x := e (f y)) (F := f ⁻¹' {f y}) ⟨hy.2.2, hfe _⟩ Set.inter_subset_right
    show z ∈ connectedComponentIn (f ⁻¹' {f z}) (e (f z))
    rw [hzy]
    exact hsub ⟨hz, hzy⟩

theorem isOpen_identityComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hG
  exact isOpen_sectionComponents_of_family G.left S G.hom (η[G]).left hG (Over.w (η[G]))
    (fun U => {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y})
    (_root_.GlobalTheory.IdCompOpen.isOpen_snd_image S G hG) (_root_.GlobalTheory.mem_unitComponent_mul_mem S G hG) (_root_.GlobalTheory.mem_identityComponents_of_mul_inv S G hG)

end GlobalTheory.IdCompOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsSympLevel (D : Datum H) {k : Type} [Field k] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) (N : ℕ) (z : kˣ) (ev : D.La → Q) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧
    (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ x : Q, x ^ N = 1 ↔ ∃ a, ev a = x) ∧
    ∀ a b, e N (ev a) (ev b) (z ^ D.EF a b)

def Induces {D : Datum H} (l : Level H) {Q : Type} [Group Q] (etaA eta ev : D.La → Q) : Prop :=
  (∀ a, ev a ^ (l.M' / l.A) = etaA a) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ev a ^ (l.M' / l.M) = eta a

theorem A_dvd_M' (l : Level H) : l.A ∣ l.M' := Nat.dvd_lcm_right _ _

theorem M_dvd_M' (l : Level H) : l.M ∣ l.M' := Nat.dvd_lcm_left _ _

theorem M'_pos (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

end GlobalTheory.FullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem ker_app_eq_kerIdeal_of_idempotents (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (_h2 : v ≫ u = 0)
    (n : ℕ) : RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    let x := Ideal.Quotient.mkₐ k (kerIdeal (v.app n))
    have hv : ∀ c, x (v.app n c) = algebraMap k _ (counit c) :=
      (kerIdeal_le_ker_iff (v.app n) x).1 fun b hb => by
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hb
    let P := (ptsPush (G.A n) (x : G.A n →ₐ[k] _)).comp toPts
    have hP : P (Hom.conv v n) = 1 := WithConv.ofConv_injective (AlgHom.ext fun c => by
      change x (v.app n c) = _
      rw [hv]
      simp)
    have e : P (Hom.conv (u + v) n) = P (Hom.conv u n) := by
      rw [add_conv, map_mul, hP, mul_one]
    rw [huv] at e
    have e' := congrArg (fun y => y.ofConv a) e
    change x a = x (u.app n a) at e'
    rw [ha, map_zero] at e'
    exact Ideal.Quotient.eq_zero_iff_mem.1 e'
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f : G ⟶ G => Hom.app f n b) h1
    change u.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[k] G.A n)).ofConv b at e
    have hb' : counit (R := k) b = 0 := hb
    refine Eq.trans e ?_
    simp [hb']

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRepsTransport
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem kerReps_transport : ∀ (K : Type) [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (a : K) (S : Finset ℂ), IsTr ι Λ₀ Λ₁ T → a ≠ 0 → (∀ x x', T x x' → T (a * x) (a * x')) → IsKerReps Λ₀ (ι a) S → ∃ (φ : ℂ → ℂ) (S' : Finset ℂ), IsKerReps Λ₁ (ι a) S' ∧ Set.BijOn φ S S' ∧ ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ ι k' = φ P ∧ T k k' := by
  intro K _ ι Λ₀ Λ₁ T a S hT ha hmul hS
  classical
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  obtain ⟨hS1, hS2, hS3⟩ := hS

  have hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k' := by
    intro P hP
    obtain ⟨b, hb⟩ := hT.rat₀ _ (hS1 P hP).1
    obtain ⟨k', hk'⟩ := hT.left (b / a)
    refine ⟨b / a, k', ?_, hk'⟩
    rw [map_div₀, hb]; field_simp
  choose! k k' hk hT' using hex
  set φ : ℂ → ℂ := fun P => ι (k' P) with hφ

  have himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice := by
    intro P hP
    have h1 := hT.mem_iff _ _ (hmul _ _ (hT' P hP))
    have h2 := hT.mem_iff _ _ (hT' P hP)
    rw [map_mul, map_mul, hk P hP] at h1
    rw [hk P hP] at h2
    exact ⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩
  have hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q := by
    intro P hP Q hQ h
    have h1 := hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))
    rw [map_sub, map_sub, hk P hP, hk Q hQ] at h1
    exact hS2 P hP Q hQ (h1.mpr h)
  refine ⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP),
    fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact himg P hP
  · intro P' hP' Q' hQ' h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hQ'
    rw [hdiff P hP Q hQ h]
  · intro z hz hz'
    obtain ⟨c, hc⟩ := hT.rat₁ _ hz
    have hzc : ι (c / a) = z := by rw [map_div₀, hc]; field_simp
    obtain ⟨m, hm⟩ := hT.right (c / a)
    have h1 := hT.mem_iff _ _ (hmul _ _ hm)
    have h2 := hT.mem_iff _ _ hm
    rw [map_mul, map_mul, hzc] at h1
    rw [hzc] at h2
    obtain ⟨P, hP, hmP⟩ := hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))
    refine ⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩
    have h3 := hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))
    rw [map_sub, map_sub, hk P hP, hzc] at h3
    exact h3.mp hmP
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP')
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact ⟨k P, k' P, hk P hP, rfl, hT' P hP⟩

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restrict : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defectSec
  | exact GlobalTheory.EtC.RedChern.res_defectSec
  | (intros; apply GlobalTheory.EtC.RedChern.res_defectSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatLatSmulLeOfIsIntegral
section
open NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory

theorem isIntegral_inv_of_pow_eq_one {K : Type} [Field K] {u : K} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    IsIntegral ℤ u⁻¹ := by
  refine IsIntegral.of_pow hn ?_
  rw [inv_pow, hu, inv_one]
  exact isIntegral_one

theorem matLat_smul_le_of_isIntegral {K : Type} [Field K] [NumberField K] {a b : ℕ} (c : K) (hc : IsIntegral ℤ c)
    (A : Matrix (Fin a) (Fin b) K) (M : Submodule (𝓞 K) (Fin b → K)) :
    Formalism.DivisionValues.matLat (c • A) M ≤ Formalism.DivisionValues.matLat A M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hmem : A.mulVec y ∈ Formalism.DivisionValues.matLat A M := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have h2 := (Formalism.DivisionValues.matLat A M).smul_mem (⟨c, hc⟩ : 𝓞 K) hmem
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  exact h2

theorem finitePlaceBound_inv_rootOfUnity_smul {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}
    {Df : DefSide Bs} (O : FunData K Df) (ze : Bs.Tup → K) (μ : Formalism.PairingDivisionLocalBalance.Pl K → Bs.Tup) (C b : ℝ)
    (hze : ∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) (h : LeafFP O μ C b) :
    LeafFP { O with vmu := fun t => (ze t)⁻¹ • O.vmu t } μ C b := by
  obtain ⟨ha, hb, hc⟩ := h
  refine ⟨fun w => ?_, hb, hc⟩
  obtain ⟨n, hn, hu⟩ := hze (μ w)
  exact le_trans (localization_mono _
    (matLat_smul_le_of_isIntegral _ (isIntegral_inv_of_pow_eq_one hn hu) _ _)) (ha w)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddiStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  first | exact @GlobalTheory.LadicDenom.valGe_iff_forall_sz | exact GlobalTheory.LadicDenom.valGe_iff_forall_sz | (intros; apply GlobalTheory.LadicDenom.valGe_iff_forall_sz <;> assumption)
end

