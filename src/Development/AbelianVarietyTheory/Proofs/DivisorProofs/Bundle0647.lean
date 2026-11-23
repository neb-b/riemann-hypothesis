module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixCoprimeDecomposition
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {S : Scheme.{0}}

def postHom {T A : Over S} [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] : (T ⟶ A) →* (T ⟶ A) where
  toFun f := f ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' f g := MonObj.mul_comp _ _ _

theorem bilin_ext {M La Q I J : Type} [AddCommGroup M] [AddCommGroup La] [CommGroup Q] [Fintype I] [Fintype J]
    (bM : Module.Basis I ℤ M) (bL : Module.Basis J ℤ La) (F G : M → La → Q)
    (hF1 : ∀ c c' a, F (c + c') a = F c a * F c' a) (hF2 : ∀ c a a', F c (a + a') = F c a * F c a')
    (hG1 : ∀ c c' a, G (c + c') a = G c a * G c' a) (hG2 : ∀ c a a', G c (a + a') = G c a * G c a')
    (h : ∀ i j, F (bM i) (bL j) = G (bM i) (bL j)) : ∀ c a, F c a = G c a := by
  intro c a
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => F c a) (fun c c' => hF1 c c' a) c,
    GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => G c a) (fun c c' => hG1 c c' a) c]
  refine Finset.prod_congr rfl fun i _ => ?_
  beta_reduce
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bL (F (bM i)) (hF2 _) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bL (G (bM i)) (hG2 _) a]
  simp only [h]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Kil {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (f : T ⟶ o.A) : Prop :=
  ∀ c ∈ w0 ^ r, f ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1

theorem Kil.comp {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T T' : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (h : T' ⟶ T) : Kil o w0 r (h ≫ f) := fun c hc => by
  rw [Category.assoc, hf c hc, MonObj.comp_one]

theorem Kil.act {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (d : D.O) : Kil o w0 r (f ≫ o.act.act d) := fun c hc => by
  haveI := o.act.hom d
  rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, hf c hc, MonObj.one_comp]

theorem vanish {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} (l : D.La → (T ⟶ o.A)) (hadd : ∀ x y, l (x + y) = l x * l y)
    (hlin : ∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) (hk : ∀ a, Kil o w0 r (l a)) :
    ∀ x ∈ wSub D w0 r, l x = 1 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [hlin]
    exact hk z' c hc
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  | add x y _ _ hx hy => rw [hadd, hx, hy, _root_.mul_one]
  | smul d x _ hx =>
    haveI := o.act.hom d
    rw [hlin, hx, MonObj.one_comp]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev


open RepLat in
theorem exists_finiteEtale_linTorsHom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ x y, et (x + y) = et x * et y) ∧ (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) ∧ (∀ x ∈ wSub D w0 r, et x = 1) ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), (∀ x y, l (x + y) = l x * l y) → (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, l x = 1) → ∃! h : T ⟶ Z, ∀ y, h ≫ et y = l y := by
  intro p _ D R _ b N w0 r _ S _ s o K κ hKf hKe hκ hK
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI := hKf
  haveI := hKe
  have hκ' : Kil o w0 r κ := hκ
  have hcan : ∀ {T : Over S} (v v' : T ⟶ K), v ≫ κ = v' ≫ κ → v = v' := fun v v' e =>
    (hK _ (v' ≫ κ) (hκ'.comp v')).unique e rfl
  have hfac : ∀ {T : Over S} (f : T ⟶ o.A), Kil o w0 r f → ∃ u : T ⟶ K, u ≫ κ = f := fun f hf =>
    (hK _ f hf).exists
  let bb := Module.finBasis ℤ D.La
  let n := Module.finrank ℤ D.La
  let bO := Module.finBasis ℤ D.O
  let Z₀ := Out.powObj K n
  let x : Fin n → (Z₀ ⟶ o.A) := fun i => Out.powPr K i ≫ κ
  let et₀ : D.La → (Z₀ ⟶ o.A) := fun a => ∏ i, x i ^ (bb.repr a i)
  have hadd : ∀ a c, et₀ (a + c) = et₀ a * et₀ c := fun a c => by
    simp only [et₀, map_add (f := _), Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et₀ (bb i) = x i := fun i => by
    simp only [et₀, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  have hkil : ∀ a, Kil o w0 r (et₀ a) := fun a c hc => by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    change postHom (T := Z₀) _ (∏ i, x i ^ (bb.repr a i)) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_zpow]
    change (x i ≫ _) ^ _ = 1
    rw [(hκ'.comp (Out.powPr K i)) c hc, one_zpow]
  haveI hZf : IsFinite Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @IsFinite K hKf n
  haveI hZe : Etale Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @Etale K hKe n
  have c1 : ClopenCond Z₀ fun _ h => ∀ (c : D.O) a, h ≫ et₀ (c • a) = h ≫ (et₀ a ≫ o.act.act c) := by
    have hfin : ClopenCond Z₀ fun _ h => ∀ ji : Fin (Module.finrank ℤ D.O) × Fin n,
        h ≫ et₀ (bO ji.1 • bb ji.2) = h ≫ (et₀ (bb ji.2) ≫ o.act.act (bO ji.1)) := by
      refine ClopenCond.forall_finite fun ji => ?_
      obtain ⟨u, hu⟩ := hfac _ (hkil (bO ji.1 • bb ji.2))
      obtain ⟨u', hu'⟩ := hfac _ ((hkil (bb ji.2)).act (bO ji.1))
      refine (clopenCond_eq u u').congr fun T' h => ?_
      rw [← hu, ← hu', ← Category.assoc, ← Category.assoc]
      exact ⟨hcan _ _, fun e => by rw [e]⟩
    refine hfin.congr fun T' h => ⟨fun H ji => H _ _, fun H => ?_⟩
    refine bilin_ext bO bb (fun c a => h ≫ et₀ (c • a)) (fun c a => h ≫ (et₀ a ≫ o.act.act c))
      (fun c c' a => by beta_reduce; rw [add_smul, hadd, MonObj.comp_mul])
      (fun c a a' => by beta_reduce; rw [smul_add, hadd, MonObj.comp_mul])
      (fun c c' a => by beta_reduce; rw [o.act.add, MonObj.comp_mul, MonObj.comp_mul])
      (fun c a a' => by
        beta_reduce
        haveI := o.act.hom c
        rw [hadd, MonObj.mul_comp, MonObj.comp_mul])
      (fun j i => H (j, i))
  obtain ⟨U, hU, HU⟩ := c1
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU V i).2 ((Hi V i).2 ⟨𝟙 V, Category.id_comp i⟩)
  have hVadd : ∀ a c, i ≫ et₀ (a + c) = (i ≫ et₀ a) * (i ≫ et₀ c) := fun a c => by
    rw [hadd, MonObj.comp_mul]
  have hVlin : ∀ (c : D.O) a, i ≫ et₀ (c • a) = (i ≫ et₀ a) ≫ o.act.act c := fun c a => by
    rw [hi, Category.assoc]
  refine ⟨V, fun a => i ≫ et₀ a, hV1, hV2, hVadd, hVlin,
    vanish _ hVadd hVlin fun a => (hkil a).comp i, fun T l hladd hllin hlw => ?_⟩
  have hlk : ∀ a, Kil o w0 r (l a) := fun a c hc => by
    rw [← hllin]
    exact hlw _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  choose y hy using fun j : Fin n => hfac _ (hlk (bb j))
  let h : T ⟶ Z₀ := (Out.powIsLimit K n).lift (Fan.mk T y)
  have hh : ∀ j, h ≫ Out.powPr K j = y j := fun j => (Out.powIsLimit K n).fac (Fan.mk T y) ⟨j⟩
  have hhe : ∀ a, h ≫ et₀ a = l a := fun a => by
    rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bb (fun a => h ≫ et₀ a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
      GlobalTheory.LatticeTorsion.eq_prod_zpow bb l hladd a]
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [hb, ← hy j, ← hh j, Category.assoc]
  have hext : ∀ u u' : T ⟶ Z₀, (∀ a, u ≫ et₀ a = u' ≫ et₀ a) → u = u' := fun u u' e =>
    (Out.powIsLimit K n).hom_ext fun ⟨j⟩ => by
      have := e (bb j)
      rw [hb] at this
      exact hcan _ _ (by simp only [x, Category.assoc] at this; exact this)
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 fun c a => by rw [hhe, hllin, ← hhe a, Category.assoc])
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hhe], fun g hg => ?_⟩
  exact (cancel_mono i).1 (hext _ _ fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hhe])

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapExists
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Katz.ModHom

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem red_lift {σ : Type} (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := by
  intro α
  exact ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    simp [WittVector.constantCoeff_apply]⟩

def substW {σ τ : Type} [Finite σ] (u : σ → MvPowerSeries τ (Fr p k)) (hu : ∀ i, constantCoeff (u i) = 0) :
    MvPowerSeries σ (Fr p k) →ₗ[WittVector p k] MvPowerSeries τ (Fr p k) where
  toFun f := subst u f
  map_add' f g := subst_add (hasSubst_of_constantCoeff_zero hu) f g
  map_smul' r f := by
    rw [← algebraMap_smul (Fr p k) r f, subst_smul (hasSubst_of_constantCoeff_zero hu),
      algebraMap_smul]
    rfl

variable [PerfectRing k p]

def modMap {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) : Mod p hν →ₗ[WittVector p k] Mod p hμ :=
  Submodule.mapQ _ _
    (((substW p (fun j => Katz.lift p (φ j)) fun j => constantCoeff_lift p (hφ.const j)).comp
      (quasiLog p hν).subtype).codRestrict (quasiLog p hμ)
      fun f => (_root_.GlobalTheory.KatzPull.quasiLog_pull p k d e μ ν hμ hν φ hφ f.1 f.2).1)
    (by
      intro f hf
      rw [Submodule.mem_comap]
      change f.1 ∈ intBy p k (Fin e) 1 at hf
      change subst (fun j => Katz.lift p (φ j)) f.1 ∈ intBy p k (Fin d) 1
      exact (_root_.GlobalTheory.Katz.red_subst p k (Fin e) (Fin d) _ φ (fun j => constantCoeff_lift p (hφ.const j))
        (fun j => red_lift p (φ j))).2 1 f.1 hf)

theorem modMap_mk {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) (f : quasiLog p hν) :
    ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
      modMap p hμ hν hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk g :=
  ⟨_, rfl, rfl⟩

end GlobalTheory.Katz.ModHom

theorem GlobalTheory.Katz.ModHom.map_exists : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∃ m : Mod p hν →ₗ[WittVector p k] Mod p hμ, ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧ m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ
  exact ⟨GlobalTheory.Katz.ModHom.modMap p hμ hν hφ, GlobalTheory.Katz.ModHom.modMap_mk p hμ hν hφ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureComplNonvanishingSetEqZeroOfDense
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem zeroSet_null_of_dense_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ hτ hd
  have hN : EXTNullStatement n := extNull n
  have hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0) := by
    intro i y hy
    rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
    simp [A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]
  refine measure_null_of_locally_null _ fun y _ => ?_
  have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have hv := (A.chart (A.pick y)).map_source hys
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
  have hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) :=
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  have hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Set.mem_preimage.mpr (Metric.mem_ball_self hr)⟩
  have hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
      (A.chart (A.pick y)).target := by
    simpa using hτ.1 (A.pick y)
  have hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    have := hF.continuousOn.comp (A.chart (A.pick y)).continuousOn
      (fun x hx => (A.chart (A.pick y)).map_source hx)
    refine this.congr fun x hx => ?_
    simp [Function.comp, (A.chart (A.pick y)).left_inv hx]
  have hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ) :=
    (hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton
  refine ⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩
  refine measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_
  · rintro x ⟨hxn, hxU⟩
    refine ⟨hxU, fun h => hxn ?_⟩
    exact (hiff _ x hxU.1).2 h.2
  rw [A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet)
    (Set.diff_subset.trans Set.inter_subset_left)]
  apply setLIntegral_measure_zero
  obtain ⟨y', hy'U, hy'M⟩ := hd.inter_open_nonempty _ hUo ⟨y, hyU⟩
  have hnull := hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
    (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by
      simp only [Function.comp, (A.chart _).left_inv hy'U.1]
      exact (hiff _ y' hy'U.1).1 hy'M⟩
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨hxU, hxn⟩, rfl⟩
  refine ⟨hxU.2, ?_⟩
  simp only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]
  by_contra h
  exact hxn ⟨hxU, h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Host

namespace GlobalTheory.MuConj

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_involutive (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

noncomputable def starAlg (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  { (starRingAut : E ≃+* E) with commutes' := hF }

theorem mem_above_iff (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P ≠ P) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = P.under (𝓞 F) ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  have hc : starAlg hF ≠ 1 := by
    intro h
    apply hP
    ext x
    have e : cO E x = x := by
      apply RingOfIntegers.ext
      exact congrArg (fun σ : E ≃ₐ[F] E => σ (x : E)) h
    rw [mem_conjP, e]
  rw [GlobalTheory.Mem.Chr.under_eq_iff_conjPl (starAlg hF) hr hc P Q, GlobalTheory.Mem.Chr.conjPl_iff_mem]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · ext y
    rw [mem_conjP]
    refine (h (cO E y) y ?_).symm
    exact (star_star (y : E)).symm
  · subst h
    intro x y hxy
    have e : y = cO E x := RingOfIntegers.ext hxy
    rw [e, mem_conjP, cO_cO]


omit [StarRing E] in
theorem valuation_up (Q : HeightOneSpectrum (𝓞 E))
    (h : ¬ (Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q.asIdeal ^ 2) (x : F) :
    Q.valuation E (algebraMap F E x) = (Q.under (𝓞 F)).valuation F x := by
  have : Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have he : Ideal.ramificationIdx' (Q.under (𝓞 F)).asIdeal Q.asIdeal = 1 := by
    by_contra hne
    exact h ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hne)
  rw [← HeightOneSpectrum.valuation_liesOver E (Q.under (𝓞 F)) Q,
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Q.under (𝓞 F)).ne_bot, he, pow_one]

end General

theorem mem_divs_of_mem {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) {P : HeightOneSpectrum A}
    (h : a ∈ P.asIdeal) : P ∈ divs a := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h1 := Ideal.finite_factors (I := Ideal.span {a}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha)
    refine h1.subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  exact h

theorem g_notMem {X : Fields} {Pr : Primes X} (h : Pr.Ok) (P : HeightOneSpectrum (𝓞 X.E)) (h1 : P ∉ Pr.vGs)
    (h2 : conjPrime₂ P ∉ Pr.vGs) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (h.g_prime i).ne_zero
  rw [← h.piG_norm i] at hm hg
  have hsub : ∀ Q, Q ∈ Pr.vG i → Q ∈ Pr.vGs := by
    intro Q hQ
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases i
    · exact Or.inl hQ
    · exact Or.inr hQ
  have hne : X.conjO (Pr.piG i) ≠ 0 := right_ne_zero_of_mul hg
  rcases P.isPrime.mem_or_mem hm with h3 | h3
  · refine h2 (hsub _ (mem_divs_of_mem hne ?_))
    show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal
    rw [cO_cO]
    exact h3
  · exact h1 (hsub _ (mem_divs_of_mem hne h3))

end GlobalTheory.MuConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModNoPTorsion
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem mod_noPTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ b, cob1 μ b = 0 → b = 0) → ∀ m : Mod p h, (p : WittVector p k) • m = 0 → m = 0 := by
  intro p _ k _ _ _ d μ h hb m hm
  obtain ⟨R1, R2, -, -, -, R6, ZariskiNoetherianInduction⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d)
  obtain ⟨-, R2', -, -, -, R6', R7'⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, C1, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨f, hf⟩ := x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  rw [Submodule.Quotient.mk_eq_zero]
  change (p : WittVector p k) • f ∈ intBy p k (Fin d) 1 at hm
  change f ∈ intBy p k (Fin d) 1
  obtain ⟨b, hB⟩ := (R1 _).1 hm
  have hL : ∀ i, constantCoeff (lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hcob : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) =
      (p : WittVector p k) • cob1 (fun i => lift p (μ i)) f := by
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, formalCoboundary_smul hL, algebraMap_smul]
  have hcp : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) ∈ intBy p k _ (p : WittVector p k) := by
    rw [hcob, R7']; exact ⟨_, hf.2, rfl⟩
  have h0 : cob1 μ b = 0 := R2' _ _ _ (C1 _ _ hB).1 ((R6' _).1 hcp)
  have hb0 : b = 0 := hb b h0
  subst hb0
  obtain ⟨g, hg, hfg⟩ := (ZariskiNoetherianInduction _ _).1 ((R6 _).2 hB)
  have hp : (algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)) ≠ 0 := by
    rw [map_natCast]
    intro h0
    have := IsFractionRing.injective (WittVector p k) (Fr p k)
    apply WittVector.p_nonzero (p := p) (R := k)
    apply this; rw [map_natCast, map_zero]; exact h0
  have : f = g := by
    ext α
    have := congrArg (coeff α) hfg
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, ← algebraMap_smul (Fr p k) (p : WittVector p k) g,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ hp this
  rw [this]; exact hg

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSumStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ]
      [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B),
      (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ)
      (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) →
      MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q n (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g)) =
        ∑ α ∈ S, coeff α g *
          algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  intro B Q _ _ _ σ τ _ _ _ _ z u hu g n S hS
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun j => by simp [up, constantCoeff_map, hu j]
  have hprod (α : τ →₀ ℕ) : (α.prod fun j e => up Q u j ^ e) =
      map (algebraMap B Q) (α.prod fun j e => u j ^ e) := by
    rw [map_finsuppProd]
    simp [up, map_pow]
  have hcoeff (β : σ →₀ ℕ) (hβ : β ≤ n) :
      coeff β (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g) =
        ∑ α ∈ S, coeff α g * algebraMap B Q (coeff β (α.prod fun j e => u j ^ e)) := by
    rw [coeff_subst ha]
    simp_rw [hprod, coeff_map, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro α hα
    by_contra hαS
    apply hα
    dsimp only
    have hlt : n.degree < α.degree := lt_of_not_ge fun h => hαS (hS α h)
    rw [_root_.GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt B σ τ u hu α β
      (lt_of_le_of_lt (Finsupp.degree_mono hβ) hlt), map_zero, mul_zero]
  rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, Finset.sum_congr rfl fun β hβ => by
    rw [hcoeff β (Finset.mem_Iic.mp hβ)]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, map_prod]
  simp_rw [map_pow]
  ring
end

