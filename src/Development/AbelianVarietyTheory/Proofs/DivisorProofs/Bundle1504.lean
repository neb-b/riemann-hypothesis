module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0860
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieIndep

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}

theorem lieTie_add {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp C ⟶ S} {ψ : P.A.A.left ⟶ G.left}
    (hψ : IsGrpPullback P.A.A G y ψ) {x x' : LieG P.Gt}
    {u u' : Over.mk (spMap (algebraMap C (DualNumber C)) ≫ y) ⟶ G}
    (h : LieTie P ψ x u.left) (h' : LieTie P ψ x' u'.left) : LieTie P ψ (lieAdd x x') (u * u').left := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  refine ⟨lieAdd xG xG', w * w', h1.mul h1', (hψ.2 _ w w' u u' h2.symm h2'.symm).symm, ?_⟩
  let d : Over.mk ((specO C (DualNumber C)).hom ≫ spMap (algebraMap O C)) ⟶ specO O (DualNumber O) :=
    Over.homMk (spMap (dualMap (algebraMap O C))) (by
      refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
      ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  refine (P.gen_pull.2 _ w w' (d ≫ xG.1) (d ≫ xG'.1) h3.symm h3'.symm).symm.trans ?_
  rw [← MonObj.comp_mul]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem lieTie_unique_right {Y : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {x : LieG P.Gt} {u u' : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P ψ x u') : u = u' := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => (Fact.out : ¬ IsUnit (p : O)) (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hc : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h := (inferInstance : IsAdicComplete (Ideal.span {(p : O)}) O)
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  have e : xG.1 = xG'.1 := (existsUnique_right hp hc x.1).unique h1 h1'
  have e1 : w.left = w'.left :=
    P.gen_pull.1.hom_ext (by rw [h3, h3', e]) ((Over.w w).trans (Over.w w').symm)
  rw [← h2, ← h2', e1]


omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem linearIndependent_evLie {n : ℕ} (x : Fin n → LieG P.Gt)
    (h : ∀ a : Fin n → O, (∀ f : omega P.Gt, ∑ j, a j * f.1 (x j) = 0) → ∀ j, a j = 0) :
    LinearIndependent C (fun j => evLie P (x j)) := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) g
  choose a ha using hb
  have h0 := h a (fun f => P.integers.hom_inj (by
    have h1 := congrArg (fun L : P.OmC →ₗ[C] C => (b : O) • L ((1 : C) ⊗ₜ f)) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_zero, Finset.smul_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ha, ← smul_assoc, smul_eq_mul]
    congr 1
    simp [evLie])) j
  have h2 := ha j
  rw [h0, map_zero, Algebra.smul_def] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left
    ((map_ne_zero_iff _ P.integers.hom_inj).2 (nonZeroDivisors.ne_zero b.2))

end GlobalTheory.CompHt.TieIndep

namespace GlobalTheory.CompHt


open TieIndep in
theorem linearIndependent_evLie_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → LinearIndependent C (fun j => evLie P (x j)) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  have hψ : IsGrpPullback P.A.A Xo.univ.t.G z.x ψ := hz.1 ▸ hP.isGrpPullback
  obtain ⟨N, _, _, w, ρ, -, htan, hcomb, hρ, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo C z.x
  choose b hb using fun j => (htan _).1 (z.tan τ j)
  have hadd : ∀ {y y' : LieG P.Gt} {m m' : N}, LieTie P ψ y (w m) → LieTie P ψ y' (w m') →
      LieTie P ψ (lieAdd y y') (w (m + m')) := fun {y y' m m'} h h' => by
    obtain ⟨u, h1, h2⟩ := (hcomb 2 ![m, m'] ![1, 1] (w (m + m'))).2 (by simp)
    have e0 : (u 0).left = w m := (h1 0).trans ((hsm 1 m).symm.trans (by rw [one_smul]))
    have e1 : (u 1).left = w m' := (h1 1).trans ((hsm 1 m').symm.trans (by rw [one_smul]))
    rw [← h2, show (List.ofFn u).prod = u 0 * u 1 by simp]
    exact lieTie_add hψ (e0 ▸ h) (e1 ▸ h')
  have hsc : ∀ (a : O) j, LieTie P ψ (AvDefs.lieScale P.Gt a (x j)) (w (algebraMap O C a • b j)) := fun a j => by
    rw [hsm, hb]
    exact (hx j).scale a
  refine linearIndependent_evLie x fun a ha j => ?_
  have h0 := hsc 0 j
  rw [map_zero, zero_smul] at h0
  have hs : ∀ s : Finset (Fin (Dw.mult τ)), ∃ y, LieTie P ψ y (w (∑ i ∈ s, algebraMap O C (a i) • b i)) ∧
      ∀ f : omega P.Gt, f.1 y = ∑ i ∈ s, a i * f.1 (x i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨_, h0, fun f => by rw [omega_lieScale, zero_mul, Finset.sum_empty]⟩
    | insert i s hi ih =>
      obtain ⟨y, h1, h2⟩ := ih
      rw [Finset.sum_insert hi]
      exact ⟨_, hadd (hsc (a i) i) h1, fun f => by rw [omega_lieAdd, omega_lieScale, h2, Finset.sum_insert hi]⟩
  obtain ⟨y, h1, h2⟩ := hs Finset.univ
  have e : y = AvDefs.lieScale P.Gt 0 (x j) :=
    (Point.omega_free_finite_bijective p C v O (𝓞 E) P).2.2.1 (LinearMap.ext fun f => by
      change f.1 y = f.1 _
      rw [h2, ha, omega_lieScale, zero_mul])
  have e2 := lieTie_unique_right h0 (e ▸ h1)
  have hu : z.u τ = fun i => w (b i) := funext fun i => (hb i).symm
  have e3 := (z.basis τ (w 0) ((htan _).2 ⟨0, rfl⟩) fun t => by rw [← hρ, ← hsm, map_zero, smul_zero]).unique
    (y₁ := fun i => algebraMap O C (a i)) (y₂ := 0) (by rw [hu, hcomb]; exact e2) (by rw [hu, hcomb]; simp)
  exact P.integers.hom_inj ((congrFun e3 j).trans (map_zero _).symm)

end GlobalTheory.CompHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjEqOfSemidirectLatticeDatum
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal NNReal

namespace GlobalTheory.ResLine

theorem map_eq_self_of_normalises_lattice {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (Λ : Subgroup B) [Countable Λ] (ν : Measure B) [ν.IsHaarMeasure] (D : Set B) (hD : IsFundamentalDomain Λ D ν)
    (hfin : ν D ≠ ⊤) (φ : B ≃ₜ* B) (h1 : ∀ b ∈ Λ, φ b ∈ Λ) (h2 : ∀ b ∈ Λ, φ.symm b ∈ Λ) : ν.map φ = ν := by
  haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map φ) ν
  set c := Measure.haarScalarFactor (ν.map φ) ν
  have hφm : Measurable φ := φ.continuous.measurable
  have hq : Measure.QuasiMeasurePreserving φ ν ν := by
    refine ⟨hφm.aemeasurable, ?_⟩
    rw [hc]
    exact Measure.smul_absolutelyContinuous
  have h' : IsFundamentalDomain Λ (φ ⁻¹' D) ν := by
    refine hD.preimage_of_equiv hq (e := fun g : Λ => (⟨φ.symm g, h2 g g.2⟩ : Λ)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext
        exact φ.symm.injective (congrArg Subtype.val hab)
      · intro a
        exact ⟨⟨φ a, h1 a a.2⟩, Subtype.ext (φ.symm_apply_apply a)⟩
    · intro g x
      simp [Subgroup.smul_def]
  have hm : ν (φ ⁻¹' D) = ν D := h'.measure_eq hD
  have h0 : ν D ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map φ) D = ν (φ ⁻¹' D) :=
    MeasurableEquiv.map_apply φ.toHomeomorph.toMeasurableEquiv D
  have h3 : (c : ℝ≥0∞) * ν D = 1 * ν D := by
    calc (c : ℝ≥0∞) * ν D = (c • ν) D := by simp [Measure.smul_apply]
      _ = (ν.map φ) D := by rw [hc]
      _ = 1 * ν D := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h3
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem lintegral_conj_eq_of_semiLat : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ m ∈ M, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (m * u * m⁻¹) ∂ν = ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM h m hm f hf
  haveI := h.haarN
  haveI : LocallyCompactSpace N := h.closedN.locallyCompactSpace
  haveI : LocallyCompactSpace M := h.closedM.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hcount : ∀ K : Subgroup G, Countable (Λ.subgroupOf K) := fun K =>
    Function.Injective.countable (f := fun g : Λ.subgroupOf K => (⟨g.1.1, g.2⟩ : Λ))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun g : Λ => (g : G)) hab))
  haveI := hcount N
  haveI := hcount M
  have hB : ∀ x : M, ∀ b ∈ N, M.subtype x * b * (M.subtype x)⁻¹ ∈ N := fun x b hb => h.norm x x.2 b hb
  have key := GlobalTheory.ConjModulus.map_conj_eq_self_of_lattice M G M.subtype continuous_subtype_val N h.closedN hB ν h.haarN
    (Λ.subgroupOf M) π DM h.haarM h.domM h.finM (fun x hx => by
      have hx' : (x : G) ∈ Λ := hx
      refine map_eq_self_of_normalises_lattice (Λ.subgroupOf N) ν DN h.domN h.finN
        (GlobalTheory.ConjModulus.conjCME M.subtype N hB x) ?_ ?_
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem hx' hb') (Λ.inv_mem hx')
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hx') hb') (Λ.inv_mem (Λ.inv_mem hx'))) ⟨m, hm⟩
  have hφm : Measurable (fun b : N => (⟨M.subtype ⟨m, hm⟩ * b * (M.subtype ⟨m, hm⟩)⁻¹, hB ⟨m, hm⟩ b b.2⟩ : N)) :=
    (GlobalTheory.ConjModulus.conjCME M.subtype N hB ⟨m, hm⟩).continuous.measurable
  have := lintegral_map (μ := ν) (hf.comp measurable_subtype_coe) hφm
  rw [key] at this
  exact this.symm

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum

theorem IsMinPol.scaleRoots_eq {K : Type} [Field K] {σ : K →+* ℂ} {β : ℂ} {u : K} {p q : K[X]}
    (hp : IsMinPol σ β p) (hq : IsMinPol σ (σ u * β) q) (hu : u ≠ 0) : q = p.scaleRoots u := by
  let := σ.toAlgebra
  have ep := hp.eq_minpoly
  have eq := hq.eq_minpoly
  have hr0 : (p.scaleRoots u).eval₂ σ (σ u * β) = 0 := scaleRoots_eval₂_eq_zero σ hp.2.2
  have hs0 : (q.scaleRoots u⁻¹).eval₂ σ β = 0 := by
    have := scaleRoots_eval₂_eq_zero σ (s := u⁻¹) hq.2.2
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul] at this
  have d1 : q ∣ p.scaleRoots u := by
    rw [eq]; exact minpoly.dvd K (σ u * β) hr0
  have d2 : p ∣ q.scaleRoots u⁻¹ := by
    rw [ep]; exact minpoly.dvd K β hs0
  have hq0 : q.scaleRoots u⁻¹ ≠ 0 := scaleRoots_ne_zero hq.1.ne_zero _
  have le1 : p.natDegree ≤ q.natDegree := by
    have := natDegree_le_of_dvd d2 hq0
    rwa [natDegree_scaleRoots] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le hq.1 ((monic_scaleRoots_iff u).2 hp.1) d1
    (by rw [natDegree_scaleRoots]; exact le1)).symm

end GlobalTheory.FunObj.SqNum

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_smul : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  intro K _ _ _ σ β u p q hp hq hβ hu w
  obtain ⟨hc, hd⟩ := hp.ne_zero hβ
  rw [hp.scaleRoots_eq hq hu]
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  rw [natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_zero]
  have hm : vw w (p.coeff 0 * u ^ p.natDegree) = vw w (p.coeff 0) + p.natDegree * vw w u := by
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hc)
        (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 (pow_ne_zero _ hu)),
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
  rw [hm]
  have : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]; push_cast; ring_nf
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]; push_cast; ring_nf

theorem prod_apow_list (ϖ : kˣ) {α : Type*} (l : List α) (f : α → ℂ) :
    (l.map fun b => apow ϖ (f b)).prod = apow ϖ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, ← apow_add]; simp

theorem prod_apow_finset (ϖ : kˣ) {α : Type*} (s : Finset α) (f : α → ℂ) :
    ∏ i ∈ s, apow ϖ (f i) = apow ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← apow_add]

end Generic
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Vol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem setOf_le_eq_preimage (u : kˣ) :
    {x : k | valuation k x ≤ valuation k (u : k)} = (fun x => ((u⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
  ext x
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_one₀ h0]

variable [MeasurableSpace k] [BorelSpace k]

theorem measurableSet_setOf_le (u : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (u : k)} := by
  rw [setOf_le_eq_preimage]
  exact (Model.isOpen_int.preimage (continuous_const.mul continuous_id)).measurableSet

theorem vol_setOf_le (ν : Measure k) (hν : IsUnitVol ν) (u : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (u : k)} = ENNReal.ofReal (nabs k u) := by
  rw [← Model.nabs_vol ν hν u, setOf_le_eq_preimage]
  congr 1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_box (G : Grid k) (ϖ : kˣ) (a a' : ℤ) : MeasurableSet (box G ϖ a a') :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_setOf_le _

open Classical in
theorem vol_box (G : Grid k) (ν : Measure k) (hν : IsUnitVol ν) (ϖ : kˣ) (a a' : ℤ) :
    (varsVol G ν (box G ϖ a a')).toReal = ∏ j, ∏ v, nabs k (ϖ ^ boxExp G a a' j v) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have := hν.1
  rw [varsVol, box, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [vol_setOf_le ν hν, ENNReal.toReal_ofReal (Model.nabs_pos _).le]

end Vol
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_zpow_units {α : Type*} (ϖ : kˣ) (s : Finset α) (f : α → ℤ) : ∏ i ∈ s, ϖ ^ f i = ϖ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, _root_.zpow_add]

variable (G : Grid k)

def vtxDet (a a' : ℤ) (X : ℕ × ℕ) : ℤ :=
  if X.1 = G.m then ∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x else 0


open Classical in
def expo (a a' : ℤ) : ℤ :=
  ((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum -
    2 * ∑ j, ∑ v, boxExp G a a' j v

variable {G}

theorem gdet_eq (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j)
    (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) (X : ℕ × ℕ) : gdet (g X) = ϖ ^ vtxDet G a a' X := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · rw [show (i, j) = (G.m, j) by rw [hi], hg, vtxDet, if_pos rfl, colDiag, gdet, det_diagGL, prod_zpow_units]
  · rw [hg' i j hi, vtxDet, if_neg hi]
    simp

end Expo
end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrameStabOfParFlag
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLineLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}


theorem mem_frameStab_of_parFlag {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {L : Matrix (Fin s) (Fin n) E} (hL : L * C = 1)
    {d : Fin s → ℕ} {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) : g ∈ frameStab σ J C ⊤ := by
  obtain ⟨⟨B, -, e⟩, B', -, e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  exact ⟨⟨B, B', hBB, mul_eq_one_comm.1 hBB⟩, Subgroup.mem_top _, e⟩


omit [NumberField E] in
theorem unipRad_fix {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, Units.val_one, Matrix.mul_one]⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [e, Subgroup.mem_bot.1 hB, Units.val_one, Matrix.mul_one]


end GlobalTheory.ResLineLevi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

def psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) : A ⊗ A ⟶ A ⊗ A :=
  lift (fst A A ^ a₁ * snd A A ^ b₁) (fst A A ^ a₂ * snd A A ^ b₂)

theorem psiMap_fst {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ fst A A = fst A A ^ a₁ * snd A A ^ b₁ := lift_fst _ _

theorem psiMap_snd {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ snd A A = fst A A ^ a₂ * snd A A ^ b₂ := lift_snd _ _

end GlobalTheory.AmpleGen
end
end

