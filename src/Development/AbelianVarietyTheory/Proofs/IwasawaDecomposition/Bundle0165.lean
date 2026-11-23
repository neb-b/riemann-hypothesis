module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibProp

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem form_eq (x y : Fin n → A) :
    Formalism.UG.hform s J x y = dotProduct (fun i => s (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT s g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform s J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform s J x y := by
  have e : (fun i => s (g.mulVec x i)) = Matrix.vecMul (fun i => s (x i)) (Formalism.UG.cT s g) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [form_eq, form_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem form_smul (a : A) (x : Fin n → A) :
    Formalism.UG.hform s J (a • x) (a • x) = s a * a * Formalism.UG.hform s J x x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem det_norm {g : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) (hg : Formalism.UG.cT s g * J * g = J) :
    g.det * s g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem lrAct_one (g : Matrix (Fin n) (Fin n) A) {k : ℕ} (X : Fin k → Fin n → A) :
    lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

end Alg

section Q

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sig_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_incl (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem q_scale (r : R) (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  unfold qR hR
  rw [form_smul, sig_alg, ← map_mul, ← Algebra.smul_def (r * r), map_smul, smul_eq_mul]
  ring

theorem q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin M → E) (β : F)
    (hx : hE σ J x x = algebraMap F E β) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R β := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have e : hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (x i)) = inclR R (hE σ J x x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, hE, Formalism.UG.hform, JR, Matrix.map_apply, sig_incl, map_sum, map_mul]
    rfl
  have e2 : inclR R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  unfold qR
  rw [e, hx, e2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (algebraMap F R), ← map_mul]
  norm_num

theorem q_cont [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R] :
    Continuous (qR R σ J) := by
  have hs : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  have ht : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  unfold qR hR Formalism.UG.hform
  fun_prop

end Q

theorem fibre_invariant_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hN M J x β lam ν m hJ hβ hx hlam hν hm
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 β hβ).map _
  have hq : qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := q_rat R σ J hCM.2.2.1 (x 0) β hx
  obtain ⟨hsupp, -, huniq⟩ := _root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hN M J _ ν _ m hν hu hm
  have h1 : modu R 1 = 1 := (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  refine ⟨fun g => ?_, ?_, ?_⟩
  · set G : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (HA.mat R σ J g).val with hG
    have hg : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := g.2
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 (HA.mat R σ J g).isUnit
    have hJu : IsUnit (JR (F := F) R J).det := by
      unfold JR
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hm1 : modu (R ⊗[F] E) G.det = 1 := by
      rw [(_root_.GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R G.det 1 hd (by rw [map_one, det_norm _ _ hJu hg])).2, h1]
    have := _root_.GlobalTheory.GaugeEx.fibAt_similitude F E σ R hN M J J lam ν _ 1 m G hlam hν hd isUnit_one
      (fun z => by rw [one_mul]; unfold qR hR; rw [form_mulVec _ _ hg]) hm
    rw [one_mul, hm1, h1, inv_one, mul_one, one_smul] at this
    have e : lrAct G 1 = fun X : Fin 1 → Fin M → R ⊗[F] E => g • X := by
      funext X; rw [lrAct_one]; rfl
    rw [e] at this
    exact huniq _ this
  · refine measure_mono_null (fun y hy => ?_) hsupp
    exact fun h => hy (_root_.GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hCM R hN M J hJ _ _ y hu hq h)
  · rintro rfl
    obtain ⟨-, -, hO, U, hU, h1U, s, -, -, hs⟩ := id hN
    obtain ⟨fib, hfib, -⟩ := id hm
    obtain ⟨w, hw⟩ := hu
    let T : Set R := {b | IsUnit b} ∩ (fun b => b * (↑w⁻¹ : R)) ⁻¹' U
    have hT : IsOpen T := by
      refine IsOpen.inter ?_ (hU.preimage (by fun_prop))
      exact hO.isOpenEmbedding_unitsVal.isOpen_range
    have hz : ∀ b ∈ T, fib b = 0 := by
      rintro b ⟨hb, hbU⟩
      set r := s (b * (↑w⁻¹ : R))
      have hr : r * r = b * (↑w⁻¹ : R) := hs _ hbU
      have hrr : IsUnit (r * r) := hr ▸ IsUnit.mul hb (Units.isUnit _)
      have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
      have := _root_.GlobalTheory.GaugeEx.fibAt_similitude F E σ R hN M J J lam ν _ (r * r) 0
        (algebraMap R (R ⊗[F] E) r • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact (hru.map _).pow _) hrr
        (fun z => by rw [Matrix.smul_mulVec, Matrix.one_mulVec, q_scale]) hm
      rw [Measure.map_zero, smul_zero, hr, ← hw, Units.inv_mul_cancel_right] at this
      exact (_root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hN M J _ ν _ 0 hν hb this).2.2 _ ⟨fib, hfib, rfl⟩
    let O : Set (Fin 1 → Fin M → R ⊗[F] E) := (fun X => qR R σ J (X 0)) ⁻¹' T
    have hOo : IsOpen O := hT.preimage ((q_cont R σ J).comp (continuous_apply 0))
    have hne : O.Nonempty := ⟨ratTup (F := F) R x, by
      show qR R σ J (ratTup (F := F) R x 0) ∈ T
      rw [hq, ← hw]
      exact ⟨w.isUnit, by simpa using h1U⟩⟩
    have key := hfib.2.1 (O.indicator 1) (measurable_one.indicator hOo.measurableSet)
    have hz' : ∀ b, fib b O = 0 := by
      intro b
      by_cases hb : b ∈ T
      · rw [hz b hb]; rfl
      · refine measure_mono_null (fun y hy => ?_) (hfib.1 b)
        intro h
        apply hb
        have : qR R σ J (y 0) = b := h.1
        rw [← this]; exact hy
    simp only [Measure.restrict_univ, lintegral_indicator_one hOo.measurableSet, hz',
      lintegral_zero] at key
    haveI : (tupMeas lam 1 M).IsOpenPosMeasure := by
      unfold tupMeas
      haveI : (Measure.pi fun _ : Fin M => lam).IsOpenPosMeasure :=
        Measure.pi.isOpenPosMeasure (fun _ : Fin M => lam)
      exact Measure.pi.isOpenPosMeasure (fun _ : Fin 1 => Measure.pi fun _ : Fin M => lam)
    exact (hOo.measure_pos _ hne).ne' key

end GlobalTheory.GaugeEx.FibProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WittLow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem exists_repr (hnd : h.Nondegenerate) (f : V →ₗ[K] K) : ∃ w, h w = f := by
  have h0 : (LinearMap.range h).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact hnd.2 v fun x => hv _ ⟨x, rfl⟩
  have h1 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)
  rw [h0, Submodule.dualAnnihilator_bot] at h1
  have : f ∈ LinearMap.range h := by rw [← h1]; trivial
  exact this

theorem mem_of_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) (I : Submodule K V) (v : V)
    (hv : ∀ x, (∀ y ∈ I, h y x = 0) → h x v = 0) : v ∈ I := by
  by_contra hn
  obtain ⟨f, hf, hI⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨w, rfl⟩ := exists_repr hnd f
  refine hf (hv w fun y hy => ?_)
  have : h w y = 0 := by
    have : h w y ∈ I.map (h w) := ⟨y, hy, rfl⟩
    rwa [hI] at this
  rw [← hs.eq w y, this, map_zero]

theorem finrank_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) {i : ℕ} (e : Fin i → V) (he : LinearIndependent K e) :
    i + Module.finrank K (LinearMap.ker (LinearMap.pi fun j => h (e j))) = Module.finrank K V := by
  have hsurj : LinearMap.range (LinearMap.pi fun j => h (e j)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span he).constr K fun j => star (c j))
    obtain ⟨w, rfl⟩ := exists_repr hnd f
    refine ⟨w, funext fun j => ?_⟩
    have h1 := LinearMap.congr_fun hf (Module.Basis.span he j)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at h1
    rw [LinearMap.pi_apply, ← hs.eq w (e j), h1]
    exact star_star _
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j => h (e j))
  rw [hsurj, finrank_top] at this
  simpa using this

end Lin

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]


omit [NumberField E] in
theorem mem_dual {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 E) E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem exists_lower (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (V : HSpace E) {i : ℕ} (e : Fin i → V.V)
    (he : LinearIndependent E e) (hiso : ∀ a b, V.hT (e a) (e b) = 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), V'.rank + 2 * i = V.rank ∧ HSpace.IsIsomEmb V' V ι ∧
      ∀ x a, V.hT (ι x) (e a) = 0 := by
  have hs := V.herm
  have hnd := V.nondeg
  have hfg : V.L0.FG := V.standardTuple_isLattice.fg
  have hst1 : ∀ x : E, x ∈ (1 : Submodule (𝓞 E) E) → star x ∈ (1 : Submodule (𝓞 E) E) := by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
    exact Submodule.mem_one.2 ⟨⟨_, hst _ r.2⟩, rfl⟩
  have hL : ∀ x, x ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    rw [← mem_dual, V.baseLattice_isUnimodular]
  have hsp : Submodule.span E (V.L0 : Set V.V) = ⊤ := by
    by_contra hn
    obtain ⟨v, hv⟩ : ∃ v : V.V, v ∉ Submodule.span E (V.L0 : Set V.V) := by
      by_contra h
      apply hn
      apply eq_top_iff.mpr
      intro x _
      exact not_not.mp (fun hx => h ⟨x, hx⟩)
    obtain ⟨f, hf, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    obtain ⟨w, hw⟩ := exists_repr hnd f
    have hw0 : w ≠ 0 := by
      intro h
      apply hf
      rw [← hw, h, map_zero]
      rfl
    have hsmul (a : E) : a • w ∈ V.L0 := by
      rw [hL]
      intro y hy
      have hy0 : f y = 0 := by
        have : f y ∈ (Submodule.span E (V.L0 : Set V.V)).map f :=
          ⟨y, Submodule.subset_span hy, rfl⟩
        simpa [hfL] using this
      rw [map_smul, ← hs.eq w y, hw, hy0, map_zero, smul_zero]
      exact Submodule.zero_mem _
    let j : E →ₗ[𝓞 E] V.L0 :=
      ((LinearMap.toSpanSingleton E V.V w).restrictScalars (𝓞 E)).codRestrict V.L0 hsmul
    letI : Module.Finite (𝓞 E) V.L0 := Module.Finite.iff_fg.mpr hfg
    letI : Module.Finite (𝓞 E) E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective E hw0 (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  set I : Submodule E V.V := Submodule.span E (Set.range e) with hI
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (e j)) with hPdef
  have hP : ∀ x, x ∈ P ↔ ∀ y ∈ I, V.hT y x = 0 := by
    intro x
    constructor
    · intro hx y hy
      have : I ≤ LinearMap.ker (V.hT.flip x) := by
        rw [hI, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact congrFun hx j
      exact this hy
    · intro hx
      exact funext fun j => hx _ (Submodule.subset_span ⟨j, rfl⟩)
  have hIP : I ≤ P := by
    rw [hI, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact funext fun a => hiso a j
  have hPI : ∀ x ∈ P, ∀ y ∈ I, V.hT x y = 0 := fun x hx y hy => by
    rw [← hs.eq y x, (hP x).1 hx y hy, map_zero]
  obtain ⟨σ, σI, σid, σL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp I
  obtain ⟨π, πP, πid, πL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp P
  set W : Submodule E V.V := P ⊓ LinearMap.ker σ with hW
  have hsub : ∀ z ∈ P, z - σ z ∈ W := fun z hz =>
    ⟨P.sub_mem hz (hIP (σI z)), by
      change σ (z - σ z) = 0
      rw [map_sub, σid _ (σI z), sub_self]⟩
  have hsup : I ⊔ W = P := by
    refine le_antisymm (sup_le hIP inf_le_left) fun z hz => ?_
    rw [← add_sub_cancel (σ z) z]
    exact Submodule.add_mem_sup (σI z) (hsub z hz)
  have hinf : I ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨h1, -, h2⟩
    rw [Submodule.mem_bot, ← σid z h1]
    exact h2
  have hrk : Module.finrank E W + 2 * i = V.rank := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I W
    have h2 := finrank_orth hs hnd e he
    have h3 : Module.finrank E I = i := by rw [hI, finrank_span_eq_card he, Fintype.card_fin]
    rw [hsup, hinf, finrank_bot, h3] at h1
    rw [← hPdef, V.rank_eq] at h2
    omega

  have hWz : ∀ v ∈ W, ∀ z ∈ P, V.hT z v = V.hT (z - σ z) v := fun v hv z hz => by
    rw [map_sub, LinearMap.sub_apply, (hP v).1 hv.1 _ (σI z), sub_zero]
  have hrad : ∀ v : W, (∀ y : W, V.hT y v = 0) → v = 0 := by
    intro v hv
    have : (v : V.V) ∈ I := mem_of_orth hs hnd I v fun x hx => by
      rw [hWz v v.2 x ((hP x).2 hx)]
      exact hv ⟨_, hsub x ((hP x).2 hx)⟩
    have h2 : (v : V.V) ∈ I ⊓ W := ⟨this, v.2⟩
    rw [hinf] at h2
    exact Subtype.ext h2
  have hden : ∀ v : V.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ V.L0 := by
    intro v
    have hv : v ∈ Submodule.span E (V.L0 : Set V.V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (V.L0 : Set V.V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  let h' : W →ₗ⋆[E] W →ₗ[E] E := V.hT.domRestrict₁₂ W W
  have hh : ∀ x y : W, h' x y = V.hT x y := fun _ _ => rfl
  let j : W →ₗ[𝓞 E] V.V := W.subtype.restrictScalars (𝓞 E)
  let L' : Submodule (𝓞 E) W := V.L0.comap j
  have hL' : ∀ x : W, x ∈ L' ↔ (x : V.V) ∈ V.L0 := fun _ => Iff.rfl
  have hlat : Submodule.IsLattice E L' := by
    apply Submodule.IsLattice.of_fg E
    refine Submodule.fg_of_fg_map_injective j Subtype.val_injective ?_
    exact hfg.of_le (Submodule.map_comap_le _ _)
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L' := by
    ext v
    rw [mem_dual]
    refine ⟨fun hv => ?_, fun hv y hy => (hL _).1 hv _ hy⟩
    obtain ⟨w, hw⟩ := exists_repr hnd (V.hT v ∘ₗ π)
    have hw' : ∀ z, V.hT w z = V.hT v (π z) := fun z => LinearMap.congr_fun hw z
    have hwL : w ∈ V.L0 := by
      rw [hL]
      intro y hy
      rw [← hs.eq w y, hw', starRingEnd_apply, ← starRingEnd_apply, hs.eq, hWz v v.2 _ (πP y)]
      exact hv ⟨_, hsub _ (πP y)⟩ (V.L0.sub_mem (πL y hy) (σL _ (πL y hy)))
    have hwv : w - v ∈ I := mem_of_orth hs hnd I _ fun x hx => by
      rw [← hs.eq, map_sub, LinearMap.sub_apply, hw', πid x ((hP x).2 hx), sub_self, map_zero]
    have h1 := σid _ hwv
    rw [map_sub, show σ v = 0 from v.2.2, sub_zero] at h1
    rw [hL', show (v : V.V) = w - σ w by rw [h1]; abel]
    exact V.L0.sub_mem hwL (σL w hwL)
  have hs' : h'.IsSymm := ⟨fun x y => hs.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun x hx => hrad x fun y => by
    rw [← hs.eq, ← hh, hx, map_zero], fun x hx => hrad x hx⟩
  exact ⟨⟨W, h', hs', hnd', Module.finrank E W, rfl, Module.finBasis E W, fun _ => (0, 0), L', hlat, hun⟩, W.subtype,
    hrk, fun _ _ => rfl, fun x a => hPI _ x.2.1 _ (Submodule.subset_span ⟨a, rfl⟩)⟩

end Lat

variable {D : D7}

theorem exists_sig (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
    rw [← hτ]
    exact congrArg τ (V.herm.eq _ _)) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  exact ⟨(p, q), h⟩

theorem wittLowEx : ∀ D : D7, WittLowEx D := by
  rintro D V i ⟨C, hC⟩
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := exists_lower Examples₂.star_isIntegral V e he hiso
  choose s hs using exists_sig (D := D) V'
  refine ⟨{ V' with sig := s }, ⟨h1, ι, h2, _, hC, ?_⟩, hs⟩
  refine Matrix.ext fun a b => ?_
  rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
  exact h3 _ _

end GlobalTheory.WittLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
section
namespace GlobalTheory.Published

theorem GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt :
    GlobalArtinReciprocity → HeckeLAdicCharacter ∧ PrincipalIdealSt :=
  fun h => ⟨h.heckeLAdicCharacter, h.principalIdealSt⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  first | exact @GlobalTheory.OscGauss.inner_omAct0_adjZ | exact GlobalTheory.OscGauss.inner_omAct0_adjZ | (intros; apply GlobalTheory.OscGauss.inner_omAct0_adjZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_theorem_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ latV (M := M) (n := 1) b v, qR (Fv F v) σ J (y 0) = algebraMap F (Fv F v) β → ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y ∧ ∀ i j, ((HA.mat (Fv F v) σ J g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v ∧ ((HA.mat (Fv F v) σ J g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v := by
  first | exact @GlobalTheory.WittIntegral.witt_integral | exact GlobalTheory.WittIntegral.witt_integral | (intros; apply GlobalTheory.WittIntegral.witt_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem isCuspFun_closed : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  intro D V φ φ' h h' c c'
  refine ⟨?_, fun a r C hC μ 𝓕 hμ h𝓕 g => ?_, fun k r C hC μ 𝓕 hμ h𝓕 g => ?_, fun r C hC μ 𝓕 hμ h𝓕 g => ?_⟩
  · refine (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + φ') (h.cont.add h'.cont) fun γ hγ g => ?_).2
      (add_mem ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c)
        ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ' h'.cont h'.left).1 c'))
    rw [Pi.add_apply, Pi.add_apply, h.left γ hγ, h'.left γ hγ]
  · simp only [Pi.smul_apply]
    rw [integral_smul, c r C hC μ 𝓕 hμ h𝓕 g, smul_zero]
  · simp only [rTr, mul_assoc]
    exact c r C hC μ 𝓕 hμ h𝓕 (g * k)
  · have e := integral_conj (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun n : NI V C => φ ((n : GA D V) * g))
    rw [c r C hC μ 𝓕 hμ h𝓕 g, map_zero] at e
    exact e

end GlobalTheory.Mem.Th
end

