module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelNeTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteTopologyProdMap
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Function
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TwUnfold

theorem mk_eq_iff_twConjugate {R : Type*} [Group R] (θ : Monoid.End R) (c : Quot (TwConjugate θ)) (d : R) :
    Quot.mk _ d = c ↔ TwConjugate θ (Quot.out c) d := by
  have hr : ∀ x, TwConjugate θ x x := fun x => ⟨1, by simp [twConj]⟩
  have hs : ∀ {x y}, TwConjugate θ x y → TwConjugate θ y x := by
    rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  have ht : ∀ {x y z}, TwConjugate θ x y → TwConjugate θ y z → TwConjugate θ x z := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul]
    group
  have he : Equivalence (TwConjugate θ) := ⟨hr, hs, ht⟩
  constructor
  · intro h
    have h1 : Quot.mk (TwConjugate θ) (Quot.out c) = Quot.mk _ d := by rw [Quot.out_eq, h]
    exact he.eqvGen_iff.1 (Quot.eqvGen_exact h1)
  · intro h
    rw [← Quot.sound h, Quot.out_eq]

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thetaA_ratGL (n : ℕ) (d : GL (Fin n) E) : thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

theorem discreteTopology_prodMap : DiscreteTopology ((ratGL E a).prodMap (ratGL E b)).range := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := a)
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := b)
  let f : ((ratGL E a).prodMap (ratGL E b)).range → (ratGL E a).range × (ratGL E b).range := fun z =>
    (⟨z.1.1, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.1, congrArg Prod.fst hw⟩⟩,
     ⟨z.1.2, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.2, congrArg Prod.snd hw⟩⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hi : Injective f := by
    intro z w h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun p => (p.1 : GA E a)) h
    · exact congrArg (fun p => (p.2 : GA E b)) h
  exact DiscreteTopology.of_continuous_injective hf hi

theorem finite_pair {φ : GA E a × GA E b → ℂ} (hφ : HasCompactSupport φ) {L : Set (GA E a × GA E b)} (hL : IsCompact L) :
    {d : GL (Fin a) E × GL (Fin b) E | ∃ x ∈ L,
      φ (twConj (thetaA E a) x.1 (ratGL E a d.1), twConj (thetaA E b) x.2 (ratGL E b d.2)) ≠ 0}.Finite := by
  have hθ₁ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := a)
  have hθ₂ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := b)
  have hL₁ : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hL₂ : IsCompact (Prod.snd '' L) := hL.image continuous_snd
  have hS₁ : IsCompact (Prod.fst '' tsupport φ) := IsCompact.image hφ continuous_fst
  have hS₂ : IsCompact (Prod.snd '' tsupport φ) := IsCompact.image hφ continuous_snd
  have hK₁ := (hL₁.mul hS₁).mul (hL₁.image hθ₁).inv
  have hK₂ := (hL₂.mul hS₂).mul (hL₂.image hθ₂).inv
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₁).prod (GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₂)).subset ?_
  rintro ⟨d₁, d₂⟩ ⟨x, hx, h⟩
  have hs := subset_tsupport _ h
  constructor
  · change ratGL E a d₁ ∈ Prod.fst '' L * Prod.fst '' tsupport φ * (thetaA E a '' (Prod.fst '' L))⁻¹
    have hd : ratGL E a d₁ = x.1 * twConj (thetaA E a) x.1 (ratGL E a d₁) * (thetaA E a x.1)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
  · change ratGL E b d₂ ∈ Prod.snd '' L * Prod.snd '' tsupport φ * (thetaA E b '' (Prod.snd '' L))⁻¹
    have hd : ratGL E b d₂ = x.2 * twConj (thetaA E b) x.2 (ratGL E b d₂) * (thetaA E b x.2)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩)

theorem chiT_norm_le (τ : ℝ) {n : ℕ} (x : GA E n) : ‖(chiT τ x : ℂ)‖ ≤ 1 := by
  by_cases h : x ∈ cutSet E n τ <;> simp [chiT, h]

theorem mem_cutSet_of_chiT_ne_zero {τ : ℝ} {n : ℕ} {x : GA E n} (h : (chiT τ x : ℂ) ≠ 0) : x ∈ cutSet E n τ := by
  by_contra hx
  exact h (by simp [chiT, hx])

end Adelic

theorem unfold2_of (hM : Mahler) : Unfold2 := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨hc₁, hi₁, C₁, hC₁, hs₁⟩ := hM E a τ
  obtain ⟨hc₂, hi₂, C₂, hC₂, hs₂⟩ := hM E b τ
  let ι : GL (Fin a) E × GL (Fin b) E →* GA E a × GA E b := (ratGL E a).prodMap (ratGL E b)
  let θ : Monoid.End (GA E a × GA E b) := (thetaA E a).prodMap (thetaA E b)
  let θR : Monoid.End (GL (Fin a) E × GL (Fin b) E) := (thetaE E a).prodMap (thetaE E b)
  haveI : DiscreteTopology ι.range := discreteTopology_prodMap
  haveI : Countable ι.range := by
    haveI : SecondCountableTopology ι.range := inferInstance
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  have hι : Injective ι :=
    GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL.prodMap GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL
  haveI : Countable (GL (Fin a) E × GL (Fin b) E) :=
    Injective.countable (f := ι.rangeRestrict) (fun x y h => hι (congrArg Subtype.val h))
  have hθ : ∀ r, ι (θR r) = θ (ι r) := fun r => Prod.ext (thetaA_ratGL a r.1).symm (thetaA_ratGL b r.2).symm
  have hFd : IsFundamentalDomain ι.range (F₁ ×ˢ F₂) (μ₁.prod μ₂) :=
    GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ hF₁ hF₂
  let cls : GL (Fin a) E × GL (Fin b) E → TwClass E a × TwClass E b := fun d => (Quot.mk _ d.1, Quot.mk _ d.2)
  let rep : TwClass E a × TwClass E b → GL (Fin a) E × GL (Fin b) E := fun c => (Quot.out c.1, Quot.out c.2)
  have hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d := by
    rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩
    constructor
    · intro h
      obtain ⟨g₁, h₁⟩ := (mk_eq_iff_twConjugate _ c₁ d₁).1 (congrArg Prod.fst h)
      obtain ⟨g₂, h₂⟩ := (mk_eq_iff_twConjugate _ c₂ d₂).1 (congrArg Prod.snd h)
      exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩
    · rintro ⟨g, hg⟩
      exact Prod.ext ((mk_eq_iff_twConjugate _ c₁ d₁).2 ⟨g.1, congrArg Prod.fst hg⟩)
        ((mk_eq_iff_twConjugate _ c₂ d₂).2 ⟨g.2, congrArg Prod.snd hg⟩)
  let H : TwClass E a × TwClass E b → Subgroup (GA E a × GA E b) := fun c =>
    (ratCent (Quot.out c.1)).prod (ratCent (Quot.out c.2))
  have hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c := by
    rintro c ⟨g₁, g₂⟩
    constructor
    · rintro ⟨⟨t₁, h₁, rfl⟩, ⟨t₂, h₂, rfl⟩⟩
      exact ⟨(t₁, t₂), rfl, Prod.ext h₁ h₂⟩
    · rintro ⟨t, ht, hc⟩
      exact ⟨⟨t.1, congrArg Prod.fst hc, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd hc, congrArg Prod.snd ht⟩⟩
  have hmχ : ∀ (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)], IsClosed (cutSet E n τ) →
      Measurable (chiT τ : GA E n → ℂ) := fun n _ _ h => measurable_one.indicator h.measurableSet
  have hχm : Measurable fun x : GA E a × GA E b => (chiT τ x.1 * chiT τ x.2 : ℂ) :=
    ((hmχ a hc₁).comp measurable_fst).mul ((hmχ b hc₂).comp measurable_snd)
  have hχb : ∀ x : GA E a × GA E b, ‖(chiT τ x.1 * chiT τ x.2 : ℂ)‖ ≤ 1 := fun x => by
    rw [norm_mul]
    exact mul_le_one₀ (chiT_norm_le τ _) (norm_nonneg _) (chiT_norm_le τ _)
  have hinv : ∀ (n : ℕ), (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) → ∀ g (x : GA E n),
      (chiT τ (ratGL E n g * x) : ℂ) = chiT τ x := fun n h g x => by
    by_cases hx : x ∈ cutSet E n τ
    · simp [chiT, hx, (h g x).2 hx]
    · simp [chiT, hx, mt (h g x).1 hx]
  have hχi : ∀ (r : GL (Fin a) E × GL (Fin b) E) (x : GA E a × GA E b),
      (chiT τ (ι r * x).1 * chiT τ (ι r * x).2 : ℂ) = chiT τ x.1 * chiT τ x.2 := fun r x => by
    change (chiT τ (ratGL E a r.1 * x.1) * chiT τ (ratGL E b r.2 * x.2) : ℂ) = _
    rw [hinv a hi₁, hinv b hi₂]
  have hχK : ∀ x : GA E a × GA E b, (chiT τ x.1 * chiT τ x.2 : ℂ) ≠ 0 → ∃ r, ∃ k ∈ C₁ ×ˢ C₂, x = ι r * k := by
    intro x hx
    obtain ⟨_, ⟨r₁, rfl⟩, k₁, hk₁, e₁⟩ := Set.mem_mul.1 (hs₁ (mem_cutSet_of_chiT_ne_zero (left_ne_zero_of_mul hx)))
    obtain ⟨_, ⟨r₂, rfl⟩, k₂, hk₂, e₂⟩ := Set.mem_mul.1 (hs₂ (mem_cutSet_of_chiT_ne_zero (right_ne_zero_of_mul hx)))
    exact ⟨(r₁, r₂), (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁.symm e₂.symm⟩
  have hθc : Continuous θ := (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_fst).prodMk
    (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_snd)
  have hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d)) := fun d =>
    (hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθc)).measurable
  haveI : T2Space (GA E a × GA E b) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  obtain ⟨B, hB⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  have key := unfold_abs (μ := μ₁.prod μ₂) (ι := ι) (θ := θ) (θR := θR) (cls := cls) (rep := rep) (H := H)
    (χ := fun x => chiT τ x.1 * chiT τ x.2) (φ := φ) hι hθ hFd hcls hH hχm hχb hχi (hC₁.prod hC₂) hχK hφm hB
    (fun L hL => finite_pair hφ.supp hL)
  exact key

end GlobalTheory.CompanionTheory.TwUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

namespace Core

variable {D : D7}

theorem continuous_trA_AE : Continuous (trA (D := D)) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

theorem continuous_halfTr_AE : Continuous (halfTr (D := D)) := by
  unfold halfTr
  exact continuous_const.mul continuous_trA_AE

theorem continuous_inner_pair (V : HSp D) {n : ℕ} {X : Type*} [TopologicalSpace X] {u v : X → Mx D V.rank n}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => inner V (u x) (v x) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold StdUnn.inner
  exact (continuous_adj.comp hu).matrix_mul (continuous_const.matrix_mul hv)

theorem continuous_colJoin_left {X : Type*} [TopologicalSpace X] {m r s : ℕ} {u : X → Mx D m r} (hu : Continuous u)
    (v : Mx D m s) : Continuous fun x => colJoin (u x) v := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [colJoin_castAdd]
    exact hu.matrix_elem i j
  · simp only [colJoin_natAdd]
    exact continuous_const

theorem continuous_quad (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun t : Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr_AE.comp
    (continuous_const.matrix_mul (continuous_inner_pair V continuous_id continuous_id)).matrix_trace)

theorem continuous_lin (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (x : Mx D V.rank s) :
    Continuous fun y : Mx D V.rank s => ψ (trA (Matrix.trace (inner V x y))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_trA_AE.comp
    (continuous_inner_pair V continuous_const continuous_id).matrix_trace)

theorem enorm_char (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (x : AF D.host.F) : ‖ψ x‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, hψ.2.1, ENNReal.ofReal_one]

theorem join_mul_eq {m r s : ℕ} (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) (y : Mx D m r) :
    HMul.hMul (colJoin (rat p - y) (rat q)) (rat a) =
      rat (colJoin p q * a) + -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) := by
  have h : colJoin (rat p - y) (rat q) = colJoin (rat p) (rat q) - colJoin y (0 : Mx D m s) := by
    rw [← colJoin_sub, sub_zero]
  rw [h, Matrix.sub_mul, rat_mul, rat_colJoin, sub_eq_add_neg]

theorem join_mul_injective {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det) :
    Function.Injective fun pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E =>
      colJoin pq.1 pq.2 * a := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have h' : colJoin p q = colJoin p' q' := by
    have := congrArg (· * a⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha] using this
  obtain ⟨h1, h2⟩ := colJoin_injective h'
  rw [h1, h2]

theorem tsum_join_le {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D m (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D m r) :
    ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
      ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ ≤ B := by
  set w : Mx D m (r + s) := -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) with hw
  calc ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
        ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ
      = ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
          (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ) (colJoin pq.1 pq.2 * a) := by
        refine tsum_congr fun pq => ?_
        simp only [join_mul_eq, hw]
    _ ≤ ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective (join_mul_injective (m := m) ha) (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ)
    _ ≤ B := hB w

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  exact inferInstanceAs (Countable (Fin m → Fin n → D.host.E))

theorem enorm_cellTerm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    ‖cellTerm ψ V b a Φ p q y₁ y₂‖ₑ = ‖Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))‖ₑ := by
  simp only [cellTerm, enorm_mul, enorm_char ψ hψ, one_mul]

def cellRest (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))

theorem continuous_cellRest (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) : Continuous (cellRest ψ V b a Φ p q) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  haveI : ContinuousSub (Mx D V.rank r) := IsTopologicalAddGroup.to_continuousSub
  have h1 : Continuous fun y₁ : Mx D V.rank r => y₁ - rat p := continuous_id.sub continuous_const
  have h2 : Continuous fun y₁ : Mx D V.rank r => rat p - y₁ :=
    (continuous_const (y := rat p)).sub continuous_id
  exact ((continuous_quad ψ hψ V b).comp h1).mul
    (hΦ.comp ((continuous_colJoin_left h2 _).matrix_mul continuous_const))

def cellZero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ) (t : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a))

theorem cellRest_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D V.rank r) :
    cellRest ψ V b a Φ p 0 y = cellZero ψ V b a Φ (y - rat p) := by
  simp only [cellRest, cellZero, rat_zero, neg_sub]

theorem continuous_cellZero (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) : Continuous (cellZero (s := s) ψ V b a Φ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  exact (continuous_quad ψ hψ V b).mul
    (hΦ.comp ((continuous_colJoin_left continuous_neg _).matrix_mul continuous_const))

theorem tsum_cellZero_le (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D V.rank (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D V.rank r) :
    ∑' p : Matrix (Fin V.rank) (Fin r) D.host.E, ‖cellZero (s := s) ψ V b a Φ (y - rat p)‖ₑ ≤ B := by
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  refine le_trans (le_of_eq (tsum_congr fun p => ?_))
    ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (tsum_join_le (s := s) ha hB y))
  simp only [cellZero, enorm_mul, enorm_char ψ hψ, one_mul, neg_sub, rat_zero]

end Core

theorem integral_cells_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  intro D ψ hψ V r s μr 𝓕r μs 𝓕s hr hs b a ha Φ hΦ B hB
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D V.rank s
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  haveI := Core.countable_mat D V.rank r
  haveI := Core.countable_mat D V.rank s
  haveI : IsFiniteMeasure (μr.restrict 𝓕r) := ⟨by simp [hr.2.2]⟩
  haveI : IsFiniteMeasure (μs.restrict 𝓕s) := ⟨by simp [hs.2.2]⟩
  rw [← Measure.prod_restrict]
  have hνu : ((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp [hr.2.2, hs.2.2]
  have hform : ∀ (pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E)
      (z : Mx D V.rank r × Mx D V.rank s), cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 =
        Core.cellRest ψ V b a Φ pq.1 pq.2 z.1 * ψ (trA (Matrix.trace (inner V (rat pq.2) z.2))) :=
    fun pq z => mul_comm _ _
  have hcont : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      Continuous fun z : Mx D V.rank r × Mx D V.rank s => cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 := fun pq => by
    simp only [hform]
    exact ((Core.continuous_cellRest ψ hψ V b a hΦ pq.1 pq.2).comp continuous_fst).mul
      ((Core.continuous_lin ψ hψ V (rat pq.2)).comp continuous_snd)
  have hsum : ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫⁻ z, ‖cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2‖ₑ ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) ≠ ∞ := by
    rw [← lintegral_tsum fun pq => (hcont pq).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := fun _ => (B : ℝ≥0∞)) fun z => ?_)
    · simp [hνu]
    · simp only [Core.enorm_cellTerm ψ hψ]
      exact Core.tsum_join_le ha hB z.1
  rw [integral_tsum (fun pq => (hcont pq).aestronglyMeasurable) hsum]
  have hterm : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫ z, cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) =
        (∫ y in 𝓕r, Core.cellRest ψ V b a Φ pq.1 pq.2 y ∂μr) *
          ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat pq.2) y))) ∂μs := fun pq => by
    simp only [hform]
    exact integral_prod_mul (Core.cellRest ψ V b a Φ pq.1 pq.2)
      (fun y => ψ (trA (Matrix.trace (inner V (rat pq.2) y))))
  simp only [hterm]
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← hinj.tsum_eq]
  · obtain ⟨-, hu⟩ := GlobalTheory.CompanionTheory.EisUnfold.Lattice.tsum_setIntegral_sub_rat D V.rank r μr 𝓕r hr (Core.cellZero (s := s) ψ V b a Φ)
      (Core.continuous_cellZero ψ hψ V b a hΦ) B (Core.tsum_cellZero_le ψ hψ V b ha hB)
    refine Eq.trans (tsum_congr fun p => ?_) hu
    simp only [(GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality D ψ hψ V s μs 𝓕s hs 0).1 rfl, mul_one, Core.cellRest_zero]
  · rintro ⟨p, q⟩ hne
    by_cases hq : q = 0
    · exact ⟨p, by rw [hq]⟩
    · exact absurd (by simp only [(GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality D ψ hψ V s μs 𝓕s hs q).2 hq, mul_zero]) hne

end GlobalTheory.CompanionTheory.EisUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AdeleComp

open TensorProduct

theorem coord_zero {F A B E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (ℬ : Module.Basis ι F E) (f : A →ₗ[F] B) (c : ι →₀ A)
    (h : LinearMap.rTensor E f (c.sum fun i m => m ⊗ₜ[F] ℬ i) = 0) (i : ι) : f (c i) = 0 := by
  have h1 : (c.mapRange f (map_zero f)).sum (fun i m => m ⊗ₜ[F] ℬ i) = 0 := by
    rw [Finsupp.sum_mapRange_index (by intro i; simp)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h, Finsupp.sum, Finsupp.sum, map_sum]
    simp
  have h2 := TensorProduct.sum_tmul_basis_right_eq_zero ℬ _ h1
  simpa using DFunLike.congr_fun h2 i

theorem adele_eq_zero {F : Type} [Field F] [NumberField F] (x : AF F)
    (hi : ∀ w, evInf F w x = 0) (hf : ∀ v, evFin F v x = 0) : x = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact RestrictedProduct.ext _ _ fun v => hf v

theorem tensor_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (a : AF F ⊗[F] E) (hi : ∀ w, compInf F E w a = 0) (hf : ∀ v, compFin F E v a = 0) : a = 0 := by
  let ℬ := Module.Basis.ofVectorSpace F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ a
  have hc : c = 0 := by
    ext i
    refine adele_eq_zero _ (fun w => ?_) (fun v => ?_)
    · refine coord_zero ℬ (evInf F w).toLinearMap c ?_ i
      rw [← hi w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [compInf, Finsupp.sum, map_sum]
      rfl
    · refine coord_zero ℬ (evFin F v).toLinearMap c ?_ i
      rw [← hf v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [compFin, Finsupp.sum, map_sum]
      rfl
  simp [hc]

theorem eq_zero_of_comps (D : D7) (a : AE D) (hi : ∀ w, compInf D.host.F D.host.E w a = 0)
    (hf : ∀ v, cv D v a = 0) : a = 0 :=
  tensor_eq_zero a hi hf

end GlobalTheory.CompanionTheory.AdeleComp
end

