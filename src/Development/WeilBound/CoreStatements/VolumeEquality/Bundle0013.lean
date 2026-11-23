module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0137
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0139
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0012
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
open scoped ComplexOrder

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem stdZ_perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) := AddMonoidHom.mk' C.vec fun a b => by
    funext τ i
    simp [LatEmb.vec]
  have h : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    have e : C.vec (C.lam k) = C.bas k := by
      funext τ i
      exact (C.bas_eq k τ i).symm
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [e, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

theorem stdZ_sgU (τ : Ψ) {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : Aᴴ * C.sgr τ * A = sgI j j')
    (hA' : A'ᴴ * C.sgr τ * A' = sgI j j') : IsSgU (C.cinv A τ * A') := by
  have h1 := (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ A hA).2.1
  have e : A' = A * (C.cinv A τ * A') := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold IsSgU
  generalize C.cinv A τ * A' = v at e ⊢
  rw [e] at hA'
  refine Eq.trans ?_ hA'
  rw [← hA]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem stdZ_eqvBy_symm {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

omit [Fintype Ψ] in
theorem stdZ_zero_mem (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem stdZ_reach (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') :
    ∃ t ∈ ballDom F.q, C.IsAdapted (F.R t) A := by
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted.exists_isAdapted E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  have f1 := fun τ => _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ (A τ) (hA τ)
  obtain ⟨R', h1, h2, -, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (fun τ => A τ * C.cinv (A0 τ) τ)
    (fun τ => A0 τ * C.cinv (A τ) τ) (F.form_eq 0) (fun τ => by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.cinv (A0 τ) τ), (f0 τ).1, Matrix.one_mul, (f1 τ).2.1])
    (fun τ => (f0 τ).2.2.2.2.2 _ (hA τ))
  have h5 := h4 A0 hA0
  have e : (fun τ => A τ * C.cinv (A0 τ) τ * A0 τ) = A := by
    funext τ
    rw [Matrix.mul_assoc, (f0 τ).1, Matrix.mul_one]
  rw [e] at h5
  have hs : R'.HasSig F.σ j j' := by
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [h2]
    exact this
  obtain ⟨t, ht, he⟩ := (F.univ R' (h1.trans (F.form_eq 0)) hs).exists
  exact ⟨t, ht, _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy E Ψ j j' n g Λ F C R' (F.R t) A h5 (stdZ_eqvBy_symm he)⟩

end

theorem stdZ : StdZ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted.exists_isAdapted E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨Z, G, hZ, hG, hZeq, hpot⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists E Ψ j j' n g Λ F C A0 hA0
  have had : ∀ t ∈ ballDom F.q, ∃ A, C.IsAdapted (F.R t) A := fun t ht =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted.exists_isAdapted E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
  have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
    intro t ht
    obtain ⟨A, hA⟩ := had t ht
    rw [hZeq t ht A hA]
    exact (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props Ψ j j' n F.q _ fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)).2.1 h0
  have hinj : Set.InjOn Z (ballDom F.q) := by
    intro t ht t' ht' h
    obtain ⟨A, hA⟩ := had t ht
    obtain ⟨A', hA'⟩ := had t' ht'
    rw [hZeq t ht A hA, hZeq t' ht' A' hA'] at h
    have e : (fun τ => C.cinv (A0 τ) τ * A' τ) = fun τ => (C.cinv (A0 τ) τ * A τ) * (C.cinv (A τ) τ * A' τ) := by
      funext τ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A τ), (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ (A τ) (hA.unit τ)).2.1,
        Matrix.one_mul]
    rw [e] at h
    have h1 := (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff Ψ j j' n F.q _ _ (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ))
      (fun τ => stdZ_sgU C τ (hA.unit τ) (hA'.unit τ))).1 h
    have h2 := (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary E Ψ j j' n g Λ F C (F.R t) A A' (F.form_eq t) hA hA'.unit).2 h1
    have h3 := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (F.R t') A' (F.form_eq t) (F.form_eq t') h2 hA'
    exact (F.univ (F.R t') (F.form_eq _) (F.sig _ ht')).unique ⟨ht, h3⟩ ⟨ht', LinearEquiv.refl _ _, fun _ => rfl⟩
  have hsurj : Set.SurjOn Z (ballDom F.q) (ballDom F.q) := by
    intro s hs
    obtain ⟨w, hw, hws⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive Ψ j j' n F.q s hs
    obtain ⟨t, ht, hA⟩ := stdZ_reach C (fun τ => A0 τ * w τ) fun τ => by
      have hw' := hw τ
      unfold IsSgU at hw'
      rw [← hw']
      conv_rhs => rw [← hA0.unit τ]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨t, ht, ?_⟩
    rw [hZeq t ht _ hA, ← hws]
    congr 1
    funext τ
    rw [← Matrix.mul_assoc, (f0 τ).1, Matrix.one_mul]
  refine ⟨A0, hA0.unit, Z, ⟨hmaps, hinj, hsurj⟩, fun S hS hSD => ⟨?_, ?_⟩, ?_⟩
  · exact hS.image_of_continuousOn_injOn (hZ.continuousOn.mono hSD) (hinj.mono hSD)
  · exact ballMeas_image F.q hZ (fun t ht => hmaps ht) hinj
      (fun t ht => ballDens_transform F.q hZ hG (fun t ht => hmaps ht) hpot ht) hS hSD
  intro γ δ hδ _ hu t ht t' ht'
  obtain ⟨A, hA⟩ := had t ht
  let a : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  let ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    ((γ⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  have hai : ∀ τ, a τ * ai τ = 1 := fun τ => by
    simp only [a, ai]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hia : ∀ τ, ai τ * a τ = 1 := fun τ => mul_eq_one_comm.1 (hai τ)
  obtain ⟨R', h1, -, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R t) a ai (F.form_eq t) hai hu
  have h5 := h4 A hA
  have hP : ∀ x, R'.P (δ x) = (F.R t).P x := fun x => by
    rw [h3, ← stdZ_perExt_vec C (F.R t) x]
    congr 1
    funext τ
    have hv : C.vec (δ x) τ = a τ *ᵥ C.vec x τ := by
      funext i
      show embOf (F.σ τ) (C.e (δ x) i) = _
      rw [hδ]
      exact RingHom.map_mulVec _ _ _ i
    rw [hv, Matrix.mulVec_mulVec, hia, Matrix.one_mulVec]
  have hm : moebBall F.q (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ) (Z t) =
      moebBall F.q (fun τ => C.cinv (A0 τ) τ * (a τ * A τ)) 0 := by
    have hU : ∀ τ, IsSgU (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ τ) := fun τ =>
      ((f0 τ).2.2.2.2.1 _ _ (hai τ) (hu τ)).2.2.1
    rw [hZeq t ht A hA, ← _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul Ψ j j' n F.q _ _ hU (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)) 0 h0]
    congr 1
    funext τ
    show C.cinv (A0 τ) τ * (a τ * A0 τ) * (C.cinv (A0 τ) τ * A τ) = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A0 τ), (f0 τ).2.1, Matrix.one_mul]
  rw [hm]
  constructor
  · rintro ⟨k, hk⟩
    refine hZeq t' ht' _ (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy E Ψ j j' n g Λ F C R' (F.R t') _ h5 ⟨k, fun x => ?_⟩)
    obtain ⟨y, rfl⟩ := δ.surjective x
    exact (hk y).trans (congrArg k (hP y).symm)
  · intro h
    obtain ⟨t'', ht'', hA''⟩ := stdZ_reach C _ h5.unit
    obtain rfl : t'' = t' := hinj ht'' ht' ((hZeq t'' ht'' _ hA'').trans h.symm)
    obtain ⟨k, hk⟩ := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C R' (F.R t'') _ (h1.trans (F.form_eq t)) (F.form_eq _) h5 hA''
    exact ⟨k, fun x => (hk (δ x)).trans (congrArg k (hP x))⟩

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibA
section
noncomputable section

namespace SheetDecomposition.Fib

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

theorem ker_map {σ τ : Type} (k : Type) [Field k] [Algebra ℚ k] (g : σ → MvPolynomial τ ℚ) :
    RingHom.ker (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) =
      (RingHom.ker (aeval g : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ)).map (map (algebraMap ℚ k)) := by
  classical
  have hc : ∀ f : MvPolynomial σ ℚ, (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
      (map (algebraMap ℚ k) f) = map (algebraMap ℚ k) (aeval g f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [algebraMap_eq]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun f hf => ?_)
  · let b := Module.Basis.ofVectorSpace ℚ k
    let T : Finset _ := f.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff f m)).support
    let F : _ → MvPolynomial σ ℚ := fun i => ∑ m ∈ f.support, monomial m (b.repr (AddMonoidAlgebra.coeff f m) i)
    have hf' : f = ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (F i) := by
      conv_lhs => rw [f.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [F, map_sum, Finset.mul_sum, map_monomial, C_mul_monomial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum (monomial m)]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff f m), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun m => (b.repr (AddMonoidAlgebra.coeff f m)).support) hm)
          (fun i a => a • b i) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    have h0 : ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (aeval g (F i)) = 0 := by
      rw [RingHom.mem_ker, hf'] at hf
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, hc, aeval_C, algebraMap_eq] using hf
    have h1 : ∀ i ∈ T, aeval g (F i) = 0 := fun i hi => by
      ext m
      have := congrArg (AddMonoidAlgebra.coeff · m) h0
      simp only [coeff_sum, coeff_C_mul, coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
      refine linearIndependent_iff'.1 b.linearIndependent T (fun i => AddMonoidAlgebra.coeff (aeval g (F i)) m) ?_ i hi
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    rw [hf']
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h1 i hi))
  · rw [Ideal.mem_comap, RingHom.mem_ker, hc, (RingHom.mem_ker.1 hf : aeval g f = 0), map_zero]

variable {S : Type} {r : S → ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

abbrev Ent (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

def genU (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s)) (MvPolynomial (Ent r) ℚ) := fun l m =>
  if h : m < l then X ⟨s, ⟨(l, m), h⟩⟩ else if l = m then 1 else 0

def genMinor (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial (Ent r) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin (x.1.2 + 1) => genU r x.1.1 (x.2 a) (Fin.castLE x.1.2.2 b))

def genCone (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) ℚ :=
  rename Sum.inr (genMinor r x) * X (Sum.inl x.1)

def uNum (r : S → ℕ) {n : ℕ} (a : Fin n → (Σ s, Fin (r s)) → ℤ) : ℤ :=
  @intNum _ (fun _ _ => Classical.propDecidable _) (PlIx r) ℚ _
    (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)) n a

theorem plPt_eq [Algebra ℚ Ω] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (x) :
    plPt u x = aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genMinor r x) := by
  have e : ∀ s l m, aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genU r s l m) = u s l m := fun s l m => by
    unfold genU
    split_ifs with h h'
    · simp
    · subst h'; simp [h1]
    · rw [map_zero, h0 s l m (lt_of_le_of_ne (not_lt.1 h) h')]
  unfold plPt genMinor
  rw [AlgHom.map_det]
  congr 1
  ext a b
  exact (e _ _ _).symm

theorem pointIdeal_plPt [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    pointIdeal k (plPt u) =
      (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)).map (map (algebraMap ℚ k)) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  let φ : MvPolynomial (Ent r) k →ₐ[k] Ω := aeval fun q : Ent r => u q.1 q.2.1.1 q.2.1.2
  have hφ : Function.Injective φ := h.2.2.1
  let Θ : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) k →+* MvPolynomial (Σ s, Fin (r s)) Ω :=
    (map φ.toRingHom).comp (sumAlgEquiv k _ _).toRingHom
  have hΘ : Function.Injective Θ := (map_injective _ hφ).comp (sumAlgEquiv k _ _).injective
  have hr : ∀ f : MvPolynomial (Ent r) ℚ, Θ (map (algebraMap ℚ k) (rename Sum.inr f)) =
      C (aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [Θ, φ]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f i hf => simp only [map_mul, hf]; simp [Θ, φ]
  have key : (pointConeMap k (plPt u) : MvPolynomial _ k →+* MvPolynomial _ Ω) = Θ.comp
      (aeval (fun s => map (algebraMap ℚ k) (genCone r s)) : MvPolynomial _ k →ₐ[k] MvPolynomial _ k).toRingHom := by
    refine ringHom_ext (fun a => ?_) fun x => ?_
    · simp [pointConeMap, Θ, φ, algebraMap_eq]
    · simp only [pointConeMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply, genCone, map_mul, hr, plPt_eq u h.1 h.2.1]
      simp [Θ]
  rw [← ker_map]
  ext f
  rw [pointIdeal, RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff Θ hΘ]
  exact (RingHom.congr_fun key f).congr_left

theorem inum_plPt [Fintype S] [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) {n : ℕ}
    (a : Fin n → (Σ s, Fin (r s)) → ℤ) : inum k (plPt u) a = uNum r a := by
  unfold inum uNum
  rw [pointIdeal_plPt u h]
  exact (@GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ _ k _ _ _ _ (fun _ _ => Classical.propDecidable _)
    (PlIx r) _ _).2 n a

def rowIx {n : ℕ} (m l : Fin n) : Fin (m + 1) → Fin n := fun a => if a = Fin.last m then l else Fin.castLE m.2 a

theorem plPt_row (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (s : S) (m l : Fin (r s)) : plPt u ⟨⟨s, m⟩, rowIx m l⟩ = u s l m := by
  unfold plPt
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · simp only [Matrix.of_apply, rowIx, if_true]
      rfl
    · intro a _
      simp only [Matrix.of_apply, rowIx, if_neg (Fin.castSucc_lt_last a).ne, h1]
  · intro a b hab
    have hab' : a < b := hab
    simp only [Matrix.of_apply, rowIx, if_neg (hab'.trans_le (Fin.le_last b)).ne]
    exact h0 _ _ _ hab'

theorem plPt_ne (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (b) : ∃ i, plPt u ⟨b, i⟩ ≠ 0 :=
  ⟨rowIx b.2 b.2, by rw [show b = ⟨b.1, b.2⟩ from rfl, plPt_row u h1 h0, h1]; exact one_ne_zero⟩

theorem fnField_plPt [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) : fnField k (plPt u) =
      IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
  · have : ∀ x, plPt u x ∈ IntermediateField.adjoin k
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := fun x => by
      unfold plPt
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ =>
        IntermediateField.subset_adjoin _ _ ⟨⟨_, _, _⟩, rfl⟩)
    rintro _ ⟨p, q, -, rfl⟩
    exact div_mem (this p) (this q)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨⟨⟨s, m⟩, rowIx m l⟩, ⟨⟨s, m⟩, rowIx m m⟩, rfl, ?_⟩
    rw [plPt_row u h1 h0, plPt_row u h1 h0, h1, div_one]

theorem vdeg_plDeg [Fintype S] (O : ValuationSubring Ω) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (b : Σ s, Fin (r s)) :
    vdeg O (plPt u) (plDeg b) = (Finset.univ.sup fun i => O.valuation (plPt u ⟨b, i⟩))⁻¹ := by
  unfold vdeg
  rw [Finset.prod_eq_single b (fun b' _ h => by simp [plDeg, h]) (by simp)]
  simp [plDeg]

theorem trdeg_eq [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    Algebra.trdeg k Ω = Nat.card (Ent r) := by
  obtain ⟨h1, h0, hi, hd, hf⟩ := h
  have e : IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k (Set.range fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro _ ⟨⟨s, l, m⟩, rfl⟩
      rcases lt_trichotomy l m with h | h | h
      · simp only [h0 s l m h]; exact zero_mem _
      · subst h; simp only [h1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l, m), h⟩, rfl⟩
    · rintro _ ⟨⟨s, ⟨l, m⟩, h⟩, rfl⟩
      exact ⟨⟨s, l, m⟩, rfl⟩
  rw [e] at hf
  have := Module.finite_of_finrank_pos (hf ▸ hd)
  have hb : IsTranscendenceBasis k fun q : Ent r => u q.1 q.2.1.1 q.2.1.2 :=
    hi.isTranscendenceBasis_iff_isAlgebraic.2 (IntermediateField.isAlgebraic_adjoin_iff_top.1 inferInstance)
  rw [← hb.cardinalMk_eq_trdeg]
  exact (Nat.cast_card).symm

end SheetDecomposition.Fib
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
section
noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum mixedDiff diffStep)

theorem intNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F] (I : Ideal (MvPolynomial (Σ k, ι k) F))
    {n m : ℕ} (a : Fin n → K → ℤ) (b : Fin m → K → ℤ) (h : (List.ofFn a).Perm (List.ofFn b)) : intNum F I a = intNum F I b := by
  have : LeftCommutative (diffStep (K := K)) := ⟨fun x y g => by
    funext z
    simp only [diffStep, sub_right_comm z x y]
    ring⟩
  unfold intNum mixedDiff
  rw [h.foldr_eq]

theorem monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι) {d : ℕ}
    (w : Fin d → J) :
    (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a).Perm (List.ofFn fun j => (l (w j)).a) := by
  have h1 : Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ) = (List.ofFn w : Multiset J) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map w Finset.univ.val), Multiset.map_map]
    rfl
  have h2 : (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.Perm (List.ofFn w) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, h1]
  have h4 : (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a) =
      ((Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList).map fun x => (l x).a := by
    refine List.ext_getElem (by simp) fun i h h' => ?_
    have hi : i < (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.length := by simpa using h'
    simp only [List.getElem_ofFn, List.getElem_map, monoLines, dif_pos hi, List.get_eq_getElem]
  rw [h4]
  have h5 := h2.map fun x => (l x).a
  rwa [List.map_ofFn] at h5

theorem monoLines_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι)
    (hl : ∀ j, IsSmoothHerm (l j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) : IsSmoothHerm (monoLines l m d k) := by
  unfold monoLines
  split_ifs
  · exact hl _
  · exact contDiffOn_const

variable {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)

open Classical in
theorem geoFun_word (hI : PB.Inputs) (w : Fin (dimFl Ψ N) → Ψ × Fin N) :
    M.geoFun (toA (∏ j, X (w j))) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => M.xdeg (w j) : ℤ) := by
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h2 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ).degree = dimFl Ψ N := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  have hs : ∀ j, IsSmoothHerm (M.line 1 j) := fun j => by
    cases j
    · exact M.A_smooth
    · exact M.x_smooth _ _
  have h4 := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P (dimFl Ψ N)
    (monoLines (M.line 1) (∑ j, Finsupp.single (some (w j)) 1) (dimFl Ψ N)) M.arith (monoLines_smooth _ hs _ _)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.geoFun, Module.Basis.constr_basis, RootModel.geoMono, if_pos h2, h3, pow_zero, mul_one, div_mul_cancel₀ _ hδ]
  refine h4.trans (congrArg _ ?_)
  refine (intNum_perm _ _ _ (monoLines_perm (M.line 1) fun j => some (w j))).trans ?_
  simp only [RootModel.line, M.x_deg]

open Classical in
theorem geoFun_prod (hI : PB.Inputs) (c : Fin (dimFl Ψ N) → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => ∑ x, c j x • M.xdeg x : ℤ) := by
  obtain ⟨F, hF⟩ := exists_multilinear_gen (P := M.P) M.arith
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hF, F.map_sum, Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, F.map_smul_univ, smul_eq_mul, smul_eq_mul, mul_assoc, geoFun_word M hI, hF, Int.cast_mul]
  rfl

theorem test_pointIdeal_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [h : Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) : pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : h = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

theorem geoTest : GeoTest := by
  intro hI Ψ _ _ p q M _ n r e hq hn
  have hc : n + r = dimFl Ψ (p + q) := by
    rw [hn, ← count_pairs, ← Fintype.card_congr e, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  have key : ∀ (d : ℕ) (_ : d = dimFl Ψ (p + q)) (c : Fin d → Ψ × Fin (p + q) → ℤ),
      M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ = inum ℚ M.y fun j => ∑ x, c j x • M.xdeg x := by
    rintro _ rfl c
    rw [inum, test_pointIdeal_rat]
    convert geoFun_prod M hI c
    rfl
  rw [test_factor e hq hn, key _ hc]
  congr 2
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left, sum_muCoef, muDeg]
  · simp only [Fin.append_right, sum_fibCoef, fibDeg]

end SheetDecomposition
end
end

