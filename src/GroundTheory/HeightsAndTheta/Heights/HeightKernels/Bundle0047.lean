module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleStacked
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphHorizontal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StackedGraphHorizontal

theorem mul_mem_of_mem_sup {A : Type*} [CommRing A] {I : Ideal A} {g s : A} (hsg : s * g ∈ I) :
    ∀ x ∈ I ⊔ Ideal.span {g}, s * x ∈ I := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [mul_add, show s * (r * g) = r * (s * g) by ring]
  exact I.add_mem (I.mul_mem_left s hy) (I.mul_mem_left r hsg)

theorem length_localized_eq {A : Type*} [CommRing A] {I J W : Ideal A} [W.IsPrime] (hIJ : I ≤ J)
    {s : A} (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ I)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) := by
  let π : (A ⧸ I) →ₗ[A] (A ⧸ J) := Submodule.factor hIJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ I))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)) π
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective J y
    exact ⟨Submodule.mkQ I x, Submodule.factor_mk hIJ x⟩
  have hsurj : Function.Surjective φ := IsLocalizedModule.map_surjective _ _ _ π hπ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I m
      have hy' : LocalizedModule.mk (π (Submodule.mkQ I r)) t = 0 := by
        rw [← hy]
        exact (IsLocalizedModule.map_LocalizedModules W.primeCompl π _ t).symm
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy' ⊢
      obtain ⟨u, hu⟩ := hy'
      refine ⟨⟨s, hs⟩ * u, ?_⟩
      rw [one_smul, smul_zero, smul_zero] at hu ⊢
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submonoid.smul_def, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hu
      have hI : s * (u * r) ∈ I := hsJ _ hu
      rw [Submodule.mkQ_apply, Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      simpa [mul_assoc] using hI
  exact (LinearEquiv.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)
    (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)).length_eq

theorem multAt_eq_of_mul_mem {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]
    {I J W : Ideal (MRing ι)} (hIJ : I ≤ J) {s : MRing ι} (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    multAt I W = multAt J W := by
  by_cases hW : W.IsPrime
  · rw [multAt, multAt, dite_eq_left hW, dite_eq_left hW]
    exact congrArg ENat.toNat (length_localized_eq hIJ hs hsJ)
  · rw [multAt, multAt, dite_eq_right hW, dite_eq_right hW]

theorem sup_le_of_mul_mem {A : Type*} [CommRing A] {I Q : Ideal A} (hQ : Q.IsPrime) {f g s : A} (hs : s ∉ Q)
    (hsg : s * g ∈ I ⊔ Ideal.span {f}) (hle : I ⊔ Ideal.span {f} ≤ Q) : I ⊔ Ideal.span {g} ≤ Q := by
  refine sup_le (le_sup_left.trans hle) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact (hQ.mem_or_mem (hle hsg)).resolve_left hs

theorem mem_minimalPrimes_of_mul_mem {A : Type*} [CommRing A] {I W : Ideal A} {f g s s' : A} (hs : s ∉ W)
    (hs' : s' ∉ W) (hsg : s * g ∈ I ⊔ Ideal.span {f}) (hsf : s' * f ∈ I ⊔ Ideal.span {g})
    (hW : W ∈ (I ⊔ Ideal.span {f}).minimalPrimes) : W ∈ (I ⊔ Ideal.span {g}).minimalPrimes :=
  ⟨⟨hW.1.1, sup_le_of_mul_mem hW.1.1 hs hsg hW.1.2⟩, fun _ hQ hQW =>
    hW.2 ⟨hQ.1, sup_le_of_mul_mem hQ.1 (fun h => hs' (hQW h)) hsf hQ.2⟩ hQW⟩

variable {T : Type} [Fintype T] [DecidableEq T]

theorem mul_mem_sup_first (P : Ideal (MRing (dualBlocks T))) (a : T → ℤ) (l t : T) :
    (C (a l) * graphFirst l) * graphSecond t ∈
      graphIdeal P (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a)) ⊔ Ideal.span {C (a t) * graphFirst t} := by
  have h := TopDualSimpleStacked.minor_mem P a l t
  have e : (C (a l) * graphFirst l) * graphSecond t = graphSecond l * (C (a t) * graphFirst t) -
      (graphSecond l * (C (a t) * graphFirst t) - graphSecond t * (C (a l) * graphFirst l)) := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left h)

theorem mul_mem_sup_second (P : Ideal (MRing (dualBlocks T))) (a : T → ℤ) (l t : T) :
    graphSecond l * (C (a t) * graphFirst t) ∈
      graphIdeal P (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a)) ⊔ Ideal.span {graphSecond t} := by
  have h := TopDualSimpleStacked.minor_mem P a l t
  have e : graphSecond l * (C (a t) * graphFirst t) =
      (graphSecond l * (C (a t) * graphFirst t) - graphSecond t * (C (a l) * graphFirst l)) +
        (C (a l) * graphFirst l) * graphSecond t := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem C_mul_first_not_mem {P : Ideal (MRing (dualBlocks T))} {a : T → ℤ} (ha : ∀ t, a t ≠ 0)
    {W : Ideal (MRing (stackedBlocks T))} (hW : W.IsPrime) (hhor : IsHorizontal W)
    (hΓ : graphIdeal P (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a)) ≤ W) {j l : T} (hj : graphFirst j ∉ W)
    (hl : graphSecond l ∉ W) : C (a l) * graphFirst l ∉ W := by
  have hC : ∀ c : ℤ, c ≠ 0 → (C c : MRing (stackedBlocks T)) ∉ W := by
    intro c hc h
    have h' : c ∈ W.comap (C : ℤ →+* MRing (stackedBlocks T)) := h
    rw [hhor] at h'
    exact hc h'
  intro h
  have hm := hΓ (TopDualSimpleStacked.minor_mem P a l j)
  have h2 : graphSecond l * (C (a j) * graphFirst j) ∈ W := by
    have := W.add_mem hm (W.mul_mem_left (graphSecond j) h)
    rwa [sub_add_cancel] at this
  rcases hW.mem_or_mem h2 with h3 | h3
  · exact hl h3
  · rcases hW.mem_or_mem h3 with h4 | h4
    · exact hC _ (ha j) h4
    · exact hj h4

end StackedGraphHorizontal


open StackedGraphHorizontal in
theorem DualStackedGraphHorizontal.proof : DualStackedGraphHorizontal.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hab t W hhor
  have ha : ∀ t, a t ≠ 0 := by
    intro t h0
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h0, zero_smul]
    rfl
  have key : W.IsPrime → stackedGraph b' a ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
      ∃ s s' : MRing (stackedBlocks T), s ∉ W ∧ s' ∉ W ∧
        s * (C (a t) * graphFirst (T := T) t) ∈ stackedGraph b' a ⊔ Ideal.span {graphSecond (T := T) t} ∧
        s' * graphSecond (T := T) t ∈ stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst (T := T) t} := by
    intro hW hΓ hrel
    obtain ⟨j, hj⟩ := hrel (Sum.inl ())
    obtain ⟨l, hl⟩ := hrel (Sum.inr ())
    exact ⟨graphSecond (T := T) l, C (a l) * graphFirst (T := T) l, hl, C_mul_first_not_mem ha hW hhor hΓ hj hl,
      mul_mem_sup_second _ a l t, mul_mem_sup_first _ a l t⟩
  refine ⟨⟨fun hW => ?_, fun hW => ?_⟩, fun hW => ?_⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    exact ⟨mem_minimalPrimes_of_mul_mem hs hs' hsg hsf hW.1, hW.2⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    exact ⟨mem_minimalPrimes_of_mul_mem hs' hs hsf hsg hW.1, hW.2⟩
  · obtain ⟨s, s', hs, hs', hsg, hsf⟩ := key hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
    rw [multAt_eq_of_mul_mem le_sup_left hs (mul_mem_of_mem_sup hsg),
      multAt_eq_of_mul_mem (le_sup_left : stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst (T := T) t} ≤ _) hs'
        (mul_mem_of_mem_sup hsf), sup_right_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphImage

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [Fintype T] [DecidableEq T] in
theorem coord_stacked {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (p : Σ _ : Unit, T) :
    dualLatticeCoord b p = (a p.2 : ProjField K i) * dualLatticeCoord b' p := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dualLatticeCoord, hab p.2, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum,
    map_sum, mul_assoc]

def twist (Ω : Type) [Field Ω] : MvPolynomial Unit Ω →+* MvPolynomial Unit (MvPolynomial Unit Ω) :=
  eval₂Hom (C.comp C) fun u => C (X u) * X u

theorem twist_injective (Ω : Type) [Field Ω] : Function.Injective (twist Ω) := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω))).comp (twist Ω) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun u => ?_)
    · simp [twist]
    · simp [twist]
  exact Function.LeftInverse.injective (g := MvPolynomial.map (MvPolynomial.eval fun _ : Unit => (1 : Ω)))
    fun x => RingHom.congr_fun h x

theorem image_eq {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) :
    imageZ inrV (stackedGraph b' a) = dualIdeal b := by
  let ψ : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i) := mConeMap (dualLatticeCoord b')
  let ι : (MRing (dualBlocks T) ⧸ dualIdeal b') →+* MvPolynomial Unit (ProjField K i) :=
    Ideal.Quotient.lift (dualIdeal b') ψ fun x hx => RingHom.mem_ker.mp hx
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr hx)
  have hcomp : (MvPolynomial.map ι).comp ((graphMap (dualIdeal b') (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a))).comp
      (rename (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) :
        MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom) =
      (twist (ProjField K i)).comp (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* _) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp
    · obtain ⟨u, t⟩ := p
      cases u
      simp [graphMap, inrV, twist, mConeMap, TopDualSimpleStacked.linForm_stackedDiag, ι, ψ,
        coord_stacked hab]
      rw [show eval₂ (C.comp C) (fun u => C (X u) * X u) ((a t : ℤ) : MvPolynomial Unit (ProjField K i)) =
        ((a t : ℤ) : MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) from map_intCast (twist _) _]
      ring
  ext f
  have e := RingHom.congr_fun hcomp f
  simp only [RingHom.comp_apply] at e
  have e1 := map_eq_zero_iff _ (MvPolynomial.map_injective ι hι)
    (x := graphMap (dualIdeal b') (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a))
      ((rename (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) :
        MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T)).toRingHom f))
  have e2 := map_eq_zero_iff _ (twist_injective (ProjField K i))
    (x := (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) f)
  rw [e] at e1
  rw [imageZ, Ideal.mem_comap, stackedGraph, graphIdeal, RingHom.mem_ker, ← e1, e2]
  exact RingHom.mem_ker.symm

theorem fibre_deg (hGr : GraphStatement) (hDim : FibreDimStatement) {F F' : HermLattice K i}
    {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hi : 1 ≤ i) (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K))
    (G : GenFibre inrV (stackedGraph b' a))
    (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit)))
    (hJ : IsFieldIntersection J) :
    J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1 := by
  have hP' : IsArithVar (dualIdeal b') i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F' T b' hi
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i F T b hi
  have hprime : (dualIdeal b').IsPrime := hP'.2.1.1
  have ha : ∀ t, a t ≠ 0 := by
    intro t h0
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h0, zero_smul]
    rfl
  obtain ⟨t₀, ht₀⟩ := hP'.2.1.2.2 ()
  have hlin : (C (a t₀) * X ⟨(), t₀⟩ : MRing (dualBlocks T)) ∉ dualIdeal b' :=
    TopDualSimpleStacked.C_mul_X_not_mem hprime hP'.2.2.1 (ha t₀) ht₀
  have hform : ∀ q : Σ _ : Unit, T,
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a) q) ((fun _ _ => 1 : Unit → Unit → ℕ) q.1) := by
    rintro ⟨u, t⟩
    cases u
    rw [TopDualSimpleStacked.linForm_stackedDiag]
    have h := TopDualSimpleStacked.isMultiHomog_C_mul
      (TopDualSimpleStacked.isMultiHomog_X_int (ι := dualBlocks T) () t) (a t)
    have he : (Pi.single () 1 : Unit → ℕ) = fun _ => 1 := by
      funext u
      cases u
      simp
    rwa [he] at h
  have hΓ : IsArithVar (stackedGraph b' a) i :=
    (hGr Unit (dualBlocks T) Unit (dualBlocks T) (dualIdeal b') i (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (stackedDiag a)) (fun _ _ => 1) hP'
      hform (fun _ => ⟨t₀, by rw [TopDualSimpleStacked.linForm_stackedDiag]; exact hlin⟩)).1
  have hIm : IsArithVar (imageZ inrV (stackedGraph b' a)) i := by
    rw [image_eq hab]
    exact hP
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inr inrV _ i 0 G isBlockMap_inr hΓ hIm
  have hmem : ∀ f, f ∈ stackedGraph b' a ↔ aeval G.x' f = 0 := fun f => by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]

  have hx0 : G.x' ⟨Sum.inl (), t₀⟩ ≠ 0 := by
    intro h
    have hm : (X ⟨Sum.inl (), t₀⟩ : MRing (stackedBlocks T)) ∈ stackedGraph b' a :=
      (hmem _).2 (by rw [aeval_X]; exact h)
    rw [stackedGraph, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at hm
    exact ht₀ (Ideal.Quotient.eq_zero_iff_mem.1 (C_eq_zero.1 hm))
  have hy0 : G.x' ⟨Sum.inr (), t₀⟩ ≠ 0 := by
    intro h
    exact TopDualSimpleStacked.second_not_mem hprime a hlin
      ((hmem _).2 (by rw [graphSecond, aeval_X]; exact h))

  have haΦ : ∀ t, (a t : G.Φ) ≠ 0 := by
    intro t h
    have hm : (C (a t) : MRing (dualBlocks T)) ∈ dualIdeal b := by
      rw [← image_eq hab, ← G.ker_x, RingHom.mem_ker, aeval_C]
      simpa using h
    have h2 : a t ∈ (dualIdeal b).comap (C : ℤ →+* MRing (dualBlocks T)) := hm
    rw [hP.2.2.1] at h2
    exact ha t (Ideal.mem_bot.mp h2)

  have hrat : ∀ t, G.x' ⟨Sum.inl (), t⟩ / G.x' ⟨Sum.inl (), t₀⟩ =
      algebraMap G.Φ G.Φ' ((a t₀ : G.Φ) * G.x ⟨(), t⟩ / ((a t : G.Φ) * G.x ⟨(), t₀⟩)) := by
    intro t
    have hm := (hmem _).1 (TopDualSimpleStacked.minor_mem (dualIdeal b') a t₀ t)
    simp only [graphFirst, graphSecond, map_sub, map_mul, aeval_X, eq_intCast, map_intCast] at hm
    have c1 : G.x' ⟨Sum.inr (), t⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t⟩) := G.compat ⟨(), t⟩
    have c0 : G.x' ⟨Sum.inr (), t₀⟩ = algebraMap G.Φ G.Φ' (G.x ⟨(), t₀⟩) := G.compat ⟨(), t₀⟩
    have hat : (a t : G.Φ') ≠ 0 := by
      rw [← map_intCast (algebraMap G.Φ G.Φ')]
      exact (map_ne_zero _).2 (haΦ t)
    rw [map_div₀, map_mul, map_mul, map_intCast, map_intCast, ← c1, ← c0,
      div_eq_div_iff hx0 (mul_ne_zero hat hy0)]
    linear_combination hm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (stackedBlocks T) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => t₀
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact hx0
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (stackedBlocks T) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (stackedBlocks T) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, t⟩, rfl⟩
    · cases u
      exact IntermediateField.mem_bot.2 ⟨_, (hrat t).symm⟩
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end StackedGraphImage


open StackedGraphImage in
theorem DualStackedGraphImage.proof (hGr : GraphStatement) (hDim : FibreDimStatement) :
    DualStackedGraphImage.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hab
  exact ⟨image_eq hab, fun G J hJ => fibre_deg hGr hDim hi hab G J hJ⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂]

def intCoordSubst (A : Matrix T T₂ ℤ) : MRing (dualBlocks T₂) →ₐ[ℤ] MRing (dualBlocks T) :=
  aeval fun p => ∑ t, C (A t p.2) * X (⟨(), t⟩ : Σ _ : Unit, T)

def intCoordPt (A : Matrix T T₂ ℤ) (z : (Σ _ : Unit, T) → ℂ) : (Σ _ : Unit, T₂) → ℂ :=
  fun p => ∑ t, z ⟨(), t⟩ * (A t p.2 : ℂ)

theorem intCoordPt_ne_zero {A : Matrix T T₂ ℤ} (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    {z : (Σ _ : Unit, T) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, intCoordPt A z ⟨k, i⟩ ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := hA
  rintro ⟨⟩
  obtain ⟨t, ht⟩ := hz ()
  by_contra h
  push Not at h
  apply ht
  have h1 : ∀ t', (((A * B) t' t : ℤ) : ℂ) = ∑ s, (A t' s : ℂ) * (B s t : ℂ) := by
    intro t'
    simp [Matrix.mul_apply]
  have key : z ⟨(), t⟩ = ∑ s, intCoordPt A z ⟨(), s⟩ * (B s t : ℂ) := by
    simp only [intCoordPt, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← h1, hB, Matrix.one_apply]
    simp
  rw [key]
  exact Finset.sum_eq_zero fun s _ => by rw [h s, zero_mul]

def intCoordLine (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T) where
  a := L.a
  h z := L.h (intCoordPt A z)
  pos z hz := L.pos _ (intCoordPt_ne_zero hA hz)
  smul c z hc := by
    have hz : intCoordPt A (fun p => c p.1 * z p) = fun p => c p.1 * intCoordPt A z p := by
      funext p
      obtain ⟨⟨⟩, s⟩ := p
      simp only [intCoordPt, Finset.mul_sum, mul_assoc]
    rw [hz, L.smul c _ hc]

def IntCoordChange.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (hAB : A * B = 1), B * A = 1 → ∀ (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ (P : Ideal (MRing (dualBlocks T₂))) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)), 1 ≤ n → IsArithVar P n → (∀ j, IsSmoothHerm (L j)) →
    II Unit (dualBlocks T) (P.map (intCoordSubst A)) n (fun j => intCoordLine A ⟨B, hAB⟩ (L j)) =
      II Unit (dualBlocks T₂) P n L

end

end GroundTheory.Heights₂.Heights
end

