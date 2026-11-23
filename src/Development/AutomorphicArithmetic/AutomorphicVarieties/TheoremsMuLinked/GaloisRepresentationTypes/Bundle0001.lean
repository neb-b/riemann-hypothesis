module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem avg {Γ k M : Type} [Group Γ] [Field k] [CharZero k] [AddCommGroup M] [Module k M] (R : Representation k Γ M)
    (H : Subgroup Γ) [H.FiniteIndex] (c : Γ → M) (hc : ∀ g h, c (g * h) = c g + R g (c h)) (X : M)
    (hX : ∀ h ∈ H, c h = R h X - X) : ∃ Y, ∀ g, c g = R g Y - Y := by
  classical
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let d : Γ → M := fun g => c g - (R g X - X)
  have hd : ∀ g h, d (g * h) = d g + R g (d h) := fun g h => by
    simp only [d, hc, map_mul, map_sub, Module.End.mul_apply]
    abel
  have hd0 : ∀ g, ∀ h ∈ H, d (g * h) = d g := fun g h hh => by
    have : d h = 0 := by simp only [d, hX h hh, sub_self]
    rw [hd, this, map_zero, add_zero]
  let e : Γ ⧸ H → M := fun q => d q.out
  have he : ∀ g : Γ, e (g : Γ ⧸ H) = d g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    show d _ = d g
    rw [hh, hd0 _ _ h.2]
  have hs : ∀ g : Γ, ∑ q, e q = (Fintype.card (Γ ⧸ H) : k) • d g + R g (∑ q, e q) := fun g => by
    have h1 : ∀ q : Γ ⧸ H, e (g • q) = d g + R g (e q) := fun q => by
      induction q using QuotientGroup.induction_on with
      | H a => rw [MulAction.Quotient.smul_mk, he, he, smul_eq_mul, hd]
    conv_lhs => rw [← Equiv.sum_comp (MulAction.toPerm g) e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MulAction.toPerm_apply, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum,
      Nat.cast_smul_eq_nsmul]
  have hn : (Fintype.card (Γ ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨X - (Fintype.card (Γ ⧸ H) : k)⁻¹ • ∑ q, e q, fun g => ?_⟩
  have h2 : d g = (Fintype.card (Γ ⧸ H) : k)⁻¹ • (∑ q, e q - R g (∑ q, e q)) := by
    rw [sub_eq_of_eq_add (hs g), smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h3 : c g = d g + (R g X - X) := by simp only [d, sub_add_cancel]
  rw [h3, h2, map_sub, map_smul, smul_sub]
  abel

private theorem cc_eq {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] (c : Ω → Ω) (j : Ω →+* ℂ)
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) (x : K) :
    c (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := by
  apply j.injective
  rw [h]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) x).symm

private theorem zero_NS {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] [T2Space V]
    {ρ : Representation C (G F Ω) V} {c : G F Ω → V} (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S)
    (hρ : ∀ s ∈ NS Ω S, ρ s = 1) : ∀ s ∈ NS Ω S, c s = 0 := by
  have c1 : c 1 = 0 := by
    have := hc.2 1 1
    simpa using this
  let N : Subgroup (G F Ω) :=
    { carrier := {s | s ∈ NS Ω S ∧ c s = 0}
      one_mem' := ⟨one_mem _, c1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hc.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => by
        have h1 := hc.2 a a⁻¹
        rw [mul_inv_cancel, c1, hρ a ha.1, ha.2, zero_add] at h1
        exact ⟨inv_mem ha.1, h1.symm⟩ }
  haveI : N.Normal := ⟨fun a ha g => by
    refine ⟨(inferInstance : (NS Ω S).Normal).conj_mem a ha.1 g, ?_⟩
    have h1 := hc.2 g g⁻¹
    rw [mul_inv_cancel, c1] at h1
    rw [hc.2, hc.2, map_mul, hρ a ha.1, ha.2, mul_one, map_zero, add_zero, ← h1]⟩
  have hcl : IsClosed (N : Set (G F Ω)) := (isClosed_NS Ω S).inter (isClosed_eq hc.1 continuous_const)
  have hin : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := F) A, s ∈ NS Ω S := by
    intro w hw A hA s hs
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, A, hA, hs⟩
  have hN : NS Ω S ≤ N := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s hs => ?_) hcl
    simp only [Set.mem_iUnion] at hs
    obtain ⟨w, hw, A, hA, hs⟩ := hs
    obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w fun h => hw (hS w h)
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
    have hs' : s ∈ Ine (F := F) A := hs
    rw [← hg] at hs'
    have ht := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hs'
    have hm := hin w hw A₀ hA₀ _ ht
    have h1 : g⁻¹ * s * g ∈ N := ⟨hm, by rw [hx _ ht, hρ _ hm, Module.End.one_apply, sub_self]⟩
    have h2 := (inferInstance : N.Normal).conj_mem _ h1 g
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rwa [e] at h2
  exact fun s hs => (hN hs).2

theorem UpperTheory.V.Th.adDown :
    AdDown := by
  intro Ω _ _ _ l _ K L _ _ _ _ _ _ _ _ _ _ hLK s V n r μ R _ hR ρ ka h1 h2 hz c hc hb
  obtain ⟨c0, P, ⟨j, hj⟩, hP, hRK, hRc⟩ := hR
  obtain ⟨j', hj'⟩ := s.hc
  obtain ⟨hc', hb'⟩ := X.Kato.bkRes l (W.Lp L) Ω _ _ R c hc hb
  have he : ∀ g, V.frame.eps ℤ_[l] (Qbar l) (V.pr g) = cycBar L Ω l g := by
    intro g
    have : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε _
    ext
    show algebraMap ℤ_[l] (Qbar l) (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]) = _
    rw [this]
    rfl
  have hK : ∀ σ ∈ Base.galOf ℚ K Ω, ∃ t, Base.galEmb ℚ K Ω t = σ := fun σ h => by
    rwa [← Base.range_galEmb] at h
  have hc0 : ∀ x : K, c0⁻¹ (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := fun x => by
    refine c0.symm_apply_eq.2 ?_
    rw [cc_eq c0 j hj, IsCMField.complexConj_apply_apply]
  obtain ⟨w, hw⟩ := hK (Base.galEmb ℚ (W.Lp L) Ω s.c * c0⁻¹) fun x => by
    rw [AlgEquiv.mul_apply, hc0, Base.galEmb_apply, cc_eq s.c j' hj', IsCMField.complexConj_apply_apply]
  have hconj : ∀ t : G K Ω, ∃ t', Base.galEmb ℚ K Ω t' = c0 * Base.galEmb ℚ K Ω t * c0⁻¹ := fun t => hK _ fun x => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc0, Base.galEmb_apply, t.commutes, cc_eq c0 j hj,
      IsCMField.complexConj_apply_apply]
  have hT : ∀ g : G L Ω, ∃ t, Base.galEmb ℚ L Ω g = Base.galEmb ℚ K Ω t := fun g =>
    (hK _ (hLK (Base.galEmb_mem ℚ L Ω g))).imp fun _ h => h.symm
  have hpr : ∀ x : V.frame.G₀, ∃ g, V.pr g = x := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, rfl⟩ := (V.hη y).1 hx
    exact ⟨g, rfl⟩
  have had : ∀ (g : G L Ω) X, R (Base.galEmb ℚ L Ω g) X = Loc.adGL ρ (V.pr g) X := fun g X => by
    obtain ⟨t, ht⟩ := hT g
    have a1 : (ρ (V.pr g)).val = (ka g).val • (r t).val := h1 g t ht
    have a2 : (ρ (V.pr g)⁻¹).val = (ka g⁻¹).val • (r t⁻¹).val :=
      map_inv V.pr g ▸ h1 g⁻¹ t⁻¹ (by rw [map_inv, map_inv, ht])
    rw [map_inv ka, map_inv r, show ρ (V.pr g)⁻¹ = (ρ (V.pr g))⁻¹ from map_inv ρ (V.pr g)] at a2
    rw [ht]
    refine (hRK t X).trans ?_
    show _ = (ρ (V.pr g)).val * X * ((ρ (V.pr g))⁻¹).val
    rw [a1, a2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
  have hN : ∀ x ∈ NS Ω V.S', R (Base.galEmb ℚ (W.Lp L) Ω x) = 1 := fun x hx => by
    have e : toGS Ω V.S' x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    obtain ⟨g, rfl⟩ := (V.hη x).1 (by rw [e, map_one])
    have e' : V.pr g = 1 := Subtype.ext e
    refine LinearMap.ext fun X => (had g X).trans ?_
    rw [e']
    exact LinearMap.congr_fun (map_one (Loc.adGL ρ)) X
  have hN' := zero_NS hc' hb' V.S' (fun v hv => V.sub (Or.inl hv)) hN
  let R' : Representation (Qbar l) V.frame.Γ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    QuotientGroup.lift (NS Ω V.S') (R.comp (Base.galEmb ℚ (W.Lp L) Ω)) hN
  let z : V.frame.Γ → Matrix (Fin n) (Fin n) (Qbar l) := fun q =>
    Quotient.liftOn' q (fun x => c (Base.galEmb ℚ (W.Lp L) Ω x)) fun a b hab => by
      have h := QuotientGroup.leftRel_apply.1 hab
      have h' := hc'.2 a (a⁻¹ * b)
      have h0 := hN' _ h
      beta_reduce at h' h0
      rw [mul_inv_cancel_left, h0, map_zero, add_zero] at h'
      exact h'.symm
  have hz1 : z ∈ Z1 R' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hc'.1.quotient_liftOn' _, fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc'.2 a b
  have hform : V.frame.IsForm ℤ_[l] n ρ (P * (r w)⁻¹) := by
    intro x
    obtain ⟨g, rfl⟩ := hpr x
    obtain ⟨g', hg'⟩ := (V.hη (s.c * W.resP L Ω g * s.c⁻¹)).1 (V.frame.conj (V.pr g)).2
    have e : V.frame.conj (V.pr g) = V.pr g' := Subtype.ext (by
      show _ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
      rfl)
    obtain ⟨t, ht⟩ := hT g
    obtain ⟨t', ht'⟩ := hconj t
    have e2 : Base.galEmb ℚ L Ω g' = Base.galEmb ℚ K Ω (w * t' * w⁻¹) := by
      show Base.galEmb ℚ (W.Lp L) Ω (W.resP L Ω g') = _
      rw [hg', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hw, ht', ← ht]
      show _ * Base.galEmb ℚ L Ω g * _ = _
      group
    have e3 : (P * (r w)⁻¹).val * W.mat r (w * t' * w⁻¹) = P.val * (r t').val * ((r w)⁻¹).val := by
      show _ * (r (w * t' * w⁻¹)).val = _
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, map_mul, map_mul, map_inv]
      congr 1
      group
    have e4 : (W.mat r t).transpose * P.val * (r t').val = (μ t).val • P.val := hP t t' ht'
    rw [e, h1 g t ht, h1 g' _ e2, he, ← h2 g g' t hg' ht, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e4, Matrix.smul_mul,
      smul_smul, smul_smul, Units.val_mul, Units.val_mul, Units.val_mul]
  have hext : Ws.Eb.IsAdExt V.frame ρ (P * (r w)⁻¹) R' := by
    refine ⟨fun x X => ?_, fun X => ?_⟩
    · obtain ⟨g, rfl⟩ := hpr x
      exact had g X
    · show R (Base.galEmb ℚ (W.Lp L) Ω s.c) X = _
      rw [mul_inv_eq_iff_eq_mul.1 hw.symm, map_mul, Module.End.mul_apply, hRc]
      refine (hRK w _).trans ?_
      simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  obtain ⟨X, hX⟩ := hz _ R' hform hext z hz1 hb'
  haveI : (Base.galOf ℚ (W.Lp L) Ω).FiniteIndex :=
    ⟨by rw [(Base.galEmbTop ℚ (W.Lp L) Ω).2.2]; exact Module.finrank_pos.ne'⟩
  refine (mem_coboundaries1 _ _).2 (avg R (Base.galOf ℚ (W.Lp L) Ω) c hc.2 X fun h hh => ?_)
  rw [← Base.range_galEmb] at hh
  obtain ⟨x, rfl⟩ := hh
  exact hX (toGS Ω V.S' x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LiftSmul
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_smul {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ}
    {E : Type} [Ring E] [Algebra R E] {x : R →ₐ[O] O} {δ : R →ₗ[O] X} {ρ : E →+* Matrix (Fin n) (Fin n) O}
    {τ : E → R} {c : O} {d : E →+ Matrix (Fin n) (Fin n) X} (h : IsLift x δ ρ τ c d) (a : O) :
    IsLift x δ ρ τ (a * c) (a • d) := by
  constructor
  · intro u v
    simp only [AddMonoidHom.smul_apply, h.mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]
  · intro r u
    simp only [AddMonoidHom.smul_apply, h.smul, smul_add]
    rw [smul_comm a (x r), mul_smul, smul_assoc a]
  · intro u
    simp only [AddMonoidHom.smul_apply, Matrix.trace_smul, h.tr, mul_smul]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : ∀ᶠ g' in nhds g, ∀ i j, f g' i j = f g i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g
  exact this.mono fun g' e => Matrix.ext e

private theorem der_const {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}
    {δ : R →ₗ[O] X} (h : IsDer x δ) (a : O) : δ (algebraMap O R a) = 0 := by
  have h1 := h 1 1
  rw [mul_one, map_one x, one_smul] at h1
  have h2 : δ 1 = 0 := by simpa using h1
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h2, smul_zero]

theorem UpperTheory.V.Th.coc :
    Coc := by
  intro l hl L G0 n O _ _ _ hO _ y h2 hn
  classical
  obtain ⟨c₀, hc₀, hsp⟩ := y.span
  choose c₁ hc₁ hloc using fun v => locAt y v
  have h2O : (2 : O) ≠ 0 := by
    intro e
    haveI := hO.char
    have h3 : ((2 : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), Nat.cast_ofNat, e, map_zero]
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h3))
  refine ⟨(∏ v, c₁ v) * (c₀ * (2 * (c₀ ^ (2 * n) * c₀ ^ (2 * n)))),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => hc₁ v) (mul_ne_zero hc₀ (mul_ne_zero h2O
      (mul_ne_zero (pow_ne_zero _ hc₀) (pow_ne_zero _ hc₀)))), ?_⟩
  intro G h rN R _ _ _ p x hI hp m δ hδ
  have hsurj : Function.Surjective h.p₀ := fun g => by
    obtain ⟨g', e⟩ := h.surj g
    exact ⟨⟨g', by rw [MonoidHom.mem_ker, ← h.η, e]; exact g.2⟩, Subtype.ext e⟩
  have hcont : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have hsp' : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range (mat (y.ρ.comp h.p₀))) := fun Z => by
    have e : Set.range (mat (y.ρ.comp h.p₀)) = Set.range (mat y.ρ) := hsurj.range_comp (mat y.ρ)
    rw [e]
    exact hsp Z
  have hform : G.frame.IsForm O n (y.ρ.comp h.p₀) y.P := fun g => by
    have e1 : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := Subtype.ext (by
      change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
      rw [map_mul, map_mul, map_inv, h.c])
    have e2 : G.frame.eps O O g = G0.frame.eps O O (h.p₀ g) := by
      change Units.map _ (G.ε g) = Units.map _ (G0.ε (h.p g))
      rw [h.ε]
    have := y.form (h.p₀ g)
    rw [← e1, ← e2] at this
    exact this
  obtain ⟨htr, -, t, ht⟩ := trRep p.D x _ hn hp.1
  have ht' : (t : _ → R) = p.D.tr := funext ht
  obtain ⟨d1, hd1⟩ := liftG p.D rN.chib x δ _ c₀ hn rN.chib_inj p.red hp.1 hc₀ hsp' hδ
  obtain ⟨d2, hd2, hpol⟩ := polar G.frame x δ _ y.P t _ d1 y.sgn hform (fun g => by rw [ht, ht]; exact p.P 1 g) (ht' ▸ hd1)
  rw [ht'] at hd2
  have hk := kill x δ _ _ _ c₀ d2 hc₀ hsp' htr hd2
  have hd3 := lift_smul hd2 c₀
  have hd4 := lift_smul hd3 (∏ v, c₁ v)
  obtain ⟨h1, hcoc, hP, hT⟩ := zOf G.frame x δ _ y.P _ _ _
    (fun g => ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single g 1) * bar (Om O m) (mat (y.ρ.comp h.p₀) g⁻¹)) hδ hform hd4
    (fun a => by simp only [AddMonoidHom.smul_apply, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, hpol]) fun _ => rfl
  have hρlc : IsLocallyConstant fun g => bar (Om O m) (mat (y.ρ.comp h.p₀) g) :=
    (lc_mat _ fun i j => (lcDer (R := R) m).1 _ (y.cont i j)).comp_continuous hcont
  refine ⟨_, ⟨?_, hcoc, hP, fun u g hg => ?_, fun v => ?_⟩, hT⟩
  · have hl2 := lc x δ _ _ _ c₀ d2 hsp' hd2 hρlc ((lcDer m).2 x δ hδ _ (p.cont 1))
    exact (hl2.comp fun Z => (∏ v, c₁ v) • Z).mul (hρlc.comp_continuous continuous_inv)
  · have h4 := (hk _ (p.I u g (hI u ▸ hg))).2
    have h5 : d2 1 = 0 := by
      have := hd2.mul 1 1
      simpa using this
    rw [map_sub, h5, sub_zero] at h4
    simp only [AddMonoidHom.smul_apply, h4, smul_zero, Matrix.zero_mul]
  · obtain ⟨Y, hY⟩ := hloc v G h R x m δ _ _ _ (p.ψ v) hd3
      (fun i g => congrArg Units.val (DFunLike.congr_fun (hp.2 v i) g))
      (fun g => hk _ (p.Ord v g)) fun i g hg => by
        rw [(p.psi v i).mu ⟨g, hg⟩]
        exact der_const hδ _
    refine ⟨(∏ v' ∈ Finset.univ.erase v, c₁ v') • Y, fun g => ?_⟩
    have e : ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          bar (Om O m) (mat (y.ρ.comp h.p₀) (G.frame.φ v g)⁻¹) -
        dY G.frame (y.ρm h m) ((∏ v' ∈ Finset.univ.erase v, c₁ v') • Y) (G.frame.φ v g) =
        (∏ v' ∈ Finset.univ.erase v, c₁ v') • (c₁ v • ((c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          y.ρm h m (G.frame.φ v g)⁻¹) - dY G.frame (y.ρm h m) Y (G.frame.φ v g)) := by
      rw [smul_sub, smul_smul (∏ v' ∈ Finset.univ.erase v, c₁ v'), Finset.prod_erase_mul _ _ (Finset.mem_univ v),
        AddMonoidHom.smul_apply, Matrix.smul_mul]
      simp only [dY, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [e]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · have := (hY g).1 i j hij
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
    · have := (hY g).2 hg i
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceFour
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem exists_place_above_prime_alt (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)

private theorem charpoly_eq_prod_flag_characters {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem continuous_linear_closed {G κ : Type} [TopologicalSpace G] [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ] {n : ℕ}
    (a : G → Matrix (Fin n) (Fin n) κ) (ha : Continuous a) : Pr.LinClosed a := by
  intro f
  have h : (fun g => f (a g)) = fun g => ∑ i, ∑ j, a g i j * f (Matrix.single i j 1) := by
    funext g
    conv_lhs => rw [Matrix.matrix_eq_sum_single (a g)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    simp
  have hc : Continuous fun g => f (a g) := by
    rw [h]
    fun_prop
  exact isClosed_singleton.preimage hc

private theorem absolute_irreducible_rank_four (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (two : (2 : ResidueField O) ≠ 0) (χ : Fin 4 → F.G₀ →* (ResidueField O)ˣ)
    (K : Type) [Field K] [IsAlgClosed K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] (twoK : (2 : K) ≠ 0)
    (ρ : F.G₀ →* GL (Fin 4) K) (hρ : Continuous ρ) (hb : U3.MatIrr ⊤ (W.mat ρ))
    (A : Type) [CommRing A] (j : A →+* K) (φ : A →+* ResidueField O) (hj : Function.Injective j) (hred : Pr.RedTo ρ j φ χ)
    (u : F.G₀) (hg : u ∈ F.G') (a : Fin 4 → Kˣ) (hu : (W.mat ρ u).charpoly = ∏ i, (X - C (a i : K))) (hfr : Pr.FreeRatios a)
    (hc : ∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * χ i = χ j) → η = 1)
    (hd : ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ i / χ j) ^ n ≠ 1) : Th.TypeI F ρ ∧ Th.N3 F ρ := by
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  have hm : Continuous (W.mat ρ) := Units.continuous_val.comp hρ
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => by
    obtain ⟨m, hm0, hm1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    rw [div_pow, div_eq_one] at hm1
    exact hfr s t hst m hm0 hm1
  have hsep := Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _
  have hI : Th.TypeI F ρ := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction K F.G₀ 4 (W.mat ρ) hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction K F.G₀ twoK (W.mat ρ) hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := Ws.isClosed_setOf_matrix_stabilizes_submodule F.G₀ K 4 _ (continuous_linear_closed _ hm) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (Th.Det.perm4 K (ResidueField O) A F.G₀ 4 ρ j φ χ η hj hred hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) two
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨hI, ?_⟩
  have hsp : Submodule.span K (Set.range ((W.mat ρ).comp F.G'.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
  have hsp' : Submodule.span K (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
  have hnc := Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup K (ResidueField O) A F.G₀ (W.mat ρ) j φ χ hj hred hsp' hd F.G' _ hg hsep
  refine Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat ρ s).charpoly.Separable) fun V hV σ => ?_
  exact AlgebraTools.regCosetFour K F.G' twoK ((W.mat ρ).comp F.G'.subtype)
    (fun f => isClosed_singleton.preimage (f.continuous_eval.comp
      (continuous_pi fun p => (hm.comp continuous_subtype_val).matrix_elem p.1 p.2)))
    hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceSmall
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

theorem UpperTheory.V.Th.nice0small :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), (n = 2 ∨ n = 3) → Th.APt ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∃ v a b g, r.psib v a g ≠ r.psib v b g) → Th.NiceAPt ι x ρ := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι x ρ hn hA hirr hfree ⟨v, hne⟩
  have hp : n.Prime := by
    rcases hn with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have h3 : n ≤ 3 := by omega
  obtain ⟨-, A, _, j, φ, hj, hred, hlift⟩ := Th.Det.redB x ρ hA.rep
  haveI : V.frame.G'.Normal := MonoidHom.normal_ker _
  haveI : CompactSpace V.frame.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ V.frame.η_open).isCompact
  have key := Th.Det.irrSmall hp V.frame.G' ρ j φ r.chib (V.frame.φ v) (x.psi v) (r.psib v) hirr hj hred
    (hA.flag v) (hlift v) (hfree v) hne
  refine ⟨hA, hfree, ?_, ?_⟩
  · have h := key ⊤ (by simp)
    rwa [top_inf_eq] at h
  · obtain ⟨g, hg, hfr⟩ := hfree v
    exact Th.Det.n3small h3 V.frame.G' ρ hA.cont key
      ⟨V.frame.φ v g, hg, fun i => x.psi v i g, hfr, charpoly_flag' _ _ (hA.flag v) g⟩
end

