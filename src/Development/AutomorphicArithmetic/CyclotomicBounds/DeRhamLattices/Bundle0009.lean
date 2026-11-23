module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ContinuousLocalCoefficientRepTwist
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

theorem _root_.UpperTheory.KN.continuous_localCoefficientRep_twist :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → ∀ x, Continuous fun g => (locOC C (rTwO D.nd i r x) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
  intro D i r w hw C hr x
  have h1 := GlobalTheory.PotDual.continuous_loc D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr x).1
  have h2 : Continuous (fun y => C.inc y) :=
    continuous_induced_rng.2 continuous_subtype_val
  refine (h1.matrix_map h2).congr fun g => ?_
  ext a b
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCyclicGeneratorLamPowerQuotient
section
open GlobalTheory.UseLoc.Cases

theorem _root_.UpperTheory.KN.exists_cyclic_generator_lam_power_quotient :
    ∀ {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL], Function.Injective (algebraMap O LL) →
      ∀ (lam : O) (a : ℕ), algebraMap O LL lam ≠ 0 → ∃ x₀ : ↥(Xq LL lam a), ∀ x : ↥(Xq LL lam a), ∃ c : O, x = c • x₀ := by
  intro O LL _ _ _ _ lam a hlam
  have hK : algebraMap O LL (lam ^ a) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hlam
  have hmem : ∀ s : LL, Submodule.Quotient.mk (p := intO (O := O) LL) s ∈ Xq LL lam a ↔
      ∃ c : O, algebraMap O LL c = lam ^ a • s := by
    intro s
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  refine ⟨⟨Submodule.Quotient.mk (algebraMap O LL (lam ^ a))⁻¹, (hmem _).2 ⟨1, ?_⟩⟩, ?_⟩
  · rw [Algebra.smul_def, mul_inv_cancel₀ hK, map_one]
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc⟩ := (hmem s).1 hx
    refine ⟨c, Subtype.ext ?_⟩
    have hs : s = c • (algebraMap O LL (lam ^ a))⁻¹ := by
      rw [Algebra.smul_def, hc, Algebra.smul_def, mul_comm (algebraMap O LL (lam ^ a)) s, mul_assoc,
        mul_inv_cancel₀ hK, mul_one]
    change Submodule.Quotient.mk s = c • Submodule.Quotient.mk (p := intO (O := O) LL) (algebraMap O LL (lam ^ a))⁻¹
    rw [← Submodule.Quotient.mk_smul, ← hs]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsEmbeddingAndEigenvectorsOfAdmissibleDecomp
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

private theorem emb_gen {O K L Γ : Type} [CommRing O] [Field K] [Field L] (φ : O →+* K) (f : K →+* L)
    {n r t : ℕ} (R : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (χ : ℕ → Γ → O) (s : Γ → O)
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (he : ∀ g u, e (((R g).map φ).mulVec u) =
      (((P g).map φ).mulVec (e u).1, fun c : Fin t => φ (χ ((c : ℕ) + 1) g) * (e u).2 c)) :
    (∃ iW : (Fin r → L) →ₗ[L] (Fin n → L), Function.Injective iW ∧
      ∀ g v, iW (((s g • P g).map (f.comp φ)).mulVec v) = ((s g • R g).map (f.comp φ)).mulVec (iW v)) ∧
    ∀ c ∈ Finset.Icc 1 t, ∃ u : Fin n → L, u ≠ 0 ∧
      ∀ g, ((s g • R g).map (f.comp φ)).mulVec u = f (φ (χ c g * s g)) • u := by
  have hs : ∀ {k : ℕ} (a : O) (M : Matrix (Fin k) (Fin k) O),
      (a • M).map (f.comp φ) = f (φ a) • (M.map φ).map f := by
    intro k a M
    ext x y
    simp
  constructor
  · set A : Matrix (Fin n) (Fin r) K := LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _) with hA
    set Bm : Matrix (Fin r) (Fin n) K := LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap) with hB
    have hAv : ∀ v, A.mulVec v = e.symm (v, 0) := by
      intro v
      rw [hA, LinearMap.toMatrix'_mulVec]
      rfl
    have hBv : ∀ v, Bm.mulVec v = (e v).1 := by
      intro v
      rw [hB, LinearMap.toMatrix'_mulVec]
      rfl
    have h1 : Bm * A = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hAv, hBv]
      simp
    have h2 : ∀ g, A * (P g).map φ = (R g).map φ * A := by
      intro g
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, hAv,
        LinearEquiv.symm_apply_eq, he]
      simp only [LinearEquiv.apply_symm_apply, Pi.zero_apply, mul_zero]
      rfl
    refine ⟨Matrix.toLin' (A.map f), ?_, ?_⟩
    · intro x y hxy
      have h3 := congrArg (fun z => (Bm.map f).mulVec z) hxy
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, h1] at h3
      simpa [Matrix.map_one] using h3
    · intro g v
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hs, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.map_mul, h2]
  · intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let j : Fin t := ⟨c - 1, by omega⟩
    have hj : (j : ℕ) + 1 = c := by simp only [j]; omega
    let u : Fin n → K := e.symm (0, Pi.single j 1)
    have hu : ∀ g, ((R g).map φ).mulVec u = φ (χ c g) • u := by
      intro g
      apply e.injective
      rw [he, map_smul]
      simp only [u, LinearEquiv.apply_symm_apply, Matrix.mulVec_zero, Prod.smul_mk, smul_zero]
      congr 1
      funext d
      by_cases hd : d = j
      · subst hd
        simp [hj]
      · simp [Pi.single_eq_of_ne hd]
    refine ⟨f ∘ u, ?_, ?_⟩
    · intro h0
      have hu0 : u = 0 := by
        funext x
        exact f.injective (by simpa using congrFun h0 x)
      have h4 := congrArg (fun z => (e z).2 j) hu0
      simp [u] at h4
    · intro g
      rw [hs, Matrix.smul_mulVec]
      funext x
      rw [Pi.smul_apply, ← RingHom.map_mulVec, hu]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_apply]
      ring

private theorem emb_alg {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (o : D.nd.O i) :
    (C.inc.comp (Br.toLLK (D.nbr i w hw))) (toK D.nd i o) =
      algebraMap ↥(OL C.LL) ↥C.LL.1 (incO C.le ((D.nbr i w hw).eO o)) := by
  rw [RingHom.comp_apply, Br.toLLK_alg]
  rfl

private theorem emb_loc {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    (locOC C M g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) =
      (M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map
        ((C.inc.comp (Br.toLLK (D.nbr i w hw))).comp (toK D.nd i)) := by
  ext a b : 1
  exact (emb_alg C _).symm

theorem _root_.UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
      (∃ iW : (Fin D.R.r → ↥C.LL.1) →ₗ[↥C.LL.1] (Fin D.R.nV → ↥C.LL.1), Function.Injective iW ∧
        ∀ g v, iW (((locOC C (WpO D.nd i ρ π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec v) =
          ((locOC C (rTwO D.nd i r π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec (iW v)) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, ∃ e : Fin D.R.nV → ↥C.LL.1, e ≠ 0 ∧
        ∀ g, ((locOC C (rTwO D.nd i r π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec e =
          ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • e := by
  intro D i r ρ π w hw C hd
  obtain ⟨e, he⟩ := hd
  obtain ⟨⟨iW, h1, h2⟩, h3⟩ := emb_gen (toK D.nd i) (C.inc.comp (Br.toLLK (D.nbr i w hw)))
    (fun g => rO D.nd i r π g) (fun g => rhoO D.nd i ρ π g)
    (fun c g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
    (fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) e he
  refine ⟨⟨iW, h1, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [emb_loc, emb_loc]
    exact h2 _ v
  · obtain ⟨u, hu, hg⟩ := h3 c hc
    refine ⟨u, hu, fun g => ?_⟩
    rw [emb_loc]
    refine (hg _).trans ?_
    rw [emb_alg, algebraMap_smul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

private theorem cutPres_gen {G O O' LL Q X : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [CommRing O'] [Field LL] [Algebra O' LL] [AddCommGroup Q] [Module O' Q] (f : O →+* O')
    (fK : FractionRing O →+* LL) {a n : ℕ} (N : X → (G →* Matrix (Fin n) (Fin n) O'))
    (actQ : G → Q →ₗ[O'] Q) (x : Fin a → X) (A : G → Fin a → Matrix (Fin n) (Fin n) (FractionRing O))
    (hA : ∀ g j v, ((N (x j) g).map (algebraMap O' LL)).mulVec (fun m => fK (v m)) = fun m => fK ((A g j).mulVec v m))
    (E : Fin a → Fin n → FractionRing O) (Y : Submodule O (Fin a → Fin n → FractionRing O)) (hY : Y.FG)
    (hst : ∀ g, ∀ y ∈ Y, (fun j => (A g j).mulVec (y j)) ∈ Y)
    (hE : ∀ g, (fun j => (A g j).mulVec (E j) - E j) ∈ Y) {Q0 : Type} [AddCommGroup Q0] [Module O Q0] (φ0 : ↥Y →ₗ[O] Q0)
    (θ : Q0 → Q) (act0 : G → Q0 → Q0)
    (hinj : Function.Injective (algebraMap O' LL))
    (hf : ∀ c, fK (algebraMap O (FractionRing O) c) = algebraMap O' LL (f c))
    (hθa : ∀ p q, θ (p + q) = θ p + θ q) (hθs : ∀ (c : O) q, θ (c • q) = f c • θ q)
    (hθe : ∀ g q, θ (act0 g q) = actQ g (θ q))
    (hφ0 : ∀ g (y : ↥Y), φ0 ⟨_, hst g y.1 y.2⟩ = act0 g (φ0 y)) :
    HasPres LL N (Q := Q) (fun g => actQ g) (fun g => θ (φ0 ⟨_, hE g⟩)) := by
  let ψ : ↥Y →+ Q := AddMonoidHom.mk' (fun y => θ (φ0 y)) (fun u v => by rw [map_add (f := _), hθa])
  have hψ : ∀ (c : O) (y : ↥Y), ψ (c • y) = f c • ψ y := fun c y => by
    change θ (φ0 (c • y)) = f c • θ (φ0 y)
    rw [map_smul, hθs]
  have heq : ∀ g (y : ↥Y), ψ ⟨_, hst g y.1 y.2⟩ = actQ g (ψ y) := fun g y => by
    change θ (φ0 ⟨_, hst g y.1 y.2⟩) = actQ g (θ (φ0 y))
    rw [hφ0, hθe]
  let ι : (Fin a → Fin n → FractionRing O) → (Fin a → Fin n → LL) := fun y j m => fK (y j m)
  have hι : ι = fun y j m => fK (y j m) := rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(Submodule.span O' (ι '' (Y : Set _))) →ₗ[O'] Q,
      ∀ y : ↥Y, φ ⟨ι y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ = ψ y := by
    have H := UpperTheory.KN.exists_linearMap_span_baseChange_of_semilinear f fK Y ψ hinj hf hY hψ
    exact H
  have hact : ∀ g y, actN LL (fun j => N (x j)) g (ι y) = ι (fun j => (A g j).mulVec (y j)) := by
    intro g y
    funext j
    exact hA g j (y j)
  have hadd : ∀ g u v, actN LL (fun j => N (x j)) g (u + v) =
      actN LL (fun j => N (x j)) g u + actN LL (fun j => N (x j)) g v := by
    intro g u v
    funext j
    simp [actN, Matrix.mulVec_add]
  have hsmul : ∀ g (c : O') u, actN LL (fun j => N (x j)) g (c • u) = c • actN LL (fun j => N (x j)) g u := by
    intro g c u
    funext j
    simp [actN, Matrix.mulVec_smul]
  have hzero : ∀ g, actN LL (fun j => N (x j)) g 0 = 0 := by
    intro g
    funext j
    simp [actN]
  have hst' : ∀ g, ∀ y ∈ Submodule.span O' (ι '' (Y : Set _)),
      actN LL (fun j => N (x j)) g y ∈ Submodule.span O' (ι '' (Y : Set _)) := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      rw [hact]
      exact Submodule.subset_span ⟨_, hst g y hy, rfl⟩
    | zero => rw [hzero]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [hadd]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu => rw [hsmul]; exact Submodule.smul_mem _ c hu
  have hEE : ∀ g, actN LL (fun j => N (x j)) g (ι E) - ι E = ι (fun j => (A g j).mulVec (E j) - E j) := by
    intro g
    rw [hact]
    funext j m
    simp [hι]
  have hE' : ∀ g, actN LL (fun j => N (x j)) g (ι E) - ι E ∈ Submodule.span O' (ι '' (Y : Set _)) := by
    intro g
    rw [hEE]
    exact Submodule.subset_span ⟨_, hE g, rfl⟩
  have hfg : (Submodule.span O' (ι '' (Y : Set _))).FG := by
    obtain ⟨S, hS, hSY⟩ := Submodule.fg_def.1 hY
    refine Submodule.fg_def.2 ⟨ι '' S, hS.image _, le_antisymm (Submodule.span_mono (Set.image_mono ?_)) ?_⟩
    · rw [← hSY]; exact Submodule.subset_span
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [← hSY] at hy
      change ι y ∈ Submodule.span O' (ι '' S)
      induction hy using Submodule.span_induction with
      | mem u hu => exact Submodule.subset_span ⟨u, hu, rfl⟩
      | zero =>
        have : ι 0 = 0 := by funext j m; simp [hι]
        rw [this]; exact Submodule.zero_mem _
      | add u v _ _ hu hv =>
        have : ι (u + v) = ι u + ι v := by funext j m; simp [hι]
        rw [this]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        have : ι (c • u) = f c • ι u := by
          funext j m
          change fK (c • u j m) = f c • fK (u j m)
          simp only [Algebra.smul_def, map_mul, hf]
        rw [this]; exact Submodule.smul_mem _ _ hu
  refine ⟨a, x, ι E, _, hfg, hst', hE', φ, ?_, ?_⟩
  · intro g
    let L : (Fin a → Fin n → LL) →ₗ[O'] (Fin a → Fin n → LL) :=
      { toFun := actN LL (fun j => N (x j)) g, map_add' := hadd g, map_smul' := hsmul g }
    have key : φ ∘ₗ L.restrict (hst' g) = actQ g ∘ₗ φ := by
      rw [Submodule.linearMap_eq_iff_of_eq_span _ _ rfl]
      rintro ⟨_, y, hy, rfl⟩
      have h1 := hφ ⟨y, hy⟩
      have h2 := hφ ⟨_, hst g y hy⟩
      have h3 := heq g ⟨y, hy⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, ← h3, ← h2]
      congr 1
      exact Subtype.ext (hact g y)
    intro y
    exact LinearMap.congr_fun key y
  · intro g
    have h2 := hφ ⟨_, hE g⟩
    change ψ ⟨_, hE g⟩ = _
    rw [← h2]
    congr 1
    exact Subtype.ext (hEE g).symm

private theorem cutPres_mulVec {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (v : Fin k → KK D.nd i) :
    ((locOC C M g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec
        (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (v m)) =
      fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw)))
        ((mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).mulVec v m) := by
  have h := GlobalTheory.Pass.LocDirect.loc_mulVec i w hw M g v
  funext m
  rw [RingHom.comp_apply, ← congrFun h m, RingHom.map_mulVec]
  rfl

private theorem cutPres_alg {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : D.nd.O i) :
    ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (algebraMap (D.nd.O i) (KK D.nd i) c) =
      algebraMap ↥(OL C.LL) ↥C.LL.1 (((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c) := by
  rw [RingHom.comp_apply, Br.toLLK_alg]
  rfl

private theorem cutPres_smul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (c : D.nd.O i)
    (q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (c • q)) =
      ((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c • liftQ C.le k (Br.phi (D.nbr i w hw) k q) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have h : (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (c • u m)) =
      ((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c •
        (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (u m)) := by
    funext m
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, cutPres_alg]
  exact congrArg (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k)) h

private theorem cutPres_act {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (WKG M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) q)) =
      actD (latC C (locOC C M)) g (liftQ C.le k (Br.phi (D.nbr i w hw) k q)) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact congrArg (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k)) (cutPres_mulVec C M g u).symm

private theorem cutPres_add {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (p q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (p + q)) =
      liftQ C.le k (Br.phi (D.nbr i w hw) k p) + liftQ C.le k (Br.phi (D.nbr i w hw) k q) :=
  (congrArg (liftQ C.le k) ((Br.phi (D.nbr i w hw) k).map_add p q)).trans ((liftQ C.le k).map_add _ _)

theorem _root_.UpperTheory.KN.hasPres_cutCocycle_localCoefficient :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
      HasPres ↥C.LL.1 (fun x => locOC C (rTwO D.nd i r x)) (Q := (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k)
        (fun g => actD (latC C (locOC C M)) g) (fun g => liftQ C.le k (z g)) := by
  intro D i r w hw C k M z hz
  obtain ⟨a, x, -, E, Y, hY, hst, hE, φ, hφ, rfl⟩ := hz
  have H := cutPres_gen (Q := (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k)
    ((incO C.le).comp (D.nbr i w hw).eO.toRingHom)
    ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw)))
    (fun x => locOC C (rTwO D.nd i r x)) (fun g => actD (latC C (locOC C M)) g) x
    (fun g j => mapM (toK D.nd i) (rTwO D.nd i r (x j)) ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))
    (fun g j v => cutPres_mulVec C _ g v) E Y hY (fun g => hst _) (fun g => hE _)
    φ (fun q => liftQ C.le k (Br.phi (D.nbr i w hw) k q))
    (fun g => WKG M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))
    Subtype.val_injective (cutPres_alg C) (cutPres_add C)
    (cutPres_smul C) (cutPres_act C M) (fun g => hφ _)
  exact H
end

