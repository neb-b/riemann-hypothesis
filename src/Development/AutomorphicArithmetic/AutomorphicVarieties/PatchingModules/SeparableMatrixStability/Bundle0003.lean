module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoefficientsBoundedOfSelmerBoundary
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ar_family {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ (m : ℕ) (x : M), (∀ s, f s x ∈ I ^ (m + c) • (⊤ : Submodule A M')) →
      ∀ φ : M →ₗ[A] A, (∀ y, (∀ s, f s y = 0) → φ y = 0) → φ x ∈ I ^ m := by
  classical
  have hfg : (Submodule.span A (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let Φ : M →ₗ[A] (Fin n → M') := LinearMap.pi v
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I Φ
  have key : ∀ {ι : Type} (g : ι → M →ₗ[A] M') (N : Submodule A M') (x : M), (∀ i, g i x ∈ N) →
      ∀ u ∈ Submodule.span A (Set.range g), u x ∈ N := by
    intro ι g N x hx u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; exact hx i
    | zero => simp
    | add a b _ _ ha hb => exact N.add_mem ha hb
    | smul r a _ ha => exact N.smul_mem r ha
  refine ⟨c, fun m x hx φ hφ => ?_⟩
  have h0 : x ∈ (I ^ (m + c) • (⊤ : Submodule A (Fin n → M'))).comap Φ := by
    have h1 : ∀ i, v i x ∈ I ^ (m + c) • (⊤ : Submodule A M') := fun i =>
      key f _ x hx _ (hv ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [Submodule.mem_comap, ← Finset.univ_sum_single (Φ x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : LinearMap.single A (fun _ : Fin n => M') i (v i x) ∈
        (I ^ (m + c) • (⊤ : Submodule A M')).map (LinearMap.single A (fun _ : Fin n => M') i) :=
      Submodule.mem_map_of_mem (h1 i)
    rw [Submodule.map_smul''] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  have hle : LinearMap.ker Φ ⊔ I ^ m • (⊤ : Submodule A M) ≤ Submodule.comap φ (I ^ m : Ideal A) := by
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun a ha y _ => ?_)
    · have h1 : ∀ i, v i y ∈ (⊥ : Submodule A M') := fun i => congrFun (LinearMap.mem_ker.mp hy) i
      rw [Submodule.mem_comap, hφ y fun s => key v ⊥ y h1 (f s) (hv ▸ Submodule.subset_span ⟨s, rfl⟩)]
      exact zero_mem _
    · rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ha
  exact hle (hc m h0)

private theorem dd_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) : c • y = DD.C c * y := rfl

private theorem dd_finite (A : Type) [CommRing A] [IsNoetherianRing A] (g : ℕ) : Module.Finite A (DD A g) := by
  let f : DD A g →ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
    { toFun := DD.equiv
      map_add' := fun _ _ => rfl
      map_smul' := fun c y => by
        ext <;> simp [dd_smul, DD.equiv] }
  exact Module.Finite.of_injective f DD.equiv.injective

private theorem dd_ker {A : Type} [CommRing A] {g : ℕ} (s : A) (y : DD A g)
    (hy : DD.map g (Ideal.Quotient.mkₐ A (Ideal.span {s})) y = 0) : ∃ y' : DD A g, y = s • y' := by
  have key : ∀ a : A, Ideal.Quotient.mkₐ A (Ideal.span {s}) a = 0 → ∃ b, a = s * b := fun a ha =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
  obtain ⟨a, ha⟩ := key y.a (congrArg DD.a hy)
  choose b hb using fun j => key (y.ep j) (congrFun (congrArg DD.ep hy) j)
  choose b' hb' using fun j => key (y.ep' j) (congrFun (congrArg DD.ep' hy) j)
  obtain ⟨d, hd⟩ := key y.eta (congrArg DD.eta hy)
  refine ⟨⟨a, b, b', d⟩, ?_⟩
  ext <;> simp [dd_smul, ha, hb, hb', hd]

private theorem exists_antisymmetric_lift_of_section {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ} (f : A →ₐ[A] X)
    (σ : X →+ A) (hσ : ∀ y, f (σ y) = y) (Y : Matrix (Fin n) (Fin n) (DD X g)) (hY : Y ∈ W1 n A X g a)
    (hT : Yᵀ = -Y) : ∃ Y' ∈ W1 n A A g a, Y'ᵀ = -Y' ∧ Y'.map (DD.map g f) = Y := by
  let S : DD X g → DD A g := fun y => ⟨σ y.a, fun j => σ (y.ep j), fun j => σ (y.ep' j), σ y.eta⟩
  have hS : ∀ (b1 b2 b3 b4 : Bool) y, y ∈ ddPart A X g b1 b2 b3 b4 → S y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp [S, h1 e]
    · funext j; simp [S, h2 e]
    · funext j; simp [S, h3 e]
    · simp [S, h4 e]
  refine ⟨Y.map S, fun i j => ⟨fun e => hS _ _ _ _ _ ((hY i j).1 e), fun e => hS _ _ _ _ _ ((hY i j).2 e)⟩, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have e : Y j i = -Y i j := congrFun (congrFun hT i) j
    show S (Y j i) = -S (Y i j)
    rw [e]
    ext <;> simp [S]
  · refine Matrix.ext fun i j => ?_
    show DD.map g f (S (Y i j)) = Y i j
    ext <;> simp [S, hσ]

private theorem map_first_order_lift_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {X : Type} [CommRing X]
    [Algebra x.A X] (f : x.A →ₐ[x.A] X) (g : F.G₀) : (k.ρ1 x.A g).map (DD.map k.g f) = k.ρ1 X g := by
  have e1 : (x.ρX (DD x.A k.g) g).map (DD.map k.g f) = x.ρX (DD X k.g) g :=
    Matrix.ext fun i j => (DD.map k.g f).commutes _
  have e2 : (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (DD.map k.g f) =
      DD.epM fun j => (k.κ j g).map (algebraMap x.A X) := by
    refine Matrix.ext fun i j => ?_
    refine DD.ext (map_zero f) (funext fun r => f.commutes _) (funext fun r => map_zero f) (map_zero f)
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, e1, Matrix.map_add _ (map_add _), e2, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem exists_section (K : Type) [Field K] (I : Ideal (PowerSeries K)) :
    ∃ σ : (PowerSeries K ⧸ I) →+ PowerSeries K, ∀ y, Ideal.Quotient.mkₐ (PowerSeries K) I (σ y) = y := by
  obtain ⟨σ, hσ⟩ := (Ideal.Quotient.mkₐ K I).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective)
  exact ⟨σ.toAddMonoidHom, fun y => LinearMap.congr_fun hσ y⟩

theorem UpperTheory.V.Pa.coefficients_bounded_of_selmer_boundary :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (∀ i, z i ∈ Sel1 h x.A k) → (∀ c : Fin e → x.A, ∑ i, c i • z i ∈ Bd1 h x.A k → c = 0) → ∃ C : ℕ, ∀ (m : ℕ) (c : Fin e → x.A), (fun g => ((∑ i, c i • z i) g).map (x.redD k.g m)) ∈ Bd1 h (x.Am m) k → ∀ i, c i ∈ Ideal.span {x.t ^ (m - C)} := by
  intro l _ L G G0 h n x k e z _ _ hind
  haveI := dd_finite x.A k.g
  let V : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {Y | Y ∈ W1 n x.A x.A k.g x.a ∧ Yᵀ = -Y}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [transpose_add, ha.2, hb.2, neg_add]⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      smul_mem' := fun c Y hY => ⟨Submodule.smul_mem _ c hY.1, by rw [transpose_smul, hY.2, smul_neg]⟩ }
  let f : G.G₀ → ((Fin e → x.A) × V) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g =>
    { toFun := fun p => (∑ i, p.1 i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) p.2 g
      map_add' := fun p q => by
        simp only [dY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add,
          Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [dY, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
          Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    inferInstanceAs (Module.Finite x.A (Fin n → Fin n → DD x.A k.g))
  haveI : Module.Finite x.A V := Module.Finite.of_injective V.subtype V.subtype_injective
  obtain ⟨C, hC⟩ := ar_family (Ideal.span {x.t}) f
  refine ⟨C, fun m c hc i => ?_⟩
  rcases le_total m C with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨m, rfl⟩ : ∃ r, m = r + C := ⟨m - C, by omega⟩
  obtain ⟨Y, hY, hT, hYe⟩ := hc
  obtain ⟨σ, hσ⟩ := exists_section x.K (Ideal.span {x.t ^ (m + C)})
  obtain ⟨Y', hY', hT', rfl⟩ := exists_antisymmetric_lift_of_section _ σ hσ Y hY hT
  rw [Nat.add_sub_cancel, ← Ideal.span_singleton_pow]
  refine hC m (c, ⟨Y', hY', hT'⟩) (fun g => ?_) ((LinearMap.proj i).comp (LinearMap.fst _ _ _)) fun p hp => ?_
  · have h0 : (f g (c, ⟨Y', hY', hT'⟩)).map (x.redD k.g (m + C)) = 0 := by
      show ((∑ i, c i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y' g).map (x.redD k.g (m + C)) = 0
      rw [Matrix.map_sub _ (map_sub _), congrFun hYe g, sub_eq_zero, dY, dY, Matrix.map_sub _ (map_sub _),
        Matrix.map_mul, Matrix.map_mul, map_first_order_lift_eq, map_first_order_lift_eq]
    choose Z hZ using fun a b => dd_ker (x.t ^ (m + C)) _ (congrFun (congrFun h0 a) b)
    have h1 : f g (c, ⟨Y', hY', hT'⟩) = x.t ^ (m + C) • Matrix.of Z := Matrix.ext hZ
    rw [h1, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  · exact congrFun (hind p.1 ⟨p.2, p.2.2.1, p.2.2.2, funext fun g => sub_eq_zero.1 (hp g)⟩) i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_comm {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+ B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.map φ y) =
      MonoidAlgebra.map φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply]
  apply MonoidAlgebra.coeff_injective
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ)

private theorem md_comm' {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+* B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.mapRingHom G φ y) =
      MonoidAlgebra.mapRingHom G' φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  exact md_comm f φ.toAddMonoidHom y

private theorem md_surj (A : Type) {G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : Function.Surjective (MonoidAlgebra.mapDomainRingHom A f) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff, hx]

private theorem comap_chi {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    (y : MonoidAlgebra A G) : (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y) := by
  show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom _ f
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C y)) = _
  rw [map_sub, md_comm', MonoidAlgebra.mapDomainRingHom_apply (Polynomial A) f (MonoidAlgebra.single 1 Polynomial.X),
    MonoidAlgebra.mapDomain_single, map_one]
  rfl

private theorem md_gen {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom _ f (GDet.gen y) = GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j) := by
  unfold GDet.gen
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul,
    ← MonoidAlgebra.mapDomainRingHom_apply, md_comm']

private theorem mem_CH {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (z : MonoidAlgebra A G) :
    z ∈ D.CH ↔ ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ),
      z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) (Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))) := by
  simp only [GDet.CH, Set.mem_setOf_eq]
  refine exists_congr fun m => exists_congr fun y => exists_congr fun β => ?_
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    ext g
    rw [h g, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl
  · intro h g
    rw [h, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl

private theorem md_CH {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    {m : ℕ} (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen y)
        (((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y)))) =
    MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j))
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
          (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)))) := by
  rw [md_comm]
  congr 1
  have hc : ((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y) =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
        (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) := by
    rw [← md_gen]
    exact comap_chi f (D.map MvPolynomial.C) (GDet.gen y)
  rw [hc, ← md_gen]
  exact (Polynomial.aeval_algHom_apply
    (MonoidAlgebra.mapDomainAlgHom (R := MvPolynomial (Fin m) A) (A := MvPolynomial (Fin m) A) f) _ _).symm

theorem UpperTheory.V.Pa.comap_lam :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G'), (∀ y, (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ i y, (D.comap f).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ y, (D.comap f).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ (B : Type) [CommRing B] (φ : A →+* B), (D.comap f).map φ = (D.map φ).comap f) ∧ (∀ ρ : G' →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).comap f = GDet.ofRep (ρ.comp f)) ∧ (Function.Surjective f → (∀ D' : GDet n A G', D'.comap f = D.comap f → D' = D) ∧ MonoidAlgebra.mapDomainRingHom A f '' (D.comap f).CH = D.CH) := by
  intro n A G G' _ _ _ f D
  refine ⟨comap_chi f D, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    simp only [GDet.lam, comap_chi]
  · intro y
    simp only [GDet.tr, GDet.lam, comap_chi]
  · intro B _ φ
    apply GDet.ext
    intro C _ _ x
    rfl
  · intro ρ
    apply GDet.ext
    intro B _ _ x
    have key : ((GDet.repAlg ρ B).comp (MonoidAlgebra.mapDomainAlgHom (R := B) (A := B) f)) =
        GDet.repAlg (ρ.comp f) B := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, MonoidAlgebra.mapDomainAlgHom]
      · exact Subsingleton.elim _ _
    show Matrix.det (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B f x)) =
      Matrix.det (GDet.repAlg (ρ.comp f) B x)
    rw [← key]
    rfl
  · intro hf
    constructor
    · intro D' h
      apply GDet.ext
      intro B _ _ x
      obtain ⟨x', rfl⟩ := md_surj B f hf x
      exact congrArg (fun E : GDet n A G => E.D B x') h
    · ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨m, y, β, rfl⟩ := (mem_CH _ _).1 hw
        exact (mem_CH _ _).2 ⟨m, _, β, md_CH f D y β⟩
      · intro hz
        obtain ⟨m, y', β, rfl⟩ := (mem_CH _ _).1 hz
        choose y hy using fun j => md_surj A f hf (y' j)
        have hy' : (fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) = y' := funext hy
        refine ⟨_, (mem_CH _ _).2 ⟨m, y, β, rfl⟩, ?_⟩
        rw [md_CH, hy']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EventuallyFactorizationCompatibleWithLocalMaps
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_open_normal {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [TotallyDisconnectedSpace P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (c : K → Z) (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup P, ∀ g g' : K, (g : P)⁻¹ * g' ∈ V → c g = c g' := by
  have hKc : IsClosed (K : Set P) := Subgroup.isClosed_of_isOpen K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range c).Finite := hc.range_finite
  have hS : ∀ z, ∃ W ∈ nhds (1 : P), ∀ x ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P), ∀ w ∈ W,
      x * w ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P) := by
    intro z
    have hcpt : IsCompact (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      (hc.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      hK.isOpenMap_subtype_val _ (hc.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨W, hW, hWS⟩ := compact_open_separated_mul_right hcpt ho subset_rfl
    open scoped Pointwise in
    exact ⟨W, hW, fun x hx w hw => hWS (Set.mul_mem_mul hx hw)⟩
  choose W hW hWS using hS
  have hI : (⋂ z ∈ Set.range c, W z) ∈ nhds (1 : P) := (Filter.biInter_mem hfin).2 fun z _ => hW z
  obtain ⟨O, hOI, hOo, h1O⟩ := mem_nhds_iff.1 hI
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine ⟨H, fun g g' hgg => ?_⟩
  have h1 : (g : P)⁻¹ * g' ∈ W (c g) := Set.mem_iInter₂.1 (hOI (hH hgg)) (c g) ⟨g, rfl⟩
  have h2 : (g : P) ∈ Subtype.val '' (c ⁻¹' {c g}) := ⟨g, rfl, rfl⟩
  have h3 := hWS (c g) _ h2 _ h1
  rw [mul_inv_cancel_left] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = g' := Subtype.ext he
  rw [← e]
  exact ha'.symm

theorem UpperTheory.V.Pa.eventually_factorization_compatible_with_local_maps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z), (∀ g, zN (Λ.π0 N g) = c g) → (∀ g, z (Λ.πo0 g) = c g) → (∀ v g, zN ((T.GN N).φ v g) = z (Λ.G.φ v g)) ∧ (∀ w g, zN ((T.GN N).φu w g) = z (Λ.G.φu w g)) ∧ ∀ j, zN (T.ph N j) = z (Λ.ph j) ∧ zN (T.ta N j) = z (Λ.ta j) := by
  intro l _ L G0 T Λ Z c hc
  obtain ⟨V, hV⟩ := exists_open_normal _ Λ.Ph0_open c hc
  filter_upwards [Λ.φ_lim V, Λ.φu_lim V, Λ.ph_lim V, Λ.ta_lim V] with N h1 h2 h3 h4 zN z hN ho
  have key : ∀ (a : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (a : (T.GN N).Γ) (b : Λ.G.Γ) →
      zN a = z b := by
    rintro a b ⟨g, g', ea, eb, hg⟩
    have m : g ∈ (Λ.G.η.comp Λ.πo).ker := (Λ.η_π N g).symm.trans (by rw [ea]; exact a.2)
    have m' : g' ∈ (Λ.G.η.comp Λ.πo).ker := show Λ.G.η (Λ.πo g') = 1 by rw [eb]; exact b.2
    have ea' : a = Λ.π0 N ⟨g, m⟩ := Subtype.ext ea.symm
    have eb' : b = Λ.πo0 ⟨g', m'⟩ := Subtype.ext eb.symm
    rw [ea', eb', hN, ho]
    exact hV _ _ hg
  exact ⟨fun v g => key _ _ (h1 v g), fun w g => key _ _ (h2 w g), fun j => ⟨key _ _ (h3 j), key _ _ (h4 j)⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EventuallyLocallyConstantCompTowerEq
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.eventually_locallyConstant_comp_tower_eq :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (ρ : G0.G₀ → Z), IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g)) := by
  intro l _ L G0 T Λ Z ρ hρ
  have hKo : IsOpen ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := G0.η_open
  have hKc : IsClosed ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range ρ).Finite := hρ.range_finite
  have hS : ∀ z, ∃ V ∈ nhds (1 : G0.Γ), ∀ v ∈ V, ∀ x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ),
      v * x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) := by
    intro z
    have hc : IsCompact (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      (hρ.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
      hKo.isOpenMap_subtype_val _ (hρ.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hc ho subset_rfl
    open scoped Pointwise in
    exact ⟨V, hV, fun v hv x hx => hVS (Set.mul_mem_mul hv hx)⟩
  choose V hV hVS using hS
  have hW : (⋂ z ∈ Set.range ρ, V z) ∈ nhds (1 : G0.Γ) := (Filter.biInter_mem hfin).2 fun z _ => hV z
  obtain ⟨O, hOW, hOo, h1O⟩ := mem_nhds_iff.1 hW
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine (Λ.p_lim H).mono ?_
  intro N hN g
  set a := (T.h N).p₀ (Λ.π0 N g)
  set b := Λ.h.p₀ (Λ.πo0 g)
  have hab : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ (H : Set G0.Γ) := hN g.1
  have h1 : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ V (ρ b) := Set.mem_iInter₂.1 (hOW (hH hab)) (ρ b) ⟨b, rfl⟩
  have h2 : (b : G0.Γ) ∈ Subtype.val '' (ρ ⁻¹' {ρ b}) := ⟨b, rfl, rfl⟩
  have h3 := hVS (ρ b) _ h1 _ h2
  rw [inv_mul_cancel_right] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = a := Subtype.ext he
  rw [← e]
  exact ha'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.GdetDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem gdesc_ker {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (J : TwoSidedIdeal (MonoidAlgebra A G))
    (hJ : ∀ k, f k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J) (x : MonoidAlgebra A G)
    (hx : MonoidAlgebra.mapDomainAlgHom A A f x = 0) : x ∈ J := by
  have key : ∀ y : MonoidAlgebra A G,
      y - MonoidAlgebra.mapDomain (Function.surjInv hf) (MonoidAlgebra.mapDomainAlgHom A A f y) ∈ J := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g a =>
      have h1 := J.mul_mem_left (MonoidAlgebra.single (Function.surjInv hf (f g)) a) _
        (hJ ((Function.surjInv hf (f g))⁻¹ * g) (by simp [Function.surjInv_eq]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_inv_cancel_left, mul_one, mul_one] at h1
      simpa using h1
  simpa [hx] using key x

private theorem gdesc_toT {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G) :
    toT A G' B (MonoidAlgebra.mapDomainRingHom B f x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (MonoidAlgebra.mapDomainAlgHom A A f) (toT A G B x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp [toT_single]

theorem UpperTheory.V.Pa.gdet_desc :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G), Function.Surjective f → (∀ k, f k = 1 → D.Kills (MonoidAlgebra.single k 1 - 1)) → ∃ D' : GDet n A G', D'.comap f = D := by
  intro n A G G' _ _ _ f D hf hk
  have hs : Function.Surjective (MonoidAlgebra.mapDomainAlgHom A A f) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨g, rfl⟩ := hf g
      exact ⟨MonoidAlgebra.single g a, by simp⟩
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D.toDet (MonoidAlgebra.mapDomainAlgHom A A f) hs
    (gdesc_ker f hf _ fun k h => (UpperTheory.V.CA.d_ker _ _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hk k h)))
  refine ⟨GDet.ofDet D', ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  exact GDet.ext fun B _ _ x => congrArg (D'.D B) (gdesc_toT f B x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.hom_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (A A' B B' : Glob l L) (a : A.Hom A') (b : B.Hom B') (h : A.Hom B), a.p.ker ≤ (b.p.comp h.p).ker → ∃ h' : A'.Hom B', ∀ x, h'.p (a.p x) = b.p (h.p x) := by
  intro l _ L A A' B B' a b h hk
  have hT1 : T1Space A'.Γ := by
    refine ⟨fun x => ?_⟩
    have h1 : IsPreconnected (closure ({x} : Set A'.Γ)) := isPreconnected_singleton.closure
    have h2 := h1.subsingleton
    have h3 : closure ({x} : Set A'.Γ) = {x} :=
      h2.eq_singleton_of_mem (subset_closure (Set.mem_singleton x))
    exact closure_eq_iff_isClosed.mp h3
  have hT2 : T2Space A'.Γ := inferInstance
  let q : A'.Γ →* B'.Γ := a.p.liftOfRightInverse (Function.surjInv a.surj)
    (Function.rightInverse_surjInv a.surj) ⟨b.p.comp h.p, hk⟩
  have hq : ∀ x, q (a.p x) = b.p (h.p x) := fun x =>
    a.p.liftOfRightInverse_comp_apply _ _ ⟨b.p.comp h.p, hk⟩ x
  have hquot : Topology.IsQuotientMap a.p :=
    a.cont.isClosedMap.isQuotientMap a.cont a.surj
  refine ⟨⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hq⟩
  · rw [hquot.continuous_iff]
    have : (q : A'.Γ → B'.Γ) ∘ a.p = fun x => b.p (h.p x) := funext hq
    rw [this]
    exact b.cont.comp h.cont
  · intro y
    obtain ⟨z, rfl⟩ := b.surj y
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨a.p x, hq x⟩
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.η, h.η, a.η]
  · rw [← a.c, hq, h.c, b.c]
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.ε, h.ε, a.ε]
  · intro v g
    rw [← a.φ, hq, h.φ, b.φ]
  · intro v g
    rw [← a.φu, hq, h.φu, b.φu]
end

