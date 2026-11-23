module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.InjOfProd
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem inj_of_prod {n : ℕ} {A : Type} [CommRing A] [IsDomain A] {a b : Fin n → A}
    (h : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i)))
    (hb : Function.Injective b) : Function.Injective a := by
  have e : ∀ c : Fin n → A, (∏ i, (Polynomial.X - Polynomial.C (c i))).roots = Finset.univ.val.map c := fun c => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  have h1 : Finset.univ.val.map a = Finset.univ.val.map b := by rw [← e, ← e, h]
  have h2 : (Finset.univ.val.map a).Nodup := h1 ▸ Finset.univ.nodup.map hb
  exact fun i j hij => Multiset.inj_on_of_nodup_map h2 i (Finset.mem_univ_val i) j (Finset.mem_univ_val j) hij

private theorem lam_lift {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : D.comap φ = E.map f) (i : ℕ) (y : MonoidAlgebra R H) :
    D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) = f (E.lam i y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, ← h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  apply congrArg (fun p : Polynomial S => (-1) ^ i * p.coeff (n - i))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun S _ _ z => ?_
  change (GDet.repAlg ρ S (MonoidAlgebra.mapDomainRingHom S φ z)).det = (GDet.repAlg (ρ.comp φ) S z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem genBy_img {O R S : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [CommRing S]
    [Algebra O S] [IsLocalRing S] (f : R →ₐ[O] S) (hf : Function.Surjective f) {s : Set R} {t : Set S}
    (h : GenBy O s) (hst : ∀ a ∈ s, f a ∈ t) : GenBy O t := by
  intro N b
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨a, ha, hb⟩ := h N b
  haveI : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective _ hf
  refine ⟨f a, ?_, ?_⟩
  · have : Algebra.adjoin O s ≤ (Algebra.adjoin O t).comap f :=
      Algebra.adjoin_le fun c hc => Algebra.subset_adjoin (hst c hc)
    exact this ha
  · rw [← map_sub]
    have h1 : (maximalIdeal R).map (f : R →+* S) ≤ maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun c hc => map_nonunit (f : R →+* S) c hc
    have h2 := Ideal.mem_map_of_mem (f : R →+* S) hb
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 N h2

theorem UpperTheory.V.Pa.Core.ooPt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → Adapted T (r := r) → ∀ (D0 : ℕ) (x : Pt T u D0) (x' : Spo A →ₐ[O] x.x.A), (∀ b, x' (algebraMap B (Spo A) b) = x.f b) → Function.Surjective (algebraMap O x.x.K) → x.f (A.b.lam (MvPowerSeries.X (.inl ()))) = x.x.t → x' (m.π (fo W)) ≠ 0 ∧ ∃ P : OoPt Λ.h x.x o.p, P.f = x'.comp πb ∧ P.ker = ooKer o := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπ had D0 x x' hx' hsurj ht
  obtain ⟨-, -, hs, hU, hy⟩ := m.π_maps
  obtain ⟨hD, hψ⟩ := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπ
  have hc : x'.toRingHom.comp (algebraMap B (Spo A)) = x.f.toRingHom := RingHom.ext hx'
  have heig : ∀ j, (mat x.x.ρ (T.sg j)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (x' (m.π (W.t.U j i)))) := fun j => by
    have h1 := congrArg (Polynomial.map x'.toRingHom) (spRoots B T.q n
      (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) j).1
    rw [Polynomial.map_map, hc, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, x.maps.1, MonoidAlgebra.mapRingHom_single,
      map_one, chi_rep, Polynomial.map_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun a => Polynomial.X - Polynomial.C (x' a)) (hU j i).symm
  have hinj : ∀ j, Function.Injective fun i => x' (m.π (W.t.U j i)) := fun j =>
    inj_of_prod ((heig j).symm.trans (x.eig j).2) (x.eig j).1
  have hl := lam_lift o.D_eq
  set Φ : MonoidAlgebra W.R (Ph0 Λ) →+* MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀ :=
    (MonoidAlgebra.mapDomainRingHom _ (πo0 Λ)).comp (MonoidAlgebra.mapRingHom _ (Ideal.Quotient.mk (ii W))) with hΦ
  have hp : ∀ g a, Φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (πo0 Λ g) (Ideal.Quotient.mk (ii W) a) :=
    fun g a => by simp [hΦ]
  have hl' : ∀ i y, o.p.D.lam i (Φ y) = Ideal.Quotient.mk (ii W) (W.t.D.lam i y) := hl
  have hrel : ∀ y, Rel W (W.t.D.tr y) → o.p.D.tr (Φ y) = 0 := fun y h =>
    (hl' 1 y).trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span h))
  have hsj : Function.Surjective (πo0 Λ) := Λ.πo0_surj
  refine ⟨?_, ⟨{
      fg := ?_, Ip := fun w => ?_, surj := hsurj, q := T.q, ph := Λ.ph, ta := Λ.ta, comm := Λ.comm, p_ta := Λ.p_ta
      U := fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i), y := fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i)
      s := Ideal.Quotient.mk (ii W) W.t.s, q1 := fun j g => ?_, q2 := fun j i g => ?_, gen := ?_
      f := x'.comp πb, maps := ⟨?_, fun v i => ?_⟩, f_s := ?_, f_y := fun j i => ?_, f_U := fun j => ?_
      eig := fun j => ?_ }, rfl, rfl⟩⟩
  · simp only [fo, fEl, map_prod, map_mul, map_sub, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have := sub_ne_zero.2 ((hinj j).ne (Finset.ne_of_mem_erase hi').symm)
    exact mul_ne_zero this this
  · classical
    obtain ⟨s, hs⟩ := Λ.fg
    refine ⟨s.image Λ.πo, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure]
    exact Λ.πo_surj.denseRange.topologicalClosure_map_subgroup Λ.πo_cont hs
  · refine inf_eq_left.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_iInf.2 fun i => ?_
    have h1 : G0.φu w g ∈ r.Ip w := by rw [had.2]; exact ⟨g, hg, rfl⟩
    have h2 := Subgroup.mem_iInf.1 h1.2 i
    rw [o.compat.1 i]
    change r.chib i (Λ.h.p₀ (Λ.G.φu w g)) = 1
    rw [Λ.h.p₀_φu]
    exact h2
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    have := hrel _ (Rel.q1 j ph g hph)
    rw [map_mul, hp, map_one, q1El, map_list_prod, List.map_ofFn] at this
    refine Eq.trans ?_ this
    rw [q1El]
    congr 4
    funext k
    simp only [Function.comp_apply, map_sub, hp, map_one, hph]
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    obtain ⟨ta, hta⟩ := hsj (Λ.ta j)
    have := hrel _ (Rel.q2 j i ph ta g hph hta)
    rw [map_mul, hp, map_one, q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub, hp, hp, hta] at this
    simp only [map_one] at this
    refine Eq.trans ?_ this
    rw [q2El]
    congr 5
    funext k
    by_cases hk : k = i <;> simp only [Function.comp_apply, map_sub, hp, map_one, hph, hk, if_true, if_false]
  · refine genBy_img (Ideal.Quotient.mkₐ O (ii W)) Ideal.Quotient.mk_surjective
      (rrGen l L G0 T Λ n O r B u J D A W) ?_
    rintro a (((⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | ⟨j, i, h⟩) | rfl)
    · refine Or.inl (Or.inl (Or.inl ⟨i, πo0 Λ g, ?_⟩))
      have := hl' i (MonoidAlgebra.single g 1)
      rw [hp, map_one] at this
      exact this.symm
    · refine Or.inl (Or.inl (Or.inr ⟨v, i, g, ?_⟩))
      rw [o.ψ_eq]
      rfl
    · exact Or.inl (Or.inr ⟨j, i, h.imp (congrArg _) (congrArg _)⟩)
    · exact Or.inr rfl
  · have e : (x'.comp πb).toRingHom = x'.toRingHom.comp πb.toRingHom := rfl
    rw [e, ← (UpperTheory.V.CA.d_gmap o.p.D).2.1, hD, (UpperTheory.V.CA.d_gmap _).2.1, hc]
    change (u.D.map x.f.toRingHom).comap Λ.h.p₀ = _
    rw [x.maps.1, rep_comap]
    rfl
  · rw [← x.maps.2 v i, ← hc]
    exact congrArg (pushCh x'.toRingHom) (hψ v i)
  · rw [AlgHom.comp_apply, hπ, ← ht, ← hx']
    exact congrArg x' hs
  · rw [AlgHom.comp_apply, hπ, ← map_zero x']
    exact congrArg x' (hy j i)
  · simpa only [AlgHom.comp_apply, hπ] using hinj j
  · simpa only [AlgHom.comp_apply, hπ, Λ.p_ph] using heig j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleFreeFiniteOverIwasawaAlgebra
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tens_free {Λ B S M X : Type} [CommRing Λ] [CommRing B] [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free B S] [Module.Finite B S]
    [Module.Free Λ M] [Module.Finite Λ M] [Nontrivial B] [AddCommGroup X] [Module Λ X]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (e : X ≃+ S ⊗[B] M)
    (he : ∀ (a : Λ) (x : X), e (a • x) = algebraMap B S (lam a) • e x) :
    Module.Free Λ X ∧ Module.Finite Λ X := by
  classical
  let φ : S ⊗[B] M ≃ₗ[B] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    (TensorProduct.congr (Module.Free.chooseBasis B S).repr (LinearEquiv.refl B M)).trans
      (TensorProduct.finsuppScalarLeft B M _)
  have key : ∀ (a : Λ) (x : X), φ (e (a • x)) = a • φ (e x) := by
    intro a x
    rw [he, algebraMap_smul, map_smul]
    ext i
    simp only [Finsupp.smul_apply, hl]
  let ψ : X ≃ₗ[Λ] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    { toFun := fun x => φ (e x)
      invFun := fun f => e.symm (φ.symm f)
      map_add' := fun x y => by simp
      map_smul' := key
      left_inv := fun x => by simp
      right_inv := fun f => by simp }
  exact ⟨Module.Free.of_equiv ψ.symm, Module.Finite.equiv ψ.symm⟩

theorem UpperTheory.V.Pa.Core.patchedModule_free_finite_over_iwasawaAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → Module.Free (abelian₂ O Unit D) (X0 m) ∧ Module.Finite (abelian₂ O Unit D) (X0 m) ∧ (∀ (a : abelian₂ O Unit D) (x : X0 m), a • x = m.s.toRingHom (MvPowerSeries.C a) • x) ∧ ∀ p (x : X0 m), m.s.toRingHom (MvPowerSeries.X p) • x = 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT
  obtain ⟨⟨hco, hfree, hfin, -⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hT
  haveI := A.b.free
  haveI := A.b.fin
  haveI := hfree
  haveI := hfin
  have hs : ∀ (t : W.R) (x : X0 m), t • x = m.π t • x := fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tens_free (Λ := abelian₂ O Unit D) (X := X0 m) A.b.lam A.b.smul_lam (AddEquiv.refl _)
    (fun a x => X0.lam_smul_def m a x)
  refine ⟨h1, h2, fun a x => ?_, fun p x => ?_⟩
  · rw [X0.lam_smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s,
      MvPowerSeries.constantCoeff_C]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s, MvPowerSeries.constantCoeff_X,
      map_zero, map_zero, zero_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PiCong
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]

private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

private theorem coeff_cong {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (I : Ideal A)
    (x y : MonoidAlgebra A G) (h : ∀ i, D.lam i x - D.lam i y ∈ I) (k : ℕ) :
    (D.chi x).coeff k - (D.chi y).coeff k ∈ I := by
  by_cases hk : k ≤ n
  · have h1 := I.mul_mem_left ((-1) ^ (n - k)) (h (n - k))
    rw [GDet.lam, GDet.lam, Nat.sub_sub_self hk, ← mul_sub, ← mul_assoc, ← mul_pow] at h1
    simpa using h1
  · have hd : ∀ z, (D.chi z).coeff k = 0 := fun z => by
      rw [← (UpperTheory.V.CA.d_toDet D z).1]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (UpperTheory.V.CA.d_chi D.toDet z).2.2.2.2.2.1 (not_le.1 hk))
    rw [hd, hd, sub_self]
    exact I.zero_mem

private theorem sees_glob {l : ℕ} [Fact l.Prime] {L : Loc} (G0 : Glob l L) {n : ℕ} {R : Type} [CommRing R]
    (D : GDet n R G0.G₀) (I : Ideal R) (hD : D.IsCont I) (e : ℕ) :
    ∃ V : OpenNormalSubgroup G0.Γ, ∀ g g' : G0.G₀, (g : G0.Γ) * (g' : G0.Γ)⁻¹ ∈ V → ∀ i,
      D.lam i (MonoidAlgebra.single g' 1) - D.lam i (MonoidAlgebra.single g 1) ∈ I ^ e := by
  obtain ⟨V0, hV0⟩ := UpperTheory.V.Pa.Core.dSees n R G0.G₀ D I hD e
  have hop : IsOpen (Subtype.val '' (V0 : Set G0.G₀) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ V0.isOpen
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hop ⟨1, one_mem V0, rfl⟩
  refine ⟨V, fun g g' hg i => hV0 i _ _ ?_⟩
  obtain ⟨a, ha, e⟩ := hV hg
  have e' : a = g * g'⁻¹ := Subtype.ext e
  have h2 : QuotientGroup.mk' V0.toSubgroup g' = QuotientGroup.mk' V0.toSubgroup g := by
    have : QuotientGroup.mk' V0.toSubgroup a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    rw [e', map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, h2]

private theorem sp_le {R : Type} [CommRing R] (I : Ideal R) {q n : ℕ} (P P' : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) (h : ∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) :
    spIdeal P' ut ≤ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

private theorem sp_lift (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (K : Ideal (MvPowerSeries (Fin q × Fin n) R))
    (h : spIdeal P ut ≤ K) :
    ∃ f : Sp P ut →ₐ[O] (MvPowerSeries (Fin q × Fin n) R ⧸ K), (∀ z, f (Sp.mk P ut z) = Ideal.Quotient.mk K z) ∧
      ∀ b, f (algebraMap R _ b) = Ideal.Quotient.mk K (MvPowerSeries.C b) :=
  ⟨Ideal.Quotient.factorₐ O h, fun _ => rfl, fun _ => rfl⟩

theorem UpperTheory.V.Pa.Core.piCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), T.ProL → Adapted T (r := r) → ∀ e : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), (∀ j k, ((fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) j).coeff k - ((fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) j).coeff k ∈ maximalIdeal B ^ e) ∧ ∀ (a : W.R) (z z' : MvPowerSeries (Fin T.q × Fin n) B), m.π a = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) z → (A.m N).θ (m.ρ N a) = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) z' → z - z' ∈ spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔ (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT hA e
  obtain ⟨V, hV⟩ := sees_glob G0 u.D (maximalIdeal B) u.cont e
  have h1 : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ j, (T.h N).p (T.ph N j) * (T.sg j : G0.Γ)⁻¹ ∈ V :=
    Filter.eventually_all.2 fun j => (T.ph_lim V j (by rw [hT.1]; exact bot_le)).filter_mono Λ.U_le
  filter_upwards [h1, Λ.p_lim V] with N h1 h2
  have hc := fun j => coeff_cong u.D _ _ _ (hV ((T.h N).p₀ (T.ph N j)) (T.sg j) (h1 j))
  refine ⟨hc, fun a z z' hz hz' => ?_⟩
  have hle := sp_le (maximalIdeal B ^ e) (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1))
    (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) hc
  set K := spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔
    (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) with hK
  by_cases hKt : K = ⊤
  · rw [hKt]; exact Submodule.mem_top
  haveI := Ideal.Quotient.nontrivial_iff.2 hKt
  obtain ⟨f, hf, hfb⟩ := sp_lift O _ _ K le_sup_left
  obtain ⟨f', hf', hfb'⟩ := sp_lift O _ _ K hle
  haveI := (spoCo l L G0 T Λ n O r B u J D A hA).1.1
  haveI : IsCO O (MvPowerSeries (Fin T.q × Fin n) B ⧸ K) := co_quot O (Spo A) _ f fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hf y⟩
  obtain ⟨p1, p2, p3, p4, p5⟩ := m.π_maps
  obtain ⟨r1, r2, r3, r4, r5⟩ := m.ρ_maps N
  obtain ⟨t1, t2⟩ := (A.m N).θ_pair
  have key : f.comp m.π = f'.comp ((A.m N).θ.comp (m.ρ N)) := by
    refine rrExt l L G0 T Λ n O r B u J D A W _ _ _ (fun i g => ?_) (fun v i g => ?_) ?_ (fun j i => ?_) fun j i => ?_
    · have a1 := lam_map W.t.D m.π.toRingHom i g
      rw [p1, lam_map, lam_comap] at a1
      have a2 := lam_map W.t.D (m.ρ N).toRingHom i g
      rw [r1, lam_comap] at a2
      have a3 := lam_map (A.A N).p.D (A.m N).θ.toRingHom i (πN0 Λ N g)
      rw [t1, lam_map, lam_comap, a2] at a3
      refine (congrArg f a1.symm).trans (Eq.trans ?_ (congrArg f' a3))
      rw [hfb, hfb', Ideal.Quotient.eq, ← map_sub]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (hV _ _ (h2 g) i))
    · have a1 : m.π (W.t.ψ v i g) = algebraMap B _ (u.ψ v i g) := congrArg (fun χ => ((χ g : _ˣ) : Spo A)) (p2 v i)
      have a2 : m.ρ N (W.t.ψ v i g) = (A.A N).p.ψ v i g := congrArg (fun χ => ((χ g : _ˣ) : (A.A N).R)) (r2 v i)
      have a3 : (A.m N).θ ((A.A N).p.ψ v i g) = algebraMap B _ (u.ψ v i g) :=
        congrArg (fun χ => Units.val (χ g)) (t2 v i)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, a3, hfb, hfb']
    · rw [← m.s_X_unit, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
    · have a1 : m.π (W.t.U j i) = _ := p4 j i
      have a2 : m.ρ N (W.t.U j i) = _ := r4 j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, (A.m N).θ_U]
      exact (hf _).trans (hf' _).symm
    · rw [← m.s_y, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
  have k2 : f (m.π a) = f' ((A.m N).θ (m.ρ N a)) := DFunLike.congr_fun key a
  rw [hz, hz', hf, hf'] at k2
  exact Ideal.Quotient.eq.1 k2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RmapsEx
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem rm_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {D q n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (s : Sinf O Unit D q n →ₐ[O] R) (ρ : R →ₐ[O] R') (g : Sinf O Unit D q n →ₐ[O] R')
    (ha : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal R) (hy : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal R)
    (ea : ∀ k, g (MvPowerSeries.C (MvPowerSeries.X k)) = ρ (s (MvPowerSeries.C (MvPowerSeries.X k))))
    (ey : ∀ p, g (MvPowerSeries.X p) = ρ (s (MvPowerSeries.X p))) (z : Sinf O Unit D q n) : ρ (s z) = g z := by
  have hm : ∀ x ∈ maximalIdeal R, ρ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  obtain ⟨f, -, huniq⟩ := sinfExt O D q n R' (fun k => g (MvPowerSeries.C (MvPowerSeries.X k)))
    (fun p => g (MvPowerSeries.X p))
    (fun k => by rw [ea]; exact hm _ (ha k)) (fun p => by rw [ey]; exact hm _ (hy p))
  have h1 : ρ.comp s = f := huniq _ ⟨fun k => (ea k).symm, fun p => (ey p).symm⟩
  have h2 : g = f := huniq _ ⟨fun _ => rfl, fun _ => rfl⟩
  exact (DFunLike.congr_fun (h1.trans h2.symm) z : _)

private noncomputable def rm_cc (O : Type) [CommRing O] (D q n : ℕ) : Sinf O Unit D q n →ₐ[O] abelian₂ O Unit D :=
  { (MvPowerSeries.constantCoeff : Sinf O Unit D q n →+* abelian₂ O Unit D) with
    commutes' := fun c => by
      rw [MvPowerSeries.algebraMap_apply]
      exact MvPowerSeries.constantCoeff_C _ }

theorem UpperTheory.V.Pa.Core.rmapsEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), Adapted T (r := r) → Nonempty (RMaps W) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W hT
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  have hw : ∀ k : Fin D, (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1 ∈ maximalIdeal W.R := by
    intro k
    rw [← res_eq_zero_iff O W.R, map_sub, map_mul, AlgHom.commutes, map_one,
      (W.t.psi _ _).red, ResidueField.algebraMap_eq, A.b.wt_res, sub_self]
  obtain ⟨s, ⟨hsa, hsy⟩, -⟩ := sinfExt O D T.q n W.R
    (Sum.elim (fun _ => W.t.s) (fun k => (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1))
    (fun p => W.t.y p.1 p.2)
    (by rintro (_ | k); exacts [W.t.s_mem, hw k]) (fun p => W.t.y_mem _ _)
  have hsm : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal W.R := by
    rintro (_ | k)
    · rw [hsa]; exact W.t.s_mem
    · rw [hsa]; exact hw k
  have hym : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal W.R := fun p => by
    rw [hsy]; exact W.t.y_mem _ _
  have hρ : ∀ N, ∃ f : W.R →ₐ[O] (A.A N).R, W.t.Maps f.toRingHom ((A.A N).p.D.comap (πN0 Λ N))
      (A.A N).p.ψ ((A.A N).s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ())))) (A.A N).U
      (fun j i => (A.A N).s (MvPowerSeries.X (j, i))) := by
    intro N
    obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupN l L G0 T Λ n O r B u J D A hT N
    obtain ⟨f, hf, -⟩ := W.univ _ t
    rw [hD, hψ, hs, hU, hy] at hf
    exact ⟨f, hf⟩
  choose ρ hρ using hρ
  haveI : IsCO O (Spo A) := (spoCo l L G0 T Λ n O r B u J D A hT).1.1
  obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupPi l L G0 T Λ n O r B u J D A
  obtain ⟨π, hπ, -⟩ := W.univ _ t
  rw [hD, hψ, hs, hU, hy] at hπ
  refine ⟨⟨s, hsa (Sum.inl ()), fun k => hsa (Sum.inr k), fun j i => hsy (j, i), ρ, hρ, ?_, π, hπ, ?_⟩⟩
  · intro N z
    refine rm_ext s (ρ N) (A.A N).s hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]; exact (hρ N).2.2.1.symm
      · rw [hsa, Sum.elim_inr, (A.A N).s_w k, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (A.A N).Rˣ) : (A.A N).R))
          ((hρ N).2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        rw [← this]
        rfl
    · intro p
      rw [hsy]
      exact ((hρ N).2.2.2.2 p.1 p.2).symm
  · intro z
    refine rm_ext s π ((IsScalarTower.toAlgHom O B (Spo A)).comp (A.b.lam.comp (rm_cc O D T.q n)))
      hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]
        refine Eq.trans ?_ hπ.2.2.1.symm
        simp [rm_cc, MvPowerSeries.constantCoeff_C]
      · rw [hsa, Sum.elim_inr, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (Spo A)ˣ) : Spo A))
          (hπ.2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        change algebraMap B (Spo A) (A.b.lam (MvPowerSeries.constantCoeff
          (MvPowerSeries.C (MvPowerSeries.X (Sum.inr k))))) = _
        rw [MvPowerSeries.constantCoeff_C, A.b.segmentWeightExponent, map_sub, map_mul, map_one,
          ← IsScalarTower.algebraMap_apply]
        erw [this]
    · intro p
      rw [hsy]
      refine Eq.trans ?_ (hπ.2.2.2.2 p.1 p.2).symm
      simp [rm_cc, MvPowerSeries.constantCoeff_X]
end

