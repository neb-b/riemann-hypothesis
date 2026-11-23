module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Descend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbPt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ambPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B], ¬ Module.Finite c.O B →
      ∃ (𝔞 : Amb l) (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (s : Finset 𝔞.K)
        (y : B →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ y.comp (algebraMap c.O B) = 𝔞.a c ∧ (∀ b ∈ maximalIdeal B, y b ∈ maximalIdeal 𝔞.V) ∧
        (∃ b ∈ maximalIdeal B, y b ≠ 0) ∧ (∀ a ∈ maximalIdeal c.O, 𝔞.a c a = 0) ∧
        ∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) := by
  intro l _ c B _ _ _ hB
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨P, t, n, hP, hmP, ht, htP, hn⟩ := Po.dimOne c.O B hB
  haveI : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsCO c.O (B ⧸ P) := co_quot c.O B _ (Ideal.Quotient.mkₐ c.O P) (Ideal.Quotient.mkₐ_surjective c.O P)
  have hq : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal B).map (Ideal.Quotient.mk P) = maximalIdeal (B ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hq
  have h0 : ∀ a ∈ maximalIdeal c.O, algebraMap c.O (B ⧸ P) a = 0 := fun a ha =>
    (Ideal.Quotient.eq_zero_iff_mem (a := algebraMap c.O B a)).2 (hmP (Ideal.mem_map_of_mem _ ha))
  have hn' : maximalIdeal (B ⧸ P) ^ n ≤ Ideal.span {Ideal.Quotient.mk P t} := by
    rw [← hm, ← Ideal.map_pow]
    refine (Ideal.map_mono hn).trans ?_
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨φ, hφi, hφf, hφX, hφC⟩ := Po.psFin c.O (B ⧸ P) h0 (Ideal.Quotient.mk P t)
    (hm ▸ Ideal.mem_map_of_mem _ ht) (fun h => htP (Ideal.Quotient.eq_zero_iff_mem.1 h)) n hn'
  obtain ⟨hfin, hch⟩ := Po.fin_res c
  haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField c.O))) (PowerSeries (ResidueField c.O)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  haveI : Finite (ResidueField (PowerSeries (ResidueField c.O))) :=
    Finite.of_equiv _ (PowerSeries.residueFieldOfPowerSeries (k := ResidueField c.O)).symm.toEquiv
  haveI : CharP (PowerSeries (ResidueField c.O)) l :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ResidueField c.O)) l
  obtain ⟨𝔞, f, hK, hf, hfa⟩ := ambL c (PowerSeries (ResidueField c.O)) (PowerSeries.C.comp (residue c.O))
  obtain ⟨y, s, hy, hs⟩ := Po.finExt 𝔞.K 𝔞.V _ _ φ f hφi hφf hf.inj
  have hyφ : ∀ x, y (φ x) = f x := fun x => RingHom.congr_fun hy x
  have hya : ∀ a, y (algebraMap c.O (B ⧸ P) a) = 𝔞.a c a := fun a => by
    rw [← hφC, hyφ, ← hfa]
    rfl
  have hX : f PowerSeries.X ∈ maximalIdeal 𝔞.V := by
    haveI := hf.loc
    refine map_nonunit f _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  refine ⟨𝔞, _, inferInstance, inferInstance, inferInstance, f, s, y.comp (Ideal.Quotient.mk P), hK, hf,
    RingHom.ext hya, fun b hb => ?_, ⟨t, ht, ?_⟩, fun a ha => ?_, fun b => hs _⟩
  · have hb' : Ideal.Quotient.mk P b ∈ maximalIdeal (B ⧸ P) := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hn' (Ideal.pow_mem_pow hb' n))
    refine (maximalIdeal.isMaximal 𝔞.V).isPrime.mem_of_pow_mem n ?_
    rw [RingHom.comp_apply, ← map_pow, ← hu, map_mul, ← hφX, hyφ]
    exact Ideal.mul_mem_left _ _ hX
  · rw [RingHom.comp_apply, ← hφX, hyφ]
    exact fun h => PowerSeries.X_ne_zero (hf.inj (h.trans (map_zero f).symm))
  · rw [← hya, h0 a ha, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtClosed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem hEl_map' (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Matrix.add_apply, Matrix.smul_apply]

private theorem mult_iff' (f : R →ₐ[c.O] R') (r : Lift c.O D.rbar R) :
    D.Mult (r.map f).hom ↔ ∀ g i j,
      f ((adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) = 0 := by
  refine forall_congr' fun g => ?_
  rw [← f.commutes]
  exact UpperTheory.V.Ws.Po.gsp_iff (f : R →+* R') _ (r.hom g)

end

theorem UpperTheory.V.Ws.Po.ptClosed :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Cond.IsClosed (rbar := D.rbar) fun _ _ _ _ ρ => D.IsPt ρ := by
  intro hP Ω _ _ _ l _ c D hD
  have hL : Cond.IsClosed (rbar := D.rbarAt l) fun _ _ _ _ r => OnComp D.condL (D.r0At l) r := by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compL D hD hP.loc
    exact onCompClosed _ _ _ _ _ _ (closedL D) U ρ hrep J hJ
  have hQ : ∀ p ∈ D.Sb,
      Cond.IsClosed (rbar := D.rbarAt p) fun _ _ _ _ r => OnComp (D.condP p) (D.r0At p) r := fun p hp => by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compP D hD hP.loc p hp
    exact onCompClosed _ _ _ _ _ _ (closedP D p) U ρ hrep J hJ
  refine closed_of_set _ fun R _ _ _ r => ?_
  obtain ⟨IL, hIL⟩ := hL R (D.loc r l)
  choose IP hIP using fun p hp => hQ p hp R (D.loc r p)
  refine ⟨{x | (∃ g i j, x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) ∨
    (∃ A : ValuationSubring Ω, Raw.Away D.T A ∧ ∃ g ∈ Ine (F := ℚ) A, D.rbar g = 1 ∧ ∃ i j, x = (r.hom g - 1) i j) ∨
    (∃ i j, lamW i ≠ lamW j ∧ x = r.hom D.ph i j) ∨ x = D.hEl r.hom 0 2 ∨ x = D.hEl r.hom 2 0 ∨
    x ∈ IL ∨ ∃ p, ∃ hp : p ∈ D.Sb, x ∈ IP p hp}, fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨g, i, j, rfl⟩ | ⟨A, hA, g, hg, hg1, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl | rfl | hx | ⟨p, hp, hx⟩ := hx
    · exact (mult_iff' D f r).1 h.mult g i j
    · exact (one_iff (f : R →+* R') (r.hom g)).1 (h.unr A hA g hg hg1) i j
    · exact h.nrm.1 i j hij
    · rw [← hEl_map']; exact h.nrm.2.1
    · rw [← hEl_map']; exact h.nrm.2.2
    · exact (hIL R' f).1 h.atL x hx
    · exact (hIP p hp R' f).1 (h.atP p hp) x hx
  · refine ⟨(mult_iff' D f r).2 fun g i j => h _ (.inl ⟨g, i, j, rfl⟩),
      fun A hA g hg hg1 => (one_iff (f : R →+* R') (r.hom g)).2 fun i j =>
        h _ (.inr (.inl ⟨A, hA, g, hg, hg1, i, j, rfl⟩)),
      ⟨fun i j hij => h _ (.inr (.inr (.inl ⟨i, j, hij, rfl⟩))), ?_, ?_⟩,
      (hIL R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inl hx)))))),
      fun p hp => (hIP p hp R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inr ⟨p, hp, hx⟩))))))⟩
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inl rfl))))
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inr (.inl rfl)))))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtTorus
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ptTorus :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (r r' : Lift c.O D.rbar R) (s : Rˣ × Rˣ),
      res c.O R s.1 = 1 → res c.O R s.2 = 1 → (∀ g, r'.hom g = tconj s (r.hom g)) → D.IsPt r → D.IsPt r' := by
  intro Ω _ _ _ l _ c D _ R _ _ _ r r' s h1 h2 hc hP
  have hone : ∀ X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R, X = 1 → UpperTheory.V.GradeZeroInterpolatingElement.tconj s X = 1 := by
    rintro X rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.GradeZeroInterpolatingElement.tconj, UpperTheory.V.GradeZeroInterpolatingElement.wv, UpperTheory.V.GradeZeroInterpolatingElement.wt, Matrix.one_apply]
  have hent : ∀ (X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R) (i j : Fin 4), UpperTheory.V.GradeZeroInterpolatingElement.tconj s X i j = 0 ↔ X i j = 0 := by
    intro X i j
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    constructor
    · intro h
      have := congrArg (fun x => (↑(UpperTheory.V.GradeZeroInterpolatingElement.wv s (UpperTheory.V.GradeZeroInterpolatingElement.wt i j))⁻¹ : R) * x) h
      simpa [← mul_assoc] using this
    · intro h
      simp [h]
  have hEl' : D.hEl r'.hom = UpperTheory.V.GradeZeroInterpolatingElement.tconj s (D.hEl r.hom) := by
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.Raw.hEl, hc]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    rw [mul_add, mul_smul_comm]
  obtain ⟨hb, h02, h20⟩ := hP.nrm
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g
    rw [hc]
    exact UpperTheory.V.Ws.Po.gsp_conj s (hP.mult g)
  · intro A hA g hg hb'
    rw [hc]
    exact hone _ (hP.unr A hA g hg hb')
  · intro i j hij
    rw [hc, hent]
    exact hb i j hij
  · rw [hEl', hent]
    exact h02
  · rw [hEl', hent]
    exact h20
  · exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt l) D.condL (D.r0At l)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condL_map D f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusL D ρ ρ' t h hq)
      R (D.loc r l) (D.loc r' l) s h1 h2 (fun g => hc g) hP.atL
  · intro p hp
    exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt p) (D.condP p) (D.r0At p)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condP_map D p f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusP D p ρ ρ' t h hq)
      R (D.loc r p) (D.loc r' p) s h1 h2 (fun g => hc g) (hP.atP p hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

theorem UpperTheory.V.Ws.Po.univOf :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ P : Cond c.O D.rbar, P.IsClosed →
      (∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), P R ρ → D.UnrT ρ.hom 1) →
      (∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R), P R ρ) →
      ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O D.rbar U), Represents P ρ := by
  intro hP Ω _ _ _ l hl c D hD P hc hu ⟨R₁, _, _, _, ρ₁, h₁⟩
  obtain ⟨rb, r0, hb, -, -, -, H⟩ := descend D hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := facts D hD
  obtain ⟨_, _⟩ := UpperTheory.V.Ws.Po.fin_res c
  haveI : IsGalois ℚ Ω := {}
  haveI hcl := isClosed_NS Ω D.SP
  haveI : CompactSpace D.Gam := inferInstance
  haveI : T2Space D.Gam := inferInstance
  haveI : TotallyDisconnectedSpace D.Gam := totDisc_quot _ hcl
  have hq : Topology.IsQuotientMap (toGS Ω D.SP) := QuotientGroup.isQuotientMap_mk _
  have hlc : IsLocallyConstant D.rbar := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have : D.rbar (g⁻¹ * x) = 1 := hx
    rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]
  have hlb : IsLocallyConstant rb := fun s => by
    rw [← hq.isOpen_preimage]
    have := hlc s
    rw [← hb] at this
    exact this
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l c.O D.Gam (Fin 4) rb (phiGam D hD hP) hlb
  obtain ⟨ρ, hρ, -⟩ := (H R).1 r
  let P₀ : Cond c.O D.rbar := fun C _ _ _ s => ∃ t : Lift c.O rb C, s.hom = t.hom.comp (toGS Ω D.SP)
  have hmap : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : R →ₐ[c.O] C),
      (ρ.map f).hom = (r.map f).hom.comp (toGS Ω D.SP) := fun C _ _ _ f => by
    ext g a b
    show f (ρ.hom g a b) = f (r.hom _ a b)
    rw [hρ]
    rfl
  have h0 : Represents P₀ ρ := fun C _ _ _ => by
    refine ⟨fun f => ⟨r.map f, hmap C f⟩, fun s ⟨t, ht⟩ => ?_⟩
    obtain ⟨f, hf, huq⟩ := (hr C).2 t trivial
    refine ⟨f, Lift.ext (by rw [hmap, hf, ht]), fun f' hf' => huq f' (Lift.ext ?_)⟩
    refine (MonoidHom.cancel_right hq.surjective).1 ?_
    rw [← hmap, ← ht]
    exact congrArg Lift.hom hf'
  have hPP : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (s : Lift c.O D.rbar C), P C s → P₀ C s :=
    fun C _ _ _ s h => (H C).2 s (hu C s h)
  obtain ⟨R', _, _, _, p, -, h⟩ := univ_cond c.O (G ℚ Ω) (Fin 4) D.rbar R ρ P₀ P h0 hc
    ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hPP _ _ h₁, h₁⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ.map p, fun C _ _ _ =>
    ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨hPP _ _ h', h'⟩⟩⟩
end

