module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysinPsOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.TcSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Vertex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.OddVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.EntVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FrobIn
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem frobIn_pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong A ha hb h m

private theorem frobIn_dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {g : G K Ω} (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem frobIn_isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) :
    IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (frobIn_dec_le ih.1 hx)
    have h2 := frobIn_pow_cong A (frobIn_dec_le ih.1 hx) (b := x ^ q ^ n)
      (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

theorem UpperTheory.V.Ws.frobIn :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (M : ℕ),
          IsOpen (U : Set (G ℚ Ω)) → M ≠ 0 → ∃ (p : ℕ) (A : ValuationSubring Ω) (f : ℕ) (σ : G ℚ Ω), p.Prime ∧ ¬ p ∣ M ∧
            A.valuation (p : Ω) < 1 ∧ 0 < f ∧ σ ∈ U ∧ IsFrob A (p ^ f) σ ∧ ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) ^ f := by
  intro Ω _ _ _ l hl U M hU hM
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (M + l + 1)
  have hpM : ¬ p ∣ M := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h
    omega
  have hlp : p ≠ l := by omega
  obtain ⟨hex, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  obtain ⟨A, hA⟩ := hex p hp
  obtain ⟨φ, hφ⟩ := hfr A p hp hA
  obtain ⟨w, hw, -, -⟩ := hpl A p hp hA
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp) hA ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have h : ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [cycZ_toZModPow_eq hlw hw (q := p) hφ.2 n]
  haveI : IsGalois ℚ Ω := inferInstance
  haveI : Finite (G ℚ Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  obtain ⟨f, hf, -, hfU⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := U) Subgroup.index_ne_zero_of_finite φ
  refine ⟨p, A, f, φ ^ f, hp, hpM, hA, hf, hfU, frobIn_isFrob_pow hφ f, ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinAl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinAl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p p' : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → (T.fr W).IsRes a p' → p.In nP → p'.In nP →
      ∃ (W' : Finset ℕ) (s s' : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ (T.fr W').IsRes a s' ∧
        s.In qQ ∧ s'.In qQ ∧ s.SamePs p ∧ s'.SamePs p' ∧ s.SameAl s' ∧ Ent s.r (-wAl) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p p' hp hp' hs hs'
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨r1, -, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨y, y1, y2, y3, y4⟩ := Gys.dataPs (T.fr W) a p hp hs.1
  obtain ⟨y', y1', y2', y3', y4'⟩ := Gys.dataPs (T.fr W) a p' hp' hs'.1
  obtain ⟨W', s1, s2, hy, x, m, x1, x2, x3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wAl) (-wPs) r1 r3 Bool
    (fun b => cond b y y') fun b => by cases b; exacts [⟨y1', y2'⟩, ⟨y1, y2⟩]
  obtain ⟨z, z1, z2⟩ := hz true
  obtain ⟨z', z1', z2'⟩ := hz false
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, a6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y z m _ x1 x2 x3 (hy true) y2 y3 z1 z2
  obtain ⟨s', b1, b2, b3, b4, b5, b6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y' z' m _ x1 x2 x3 (hy false) y2' y3' z1' z2'
  exact ⟨W', s, s', s1, s2, a1, b1, a2, b2, ⟨fun g => (a5 g).trans (y4 g).symm, a6⟩, ⟨fun g => (b5 g).trans (y4' g).symm, b6⟩,
    ⟨fun g => (a3 g).trans (b3 g).symm, fun v => (a4 v).trans (b4 v).symm⟩, g, 1, 0, by decide,
    a3 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinPs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinPs :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) :=
  UpperTheory.V.Ws.Gys.gysinPs_of
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Labels
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ent_of_map {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) {r : Γ →* M4 R} {w : ℤ × ℤ}
    (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, hw, hne⟩ := h
  refine ⟨g, i, j, hw, fun h0 => hne ?_⟩
  have e : mapRep f r g i j = f (r g i j) := rfl
  rw [e, h0, map_zero]

private theorem mapRep_eq {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (r : Γ →* M4 R) (g : Γ) :
    mapRep f r g = (r g).map f := rfl

theorem UpperTheory.V.Ws.labels :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → ∃ pr, LabOk D pr ∧ ∀ g0 : G ℚ Ω,
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) →
      ∃ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P ∧ NearSplit D pr 𝔞 P ∧ IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r) ∧
        (Star (mapRep 𝔞.toK r) → StarE P.r) := by
  intro Ω _ _ _ l _ c D hD 𝔞 r u hK
  obtain ⟨pr, hok, hunit⟩ := Lab.choice D hD 𝔞 r u hK
  refine ⟨pr, hok, fun g0 hsep => ?_⟩
  have hwinv : ∀ Y : M4 𝔞.V, wM 𝔞.V pr * (adj (wM 𝔞.V pr) * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, sp_mul_adj (wM_sp pr), Matrix.one_mul]
  obtain ⟨hs, hsep2⟩ := sg_sep hD 𝔞 pr
  have hcg := hK.cg pr
  have hconj : adj (adj (wM 𝔞.V pr) * u) * (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr) *
      (adj (wM 𝔞.V pr) * u) = adj u * r (D.sg l) * u := by
    rw [adj_mul, adj_adj]
    simp only [Matrix.mul_assoc, hwinv]
  obtain ⟨-, -, -, himp⟩ := Lab.resFlag 𝔞.V (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr)
    (adj (wM 𝔞.V pr) * u) (fun i => 𝔞.a c ((chi D pr i (D.sg l) : (c.O)ˣ) : c.O))
    (fun i => 𝔞.a c ((D.ps i (D.sg l) : (c.O)ˣ) : c.O)) (hcg _) (sp_mul (sp_adj (wM_sp pr)) hK.sp)
    (by rw [hconj]; exact hK.flag _ hs) (by rw [hconj]; exact hK.char _ hs) hsep2
  have hminor := (himp hunit).1
  have hoff : ∀ i j, i ≠ j → (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i j ∈ maximalIdeal 𝔞.V := by
    intro i j hij
    have h := hcg g0 i j
    rwa [Matrix.diagonal_apply_ne _ hij, sub_zero] at h
  have hdiff : ∀ i j, i ≠ j → IsUnit ((adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i i -
      (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) j j) := by
    intro i j hij
    apply unit_of_sub_mem (𝔞.unit_sub (hsep i j hij))
    have h1 := hcg g0 i i
    have h2 := hcg g0 j j
    simp only [Matrix.diagonal_apply_eq] at h1 h2
    have h3 := (maximalIdeal 𝔞.V).sub_mem h1 h2
    rw [sub_sub_sub_comm] at h3
    exact h3
  obtain ⟨P, v, b, hsm, hv, hv1, hPr, hdg, hlow, hb, hbup, hfac⟩ := Lab.exNorm 𝔞 (G ℚ Ω) r u pr g0
    (𝔞.a c ((D.th g0 : (c.O)ˣ) : c.O)) hK.small (𝔞.unit_two c hD.l_odd) ((D.th g0).isUnit.map _)
    (hK.mult g0) hK.sp _ _ rfl rfl hoff hdiff hunit hminor
  obtain ⟨hQ, hN⟩ := Lab.pairOf D hD 𝔞 r u hK pr g0 P v b hok hsm hv hv1 hPr hdg hlow hb hbup hfac
  have hm : IsGSp 1 (wM 𝔞.V pr * v) := sp_mul (wM_sp pr) hv
  have hinj : Function.Injective 𝔞.toK := fun x y h => Subtype.ext h
  have hmap : ∀ g, mapRep 𝔞.toK P.r g =
      adj ((wM 𝔞.V pr * v).map 𝔞.toK) * mapRep 𝔞.toK r g * (wM 𝔞.V pr * v).map 𝔞.toK := by
    intro g
    rw [mapRep_eq, mapRep_eq, hPr g, adj_map, Matrix.map_mul, Matrix.map_mul]
  have hparM : (∀ g, Par (mapRep 𝔞.toK r g)) → Par ((wM 𝔞.V pr * v).map 𝔞.toK) := by
    intro hp
    have hpr : Par (r g0) := fun i j hij => hinj (by
      have h := hp g0 i j hij
      rw [mapRep_eq, Matrix.map_apply] at h
      rw [h, map_zero])
    have hX : Par (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) :=
      Par.mul (Par.mul (Par.adj (wM_par pr)) hpr) (wM_par pr)
    have hXv : (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) * v = v * Matrix.diagonal (P.r g0).diag := by
      rw [hdg.diagonal_diag, hPr g0, adj_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc v (adj v), sp_mul_adj hv, Matrix.one_mul]
    have hpv : Par v := Lab.parEig 𝔞.V _ v _ hoff hdiff hv1 hXv hX
    have hpm := Par.mul (wM_par pr) hpv
    intro i j hij
    rw [Matrix.map_apply, hpm i j hij, map_zero]
  refine ⟨P, hQ, hN, ?_, ?_⟩
  · refine ⟨⟨(adj (wM 𝔞.V pr * v)).map 𝔞.toK, (wM 𝔞.V pr * v).map 𝔞.toK, ?_, ?_⟩, fun g => ?_⟩
    · rw [← Matrix.map_mul, sp_adj_mul hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [← Matrix.map_mul, sp_mul_adj hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hmap g, adj_map]
      rfl
  · intro hstar
    have hgm : IsGSp 1 ((wM 𝔞.V pr * v).map 𝔞.toK) := by
      simpa using gsp_map 𝔞.toK hm
    obtain ⟨h1, h2, h3⟩ := Lab.starConj 𝔞.K (G ℚ Ω) (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r)
      ((wM 𝔞.V pr * v).map 𝔞.toK) hgm hmap hparM hstar
    refine ⟨ent_of_map _ h1, ent_of_map _ h2, ?_⟩
    rcases h3 with h | h | h
    · exact Or.inl (ent_of_map _ h)
    · exact Or.inr (Or.inl (ent_of_map _ h))
    · exact Or.inr (Or.inr (ent_of_map _ h))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LatSix
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem lat_six {Si : Set (ℤ × ℤ)} (h : CompanionTheory Si) (h1 : -wAl ∉ Si → -wTh ∉ Si) (h2 : wBe ∉ Si → wPs ∉ Si → -wAl ∉ Si) :
    wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP := by
  rcases h with h | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩
  · exact h
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)

theorem UpperTheory.V.Ws.lat :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (pr : Bool) (g0 : G ℚ Ω), LabOk D pr →
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) → ∀ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P → NearSplit D pr 𝔞 P → StarE P.r →
      ∃ P' : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P' ∧ IsConj4 (mapRep 𝔞.toK P.r) (mapRep 𝔞.toK P'.r) ∧ LatShape D pr g0 (𝔞.red c) (P'.map (residue 𝔞.V)) := by
  intro hP Ω _ _ _ l _ c D hD 𝔞 pr g0 _ hd P hQ hN hS
  obtain ⟨t, P', hT, h6⟩ := vertex 𝔞 P hQ.small (hQ.pair.low ())
    (fun g i j hij => by simpa [diagRep, Matrix.diagonal_apply_ne _ hij] using hN.red g i j) hN.flag hS
  obtain ⟨hp, hdg, hψ, hc⟩ := tcPair (frQ D pr g0) (𝔞.a c) 𝔞.toK Subtype.val_injective t P P' hT hQ.pair
  have hsm := tcSmall 𝔞 t P P' hT hQ.small
  have hred : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hpre : PreRes (frQ D pr g0) (𝔞.red c) (P'.map (residue 𝔞.V)) := by
    refine ⟨hp.map _, fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · refine Ideal.Quotient.eq.2 ?_
      rw [hdg]
      simpa [diagRep, frQ] using hN.red g i i
    · refine (PD.map_ψ P' _ v i s).trans (Ideal.Quotient.eq.2 ?_)
      exact (hψ v i s).symm ▸ hN.char s hs i
    · obtain ⟨A, _, _, _, f, P₁, hf, hcont, rfl⟩ := hsm
      haveI := hf.loc
      exact hcont.map ((residue 𝔞.V).comp f) fun x hx => (residue_eq_zero_iff _).2 (map_nonunit f x hx)
  have hmul : ∀ i g, (frQ D pr g0).χ i g * (frQ D pr g0).χ i.rev g = (frQ D pr g0).ν g := by
    intro i g
    cases pr <;> fin_cases i <;> simp [frQ, chi, lab, Raw.ps, Raw.th, Fin.rev, mul_comm]
  have hE := entVan _ _ _ hpre hmul (oddVan D hD hP.loc _ _ hred pr g0 hd)
  obtain ⟨n1, n2⟩ := noNeg _ _ _ hpre hE
  obtain ⟨s1, s2, s3⟩ := lat_six h6 n1 n2
  obtain ⟨u1, u2, u3, u4⟩ := shape _ _ _ hpre hE s1 s2 s3
  refine ⟨P', ⟨hsm, hp, fun s hs i => (hψ () i s).trans (hQ.inert s hs i)⟩, hc,
    ⟨hpre.pair, ⟨hpre.diag, hpre.char, .inl ⟨u1, u2⟩⟩, hpre.cont⟩, u1, u2 (), u3, u4.imp id ?_⟩
  rintro ⟨v1, ⟨v, v2, v3⟩, v4⟩
  refine ⟨v1, v2, fun s hs => ?_, fun ⟨m, hm⟩ => v4 ⟨fun _ => m, fun _ => hm⟩⟩
  have e : Raw.bar (chi D pr 0) s = Raw.bar (chi D pr 2) s := (𝔞.j c).injective (v3 s hs)
  have hu : Raw.bar D.al s ≠ 0 := ((D.al s).isUnit.map (residue c.O)).ne_zero
  have ht : Raw.bar D.th s = Raw.bar D.al s * Raw.bar D.Psi s := map_mul (residue c.O) (D.al s : c.O) (D.Psi s : c.O)
  cases pr
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e)
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem muIne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ muOf l (Dec (F := F) A)) : s ∈ Ine (F := F) A := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨h1, a, h2⟩ := hs
  exact Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h2)

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem low_desc {A V : Type} [CommRing A] [CommRing V] [IsLocalRing V] (f : A →+* V) (hf : Function.Injective f)
    [IsLocalHom f] (ν : V) (hν : IsUnit ν) (X n₀ : M4 A) (hX : IsGSp ν (X.map f)) (h0 : IsLow (n₀.map f))
    (hs : SuppM nP ((X.map f).map (residue V))) (hd : ∀ i, IsUnit (((X.map f).map (residue V)) i i))
    (h0' : IsLow ((n₀.map f).map (residue V))) (hq : SuppM qQ ((n₀.map f).map (residue V))) :
    ∃ n : M4 A, IsLow n ∧ IsUp (adj n * X * n₀) := by
  have hG : ∀ (μ : A) (Y : M4 A), IsGSp (f μ) (Y.map f) → IsGSp μ Y := fun μ Y h => by
    unfold IsGSp at h ⊢
    rw [adj_map, ← Matrix.map_mul] at h
    ext i j
    apply hf
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hμ : f ((adj X * X) 0 0) = ν := by
    have h := hX
    unfold IsGSp at h
    rw [adj_map, ← Matrix.map_mul] at h
    simpa using congrFun (congrFun h 0) 0
  obtain ⟨⟨u1, u2⟩, -⟩ := Rq.shapeQ _ _ _ hs hd h0' hq
  rw [← Matrix.map_mul, ← Matrix.map_mul] at u1 u2
  simp only [Matrix.map_apply, ← map_mul, ← map_sub] at u1 u2
  refine Rq.luG A ((adj X * X) 0 0) X n₀ (IsUnit.of_map f _ (hμ ▸ hν)) (hG _ _ (hμ ▸ hX))
    ⟨hG 1 _ (by rw [map_one]; exact h0.1), fun i => hf ?_, fun i j hij => hf ?_⟩
    (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u1)) (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u2))
  · rw [map_one]; exact h0.2.1 i
  · rw [map_zero]; exact h0.2.2 i j hij

private theorem low_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n : M4 A} (h : IsLow n) : IsLow (n.map f) :=
  ⟨by simpa using isGSp_map f h.1, fun i => by rw [Matrix.map_apply, h.2.1, map_one],
    fun i j hij => by rw [Matrix.map_apply, h.2.2 i j hij, map_zero]⟩

private theorem up_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n X m : M4 A} (h : IsUp (adj n * X * m)) :
    IsUp (adj (n.map f) * X.map f * m.map f) := fun i j hij => by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, h i j hij, map_zero]

theorem UpperTheory.V.Ws.restrQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T₀ T : Tower D, T₀.Fit → T₀.Le T → ∀ (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V), QPair D T₀.pr (resQ T₀.F T₀.g0) 𝔞 P →
      LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) (P.map (residue 𝔞.V)) →
      ∃ P' : PD T.ι (G T.F Ω) 𝔞.V, 𝔞.Small P' ∧ (T.fr ∅).IsPair (𝔞.a c) P' ∧ P'.r = P.r.comp (resQ T.F) ∧
        T.OverQ (P.map (residue 𝔞.V)) (P'.map (residue 𝔞.V)) ∧ (T.fr ∅).IsRes (𝔞.red c) (P'.map (residue 𝔞.V)) ∧
        ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), P'.ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := by
  intro Ω _ _ _ l hl c D hD T₀ T hF hLe 𝔞 P hP hS
  have hOk : T.Ok := (leFit D hD T₀ T hLe).1 hF.1
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP.small
  haveI := hf.loc
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (𝔞.a c (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit ((((P₁.map f).map (residue 𝔞.V)).r x) i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  choose n hn hb using fun v : T.ι => low_desc f hf.inj _ (hν (g v)) (P₁.r (g v)) (P₁.n ()) (hP.pair.mult (g v))
    (hP.pair.low ()) (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag
  let Q : PD T.ι (G T.F Ω) A := ⟨P₁.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj ((Q.map f).n v) * (Q.map f).r s * (Q.map f).n v) ∧
      ∀ i, (Q.map f).ψ v i s = (P₁.map f).ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ ((P₁.map f).r (g v)) ((P₁.map f).r ((g v)⁻¹ * resQ T.F s * g v)) ((P₁.map f).r (resQ T.F s)) _ _
      (hν (g v)) (hP.pair.mult (g v)) (hP.pair.low ()) (low_map f (hn v)) (up_map f (hb v))
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.pair.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hI : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), (Q.map f).ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := fun v i s hs => by
    rw [(key v s (Ine_le_Dec _ hs)).2, hP.inert _ (hgI v s hs), hconj]
  have hpair : (T.fr ∅).IsPair (𝔞.a c) (Q.map f) := by
    refine ⟨fun x => hP.pair.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ (P₁.map f).r hP.pair.kill, ?_,
      fun v => low_map f (hn v), fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩
    · obtain ⟨j, hj⟩ := hLe.g0
      show ((P₁.map f).r (resQ T.F T.g0)).IsDiag
      have h := hP.pair.nrm
      change ((P₁.map f).r (resQ T₀.F T₀.g0)).IsDiag at h
      rw [hj, map_pow, ← h.diagonal_diag, Matrix.diagonal_pow]
      exact Matrix.isDiag_diagonal _
    · refine (hI v i s (muIne T.F l _ (T.ovl v) hs)).trans ?_
      rw [Rq.muPs D hD T hOk _ s hs i, Units.val_one, map_one]
  have hb' : ∀ v, IsUp (adj (((Q.map f).map (residue 𝔞.V)).n v) * ((P₁.map f).map (residue 𝔞.V)).r (g v) *
      ((P₁.map f).map (residue 𝔞.V)).n ()) := fun v => up_map (residue 𝔞.V) (up_map f (hb v))
  have hp' := hpair.map (residue 𝔞.V)
  refine ⟨Q.map f, ⟨A, _, _, inferInstance, f, Q, hf, fun i j N => (hc i j N).comp_continuous (cont_resQ T.F), rfl⟩, hpair, rfl,
    ⟨rfl, fun v => ⟨(), g v, hg v, hb' v⟩⟩, ⟨hp', ⟨fun x i => ?_, fun v s hs i => ?_, Or.inl ⟨fun x => hS.supp _, fun v => ?_⟩⟩,
      fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, hI⟩
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F x))
    rw [hLe.pr]
    exact hS.res.res.diag (resQ T.F x) i
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F s))
    refine (PD.map_ψ (Q.map f) (residue 𝔞.V) v i s).trans ?_
    rw [(key v s hs).2, ← PD.map_ψ, hLe.pr, ← hconj (chi D T₀.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  · exact (Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag).2 _ (hp'.low v) (hb' v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCont
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  have ha0 : 0 ≤ a := by simpa using hy 1 0 (Ideal.zero_mem _)
  rw [Metric.continuous_iff']
  intro g0 ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber ((Ideal.Quotient.mk (I ^ N)) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy N _ (Ideal.Quotient.eq.mp hg)) hN

theorem UpperTheory.V.Ws.smallCont :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ {ι Γ : Type} [Group Γ] [TopologicalSpace Γ]
          (P : PD ι Γ 𝔞.V), 𝔞.Small P → Continuous (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) P.r) := by
  intro l _ 𝔞 e he ι Γ _ _ P hP
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP
  obtain ⟨inj, loc, -, -, -⟩ := hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let y : A →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp f)
  have hV : ∀ v : 𝔞.V, ‖e (v : 𝔞.K)‖ ≤ 1 := fun v => (he.2 _).mp v.2
  have hle : ∀ x : A, ‖y x‖ ≤ 1 := fun x => hV (f x)
  have hlt : ‖y ϖ‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => hϖ.not_isUnit ?_
    have hne : (f ϖ : 𝔞.K) ≠ 0 := by
      intro h0
      have h0' : f ϖ = 0 := Subtype.ext h0
      exact hϖ.ne_zero (inj (by rw [h0', map_zero]))
    have h1' : ‖e (f ϖ : 𝔞.K)‖ = 1 := h1
    have hinv : ((f ϖ : 𝔞.K))⁻¹ ∈ 𝔞.V := by
      rw [he.2, map_inv₀, norm_inv, h1', inv_one]
    have hu : IsUnit (f ϖ) := IsUnit.of_mul_eq_one (⟨_, hinv⟩ : 𝔞.V) (Subtype.ext (mul_inv_cancel₀ hne))
    haveI := loc
    exact (isUnit_map_iff f ϖ).mp hu
  have hpow : ∀ n, ∀ x ∈ maximalIdeal A ^ n, ‖y x‖ ≤ ‖y ϖ‖ ^ n := by
    intro n x hx
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hle c)
  refine continuous_matrix fun i j => ?_
  have hc' : AdicCont (maximalIdeal A) fun g => P₁.r g i j := by
    unfold PD.Cont at hc
    exact hc i j
  exact cont_of_adic (maximalIdeal A) y _ hlt hpow (fun g => P₁.r g i j) hc'
end

