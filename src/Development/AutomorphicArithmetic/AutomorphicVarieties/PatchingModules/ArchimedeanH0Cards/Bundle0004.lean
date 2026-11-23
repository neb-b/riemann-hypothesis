module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArGlob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arGlob :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F))), l ≠ 2 → S.Finite → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → FinH l (GS Ω S) ∧ SecondCohomologyRightExactModL l (GS Ω S) := by
  intro hP F Ω _ _ _ _ _ l _ S hl hS hab
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S = ↑T := ⟨hS.toFinset, by simp⟩
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))),
      (∀ m : M.X, l • m = 0) → Finite (H1 M.ρ) ∧ Finite (H2 M.ρ) ∧ Subsingleton (Hn M.ρ 3) := by
    intro A _ M hM
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
    obtain ⟨hc, -, ⟨e1, -⟩, ⟨e2, -⟩⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
    obtain ⟨-, h1, h2, h3⟩ := hP.gf F Ω l 1 M.X T (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos
      (fun v hv => hab v hv) hc
    exact ⟨Finite.of_equiv _ e1.symm.toEquiv, Finite.of_equiv _ e2.symm.toEquiv,
      GlobalTheory.Published.subsingleton_Hn_of_action_eq M.ρ (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)
        (fun _ _ => rfl) 3 (by omega) (h3 hl 3 le_rfl)⟩
  exact ⟨fun A _ M hM => ⟨(key A M hM).1, (key A M hM).2.1⟩,
    UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hM => (key A M hM).2.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArUr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arUr :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (u : (locOf r).St), UrAx l ((locOf r).Ju u) := by
  intro _ l _ L Ω _ _ _ _ _ _ s V0 _ O _ _ _ _ _ n r u
  exact UpperTheory.V.Pa.B2.urOf l _ _ (UpperTheory.V.Pa.unrLoc l L Ω s V0 O n r u)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArchH0Card
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.ge_real (hE : GlobalEulerChar) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F)))
    (hf : S.Finite) (hS : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (A : Type) [CommRing A] (M : FRep A (GS Ω S)) (hM : ∀ m : M.X, l • m = 0) :
    Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ F =
      Nat.card (H1 M.ρ) * ∏ w, Nat.card {m : M.X // M.ρ (toGS Ω S (c w)) m = m} := by
  classical
  obtain ⟨S, rfl⟩ := hf.exists_finset_coe
  letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
  obtain ⟨hρ, -, ⟨e1, -⟩, e2, -⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
  have h := hE F Ω l 1 M.X S (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos (fun v hv => hS v hv) hρ c fun w _ => hc w
  rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w] at h
  have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [c0, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  exact h

theorem UpperTheory.V.Pa.B2.arGE :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∃ c : Fin (Module.finrank ℚ (Lp L)) → (globOf r V).Γ, (∀ i, (globOf r V).η (c i) = -1 ∧ c i * c i = 1) ∧ ∀ (A : Type) [CommRing A] (M : FRep A (globOf r V).Γ), (∀ m : M.X, l • m = 0) → Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ (Lp L) = Nat.card (H1 M.ρ) * ∏ i, Nat.card {m : M.X // M.ρ (c i) m = m} := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Pa.ccEx l L Ω
  choose c hc using h1
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let e : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => toGS Ω V.S' (c (e i)), fun i => ?_, fun A _ M hM => ?_⟩
  · obtain ⟨j, hj, -⟩ := hc (e i)
    obtain ⟨a1, a2, -⟩ := h2 _ ⟨j, hj⟩
    refine ⟨(Int.units_eq_one_or (V.η (toGS Ω V.S' (c (e i))))).resolve_left fun h => a2 ((V.hη _).1 h), ?_⟩
    exact (map_mul (toGS Ω V.S') _ _).symm.trans (by rw [a1, map_one]; rfl)
  · have h := UpperTheory.V.Pa.B2.ge_real hP.ge (Lp L) Ω l V.S' V.fin (fun v hv => V.sub (Or.inl hv)) c hc A M hM
    rw [← Equiv.prod_comp e] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardOfAddEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.card_of_addEquiv {X Y : Type} {_ : Add X} {_ : Add Y} (e : X ≃+ Y) :
    Nat.card X = Nat.card Y ∧ (Finite Y → Finite X) :=
  ⟨Nat.card_congr e.toEquiv, fun _ => Finite.of_injective e e.injective⟩

theorem UpperTheory.V.Pa.B2.arLoc :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver B v → FinH l (Dec (F := F) B) ∧ SecondCohomologyRightExactModL l (Dec (F := F) B) ∧ ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocE l (Dec (F := F) B) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocE l (Dec (F := F) B) 0)) := by
  intro hP F Ω _ _ _ _ _ l _ B v hB
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (Dec (F := F) B)), (∀ m : M.X, l • m = 0) →
      (Finite (H1 M.ρ) ∧ Finite (H2 M.ρ)) ∧
      ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ locDeg v) ∧
       (((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ 0)) := by
    intro A _ M hl
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
    obtain ⟨hc, ⟨e0⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := scal A _ M (l ^ 1)
    have hf := hP.lf F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have he := hP.le F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e0).1
    have c1 : Nat.card (H1 M.ρ) = Nat.card (H1 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e1).1
    have c2 : Nat.card (H2 M.ρ) = Nat.card (H2 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e2).1
    rw [c0, c1, c2, pow_zero, mul_one]
    have f1 : Finite (H1 M.ρ) := (card_of_addEquiv e1).2 hf.2.1
    have f2 : Finite (H2 M.ρ) := (card_of_addEquiv e2).2 hf.2.2.1
    exact ⟨⟨f1, f2⟩, he⟩
  refine ⟨fun A _ M hl => (key A M hl).1, H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hl => ?_,
    fun h A _ M hl => (key A M hl).2.1 h, fun h A _ M hl => (key A M hl).2.2 h⟩
  exact (GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness hP.lf).of_nsmul l 1
    (fun m => by rw [pow_one]; exact hl m) M.ρ hB M.cont 3 le_rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ContOfKer
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem cont_of_ker {A Γ M : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation A Γ M)
    (hk : ∀ᶠ g in nhds (1 : Γ), ∀ m, ρ g m = m) : ContAction ρ := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, nhds_discrete M, Filter.tendsto_pure]
  have hg : ∀ᶠ g in nhds p.1, ∀ m, ρ g m = ρ p.1 m := by
    have ht : Filter.Tendsto (fun g => p.1⁻¹ * g) (nhds p.1) (nhds 1) := by
      simpa using (continuous_const_mul p.1⁻¹).tendsto p.1
    filter_upwards [ht.eventually hk] with g hg m
    calc ρ g m = ρ p.1 (ρ (p.1⁻¹ * g) m) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ p.1 m := by rw [hg m]
  have hm : ∀ᶠ q : Γ × M in nhds p, q.2 = p.2 := by
    have h0 : ∀ᶠ m in nhds p.2, m = p.2 := by
      rw [nhds_discrete, Filter.eventually_pure]
    exact (continuous_snd.tendsto p).eventually h0
  filter_upwards [(continuous_fst.tendsto p).eventually hg, hm] with q h1 h2
  rw [h1, h2]

private theorem ev_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) :
    ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g = 1 := by
  have key : ∀ a b : x.A, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries x.K) ^ m) a =
      Ideal.Quotient.mk _ b → algebraMap x.A X a = algebraMap x.A X b := by
    intro a b hab
    rw [Ideal.Quotient.eq, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hab
    obtain ⟨c, hc⟩ := hab
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hm, zero_mul]
  have hij : ∀ i j : Fin n, ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g i j = (1 : Matrix (Fin n) (Fin n) X) i j := by
    intro i j
    have hl := x.cont i j m
    filter_upwards [(hl.isOpen_fiber _).mem_nhds (Set.mem_singleton _)] with g hg
    have hg' := key _ _ hg
    simp only [NP.ρX, Matrix.map_apply]
    rw [hg']
    simp [mat, Matrix.one_apply]
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)] with g hg
  exact Matrix.ext hg

private theorem tri_X {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (g : F.Gv v) :
    (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v).BlockTriangular id := by
  intro i j hij
  have h := (x.tri v g).1 i j hij
  simp only [NP.wiX, NP.ρX, NP.wX, mat, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
  rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, ← Units.val_mul, ← Units.val_mul, h, map_zero]

private theorem w_wi {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  simp only [NP.wX, NP.wiX]
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

private def triSub {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ}
    (V : Submodule A (Matrix (Fin n) (Fin n) X)) (a b : Matrix (Fin n) (Fin n) X) : Submodule A V where
  carrier := {Z | (a * (Z : Matrix (Fin n) (Fin n) X) * b).BlockTriangular id}
  zero_mem' := by
    intro i j _
    simp
  add_mem' := by
    intro Z Z' h h' i j hij
    have e1 := h hij
    have e2 := h' hij
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, e1, e2, add_zero]
  smul_mem' := by
    intro c Z h i j hij
    have e1 := h hij
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, e1, smul_zero]

theorem UpperTheory.V.Pa.B2.odEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X], (∃ m : ℕ, algebraMap x.A X (x.t ^ m) = 0) → ∃ D : Dat x.A (plOf G), Nonempty (IsOd h x X D) := by
  intro l _ L G G0 h n x X _ _ _ hX
  obtain ⟨m, hm⟩ := hX
  obtain ⟨-, hok⟩ := okX l L G G0 h n x X 1
  obtain ⟨rep, hrep⟩ := adEx l G.frame x.A X n (fun g => x.ρX X (h.p₀ g))
    (fun g => algebraMap x.A X ((1 : G.Γ →* x.A) g)) (Od x.A X n x.a) hok
  have hact : ∀ (g : G.G₀) (Z : Od x.A X n x.a),
      ((rep g Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) =
        x.ρX X (h.p₀ g) * Z * x.ρX X (h.p₀ g⁻¹) := by
    intro g Z
    rw [hrep.1 g Z]
    simp
  have hc : ∀ Z : Od x.A X n x.a, ((rep G.c Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) = -(Z : Matrix (Fin n) (Fin n) X)ᵀ := by
    intro Z
    rw [hrep.2 Z]
    simp
  letI : TopologicalSpace (Od x.A X n x.a) := ⊥
  haveI : DiscreteTopology (Od x.A X n x.a) := ⟨rfl⟩
  haveI : Finite (Od x.A X n x.a) := inferInstance
  have hp : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hcont : ContAction rep := by
    apply cont_of_ker
    have E := ev_one x X m hm
    have E1 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g) = 1 := by
      have := (hp.tendsto 1).eventually (by simpa using E)
      exact this
    have E2 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g⁻¹) = 1 := by
      have ht : Filter.Tendsto (fun g : G.G₀ => g⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv.tendsto (1 : G.G₀))
      exact ht.eventually E1
    have E3 := E1.and E2
    rw [show (1 : G.G₀) = ⟨1, G.η.ker.one_mem⟩ from rfl, nhds_subtype_eq_comap, Filter.eventually_comap] at E3
    filter_upwards [E3, G.η_open.mem_nhds G.η.ker.one_mem] with g hg hker Z
    obtain ⟨h1, h2⟩ := hg ⟨g, hker⟩ rfl
    apply Subtype.ext
    have := hact ⟨g, hker⟩ Z
    rw [h1, h2, Matrix.one_mul, Matrix.mul_one] at this
    exact this
  let M : FRep x.A G.Γ := ⟨Od x.A X n x.a, rep, hcont⟩
  let N : (plOf G).ι → Submodule x.A M.X :=
    Sum.elim (fun v => triSub (Od x.A X n x.a) (x.wiX X v) (x.wX X v)) (fun _ => ⊥)
  have hN : ∀ (w : (plOf G).ι) (g : (plOf G).G w), N w ≤ Submodule.comap (M.ρ ((plOf G).φ w g)) (N w) := by
    intro w g
    cases w with
    | inl v =>
      change L.Gv v at g
      intro Z hZ
      have hZ' : (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id := hZ
      show (x.wiX X v * ((rep ((G.φ v g : G.G₀) : G.Γ) Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id
      have e1 : h.p₀ (G.φ v g) = G0.frame.φ v g := Subtype.ext (h.φ v g)
      have e2 : h.p₀ (G.φ v g)⁻¹ = G0.frame.φ v g⁻¹ := by
        rw [map_inv h.p₀, e1]
        exact (map_inv (G0.frame.φ v) g).symm
      rw [hact, e1, e2]
      have hww := w_wi x X v
      have heq : x.wiX X v * (x.ρX X (G0.frame.φ v g) * (Z : Matrix (Fin n) (Fin n) X) * x.ρX X (G0.frame.φ v g⁻¹)) * x.wX X v =
          (x.wiX X v * x.ρX X (G0.frame.φ v g) * x.wX X v) * (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v) *
            (x.wiX X v * x.ρX X (G0.frame.φ v g⁻¹) * x.wX X v) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul,
          ← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul]
      rw [heq]
      exact ((tri_X x X v g).mul hZ').mul (tri_X x X v g⁻¹)
    | inr u =>
      intro Z hZ
      have hZ0 : Z = 0 := (Submodule.mem_bot _).1 hZ
      simp [N, hZ0]
  refine ⟨Dat.ofSub (plOf G) M N hN, ⟨⟨LinearEquiv.refl _ _, fun g m => hact g m, fun m => hc m, ?_, ?_⟩⟩⟩
  · intro v m
    exact (Submodule.Quotient.mk_eq_zero (N (Sum.inl v)) (x := (m : M.X))).trans
      ⟨fun hb i j hij => hb hij, fun hb i j hij => hb i j hij⟩
  · intro u a b hab
    have hab' := (Submodule.Quotient.eq (N (Sum.inr u)) (x := (a : M.X)) (y := b)).1 hab
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hab')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.odKill_char (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] :
    (l : K) = 0 := by
  obtain ⟨q, hq⟩ := CharP.exists K
  haveI := hq
  have hx : (q : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite K q)
  have h1 := congrArg (algebraMap ℤ_[l] K) (PadicInt.unitCoeff_spec hx)
  rw [map_natCast, CharP.cast_eq_zero, map_mul, map_pow, map_natCast] at h1
  have hu : algebraMap ℤ_[l] K (PadicInt.unitCoeff hx : ℤ_[l]) ≠ 0 :=
    ((PadicInt.unitCoeff hx).isUnit.map (algebraMap ℤ_[l] K)).ne_zero
  exact pow_eq_zero_iff'.mp ((mul_eq_zero.mp h1.symm).resolve_left hu) |>.1

theorem UpperTheory.V.Pa.B2.odKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (D : Dat x.A (plOf G)), IsOd h x X D → (∀ m : D.M.X, l • m = 0) ∧ (∀ w, ∀ m : (D.Q w).X, l • m = 0) ∧ ∀ u, ∀ g ∈ L.Ju u, ∀ m : (D.Q (inU G u)).X, (D.Q (inU G u)).ρ g m = m := by
  intro l _ L G G0 h n x X _ _ D hD
  have hlA : (l : x.A) = 0 := by
    show (l : PowerSeries x.K) = 0
    rw [← map_natCast (algebraMap x.K (PowerSeries x.K)) l, odKill_char l x.K, map_zero]
  refine ⟨fun m => ?_, fun w m => ?_, fun u g hg m => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · obtain ⟨m', rfl⟩ := D.surj (inU G u) m
    refine (D.equiv (inU G u) g m').symm.trans ?_
    congr 1
    let g' : G.G₀ := G.φu u g
    have hp : h.p₀ g' = G0.φu u g := Subtype.ext (by exact h.φu u g)
    have hmem : h.p₀ g' ∈ G0.frame.Iu u := by
      rw [hp]
      exact Subgroup.mem_map_of_mem _ hg
    have h1 : x.ρ (h.p₀ g') = 1 := x.ine u _ hmem
    have h2 : x.ρ (h.p₀ g'⁻¹) = 1 := by rw [map_inv h.p₀, map_inv x.ρ, h1, inv_one]
    apply hD.e.injective
    apply Subtype.ext
    show ((hD.e (D.M.ρ (g' : G.Γ) m')) : Matrix (Fin n) (Fin n) X) = hD.e m'
    rw [hD.act g' m']
    show ((x.ρ (h.p₀ g') : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * _ *
      ((x.ρ (h.p₀ g'⁻¹) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) = _
    rw [h1, h2, Units.val_one]
    simp
end

