module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.GwCntBare

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DescendO
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def zeroSub {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) : Subgroup Γ where
  carrier := {g | y g = 0}
  one_mem' := by simpa using hy.2 1 1
  mul_mem' := by
    intro a b ha hb
    have ha' : y a = 0 := ha
    have hb' : y b = 0 := hb
    show y (a * b) = 0
    rw [hy.2, ha', hb', map_zero, add_zero]
  inv_mem' := by
    intro a ha
    have ha' : y a = 0 := ha
    have y1 : y 1 = 0 := by simpa using hy.2 1 1
    have h := hy.2 a⁻¹ a
    rw [inv_mul_cancel, y1, ha', map_zero, add_zero] at h
    exact h.symm

private theorem conj_zero {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) (t g : Γ) (ht : ρ t = 1)
    (h0 : y t = 0) : y (g * t * g⁻¹) = 0 := by
  have y1 : y 1 = 0 := by simpa using hy.2 1 1
  have h := hy.2 g g⁻¹
  rw [mul_inv_cancel, y1] at h
  rw [hy.2, hy.2, h0, map_zero, add_zero, map_mul, ht, mul_one]
  exact h.symm

private theorem factor_lc {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [T2Space Γ'] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)
    (y : Γ → M) (hy : y ∈ Zl ρ) (p : Γ →* Γ') (hc : Continuous p) (hs : Function.Surjective p)
    (hk : ∀ g ∈ p.ker, y g = 0) : ∃ Z : Γ' → M, IsLocallyConstant Z ∧ ∀ g, y g = Z (p g) := by
  have e : ∀ g, y g = y (Function.surjInv hs (p g)) := by
    intro g
    have : g⁻¹ * Function.surjInv hs (p g) ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel]
    have h := hy.2 g (g⁻¹ * Function.surjInv hs (p g))
    rw [hk _ this, map_zero, add_zero, mul_inv_cancel_left] at h
    exact h.symm
  refine ⟨fun γ => y (Function.surjInv hs γ), fun s => ?_, e⟩
  have hq : Topology.IsQuotientMap p := hc.isClosedMap.isQuotientMap hc hs
  rw [← hq.isOpen_preimage]
  convert hy.1 s using 1
  ext g
  simp only [Set.mem_preimage, ← e g]

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] (n m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.descendO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m N : ℕ) (rep' : Representation O (T.GN N).Γ (Mm O n m)), G0.ε G0.c = -1 → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → IsAd1 (T.h N) y m rep' → ∀ z' ∈ Zl rep', z' (T.GN N).c = 0 → (∀ j, z' (T.ta N j) = 0) → ∃ z ∈ Tw y m, ∀ g : (T.GN N).G₀, z' g = z ((T.h N).p₀ g) := by
  intro l _ L G0 T O _ _ _ _ _ n y m N rep' hεc hPL had z' hz hc hta
  have heps : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    unfold epsm
    rw [(T.h N).ε]
  have hcoc : ∀ g g' : (T.GN N).G₀, z' ((g * g' : (T.GN N).G₀) : (T.GN N).Γ) =
      z' g + epsm O (T.GN N) m g • (y.ρm (T.h N) m g * z' g' * y.ρm (T.h N) m g⁻¹) := fun g g' => by
    have e := hz.2 g g'
    rw [had.1 g] at e
    exact e
  have htriv : ∀ j, rep' (T.ta N j) = 1 := by
    intro j
    have h1 : (T.h N).p₀ (T.ta N j) = 1 := Subtype.ext (T.ta_ker N j)
    have h2 : y.ρm (T.h N) m (T.ta N j) = 1 := by
      unfold Pt.ρm
      rw [h1]
      simp [mat, red_one]
    have h3 : y.ρm (T.h N) m (T.ta N j)⁻¹ = 1 := by
      unfold Pt.ρm
      rw [map_inv, h1, inv_one]
      simp [mat, red_one]
    have h4 : epsm O (T.GN N) m (T.ta N j) = 1 := by
      rw [heps, T.ta_ker]
      simp [epsm]
    refine LinearMap.ext fun Z => (had.1 _ Z).trans ?_
    rw [h2, h3, h4, one_smul, one_mul, mul_one]
    rfl
  have hker : (T.h N).p.ker ≤ zeroSub rep' z' hz := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (hz.1.isClosed_fiber 0))
    · refine (Subgroup.closure_le _).2 fun a ha => ?_
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Group.mem_conjugatesOfSet_iff.1 ha
      obtain ⟨g, rfl⟩ := isConj_iff.1 hj
      exact conj_zero rep' z' hz _ g (htriv j) (hta j)
    · intro a ha
      have hη : a ∈ (T.GN N).η.ker := by
        have ha' := ha
        simp only [PL, Subgroup.mem_iInf] at ha'
        exact ha' ⟨⟨(T.GN N).η.ker, (T.GN N).η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
          ⟨0, by
            rw [pow_zero, pow_one]
            show (T.GN N).η h = 1
            rw [← (T.h N).η]
            exact T.H_η _ hh⟩
      exact (plKill l L G0 T O n y m (T.GN N) (T.h N) hPL (fun g => z' g)
        (hz.1.comp_continuous continuous_subtype_val) hcoc ⟨a, hη⟩ ha).1
  obtain ⟨Z, z1, z2⟩ := factor_lc rep' z' hz (T.h N).p (T.h N).cont (T.h N).surj fun g hg => hker hg
  have hs : ∀ g0 : G0.G₀, ∃ g : (T.GN N).G₀, (T.h N).p₀ g = g0 := by
    intro g0
    obtain ⟨g, hg⟩ := (T.h N).surj g0
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [MonoidHom.mem_ker, ← (T.h N).η, hg]
    exact g0.2
  have z3 : ∀ g : (T.GN N).G₀, Z ((T.h N).p₀ g : G0.G₀) = z' g := fun g => (z2 g).symm
  refine ⟨fun g0 => Z g0, ⟨z1.comp_continuous continuous_subtype_val, fun g0 h0 => ?_, fun g0 => ?_⟩,
    fun g => by rw [← z3]⟩
  · obtain ⟨g, rfl⟩ := hs g0
    obtain ⟨h, rfl⟩ := hs h0
    have e := hcoc g h
    rw [heps] at e
    simp only []
    rw [← map_mul, z3, z3, z3, ← map_inv]
    exact e
  · obtain ⟨g, rfl⟩ := hs g0
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      (Units.isUnit y.P).map (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix
    have e := ((polP l (T.GN N).frame O _ n _ _ _ rep' hP had).2 z' hz hc).1 g
    have e2 : G0.frame.conj ((T.h N).p₀ g) = (T.h N).p₀ ((T.GN N).frame.conj g) := by
      refine Subtype.ext ?_
      show G0.c * (T.h N).p g * G0.c⁻¹ = (T.h N).p ((T.GN N).c * g * (T.GN N).c⁻¹)
      rw [map_mul, map_mul, map_inv, (T.h N).c]
    have e3 : epsm O (T.GN N) m (T.GN N).c = -1 := by
      rw [heps, (T.h N).c]
      simp [epsm, hεc]
    simp only []
    rw [e2, z3, z3]
    refine e.trans ?_
    show -(epsm O (T.GN N) m (T.GN N).c • _) = _
    rw [e3, neg_smul, neg_neg, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinTwO
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem phiCond_of_isOpen_subgroup {Γ : Type} [Group Γ] [TopologicalSpace Γ] (l : ℕ) (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : PhiCond Γ l) : PhiCond K l := by
  intro H hH
  let H' : Subgroup Γ := H.map K.subtype
  have hH' : IsOpen (H' : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ hH
  haveI := h H' hH'
  let e : H ≃* H' := H.equivMapOfInjective K.subtype K.subtype_injective
  have hEq : ∀ x : H', (((e.symm x : K) : Γ)) = (x : Γ) := fun x => by
    conv_rhs => rw [← e.apply_symm_apply x]
    rfl
  have hc : Continuous (fun x : H' => e.symm x) := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.congr (fun x => (hEq x).symm)
  refine Finite.of_injective
    (fun φ : {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H)} =>
      (⟨φ.1.comp e.symm.toMonoidHom, by
        rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
        exact φ.2.preimage hc⟩ :
        {ψ : H' →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set H')})) ?_
  intro φ ψ hφψ
  apply Subtype.ext
  ext y
  have := DFunLike.congr_fun (congrArg Subtype.val hφψ) (e y)
  simpa using this

theorem UpperTheory.V.Th.finTwO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), PhiCond G0.Γ l → (Tw y m).Finite := by
  intro l _ L G0 O _ _ _ _ _ n y m hphi
  classical
  obtain ⟨-, hom⟩ := omFacts l O
  obtain ⟨hfin, -, hkill, -, -⟩ := hom m
  obtain ⟨-, ⟨rep, hrep⟩, hlc⟩ := adExP l L G0 G0 (Glob.Hom.refl G0) O n y m
  have hLC := hlc rep (Or.inr hrep)
  have hKo : IsOpen (G0.η.ker : Set G0.Γ) := G0.η_open
  have hKc : IsClosed (G0.η.ker : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  let rep0 : Representation O G0.G₀ (Mm O n m) := rep.comp G0.η.ker.subtype
  have hLC0 : LC rep0 := fun Z => (hLC Z).comp_continuous continuous_subtype_val
  have hphi0 : PhiCond G0.G₀ l := phiCond_of_isOpen_subgroup l G0.η.ker hKo hphi
  haveI : Finite (Om O m) := hfin
  have hZ := finZK l m O G0.G₀ (Mm O n m) rep0 hphi0 hLC0
    (fun Z => by
      ext i j
      simpa using hkill (Z i j))
  refine Set.Finite.subset (Set.finite_coe_iff.mp hZ) ?_
  rintro z ⟨hz1, hz2, -⟩
  refine ⟨hz1, fun g h => ?_⟩
  rw [hz2 g h]
  congr 1
  exact (hrep.1 g (z h)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocSup
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem up_mul {R : Type} [CommRing R] {n : ℕ} {P Q : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j, j < i → P i j = 0) (hQ : ∀ i j, j < i → Q i j = 0) : ∀ i j, j < i → (P * Q) i j = 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hP i c hc, zero_mul]
  · rw [hQ c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem up_conj {R : Type} [CommRing R] {n : ℕ} {w wi r s y : Matrix (Fin n) (Fin n) R}
    (h2 : w * wi = 1)
    (hr : ∀ i j, j < i → (wi * r * w) i j = 0) (hs : ∀ i j, j < i → (wi * s * w) i j = 0)
    (hy : ∀ i j, j < i → (wi * y * w) i j = 0) :
    ∀ i j, j < i → (wi * (r * y * s - y) * w) i j = 0 := by
  have e : wi * (r * y * s - y) * w = (wi * r * w) * (wi * y * w) * (wi * s * w) - wi * y * w := by
    calc wi * (r * y * s - y) * w = wi * r * (w * wi) * y * (w * wi) * s * w - wi * y * w := by
          rw [h2]; noncomm_ring
      _ = _ := by noncomm_ring
  intro i j h
  rw [e, Matrix.sub_apply, up_mul (up_mul hr hy) hs i j h, hy i j h, sub_zero]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem UpperTheory.V.Th.locSup :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)) (v : L.Vl), IsAd0 h y m rep → LC rep → Finite (Zbor y m v) → ((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v ≤ (Zl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup) ∧ Finite ↥((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ Nat.card ↥((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) * Nat.card (ResidueField O) ^ (m * (n + n.choose 2)) ≤ Nat.card (Mm O n m) * Nat.card (Zbor y m v) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep v hrep hLC hZ
  haveI : Finite (Om O m) := ((omFacts l O).2 m).1
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  have hpφ : ∀ g, h.p₀ (G.φ v g) = G0.φ v g := fun g => Subtype.ext (h.φ v g)
  have hv : ∀ (g : L.Gv v) (Z : Mm O n m), rep (G.φ v g : G.Γ) Z =
      y.ρ0 m (G0.φ v g) * Z * y.ρ0 m (G0.φ v g)⁻¹ := fun g Z => by
    have := hrep.1 (G.φ v g) Z
    simp only [one_smul, Pt.ρm, map_inv, hpφ] at this
    exact this
  have hLCv : LC (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _) := fun Z =>
    (hLC Z).comp_continuous (continuous_subtype_val.comp (G.φ_cont v))
  have hle := block_le₂ _ hLCv
  refine ⟨sup_le hle fun β hβ => ⟨hβ.1, fun g g' => ?_⟩, ?_⟩
  · exact (hβ.2.1 g g').trans (congrArg (_ + ·) (hv g (β g')).symm)
  · rw [← borCard l L G0 O n y m v]
    refine sumCount O (L.Gv v) _ _ (bor y m v) (Zbor y m v) hZ fun Y hY => ?_
    have hmem := hle (show (fun g => (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _) g Y - Y) ∈ _ from
      (mem_Bl _).2 ⟨Y, fun _ => rfl⟩)
    have hw : red m (y.w v : Matrix (Fin n) (Fin n) O) *
        red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have t : ∀ (g : L.Gv v) i j, j < i → (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) *
        y.ρ0 m (G0.φ v g) * red m (y.w v : Matrix (Fin n) (Fin n) O) : Mm O n m) i j = 0 := fun g i j hij => by
      have := congrArg (Ideal.Quotient.mk (maximalIdeal O ^ m)) ((y.tri v g).1 i j hij)
      rw [map_zero] at this
      rw [Pt.ρ0, ← red_mul, ← red_mul]
      exact this
    refine ⟨hmem.1, fun g g' => ?_, fun g i j hij => ?_⟩
    · exact (hmem.2 g g').trans (congrArg (_ + ·) (hv g _))
    · have := up_conj hw (t g) (by have := t g⁻¹; rwa [map_inv] at this) hY i j hij
      rw [← hv g Y] at this
      exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneCntO
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def chRep {A D : Type} (M : Type) [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ) :
    Representation A D M where
  toFun g := (χ g : A) • LinearMap.id
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp [smul_smul, mul_comm]

private theorem chRep_apply {A D M : Type} [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ)
    (g : D) (y : M) : chRep M χ g y = (χ g : A) • y := rfl

private theorem ker_le {A : Type} [CommRing A] (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] (a : A)
    (h : J ≤ Ideal.span {a}) (S : Submodule A (A ⧸ I)) (hS : ∀ y ∈ S, a • y = 0) :
    Nat.card S ≤ Nat.card (A ⧸ J) := by
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := a • LinearMap.id
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at h1
  have h3 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := LinearMap.range f))
    rw [← h2, mul_comm, ← h1]
  have h4 : Nat.card S ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective _ (Submodule.inclusion_injective (show S ≤ LinearMap.ker f from hS))
  let p : A →ₗ[A] ((A ⧸ I) ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.comp (Submodule.mkQ I)
  have hp : J ≤ LinearMap.ker p := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 (h hy)
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.mkQ I c, ?_⟩
    exact (map_smul (Submodule.mkQ I) a c).symm
  have hs : Function.Surjective (Submodule.liftQ J p hp) := by
    intro y
    obtain ⟨c, rfl⟩ := ((Submodule.mkQ_surjective (LinearMap.range f)).comp (Submodule.mkQ_surjective I)) y
    exact ⟨Submodule.mkQ J c, rfl⟩
  exact h4.trans (h3.le.trans (Nat.card_le_card_of_surjective _ hs))

theorem UpperTheory.V.Th.oneCntO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) (χ : D →* Oˣ), LocCnt D ε d → AdicCont (maximalIdeal O) (fun g => (χ g : O)) → (∃ g, (χ g : O) ≠ algebraMap ℤ_[l] O (ε g : ℤ_[l])) → ∃ C : ℕ, ∀ m, {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.Finite ∧ {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
  intro l _ O _ _ _ _ _ D _ _ _ ε d χ hL hχ ⟨g₀, hg₀⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨C, hC⟩ := IsDiscreteValuationRing.associated_pow_irreducible (sub_ne_zero.2 hg₀) hϖ
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, hcard, -, -, hlc⟩ := (omFacts l O).2 m
  obtain ⟨hfinC, hcardC, -⟩ := (omFacts l O).2 C
  obtain ⟨k, τ, hk, hτ, hlin⟩ := pairO l O m
  let e : D →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ε
  have he : ∀ g, (e g : O) = algebraMap ℤ_[l] O (ε g : ℤ_[l]) := fun _ => rfl
  let χ' : D →* Oˣ := e * χ⁻¹
  have hχ' : ∀ g, (χ g : O) * χ' g = e g := fun g => by
    rw [← Units.val_mul]
    congr 1
    simp [χ']
  let b : Om O m →+ Om O m →+ ZMod (l ^ k) := (AddMonoidHom.mul (R := Om O m)).compr₂ τ
  have hb : ∀ y z, b y z = τ (y * z) := fun _ _ => rfl
  have hLC : LC (chRep (Om O m) χ) := fun y =>
    (hlc D _ hχ).comp (fun u => u * y)
  have hD : DualPair k ε (chRep (Om O m) χ) (chRep (Om O m) χ') b :=
    { left := fun y h => hτ y h
      right := fun y h => hτ y fun z => by rw [mul_comm]; exact h z
      equiv := fun g y z => by
        rw [hb, hb, chRep_apply, chRep_apply, smul_mul_smul_comm, hχ', he, Algebra.smul_def, hlin] }
  obtain ⟨hf, hc⟩ := hL k hk O (Om O m) (Om O m) _ _ b hLC hD
  have hinv : Nat.card (chRep (Om O m) χ').invariants ≤ Nat.card (Om O C) := by
    refine ker_le _ _ ((χ g₀ : O) - algebraMap ℤ_[l] O (ε g₀ : ℤ_[l])) ?_ _ fun y hy => ?_
    · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 hC.dvd)
    · have h1 : (χ' g₀ : O) • y = y := hy g₀
      rw [← he, ← hχ', sub_smul, mul_smul, h1, sub_self]
  refine ⟨hf, ?_⟩
  have h2 : {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard =
      Nat.card (Zl (chRep (Om O m) χ)) := rfl
  rw [h2, hc, hcard, ← pow_mul, pow_add, ← hcardC]
  exact Nat.mul_le_mul_left _ hinv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PresCnts
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.presCnts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → Cnts a := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  have hmatch : ∀ (w : ArData.W Lc q) (g : a.D w),
      G.ε (a.ι w g) = cycZ F Ω l ((Dec (P.A w)).subtype (P.α w g)) := by
    intro w g
    exact (congrArg G.ε (P.ι_eq w g)).trans (P.e_ε _)
  refine Cnts.mk ?_ ?_ ?_ ?_
  · have key := gwCntBare hC.gw hC.lt hC.gf hC.lf l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A
      a.D a.ι P.α d P.ip P.c hl P.above P.e_ε P.isOver P.ι_eq P.cc
    have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
    rw [hcw]
    exact key
  · intro v
    have hv : (l : 𝓞 F) ∈ (P.pl (Sum.inl v) : HeightOneSpectrum (𝓞 F)).asIdeal := (P.pl_l _).2 ⟨v, rfl⟩
    have h1 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inl v)) _ (P.isOver (Sum.inl v))).1 hv
    rw [P.dv_eq v]
    exact locCntCongr l (a.D (Sum.inl v)) _ (P.α (Sum.inl v)) _ _ _ (hmatch (Sum.inl v)) h1
  · intro j
    have hn : (l : 𝓞 F) ∉ (P.pl (Sum.inr (Sum.inr j)) : HeightOneSpectrum (𝓞 F)).asIdeal := by
      intro hm
      obtain ⟨v, hv⟩ := (P.pl_l _).1 hm
      cases hv
    have h0 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inr (Sum.inr j))) _
      (P.isOver (Sum.inr (Sum.inr j)))).2 hn
    exact locCntCongr l (a.D (Sum.inr (Sum.inr j))) _ (P.α (Sum.inr (Sum.inr j))) _ _ _
      (hmatch (Sum.inr (Sum.inr j))) h0
  · intro u
    exact unrDev l _ _ (hU u)
end

