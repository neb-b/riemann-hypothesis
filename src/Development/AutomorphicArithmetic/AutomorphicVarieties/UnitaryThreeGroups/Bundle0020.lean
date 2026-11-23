module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LocPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelOfPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RootOfCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanCocIsBK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelLower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (ReciprocityTheory.Gal.H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (ReciprocityTheory.Gal.Z1 (permR (ZMod n) H)) := by
    have hB : Finite (ReciprocityTheory.Gal.B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((ReciprocityTheory.Gal.B1 (permR (ZMod n) H)).comap
        (ReciprocityTheory.Gal.Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : ReciprocityTheory.Gal.B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → ReciprocityTheory.Gal.Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

private theorem phi_surj {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (π : Γ →* Δ)
    (hc : Continuous π) (hπ : Function.Surjective π) {l : ℕ} (h : PhiCond Γ l) : PhiCond Δ l := fun H hH => by
  haveI := h (H.comap π) (hH.preimage hc)
  let p : H.comap π →* H := π.subgroupComap H
  have hp : Continuous p := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective p := MonoidHom.subgroupComap_surjective_of_surjective _ _ hπ
  refine Finite.of_injective
    (β := {φ : H.comap π →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set (H.comap π))})
    (fun φ => ⟨φ.1.comp p, φ.2.preimage hp⟩) fun φ φ' e => ?_
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem fin_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]; exact hv

private theorem phi_kill (hGF : GlobalFiniteness) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type}
    [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ}
    {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (M : Subgroup (G ℚ Ω)) [M.Normal]
    (hM : M = (Subgroup.normalClosure D.Kill).topologicalClosure) : PhiCond (G ℚ Ω ⧸ M) l := by
  subst hM
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hK, -⟩ := dat_facts D
  obtain ⟨⟨T, hT⟩, -⟩ := ramFinite ℚ ℚ K Ω
  obtain ⟨-, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω N
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  classical
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := T ∪ (fin_above hlN).toFinset
  have hS1 : ∀ v, ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := fun v hv =>
    Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hv)
  have hS : ContainsAbove S l := fun v hv => hS1 v (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  have hval : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ∀ n : ℕ,
      A.valuation (n : Ω) < 1 → ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hv n hn
    have h := hv ((n : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e] at h
    exact h.1 hn
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ (Subgroup.normalClosure D.Kill).topologicalClosure := by
    refine Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono ?_)
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    have hv' : ((l * N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hS1 v h)
    rw [Nat.cast_mul] at hv'
    refine (hK g).2 ⟨A, fun h => hv' (v.asIdeal.mul_mem_right _ (hval A v hA l h)), hg, ?_, ?_⟩
    · have h1 : g ∈ galOf ℚ K Ω := hT v (fun h => hv (Finset.mem_union_left _ h)) A hA
        ⟨by rw [galOf_self]; trivial, hg⟩
      rwa [← D.η_ker] at h1
    · have h1 : Chr.cls ℚ Ω N g = 1 := hIne A (fun h => hv' (v.asIdeal.mul_mem_left _ (hval A v hA N h))) hg
      rw [Chr.dirG, MonoidHom.comp_apply, h1, map_one]
  haveI hc : CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) :=
    phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
      obtain ⟨-, f1, -⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
      exact f1
  rw [pow_one] at key
  refine phi_surj (QuotientGroup.lift (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (QuotientGroup.mk' _)
    fun g hg => (QuotientGroup.eq_one_iff g).2 (hNS hg)) ?_ ?_ key
  · exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_quotient_mk'
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem UpperTheory.V.U3.exists_model :
    CohInp → LemmaP → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), Nonempty (Model S (PadicAlgCl l)) := by
  intro hC hP Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hg S
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨-, -, -, hη, hΨ, hK, -⟩ := dat_facts D
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have hL : LocGood U (D.loc.It U) := Loc.locGood hC.loc D.loc U
  have hcont : ∀ j : ℤ, AdicCont (maximalIdeal c.O) fun g => ((D.Ψ g ^ j : (c.O)ˣ) : c.O) := D.Ψ_cont
  haveI := Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure D.Kill)
  have hV := exists_univ l D.η D.Ψ hη hΨ D.Kill (fun g h => h.choose_spec.2.2) _ rfl (phi_kill hC.gf D _ rfl)
  obtain ⟨⟨B⟩, -⟩ := exists_sRing D.ι_cont U (D.loc.It U) D.cc g₁ hg hL hcont hK hV
  obtain ⟨WB, hWB⟩ := exists_locPres U (D.loc.It U) (hη.comp_continuous D.ι_cont) hL
  exact model_of_pres S B WB D.gd.l_odd hg hL hcont hK hWB (boxPres hC hP D U B WB hWB)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtHypOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
      IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R).map f = tor S (Units.map f.toMonoidHom (Ψ g))
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) (Ψ g) (wt1 i))

private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨-m, funext fun g => ?_⟩
  show adRep r g m - m = -m - adRep r g (-m)
  rw [map_neg]
  abel

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) :
    IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.VlenLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem first_cohomology_torsion {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : Γ →* Oˣ) (x : H1U (twist₂ l α) (⊤ : Subgroup Γ)) : ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
  classical
  choose k hk0 hk using (UpperTheory.V.ML.qoCyc l O).1
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc : IsLocallyConstant fun g : Γ => z.1 ⟨g, trivial⟩ :=
    (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_id.subtype_mk _))
  have hfin := hc.range_finite
  refine ⟨∏ w ∈ hfin.toFinset, k w, Finset.prod_ne_zero_iff.2 fun w _ => hk0 w, ?_⟩
  have hz : (∏ w ∈ hfin.toFinset, k w) • z = 0 := Subtype.ext (funext fun g =>
    (hk _ _).2 (Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 ⟨g.1, rfl⟩)))
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]

private theorem len_of_torsion (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : ∀ x : M, ∃ a : O, a ≠ 0 ∧ a • x = 0) (n : ℕ∞)
    (hn : ∀ b : O, b ≠ 0 → Module.length O (Submodule.torsionBy O M b) ≤ n) : Module.length O M ≤ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [← Module.length_top]
  refine Kum.lenDirected O _ _ (fun k => Submodule.torsionBy O M (ϖ ^ k)) n ?_ ?_
    fun k => ⟨k, le_rfl, hn _ (pow_ne_zero _ hϖ.ne_zero)⟩
  · intro i j hij
    exact Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ hij)
  · intro x _
    obtain ⟨a, ha, hx⟩ := h x
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
    exact Submodule.mem_iSup_of_mem k (Submodule.torsionBy_le_torsionBy_of_dvd _ _ hk.dvd
      ((Submodule.mem_torsionBy_iff _ _).2 hx))

private theorem vs_le {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (m e : ℕ) (θ : G ℚ Ω →* Oˣ) (n : ℕ∞)
    (hn : ∀ b : O, b ≠ 0 → Module.length O (Submodule.torsionBy O (ShaU (Chr.rho l e θ) m ⊤) b) ≤ n) :
    Chr.VS l m e θ ≤ n := by
  refine len_of_torsion O _ (fun x => ?_) _ hn
  obtain ⟨a, ha, hx⟩ := first_cohomology_torsion l O _ x.1
  exact ⟨a, ha, Subtype.ext hx⟩

theorem UpperTheory.V.U3.vlen_le :
    CohInp → LemmaM' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ M : Model S (PadicAlgCl l), Vlen Ω c e ψ ≤ M.len := by
  intro hC hM' Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg S M
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  obtain ⟨-, -, -, -, -, hK, h2, -⟩ := dat_facts D
  have hG : LocGood U (D.loc.It U) := Loc.locGood hC.loc D.loc U
  refine vs_le l c.O (l * N) e (Chr.dirG ℚ Ω ψ) _ fun b hb => ?_
  have h := sha_inj D g₁ hg b hb
  refine h.elim fun a h => h.2.elim fun γ hγ => ?_
  set_option synthInstance.maxHeartbeats 400000 in
    exact model_lower S M h2 hg hM' hG D.Ψ_cont hK a h.1 _ γ hγ.1 hγ.2
end

