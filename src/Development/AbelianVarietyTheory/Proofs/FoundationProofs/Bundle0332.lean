module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
open Matrix

noncomputable section

namespace GlobalTheory.DefU.FinCompact

theorem exists_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ n
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (finU (E := E) (n := n)) := U0.comap p
  have hKo : IsOpen (K : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, hx, ?_⟩⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.DefU.FinCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryForm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU

theorem finiteDimensional_vecForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let T : M →ₗ[ℂ] (S₀ → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    obtain ⟨hl, hr, hk⟩ := hM f.1 f.2
    have h0 : ∀ s ∈ S₀, ∀ v, f.1 v s = 0 := fun s hs v => LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    apply Subtype.ext
    refine LinearMap.ext fun v => funext fun g => ?_
    obtain ⟨γ, hγ, s, hs, x, hx, k, hkK, rfl⟩ := hS₀ g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := by
      have := congrFun (hk k hkK v) (γ * s * x)
      rw [← this]; rfl
    have e3 : f.1 v (s * x) = f.1 (ρ ⟨x, hx⟩ v) s := by
      rw [hr ⟨x, hx⟩ v]; rfl
    rw [e1, mul_assoc γ s x, hl v γ hγ, e3, h0 s hs]
    rfl
  exact Module.Finite.of_injective T hT

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Host

variable (D : D7) (H : Geo.Tor.Host D.host.E)

theorem isAbelianGalois_host : IsAbelianGalois ℚ D.host.E := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have : IsMulCommutative Gal(D.host.E/ℚ) := ⟨⟨fun σ τ => hbij.1 (by rw [hmul, hmul, _root_.mul_comm])⟩⟩
  exact {}

theorem not_cube_dvd (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ¬ w.asIdeal ^ 3 ∣ Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have hp := D.host.hyp.2.1
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := w.isPrime
  have hmax : (Ideal.span {(D.host.d : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have : w.asIdeal.LiesOver (Ideal.span {(D.host.d : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simpa using hw)⟩
  have hb : (Ideal.span {(D.host.d : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have hIn : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) =
        Nat.card ({1, D.R.toFrame.iod} : Set (D.R.GG)) :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) fun σ => by
        rw [AddSubgroup.mem_inertia]
        exact D.host.der.inertia_d w.asIdeal σ)
    rw [e, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    have := congrArg (fun g : D.R.GG => g.1.2) h
    exact absurd (show (1 : ℤˣ) = -1 from this) (by decide)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(D.host.d : ℤ)}) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(D.host.d : ℤ)}) w.asIdeal hb] at hIn
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 D.host.E)) (Ideal.span {(D.host.d : ℤ)}) =
      Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity (by rw [hm]; simpa using hp.ne_zero) w.isPrime, hm] at hIn
  have hf : FiniteMultiplicity w.asIdeal (Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)}) := by
    by_contra hn
    rw [multiplicity_eq_one_of_not_finiteMultiplicity hn] at hIn
    omega
  have := hf.le_multiplicity_of_pow_dvd h
  omega

theorem isHostField (hd : H.d = D.host.d) : EigenvectorLieDegree.IsHostField H := by
  have hA := isAbelianGalois_host D
  obtain ⟨-, -, hdisc, hmov⟩ := PlaceInt.host_galois_discr_moves D H
  refine (HostRamif.isHostField_iff _ H).2 ⟨hA, fun l w hl hdv hw hlw => ?_⟩
  have h1 : l ∣ D.host.condN := hdisc l hl hdv
  have h2 : l ∈ D.host.small ∨ l = D.host.q ∨ l = D.host.d := (D.host.toHostRaw.dvd_condN_iff_small hl).1 h1
  refine ⟨fun h => ?_, fun h => (HostRamif.isSquare_iff H hl hw hlw h).1 ?_, fun h h3 => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (hmov l (Nat.mem_primeFactors.2 ⟨hl, h1, D.host.toHostRaw.condN_ne_zero⟩)).2 w hw.isPrime hlw
    exact hx' (h ▸ Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hx)
  · rcases h2 with h2 | rfl | h2
    · by_cases e2 : l = 2
      · subst e2
        exact FiniteField.isSquare_of_char_two (ZMod.ringChar_zmod_n 2) _
      · have := Fact.mk hl
        have := ZMod.isSquare_of_jacobiSym_eq_one
          (D.host.QS_split l hl e2 ((D.host.toHostRaw.mem_small_iff).1 h2).2)
        rw [hd]
        simpa using this
    · have := Fact.mk hl
      have := ZMod.isSquare_of_jacobiSym_eq_one D.host.hyp.2.2.2.2
      rw [hd]
      simpa using this
    · exact absurd (h2.trans hd.symm) h
  · obtain rfl : l = D.host.d := h.trans hd
    have hb : w ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hlw
      exact hl.ne_zero (by exact_mod_cast hlw)
    exact not_cube_dvd D ⟨w, hw.isPrime, hb⟩ hlw (Ideal.dvd_span_singleton.2 h3)

end Host

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_eigenBasis {S : Scheme.{0}} {T : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {t : SAB H (Sp R)}
    (n : SABMap t T x) {χ : 𝓞 E →+* R} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)} (hv : EigenvectorLieDegree.IsEigBasis t.act χ v) :
    ∃ u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G), FramedFlatCoordinates.IsEigenBasis T.act x χ u ∧ ∀ i, (v i).left ≫ n.φ = (u i).left := by
  have h := n.cart
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  have one : (1 : Over.mk x ⟶ T.G).left = η[t.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ t.G), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have hP : ∀ v : epsR R ⟶ t.G, EigenvectorLieDegree.IsEigVec t.act χ v ↔ FramedFlatCoordinates.IsEigenTangent T.act x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[t.G]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ t.act.act c) = e v ≫ T.act.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, n.act, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin m → (epsR R ⟶ t.G), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine ⟨fun i => e (v i), ⟨fun i => (hP _).1 (hv.1 i), fun w hw => ?_⟩, fun i => (he _).symm⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (hv.2 w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

variable {Y : Model Xo c β} {Xc : (Xo.XF c).Opens} {τ : E →+* ℂ}

end Point

section Record

variable {D : D7} (large₂ : SizeData₂ D) {X : DivX D} (Lc : placeRankTwoOne.Loc D X)

end Record

end GlobalTheory.FlatRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.EquivCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {X : Type} [AddCommGroup X] [Module ℂ X]

def coefL (R : UA E n →* Module.End ℂ X) (F : UA E n → X) : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) where
  toFun μ := fun g => μ (R g⁻¹ (F g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFormU_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Type) [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X),
    (∀ k ∈ finU (E := E) (n := n), R k = 1) → (∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u)) →
    (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g)) →
    (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) →
    ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  intro E _ _ _ n X _ _ _ R F hfin hcont hinf hrat hsm ℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    change ℓ (R g⁻¹ (F g0)) = ℓ (R g⁻¹ (F g))
    rw [e]
  · intro γ hγ g
    change ℓ (R (γ * g)⁻¹ (F (γ * g))) = ℓ (R g⁻¹ (F g))
    rw [hrat γ hγ g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (R γ⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · let φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F g))
    let H : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n (k : UA E n) φ = φ}
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n (a : UA E n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    have hnb : {k : finU (E := E) (n := n) | ∀ g, F (g * (k : UA E n)) = F g} ∈ 𝓝 (1 : finU (E := E) (n := n)) :=
      (continuous_subtype_val.tendsto (1 : finU (E := E) (n := n))).eventually hsm
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hnb fun k hk => ?_)
    change RU E n (k : UA E n) φ = φ
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, _root_.mul_inv_rev, map_mul, hfin _ ((finU (E := E) (n := n)).inv_mem k.2), one_mul]
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefL R F)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]

end GlobalTheory.EquivCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutRepUSpanValues
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.FrameAut.VecForms

theorem isAutRepU_span_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), M ≠ ⊥ → (∀ f ∈ M, (∀ v, IsAutFormU (f v)) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → (∀ k ∈ finU (E := E) (n := n), ∀ f ∈ M, (RU E n k) ∘ₗ f ∈ M) → (∀ N ≤ M, (∀ k ∈ finU (E := E) (n := n), ∀ f ∈ N, (RU E n k) ∘ₗ f ∈ N) → N = ⊥ ∨ N = M) → IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) := by
  intro E _ _ _ n S _ _ _ ρ hsp M hM0 hf hk hirr
  let j : M →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := M.subtype
  have himg : Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} = GlobalTheory.DefU.Pairs.img j := by
    unfold GlobalTheory.DefU.Pairs.img
    congr 1
    ext φ
    constructor
    · rintro ⟨f, hf, v, rfl⟩
      exact ⟨⟨f, hf⟩, v, rfl⟩
    · rintro ⟨p, v, rfl⟩
      exact ⟨p.1, p.2, v, rfl⟩
  rw [himg]
  have hj : ∀ (p : M) (x : infU E n) (v : S), j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => (hf p.1 p.2).2 x v
  have hstab : ∀ x, ∀ φ ∈ GlobalTheory.DefU.Pairs.img j, RU E n x φ ∈ GlobalTheory.DefU.Pairs.img j := by
    intro x φ hφ
    refine GlobalTheory.DefU.Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        change RU E n a.1 _ ∈ GlobalTheory.DefU.Pairs.img j
        rw [← hj]
        exact GlobalTheory.DefU.Pairs.apply_mem_img _ _ _)
      exact fun φ hφ => h1 hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact GlobalTheory.DefU.Pairs.apply_mem_img j ⟨(RU E n k.1) ∘ₗ p.1, hk k k.2 p.1 p.2⟩ v)
      exact fun φ hφ => h1 hφ
  have hne : GlobalTheory.DefU.Pairs.img j ≠ ⊥ := by
    obtain ⟨f, hfM, h0⟩ := (Submodule.ne_bot_iff _).1 hM0
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
    intro e
    have := GlobalTheory.DefU.Pairs.apply_mem_img j ⟨f, hfM⟩ v
    rw [e, Submodule.mem_bot] at this
    exact hv this
  let Q : finU (E := E) (n := n) → Module.End ℂ M := fun k =>
    ((LinearMap.llcomp ℂ S (UA E n → ℂ) (UA E n → ℂ) (RU E n k.1)) ∘ₗ M.subtype).codRestrict M
      (fun p => hk k k.2 p.1 p.2)
  have hP : ∀ N : Submodule ℂ M, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hst : ∀ k ∈ finU (E := E) (n := n), ∀ f ∈ N.map M.subtype, (RU E n k) ∘ₗ f ∈ N.map M.subtype := by
      rintro k hkk _ ⟨p, hp, rfl⟩
      exact ⟨Q ⟨k, hkk⟩ p, hN ⟨k, hkk⟩ p hp, rfl⟩
    have hc : N = (N.map M.subtype).comap M.subtype :=
      (Submodule.comap_map_eq_of_injective M.injective_subtype N).symm
    rcases hirr _ (Submodule.map_subtype_le M N) hst with h | h
    · left
      rw [hc, h, Submodule.comap_bot, Submodule.ker_subtype]
    · right
      rw [hc, h, Submodule.comap_subtype_self]
  refine ⟨fun φ hφ => ?_, hstab, hne, fun U hle hU => ?_⟩
  · have h1 : GlobalTheory.DefU.Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact (hf p.1 p.2).1 v)
    exact h1 hφ
  · exact GlobalTheory.DefU.Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
      (Q := Q) (T := fun k => RU E n k.1) (fun _ _ _ => rfl) hP hle
      (fun x => hU x.1) (fun k => hU k.1)

end GlobalTheory.FrameAut.VecForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

namespace GlobalTheory.FlatLine.DefinitePoint

theorem subsingleton_of_etale {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Sp K) [Etale f] {Z : Set X}
    (hZ : IsIrreducible Z) : Z.Subsingleton := by
  have : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  obtain ⟨o⟩ : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  have hd := f.isDiscrete_preimage_singleton o
  have hu : f ⁻¹' {o} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum K) _ _
  have : DiscreteTopology X := isDiscrete_univ_iff.mp (hu ▸ hd)
  exact hZ.isPreirreducible.subsingleton

theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 _) :
    IsOpenImmersion s := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
    (inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal f))) (by rw [hs]; infer_instance)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etale_strK (Xo : Moduli Dw l) (c : Coeff l) (hq : Dw.q = 0) : Etale (strK (Xo := Xo) (c := c)) := by
  have h0 : Dw.dim = 0 := by rw [Datum.dim, hq, mul_zero]
  have hs : SmoothOfRelativeDimension 0 Xo.s := h0 ▸ Xo.smooth
  have he : Etale Xo.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  infer_instance

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

theorem isAlgebraic_kap (Z : Comp Xo c) (hZ : (Z : Set (Xo.XF c)).Subsingleton) :
    Algebra.IsAlgebraic c.F (kap Z) := by
  obtain ⟨L, _, _, j, g, hg, hgZ⟩ := exists_numberField_point Z
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L (Xo.XF c)).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hg hgZ
  have hp : p = genPt Z := by
    refine hZ ?_ (CompSplitPfB.cspB_genPt_mem Z)
    obtain ⟨o⟩ : Nonempty (Sp L) := ⟨IsLocalRing.closedPoint L⟩
    have := hgZ o
    rwa [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at this
  subst hp
  have : CharZero (kap Z) := charZero_of_injective_algebraMap (algebraMap c.F (kap Z)).injective
  have ha : Algebra.IsAlgebraic ℚ (kap Z) :=
    Algebra.IsAlgebraic.of_injective (φ.hom.toRatAlgHom) φ.hom.injective
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → FnAlgClosed (Xo := Xo) (c := c) → ∀ Z : Comp Xo c, ∃ y₀ : FrPt Xo c c.F, LiesOn Z y₀ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x := by
  intro E _ _ _ H Dw l Xo c hq hac Z
  have := etale_strK Xo c hq
  have hZ := subsingleton_of_etale (strK (Xo := Xo) (c := c)) (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))
  have halg := isAlgebraic_kap Z hZ
  have hsurj : Function.Surjective (algebraMap c.F (kap Z)) := fun a => by
    obtain ⟨b, hb⟩ := hac Z (algebraMap (kap Z) (Om Z) a) ((halg.isAlgebraic a).algebraMap)
    refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
    rw [← hb, ← IsScalarTower.algebraMap_apply]
  let e : c.F ≃+* kap Z := RingEquiv.ofBijective _ ⟨(algebraMap c.F (kap Z)).injective, hsurj⟩
  let g₀ : Sp c.F ⟶ Xo.XF c := spMap e.symm.toRingHom ≫ genSp Z
  have hg₀ : g₀ ≫ strK = spMap (algebraMap c.F c.F) := by
    rw [Category.assoc, genSp_strK, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x => e.symm_apply_apply x)
  have hid : spMap (algebraMap c.F c.F) = 𝟙 _ := Spec.map_id _
  have hpt : ∀ s, g₀ s = genPt Z := fun s => by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have := isOpenImmersion_of_section strK g₀ (hg₀.trans hid)
  obtain ⟨y₀, hy₀⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (prX_over hg₀)
  refine ⟨y₀, fun s => ?_, fun S _ _ y hy => ?_⟩
  · rw [ptF_eq hg₀ hy₀, hpt]
    exact CompSplitPfB.cspB_genPt_mem Z
  · have hr : Set.range (ptF y) ⊆ Set.range g₀ := by
      rintro _ ⟨s, rfl⟩
      exact ⟨IsLocalRing.closedPoint c.F, (hpt _).trans (hZ (CompSplitPfB.cspB_genPt_mem Z) (hy s))⟩
    have h1 := IsOpenImmersion.lift_fac g₀ (ptF y) hr
    have h2 : IsOpenImmersion.lift g₀ (ptF y) hr = spMap (algebraMap c.F S) := by
      have h3 := congrArg (· ≫ strK) h1
      simp only [Category.assoc, hg₀, hid, Category.comp_id] at h3
      rw [h3, ptF, Limits.pullback.lift_snd]
    rw [hy₀, ← Category.assoc, ← h2, h1, ptF, Limits.pullback.lift_fst]

end GlobalTheory.FlatLine.DefinitePoint
end

