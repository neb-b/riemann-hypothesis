module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.TriSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private theorem lc_ker {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group M]
    (φ : H →* M) (h : IsOpen (φ.ker : Set H)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H)) := h.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy
  have : φ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

private theorem fin_chars (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [hl : Fact l.Prime] (N : ℕ) (hN : N ≠ 0) (K H : Subgroup (G F Ω)) (hK : IsOpen (K : Set (G F Ω)))
    (hH : IsOpen (H : Set (G F Ω))) (M : Subgroup (G F Ω))
    (hM : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := F) A, g ∈ K → g ∈ M) :
    Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : G F Ω) ∈ M → φ g = 1} := by
  haveI : IsGalois F Ω := {}
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let V : Subgroup (G F Ω) := (H ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ
  have hVo : IsOpen (V : Set (G F Ω)) := (hH.inter hK).inter (stabilizer_isOpen_of_isIntegral ζ)
  let E : IntermediateField F Ω := IntermediateField.fixedField V
  have hE : E.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)
  haveI : NumberField E := NumberField.of_module_finite F E
  have hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V := fun σ => by
    rw [← hE, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => σ.commutes ⟨x, hx⟩
  have hgal : V ≤ Base.galOf F E Ω := fun u hu x => x.2 ⟨u, hu⟩
  have hζE : ζ ∈ E := fun v => v.2.2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective
  haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype
  let e : G E Ω →* H := (Base.galEmb F E Ω).codRestrict H fun σ => (hmem σ).1.1
  have he : Continuous e := ((Base.galEmbTop F E Ω).1.continuous).subtype_mk _
  haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo
  have hfin : Finite (H ⧸ e.range) := by
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have h2 : V.subgroupOf H ≤ e.range := fun x hx => ⟨Kum.toGal E hgal ⟨x, hx⟩, Subtype.ext rfl⟩
    haveI := Subgroup.finiteIndex_of_le h2
    infer_instance
  refine Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} ×
      (H ⧸ e.range → Multiplicative (ZMod l)))
    (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e g)), ((lc_ker φ.1 φ.2.1).comp_continuous he).comp _,
      fun a b => by simp only [map_mul, toAdd_mul], fun A hA g hg => by
        show Multiplicative.toAdd (φ.1 (e g)) = 0
        rw [φ.2.2 (e g) (hM A hA _ ⟨hg.1, hg.2⟩ (hmem g).1.2), toAdd_one]⟩, fun q => φ.1 q.out)) ?_
  intro φ ψ h
  have h1 : ∀ g, φ.1 (e g) = ψ.1 (e g) := fun g =>
    Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)
  have h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out := congrFun (congrArg Prod.snd h)
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := QuotientGroup.mk_out_eq_mul e.range x
  have h3 := h2 (QuotientGroup.mk x)
  rw [hg, map_mul, map_mul, h1] at h3
  exact mul_right_cancel h3

private theorem l_mem {l : ℕ} [Fact l.Prime] (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
  rwa [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0

private theorem char_res {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : CharP (ResidueField c.O) l :=
  (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact l_mem c)

private theorem inc_max {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, inc h x ∈ maximalIdeal c'.O := by
  letI : Algebra c.O c'.O := (inc h).toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite ℤ_[l] c'.O := inferInstance
  haveI : Module.Finite c.O c'.O := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul c.O c'.O := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective h)
  haveI : Algebra.IsIntegral c.O c'.O := Algebra.IsIntegral.of_finite _ _
  haveI : IsLocalHom (algebraMap c.O c'.O) := Algebra.IsIntegral.isLocalHom _ _
  exact fun x hx => map_nonunit (algebraMap c.O c'.O) x hx

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem cont_resQ (T : Tower D) : Continuous (resQ T.F) := (Base.galEmbTop ℚ T.F Ω).1.continuous

private theorem ok_of (hD : D.Good) (T : Tower D) (hT : T.Ok) (W : Finset ℕ) (k : Type) [Field k] (a : c.O →+* k)
    (ha : ∀ x ∈ maximalIdeal c.O, a x = 0) : (T.fr W).Ok a := by
  obtain ⟨-, -, -, -, -, f6, -, -, -, -, f11, -⟩ := facts D hD
  let j : ResidueField c.O →+* k := Ideal.Quotient.lift _ a ha
  have hj : ∀ x, a x = j (residue c.O x) := fun _ => rfl
  haveI := char_res c
  refine ⟨fun i g => ?_, ?_, fun i i' hi => ?_, ?_, fun i => ?_⟩
  · have e : lab T.pr i.rev = (lab T.pr i).rev := by
      generalize T.pr = b
      revert b i
      decide
    show D.ps (lab T.pr i) (resQ T.F g) * D.ps (lab T.pr i.rev) (resQ T.F g) = D.th (resQ T.F g)
    rw [e, ← f6 (lab T.pr i)]
    rfl
  · rintro g ⟨A, -, -, hg⟩ i
    have h1 : residue c.O (D.ps (lab T.pr i) (resQ T.F g) : c.O) = 1 := by
      simpa [Raw.rbar, Raw.r0, diagRep] using congrFun (congrFun hg (lab T.pr i)) (lab T.pr i)
    rw [hj, ← map_one j]
    exact congrArg j h1
  · rw [hj, hj, ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 (hT.dist i i' hi))).map j
  · have h2 : (2 : ResidueField c.O) ≠ 0 := fun h => hD.l_odd
      ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h)))
    simpa only [map_ofNat] using (IsUnit.mk0 _ h2).map j
  · exact ((f11 (lab T.pr i) 1).comp_continuous (cont_resQ T)).comp
      (Ideal.Quotient.lift _ a fun x hx => ha x (by rwa [pow_one] at hx))

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.std :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (W : Finset ℕ) (c' : Coef l) (h : c.O ≤ c'.O), (0 ∉ W → (T.fr W).Std l (inc h)) ∧ ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr W).Ok a := by
  intro hP Ω _ _ _ l hl c D T hT W c' h
  have hD : D.Good := hT.2.elim (fun x => x.1.1) fun x => x.1.1
  refine ⟨fun hW => ?_, ok_of hD T hT.1 W⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, f11, f12, -⟩ := facts D hD
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  have ok : (T.fr W).Ok ((residue c'.O).comp (inc h)) :=
    ok_of hD T hT.1 W _ _ fun x hx => (residue_eq_zero_iff _).2 (inc_max h x hx)
  haveI := char_res c'
  refine ⟨ok, char_res c', fun i n => ?_, fun H hH _ => ?_, fun v => isClosed_Dec _, fun v => ?_, ?_⟩
  · exact ((f11 (lab T.pr i) n).comp_continuous (cont_resQ T)).comp
      (Ideal.quotientMap (maximalIdeal c'.O ^ n) (inc h)
        ((Ideal.pow_right_mono (fun x hx => inc_max h x hx) n).trans (Ideal.le_comap_pow _ n)))
  · refine fin_chars T.F Ω l (∏ p ∈ insert l W, p) (Finset.prod_ne_zero_iff.2 fun p hp => ?_)
      (D.rbar.ker.comap (resQ T.F)) H (f12.preimage (cont_resQ T)) hH _ fun A hA g hg hg' => ?_
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hl.out.ne_zero
      · exact fun e => hW (e ▸ hp)
    · refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, fun p hp hpA => hA ?_, hg, hg'⟩)
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
      rw [hm, Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (natCast_mem A m))) hpA
  · have hA : T.pl v ≠ ⊤ := fun e => by
      have h1 := T.ovl v
      have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
      have h2 := ((T.pl v).valuation_le_one_iff (l : Ω)⁻¹).2 (e ▸ ValuationSubring.mem_top _)
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0))] at h2
      exact absurd h1 (not_lt.2 h2)
    obtain ⟨w, hw⟩ := (Kum.placeDict T.F Ω).2.1 _ hA
    exact Pa.phiDec hP.loc.lf l T.F Ω _ w hw
  · rintro v s ⟨hs, m, hm⟩
    refine ⟨hs, fun i => ?_⟩
    let γ : G T.F Ω →* (ResidueField c'.O)ˣ := (Units.map ((residue c'.O).comp (inc h)).toMonoidHom).comp ((T.fr W).χ i)
    have ho : IsClosed (γ.ker : Set (G T.F Ω)) := by
      have e : (γ.ker : Set (G T.F Ω)) = {g | ((residue c'.O).comp (inc h)) ((T.fr W).χ i g) = 1} :=
        Set.ext fun g => Units.ext_iff
      rw [e]
      exact (ok.lc i).isClosed_fiber 1
    have h1 : γ (s ^ l ^ m) = 1 := Subgroup.topologicalClosure_minimal _
      ((Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker γ)) ho hm
    rw [map_pow] at h1
    have h2 : ((γ s : ResidueField c'.O) - 1) ^ l ^ m = 0 := by
      rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero) |>.1 h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtPair
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ptp_root {B V : Type} [CommRing B] [CommRing V] [IsLocalRing V] (f : B →+* V) {I : Ideal B}
    (hf : ∀ b ∈ I, f b ∈ maximalIdeal V) {q : B[X]} (hq : Pp.Dist I q) {v : V} (hv : q.eval₂ f v = 0) :
    v ∈ maximalIdeal V := by
  rw [hq.1.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum, add_eq_zero_iff_eq_neg] at hv
  refine Ideal.IsPrime.mem_of_pow_mem inferInstance q.natDegree ?_
  rw [hv]
  refine neg_mem (Ideal.sum_mem _ fun n hn => ?_)
  rw [eval₂_mul, eval₂_C]
  exact Ideal.mul_mem_right _ _ (hf _ (hq.2 n (Finset.mem_range.1 hn)))

theorem UpperTheory.V.Ws.ptPair :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r, VPt D 𝔞 r → ∃ u, KPair D 𝔞 r u := by
  intro _ Ω _ _ _ l _ c D hD 𝔞 r ⟨hs, R, _, _, _, ρ, y, hρ, hy, hm, hr⟩
  subst hr
  have hy' : ∀ a, y (algebraMap c.O R a) = 𝔞.a c a := fun a => DFunLike.congr_fun hy a
  obtain ⟨B, _, _, _, _, τ, hτ, ⟨x, hx⟩, z, hz⟩ := hρ.atL
  obtain ⟨-, -, -, -, -, hrev, hinj, -⟩ := facts D hD
  haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B
  obtain ⟨h, P, H, hP, hI⟩ := Pp.genTri ((D.Ip l).subgroupOf (D.Gp l)) (fun i (g : D.Gp l) => (D.ps i g : c.O)) D.s0
    (D.th D.s0 : c.O) τ.hom x hD.decompSigma_mem.1.1 hinj (fun i => by rw [← hrev i]; rfl) (Units.ne_zero _) (hτ.1 _) hτ.2 hx
  let f : B →+* 𝔞.V := y.comp (z : B →+* R)
  obtain ⟨h', H'⟩ := Pp.triSpec _ P _ (𝔞.V.subtype.comp f) h (fun a ha => by
    rw [RingHom.mem_ker, map_eq_zero_iff _ (IsFractionRing.injective B (FractionRing B))] at ha
    rw [ha]
    exact zero_mem _) H
  obtain ⟨u, hu, U⟩ := Pp.triIwa 𝔞.V _ P f h' H'
  have hf : ∀ a, f (algebraMap c.O B a) = 𝔞.a c a := fun a => (congrArg y (z.commutes a)).trans (hy' a)
  have hfm : ∀ b ∈ maximalIdeal B, f b ∈ maximalIdeal 𝔞.V := fun b hb =>
    hm _ ((res_eq_zero_iff c.O R _).1 ((res_map z b).trans ((res_eq_zero_iff c.O B _).2 hb)))
  have e : ∀ s : D.Gp l, (τ.hom s).map f = mapRep y ρ.hom s := fun s => by
    have : (D.loc ρ l).hom s = ρ.hom s := rfl
    ext i j
    rw [mapRep_apply, ← this, ← hz]
    rfl
  refine ⟨u, Pp.smallFlag 𝔞 _ u hs, fun g i j => ?_, fun g => ?_, fun A hA g hg hb => ?_, fun p hp g hg => ?_, hu,
    fun s hs => ?_, fun s hs i => ?_, fun s hs i => ?_⟩
  · rw [mapRep_apply, ← hy', ← map_sub]
    refine hm _ ((res_eq_zero_iff c.O R _).1 ?_)
    rw [map_sub, ρ.red, AlgHom.commutes]
    exact sub_self _
  · have h1 := hρ.mult g
    unfold IsGSp at h1 ⊢
    show adj ((ρ.hom g).map y) * (ρ.hom g).map y = _
    rw [(grp R).2.2.2.2.2.1, ← Matrix.map_mul, h1, ← hy']
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply,
      Matrix.one_apply, apply_ite y, map_one, map_zero]
  · show y.mapMatrix (ρ.hom g) = 1
    rw [hρ.unr A hA g hg hb, map_one]
  · obtain ⟨B', _, _, _, _, τ', hτ', -, z', hz'⟩ := hρ.atP p hp
    have h1 : ρ.hom g = (D.loc ρ p).hom ⟨g, hg.1.1⟩ := rfl
    show y.mapMatrix (ρ.hom g) = 1
    rw [h1, ← hz']
    show y.mapMatrix (z'.mapMatrix (τ'.hom _)) = 1
    rw [hτ'.2 _ hg, map_one, map_one]
  · have := (U ⟨s, hs⟩).1
    rwa [e] at this
  · obtain ⟨q, hq, hq'⟩ := hP ⟨s, hs⟩ i
    have := (U ⟨s, hs⟩).2 i
    rw [e, hq', eval₂_comp, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact ptp_root f hfm hq this
  · have := (U ⟨s, hs.1⟩).2 i
    rw [e, hI _ hs, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact sub_eq_zero.1 this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Pur
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3

private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]

private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.pur :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, ProMod D ι 𝔞 r → Pure ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l _ c D hD ι 𝔞 e he r hr
  obtain ⟨T, c', h, X, J, y, r₁, -, -, hPM, hy, -, hJ, hconj, -, hres, hin⟩ := hr
  let f : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK
  let y' : X.A →ₐ[c'.O] PadicAlgCl l :=
    { f.comp y with
      commutes' := fun x => by
        have h1 : y (algebraMap c'.O X.A x) = 𝔞.a c' x := DFunLike.congr_fun hy x
        exact (congrArg f h1).trans (he.1 c' x) }
  have hy' : ∀ x, y' x = f (y x) := fun _ => rfl
  have hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y' : X.A →+* PadicAlgCl l)) := by
    have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
    refine ⟨(D.ψ.ker ⊓ D.om.ker).comap (resQ T.F),
      (hD.psi_open.inter (facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.1).preimage hc, fun v i s hs => ?_⟩
    have h1 : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := hs.2
    have h2 := ps_wt_any hD (T.ovl v) i h1 hs.1.1 hs.1.2
    have h3 : f (y (X.P.ψ v i s)) = ((D.ps i (resQ T.F s) : c.O) : PadicAlgCl l) :=
      (congrArg f (hin v i s hs.2)).trans (he.1 c _)
    have h4 : (GlobalTheory.GalOfCusp.cycBar T.F Ω l s : PadicAlgCl l) =
      ((chiO ℚ Ω l c.O (resQ T.F s) : c.O) : PadicAlgCl l) := rfl
    refine (congrArg (· ^ 2) ((map_psi X.P _ v i s).trans h3)).trans ?_
    rw [h2]
    have h5 : (2 * (D.wts4 i : ℤ)) = ((D.wts4 i * 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [h5, zpow_natCast, Units.val_pow_eq_pow_val, h4, SubmonoidClass.coe_pow, pow_mul]
  have hp := hPM.pur y' (fun b hb => by rw [hy', hJ b hb, map_zero]) hw (mapRep f r₁) (by
    ext g i j
    exact congrArg f (congrFun (congrFun (DFunLike.congr_fun hres g) i) j))
  obtain ⟨H, M, hH, hM, hp⟩ := hp
  refine ⟨H, M, hH, hM, fun p h1 h2 A hA n σ hn hσ hF => ?_⟩
  have h3 : (mapRep f r σ).charpoly = (mapRep f r₁ σ).charpoly :=
    charpoly_conj (e : 𝔞.K →+* PadicAlgCl l) hconj σ
  rw [h3]
  exact hp p h1 h2 A hA n σ hn hσ hF
end

