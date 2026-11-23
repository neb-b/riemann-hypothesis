module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import GroundTheory.PAdicHodge.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0240
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import GroundTheory.PAdicHodge.BdRLattice
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecsMapArrow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem secs_map_arrow {X : Scheme.{0}} {E : X.Modules} (D : Subobject E)
    (B : Subobject (D : X.Modules)) (V : X.Opens) :
    secs ((Subobject.map D.arrow).obj B) V = (D.arrow.app V) '' secs B V := by
  have hmk : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    exact Subobject.map_mk _ _
  let e := Subobject.isoOfEqMk _ _ hmk
  have he : e.hom ≫ (B.arrow ≫ D.arrow) = ((Subobject.map D.arrow).obj B).arrow := by
    simp only [e, Subobject.isoOfEqMk_hom, Subobject.ofLEMk_comp]
  have he' : e.inv ≫ ((Subobject.map D.arrow).obj B).arrow = B.arrow ≫ D.arrow := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext y
  simp only [GlobalTheory.CompanionTheory.GE.secs]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(B.arrow.app V) ((e.hom.app V) x), ⟨_, rfl⟩, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(e.inv.app V) x, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he'
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenChar

theorem cycloChar_inertia_image_infinite : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  intro l _ h L _
  let H : Subgroup Gal(Om l/↥L) :=
    { carrier := {σ | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}
      mul_mem' := by
        intro a b ha hb w hw
        show a (b w) = w
        rw [hb w hw, ha w hw]
      one_mem' := by
        intro w _
        rfl
      inv_mem' := by
        intro a ha w hw
        have haw : a w = w := ha w hw
        calc a⁻¹ w = a⁻¹ (a w) := by rw [haw]
          _ = w := by simp [AlgEquiv.aut_inv] }
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ℤ_[l]ˣ, M = H.map (GroundTheory.PAdicHodge.cycloChar L) := ⟨_, rfl⟩
  have hMfin : Finite M := by
    have hs : (M : Set ℤ_[l]ˣ).Finite := by
      rw [hM, Subgroup.coe_map]
      exact hfin
    exact hs.to_subtype
  obtain ⟨n, hnM⟩ : ∃ n : ℕ, n = Nat.card M := ⟨_, rfl⟩
  have hn : 0 < n := by
    rw [hnM]
    exact Nat.card_pos
  have hpow : ∀ σ ∈ H, (GroundTheory.PAdicHodge.cycloChar L σ) ^ n = 1 := by
    intro σ hσ
    have hmem : GroundTheory.PAdicHodge.cycloChar L σ ∈ M := by
      rw [hM]
      exact Subgroup.mem_map_of_mem _ hσ
    have h1 : (⟨GroundTheory.PAdicHodge.cycloChar L σ, hmem⟩ : M) ^ n = 1 := by
      rw [hnM]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hroots : ∀ σ : Gal(Om l/↥L), GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → σ ∈ H := by
    intro σ hσ
    have hfix := (GroundTheory.LocalField.unramifiedDegree_eq_one_iff σ).mp hσ
    have hS : ∀ y ∈ GroundTheory.PAdicHodge.primeToPRoots l, σ y = y := by
      rintro y ⟨m, hm0, hmcop, hym⟩
      apply hfix
      have hcop : Nat.Coprime l m := Nat.Coprime.symm hmcop
      have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
      have hle : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
      have hdvd : m ∣ l ^ Nat.totient m - 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      obtain ⟨c, hc⟩ := hdvd
      refine GroundTheory.PAdicHodge.EigenWitt.mem_unramifiedRoots_of_pow_eq_one (L := L)
        (Nat.totient_pos.2 hm0) ?_
      rw [hc, pow_mul, hym, one_pow]
    have hσ' : (σ.restrictScalars ℚ_[l]) ∈
        (IntermediateField.adjoin ℚ_[l] (GroundTheory.PAdicHodge.primeToPRoots l)).fixingSubgroup :=
      GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff.mpr (fun y hy => hS y hy)
    show ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w
    intro w hw
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' w hw
  let ψ : Gal(Om l/↥L) →* ℤ_[l]ˣ := (powMonoidHom n).comp (GroundTheory.PAdicHodge.cycloChar L)
  have hψc : Continuous ψ := (GroundTheory.PAdicHodge.continuous_cycloChar L).pow n
  have hψu : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → ψ σ = 1 := by
    intro σ hσ
    exact hpow σ (hroots σ hσ)
  obtain ⟨f, hf, x, hx0, hx⟩ := h L ψ hψc hψu
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -((n * f : ℕ) : ℤ) := ⟨_, rfl⟩
  have hj0 : j ≠ 0 := by
    rw [hj, neg_ne_zero, Nat.cast_ne_zero]
    exact Nat.mul_ne_zero hn.ne' hf.ne'
  have hinv : x ∈ (GroundTheory.PAdicHodge.cpTwistRep L j).invariants := by
    change ∀ σ, (GroundTheory.PAdicHodge.cpTwistRep L j σ) x = x
    intro σ
    have key : (((GroundTheory.PAdicHodge.cycloChar L σ ^ j : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ^ f = 1 := by
      have hψσ : ψ σ = GroundTheory.PAdicHodge.cycloChar L σ ^ n := rfl
      have hu : GroundTheory.PAdicHodge.cycloChar L σ ^ j * (GroundTheory.PAdicHodge.cycloChar L σ ^ n) ^ f = 1 := by
        rw [hj, ← pow_mul, zpow_neg, zpow_natCast, inv_mul_cancel]
      rw [hψσ, ← PadicInt.coe_pow, ← PadicInt.coe_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hu]
      simp
    rw [GroundTheory.PAdicHodge.cpTwistRep_apply, hx σ, GroundTheory.PAdicHodge.twistScalar, ← mul_assoc, ← map_mul, key,
      map_one, one_mul]
  rw [GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot L hj0] at hinv
  exact hx0 ((Submodule.mem_bot _).mp hinv)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriod
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.LocalField GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenWitt GroundTheory.PAdicHodge.EigenChar

theorem exists_pow_eigenvector_of_unramified_units {l : ℕ} [Fact l.Prime]
    (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E]
    (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ) (hψ : Continuous ψ)
    (hI : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
      σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  have := isSepClosure_padicAlgCl (p := l) (L := E)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := E) (Ω := PadicAlgCl l)
    (Multiplicative.ofAdd 1)
  set w : ℤ_[l]ˣ := ψ σ₀ with hwdef
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (p := l) (L := E)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := E) w
  set cA := wittToAInf (b : WittVector l (Fpbar l)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[l]) l
  set xc : ℂ_[l] := ((θ cA : normInteger ℂ_[l]) : ℂ_[l]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[l] ℂ_[l] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz₀ : (z σ₀ : ℚ_[l]) = ((w : ℤ_[l]) : ℚ_[l]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree E (PadicAlgCl l) σ = 1 → (z σ : ℚ_[l]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector l (Fpbar l)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt l (z σ) * cA =
        IsPerfectoidField.padicIntToWitt l 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  obtain ⟨χ, hχc, hχ⟩ := exists_eigenChar hxc (fun σ => ⟨_, hxcσ σ⟩)
  have hχeq : ∀ σ, ((χ σ : ℚ_[l]ˣ) : ℚ_[l]) = (z σ : ℚ_[l]) := fun σ =>
    eq_of_mul_eq hxc ((hχ σ).symm.trans (hxcσ σ))
  have hψne : ∀ σ, ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ≠ 0 := fun σ => by
    intro h
    exact (ψ σ).ne_zero (Subtype.ext (h.trans PadicInt.coe_zero.symm))
  let ρC : Gal(PadicAlgCl l/E) →* ℂ_[l] :=
    { toFun := fun σ => algebraMap ℚ_[l] ℂ_[l]
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]))
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [mul_inv_rev, map_mul, Units.val_mul, PadicInt.coe_mul, mul_pow]
        ring }
  have hρC : Continuous ρC := by
    have hc1 : Continuous fun σ : Gal(PadicAlgCl l/E) => (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      have hu : Continuous fun σ : Gal(PadicAlgCl l/E) => ((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) :=
        (Units.continuous_val (M := ℤ_[l])).comp hψ
      exact (continuous_subtype_val : Continuous (fun y : ℤ_[l] => (y : ℚ_[l]))).comp hu
    have hc2 : Continuous fun σ : Gal(PadicAlgCl l/E) => ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) :=
      Units.continuous_val.comp (hχc.comp continuous_inv)
    exact isometry_algebraMap_padic_cp.continuous.comp ((hc1.pow f).mul hc2)
  have hρval : ∀ σ, ρC σ = algebraMap ℚ_[l] ℂ_[l]
      ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹) := fun σ => by
    change algebraMap ℚ_[l] ℂ_[l] _ = _
    rw [map_inv, Units.val_inv_eq_inv_val, hχeq]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (by rw [hρval, hz₀, ← hwdef, mul_inv_cancel₀ (pow_ne_zero _ (hψne σ₀)), map_one])
    (fun σ hσ => by rw [hρval, hzI σ hσ, hI σ hσ, Units.val_one, PadicInt.coe_one, one_pow, inv_one,
      mul_one, map_one])
  refine ⟨f, hf, xc, hxc, fun σ => ?_⟩
  have h1 : (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹ = 1 :=
    algebraMap_padic_cp_injective (by rw [map_one, ← hρval]; exact hall σ)
  have hz0 : (z σ : ℚ_[l]) ≠ 0 := by
    intro h
    rw [h, inv_zero, mul_zero] at h1
    exact zero_ne_one h1
  rw [hxcσ σ, (mul_inv_eq_one₀ hz0).1 h1]

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulFil
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.BetaFil

open CrystallineSemistableComparison.CH CrystallineSemistableComparison.CechClassBoundaries

theorem img_smul {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F : C ⥤ ModuleCat.{w} R}
    (S S' : SubF F) (a : R) (h : ∀ T, ∀ x ∈ S.S T, a • x ∈ S'.S T) (j : ℕ) :
    ∀ x ∈ S.img j, a • x ∈ S'.img j := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, hc, rfl⟩ := clsSurj y
  let α : S.fn ⟶ S'.fn :=
    { app := fun T => ModuleCat.ofHom ((a • (LinearMap.id : F.obj T →ₗ[R] F.obj T)).restrict fun x hx => h T x hx)
      naturality := fun T T' φ => by
        ext x
        exact Subtype.ext (map_smul (F.map φ).hom a x.1).symm }
  have hc' := cyc (Mor.ofNatTrans α).hom c hc
  have hc'' := cyc S'.inc.hom _ hc'
  have hs := cyc S.inc.hom c hc
  refine ⟨(Mor.ofNatTrans α).pull j ((cx S.fn).cls c hc), ?_⟩
  change S'.inc.hom.mapH j ((Mor.ofNatTrans α).hom.mapH j ((cx S.fn).cls c hc)) =
    a • S.inc.hom.mapH j ((cx S.fn).cls c hc)
  rw [mapH_cls' _ c hc hc', mapH_cls' _ _ hc' hc'', mapH_cls' _ c hc hs,
    ← cls_smul a _ hs (by rw [map_smul, hs, smul_zero])]
  rfl

theorem pdS_smul {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r j : ℕ) (a : Λ)
    (ha : c a ∈ b.I) : ∀ x ∈ (CrystallineSemistableComparison.B.pdS L c r).img j, a • x ∈ (CrystallineSemistableComparison.B.pdS L c (r + 1)).img j :=
  img_smul _ _ a (fun T _ hx => CrystallineSemistableComparison.B.mul_pdPow L T r (T.i_mem ha) hx) j


set_option maxHeartbeats 1000000 in
theorem smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j := by
  intro l _ O _ F κ k n r j a ha x hx
  exact @pdS_smul (bs l k n) (Lc F κ k n) (Acris l) _ ((base l).cris n) r j a ha x hx

end GlobalTheory.CompanionTheory.BetaFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclicStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_pull_bijective_of_acyclic : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (ha : ∀ T, a.S T = ⊤),
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) → ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | exact GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | (intros; apply GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAbove
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.SnocPerm

theorem eq_succAbove_of_snoc_eq_perm {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (hI : StrictMono I)
    (h : Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π) : I = k.succAbove := by
  have hcast : ∀ i : Fin n, π i.castSucc = I i := fun i => by
    rw [← h]; simp
  have hlast : π (Fin.last n) = k := by
    rw [← h]; simp
  have hrange : Set.range I = Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩ hy
      rw [← hcast i, ← hlast] at hy
      exact (Fin.castSucc_lt_last i).ne (π.injective hy)
    · intro hy
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : x ≠ Fin.last n := fun hx => hy (by rw [hx, hlast])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hx
      exact ⟨i, (hcast i).symm⟩
  exact (StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange

end GlobalTheory.CompanionTheory.ConeLocal.SnocPerm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_affineOpens {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, (U : X.Opens))), φ.app (U : X.Opens) s = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have key : ∀ s : Γ(M, U), φ.app U s = 0 := by
    intro s
    refine TopCat.Sheaf.eq_of_locally_eq' F
      (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U
      (fun i => homOfLE i.2) ?_ _ _ ?_
    · refine fun x (hx : x ∈ U) => ?_
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · intro i
      have hnat := ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s
      simp only [ConcreteCategory.comp_apply] at hnat
      have h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0 := by
        rw [← h i.1 (M.presheaf.map (homOfLE i.2).op s)]
        exact hnat.symm
      exact h2.trans (map_zero _).symm
  ext s
  simp [key s]

theorem le_iff_secs_subset {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E) :
    S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  unfold GlobalTheory.CompanionTheory.GE.secs
  constructor
  · intro hST U x hx
    obtain ⟨s, rfl⟩ := hx
    refine ⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]
  · intro h
    have hzero : S.arrow ≫ cokernel.π T.arrow = 0 := by
      apply GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens
      intro U s
      obtain ⟨t, ht⟩ := h U (Set.mem_range_self s)
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
        Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
    exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero)
      (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem secs_pullback_arrow {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens) :
    secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  let G : X.Modules ⥤ Type :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab
  haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj
      (Opposite.op V)) := ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩
  haveI : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan (forget Ab.{0}) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan G := inferInstance
  have hp := (Subobject.isPullback D.arrow S).map G
  ext d
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(Subobject.pullbackπ D.arrow S).app V p, ?_⟩
    exact congr($(hp.w) p)
  · rintro ⟨s, hs⟩
    obtain ⟨p, h₁, h₂⟩ := Types.exists_of_isPullback hp s d hs
    exact ⟨p, h₂⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

def latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) : Subring (Formalism.Per6.BdRp l) :=
  Subring.closure (Set.range (wB l) ∪ (rB l) '' {x | x ∈ K' ∧ IsIntegral ℤ_[l] x})

theorem wB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (a : Wl l) :
    wB l a ∈ latS K' :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem rB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) {x : Om l}
    (hx : x ∈ K') (hi : IsIntegral ℤ_[l] x) : rB l x ∈ latS K' :=
  Subring.subset_closure (Or.inr ⟨x, ⟨hx, hi⟩, rfl⟩)

theorem ker_thB_eq {l : ℕ} [Fact l.Prime] :
    RingHom.ker (thB l) = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) :=
  (GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

end GlobalTheory.CompanionTheory.LTPer
end
end

