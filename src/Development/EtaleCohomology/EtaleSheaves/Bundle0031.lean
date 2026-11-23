module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHAlgSecPf
section
noncomputable section
open CategoryTheory Limits IsLocalRing

namespace LateralTheory.E.SHAlgSecPf

theorem retract_alg {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [Algebra.Etale A R] (Q : Ideal R) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A R)).IsMaximal) : Nonempty (R →ₐ[A] A) := by
  have hQm : Q.comap (algebraMap A R) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hQ
  have hEt : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := R)).mpr inferInstance
    have : (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus A R := by rw [h]; trivial
    exact this
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let Rg := Localization.Away g
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (Q : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgQ
  let Q' : Ideal Rg := Q.map (algebraMap R Rg)
  have hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap R Rg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have hcomap : Q'.comap (algebraMap A Rg) = RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [IsScalarTower.algebraMap_eq A R Rg, ← Ideal.comap_comap, hQ'c, hQm,
      ResidueField.algebraMap_eq, ker_residue]
  obtain ⟨φ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := A) (K := ResidueField A) Q' hcomap
  obtain ⟨ψ, -⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale (R := A) (A := Rg) (B := A)
    (C := ResidueField A) (maximalIdeal A) (Algebra.ofId A (ResidueField A))
    (residue_surjective) (fun b => by
      simp [Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff]) φ
  exact ⟨ψ.comp (IsScalarTower.toAlgHom A R Rg)⟩

theorem SHAlgSec_of : LateralTheory.E.SHSectionPf.SHAlgSec := by
  intro A R f hA hf hQ
  obtain ⟨hH, hS⟩ := hA
  let := f.hom.toAlgebra
  have : Algebra.Etale A R := (RingHom.etale_algebraMap).mp hf
  obtain ⟨Q, hQp, hQm⟩ := hQ
  obtain ⟨σ⟩ := retract_alg (A := A) (R := R) Q hQm
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  ext a
  exact σ.commutes a

end LateralTheory.E.SHAlgSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut Polynomial

namespace LateralTheory.E.SHLocPf

def EtClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C] (χ : C →+* Ω),
    χ.comp (algebraMap O C) = ψ → ∃ s : C →ₐ[O] O, ψ.comp s.toRingHom = χ

def Build : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ψ : O →+* Ω),
    IE f ∧ Function.Surjective ψ ∧ (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → ψ (f.hom a) = 0) ∧ EtClosed ψ

def Lift : Prop := ∀ (O Ω : Type) [CommRing O] [Field Ω] (ψ : O →+* Ω), EtClosed ψ →
  ∀ p : O[X], p.Monic → ∀ a₀ : O, ψ (p.eval a₀) = 0 → ψ (p.derivative.eval a₀) ≠ 0 →
    ∃ a : O, p.IsRoot a ∧ ψ a = ψ a₀

def Colim : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧ EtClosed ψ

theorem unit_of_etClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) (h : EtClosed ψ)
    (x : O) (hx : ψ x ≠ 0) : IsUnit x := by
  have hu : IsUnit (ψ x) := isUnit_iff_ne_zero.mpr hx
  let χ : Localization.Away x →+* Ω := IsLocalization.Away.lift x hu
  have hχ : χ.comp (algebraMap O (Localization.Away x)) = ψ := IsLocalization.Away.lift_comp x hu
  obtain ⟨s, -⟩ := h (Localization.Away x) χ hχ
  refine IsUnit.of_mul_eq_one (b :=  s (IsLocalization.Away.invSelf x)) ?_
  have e := congrArg s (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, map_one, AlgHom.commutes] at e
  simpa using e

theorem etaleClosed_point_lifts_simple_roots_monic : Lift := by
  intro O Ω _ _ ψ hE p hp a₀ h₁ h₂
  letI : Algebra O Ω := ψ.toAlgebra
  let P : StandardEtalePair O := ⟨p, hp, p.derivative, ⟨1, 0, 1, by ring⟩⟩
  have hev : ∀ q : O[X], aeval (ψ a₀) q = ψ (q.eval a₀) := by
    intro q
    rw [Polynomial.aeval_def]; exact Polynomial.eval₂_at_apply (p := q) ψ a₀
  have hM : P.HasMap (ψ a₀) := ⟨by rw [hev]; exact h₁, by rw [hev]; exact isUnit_iff_ne_zero.mpr h₂⟩
  let χ : P.Ring →+* Ω := (P.lift (ψ a₀) hM).toRingHom
  have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift (ψ a₀) hM).comp_algebraMap
  obtain ⟨s, hs⟩ := hE P.Ring χ hχ
  refine ⟨s P.X, ?_, ?_⟩
  · have h0 : aeval P.X P.f = 0 := P.hasMap_X.1
    have h1 := congrArg s h0
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at h1
    rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
    exact h1
  · have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X (ψ a₀) hM

theorem build_of (hC : Colim) : Build := by
  intro A _
  let k := IsLocalRing.ResidueField A
  let ι : A →+* SeparableClosure k := (algebraMap k (SeparableClosure k)).comp (IsLocalRing.residue A)
  obtain ⟨O, f, ψ, hIE, hcomp, hE⟩ := hC A (SeparableClosure k) ι
  refine ⟨O, f, SeparableClosure k, inferInstance, inferInstance, ψ, hIE, ?_, ?_, hE⟩
  · intro ω
    have hsep : (minpoly k ω).Separable := Algebra.IsSeparable.isSeparable k ω
    have hmon : (minpoly k ω).Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k ω)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts _).2 (fun n => IsLocalRing.residue_surjective _)) hmon
    letI : Algebra O (SeparableClosure k) := ψ.toAlgebra
    let P : StandardEtalePair O :=
      ⟨q.map f.hom, hqm.map _, (q.map f.hom).derivative, ⟨1, 0, 1, by ring⟩⟩
    have hev : ∀ r : A[X], aeval ω (r.map f.hom) = aeval ω (r.map (IsLocalRing.residue A)) := by
      intro r
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map]
      congr 1
    have hM : P.HasMap ω := by
      refine ⟨?_, ?_⟩
      · change aeval ω (q.map f.hom) = 0
        rw [hev, hq]; exact minpoly.aeval k ω
      · change IsUnit (aeval ω (q.map f.hom).derivative)
        rw [Polynomial.derivative_map, hev, ← Polynomial.derivative_map, hq]
        exact isUnit_iff_ne_zero.mpr (hsep.aeval_derivative_ne_zero (minpoly.aeval k ω))
    let χ : P.Ring →+* SeparableClosure k := (P.lift ω hM).toRingHom
    have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift ω hM).comp_algebraMap
    obtain ⟨s, hs⟩ := hE P.Ring χ hχ
    refine ⟨s P.X, ?_⟩
    have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X ω hM
  · intro a ha
    have e : ψ (f.hom a) = ι a := congrArg (fun g => g a) hcomp
    rw [e]
    simp [ι, (IsLocalRing.residue_eq_zero_iff a).2 ha]

theorem SHLoc_of (hB : Build) (hL : Lift) : LateralTheory.E.SHExistsPf.SHLoc := by
  intro A _
  obtain ⟨O, f, Ω, _, _, ψ, hIE, hs, hm, hE⟩ := hB A
  have hU : ∀ x : O, ψ x ≠ 0 → IsUnit x := unit_of_etClosed ψ hE
  have hZ : ∀ x : O, IsUnit x → ψ x ≠ 0 := fun x hx => (hx.map ψ).ne_zero
  have : Nontrivial O := ⟨⟨1, 0, fun h => by simpa using congrArg ψ h⟩⟩
  have : IsLocalRing O := IsLocalRing.of_nonunits_add (by
    intro a b ha hb hab
    have ha' : ψ a = 0 := by by_contra h; exact ha (hU a h)
    have hb' : ψ b = 0 := by by_contra h; exact hb (hU b h)
    exact hZ _ hab (by rw [map_add (f := _), ha', hb', add_zero]))
  have hmem : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ ψ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hU x h'), fun h hx => hZ x hx h⟩
  have hker : IsLocalRing.maximalIdeal O = RingHom.ker ψ := by
    ext x; rw [hmem, RingHom.mem_ker]
  let e : IsLocalRing.ResidueField O ≃+* Ω :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs)
  have hSC : IsSepClosed (IsLocalRing.ResidueField O) := by
    refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
    have hd : (p.map (e : IsLocalRing.ResidueField O →+* Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨y, hy⟩ := IsSepClosed.exists_root _ hd (hsep.map)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [map_zero, ← hy]
    have h := Polynomial.eval₂_at_apply (p := p) (e : IsLocalRing.ResidueField O →+* Ω) (e.symm y)
    rw [Polynomial.eval_map]
    simpa using h.symm
  have hH : HenselianLocalRing O := {
    is_henselian := by
      intro p hp a₀ h₁ h₂
      obtain ⟨a, ha, ha'⟩ := hL O Ω ψ hE p hp a₀ ((hmem _).1 h₁) (hZ _ h₂)
      exact ⟨a, ha, (hmem _).2 (by rw [map_sub, ha', sub_self])⟩ }
  refine ⟨O, f, hIE, ⟨hH, hSC⟩, ⟨fun a ha => ?_⟩⟩
  by_contra hna
  exact hZ _ ha (hm a ((IsLocalRing.mem_maximalIdeal _).2 hna))

end LateralTheory.E.SHLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SecPrePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.SecPrePf
open LateralTheory.E.t_E3Cut

theorem id_mem (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {S : Sieve (Spec A)}
    (hS : S ∈ Scheme.etaleTopology (Spec A)) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have : IsLocalRing A := hA.elim fun h _ => h.toIsLocalRing
  obtain ⟨hcov, -⟩ := (Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨j, y, hy⟩ := hcov (IsLocalRing.closedPoint A : PrimeSpectrum A)
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have hsurj : Function.Surjective (𝒰.f j) := by
    intro z
    have hopen : IsOpen (Set.range (𝒰.f j)) := (𝒰.f j).isOpenMap.isOpen_range
    have hmem : (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ Set.range (𝒰.f j) := ⟨y, hy⟩
    exact (IsLocalRing.specializes_closedPoint (z : PrimeSpectrum A)).mem_open hopen hmem
  have : Surjective (𝒰.f j) := ⟨hsurj⟩
  obtain ⟨s, hs⟩ := hSec A hA (𝒰.f j)
  have h1 : S.arrows (𝒰.f j) := hle _ _ (Presieve.ofArrows.mk j)
  have h2 := S.downward_closed h1 s
  rwa [hs] at h2

theorem mem_of_cov (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {V : Scheme.{0}} (h : Spec A ⟶ V)
    (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) : S.arrows h := by
  have := id_mem hSec A hA (Scheme.etaleTopology.pullback_stable h hS)
  simpa using this

variable {R : Type} [CommRing R]

def sky (U : Scheme.{0}) (N : ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ ((U ⟶ V.unop) → N)
  map g := ModuleCat.ofHom
    { toFun := fun φ h => φ (h ≫ g.unop)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

theorem sky_isSheaf (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (N : ModuleCat.{1} (ULift.{1} R)) : Presheaf.IsSheaf Scheme.etaleTopology (sky U N) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  have hc := hx.to_sieveCompatible
  refine ⟨fun h => x h (hU h S hS) (𝟙 U), ?_, ?_⟩
  · intro W f hf
    funext k
    have e := congrFun (hc f k hf) (𝟙 U)
    change x (k ≫ f) _ (𝟙 U) = x f hf k
    rw [e]
    change x f hf (𝟙 U ≫ k) = _
    rw [Category.id_comp]
  · intro t ht
    funext h
    have e := congrFun (ht h (hU h S hS)) (𝟙 U)
    change t (𝟙 U ≫ h) = _ at e
    rw [Category.id_comp] at e
    exact e

@[simps]
def toSky (Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) {N : ModuleCat.{1} (ULift.{1} R)}
    (g : Q.obj (op U) ⟶ N) : Q ⟶ sky U N where
  app V := ModuleCat.ofHom
    { toFun := fun p h => g.hom ((Q.map h.op).hom p)
      map_add' := fun _ _ => by funext h; simp
      map_smul' := fun _ _ => by funext h; simp }
  naturality V W f := by
    ext p
    funext h
    change g.hom ((Q.map h.op).hom ((Q.map f).hom p)) = g.hom ((Q.map (h ≫ f.unop).op).hom p)
    rw [op_comp, Quiver.Hom.op_unop, Q.map_comp]
    rfl

theorem toSheafify_bij (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Function.Bijective ((toSheafify Scheme.etaleTopology P).app (op U)).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e := toSheafify_sheafifyLift Scheme.etaleTopology (toSky P U (𝟙 _)) (sky_isSheaf U hU _)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom x) e) (𝟙 U)
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] at e2
    have e3 : (P.map (𝟙 U).op).hom x = 0 := e2.symm
    rwa [op_id, P.map_id] at e3
  · intro y
    let η := toSheafify Scheme.etaleTopology P
    let Q := sheafify Scheme.etaleTopology P
    let g : Q.obj (op U) ⟶ ModuleCat.of _ (Q.obj (op U) ⧸ LinearMap.range (η.app (op U)).hom) :=
      ModuleCat.ofHom (Submodule.mkQ _)
    have e := sheafify_hom_ext Scheme.etaleTopology (toSky Q U g) 0 (sky_isSheaf U hU _) (by
      ext V p
      funext h
      have nat : (Q.map h.op).hom ((η.app V).hom p) = (η.app (op U)).hom ((P.map h.op).hom p) :=
        (congrArg (fun φ => φ.hom p) (η.naturality h.op)).symm
      simp only [NatTrans.comp_app, toSky_app, Limits.comp_zero]
      change (Submodule.mkQ _) ((Q.map h.op).hom (η.app V |>.hom p)) = 0
      rw [nat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom y) e) (𝟙 U)
    simp only [toSky_app] at e2
    change (Submodule.mkQ _) ((Q.map (𝟙 U).op).hom y) = 0 at e2
    rw [op_id, Q.map_id, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e2
    obtain ⟨x, hx⟩ := e2
    exact ⟨x, hx⟩

theorem SecPre_of (hSec : SHSection) : LateralTheory.E.SHEqvPf.SecPre := by
  intro _ q i A hA
  exact toSheafify_bij (R := ZMod q) (Spec A) (fun h S hS => mem_of_cov hSec A hA h S hS) (Scheme.Γ ⋙ twF q i)

end LateralTheory.E.SecPrePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ShiftLvlPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ShiftLvlPf

universe u v

section General

variable {C : Type u} [Category.{v} C] [Abelian C]

def coneIso {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B')
    (h : φ ≫ e₂.hom = e₁.hom ≫ ψ) : mappingCone φ ≅ mappingCone ψ where
  hom := mappingCone.map φ ψ e₁.hom e₂.hom h
  inv := mappingCone.map ψ φ e₁.inv e₂.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact mappingCone.map_id φ
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact mappingCone.map_id ψ

theorem sub_of_iso {K K' : CochainComplex C ℤ} (L : CochainComplex C ℤ) (n : ℤ) (e : K ≅ K')
    (h : Subsingleton (CohomologyClass K' L n)) : Subsingleton (CohomologyClass K L n) := by
  rw [(CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).toEquiv.subsingleton_congr] at h
  exact @Equiv.subsingleton _ _ ((((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso e).homCongr (Iso.refl ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))))) h

theorem sub_of_shift {A0 Ap : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p n : ℤ) (e : Ap ≅ A0⟦p⟧)
    (h : Subsingleton (CohomologyClass A0 I (n - p))) : Subsingleton (CohomologyClass Ap I n) := by
  rw [(CohomologyClass.homAddEquiv (K := Ap) (L := I) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := A0) (L := I) (n := n - p)).toEquiv.subsingleton_congr] at h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let α : (Q.obj A0)⟦p⟧ ≅ Q.obj Ap := ((Q.commShiftIso p).app A0).symm ≪≫ Q.mapIso e.symm
  let β : (Q.obj (I⟦n - p⟧))⟦p⟧ ≅ Q.obj (I⟦n⟧) :=
    ((Q.commShiftIso p).app _).symm ≪≫ Q.mapIso ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (n - p) p n (by omega)).app I).symm
  have e1 := (Functor.FullyFaithful.ofFullyFaithful (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) p)).homEquiv
    (X := Q.obj A0) (Y := Q.obj (I⟦n - p⟧))
  exact @Equiv.subsingleton _ _ (e1.trans (α.homCongr β)).symm h

def singleConeIso {X Y : C} (f : X ⟶ Y) (p : ℤ) :
    mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) (-p)).map f) ≅
      (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f))⟦p⟧ :=
  let σ := (CochainComplex.singleFunctors C).shiftIso p (-p) 0 (by omega)
  coneIso _ _ (σ.app X).symm (σ.app Y).symm (σ.inv.naturality f) ≪≫
    (mappingCone.shiftIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) p).symm

end General

theorem chains_f_comm (R : Type) [CommRing R] {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      (chainsXIso R E₀ p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) := by
  unfold chains chainsXIso
  rw [Functor.comp_map]
  show (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat).f (ComplexShape.embeddingDownNat.f p) ≫
      (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p) rfl).hom =
    (HomologicalComplex.extendXIso ((chainsN R).obj E₀) ComplexShape.embeddingDownNat (i := p) rfl).hom ≫ _
  rw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1

theorem ShiftLvl_of : LateralTheory.E.CechFiltPf.ShiftLvl := by
  intro R _ F E₀ E g p n h
  have h1 := sub_of_shift (res R F) (p : ℤ) n
    (singleConeIso ((free R).map (g.app (op (SimplexCategory.mk p)))) (p : ℤ)) h
  refine sub_of_iso (res R F) n ?_ h1
  exact coneIso _ _ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E₀ p))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, chains_f_comm])

end LateralTheory.E.ShiftLvlPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkGermPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.StalkGermPf

abbrev toO {X S : Scheme.{0}} (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback p (S.fromSpecStalk s) ⟶ overO p U :=
  pullback.map p (S.fromSpecStalk s) p U.ι (𝟙 _) (U.fromSpecStalkOfMem s hs) (𝟙 _) (by simp) (by simp)

def StalkCont : Prop := Cont → Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p], IsUnit (q : Γ(S, ⊤)) → ∀ (i n : ℤ) (s : S),
  (∀ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i), pull _ (sch.map (toO p s U hs)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ z : Ht q (sch.obj (pullback p (S.fromSpecStalk s))) n i, ∃ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i),
    pull _ (sch.map (toO p s U hs)) _ _ x = z)

variable {Y X S : Scheme.{0}}

theorem pull_mc {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Ht q (sch.obj C) n i) :
    pull _ (sch.map (a ≫ b)) (tw q i) n x = pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) := by
  rw [Functor.map_comp, pull_comp]

theorem toO_res (p : X ⟶ S) (s : S) {V U : S.Opens} (h : V ≤ U) (hV : s ∈ V) :
    toO p s V hV ≫ resO p h = toO p s U (h hV) := by
  have e : V.fromSpecStalkOfMem s hV ≫ S.homOfLE h = U.fromSpecStalkOfMem s (h hV) := by
    rw [← cancel_mono U.ι]; simp
  simp only [toO, resO]; rw [pullback.map_comp]; congr 1 <;> simp [e]

theorem toO_f (f : Y ⟶ X) (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ toO p s U hs =
      toO (f ≫ p) s U hs ≫ fO f p U := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_f (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_res (p : X ⟶ S) {W V U : S.Opens} (h1 : W ≤ V) (h2 : V ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem StalkGerm_of (hS : StalkCont) : StalkGerm := by
  intro hC hH q Y X S f p _ _ _ _ _ _ hq i s he n
  obtain ⟨ia, sa⟩ := hS hC hH q p hq i n s
  obtain ⟨ib, -⟩ := hS hC hH q (f ≫ p) hq i n s
  have hb := he n
  constructor
  · intro U hs x hx
    apply ia U hs x
    apply hb.1
    rw [map_zero, ← pull_mc, toO_f, pull_mc, hx, map_zero]
  · intro U hs y
    obtain ⟨w, hw⟩ := hb.2 (pull _ (sch.map (toO (f ≫ p) s U hs)) _ _ y)
    obtain ⟨U1, hs1, x1, hx1⟩ := sa w
    have hs2 : s ∈ U ⊓ U1 := ⟨hs, hs1⟩
    have hx2' : pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n
        (pull (ZMod q) (sch.map (resO p (inf_le_right : U ⊓ U1 ≤ U1))) (tw q i) n x1) = w := by
      rw [← pull_mc, toO_res]; exact hx1
    obtain ⟨x2, hx2⟩ : ∃ x2 : H (ZMod q) (sch.obj (overO p (U ⊓ U1))) (tw q i) n,
        pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n x2 = w := ⟨_, hx2'⟩
    have e1 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _ (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) =
        pull _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _)
          (by simp) (by simp))) (tw q i) n (pull _ (sch.map (toO p s (U ⊓ U1) hs2)) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, toO_f]
    have e2 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (toO (f ≫ p) s U hs)) (tw q i) n y := by
      rw [← pull_mc, toO_res]
    have h0 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2 -
          pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) = 0 := by
      rw [map_sub, e1, e2, hx2, hw, sub_self]
    obtain ⟨V, hV, hsV, hd⟩ := ib _ hs2 _ h0
    refine ⟨V, hV.trans inf_le_left, hsV, pull _ (sch.map (resO p hV)) _ _ x2, ?_⟩
    rw [map_sub, sub_eq_zero] at hd
    have g1 : pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p hV)) _ _ x2) =
        pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, res_f]
    have g2 : pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (resO (f ≫ p) (hV.trans inf_le_left))) (tw q i) n y := by
      rw [← pull_mc, res_res]
    rw [g1, hd, g2]

end LateralTheory.E.StalkGermPf
end
end

