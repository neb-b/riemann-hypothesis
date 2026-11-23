module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0237
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.IrreducibleCharpolyInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrrCharEqOneOfSubsingleton
public import Development.AbelianVarietyTheory.Counterexamples.SubgroupCharacterSums.SumSubgroupEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsEqOfEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w

namespace GlobalTheory.CompanionTheory.RedPull

theorem cls_eq_of_eq {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b)
    (ha : K.d n a = 0) (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem pull_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {F G : C ⥤ ModuleCat.{0} R} {F' G' : C' ⥤ ModuleCat.{0} R'}
    (a : CH.Mor F G (RingHom.id R)) (b : CH.Mor G G' σ) (c : CH.Mor F F' σ) (d : CH.Mor F' G' (RingHom.id R'))
    (j : ℕ) (h : ∀ x : CH.Cn F j, b.pullC j (a.pullC j x) = d.pullC j (c.pullC j x)) (z : CH.H F j) :
    b.pull j (a.pull j z) = d.pull j (c.pull j z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) j).1 z
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc a.hom x hx
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc b.hom _ h1
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc c.hom x hx
  have h4 := CrystallineSemistableComparison.CechClassBoundaries.cyc d.hom _ h3
  change b.hom.mapH j (a.hom.mapH j _) = d.hom.mapH j (c.hom.mapH j _)
  rw [CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' a.hom x hx h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' b.hom _ h1 h2,
    CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' c.hom x hx h3, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' d.hom _ h3 h4]
  exact cls_eq_of_eq (h x) h2 h4

theorem sq_toSq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} (mm : SMor Φ Φ' σ) (b : IdF Φ.A) (b' : IdF Φ'.A)
    (ha : mm.Le (IdF.top _) (IdF.top _)) (hb : mm.Le b b') (j : ℕ) (z : CH.H (CH.modF Φ.A) j) :
    (mm.sq ha hb).pull j ((toSq (IdF.top _) b fun _ => rfl).pull j z) =
      (toSq (IdF.top _) b' fun _ => rfl).pull j (mm.o.pull j z) := by
  refine pull_square _ _ _ _ j (fun x => ?_) z
  funext t
  exact Subtype.ext Ideal.quotientMap_mk

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := by
  intro O A A' _ _ _ _ _ I I' γ γ' X X' q q' σ m l s r n j z
  exact sq_toSq (nmS m l s) _ _ (fun _ _ _ => trivial) (nm_std m l s r n) j z

end GlobalTheory.CompanionTheory.RedPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_subobject {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    IsCoherent (D : X.Modules) := by
  have hEq := hE.1
  have hC : (cokernel D.arrow).IsQuasicoherent := inferInstance
  have hK : IsCoherent (kernel (cokernel.π D.arrow)) := isCoherent_kernel _ hE
  let e : (D : X.Modules) ≅ kernel (cokernel.π D.arrow) :=
    IsLimit.conePointUniqueUpToIso
      (Abelian.monoIsKernelOfCokernel (f := D.arrow)
        (CokernelCofork.ofπ _ (cokernel.condition D.arrow)) (cokernelIsCokernel _))
      (limit.isLimit _)
  refine ⟨hD, fun U hU => ?_⟩
  have := hK.2 U hU
  let f : Γ(kernel (cokernel.π D.arrow), U) →ₗ[Γ(X, U)] Γ((D : X.Modules), U) :=
    { toFun := e.inv.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective f (bijective_app_of_iso e.symm U).2

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLift
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerHom

theorem exists_roots {R : Type} [CommRing R] {l : ℕ} (h : ∀ x : R, ∃ y, y ^ l = x) (u : R) :
    ∃ y : ℕ → R, y 0 = u ∧ ∀ m, y (m + 1) ^ l = y m := by
  choose r hr using h
  exact ⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩

theorem roots_unique {R : Type} [CommRing R] {l : ℕ} (h : ∀ x y : R, x ^ l = y ^ l → x = y) {y z : ℕ → R}
    (h0 : y 0 = z 0) (hy : ∀ m, y (m + 1) ^ l = y m) (hz : ∀ m, z (m + 1) ^ l = z m) (m : ℕ) : y m = z m := by
  induction m with
  | zero => exact h0
  | succ m ih => exact h _ _ (by rw [hy, hz, ih])

theorem pow_sub_pow {R : Type} [CommRing R] {l : ℕ} (F : R →+* R) (hF : ∀ x, F x = x ^ l) (x y : R) (m : ℕ) :
    x ^ l ^ m - y ^ l ^ m = (x - y) ^ l ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]

theorem iter_root {R : Type} [CommRing R] {l : ℕ} {x : ℕ → R} (hx : ∀ m, x (m + 1) ^ l = x m) (m : ℕ) :
    x m ^ l ^ m = x 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]

variable {l : ℕ} [Fact l.Prime]

theorem pow_char (A : PAlg l) (x : A.A) : A.frob x = x ^ l := rfl

theorem pow_inj (A : PAlg l) (x y : A.A) (h : x ^ l = y ^ l) : x = y := A.frob_bijective.1 h

theorem pow_surj (A : PAlg l) (x : A.A) : ∃ y, y ^ l = x := A.frob_bijective.2 x

theorem eq_of_roots_mod (A : PAlg l) {x y : ℕ → A.A} (hx : ∀ m, x (m + 1) ^ l = x m) (hy : ∀ m, y (m + 1) ^ l = y m)
    (h : ∀ m, x m - y m ∈ Ideal.span {A.pi}) : x 0 = y 0 := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A := A.compl.toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun n => ?_)
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n,
    pow_sub_pow A.frob (pow_char A)]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)

theorem mapU_mem {A A' : PAlg l} (φ : A ⟶ A') {x : A.U} (hx : x ∈ Ideal.span {(l : A.U)}) :
    mapU φ x ∈ Ideal.span {(l : A'.U)} := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_sharp_cong (A : PAlg l) (x : A.U) : ∃ a, A.sharp a - x ∈ Ideal.span {(l : A.U)} := by
  obtain ⟨a, ha⟩ := (RL.u_mod A).1 (Ideal.Quotient.mk _ x)
  refine ⟨a, ?_⟩
  rw [A.sharpMap_eq] at ha
  simpa using Ideal.Quotient.eq.1 ha

def modEquiv (A : PAlg l) : (A.A ⧸ Ideal.span {A.pi}) ≃+* A.Un 1 :=
  (Ideal.quotEquivOfEq (RL.u_mod A).2.symm).trans (RingHom.quotientKerEquivOfSurjective (RL.u_mod A).1)

theorem modEquiv_mk (A : PAlg l) (a : A.A) : modEquiv A (Ideal.Quotient.mk _ a) = A.aToU1 a := rfl

def gBar (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) : R →+* A.A ⧸ Ideal.span {A.pi} :=
  ((modEquiv A).symm : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi}).comp ((Ideal.Quotient.mk _).comp g)

theorem gBar_iff (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) (r : R) (a : A.A) :
    gBar A g r = Ideal.Quotient.mk _ a ↔ A.sharp a - g r ∈ Ideal.span {(l : A.U)} := by
  have e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r)) := rfl
  rw [e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]


open CrystallineSemistableComparison.PAlg in
theorem core {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (A' : PAlg l)
    (g : s.R →+* A'.U) (hga : g.comp s.a = A'.oC.comp κ) (u : Fin d → A'.A) (hu : ∀ k, A'.sharp (u k) = g (s.T k)) :
    ∃ φ : 𝒯.A ⟶ A', ((mapU φ).comp 𝒯.g = g ∧ ∀ k, Hom.f φ (𝒯.c k 0).val = u k) ∧
      ∀ φ' : 𝒯.A ⟶ A', (mapU φ').comp 𝒯.g = g → (∀ k, Hom.f φ' (𝒯.c k 0).val = u k) → φ' = φ := by
  have hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m := fun k => exists_roots (pow_surj A') (u k)
  choose y hy0 hys using hy
  have hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val := fun k m => by
    rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  have ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0) := by
    intro x w hw
    have hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0) := WittVector.map_coeff _ _ _
    refine (gBar_iff A' g _ _).2 ?_
    have e1 : g (s.a x) = A'.th (A'.sW w) := by
      rw [← A'.oC_theta0, hw]
      exact RingHom.congr_fun hga x
    have e2 := A'.sharpMap_coeff (A'.sW w)
    rw [hcf, A'.sharpMap_eq] at e2
    rw [e1]
    simpa using Ideal.Quotient.eq.1 e2
  have h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k) := fun k =>
    ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm
  have h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m) :=
    fun k m => by rw [← map_pow, hys]
  obtain ⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩ := 𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g)
    (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3
  obtain ⟨φ, hφ, hφu⟩ := GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo
  have hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a := fun a => RingHom.congr_fun hφ a
  have hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k := by
    intro k
    rw [← hy0 k]
    refine eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_
    · rw [← map_pow, hc]
    · refine Ideal.Quotient.eq.1 ?_
      rw [hφa, hfc]
  have hgφ : (mapU φ).comp 𝒯.g = g := by
    have hE := GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU
      (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et
      (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) rfl
    refine hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_
      · have e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o) := RingHom.congr_fun 𝒯.hg o
        have e2 : g (s.a o) = A'.oC (κ o) := RingHom.congr_fun hga o
        simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [e1, e2, mapU_oC]
      · simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        rw [← 𝒯.c_sharp, mapU_sharp, hck, hu]
    · refine RingHom.ext fun r => ?_
      obtain ⟨a, ha⟩ := exists_sharp_cong 𝒯.A (𝒯.g r)
      have e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a) := by rw [hφa]; exact (hfg r a ha).symm
      have e1 := (gBar_iff A' g r _).1 e
      have e2 := mapU_mem φ ha
      rw [map_sub, mapU_sharp] at e2
      refine Ideal.Quotient.eq.2 ?_
      have e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r)) := by ring
      change mapU φ (𝒯.g r) - g r ∈ _
      rw [e3]
      exact Ideal.sub_mem _ e1 e2
  refine ⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩
  · rw [RingHom.comp_assoc, Hom.comm]
  · intro r a ha
    have e2 := mapU_mem φ' ha
    rw [map_sub, mapU_sharp] at e2
    have e3 : mapU φ' (𝒯.g r) = g r := RingHom.congr_fun hg' r
    rw [e3] at e2
    exact ((gBar_iff A' g r _).2 e2).symm
  · intro k m
    have := roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k)
      ((hk' k).trans (hy0 k).symm) (fun m => by
        rw [← map_pow, hc]) (hys k) m
    exact congrArg (Ideal.Quotient.mk _) this

theorem tower_hom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  intro l _ O _ F κ d s 𝒯 T
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2
  have hga : g.comp s.a = T.1.oC.comp κ :=
    F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2
  have hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g := by
    intro φ
    refine hgu _ ?_
    have h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1 :=
      congrArg Subtype.val φ.2
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
      exact h1
    exact h2
  refine ⟨g, hg, hall, fun u hu => ?_⟩
  obtain ⟨φ, ⟨hφg, hφk⟩, hφu⟩ := core 𝒯 T.1 g hga u hu
  have hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2 := by
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [hφg]
      exact hg
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp] at h2
    exact h2
  refine ⟨⟨φ, hpt⟩, hφk, fun φ' hk => CategoryTheory.Functor.Elements.Hom.ext (hφu φ'.1 (hall φ') hk)⟩

end GlobalTheory.CompanionTheory.TowerHom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem isCuspChar_character {d : ℕ} (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    CuspElliptic.IsCuspChar τ.character := by
  rw [GlobalTheory.CuspCharCheck.isCuspChar_iff]
  refine ⟨τ, hs, rfl, fun a h0 h1 v hv => ?_⟩
  refine hc 2 (twoBlock d a) ?_ le_rfl v fun u hu => hv u ?_
  · intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [twoBlock, h0]⟩
    · exact ⟨⟨a, h1⟩, by simp [twoBlock]⟩
  · intro i j
    by_cases hij : i.val < a ∧ a ≤ j.val
    · exact Or.inr hij
    · left
      by_cases hb : twoBlock d a i = twoBlock d a j
      · exact hu.2 i j hb
      · have hi : a ≤ i.val := by
          by_contra hi
          have hj : j.val < a := by
            by_contra hj
            exact hij ⟨by omega, by omega⟩
          exact hb (by simp [twoBlock, show i.val < a by omega, hj])
        have hj : j.val < a := by
          by_contra hj
          exact hb (by simp [twoBlock, show ¬ i.val < a by omega, show ¬ j.val < a by omega])
        have hne : i ≠ j := fun e => by subst e; omega
        rw [if_neg hne]
        exact hu.1.1 i j (by simp [twoBlock, show ¬ i.val < a by omega, hj])

theorem finrank_of_simple_cuspidal (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d : ℕ} (hd : 1 ≤ d)
    (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) := by
  have h := isCuspChar_character τ hs hc
  obtain ⟨k, -, hk⟩ := GlobalTheory.CuspFormula.exists_regular K θ hθ d hd τ.character
    (GlobalTheory.CuspGL.isIrrChar_of_norm_one _ h.1) (GlobalTheory.CuspGL.isPrimitive_of_isCuspChar _ h)
  have h1 := hk 1
  have hid : Matrix.toLin' ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    simp [Module.End.one_eq_id]
  have hfr : Module.finrank K (Fin d → K) = d := by simp
  rw [FDRep.char_one, hid, GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico K (Fin d → K) (GlobalTheory.CuspGL.rootSum θ k) (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one K θ k).2
    (by rw [hfr]; omega), hfr, Nat.card_eq_fintype_card] at h1
  have hsign : ((-1 : ℂ)) ^ (d - 1) * ∏ i ∈ Finset.Ico 1 d, (1 - (Fintype.card K : ℂ) ^ i) =
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1) := by
    rw [← Nat.card_Ico 1 d, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hsign] at h1
  have h2 : ((Module.finrank ℂ τ : ℤ) : ℂ) = ((∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) : ℤ) : ℂ) := by
    push_cast
    exact h1
  exact_mod_cast h2

end

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DPullCEqZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.MuThick

universe w w' v u v' u'

theorem d_pullC_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'} (m : CH.Mor F F' σ) (n : ℕ) (b : CH.Cn F n)
    (hb : CH.d F n b = 0) : CH.d F' n (m.pullC n b) = 0 := by
  rw [m.d_pullC, hb, map_zero]

theorem muB_incl {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (j : ℕ) (x : HdR q j) :
    (incl h).o.pull j (muB γ q l s' 𝒱 j x) = muB γ q l s 𝒱 j x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (GlobalTheory.LogCris.O (smFun X q))) j).1 x
  have d1 : ∀ (s₀ : ℕ), CH.d _ j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j a ha
  have d2 : ∀ (s₀ : ℕ), CH.d _ j ((smO γ q l s₀ 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a)) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j _ (d1 s₀)
  have d3 : CH.d _ j ((incl h).o.pullC j ((smO γ q l s' 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s' 𝒱).ι).pullC j a))) = 0 :=
    d_pullC_eq_zero _ j _ (d2 s')
  have e : ∀ s₀ : ℕ, muB γ q l s₀ 𝒱 j ((CH.cx (GlobalTheory.LogCris.O (smFun X q))).cls a ha) =
      (CH.cx _).cls _ (d2 s₀) := fun s₀ =>
    (congrArg ((smO γ q l s₀ 𝒱).o.pull j) (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).hom j a ha (d1 s₀))).trans
      (CrystallineSemistableComparison.P.mapH_cls (smO γ q l s₀ 𝒱).o.hom j _ (d1 s₀) (d2 s₀))
  rw [e s', e s]
  refine (CrystallineSemistableComparison.P.mapH_cls (incl h).o.hom j _ (d2 s') d3).trans ?_
  have key : ∀ (b : CH.Cn (CH.modF (sP (TS γ q l s 𝒱)).A) j) (hb : CH.d _ j b = 0),
      b = (smO γ q l s 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s 𝒱).ι).pullC j a) →
      (CH.cx (CH.modF (sP (TS γ q l s 𝒱)).A)).cls b hb = (CH.cx _).cls _ (d2 s) := by
    rintro _ _ rfl
    rfl
  refine key _ d3 ?_
  funext t
  rfl

end GlobalTheory.CompanionTheory.MuThick
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_cyclotomic_element_properties : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.EpsFacts.eps_facts | exact GlobalTheory.CompanionTheory.EpsFacts.eps_facts | (intros; apply GlobalTheory.CompanionTheory.EpsFacts.eps_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open TensorProduct DividedPowers

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem dividedPowerFiltration_dividedPowersBot_of_one_le {K : Type} [CommRing K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase_dpBot {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s := by
  refine ⟨dividedPowerFiltration_dividedPowersBot_of_one_le hs, ?_, ?_⟩
  · intro r x h
    simpa only [Nat.cast_one, one_mul] using h
  · intro n hn
    refine ⟨0, (n : K)⁻¹, ?_⟩
    rw [pow_zero, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]

theorem exists_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  intro K _ _ X q W d c s hs
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase_dpBot hs
  obtain ⟨c', e, hTF, he1, he2, he3⟩ := GlobalTheory.CompanionTheory.ChartAlg.chart_exists (O := K) (R := K) (dividedPowersBot K) 1 s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  letI := (strV q W).toAlgebra
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hD : KS q s {W} c'.D := ⟨hTF, W, rfl, c'.inV⟩
  let E := c'.frame hg (KS q s {W}) (ks_in q s W) hD
  have hpow (r : ℕ) : c'.D.pdPow r = (pdP (dividedPowersBot K) r).map c'.D.i :=
    GlobalTheory.CompanionTheory.ChartFil.dividedPowerFiltration_eq_map _ _ _ c'.D.compat c'.J_eq r
  have hc : E.GrConst (sFil (KS q s {W})) := by
    intro n T u v x hx
    have hx' : (show c'.D.B from x) ∈ c'.D.pdPow ((n : ℤ).toNat) := hx
    rw [Int.toNat_natCast, hpow] at hx'
    change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
    rw [show ((n : ℤ) + 1).toNat = n + 1 by omega]
    exact GlobalTheory.CompanionTheory.ChartFil.sub_mem_pdP c' (ks_in q s W _ T.property) u.hom v.hom n hx'
  let ε : Γ(X, W) ≃+* c'.D.B := (Algebra.TensorProduct.lid K Γ(X, W)).symm.toRingEquiv.trans e
  have hε : ∀ f, ε f = e ((1 : K) ⊗ₜ[K] f) := fun f => rfl
  refine ⟨E, ε, hc, fun x hx => ?_, fun a => ?_, fun T u g => ?_, fun i T u v => ?_⟩
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow 1 := hx
    rw [hpow, dividedPowerFiltration_dividedPowersBot_of_one_le le_rfl, Ideal.map_bot] at h2
    exact Ideal.mem_bot.1 h2
  · have e1 : (1 : K) ⊗ₜ[K] (strV q W a) = a ⊗ₜ[K] (1 : Γ(X, W)) := by
      have : strV q W a = a • (1 : Γ(X, W)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change ε (strV q W a) = c'.D.i a
    rw [hε, e1, he1]
  · have h1 := GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) u.hom c'.inV (ks_in q s W _ T.property) g
    exact h1.trans ((congrArg (Ideal.quotientMap T.obj.J u.hom.φ u.hom.hle) (he3 g)).trans rfl)
  · change (v.hom.φ (c'.t i) - u.hom.φ (c'.t i) : T.obj.B) = v.hom.φ (ε (c.t i)) - u.hom.φ (ε (c.t i))
    rw [hε, he2]

end GlobalTheory.CompanionTheory.ConeLocal
end

