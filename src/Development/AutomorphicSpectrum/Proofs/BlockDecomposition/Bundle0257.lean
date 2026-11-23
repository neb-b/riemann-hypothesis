module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0242
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuot
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := _root_.GlobalTheory.CompanionTheory.TowerHom.tower_hom 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := _root_.GlobalTheory.CompanionTheory.TowerHom.tower_hom 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := _root_.GlobalTheory.CompanionTheory.TowerHom.tower_hom 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := _root_.GlobalTheory.CompanionTheory.TowerHom.tower_hom 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWitt
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisFlat

theorem flat_quotient_of_flat {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) (f : R ⧸ I →+* A ⧸ J)
    (hf : ∀ a, f (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap R A a)) :
    letI := f.toAlgebra; Module.Flat (R ⧸ I) (A ⧸ J) := by
  subst hJ
  letI := f.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  let e₀ : (R ⧸ I) ⊗[R] A ≃ₗ[R] A ⧸ I.map (algebraMap R A) :=
    (TensorProduct.comm R (R ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.restrictScalars R)
  let e : (R ⧸ I) ⊗[R] A ≃ₗ[R ⧸ I] A ⧸ I.map (algebraMap R A) :=
    e₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact Module.Flat.of_linearEquiv e.symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def wToAcr0 (r : Res l K) : WittVector l r.k →+* (base l).Acr0 :=
  (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))

theorem isTorsionFree_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.IsTorsionFree (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x h
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' a ha
  rw [Algebra.smul_def] at h
  have h1 : (wToAcr0 r a : Localization.Away (l : (base l).W)) * (x : Localization.Away (l : (base l).W)) = 0 :=
    congrArg Subtype.val h
  have hl : IsUnit (l : Localization.Away (l : (base l).W)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : (base l).W)) (l : (base l).W)
    rwa [map_natCast] at this
  have hu : IsUnit (wToAcr0 r a : Localization.Away (l : (base l).W)) := by
    have e2 : (wToAcr0 r a : Localization.Away (l : (base l).W)) =
        (l : Localization.Away (l : (base l).W)) ^ m * ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) b := by
      change ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) a = _
      rw [e, map_mul, map_pow, map_natCast]
    rw [e2]
    exact (hl.pow m).mul (b.isUnit.map _)
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h1)

theorem flat_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.Flat (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  haveI := isTorsionFree_acris_zero r
  infer_instance

theorem flat_acr (r : Res l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  letI := (wToAcr0 r).toAlgebra
  haveI := flat_acris_zero r
  refine flat_quotient_of_flat (R := WittVector l r.k) (A := (base l).Acr0)
    (Ideal.span {(l : WittVector l r.k) ^ n}) (Ideal.span {(l : (base l).Acr0) ^ n}) ?_ (Mid.wn r n) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · intro a
    exact (Mid.wn_mk r n a).trans ((base l).cris_algebraMap n (WittVector.map r.s a))

end GlobalTheory.CompanionTheory.CrisFlat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeightStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_character_weight : ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
    ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite →
    ∀ (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l]),
    (∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l))) →
    (∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    n = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | exact GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | (intros; apply GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Globalize

lemma exists_pow_smul_uniform {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (hP : P.FG) (N : ℕ → Submodule R M) (f : R)
    (h : ∀ x ∈ P, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n) :
    ∃ k : ℕ, ∀ n, ∀ x ∈ P, f ^ k • x ∈ N n := by
  classical
  obtain ⟨s, rfl⟩ := hP
  have h' : ∀ x ∈ s, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n :=
    fun x hx => h x (Submodule.subset_span (Finset.mem_coe.2 hx))
  choose! k hk using h'
  refine ⟨s.sup k, fun n x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ s := Finset.mem_coe.1 hy
    have e : f ^ s.sup k • y = f ^ (s.sup k - k y) • f ^ k y • y := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hy')]
    rw [e]
    exact (N n).smul_mem _ (hk y hy' n)
  | zero => rw [smul_zero]; exact (N n).zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact (N n).add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact (N n).smul_mem _ hy

variable {X : Scheme.{0}}

def killIdeal {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (V : X.Opens) :
    Ideal Γ(X, V) :=
  ⨅ n, (secsSub (S n) V).colon (secs D V)

lemma mem_killIdeal {E : X.Modules} {D : Subobject E} {S : ℕ → Subobject E} {V : X.Opens}
    {a : Γ(X, V)} : a ∈ killIdeal D S V ↔ ∀ n, ∀ x ∈ secs D V, a • x ∈ secs (S n) V := by
  simp only [killIdeal, Submodule.mem_iInf, Submodule.mem_colon]
  rfl

theorem exists_pow_le_killIdeal [IsLocallyNoetherian X] {E : X.Modules} (hE : IsCoherent E)
    (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) (S : ℕ → Subobject E)
    (J₀ : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ f ∈ J₀.ideal V, ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) :
    ∃ m : ℕ, J₀.ideal V ^ m ≤ killIdeal D S V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have hfin : Module.Finite Γ(X, V) Γ((D : X.Modules), V) :=
    (isCoherent_subobject hE D hD).2 V V.2
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hr : secsSub D V = LinearMap.range φ := Submodule.ext fun _ => Iff.rfl
  have hP : (secsSub D V).FG := by
    rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map φ
  have hrad : J₀.ideal V ≤ (killIdeal D S V).radical := by
    intro f hf
    obtain ⟨k, hk⟩ := exists_pow_smul_uniform (secsSub D V) hP (fun n => secsSub (S n) V) f
      (fun x hx => h f hf x hx)
    exact ⟨k, mem_killIdeal.2 fun n x hx => hk n x hx⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

variable {X : Scheme.{0}}

theorem pow_le_killIdeal_basicOpen {E : X.Modules} (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] (S : ℕ → Subobject E) (J₀ : X.IdealSheafData)
    (V : X.affineOpens) (m : ℕ) (hV : J₀.ideal V ^ m ≤ killIdeal D S V) (g : Γ(X, V)) :
    J₀.ideal (X.affineBasicOpen g) ^ m ≤ killIdeal D S (X.basicOpen g) := by
  have hmap : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) =
      J₀.ideal (X.affineBasicOpen g) ^ m := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl
  intro a ha
  rw [← hmap] at ha
  refine (Ideal.map_le_iff_le_comap.2 ?_ : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) ≤
    killIdeal D S (X.basicOpen g)) ha
  intro r hr
  rw [Ideal.mem_comap]
  refine mem_killIdeal.2 fun n x hx => ?_
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨e, y', hy'⟩ := qcoh_exists_res_eq (D : X.Modules) V.2 g y
  obtain ⟨z, hz⟩ := mem_killIdeal.1 (hV hr) n _ ⟨y', rfl⟩
  have key : resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y) ∈
      secs (S n) (X.basicOpen g) := by
    refine ⟨resF _ (X.basicOpen_le g) z, ?_⟩
    rw [← resF_app, hz, resF_smul, resF_app, hy', Scheme.Modules.Hom.app_smul, smul_comm]
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le g) g) := X.toRingedSpace.isUnit_res_basicOpen g
  have e2 : resO (X.basicOpen_le g) r • D.arrow.app _ y =
      ((u⁻¹ : (Γ(X, X.basicOpen g))ˣ) : Γ(X, X.basicOpen g)) ^ e •
        (resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y)) := by
    rw [smul_smul, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_smul]
  rw [e2]
  exact (secsSub (S n) (X.basicOpen g)).smul_mem _ key

theorem mem_secs_of_local {E : X.Modules} [E.IsQuasicoherent] (T : Subobject E)
    [(T : X.Modules).IsQuasicoherent] (U : X.affineOpens) (x : Γ(E, U))
    (h : ∀ p ∈ (U : X.Opens), ∃ W : X.affineOpens, p ∈ (W : X.Opens) ∧
      ∃ hW : (W : X.Opens) ≤ U, resF E hW x ∈ secs T W) :
    x ∈ secs T U := by
  choose W hpW hWU hW using h
  have h0 : (cokernel.π T.arrow).app U x = 0 := by
    refine eq_of_forall_resF (cokernel T.arrow) (fun p : (U : X.Opens) => (W p.1 p.2 : X.Opens))
      (fun p => hWU p.1 p.2) ?_ _ 0 ?_
    · intro p hp
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW p hp⟩
    · intro p
      obtain ⟨z, hz⟩ := hW p.1 p.2
      rw [resF_app, ← hz, map_zero, (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow (W p.1 p.2).2).apply_apply_eq_zero z]
  exact (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow U.2 x).1 h0

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

theorem exists_uniform_pow_kills : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent →
    ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) →
    ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) →
    ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro X _ _ E hE D hD S hS J₀ hJ
  choose mV hmV using fun V : X.affineOpens => exists_pow_le_killIdeal hE D hD S J₀ V (hJ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).isOpen) (by
      intro p _
      obtain ⟨V, hV⟩ : ∃ V : X.affineOpens, p ∈ (V : X.Opens) := by
        obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show p ∈ (⊤ : X.Opens) from trivial)
        exact ⟨⟨V, hV⟩, hpV⟩
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨t.sup mV, fun n U a ha x hx => ?_⟩
  haveI : E.IsQuasicoherent := hE.1
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI := hS n
  refine mem_secs_of_local (S n) U (a • x) fun p hpU => ?_
  obtain ⟨V, hVt, hpV⟩ : ∃ V ∈ t, p ∈ ((V : X.Opens) : Set X) := by
    simpa using ht (Set.mem_univ p)
  obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 p ⟨hpU, hpV⟩
  have hWU : X.basicOpen g ≤ (U : X.Opens) := hfg ▸ X.basicOpen_le f
  refine ⟨X.affineBasicOpen g, (show p ∈ X.basicOpen g from hfg ▸ hpf), hWU, ?_⟩
  have hVm : J₀.ideal V ^ t.sup mV ≤ killIdeal D S V :=
    (Ideal.pow_le_pow_right (Finset.le_sup hVt)).trans (hmV V)
  have hk := pow_le_killIdeal_basicOpen D S J₀ V _ hVm g
  have hWU' : X.affineBasicOpen g ≤ U := hWU
  have ha' : resO hWU a ∈ J₀.ideal (X.affineBasicOpen g) ^ t.sup mV := by
    have := Ideal.mem_map_of_mem (resO hWU) (show a ∈ J₀.ideal U ^ t.sup mV from ha)
    rw [Ideal.map_pow] at this
    exact (J₀.map_ideal hWU') ▸ this
  obtain ⟨y, rfl⟩ := hx
  have e3 := resF_smul E hWU a (D.arrow.app U y)
  erw [e3, resF_app]
  exact mem_killIdeal.1 (hk ha') n _ ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE.Globalize
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevel
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_fiber {R I J : Type} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (π : I → J) {e : I → R} (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun c : J => ∑ c' with π c' = c, e c') := by
  classical
  have hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') =
      if c = d then ∑ c' with π c' = c, e c' else 0 := by
    intro c d
    rw [Finset.sum_mul_sum]
    split_ifs with hcd
    · subst hcd
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · exact he.idem i
      · intro j _ hji
        exact he.ortho hji.symm
      · intro h; exact absurd hi h
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
      rintro rfl
      exact hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  refine ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩
  · change _ * _ = _
    rw [hmul, if_pos rfl]
  · change _ * _ = _
    rw [hmul, if_neg hcd]
  · rw [Finset.sum_fiberwise]
    exact he.complete

theorem chain_pow {M : Type} [Monoid M] {p : ℕ} {x : ℕ → M} (h : ∀ k, x (k + 1) ^ p = x k)
    (m d : ℕ) : x (m + d) ^ p ^ d = x m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem mul_sub_pow {S : Type} [CommRing S] {a x y : S} (h : a * (x - y) = 0) (q : ℕ) :
    a * (x ^ q - y ^ q) = 0 := by
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x y q
  rw [hd, ← mul_assoc, h, zero_mul]

theorem val_modEq {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (c : ZMod N) :
    c.val ≡ (ZMod.castHom h (ZMod M) c).val [MOD M] := by
  have h0 := map_natCast (ZMod.castHom h (ZMod M)) c.val
  rw [ZMod.natCast_zmod_val] at h0
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact h0.symm

variable {l : ℕ} [Fact l.Prime]

theorem sharp_xi_pow (ε : Eps l) (t : PAlg l) (m d : ℕ) :
    t.sharp (t.s (ε.e (m + d))) ^ l ^ d = t.sharp (t.s (ε.e m)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]

theorem sharp_xi_period (ε : Eps l) (t : PAlg l) (m : ℕ) :
    t.sharp (t.s (ε.e m)) ^ l ^ m = 1 := by
  have := sharp_xi_pow ε t 0 m
  rw [zero_add] at this
  rw [this]
  exact ε.sharp_e t

theorem coi_descend (ε : Eps l) (t : PAlg l) (r : ℕ → t.A) (hr : ∀ m, r (m + 1) ^ l = r m)
    {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A) (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) :
    CompleteOrthogonalIdempotents
        (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
      ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') *
        (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨coi_fiber _ he, fun c => ?_⟩
  rw [(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hπ := (Finset.mem_filter.1 hc').2
  have h1 := mul_sub_pow (hc c') (l ^ d)
  rw [← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow] at h1
  have h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val := by
    have hv := val_modEq (pow_dvd_pow l h) c'
    rw [hπ] at hv
    rw [pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]
    exact congrArg _ hv
  rwa [h2] at h1

end GlobalTheory.CompanionTheory.ContUniv
end
end

