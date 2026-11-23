module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PosAHIsog

open GlobalTheory.PullUnifHom GlobalTheory.PullHermitian GlobalTheory.CechPic

variable {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B]

def trivUnif {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A (LB.triv A.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun _ _ => 1
  fr_hol := fun _ => differentiableOn_const 1
  fr_ne := fun _ _ _ => one_ne_zero
  fr_compat := fun i j z h => by
    simp [valAt', valAt, h]

theorem trivUnif_factor {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    IsFactorAH (trivUnif u) 0 (fun _ => 1) :=
  ⟨Matrix.isHermitian_zero, fun _ => by simp, fun l i z hz => by simp [trivUnif]⟩

theorem pull_chart_iff (φ : A ⟶ B) {L : LB B.left} {g : ℕ} (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (ex' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ B)) (hφ : ∀ z, ex z ≫ φ = ex' z)
    (j : (L.pull φ.left).ι) (z : Fin g → ℂ) :
    ⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔ ⊤ ≤ (ex' z).left ⁻¹ᵁ L.U (j PUnit.unit) := by
  have keyl : (ex z).left ≫ φ.left = (ex' z).left := by rw [← Over.comp_left, hφ]
  exact (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl]))

def pullUnif (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g) (u' : HolUnif B L g)
    (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) : HolUnif A (L.pull φ.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => u'.fr (j PUnit.unit) z
  fr_hol := fun j => (u'.fr_hol (j PUnit.unit)).mono
    (fun z hz => (pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_ne := fun j z hz => u'.fr_ne _ _ ((pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_compat := fun i j z h => by
    have keyl : (u.ex z).left ≫ φ.left = (u'.ex z).left := by rw [← Over.comp_left, hφ]
    have hi := (pull_chart_iff φ u.ex u'.ex hφ i z).1 (le_left' h)
    have hj := (pull_chart_iff φ u.ex u'.ex hφ j z).1 (le_right' h)
    show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
    rw [valAt'_pull_g' _ L _ i j h, keyl]
    exact u'.fr_compat _ _ _ (inf_of _ hi hj)

theorem pullUnif_factor (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g)
    (u' : HolUnif B L g) (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) (hΛ : u.Λ ≤ u'.Λ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (h : IsFactorAH u' Hm χ') :
    IsFactorAH (pullUnif φ u u' hφ) Hm (fun l => χ' ⟨l.1, hΛ l.2⟩) := by
  obtain ⟨h1, h3, h4⟩ := h
  exact ⟨h1, fun l => h3 _, fun l i z hz =>
    h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((pull_chart_iff φ u.ex u'.ex hφ i z).1 hz)⟩

theorem ex_nsmul {G : Over (Sp ℂ)} [GrpObj G] {g : ℕ} (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G))
    (he : ∀ z w, e (z + w) = e z * e w) (he0 : e 0 = 1) (w : Fin g → ℂ) (n : ℕ) :
    e ((n : ℂ) • w) = e w ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he, ih, pow_succ]

theorem unif_ex_zero {G : Over (Sp ℂ)} [GrpObj G] {L : LB G.left} {g : ℕ} (u : HolUnif G L g) : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

end GlobalTheory.PosAHIsog

namespace GlobalTheory.PosAHIsog

open GlobalTheory.CechPic

theorem exists_isog_principal_lam :
    ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → u.IsAH Hm χ →
    ∃ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), 1 ≤ N ∧ IsMonHom ψ ∧ IsMonHom ρ ∧
      ψ ≫ ρ = (𝟙 A) ^ N ∧ ρ ≫ ψ = (𝟙 P.A) ^ N ∧
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) := by
  intro g A _ hA M u Hm χ hM hAH
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  have hint := GlobalTheory.TorusRM.ahFactor_im_int g A M u Hm χ hM (isFactorAH_of_isAH hAH)
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd1, hf1, hEf, hbij⟩ :=
    GlobalTheory.UnimodOver.exists_unimodular_overlattice g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, -, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  haveI : IsReduced P.A.left := GlobalTheory.isReduced_of_smooth_complex _ P.A.hom P.isAb.smooth
  have hsA := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u
  have hsP := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif P.A P.isAb uB
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A P.A g hA P.isAb hsA hsP M P.L u uB
    LinearMap.id (fun x hx => hle' hx)
  obtain ⟨ρ, hρ, hρe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice P.A A g P.isAb hA hsP hsA P.L M uB u
    ((N : ℂ) • LinearMap.id) (fun x hx => by simpa using hNΛ x (hΛB ▸ hx))
  have hψe' : ∀ w, u.ex w ≫ ψ = uB.ex w := fun w => (hψe w).symm
  have hρe' : ∀ w, uB.ex w ≫ ρ = u.ex ((N : ℂ) • w) := fun w => by simpa using (hρe w).symm
  refine ⟨P, ψ, ρ, N, hN, hψ, hρ, ?_, ?_, ?_⟩
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := u.ex_onto x
    rw [← Category.assoc, hψe', hρe', comp_pow, Category.comp_id,
      ex_nsmul u.ex u.ex_add (unif_ex_zero u)]
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := uB.ex_onto x
    rw [← Category.assoc, hρe', hψe', comp_pow, Category.comp_id,
      ex_nsmul uB.ex uB.ex_add (unif_ex_zero uB)]
  · haveI := hψ
    have hM' : (P.L.pull ψ.left).IsLB := pull_isLB P.isLB _
    have hF₃ := pullUnif_factor ψ u uB hψe' hle' Hm χB (isFactorAH_of_isAH hAHB)
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
    have hamp : Out.RelAmple A H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    have hadd := _root_.GlobalTheory.TorusRM.lbIso_lam_of_add g A hA (GlobalTheory.ProjSpace.isProjOver_of_relAmple hamp) (LB.triv A.left) M (P.L.pull ψ.left) (trivUnif u) u (pullUnif ψ u uB hψe')
      0 Hm Hm (fun _ => 1) χ _ (LB.isLB_triv _) hM hM' rfl rfl (trivUnif_factor u) (isFactorAH_of_isAH hAH) hF₃
      (by rw [zero_add])
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    have hLM' : (abelian₂ A (P.L.pull ψ.left)).IsLB := LB.isLB_linComb hM' _ _
    have hLT : (abelian₂ A (LB.triv A.left)).IsLB := LB.isLB_linComb (LB.isLB_triv _) _ _
    have hD : (LB.div (abelian₂ A (P.L.pull ψ.left)) (abelian₂ A (LB.triv A.left))).IsLB := LB.isLB_div hLM' hLT
    have hR : ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left).IsLB :=
      pull_isLB (LB.isLB_linComb P.isLB _ _) _
    refine (cls_eq_iff hLM hR).1 ?_
    have e₁ : cls _ hLM' = lam (cls _ hM') (fst A A) (snd A A) := cls_cube_two hM' _ _ hLM'
    have e₂ : cls _ hLT = lam (cls _ (LB.isLB_triv A.left)) (fst A A) (snd A A) :=
      cls_cube_two (LB.isLB_triv _) _ _ hLT
    rw [(cls_eq_iff hLM hD).2 hadd, cls_div hLM' hLT hD, GlobalTheory.RealMult.Elliptic.cls_pull_lam P.isLB _ _ hR,
      e₁, e₂, cls_pull P.isLB, lam_pull]
    have h0 : cls (LB.triv A.left) (LB.isLB_triv _) = 0 := rfl
    rw [h0]
    simp [lam]

end GlobalTheory.PosAHIsog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.TorsExtend

theorem exists_section_of_isFinite {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ Sp R) [IsFinite p] (y : Sp K ⟶ Z)
    (h : y ≫ p = spMap (algebraMap R K)) : ∃ x : Sp R ⟶ Z, spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 _ := by
  first
  | exact @_root_.GlobalTheory.FactorAndSection.exists_section
  | exact _root_.GlobalTheory.FactorAndSection.exists_section
  | (apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorAndSection.exists_section <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorAndSection.exists_section ..)

theorem pow_eq_one_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (z : T ⟶ G) :
    z ^ n = 1 ↔ z.left ≫ (mulA G n).left = T.hom ≫ (η[G]).left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := by
    rw [Hom.one_def]; simp
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, ← e]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem exists_torsion_section (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n)
    {s : Sp K ⟶ Sp R} (hs : s = spMap (algebraMap R K)) (y : Over.mk s ⟶ P.A) (hy : y ^ n = 1) :
    ∃ x : baseOver (Sp R) ⟶ P.A, x ^ n = 1 ∧ spMap (algebraMap R K) ≫ x.left = y.left := by
  subst hs
  haveI := (hL.mulN _ P n hn).1
  let e : Sp R ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  obtain ⟨x, h₁, h₂⟩ := exists_section_of_isFinite (pullback.snd (mulA P.A n).left e)
    (pullback.lift y.left (spMap (algebraMap R K)) ((pow_eq_one_iff _ _ _).1 hy)) (pullback.lift_snd _ _ _)
  have h₃ : (x ≫ pullback.fst (mulA P.A n).left e) ≫ (mulA P.A n).left = e := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨Over.homMk (x ≫ pullback.fst _ _) ?_, (pow_eq_one_iff _ _ _).2 (h₃.trans (Category.id_comp _).symm), ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc, h₃]
    exact he
  · show _ ≫ x ≫ pullback.fst _ _ = _
    rw [← Category.assoc, h₁, pullback.lift_fst]

theorem torsion_section_eq (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R)) {x y : baseOver (Sp R) ⟶ P.A} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : Sp K ⟶ Sp R) (h : s ≫ x.left = s ≫ y.left) : x = y := by
  haveI := (hL.mulN _ P n hn).1
  haveI := (hL.mulN _ P n hn).2.2.2.1 (by simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  haveI : PreconnectedSpace (Sp R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  exact Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := Sp R) (mulA P.A n).left
    (((pow_eq_one_iff _ _ _).1 hx).trans ((pow_eq_one_iff _ _ _).1 hy).symm) s h)

theorem exists_labelled (hL : Laws) {R R₀ Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] [CommRing R₀] (j₀ : R₀ →+* Ω)
    (P : PolAV (Sp R₀)) (P' : PolAV (Sp R)) (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left)
    (ha : IsGrpPullback P₀.A P.A (spMap j₀) a) (ha' : IsGrpPullback P₀.A P'.A (spMap (algebraMap R Ω)) a')
    (hl : LBIso P₀.L (P.L.pull a)) (hl' : LBIso P₀.L (P'.L.pull a')) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R))
    {M : Type} [AddCommGroup M] (hM : ∀ x : M, n • x = 0) (pt : M → (baseOver (Sp R₀) ⟶ P.A))
    (add : ∀ x y, pt (x + y) = pt x * pt y)
    (bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R₀) (z : Over.mk x ⟶ P.A), z ^ n = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₀)) ≫ pt c = z) :
    ∃ pt' : M → (baseOver (Sp R) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P'.A), z ^ n = 1 →
        ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt' c = z) ∧
      (∀ x y (c₀ : R₀ˣ) (c : Rˣ), j₀ c₀ = algebraMap R Ω c → WeilIs P.A P.L n (pt x) (pt y) (unitOn c₀) →
        WeilIs P'.A P'.L n (pt' x) (pt' y) (unitOn c)) ∧
      ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap j₀ ≫ (pt x).left ∧
        w0 ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := by
  haveI := P₀.isAb.comm
  haveI := P'.isAb.proper
  have hi := IsFractionRing.injective R Ω
  have hb := GenericKTriv.pushHom_bijective ha (baseOver (Sp Ω))
  have hb' := GenericKTriv.pushHom_bijective ha' (baseOver (Sp Ω))
  let h₀ : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (spMap j₀) (by simp)
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap (algebraMap R Ω)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R Ω)) (by simp)
  have zero : pt 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have smul : ∀ (k : ℕ) x, pt (k • x) = pt x ^ k := fun k x => by
    induction k with
    | zero => rw [zero_smul, zero, pow_zero]
    | succ k ih => rw [succ_nsmul, add, ih, pow_succ]
  have tor : ∀ x, pt x ^ n = 1 := fun x => by rw [← smul, hM, zero]
  choose w hw using fun x => hb.2 (h₀ ≫ pt x)
  have torw : ∀ x, w x ^ n = 1 := fun x => hb.1 (by
    rw [map_pow, hw, map_one, ← MonObj.comp_pow, tor, MonObj.comp_one])
  have addw : ∀ x y, w (x + y) = w x * w y := fun x y => hb.1 (by
    rw [map_mul, hw, hw, hw, add, MonObj.comp_mul])
  choose pt' tor' hpt' using fun x => exists_torsion_section hL P' hn (Category.id_comp _)
    (pushHom ha' (baseOver (Sp Ω)) (w x)) (by rw [← map_pow, torw, map_one])
  have hpt : ∀ x, h ≫ pt' x = pushHom ha' (baseOver (Sp Ω)) (w x) := fun x => Over.OverMorphism.ext (hpt' x)
  have e₀ : ∀ x, (w x).left ≫ a = spMap j₀ ≫ (pt x).left := fun x => congrArg (fun q => q.left) (hw x)
  have e₁ : ∀ x, (w x).left ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := fun x => (hpt' x).symm
  let F := AlgebraicClosure Ω
  let t : Sp F ⟶ Sp Ω := spMap (algebraMap Ω F)
  let g : Over.mk (t ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (t ≫ spMap j₀) (by simp)
  have torg : ∀ x, (g ≫ pt x) ^ n = 1 := fun x => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]
  have inj : Function.Injective pt' := fun x y e => by
    have e₂ : w x = w y := hb'.1 (by rw [← hpt, ← hpt, e])
    refine (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (Over.OverMorphism.ext ?_) rfl
    show (t ≫ spMap j₀) ≫ (pt x).left = (t ≫ spMap j₀) ≫ (pt y).left
    rw [Category.assoc, Category.assoc, ← e₀, ← e₀, e₂]
  have ne : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R), (n : K) ≠ 0 := fun K _ s => by
    have := hu.map (Spec.preimage s).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have card : Nat.card M = n ^ (2 * P'.g) := by
    rw [← (hL.mulN _ P' n hn).2.2.2.2 F (t ≫ spMap (algebraMap R Ω)) (ne F (t ≫ spMap (algebraMap R Ω))),
      GenericKTriv.card_torsion ha' t rfl, ← GenericKTriv.card_torsion ha t rfl]
    refine Nat.card_eq_of_bijective (fun x => ⟨g ≫ pt x, torg x⟩) ⟨fun x y e => ?_, fun z => ?_⟩
    · exact (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (congrArg Subtype.val e) rfl
    · obtain ⟨c, hc, -⟩ := bij F (t ≫ spMap j₀) z.1 z.2
      exact ⟨c, Subtype.ext hc⟩
  refine ⟨pt', fun x y => ?_, fun K _ _ s z hz => ?_, fun x y c₀ c hc H => ?_, fun x => ⟨(w x).left, e₀ x, e₁ x⟩⟩
  · have e : h ≫ pt' (x + y) = h ≫ (pt' x * pt' y) := by
      rw [MonObj.comp_mul, hpt, hpt, hpt, addw, map_mul]
    exact over_points_ext_of_injective _ P'.A R Ω _ hi _ _ _ (congrArg (fun q => q.left) e)
  · have hc := (hL.mulN _ P' n hn).2.2.2.2 K s (ne K s)
    let Φ : M → {x : Over.mk s ⟶ P'.A // x ^ n = 1} := fun c =>
      ⟨(Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ pt' c, by
        rw [← MonObj.comp_pow, tor', MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' e =>
      inj (torsion_section_eq hL P' hn hu (tor' c) (tor' c') s (congrArg (fun q => q.1.left) e))
    have : Finite {x : Over.mk s ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    obtain ⟨c, e⟩ := (hΦ.bijective_of_nat_card_le (by rw [hc, card])).2 ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val e, fun c' e' => hΦ ((Subtype.ext e').trans e.symm)⟩
  · refine MumPair.weilIs_of_spread Ω R _ hi P₀ P' a' ha' hl' n (w x) (w y) _ _ c hn (e₁ x) (e₁ y) (tor' x) (tor' y) ?_
    have H₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h₀ H
    have H₂ := (weilIs_grpPullback_of_comm' (Sp R₀) (Sp Ω) P.A P₀.A (spMap j₀) a P.L P₀.L P.isLB P₀.isLB ha hl
      (baseOver (Sp Ω)) n (w x) (w y) (h₀ ≫ pt x) (h₀ ≫ pt y) _ (e₀ x).symm (e₀ y).symm).2 H₁
    have e := SpreadLevel.appTop_unitOn j₀ c₀ (Units.map (algebraMap R Ω).toMonoidHom c) hc
    exact e ▸ H₂

theorem isIntegrallyClosed_ringOn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
    IsIntegrallyClosed (M.ringOn U) := by
  haveI := RatModel.isFractionRing_ringOn hU hne
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => ?_⟩, rfl⟩
  have := RatModel.isIntegrallyClosed_O hM z
  letI : Algebra (M.ringOn U) (M.O z) := (Subalgebra.inclusion (RatModel.ringOn_le_O hz)).toRingHom.toAlgebra
  haveI : IsScalarTower (M.ringOn U) (M.O z) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := M.O z))
  exact hy ▸ y.2

theorem exists_labelled_on_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  intro g n F W Z i X₁ U P' P₀ a a' hU hne ha ha' hl hl'
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := isIntegrallyClosed_ringOn X₁.M ((isNormalScheme_iff_pred _).1 X₁.normal) hU hne
  haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : IsNoetherianRing (X₁.M.ringOn U) := isNoetherianRing_of_fg (fg_ringOn_of_isAffineOpen _ _ X₁.M U hU hne)
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (le_trans one_le_two X₁.S.N_ge)
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : X₁.M.ringOn U) := by
    have := X₁.S.unit.map (algebraMap X₁.o₁ (X₁.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', h₁, h₂, h₃, h₄⟩ := exists_labelled hL X₁.S.R.val.toRingHom X₁.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X₁.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.pt_bij
  refine ⟨pt', h₁, h₂, fun x y c hc => ?_, h₄⟩
  obtain ⟨c₀, hc₀⟩ := ((X₁.S.prim.isUnit (by positivity)).pow (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)).map
    (algebraMap X₁.o₁ X₁.S.R)
  refine h₃ x y c₀ c ?_ (X₁.ρ.weil x y c₀ hc₀)
  rw [hc₀, hc]
  rfl

end GlobalTheory.Poinc.TorsExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebung
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem frobProj_frobTwist_app {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (x : (frobTwist h G).A n) :
    ((frobProj h G).frobTwist h h).app n x = (frobProj h (frobTwist h G)).app n x := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj]

private theorem frobProj_app_verschiebung {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    (frobProj h (frobTwist h G)).app n ((verschiebung h G).app n a) =
      (verschiebung h (frobTwist h G)).app n ((frobProj h G).app n a) := by
  refine Test.mulP_injective (frobTwist h (frobTwist h G)) n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app,
    mulP_res, mulP_res, ← map_mulBy, ← SemiBialgHom.map_mulBy ((frobProj h G).app (n + 1)),
    ← relFrob_app_verschiebung_app h G, frobProj_app_relFrob_app,
    ← relFrob_app_frobProj h (G := frobTwist h G) (n + 1),
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

theorem pow_char_eq_zero_of_verschiebung (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n))
    (hχ : ∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) : χ ^ p = 0 := by
  refine CartierDual.ext_apply fun y => ?_
  induction y using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  | h1 r a =>
    rw [map_smul, ← frobTwistDual_verschiebung h (G := frobTwist h G) n χ,
      ← frobProj_app_verschiebung h G,
      frobTwistDual_frobProj, hχ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]
    rfl

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_restrict : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hf y hy E' hE'
  have e := functionFieldMap_comp_constFn p f
  have hc : ∀ a, functionFieldMap f (Cartier.constFn p a) ∈ E'.ring := fun a => by
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  obtain ⟨z, hzy, hz⟩ := GlobalTheory.T.exists_specializes_dominatesStalk_of_regular M E'.ring y hE'
  have hzU : z ∈ U := hzy.mem_open U.isOpen hy
  have hfin := GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' M W f U hf ⟨y, hy⟩
  have hess' : ((functionFieldMap f).comp (Cartier.constFn p)).codRestrict E'.ring hc =
      (Cartier.constFn (f ≫ p)).codRestrict E'.ring E'.const_mem :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  obtain ⟨hdvr, hess⟩ := GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex W.functionField M.functionField (functionFieldMap f)
    (Cartier.constFn p) hfin E'.ring hc (hess' ▸ E'.essFiniteType)
  let E : DivOver p := ⟨E'.ring.comap (functionFieldMap f), hc, hdvr, hess⟩
  haveI : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap f)) := hdvr
  have hun := GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk M W f U hf z hzU E'.ring hz
  let ψ : E.ring →+* E'.ring := (functionFieldMap f).restrict E.ring E'.ring fun _ hx => hx
  letI := ψ.toAlgebra
  have hψ : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  have hft : Algebra.EssFiniteType E.ring E'.ring := by
    have h1 : (ψ.comp E.const).EssFiniteType := hψ ▸ E'.essFiniteType
    exact RingHom.EssFiniteType.of_comp E.const h1
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr W.functionField M.functionField (functionFieldMap f) E'.ring ⟨hun, hft⟩ g g.ne_zero
  refine ⟨E, fun g ⟨a, ha⟩ => ?_, hord, fun η hη => ?_⟩
  · show functionFieldMap f g ∈ E'.ring
    exact hE' _ ⟨f.stalkMap y a, by rw [← functionFieldMap_algebraMap, ha]⟩
  · haveI := SmoothOfRelativeDimension.smooth n p
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
    have hnW : topologicalKrullDim W = n := NadelApp.topologicalKrullDim_eq_of_smooth W p n
    have hnM : topologicalKrullDim M = n := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
    obtain ⟨ω, hω, g, rfl, hg⟩ := E.isFormOrd_formOrd hnW hη
    have hω' := GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified E.const E'.const ψ hψ n hun ω hω (E'.exists_isFreeGen hnM)
    have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      have h1 := formMap_formMap (D := n) E.ring.subtype (functionFieldMap f)
        ((functionFieldMap f).comp E.ring.subtype) rfl rfl e
        (by rw [RingHom.comp_assoc]; exact e) ω
      have h2 := formMap_formMap (D := n) ψ E'.ring.subtype
        ((functionFieldMap f).comp E.ring.subtype) rfl hψ rfl
        (by rw [RingHom.comp_assoc]; exact e) ω
      exact h1.trans h2.symm
    have hpull : ratPull p f n ((g : W.functionField) • E.toRat n ω) =
        ((Units.map (functionFieldMap f).toMonoidHom g : M.functionFieldˣ) : M.functionField) •
          E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      rw [map_smulₛₗ, key]; rfl
    have hne : ratPull p f n ((g : W.functionField) • E.toRat n ω) ≠ 0 := by
      rw [hpull]
      refine smul_ne_zero (Units.ne_zero _) fun h0 => ?_
      have := (E'.isFreeGen_toRat hω').1 (a₁ := 0) (a₂ := 1) (by simp [h0])
      exact zero_ne_one this
    change E'.formOrd (ratPull p f n ((g : W.functionField) • E.toRat n ω)) =
      E.formOrd ((g : W.functionField) • E.toRat n ω)
    rw [← hg, ← hord g]
    exact DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', _, hpull, rfl⟩

end GlobalTheory.EtaleKlt
end
end

