module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0453
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimplicialCochainRepresentingClassAcyclicLStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simplicialCochain_representing_class_acyclicLevels :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
      (∀ k m : ℕ, 0 < m → k + m = n →
        ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk k)))) F m, y = 0) →
      ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
        GlobalTheory.EtC.cobd (R := R) s = 0 ∧ GlobalTheory.EtC.IsCls (R := R) s x := by
  intro R _ F E n hyp x
  obtain ⟨z, rfl, hv⟩ := GlobalTheory.EtC.LeraySurj.reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ :=
    _root_.GlobalTheory.EtC.res_basic R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  have hcobd : GlobalTheory.EtC.cobd (R := R) u =
      (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (chainsXIso R E n).hom ≫ u := by
    rw [GlobalTheory.EtC.LeraySurj.chains_d_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp]
    rfl
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [hcobd]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫
        resι R F = 0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSection
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

noncomputable section

namespace GlobalTheory.SpecField

open AlgebraicGeometry

variable {A : Type} [CommRing A]

theorem dualMap_fst {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).fst = f x.fst := by
  simp [Formalism.L2.Pj.dualMap]

theorem dualMap_snd {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).snd = f x.snd := by
  simp [Formalism.L2.Pj.dualMap]

variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)

def liftLoc : LocalizedModule S A →+* DualNumber (LocalizedModule S A) :=
  IsLocalization.lift (M := S) (g := (Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A))).comp σ)
    (fun y => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, RingHom.comp_apply, dualMap_fst, hσ]
      exact IsLocalization.map_units _ y)

theorem liftLoc_algebraMap (a : A) :
    liftLoc σ hσ S (algebraMap A _ a) = Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A)) (σ a) :=
  IsLocalization.lift_eq _ _

theorem liftLoc_fst (b : LocalizedModule S A) : (liftLoc σ hσ S b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom (LocalizedModule S A) (LocalizedModule S A) (LocalizedModule S A)).toRingHom.comp
      (liftLoc σ hσ S)) = RingHom.id _ :=
    IsLocalization.ringHom_ext S (RingHom.ext fun a => by
      simp [liftLoc_algebraMap, dualMap_fst, hσ])
  exact congrArg (fun φ => φ b) h

def dloc (b : LocalizedModule S A) : LocalizedModule S A := (liftLoc σ hσ S b).snd

theorem dloc_add (b b' : LocalizedModule S A) : dloc σ hσ S (b + b') = dloc σ hσ S b + dloc σ hσ S b' := by
  simp [dloc]

theorem dloc_mul (b b' : LocalizedModule S A) :
    dloc σ hσ S (b * b') = b * dloc σ hσ S b' + b' * dloc σ hσ S b := by
  simp only [dloc, map_mul, TrivSqZeroExt.snd_mul, liftLoc_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem dloc_algebraMap (a : A) : dloc σ hσ S (algebraMap A _ a) = algebraMap A _ (σ a).snd := by
  simp [dloc, liftLoc_algebraMap, dualMap_snd]

theorem mk_mul_algebraMap (m : A) (u : S) :
    LocalizedModule.mk m u * algebraMap A (LocalizedModule S A) u = algebraMap A _ m := by
  rw [show algebraMap A (LocalizedModule S A) u = LocalizedModule.mk (u : A) 1 from rfl]
  erw [LocalizedModule.mk_mul_mk]
  rw [show algebraMap A (LocalizedModule S A) m = LocalizedModule.mk m 1 from rfl, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]; ring⟩

theorem dloc_mk (r : A) (t : S) :
    dloc σ hσ S (LocalizedModule.mk r t) =
      LocalizedModule.mk (t * (σ r).snd - r * (σ t).snd) (t * t) := by
  have h1 := mk_mul_algebraMap S r t
  have h2 := congrArg (dloc σ hσ S) h1
  rw [dloc_mul, dloc_algebraMap, dloc_algebraMap] at h2
  have hu : IsUnit (algebraMap A (LocalizedModule S A) ((t * t : S) : A)) := IsLocalization.map_units _ (t * t)
  refine (hu.mul_left_inj).1 ?_
  rw [mk_mul_algebraMap]
  simp only [Submonoid.coe_mul, map_mul, map_sub]
  linear_combination (algebraMap A (LocalizedModule S A) t) * h2 -
    (algebraMap A (LocalizedModule S A) (σ t).snd) * h1

def dsec (O : (Sp A).Opens) (s : Γ(Sp A, O)) : Γ(Sp A, O) :=
  ⟨fun x => dloc σ hσ _ (s.1 x), fun x => by
    obtain ⟨V, hxV, i, r, t, w⟩ := s.2 x
    refine ⟨V, hxV, i, t * (σ r).snd - r * (σ t).snd, t * t, fun y => ?_⟩
    obtain ⟨ht, hs⟩ := w y
    refine ⟨fun h => ((PrimeSpectrum.isPrime (y.1 : PrimeSpectrum A)).mem_or_mem h).elim ht ht, ?_⟩
    exact (congrArg (dloc σ hσ _) hs).trans (dloc_mk σ hσ _ r ⟨t, ht⟩)⟩

theorem isField_dsec : IsField ⊤ (dsec σ hσ) :=
  ⟨fun _ _ f f' => Subtype.ext (funext fun x => dloc_add σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ f f' => Subtype.ext (funext fun x => dloc_mul σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ _ _ _ => rfl⟩

theorem dsec_top (a : A) :
    dsec σ hσ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  Subtype.ext (funext fun x => dloc_algebraMap σ hσ _ a)

end GlobalTheory.SpecField

theorem GlobalTheory.SpecField.exists_isField (A : Type) [CommRing A] (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) :
    ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧
      ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  ⟨GlobalTheory.SpecField.dsec σ hσ, GlobalTheory.SpecField.isField_dsec σ hσ, GlobalTheory.SpecField.dsec_top σ hσ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
  obtain ⟨hNL, hLstd⟩ := hL
  have hLint : ∀ v ∈ L, ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := fun v hv i =>
    (Submodule.mem_pi.1 (hLstd hv)) i (Set.mem_univ i)
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hsingle : ∀ i, Pi.single i (N : F) ∈ L := by
    intro i
    have hstd : (Pi.single i (1 : F) : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.stdLat F := by
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simpa using (1 : Submodule (𝓞 F) F).one_le.1 le_rfl
      · simp [hj]
    have := hNL _ hstd
    convert this using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Algebra.smul_def]
    · simp [hj]
  let B0 : Submodule (𝓞 F) F := L.map (LinearMap.proj (R := 𝓞 F) (φ := fun _ : Fin 2 => F) 0)
  let C0 : Submodule (𝓞 F) F := L.comap (LinearMap.single (𝓞 F) (fun _ : Fin 2 => F) 1)
  have hB0 : B0 ≤ 1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hLint v hv 0
  have hC0 : C0 ≤ 1 := by
    intro c hc
    simpa using hLint _ hc 1
  let Bf : FractionalIdeal (𝓞 F)⁰ F := ⟨B0, FractionalIdeal.isFractional_of_le_one B0 hB0⟩
  let Cf : FractionalIdeal (𝓞 F)⁰ F := ⟨C0, FractionalIdeal.isFractional_of_le_one C0 hC0⟩
  have hBne : Bf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Bf := by
      show (N : F) ∈ B0
      exact ⟨_, hsingle 0, by simp⟩
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have hCne : Cf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Cf := by
      show Pi.single 1 (N : F) ∈ L
      exact hsingle 1
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have key : ∀ t ∈ (Bf : Submodule (𝓞 F) F) * ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
      ∃ y : F, ∀ b ∈ Bf, (![t * b, y * b] : Fin 2 → F) ∈ L := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b' hb' c hc
      obtain ⟨w, hw, hw0⟩ := (show b' ∈ B0 from hb')
      refine ⟨c * w 1, fun b hb => ?_⟩
      have hcb : c * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← inv_mul_cancel₀ hBne]
        exact FractionalIdeal.mul_mem_mul hc hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hcb
      convert L.smul_mem r hw using 1
      ext i
      fin_cases i
      · simp [Algebra.smul_def, hr, ← hw0]
        ring
      · simp [Algebra.smul_def, hr]
        ring
    · rintro t₁ t₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
      refine ⟨y₁ + y₂, fun b hb => ?_⟩
      convert L.add_mem (hy₁ b hb) (hy₂ b hb) using 1
      ext i
      fin_cases i <;> simp <;> ring
  have h1 : (1 : F) ∈ (Bf : Submodule (𝓞 F) F) *
      ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hBne]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨x, hx⟩ := key 1 h1
  refine ⟨Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne),
    Units.mk0 Bf hBne, x, ?_⟩
  have hlat : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne)) = Cf := by
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, Units.val_mk0, FractionalIdeal.dual_dual]
  ext v
  unfold _root_.GlobalTheory.HilbFam.split
  rw [Submodule.mem_mk]
  change v ∈ L ↔ v 0 ∈ ((Units.mk0 Bf hBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne))
  rw [hlat, Units.val_mk0]
  change v ∈ L ↔ v 0 ∈ B0 ∧ Pi.single 1 (v 1 - v 0 * x) ∈ L
  constructor
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    convert L.sub_mem hv (hx (v 0) ⟨v, hv, rfl⟩) using 1
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨hb, hc⟩
    convert L.add_mem (hx (v 0) hb) hc using 1
    ext i
    fin_cases i <;> simp <;> ring

end GlobalTheory.HilbFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  first | (exact @GlobalTheory.EtC.TrGal.exists_trace_galois) | (exact GlobalTheory.EtC.TrGal.exists_trace_galois) | (intros; apply GlobalTheory.EtC.TrGal.exists_trace_galois  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldAffineOpenTransport
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

namespace GlobalTheory.FieldTransport

theorem exists_isField_transport : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  intro Z W hW δ d' hd hδ
  classical
  have hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O) := fun O h =>
    hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])
  let e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O) := fun O h =>
    haveI := hiso O h; (asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv
  have he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f := fun _ _ _ => rfl
  have hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)),
      (hW.fromSpec.app O').hom (resG Z h f) =
        resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f) := by
    intro O O' h f
    have := congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)
    simpa [resG] using this
  refine ⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro O h f f'
    simp only [dif_pos h, map_add (f := _), hd.1 _ le_top]
  · intro O h f f'
    simp only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add (f := _), RingEquiv.symm_apply_apply]
  · intro O O' h hO f
    have hO' : O' ≤ W := h.trans hO
    simp only [dif_pos hO, dif_pos hO']
    apply (e O' hO').injective
    simp only [RingEquiv.apply_symm_apply, he O' hO', hres]
    rw [← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]
    exact (e O' hO').apply_symm_apply _
  · intro a
    simp only [dif_pos (le_refl W)]
    apply (e W (le_refl W)).symm_apply_eq.mpr
    have hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤ := le_top
    have key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x) := by
      intro x
      rw [he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
      rfl
    rw [key, key, hd.2.2 _ _ hs le_rfl, hδ]

end GlobalTheory.FieldTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInvStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair), IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa → IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb → ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟 → nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by
  first | exact @GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | exact GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | (intros; apply GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.MVFree

theorem shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  intro R _ A A' _ _ _ _ f hN w
  obtain ⟨h1, h2⟩ := hN
  obtain ⟨w', hex⟩ := GlobalTheory.T.etale_mayerVietoris_free_sequence_exact R A A' f h1 h2
  have hm := GlobalTheory.T.mono_free_etale_mayerVietoris_left_map R A A' f
  have he := GlobalTheory.T.etaleMayerVietoris_free_right_epi R A A' f h1 h2
  exact { exact := hex, mono_f := hm, epi_g := he }

end GlobalTheory.EtC.MVFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosureStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k)))) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  first | (exact @GlobalTheory.EtC.GalSec.gal_sec) | (exact GlobalTheory.EtC.GalSec.gal_sec) | (intros; apply GlobalTheory.EtC.GalSec.gal_sec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
section
noncomputable section

open NumberField

namespace GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def hmon (n : ℤ) (z : ℂ) : ℂ := if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ (-n).toNat

def gauss (n : I → ℤ) (w : I → ℂ) : ℂ :=
  ∏ i, hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)

def dil (y : I → ℝ) (v : I → ℂ) : I → ℂ := fun i => (Real.exp (y i / 2) : ℂ) * v i

def theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (y : I → ℝ) : ℂ :=
  ∑' j, a j * gauss n (dil y (e j))

def emb {K : Type} [Field K] (φ : I → K →+* ℂ) (α : K) : I → ℂ := fun i => φ i α

def ulog {K : Type} [Field K] [NumberField K] (φ : I → K →+* ℂ) (u : (𝓞 K)ˣ) : I → ℝ :=
  fun i => Real.log (‖φ i ((u : 𝓞 K) : K)‖ ^ 2)

theorem hmon_zero {n : ℤ} (hn : n ≠ 0) : hmon n 0 = 0 := by
  unfold hmon
  split_ifs with h
  · rw [map_zero]; exact zero_pow (by omega)
  · exact zero_pow (by omega)

theorem gauss_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) : gauss n 0 = 0 := by
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hmon_zero hi])

theorem norm_hmon (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by
  unfold hmon
  split_ifs with h
  · rw [norm_pow, Complex.norm_conj]; congr 1; omega
  · rw [norm_pow]; congr 1; omega

end GlobalTheory.HeckeTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductShintaniLiftGaloisStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProduct_shintaniLift_galois : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) → ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) = J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  first | (exact @GlobalTheory.Shin.J_liftL_galAct) | (exact GlobalTheory.Shin.J_liftL_galAct) | (intros; apply GlobalTheory.Shin.J_liftL_galAct <;> assumption)
end

