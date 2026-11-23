module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Intertwine

variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}

end GlobalTheory.DetInv.Intertwine

namespace GlobalTheory.DetInv

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_right_cancel_lemma {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B X : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hX : X * B = 0) : X = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : X * B * B.adjugate = B.det • X := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [hX, Matrix.zero_mul] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hB

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_left_cancel_lemma_2 {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B Y : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hY : A * Y = 0) : Y = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : A.adjugate * (A * Y) = A.det • Y := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hY, Matrix.mul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hA


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.datum_scalar_intertwine : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))) ∧ D.F * D.G = _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧ (∀ l, D.G * D.ρM l = _root_.GlobalTheory.DetInv.rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) * D.Ψ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  set F := D.F with hF
  set G := D.G with hG
  set Ψ := D.Ψ with hΨ
  set Ψ' := D.Ψ' with hΨ'
  set M := D.ρM with hM
  set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ
  have hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 :=
    (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1
  have hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0 := by
    rw [hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]
    exact (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2
  have hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    have h1 := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])
    exact one_ne_zero h1
  have hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1 := D.G_mul_F
  have hFΨ : F = Ψ * F.map φ := D.F_eq
  have hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1 := D.Ψ_mul
  have hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F := fun l =>
    D.F_act l

  have hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1 := by
    have h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)

  have hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l := by
    intro l
    unfold _root_.GlobalTheory.DetInv.rhoTA
    rw [Matrix.map_map]
    congr 1
    funext x
    exact _root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x

  have hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ := by
    intro l
    have := congrArg (fun X => X.map φ) (hFT l)
    simp only [Matrix.map_mul] at this
    rwa [hTφ] at this
  have hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ := by
    intro l
    have h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT,
        Matrix.mul_assoc, ← hFΨ, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)
  refine ⟨?_, hFG, ?_, hΨM, ?_⟩
  · intro c
    have hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) =
        _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) := by
      unfold _root_.GlobalTheory.DetInv.rhoTA
      rw [AlgHom.commutes]
      ext i j
      simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 := hFT (algebraMap ℤ_[p] Λ c)
    rw [hT] at h1
    have h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0 := by
      rw [Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc,
        hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc,
        hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

abbrev TT (s : X ⟶ Sp R) : Type 1 := (IsTriv s).FullSubcategory

theorem π_bij (T : TT s) : Function.Bijective T.obj.π := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, T.obj.surj⟩
  have h := (T.obj.ker b).1 hb
  rw [T.property] at h
  exact Ideal.mem_bot.1 h

def πe (T : TT s) : T.obj.B ≃+* T.obj.B₀ := RingEquiv.ofBijective T.obj.π (π_bij T)

def pt (T : TT s) : Sp T.obj.B ⟶ X := spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) ≫ T.obj.x

theorem pt_w (T : TT s) : pt T ≫ s = algStr R T.obj.B := by
  rw [pt, Category.assoc, T.obj.w, ← spMap_comp]
  congr 1
  ext r
  exact (πe T).symm_apply_apply (algebraMap R T.obj.B r)

abbrev affF (s : X ⟶ Sp R) : AffOp X ⥤ TT s where
  obj U := ⟨Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop), rfl⟩
  map {U V} a := ⟨Thick.trivHom (hx := affPt_w s U.unop)
    (T := Thick.triv (Sec s V.unop.1) (affPt s V.unop) (affPt_w s V.unop))
    (Sec.res s (leOfHom a.unop)) (affPt_res s (leOfHom a.unop))⟩
  map_id U := by
    apply ObjectProperty.hom_ext (IsTriv s)
    apply Thick.Hom.ext'
    ext b
    exact congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U.unop.1))
  map_comp a b := by
    apply ObjectProperty.hom_ext (IsTriv s)
    apply Thick.Hom.ext'
    ext c
    exact Sec.res_res s (leOfHom a.unop) (leOfHom b.unop) c

abbrev thk (T : TT s) (p : Pair (pt T)) : TT s :=
  ⟨Thick.triv (Sec (algStr R T.obj.B) p.1.1.1) (affPt _ p.1.1 ≫ pt T)
    (by rw [Category.assoc, pt_w]; exact affPt_w _ p.1.1), rfl⟩

def secPullA (T : TT s) (p : Pair (pt T)) : Sec s p.1.2.1 →ₐ[R] Sec (algStr R T.obj.B) p.1.1.1 :=
  { secPull s (algStr R T.obj.B) p with
    commutes' := (semiHom_secPull (σ := RingHom.id R)
      (by rw [spMap_id, Category.comp_id, pt_w]) p).map_algebraMap }

def aM (T : TT s) (p : Pair (pt T)) : (affF s).obj (op p.1.2) ⟶ thk T p :=
  ⟨Thick.trivHom (hx := affPt_w s p.1.2) (T := (thk T p).obj) (secPullA T p) (secPull_affPt s _ p)⟩

theorem bM_pt (T : TT s) (p : Pair (pt T)) :
    spMap ((toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)) =
      affPt (algStr R T.obj.B) p.1.1 ≫ spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
  rw [spMap_comp, affPt_eq]
  rfl

abbrev fv (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T T' : TT s} (a : T ⟶ T') : T'.obj.B := f.1 T T' a

def bM (T : TT s) (p : Pair (pt T)) : T ⟶ thk T p :=
  ⟨{ φ := toSec R T.obj.B p.1.1
     φ₀ := (toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
     comm := fun b ↦ congrArg (toSec R T.obj.B p.1.1) ((πe T).symm_apply_apply b)
     dp := isDPMorphism_of_eq_bot _ T.property _ _
     pt := (congrArg (· ≫ T.obj.x) (bM_pt T p)).trans (Category.assoc _ _ _) }⟩

def hSec (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)) (T : TT s) (p : Pair (pt T)) :
    Sec (algStr R T.obj.B) p.1.1.1 :=
  secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)

end GlobalTheory.CechDR.AffLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullSurjectiveAndKer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR

namespace GlobalTheory.CechDR

private theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

private theorem spi {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secPull_surjective_and_ker (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by
  set J : Ideal (Sec s p.1.2.1) := I.map (algebraMap R (Sec s p.1.2.1)) with hJ
  let q := Ideal.Quotient.mk J
  have hφ : ∀ r, secPull s s₀ p (algebraMap R _ r) = algebraMap R₀ _ (π r) :=
    (semiHom_secPull hpb.w p).map_algebraMap
  have hJker : ∀ a ∈ J, secPull s s₀ p a = 0 := by
    have : J ≤ RingHom.ker (secPull s s₀ p) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [← hk, RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, hr, map_zero]
    exact fun a ha ↦ this ha
  let τ : R₀ →+* (Sec s p.1.2.1 ⧸ J) := π.liftOfSurjective hπ
    ⟨q.comp (algebraMap R _), fun r hr ↦ by
      rw [hk] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hτ : τ.comp π = q.comp (algebraMap R _) := RingHom.liftOfSurjective_comp _ _ _
  have hz : (spMap q ≫ affPt s p.1.2) ≫ s = spMap τ ≫ spMap π := by
    rw [Category.assoc, affPt_w, ← spc, ← spc, hτ]
  let w := hpb.lift _ _ hz
  have hw : w ≫ i = spMap q ≫ affPt s p.1.2 := hpb.lift_fst _ _ _
  haveI : IsOpenImmersion (affPt s₀ p.1.1) := p.1.1.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion (affPt s p.1.2) := p.1.2.2.isOpenImmersion_fromSpec
  have hr : Set.range w ⊆ Set.range (affPt s₀ p.1.1) := by
    rintro _ ⟨x, rfl⟩
    have e : Set.range (affPt s₀ p.1.1) = p.1.1.1 := p.1.1.2.range_fromSpec
    have e' : Set.range (affPt s p.1.2) = p.1.2.1 := p.1.2.2.range_fromSpec
    rw [e, ← hp]
    change i (w x) ∈ (p.1.2.1 : Set X)
    rw [← e', ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let w' := IsOpenImmersion.lift (affPt s₀ p.1.1) w hr
  have hw' : w' ≫ affPt s₀ p.1.1 = w := IsOpenImmersion.lift_fac _ _ _
  let ψ : Sec s₀ p.1.1.1 →+* (Sec s p.1.2.1 ⧸ J) := (Spec.preimage w').hom
  have hψ : spMap ψ = w' := Spec.map_preimage w'
  have h1 : ψ.comp (secPull s s₀ p) = q := by
    apply spi
    rw [← cancel_mono (affPt s p.1.2), spc, Category.assoc, secPull_affPt, hψ, ← Category.assoc,
      hw', hw]
  let ψ' := Ideal.Quotient.lift J (secPull s s₀ p) hJker
  have h2 : ψ'.comp q = secPull s s₀ p := Ideal.Quotient.lift_comp_mk _ _ _
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback hpb.flip this
  haveI : Mono (spMap (secPull s s₀ p) ≫ affPt s p.1.2) := by
    rw [secPull_affPt]; infer_instance
  haveI : Mono (spMap (secPull s s₀ p)) := mono_of_mono _ (affPt s p.1.2)
  have h3 : ψ'.comp ψ = RingHom.id _ := by
    apply spi
    rw [← cancel_mono (spMap (secPull s s₀ p)), ← spc, ← spc, RingHom.comp_assoc, h1, h2,
      RingHom.id_comp]
  refine ⟨fun b ↦ ?_, fun b ↦ ⟨fun hb ↦ ?_, hJker b⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [← h2, RingHom.comp_apply, show q a = ψ b from ha]
    exact congrArg (fun f ↦ f b) h3
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q b = 0
    rw [← h1, RingHom.comp_apply, hb, map_zero]

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SchLocExact

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map ψ (Sec.res g x) = Sec.res g (Sec.map ψ x) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  simp [Sec.res]

theorem res_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem subsingleton_of_homotopyEquiv {K L M : Cx R} (e : HomotopyEquiv K L) (n : ℤ)
    (h : Subsingleton (CohomologyClass L M n)) : Subsingleton (CohomologyClass K M n) := by
  suffices H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h0 : cpull e.inv M n (CohomologyClass.mk α) = 0 := Subsingleton.elim _ _
  have key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) =
      CohomologyClass.mk α
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩
    rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  rw [← key, h0, map_zero]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm] at h0
  exact h0

end GlobalTheory.EtC.SchLocExact


open GlobalTheory.EtC.SchLocExact in
theorem GlobalTheory.EtC.sch_loc_exact : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}),
    (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U),
    Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  intro R _ M U hU n b hb
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  have hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n) :=
    subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)
  obtain ⟨hex, -, -, -⟩ := GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)
  obtain ⟨φ, hφ⟩ := hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)
  have hφd : φ ≫ M.d n (n + 1) = 0 := by
    apply (GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1
    intro W x
    rw [map_comp, hφ, map_res, hb]
    simp [Sec.map, Sec.res]
  obtain ⟨ψ, hψ⟩ := lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd
  let a0 : Sec (M.X (n - 1)) U := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  have ha0 : Sec.map (M.d (n - 1) n) a0 = b := by
    simp only [a0]
    rw [← map_comp, hψ, hφ, res_id]
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩
  rw [map_res, ha0]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  first | (exact @GlobalTheory.EtC.tensor_loc_bij) | (exact GlobalTheory.EtC.tensor_loc_bij) | (intros; apply GlobalTheory.EtC.tensor_loc_bij  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem sep_of_factoring_cover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) := by
  intro R _ C _ C' _ F G H hcov T x hx
  obtain ⟨n, b, hb, h⟩ := hcov T
  refine Desc.sep_std (H := H) (hb := hb) x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t, v, w, rfl⟩ := h i S u hi
  rw [mp_comp, hx t v, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  first | (exact @GlobalTheory.EtC.OpComp.op_comp_bij) | (exact GlobalTheory.EtC.OpComp.op_comp_bij) | (intros; apply GlobalTheory.EtC.OpComp.op_comp_bij  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanDLiftClearDenominatorsStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_mem_smul_D_eq_sum : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  first | (exact @GlobalTheory.span_D_lift_clear_denominators) | (exact GlobalTheory.span_D_lift_clear_denominators) | (intros; apply GlobalTheory.span_D_lift_clear_denominators  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | exact GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | (intros; apply GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps <;> assumption)
end

