module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAlgebraMap
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctions
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GrSpec

open Polynomial HomogeneousLocalization

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)

theorem coe_hel_pow {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) :
    ((hel hN k b hb ^ n : ring hN) : F[X]) = monomial (k * n) (b ^ n) := by
  rw [SubmonoidClass.coe_pow, coe_hel, monomial_pow]

theorem hel_pow_mem {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : hel hN k b hb ^ n ∈ piece hN (k * n) := by
  have := SetLike.pow_mem_graded n (hel_mem hN k b hb)
  rwa [smul_eq_mul, mul_comm] at this

theorem isUnit_mk_iff (P : Ideal (ring hN)) [P.IsPrime] (g : NumDenSameDeg (piece hN) P.primeCompl) :
    IsUnit (mk g : AtPrime (piece hN) P) ↔ (g.num : ring hN) ∉ P := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem affine {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) : IsAffineOpen (Dp hN k b) := by
  rw [Dp_of_mem hN hb]
  exact Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)

theorem cover (z : Proj (piece hN)) : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp hN k b := by
  classical
  obtain ⟨y, hy, hyz⟩ := Set.not_subset.1 z.not_irrelevant_le
  have : ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal := by
    by_contra hc
    push_neg at hc
    apply hyz
    rw [← DirectSum.sum_support_decompose (piece hN) y]
    exact Ideal.sum_mem _ fun j _ => hc j
  obtain ⟨j, hj⟩ := this
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hj
    have : (DirectSum.decompose (piece hN) y 0 : ring hN) = 0 := by
      rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy
    rw [this]; exact zero_mem _
  set c := DirectSum.decompose (piece hN) y j
  have hb : ((c : ring hN) : F[X]).coeff j ∈ N j := (c : ring hN).2 j
  refine ⟨j, by omega, _, hb, ?_⟩
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen]
  have : hel hN j _ hb = (c : ring hN) := Subtype.ext ((mem_piece_iff hN).1 c.2).symm
  rw [this]; exact hj

theorem ideal_gen [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) :
    (genericPoint (Proj (piece hN))).asHomogeneousIdeal = ⊥ :=
  le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2
    (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))

theorem genMem [IsIntegral (Proj (piece hN))] (h : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) {k : ℕ} {b : F} (hb : b ∈ N k) :
    genericPoint (Proj (piece hN)) ∈ Dp hN k b ↔ b ≠ 0 := by
  obtain ⟨k', hk', b', hb', h0'⟩ := h
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']
  change ¬ (hel hN k b hb = 0) ↔ _
  rw [not_iff_not, Subtype.ext_iff]
  simp

theorem hel_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k} (n : ℕ)
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : hel hN k b hb ^ n ∉ z.asHomogeneousIdeal.toIdeal :=
  fun h => hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

theorem ne_zero_of_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k}
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : b ≠ 0 := by
  rintro rfl
  apply hz
  have : hel hN k 0 hb = 0 := Subtype.ext (by simp)
  rw [this]; exact zero_mem _

theorem mem [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (z : Proj (piece hN))
    (hz : z ∈ Dp hN k b) {l : ℕ} {a : F} (ha : a ∈ N l) :
    z ∈ Dp hN l a ↔ ∃ v, UnitAt z v ∧ psi hN v = a ^ k / b ^ l := by
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen] at hz
  rw [Dp_of_mem hN ha, Proj.mem_basicOpen]
  have hfz := hel_notMem hN l hz
  have hb0 := ne_zero_of_notMem hN hz
  constructor
  · intro hg
    let nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl :=
      ⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩
    refine ⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩
    · exact ((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm
    · refine (psi_algebraMap hN z _).trans ?_
      erw [RingEquiv.apply_symm_apply]
      rw [psiAt_mk]
      simp only [nd, coe_hel_pow, coeff_monomial, Finsupp.single_apply, mul_comm k l, ↓reduceIte]
  · rintro ⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg
    rw [psi_algebraMap] at hv
    obtain ⟨g, hg'⟩ := mk_surjective (Proj.stalkIso' (piece hN) z w)
    rw [← hg', psiAt_mk] at hv
    have hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal) := by
      rw [hg']; exact hwu.map (Proj.stalkIso' (piece hN) z)
    rw [isUnit_mk_iff] at hu
    have hnum := (mem_piece_iff hN).1 g.num.2
    have hden := (mem_piece_iff hN).1 g.den.2
    have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
      intro h0
      apply g.den_mem
      have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
      rw [this]; exact zero_mem _
    have key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN) := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial,
        monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]
      congr 1
      rw [div_eq_div_iff hs (pow_ne_zero _ hb0)] at hv
      exact hv
    have : (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal := by
      rw [key]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
    · exact hu h
    · exact hfz h

def fracAt {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F} (ha : a ∈ N (k * m)) (x : Proj (piece hN))
    (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) : NumDenSameDeg (piece hN) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨k * m, ⟨hel hN (k * m) a ha, hel_mem hN _ _ ha⟩, ⟨_, hel_pow_mem hN hb m⟩, hel_notMem hN m hx⟩

theorem psi_fracAt [IsIntegral (Proj (piece hN))] {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F}
    (ha : a ∈ N (k * m)) (x : Proj (piece hN)) (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) :
    psi hN (algebraMap ((Proj (piece hN)).presheaf.stalk x) _
      ((Proj.stalkIso' (piece hN) x).symm (mk (fracAt hN hb m ha x hx)))) = a / b ^ m := by
  refine (psi_algebraMap hN x _).trans ?_
  erw [RingEquiv.apply_symm_apply]
  rw [psiAt_mk]
  simp only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, Finsupp.single_eq_same]

theorem ringChar [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (hb0 : b ≠ 0) (u : F) :
    (∃ v, (∀ z ∈ Dp hN k b, RegAt z v) ∧ psi hN v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m := by
  have h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0 := ⟨k, hk, b, hb, hb0⟩
  have hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b := (genMem hN h1 hb).2 hb0
  rw [Dp_of_mem hN hb] at hgen ⊢
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := exists_fnOf_eq hgen hv
    obtain ⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by
      refine ⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩
      rw [← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]
      exact (Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s
    obtain ⟨nd, rfl⟩ := mk_surjective y
    obtain ⟨m, hm⟩ := nd.den_mem
    have hdeg : nd.deg = k * m := by
      have hne : (nd.den : ring hN) ≠ 0 := by
        rw [← hm]; exact pow_ne_zero _ (hel_ne_zero hN hb hb0)
      exact DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne
    refine ⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩
    change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen
      (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _
    erw [Proj.stalkIso'_germ]
    have key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤
        (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl),
        psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) =
          ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg := by
      intro h
      exact psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩
    refine (key _).trans ?_
    rw [← hm, coe_hel_pow, coeff_monomial]
    have he : (Finsupp.single (k * m) (b ^ m)) nd.deg = b ^ m := by
      rw [hdeg, Finsupp.single_eq_same]
    rw [he]
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans
      (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩

def gR : CommRingCat.of R ⟶ Γ(Proj (piece hN), ⊤) :=
  CommRingCat.ofHom ((fromZeroRingHom (piece hN) _).comp (toZero hN)) ≫ Proj.awayToSection (piece hN) 1 ≫
    (Proj (piece hN)).presheaf.map (homOfLE (Proj.basicOpen_one (piece hN)).ge).op

def pstr : Proj (piece hN) ⟶ Sp R := (Proj (piece hN)).toSpecΓ ≫ Spec.map (gR hN)

theorem sep : IsSeparated (pstr hN) := inferInstance

theorem const [IsIntegral (Proj (piece hN))] : (psi hN).comp (cst (pstr hN)) = c₀ := by
  ext r
  have hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1 := by
    rw [Proj.basicOpen_one]; trivial
  have e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN := by
    rw [pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  change psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r
  rw [e0]
  change psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge
    (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r
  rw [fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg
      (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _
  erw [Proj.stalkIso'_germ]
  refine (psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_
  · exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)
  · simp [toZero]

end GlobalTheory.Desc.GrSpec

namespace GlobalTheory.Desc

theorem exists_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F),
    GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R)
      (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  intro R F _ _ _ c₀ N hN h
  obtain ⟨k₀, hk₀, b₀, hb₀, h₀⟩ := h
  haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀
  refine ⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩
  exact
    { sep := GrSpec.sep hN
      const := GrSpec.const hN
      affine := fun k hk b hb => GrSpec.affine hN hk hb
      cover := GrSpec.cover hN
      gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb
      ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u
      mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem padd_eq {T : Over (Sp ℂ)} (a b : T ⟶ A) : padd A a b = a * b := (Hom.mul_def a b).symm

theorem pzero_eq (T : Over (Sp ℂ)) : pzero A T = 1 := by
  rw [pzero, Hom.one_def]

theorem pt_diag_psum (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (I : Finset (Fin 2)) :
    y ≫ (lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I) = y ^ I.card := by
  have h0 : y ≫ lift (𝟙 A) (𝟙 A) ≫ fst A A = y := by simp
  have h1 : y ≫ lift (𝟙 A) (𝟙 A) ≫ snd A A = y := by simp
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd_eq, pzero_eq, x2, List.finRange_succ, comp_mul, comp_one, h0, h1, pow_two]

theorem sum_exp_sq :
    (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) = 2 := by
  have hZ : (∑ I : Finset (Fin 2), ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2) = 2 := by decide
  have hU : (∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) * (I.down.card : ℤ) ^ 2) = 2 :=
    (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2)
      (fun _ => rfl)).trans hZ
  exact_mod_cast hU

theorem herm_smul_nat {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℕ) (z l : Fin g → ℂ) :
    ((c : ℂ) • z) ⬝ᵥ Hm.mulVec (star ((c : ℂ) • l)) = (c : ℂ) ^ 2 * (z ⬝ᵥ Hm.mulVec (star l)) := by
  have hs : star ((c : ℂ) • l) = (c : ℂ) • star l := by
    rw [star_smul]; simp
  rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def diagSum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : ULift.{0} (Finset (Fin 2))) : A ⟶ A :=
  lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I.down

theorem chart (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (J PUnit.unit I) := by
  rw [GlobalTheory.ThetaPoint.top_le_pull_iff]
  show ⊤ ≤ (x ≫ (lift (𝟙 A) (𝟙 A)).left) ⁻¹ᵁ
      LB.wchart M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) (J PUnit.unit) ↔ _
  refine (CubeValues.le_preimage_wchart _ M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left)
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι)).trans ?_
  simp only [diagSum, Over.comp_left, Category.assoc]

theorem chart' (M : LB A.left) (x : Sp ℂ ⟶ A.left) (j : ULift.{0} (Finset (Fin 2)) → M.ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ LB.wchart M (fun I => (diagSum A I).left) j ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (j I) :=
  CubeValues.le_preimage_wchart _ _ _ _

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def expo (I : ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - I.down.card)

theorem val_g (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J J' : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι)
    (h : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J)
    (h' : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J') :
    valAt' x (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ⊓ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J')
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).g J J').val =
      valAt' x ((M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) ⊓
          (M.LinComb (fun I => (diagSum A I).left) expo).U (J' PUnit.unit))
        ((M.LinComb (fun I => (diagSum A I).left) expo).g (J PUnit.unit) (J' PUnit.unit)).val := by
  refine (GlobalTheory.ThetaPoint.valAt'_pull_g _ _ _ _ _ h h').trans ?_
  have hL := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h
  have hL' := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h'
  have hc := (chart' M x (J PUnit.unit)).2 ((chart M x J).1 h)
  have hc' := (chart' M x (J' PUnit.unit)).2 ((chart M x J').1 h')
  refine (CubeValues.val_linComb (x ≫ (lift (𝟙 A) (𝟙 A)).left) valAt'_rules M
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) expo
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) (J' PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) hL hL').trans ?_
  refine Eq.trans ?_ (CubeValues.val_linComb x valAt'_rules M (fun I => (diagSum A I).left) expo _ _ hc hc').symm
  simp only [diagSum, Over.comp_left, Category.assoc]

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

def mulCard (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ((I.down.card : ℕ) : ℂ) • LinearMap.id

theorem mulCard_apply (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    mulCard g I z = ((I.down.card : ℕ) : ℂ) • z := rfl

theorem ex_mulCard (u : HolUnif A M g) (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    u.ex (mulCard g I z) = u.ex z ≫ diagSum A I := by
  rw [mulCard_apply, Nat.cast_smul_eq_nsmul, holUnif_ex_nsmul_eq_pow]
  exact (pt_diag_psum (u.ex z) I.down).symm

theorem smul_mem_lat (u : HolUnif A M g) (l : u.Λ) (I : ULift.{0} (Finset (Fin 2))) :
    ((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ) ∈ u.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem l.2 _

def diagUnif (u : HolUnif A M g) : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g :=
  let u₁ := linCombUnif u u (diagSum A) (mulCard g) expo (ex_mulCard u)
  have hc : ∀ (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ),
      (⊤ : (Sp ℂ).Opens) ≤ (u.ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J →
      (⊤ : (Sp ℂ).Opens) ≤ (u₁.ex z).left ⁻¹ᵁ (M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) :=
    fun J z hz => (chart' M _ (J PUnit.unit)).2 ((chart M _ J).1 hz)
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun J z => u₁.fr (J PUnit.unit) z
    fr_hol := fun J => (u₁.fr_hol (J PUnit.unit)).mono fun z hz => hc J z hz
    fr_ne := fun J z hz => u₁.fr_ne _ z (hc J z hz)
    fr_compat := fun J J' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      rw [val_g M _ J J' h1 h2]
      exact u₁.fr_compat _ _ z ((top_le_preimage_inf _ _ _).2 ⟨hc J z h1, hc J' z h2⟩) }

theorem diagUnif_fr (u : HolUnif A M g) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ) :
    (diagUnif u).fr J z = ∏ I, u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I := rfl

theorem diagUnif_ex (u : HolUnif A M g) : (diagUnif u).ex = u.ex := rfl

def diagChar (u : HolUnif A M g) (χ : u.Λ → ℂ) (l : u.Λ) : ℂ :=
  ∏ I, χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

theorem isFactorAH_diagUnif (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hF : IsFactorAH u Hm χ) : IsFactorAH (diagUnif u) ((2 : ℂ) • Hm) (diagChar u χ) := by
  refine ⟨?_, fun l => ?_, fun l J z hz => ?_⟩
  · show Matrix.conjTranspose ((2 : ℂ) • Hm) = (2 : ℂ) • Hm
    rw [Matrix.conjTranspose_smul, hF.1.eq]
    simp
  · show ‖∏ I, _‖ = 1
    rw [norm_prod]
    exact Finset.prod_eq_one fun I _ => by rw [norm_zpow, hF.2.1, one_zpow]
  · have hc : ∀ I, (⊤ : (Sp ℂ).Opens) ≤ (u.ex (((I.down.card : ℕ) : ℂ) • z)).left ⁻¹ᵁ M.U (J PUnit.unit I) := by
      intro I
      have h := (chart M _ J).1 hz I
      rw [← mulCard_apply, ex_mulCard, Over.comp_left]
      exact h
    set E : ℂ := Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) with hE
    have key : ∀ I : ULift.{0} (Finset (Fin 2)),
        u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I =
          χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I *
            Complex.exp ((expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) *
            u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • (z + (l : Fin g → ℂ))) ^ expo I := by
      intro I
      rw [hF.2.2 ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ (J PUnit.unit I) _ (hc I)]
      simp only []
      rw [herm_smul_nat, herm_smul_nat, smul_add, mul_zpow, mul_zpow, Complex.exp_int_mul]
      congr 3
      rw [hE]
      ring_nf
    rw [diagUnif_fr, diagUnif_fr, Finset.prod_congr rfl fun I _ => key I, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    have hs := sum_exp_sq
    have e1 : (∑ I : ULift.{0} (Finset (Fin 2)), (expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) =
        (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) * E := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [expo]
      ring
    rw [e1, hs, hE, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    congr 1
    ring

end GlobalTheory.TorusRM.DiagFrame


open GlobalTheory GlobalTheory.TorusRM.DiagFrame in
theorem GlobalTheory.TorusRM.exists_isFactorAH_lam_diag : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → IsFactorAH u Hm χ →
    ∃ (u' : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g) (χ' : u'.Λ → ℂ),
      u'.ex = u.ex ∧ IsFactorAH u' ((2 : ℂ) • Hm) χ' := by
  intro g A _ hA M u Hm χ hM hF
  haveI : IsCommMonObj A := hA.comm
  exact ⟨diagUnif u, diagChar u χ, rfl, isFactorAH_diagUnif u hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem homLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  intro R R₀ _ _ I hI π _ _ B B₀ _ _ _ _ p hs _ _ B' B₀' _ _ _ _ p' hs' hp' hker' _ φ
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  letI : Algebra R B₀' := ((algebraMap R₀ B₀').comp π).toAlgebra
  let P : B →ₐ[R] B₀' := { (φ : B₀ →+* B₀').comp p with
    commutes' := fun r ↦ by
      show φ (p (algebraMap R B r)) = algebraMap R₀ B₀' (π r)
      rw [hs.map_algebraMap r]
      exact φ.commutes (π r) }
  let P' : B' →ₐ[R] B₀' := { p' with commutes' := fun r ↦ hs'.map_algebraMap r }
  have hn := LocalIsomorphism.nil I P' hker' (map_sq hI B')
  exact ⟨Algebra.FormallySmooth.liftOfSurjective P P' hp' hn,
    fun b ↦ Algebra.FormallySmooth.liftOfSurjective_apply P P' hp' hn b⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_over_normal_quasi_projective_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  first | (exact @GlobalTheory.ExtendNormal.exists_extension) | (exact GlobalTheory.ExtendNormal.exists_extension) | (intros; apply GlobalTheory.ExtendNormal.exists_extension  <;> assumption)
end

